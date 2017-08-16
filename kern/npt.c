/**
 * npt.c - Support for AMD's Nested Page Tables (RVI)
 *
 * Authors:
 *   Adam Belay            <abelay@stanford.edu>
 *   Elias Kouskoumvekakis <eliask.kousk@stromasys.com>
 *
 * We support the NPT by making a sort of 'shadow' copy of the Linux
 * process page table. Mappings are created lazily as they are needed.
 * We keep the NPT synchronized with the process page table through
 * mmu_notifier callbacks.
 * 
 * Some of the low-level NPT functions are based on KVM.
 * Original Authors:
 *   Avi Kivity   <avi@qumranet.com>
 *   Yaniv Kamay  <yaniv@qumranet.com>
 */

#include <linux/mm.h>
#include <linux/hugetlb.h>
#include <linux/kernel.h>
#include <linux/sched.h>
#include <asm/pgtable.h>

#include "dune.h"
#include "svm.h"
#include "compat.h"

#define NPT_LEVELS	4	/* 0 through 3 */
#define HUGE_PAGE_SIZE	2097152

#define SVM_NPT_FAULT_READ	0x01
#define SVM_NPT_FAULT_WRITE	0x02
#define SVM_NPT_FAULT_INS	0x04

typedef unsigned long npte_t;

#define __NPTE_READ	0x01
#define __NPTE_WRITE	0x02
#define __NPTE_EXEC	0x04
#define __NPTE_IPAT	0x40
#define __NPTE_SZ	0x80
#define __NPTE_A	0x100
#define __NPTE_D	0x200
#define __NPTE_PFNMAP	0x400 /* ignored by HW */
#define __NPTE_TYPE(n)	(((n) & 0x7) << 3)

enum {
	NPTE_TYPE_UC = 0, /* uncachable */
	NPTE_TYPE_WC = 1, /* write combining */
	NPTE_TYPE_WT = 4, /* write through */
	NPTE_TYPE_WP = 5, /* write protected */
	NPTE_TYPE_WB = 6, /* write back */
};

#define __NPTE_NONE	0
#define __NPTE_FULL	(__NPTE_READ | __NPTE_WRITE | __NPTE_EXEC)

#define NPTE_ADDR	(~(PAGE_SIZE - 1))
#define NPTE_FLAGS	(PAGE_SIZE - 1)

static inline uintptr_t npte_addr(npte_t npte)
{
	return (npte & NPTE_ADDR);
}

static inline uintptr_t npte_page_vaddr(npte_t npte)
{
	return (uintptr_t) __va(npte_addr(npte));
}

static inline npte_t npte_flags(npte_t npte)
{
	return (npte & NPTE_FLAGS);
}

static inline int npte_present(npte_t npte)
{
	return (npte & __NPTE_FULL) > 0;
}

static inline int npte_big(npte_t npte)
{
	return (npte & __NPTE_SZ) > 0;
}

#define ADDR_INVAL ((unsigned long) -1)

static unsigned long hva_to_gpa(struct svm_vcpu *vcpu,
				struct mm_struct *mm,
				unsigned long hva)
{
	uintptr_t mmap_start;

	if (!mm) {
		printk(KERN_ERR "npt: proc has no MM %d\n", current->pid);
		return GPA_ADDR_INVAL;
	}

	BUG_ON(!mm);

	mmap_start = LG_ALIGN(mm->mmap_base) - GPA_SIZE;

	if ((hva & ~GPA_MASK) == 0)
		return (hva & GPA_MASK) | GPA_ADDR_PROC;
	else if (hva < LG_ALIGN(mm->mmap_base) && hva >= mmap_start)
		return (hva - mmap_start) | GPA_ADDR_MAP;
	else if ((hva & ~GPA_MASK) == (mm->start_stack & ~GPA_MASK))
		return (hva & GPA_MASK) | GPA_ADDR_STACK;
	else
		return GPA_ADDR_INVAL;
}

static unsigned long gpa_to_hva(struct svm_vcpu *vcpu,
				struct mm_struct *mm,
				unsigned long gpa)
{
	if ((gpa & ~GPA_MASK) == GPA_ADDR_PROC)
		return (gpa & GPA_MASK);
	else if ((gpa & ~GPA_MASK) == GPA_ADDR_MAP)
		return (gpa & GPA_MASK) + LG_ALIGN(mm->mmap_base) - GPA_SIZE;
	else if ((gpa & ~GPA_MASK) == GPA_ADDR_STACK)
		return (gpa & GPA_MASK) | (mm->start_stack & ~GPA_MASK);
	else
		return GPA_ADDR_INVAL;
}

#define ADDR_TO_IDX(la, n) \
	((((unsigned long) (la)) >> (12 + 9 * (n))) & ((1 << 9) - 1))

static int
npt_lookup_gpa(struct svm_vcpu *vcpu, void *gpa, int level,
	   int create, npte_t **npte_out)
{
	int i;
	npte_t *dir = (npte_t *) __va(vcpu->npt_root);

	for (i = NPT_LEVELS - 1; i > level; i--) {
		int idx = ADDR_TO_IDX(gpa, i);

		if (!npte_present(dir[idx])) {
			void *page;

			if (!create)
				return -ENOENT;

			page = (void *) __get_free_page(GFP_ATOMIC);
			if (!page)
				return -ENOMEM;

			memset(page, 0, PAGE_SIZE);
			dir[idx] = npte_addr(virt_to_phys(page)) |
				   __NPTE_FULL;
		}

		if (npte_big(dir[idx])) {
			if (i != 1 && i != 2)
				return -EINVAL;
			level = i;
			break;
		}

		dir = (npte_t *) npte_page_vaddr(dir[idx]);
	}

	*npte_out = &dir[ADDR_TO_IDX(gpa, level)];
	return 0;
}

static int
npt_lookup(struct svm_vcpu *vcpu, struct mm_struct *mm,
	   void *hva, int level, int create, npte_t **npte_out)
{
	void *gpa = (void *) hva_to_gpa(vcpu, mm, (unsigned long) hva);

	if (gpa == (void *) GPA_ADDR_INVAL) {
		printk(KERN_ERR "npt: hva %p is out of range\n", hva);
		printk(KERN_ERR "npt: mem_base %lx, stack_start %lx\n",
		       mm->mmap_base, mm->start_stack);
		return -EINVAL;
	}

	return npt_lookup_gpa(vcpu, gpa, level, create, npte_out);
}

static void free_npt_page(npte_t npte)
{
	struct page *page = pfn_to_page(npte_addr(npte) >> PAGE_SHIFT);

	/* PFN mapppings are not backed by pages. */
	if (npte & __NPTE_PFNMAP)
		return;

	if (npte & __NPTE_WRITE)
		set_page_dirty(page);
	put_page(page);
}

static void free_npt_page_lock(npte_t npte)
{
	struct page *page = pfn_to_page(npte_addr(npte) >> PAGE_SHIFT);

	/* PFN mapppings are not backed by pages. */
	if (npte & __NPTE_PFNMAP)
		return;

	if (npte & __NPTE_WRITE)
		set_page_dirty_lock(page);
	put_page(page);
}

static void svm_free_npt(unsigned long npt_root)
{
	npte_t *pgd = (npte_t *) __va(npt_root);
	int i, j, k, l;

	for (i = 0; i < PTRS_PER_PGD; i++) {
		npte_t *pud = (npte_t *) npte_page_vaddr(pgd[i]);
		if (!npte_present(pgd[i]))
			continue;

		for (j = 0; j < PTRS_PER_PUD; j++) {
			npte_t *pmd = (npte_t *) npte_page_vaddr(pud[j]);
			if (!npte_present(pud[j]))
				continue;
			if (npte_flags(pud[j]) & __NPTE_SZ) {
				free_npt_page_lock(pud[j]);
				continue;
			}

			for (k = 0; k < PTRS_PER_PMD; k++) {
				npte_t *pte = (npte_t *) npte_page_vaddr(pmd[k]);
				if (!npte_present(pmd[k]))
					continue;
				if (npte_flags(pmd[k]) & __NPTE_SZ) {
					free_npt_page_lock(pmd[k]);
					continue;
				}

				for (l = 0; l < PTRS_PER_PTE; l++) {
					if (!npte_present(pte[l]))
						continue;

					free_npt_page_lock(pte[l]);
				}

				free_page((unsigned long) pte);
			}

			free_page((unsigned long) pmd);
		}

		free_page((unsigned long) pud);
	}

	free_page((unsigned long) pgd);
}

static int npt_clear_npte(npte_t *npte)
{
	if (*npte == __NPTE_NONE)
		return 0;

	free_npt_page(*npte);
	*npte = __NPTE_NONE;

	return 1;
}

static int npt_clear_l1_npte(npte_t *npte)
{
	int i;
	npte_t *pte = (npte_t *) npte_page_vaddr(*npte);

	if (*npte == __NPTE_NONE)
		return 0;

	for (i = 0; i < PTRS_PER_PTE; i++) {
		if (!npte_present(pte[i]))
			continue;

		free_npt_page(pte[i]);
	}

	free_page((uintptr_t) pte);
	*npte = __NPTE_NONE;

	return 1;
}

static int npt_clear_l2_npte(npte_t *npte)
{
	int i, j;
	npte_t *pmd = (npte_t *) npte_page_vaddr(*npte);

	if (*npte == __NPTE_NONE)
		return 0;

	for (i = 0; i < PTRS_PER_PMD; i++) {
		npte_t *pte = (npte_t *) npte_page_vaddr(pmd[i]);
		if (!npte_present(pmd[i]))
			continue;
		if (npte_flags(pmd[i]) & __NPTE_SZ) {
			free_npt_page(pmd[i]);
			continue;
		}

		for (j = 0; j < PTRS_PER_PTE; j++) {
			if (!npte_present(pte[j]))
				continue;

			free_npt_page(pte[j]);
		}

		free_page((uintptr_t) pte);
	}

	free_page((uintptr_t) pmd);

	*npte = __NPTE_NONE;

	return 1;
}

static int npt_set_pfnmap_npte(struct svm_vcpu *vcpu, int make_write,
				unsigned long gpa, unsigned long hva)
{
	struct vm_area_struct *vma;
	struct mm_struct *mm = current->mm;
	npte_t *npte, flags;
	unsigned long pfn;
	int ret;
	int cache_control;

	down_read(&mm->mmap_sem);
	vma = find_vma(mm, hva);
	if (!vma) {
		up_read(&mm->mmap_sem);
		return -EFAULT;
	}

	if (!(vma->vm_flags & (VM_IO | VM_PFNMAP))) {
		up_read(&mm->mmap_sem);
		return -EFAULT;
	}

	ret = follow_pfn(vma, hva, &pfn);
	if (ret) {
		up_read(&mm->mmap_sem);
		return ret;
	}

	if (pgprot2cachemode(vma->vm_page_prot) == _PAGE_CACHE_MODE_WB)
		cache_control = NPTE_TYPE_WB;
	else if (pgprot2cachemode(vma->vm_page_prot) == _PAGE_CACHE_MODE_WC)
		cache_control = NPTE_TYPE_WC;
	else
		cache_control = NPTE_TYPE_UC;

	up_read(&mm->mmap_sem);

	/* NOTE: pfn's can not be huge pages, which is quite a relief here */
	spin_lock(&vcpu->npt_lock);
	ret = npt_lookup_gpa(vcpu, (void *) gpa, 0, 1, &npte);
	if (ret) {
		spin_unlock(&vcpu->npt_lock);
		printk(KERN_ERR "npt: failed to lookup NPT entry\n");
		return ret;
	}

	flags = __NPTE_READ | __NPTE_TYPE(cache_control) |
		__NPTE_IPAT | __NPTE_PFNMAP;
	if (make_write)
		flags |= __NPTE_WRITE;
	if (vcpu->npt_ad_enabled) {
		/* premark A/D to avoid extra memory references */
		flags |= __NPTE_A;
		if (make_write)
			flags |= __NPTE_D;
	}

	if (npte_present(*npte))
		npt_clear_npte(npte);

	*npte = npte_addr(pfn << PAGE_SHIFT) | flags;
	spin_unlock(&vcpu->npt_lock);

	return 0;
}

static int npt_set_npte(struct svm_vcpu *vcpu, int make_write,
			unsigned long gpa, unsigned long hva)
{
	int ret;
	npte_t *npte, flags;
	struct page *page;
	unsigned huge_shift;
	int level;

	ret = get_user_pages_fast(hva, 1, make_write, &page);
	if (ret != 1) {
		ret = npt_set_pfnmap_npte(vcpu, make_write, gpa, hva);
		if (ret)
			printk(KERN_ERR "npt: failed to get user page %lx\n", hva);
		return ret;
	}

	spin_lock(&vcpu->npt_lock);

	huge_shift = compound_order(compound_head(page)) + PAGE_SHIFT;
	level = 0;
	if (huge_shift == 30)
		level = 2;
	else if (huge_shift == 21)
		level = 1;

	ret = npt_lookup_gpa(vcpu, (void *) gpa,
			     level, 1, &npte);
	if (ret) {
		spin_unlock(&vcpu->npt_lock);
		put_page(page);
		printk(KERN_ERR "npt: failed to lookup EPT entry\n");
		return ret;
	}

	if (npte_present(*npte)) {
		if (!npte_big(*npte) && level == 2)
			npt_clear_l2_npte(npte);
		else if (!npte_big(*npte) && level == 1)
			npt_clear_l1_npte(npte);
		else
			npt_clear_npte(npte);
	}

	flags = __NPTE_READ | __NPTE_EXEC |
		__NPTE_TYPE(NPTE_TYPE_WB) | __NPTE_IPAT;
	if (make_write)
		flags |= __NPTE_WRITE;
	if (vcpu->npt_ad_enabled) {
		/* premark A/D to avoid extra memory references */
		flags |= __NPTE_A;
		if (make_write)
			flags |= __NPTE_D;
	}

	if (level) {
		struct page *tmp = page;
		page = compound_head(page);
		get_page(page);
		put_page(tmp);

		flags |= __NPTE_SZ;
	}

	*npte = npte_addr(page_to_phys(page)) | flags;

	spin_unlock(&vcpu->npt_lock);

	return 0;
}

int svm_do_npt_fault(struct svm_vcpu *vcpu, unsigned long gpa,
		     unsigned long gva, int fault_flags)
{
	int ret;
	unsigned long hva = gpa_to_hva(vcpu, current->mm, gpa);
	int make_write = (fault_flags & SVM_NPT_FAULT_WRITE) ? 1 : 0;

	pr_debug("npt: GPA: 0x%lx, GVA: 0x%lx, HVA: 0x%lx, flags: %x\n",
		 gpa, gva, hva, fault_flags);

	ret = npt_set_npte(vcpu, make_write, gpa, hva);

	return ret;
}

/**
 * npt_invalidate_page - removes a page from the EPT
 * @vcpu: the vcpu
 * @mm: the process's mm_struct
 * @addr: the address of the page
 * 
 * Returns 1 if the page was removed, 0 otherwise
 */
static int npt_invalidate_page(struct svm_vcpu *vcpu,
			       struct mm_struct *mm,
			       unsigned long addr)
{
	int ret;
	npte_t *npte;
	void *gpa = (void *) hva_to_gpa(vcpu, mm, (unsigned long) addr);

	if (gpa == (void *) GPA_ADDR_INVAL) {
		printk(KERN_ERR "npt: hva %lx is out of range\n", addr);
		return 0;
	}

	spin_lock(&vcpu->npt_lock);
	ret = npt_lookup_gpa(vcpu, (void *) gpa, 0, 0, &npte);
	if (ret) {
		spin_unlock(&vcpu->npt_lock);
		return 0;
	}

	ret = npt_clear_npte(npte);
	spin_unlock(&vcpu->npt_lock);

	if (ret)
		svm_npt_sync_individual_addr(vcpu, (gpa_t) gpa);

	return ret;
}

/**
 * npt_check_page_mapped - determines if a page is mapped in the npt
 * @vcpu: the vcpu
 * @mm: the process's mm_struct
 * @addr: the address of the page
 * 
 * Returns 1 if the page is mapped, 0 otherwise
 */
static int npt_check_page_mapped(struct svm_vcpu *vcpu,
				 struct mm_struct *mm,
				 unsigned long addr)
{
	int ret;
	npte_t *npte;
	void *gpa = (void *) hva_to_gpa(vcpu, mm, (unsigned long) addr);

	if (gpa == (void *) GPA_ADDR_INVAL) {
		printk(KERN_ERR "npt: hva %lx is out of range\n", addr);
		return 0;
	}

	spin_lock(&vcpu->npt_lock);
	ret = npt_lookup_gpa(vcpu, (void *) gpa, 0, 0, &npte);
	spin_unlock(&vcpu->npt_lock);

	return !ret;
}

/**
 * npt_check_page_accessed - determines if a page was accessed using AD bits
 * @vcpu: the vcpu
 * @mm: the process's mm_struct
 * @addr: the address of the page
 * @flush: if true, clear the A bit
 * 
 * Returns 1 if the page was accessed, 0 otherwise
 */
static int npt_check_page_accessed(struct svm_vcpu *vcpu,
				   struct mm_struct *mm,
				   unsigned long addr,
				   bool flush)
{
	int ret, accessed;
	npte_t *npte;
	void *gpa = (void *) hva_to_gpa(vcpu, mm, (unsigned long) addr);

	if (gpa == (void *) GPA_ADDR_INVAL) {
		printk(KERN_ERR "npt: hva %lx is out of range\n", addr);
		return 0;
	}

	spin_lock(&vcpu->npt_lock);
	ret = npt_lookup_gpa(vcpu, (void *) gpa, 0, 0, &npte);
	if (ret) {
		spin_unlock(&vcpu->npt_lock);
		return 0;
	}

	accessed = (*npte & __NPTE_A);
	if (flush & accessed)
		*npte = (*npte & ~__NPTE_A);
	spin_unlock(&vcpu->npt_lock);

	if (flush & accessed)
		svm_npt_sync_individual_addr(vcpu, (gpa_t) gpa);

	return accessed;
}

static inline struct svm_vcpu *mmu_notifier_to_svm(struct mmu_notifier *mn)
{
	return container_of(mn, struct svm_vcpu, mmu_notifier);
}

static void npt_mmu_notifier_invalidate_page(struct mmu_notifier *mn,
					     struct mm_struct *mm,
					     unsigned long address)
{
	struct svm_vcpu *vcpu = mmu_notifier_to_svm(mn);

	pr_debug("npt: invalidate_page addr %lx\n", address);

	npt_invalidate_page(vcpu, mm, address);
}

static void npt_mmu_notifier_invalidate_range_start(struct mmu_notifier *mn,
						    struct mm_struct *mm,
						    unsigned long start,
						    unsigned long end)
{
	struct svm_vcpu *vcpu = mmu_notifier_to_svm(mn);
	int ret;
	npte_t *npte;
	unsigned long pos = start;
	bool sync_needed = false;

	pr_debug("npt: invalidate_range_start start %lx end %lx\n", start, end);

	spin_lock(&vcpu->npt_lock);
	while (pos < end) {
		ret = npt_lookup(vcpu, mm, (void *) pos, 0, 0, &npte);
		if (!ret) {
			pos += npte_big(*npte) ? HUGE_PAGE_SIZE : PAGE_SIZE;
			npt_clear_npte(npte);
			sync_needed = true;
		} else
			pos += PAGE_SIZE;
	}
	spin_unlock(&vcpu->npt_lock);

	if (sync_needed)
		svm_npt_sync_vcpu(vcpu);
}

static void npt_mmu_notifier_invalidate_range_end(struct mmu_notifier *mn,
						  struct mm_struct *mm,
						  unsigned long start,
						  unsigned long end)
{
}

static void npt_mmu_notifier_change_pte(struct mmu_notifier *mn,
					struct mm_struct *mm,
					unsigned long address,
					pte_t pte)
{
	struct svm_vcpu *vcpu = mmu_notifier_to_svm(mn);

	pr_debug("npt: change_pte addr %lx flags %lx\n", address, pte_flags(pte));

	/*
	 * NOTE: Recent linux kernels (seen on 3.7 at least) hold a lock
	 * while calling this notifier, making it impossible to call
	 * get_user_pages_fast(). As a result, we just invalidate the
	 * page so that the mapping can be recreated later during a fault.
	 */
	npt_invalidate_page(vcpu, mm, address);
}

#if LINUX_VERSION_CODE >= KERNEL_VERSION(3,17,0)
static int npt_mmu_notifier_clear_flush_young(struct mmu_notifier *mn,
					      struct mm_struct *mm,
					      unsigned long start,
					      unsigned long end)
{
	int ret = 0;
	struct svm_vcpu *vcpu = mmu_notifier_to_svm(mn);

	pr_debug("npt: clear_flush_young start %lx end %lx\n", start, end);

	if (!vcpu->npt_ad_enabled) {
		for (; start < end; start += PAGE_SIZE)
			ret |= npt_invalidate_page(vcpu, mm, start);
	} else {
		for (; start < end; start += PAGE_SIZE)
			ret |= npt_check_page_accessed(vcpu, mm, start, true);
	}

	return ret;
}
#else
static int npt_mmu_notifier_clear_flush_young(struct mmu_notifier *mn,
					      struct mm_struct *mm,
					      unsigned long address)
{
	struct svm_vcpu *vcpu = mmu_notifier_to_svm(mn);

	pr_debug("npt: clear_flush_young addr %lx\n", address);

	if (!vcpu->npt_ad_enabled)
		return npt_invalidate_page(vcpu, mm, address);
	else
		return npt_check_page_accessed(vcpu, mm, address, true);
}
#endif

static int npt_mmu_notifier_test_young(struct mmu_notifier *mn,
				       struct mm_struct *mm,
				       unsigned long address)
{
	struct svm_vcpu *vcpu = mmu_notifier_to_svm(mn);

	pr_debug("npt: test_young addr %lx\n", address);

	if (!vcpu->npt_ad_enabled)
		return npt_check_page_mapped(vcpu, mm, address);
	else
		return npt_check_page_accessed(vcpu, mm, address, false);
}

static void npt_mmu_notifier_release(struct mmu_notifier *mn,
				     struct mm_struct *mm)
{
}

static const struct mmu_notifier_ops npt_mmu_notifier_ops = {
	.invalidate_page	= npt_mmu_notifier_invalidate_page,
	.invalidate_range_start	= npt_mmu_notifier_invalidate_range_start,
	.invalidate_range_end	= npt_mmu_notifier_invalidate_range_end,
	.clear_flush_young	= npt_mmu_notifier_clear_flush_young,
	.test_young		= npt_mmu_notifier_test_young,
	.change_pte		= npt_mmu_notifier_change_pte,
	.release		= npt_mmu_notifier_release,
};

int svm_init_npt(struct svm_vcpu *vcpu)
{
	void *page = (void *) __get_free_page(GFP_KERNEL);

	if (!page)
		return -ENOMEM;

	memset(page, 0, PAGE_SIZE);
	vcpu->npt_root =  __pa(page);
	
	return 0;
}

int svm_create_npt(struct svm_vcpu *vcpu)
{
	int ret;

	vcpu->mmu_notifier.ops = &npt_mmu_notifier_ops;
	ret = mmu_notifier_register(&vcpu->mmu_notifier, current->mm);
	if (ret)
		goto fail;

	return 0;

fail:
	svm_free_npt(vcpu->npt_root);

	return ret;
}

void svm_destroy_npt(struct svm_vcpu *vcpu)
{
	if (current->mm)
		mmu_notifier_unregister(&vcpu->mmu_notifier, current->mm);
	svm_free_npt(vcpu->npt_root);
}
