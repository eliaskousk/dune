/**
 *  svm.c - The AMD-V (SVM) driver for Dune
 *
 * This file is derived from Linux KVM AMD-V (SVM) support.
 * Copyright (C) 2006 Qumranet, Inc.
 * Copyright 2010 Red Hat, Inc. and/or its affiliates.
 *
 * Original Authors:
 *   Avi Kivity   <avi@qumranet.com>
 *   Yaniv Kamay  <yaniv@qumranet.com>
 *
 * This modified version is simpler because it avoids the following
 * features that are not requirements for Dune:
 *  * Real-mode emulation
 *  * Nested SVM support
 *  * I/O hardware emulation
 *  * Any of the more esoteric X86 features and registers
 *  * KVM-specific functionality
 *
 * In essence we provide only the minimum functionality needed to run
 * a process in svm non-root mode rather than the full hardware emulation
 * needed to support an entire OS.
 *
 * This driver is a research prototype and as such has the following
 * limitations:
 *
 * FIXME: Backward compatability is currently a non-goal, and only recent
 * full-featured (NPT, ASID, etc.) AMD hardware is supported by this
 * driver. Tested on the AMD Ryzen 1500X processor.
 *
 * FIXME: Eventually we should handle concurrent user's of SVM more
 * gracefully instead of requiring exclusive access. This would allow
 * Dune to interoperate with KVM and other HV solutions.
 *
 * FIXME: We need to support hotplugged physical CPUs.
 *
 * Authors:
 *   Adam Belay            <abelay@stanford.edu>
 *   Elias Kouskoumvekakis <eliask.kousk@stromasys.com>
 */

#include <linux/module.h>
#include <linux/kernel.h>
#include <linux/mm.h>
#include <linux/highmem.h>
#include <linux/sched.h>
#include <linux/moduleparam.h>
#include <linux/slab.h>
#include <linux/tboot.h>
#include <linux/init.h>
#include <linux/smp.h>
#include <linux/percpu.h>
#include <linux/syscalls.h>
#include <linux/version.h>

#include <asm/desc.h>
#include <asm/vmx.h>
#include <asm/svm.h>
#include <asm/unistd_64.h>
#include <asm/virtext.h>
#include <asm/traps.h>

#include "dune.h"
#include "svm.h"
#include "compat.h"

// =========================
// Start of KVM SVM includes
// =========================

//#include "irq.h"
//#include "mmu.h"
//#include "x86.h"
//#include "cpuid.h"
//#include "trace.h"

// =======================
// End of KVM SVM includes
// =======================

static atomic_t svm_enable_failed;

static DECLARE_BITMAP(svm_vpid_bitmap, VMX_NR_VPIDS);
static DEFINE_SPINLOCK(svm_vpid_lock);

static unsigned long *msr_bitmap;

#define NUM_SYSCALLS 312

#if LINUX_VERSION_CODE <= KERNEL_VERSION(3,11,0)
typedef void (*sys_call_ptr_t)(void);
#else
#include <asm/syscall.h>
#endif
static sys_call_ptr_t dune_syscall_tbl[NUM_SYSCALLS] __cacheline_aligned;

static DEFINE_PER_CPU(struct svm_cpu_data *, svm_data);
static DEFINE_PER_CPU(struct vmcs *, svmarea);
static DEFINE_PER_CPU(struct desc_ptr, host_gdt);
static DEFINE_PER_CPU(int, svm_enabled);
DEFINE_PER_CPU(struct svm_vcpu *, local_vcpu);

static LIST_HEAD(vcpus);

static inline void __invvpid(int ext, u16 vpid, gva_t gva)
{
	struct {
		u64 vpid : 16;
		u64 rsvd : 48;
		u64 gva;
	} operand = { vpid, 0, gva };

	asm volatile (ASM_VMX_INVVPID
		/* CF==1 or ZF==1 --> rc = -1 */
		"; ja 1f ; ud2 ; 1:"
	: : "a"(&operand), "c"(ext) : "cc", "memory");
}

static inline void __invnpt(int ext, u64 eptp, gpa_t gpa)
{
	struct {
		u64 eptp, gpa;
	} operand = {eptp, gpa};

	asm volatile (ASM_VMX_INVEPT
		/* CF==1 or ZF==1 --> rc = -1 */
		"; ja 1f ; ud2 ; 1:\n"
	: : "a" (&operand), "c" (ext) : "cc", "memory");
}

static inline void npt_sync_global(void)
{
	if (cpu_has_svm_invnpt_global())
		__invnpt(VMX_EPT_EXTENT_GLOBAL, 0, 0);
}

static inline void npt_sync_context(u64 eptp)
{
	if (cpu_has_svm_invnpt_context())
		__invept(VMX_EPT_EXTENT_CONTEXT, nptp, 0);
	else
		npt_sync_global();
}

static inline void npt_sync_individual_addr(u64 nptp, gpa_t gpa)
{
	if (cpu_has_vmx_invept_individual_addr())
		__invept(VMX_EPT_EXTENT_INDIVIDUAL_ADDR,
			 nptp, gpa);
	else
		npt_sync_context(nptp);
}

static inline void __vmxon(u64 addr)
{
	asm volatile (ASM_VMX_VMXON_RAX
	: : "a"(&addr), "m"(addr)
	: "memory", "cc");
}

static inline void vpid_sync_vcpu_single(u16 vpid)
{
	if (vpid == 0)
		return;

	if (cpu_has_svm_invvpid_single())
		__invvpid(VMX_VPID_EXTENT_SINGLE_CONTEXT, vpid, 0);
}

static inline void vpid_sync_vcpu_global(void)
{
	if (cpu_has_svm_invvpid_global())
		__invvpid(VMX_VPID_EXTENT_ALL_CONTEXT, 0, 0);
}

static inline void vpid_sync_context(u16 vpid)
{
	if (cpu_has_svm_invvpid_single())
		vpid_sync_vcpu_single(vpid);
	else
		vpid_sync_vcpu_global();
}

static __init int adjust_svm_controls(u32 ctl_min, u32 ctl_opt,
				      u32 msr, u32 *result)
{
	u32 svm_msr_low, svm_msr_high;
	u32 ctl = ctl_min | ctl_opt;

	rdmsr(msr, svm_msr_low, svm_msr_high);

	ctl &= svm_msr_high; /* bit == 0 in high word ==> must be zero */
	ctl |= svm_msr_low;  /* bit == 1 in low word  ==> must be one  */

	/* Ensure minimum (required) set of control bits are supported. */
	if (ctl_min & ~ctl)
		return -EIO;

	*result = ctl;
	return 0;
}

static __init bool allow_1_setting(u32 msr, u32 ctl)
{
	u32 svm_msr_low, svm_msr_high;

	rdmsr(msr, svm_msr_low, svm_msr_high);
	return svm_msr_high & ctl;
}

static __init int setup_vmcs_config(struct vmcs_config *vmcs_conf)
{
	u32 svm_msr_low, svm_msr_high;
	u32 min, opt, min2, opt2;
	u32 _pin_based_exec_control = 0;
	u32 _cpu_based_exec_control = 0;
	u32 _cpu_based_2nd_exec_control = 0;
	u32 _vmexit_control = 0;
	u32 _vmentry_control = 0;

	min = PIN_BASED_EXT_INTR_MASK | PIN_BASED_NMI_EXITING;
	opt = PIN_BASED_VIRTUAL_NMIS;
	if (adjust_svm_controls(min, opt, MSR_IA32_VMX_PINBASED_CTLS,
				&_pin_based_exec_control) < 0)
		return -EIO;

	min =
#ifdef CONFIG_X86_64
CPU_BASED_CR8_LOAD_EXITING |
CPU_BASED_CR8_STORE_EXITING |
#endif
CPU_BASED_CR3_LOAD_EXITING |
CPU_BASED_CR3_STORE_EXITING |
CPU_BASED_MOV_DR_EXITING |
CPU_BASED_USE_TSC_OFFSETING |
CPU_BASED_INVLPG_EXITING;

	opt = CPU_BASED_TPR_SHADOW |
	      CPU_BASED_USE_MSR_BITMAPS |
	      CPU_BASED_ACTIVATE_SECONDARY_CONTROLS;
	if (adjust_svm_controls(min, opt, MSR_IA32_VMX_PROCBASED_CTLS,
				&_cpu_based_exec_control) < 0)
		return -EIO;
#ifdef CONFIG_X86_64
	if ((_cpu_based_exec_control & CPU_BASED_TPR_SHADOW))
		_cpu_based_exec_control &= ~CPU_BASED_CR8_LOAD_EXITING &
					   ~CPU_BASED_CR8_STORE_EXITING;
#endif
	if (_cpu_based_exec_control & CPU_BASED_ACTIVATE_SECONDARY_CONTROLS) {
		min2 = 0;
		opt2 =  SECONDARY_EXEC_WBINVD_EXITING |
			SECONDARY_EXEC_ENABLE_VPID |
			SECONDARY_EXEC_ENABLE_EPT |
			SECONDARY_EXEC_RDTSCP |
			SECONDARY_EXEC_ENABLE_INVPCID;
		if (adjust_svm_controls(min2, opt2,
					MSR_IA32_VMX_PROCBASED_CTLS2,
					&_cpu_based_2nd_exec_control) < 0)
			return -EIO;
	}
#ifndef CONFIG_X86_64
	if (!(_cpu_based_2nd_exec_control &
				SECONDARY_EXEC_VIRTUALIZE_APIC_ACCESSES))
		_cpu_based_exec_control &= ~CPU_BASED_TPR_SHADOW;
#endif
	if (_cpu_based_2nd_exec_control & SECONDARY_EXEC_ENABLE_EPT) {
		/* CR3 accesses and invlpg don't need to cause VM Exits when EPT
		   enabled */
		_cpu_based_exec_control &= ~(CPU_BASED_CR3_LOAD_EXITING |
					     CPU_BASED_CR3_STORE_EXITING |
					     CPU_BASED_INVLPG_EXITING);
		rdmsr(MSR_IA32_VMX_EPT_VPID_CAP,
		      svm_capability.ept, svm_capability.vpid);
	}

	min = 0;
#ifdef CONFIG_X86_64
	min |= VM_EXIT_HOST_ADDR_SPACE_SIZE;
#endif
//	opt = VM_EXIT_SAVE_IA32_PAT | VM_EXIT_LOAD_IA32_PAT;
	opt = 0;
	if (adjust_svm_controls(min, opt, MSR_IA32_VMX_EXIT_CTLS,
				&_vmexit_control) < 0)
		return -EIO;

	min = 0;
//	opt = VM_ENTRY_LOAD_IA32_PAT;
	opt = 0;
	if (adjust_svm_controls(min, opt, MSR_IA32_VMX_ENTRY_CTLS,
				&_vmentry_control) < 0)
		return -EIO;

	rdmsr(MSR_IA32_VMX_BASIC, svm_msr_low, svm_msr_high);

	/* IA-32 SDM Vol 3B: VMCS size is never greater than 4kB. */
	if ((svm_msr_high & 0x1fff) > PAGE_SIZE)
		return -EIO;

#ifdef CONFIG_X86_64
	/* IA-32 SDM Vol 3B: 64-bit CPUs always have VMX_BASIC_MSR[48]==0. */
	if (svm_msr_high & (1u<<16))
		return -EIO;
#endif

	/* Require Write-Back (WB) memory type for VMCS accesses. */
	if (((svm_msr_high >> 18) & 15) != 6)
		return -EIO;

	vmcs_conf->size = svm_msr_high & 0x1fff;
	vmcs_conf->order = get_order(vmcs_config.size);
	vmcs_conf->revision_id = svm_msr_low;

	vmcs_conf->pin_based_exec_ctrl = _pin_based_exec_control;
	vmcs_conf->cpu_based_exec_ctrl = _cpu_based_exec_control;
	vmcs_conf->cpu_based_2nd_exec_ctrl = _cpu_based_2nd_exec_control;
	vmcs_conf->vmexit_ctrl         = _vmexit_control;
	vmcs_conf->vmentry_ctrl        = _vmentry_control;

	svm_capability.has_load_efer =
		allow_1_setting(MSR_IA32_VMX_ENTRY_CTLS,
				VM_ENTRY_LOAD_IA32_EFER)
		&& allow_1_setting(MSR_IA32_VMX_EXIT_CTLS,
				   VM_EXIT_LOAD_IA32_EFER);

	return 0;
}

static struct vmcs *__svm_alloc_vmcs(int cpu)
{
	int node = cpu_to_node(cpu);
	struct page *pages;
	struct vmcs *vmcs;

	pages = alloc_pages_exact_node(node, GFP_KERNEL, vmcs_config.order);
	if (!pages)
		return NULL;
	vmcs = page_address(pages);
	memset(vmcs, 0, vmcs_config.size);
	vmcs->revision_id = vmcs_config.revision_id; /* vmcs revision id */
	return vmcs;
}

/**
 * svm_alloc_vmcs - allocates a VMCS region
 *
 * NOTE: Assumes the new region will be used by the current CPU.
 *
 * Returns a valid VMCS region.
 */
static struct vmcs *svm_alloc_vmcs(void)
{
	return __svm_alloc_vmcs(raw_smp_processor_id());
}

/**
 * svm_free_vmcs - frees a VMCS region
 */
static void svm_free_vmcs(struct vmcs *vmcs)
{
	free_pages((unsigned long)vmcs, vmcs_config.order);
}

/*
 * Set up the vmcs's constant host-state fields, i.e., host-state fields that
 * will not change in the lifetime of the guest.
 * Note that host-state that does change is set elsewhere. E.g., host-state
 * that is set differently for each CPU is set in svm_vcpu_load(), not here.
 */
static void svm_setup_constant_host_state(void)
{
	u32 low32, high32;
	unsigned long tmpl;
	struct desc_ptr dt;

	vmcs_writel(HOST_CR0, read_cr0() & ~X86_CR0_TS);  /* 22.2.3 */
	vmcs_writel(HOST_CR4, __read_cr4());  /* 22.2.3, 22.2.5 */
	vmcs_writel(HOST_CR3, read_cr3());  /* 22.2.3 */

	vmcs_write16(HOST_CS_SELECTOR, __KERNEL_CS);  /* 22.2.4 */
	vmcs_write16(HOST_DS_SELECTOR, __KERNEL_DS);  /* 22.2.4 */
	vmcs_write16(HOST_ES_SELECTOR, __KERNEL_DS);  /* 22.2.4 */
	vmcs_write16(HOST_SS_SELECTOR, __KERNEL_DS);  /* 22.2.4 */
	vmcs_write16(HOST_TR_SELECTOR, GDT_ENTRY_TSS*8);  /* 22.2.4 */

	native_store_idt(&dt);
	vmcs_writel(HOST_IDTR_BASE, dt.address);   /* 22.2.4 */

	asm("mov $.Lkvm_vmx_return, %0" : "=r"(tmpl));
	vmcs_writel(HOST_RIP, tmpl); /* 22.2.5 */

	rdmsr(MSR_IA32_SYSENTER_CS, low32, high32);
	vmcs_write32(HOST_IA32_SYSENTER_CS, low32);
	rdmsrl(MSR_IA32_SYSENTER_EIP, tmpl);
	vmcs_writel(HOST_IA32_SYSENTER_EIP, tmpl);   /* 22.2.3 */

	rdmsr(MSR_EFER, low32, high32);
	vmcs_write32(HOST_IA32_EFER, low32);

	if (vmcs_config.vmexit_ctrl & VM_EXIT_LOAD_IA32_PAT) {
		rdmsr(MSR_IA32_CR_PAT, low32, high32);
		vmcs_write64(HOST_IA32_PAT, low32 | ((u64) high32 << 32));
	}

	vmcs_write16(HOST_FS_SELECTOR, 0);            /* 22.2.4 */
	vmcs_write16(HOST_GS_SELECTOR, 0);            /* 22.2.4 */

#ifdef CONFIG_X86_64
	rdmsrl(MSR_FS_BASE, tmpl);
	vmcs_writel(HOST_FS_BASE, tmpl); /* 22.2.4 */
	rdmsrl(MSR_GS_BASE, tmpl);
	vmcs_writel(HOST_GS_BASE, tmpl); /* 22.2.4 */
#else
	vmcs_writel(HOST_FS_BASE, 0); /* 22.2.4 */
	vmcs_writel(HOST_GS_BASE, 0); /* 22.2.4 */
#endif
}

static inline u16 svm_read_ldt(void)
{
	u16 ldt;
	asm("sldt %0" : "=g"(ldt));
	return ldt;
}

static unsigned long segment_base(u16 selector)
{
	struct desc_ptr *gdt = this_cpu_ptr(&host_gdt);
	struct desc_struct *d;
	unsigned long table_base;
	unsigned long v;

	if (!(selector & ~3))
		return 0;

	table_base = gdt->address;

	if (selector & 4) {           /* from ldt */
		u16 ldt_selector = svm_read_ldt();

		if (!(ldt_selector & ~3))
			return 0;

		table_base = segment_base(ldt_selector);
	}
	d = (struct desc_struct *)(table_base + (selector & ~7));
	v = get_desc_base(d);
#ifdef CONFIG_X86_64
	if (d->s == 0 && (d->type == 2 || d->type == 9 || d->type == 11))
		v |= ((unsigned long)((struct ldttss_desc64 *)d)->base3) << 32;
#endif
	return v;
}

static inline unsigned long svm_read_tr_base(void)
{
	u16 tr;
	asm("str %0" : "=g"(tr));
	return segment_base(tr);
}

static void __svm_setup_cpu(void)
{
	struct desc_ptr *gdt = this_cpu_ptr(&host_gdt);
	unsigned long sysenter_esp;
	unsigned long tmpl;

	/*
	 * Linux uses per-cpu TSS and GDT, so set these when switching
	 * processors.
	 */
	vmcs_writel(HOST_TR_BASE, vmx_read_tr_base()); /* 22.2.4 */
	vmcs_writel(HOST_GDTR_BASE, gdt->address);   /* 22.2.4 */

	rdmsrl(MSR_IA32_SYSENTER_ESP, sysenter_esp);
	vmcs_writel(HOST_IA32_SYSENTER_ESP, sysenter_esp); /* 22.2.3 */

	rdmsrl(MSR_FS_BASE, tmpl);
	vmcs_writel(HOST_FS_BASE, tmpl); /* 22.2.4 */
	rdmsrl(MSR_GS_BASE, tmpl);
	vmcs_writel(HOST_GS_BASE, tmpl); /* 22.2.4 */
}

static const u32 host_save_user_msrs[] = {
#ifdef CONFIG_X86_64
	MSR_STAR, MSR_LSTAR, MSR_CSTAR, MSR_SYSCALL_MASK, MSR_KERNEL_GS_BASE,
	MSR_FS_BASE,
#endif
	MSR_IA32_SYSENTER_CS, MSR_IA32_SYSENTER_ESP, MSR_IA32_SYSENTER_EIP,
	MSR_TSC_AUX,
};

#define NR_HOST_SAVE_USER_MSRS ARRAY_SIZE(host_save_user_msrs)

static void svm_vcpu_load_orig(struct kvm_vcpu *vcpu, int cpu)
{
	struct vcpu_svm *svm = to_svm(vcpu);
	int i;

	if (unlikely(cpu != vcpu->cpu)) {
		svm->asid_generation = 0;
		mark_all_dirty(svm->vmcb);
	}

#ifdef CONFIG_X86_64
	rdmsrl(MSR_GS_BASE, to_svm(vcpu)->host.gs_base);
#endif
	savesegment(fs, svm->host.fs);
	savesegment(gs, svm->host.gs);
	svm->host.ldt = kvm_read_ldt();

	for (i = 0; i < NR_HOST_SAVE_USER_MSRS; i++)
		rdmsrl(host_save_user_msrs[i], svm->host_user_msrs[i]);

	if (static_cpu_has(X86_FEATURE_TSCRATEMSR)) {
		u64 tsc_ratio = vcpu->arch.tsc_scaling_ratio;
		if (tsc_ratio != __this_cpu_read(current_tsc_ratio)) {
			__this_cpu_write(current_tsc_ratio, tsc_ratio);
			wrmsrl(MSR_AMD64_TSC_RATIO, tsc_ratio);
		}
	}
	/* This assumes that the kernel never uses MSR_TSC_AUX */
	if (static_cpu_has(X86_FEATURE_RDTSCP))
		wrmsrl(MSR_TSC_AUX, svm->tsc_aux);

	avic_vcpu_load(vcpu, cpu);
}

static void __svm_get_cpu_helper(void *ptr)
{
	struct svm_vcpu *vcpu = ptr;

	BUG_ON(raw_smp_processor_id() != vcpu->cpu);
	vmcs_clear(vcpu->vmcs);
	if (__this_cpu_read(local_vcpu) == vcpu)
		this_cpu_write(local_vcpu, NULL);
}

/**
 * svm_get_cpu - called before using a cpu
 * @vcpu: VCPU that will be loaded.
 *
 * Disables preemption. Call svm_put_cpu() when finished.
 */
static void svm_get_cpu(struct svm_vcpu *vcpu)
{
	int cur_cpu = get_cpu();

	wrmsrl(MSR_KERNEL_GS_BASE, vcpu->guest_kernel_gs_base);

	if (__this_cpu_read(local_vcpu) != vcpu) {
		this_cpu_write(local_vcpu, vcpu);

		if (vcpu->cpu != cur_cpu) {
			if (vcpu->cpu >= 0)
				smp_call_function_single(vcpu->cpu,
							 __svm_get_cpu_helper, (void *) vcpu, 1);
			else
				vmcs_clear(vcpu->vmcs);

			vpid_sync_context(vcpu->vpid);
			npt_sync_context(vcpu->nptp);

			vcpu->launched = 0;
			vmcs_load(vcpu->vmcs);
			__svm_setup_cpu();
			vcpu->cpu = cur_cpu;
		} else {
			vmcs_load(vcpu->vmcs);
		}
	}
}

static void svm_vcpu_put_orig(struct kvm_vcpu *vcpu)
{
	struct vcpu_svm *svm = to_svm(vcpu);
	int i;

	avic_vcpu_put(vcpu);

	++vcpu->stat.host_state_reload;
	kvm_load_ldt(svm->host.ldt);
#ifdef CONFIG_X86_64
	loadsegment(fs, svm->host.fs);
	wrmsrl(MSR_KERNEL_GS_BASE, current->thread.gsbase);
	load_gs_index(svm->host.gs);
#else
	#ifdef CONFIG_X86_32_LAZY_GS
	loadsegment(gs, svm->host.gs);
#endif
#endif
	for (i = 0; i < NR_HOST_SAVE_USER_MSRS; i++)
		wrmsrl(host_save_user_msrs[i], svm->host_user_msrs[i]);
}

/**
 * svm_put_cpu - called after using a cpu
 * @vcpu: VCPU that was loaded.
 */
static void svm_put_cpu(struct svm_vcpu *vcpu)
{
	rdmsrl(MSR_KERNEL_GS_BASE, vcpu->guest_kernel_gs_base);
	put_cpu();
}

static void __svm_sync_helper(void *ptr)
{
	struct svm_vcpu *vcpu = ptr;

	npt_sync_context(vcpu->nptp);
}

struct sync_addr_args {
	struct svm_vcpu *vcpu;
	gpa_t gpa;
};

static void __svm_sync_individual_addr_helper(void *ptr)
{
	struct sync_addr_args *args = ptr;

	npt_sync_individual_addr(args->vcpu->nptp,
				 (args->gpa & ~(PAGE_SIZE - 1)));
}

/**
 * svm_npt_sync_vcpu - used to evict everything in the NPT
 * @vcpu: the vcpu
 */
void svm_npt_sync_vcpu(struct svm_vcpu *vcpu)
{
	smp_call_function_single(vcpu->cpu,
				 __vmx_sync_helper, (void *) vcpu, 1);
}

/**
 * svm_npt_sync_individual_addr - used to evict an individual address
 * @vcpu: the vcpu
 * @gpa: the guest-physical address
 */
void vmx_npt_sync_individual_addr(struct svm_vcpu *vcpu, gpa_t gpa)
{
	struct sync_addr_args args;
	args.vcpu = vcpu;
	args.gpa = gpa;

	smp_call_function_single(vcpu->cpu,
				 __svm_sync_individual_addr_helper, (void *) &args, 1);
}

#define STACK_DEPTH 12

/**
 * svm_dump_cpu - prints the CPU state
 * @vcpu: VCPU to print
 */
static void svm_dump_cpu(struct svm_vcpu *vcpu)
{
	unsigned long flags;
	int i;
	unsigned long *sp, val;

	svm_get_cpu(vcpu);
	vcpu->regs[VCPU_REGS_RIP] = vmcs_readl(GUEST_RIP);
	vcpu->regs[VCPU_REGS_RSP] = vmcs_readl(GUEST_RSP);
	flags = vmcs_readl(GUEST_RFLAGS);
	svm_put_cpu(vcpu);

	printk(KERN_INFO "svm: --- Begin VCPU Dump ---\n");
	printk(KERN_INFO "svm: CPU %d VPID %d\n", vcpu->cpu, vcpu->vpid);
	printk(KERN_INFO "svm: RIP 0x%016llx RFLAGS 0x%08lx\n",
	       vcpu->regs[VCPU_REGS_RIP], flags);
	printk(KERN_INFO "svm: RAX 0x%016llx RCX 0x%016llx\n",
	       vcpu->regs[VCPU_REGS_RAX], vcpu->regs[VCPU_REGS_RCX]);
	printk(KERN_INFO "svm: RDX 0x%016llx RBX 0x%016llx\n",
	       vcpu->regs[VCPU_REGS_RDX], vcpu->regs[VCPU_REGS_RBX]);
	printk(KERN_INFO "svm: RSP 0x%016llx RBP 0x%016llx\n",
	       vcpu->regs[VCPU_REGS_RSP], vcpu->regs[VCPU_REGS_RBP]);
	printk(KERN_INFO "svm: RSI 0x%016llx RDI 0x%016llx\n",
	       vcpu->regs[VCPU_REGS_RSI], vcpu->regs[VCPU_REGS_RDI]);
	printk(KERN_INFO "svm: R8  0x%016llx R9  0x%016llx\n",
	       vcpu->regs[VCPU_REGS_R8], vcpu->regs[VCPU_REGS_R9]);
	printk(KERN_INFO "svm: R10 0x%016llx R11 0x%016llx\n",
	       vcpu->regs[VCPU_REGS_R10], vcpu->regs[VCPU_REGS_R11]);
	printk(KERN_INFO "svm: R12 0x%016llx R13 0x%016llx\n",
	       vcpu->regs[VCPU_REGS_R12], vcpu->regs[VCPU_REGS_R13]);
	printk(KERN_INFO "svm: R14 0x%016llx R15 0x%016llx\n",
	       vcpu->regs[VCPU_REGS_R14], vcpu->regs[VCPU_REGS_R15]);
	printk(KERN_INFO "svm: FS.base 0x%016lx GS.base 0x%016lx\n",
	       vmcs_readl(GUEST_FS_BASE), vmcs_readl(GUEST_GS_BASE));

	printk(KERN_INFO "svm: Dumping Stack Contents...\n");
	sp = (unsigned long *) vcpu->regs[VCPU_REGS_RSP];
	for (i = 0; i < STACK_DEPTH; i++)
		if (get_user(val, &sp[i]))
			printk(KERN_INFO "svm: RSP%+-3ld ?\n",
			       i * sizeof(long));
		else
			printk(KERN_INFO "svm: RSP%+-3ld 0x%016lx\n",
			       i * sizeof(long), val);

	printk(KERN_INFO "svm: --- End VCPU Dump ---\n");
}

static u64 construct_nptp(unsigned long root_hpa)
{
	u64 eptp;

	/* TODO write the value reading from MSR */
	eptp = VMX_EPT_DEFAULT_MT |
	       VMX_EPT_DEFAULT_GAW << VMX_EPT_GAW_EPTP_SHIFT;
	if (cpu_has_vmx_ept_ad_bits())
		eptp |= VMX_EPT_AD_ENABLE_BIT;
	eptp |= (root_hpa & PAGE_MASK);

	return eptp;
}

/**
 * svm_setup_initial_guest_state - configures the initial state of guest registers
 */
static void svm_setup_initial_guest_state(struct dune_config *conf)
{
	unsigned long tmpl;
	unsigned long cr4 = X86_CR4_PAE | X86_CR4_VMXE | X86_CR4_OSXMMEXCPT |
			    X86_CR4_PGE | X86_CR4_OSFXSR;
	if (boot_cpu_has(X86_FEATURE_PCID))
		cr4 |= X86_CR4_PCIDE;
	if (boot_cpu_has(X86_FEATURE_OSXSAVE))
		cr4 |= X86_CR4_OSXSAVE;
	if (boot_cpu_has(X86_FEATURE_FSGSBASE))
		cr4 |= X86_CR4_FSGSBASE;

	/* configure control and data registers */
	vmcs_writel(GUEST_CR0, X86_CR0_PG | X86_CR0_PE | X86_CR0_WP |
			       X86_CR0_MP | X86_CR0_ET | X86_CR0_NE);
	vmcs_writel(CR0_READ_SHADOW, X86_CR0_PG | X86_CR0_PE | X86_CR0_WP |
				     X86_CR0_MP | X86_CR0_ET | X86_CR0_NE);
	vmcs_writel(GUEST_CR3, conf->cr3);
	vmcs_writel(GUEST_CR4, cr4);
	vmcs_writel(CR4_READ_SHADOW, cr4);
	vmcs_writel(GUEST_IA32_EFER, EFER_LME | EFER_LMA |
				     EFER_SCE | EFER_FFXSR);
	vmcs_writel(GUEST_GDTR_BASE, 0);
	vmcs_writel(GUEST_GDTR_LIMIT, 0);
	vmcs_writel(GUEST_IDTR_BASE, 0);
	vmcs_writel(GUEST_IDTR_LIMIT, 0);
	vmcs_writel(GUEST_DR7, 0);

	/* guest segment bases */
	vmcs_writel(GUEST_CS_BASE, 0);
	vmcs_writel(GUEST_DS_BASE, 0);
	vmcs_writel(GUEST_ES_BASE, 0);
	vmcs_writel(GUEST_GS_BASE, 0);
	vmcs_writel(GUEST_SS_BASE, 0);
	rdmsrl(MSR_FS_BASE, tmpl);
	vmcs_writel(GUEST_FS_BASE, tmpl);

	/* guest segment access rights */
	vmcs_writel(GUEST_CS_AR_BYTES, 0xA09B);
	vmcs_writel(GUEST_DS_AR_BYTES, 0xA093);
	vmcs_writel(GUEST_ES_AR_BYTES, 0xA093);
	vmcs_writel(GUEST_FS_AR_BYTES, 0xA093);
	vmcs_writel(GUEST_GS_AR_BYTES, 0xA093);
	vmcs_writel(GUEST_SS_AR_BYTES, 0xA093);

	/* guest segment limits */
	vmcs_write32(GUEST_CS_LIMIT, 0xFFFFFFFF);
	vmcs_write32(GUEST_DS_LIMIT, 0xFFFFFFFF);
	vmcs_write32(GUEST_ES_LIMIT, 0xFFFFFFFF);
	vmcs_write32(GUEST_FS_LIMIT, 0xFFFFFFFF);
	vmcs_write32(GUEST_GS_LIMIT, 0xFFFFFFFF);
	vmcs_write32(GUEST_SS_LIMIT, 0xFFFFFFFF);

	/* configure segment selectors */
	vmcs_write16(GUEST_CS_SELECTOR, 0);
	vmcs_write16(GUEST_DS_SELECTOR, 0);
	vmcs_write16(GUEST_ES_SELECTOR, 0);
	vmcs_write16(GUEST_FS_SELECTOR, 0);
	vmcs_write16(GUEST_GS_SELECTOR, 0);
	vmcs_write16(GUEST_SS_SELECTOR, 0);
	vmcs_write16(GUEST_TR_SELECTOR, 0);

	/* guest LDTR */
	vmcs_write16(GUEST_LDTR_SELECTOR, 0);
	vmcs_writel(GUEST_LDTR_AR_BYTES, 0x0082);
	vmcs_writel(GUEST_LDTR_BASE, 0);
	vmcs_writel(GUEST_LDTR_LIMIT, 0);

	/* guest TSS */
	vmcs_writel(GUEST_TR_BASE, 0);
	vmcs_writel(GUEST_TR_AR_BYTES, 0x0080 | AR_TYPE_BUSY_64_TSS);
	vmcs_writel(GUEST_TR_LIMIT, 0xff);

	/* initialize sysenter */
	vmcs_write32(GUEST_SYSENTER_CS, 0);
	vmcs_writel(GUEST_SYSENTER_ESP, 0);
	vmcs_writel(GUEST_SYSENTER_EIP, 0);

	/* other random initialization */
	vmcs_write32(GUEST_ACTIVITY_STATE, GUEST_ACTIVITY_ACTIVE);
	vmcs_write32(GUEST_INTERRUPTIBILITY_INFO, 0);
	vmcs_write32(GUEST_PENDING_DBG_EXCEPTIONS, 0);
	vmcs_write64(GUEST_IA32_DEBUGCTL, 0);
	vmcs_write32(VM_ENTRY_INTR_INFO_FIELD, 0);  /* 22.2.1 */
}

static void setup_perf_msrs(struct svm_vcpu *vcpu)
{
	int nr_msrs, i;
	struct perf_guest_switch_msr *msrs;
	struct svm_msr_entry *e;

	msrs = perf_guest_get_msrs(&nr_msrs);

	vcpu->msr_autoload.nr = nr_msrs;

	vmcs_write32(VM_EXIT_MSR_LOAD_COUNT, vcpu->msr_autoload.nr);
	vmcs_write32(VM_ENTRY_MSR_LOAD_COUNT, vcpu->msr_autoload.nr);

	for (i = 0; i < nr_msrs; i++) {
		e = &vcpu->msr_autoload.host[i];
		e->index = msrs[i].msr;
		e->value = msrs[i].host;
		e = &vcpu->msr_autoload.guest[i];
		e->index = msrs[i].msr;
		e->value = msrs[i].guest;
	}
}

static void __svm_disable_intercept_for_msr(unsigned long *msr_bitmap, u32 msr)
{
	int f = sizeof(unsigned long);
	/*
	 * See Intel PRM Vol. 3, 20.6.9 (MSR-Bitmap Address). Early manuals
	 * have the write-low and read-high bitmap offsets the wrong way round.
	 * We can control MSRs 0x00000000-0x00001fff and 0xc0000000-0xc0001fff.
	 */
	if (msr <= 0x1fff) {
		__clear_bit(msr, msr_bitmap + 0x000 / f); /* read-low */
		__clear_bit(msr, msr_bitmap + 0x800 / f); /* write-low */
	} else if ((msr >= 0xc0000000) && (msr <= 0xc0001fff)) {
		msr &= 0x1fff;
		__clear_bit(msr, msr_bitmap + 0x400 / f); /* read-high */
		__clear_bit(msr, msr_bitmap + 0xc00 / f); /* write-high */
	}
}

static void setup_msr(struct svm_vcpu *vcpu)
{
	/* XXX enable only MSRs in set */
	vmcs_write64(MSR_BITMAP, __pa(msr_bitmap));

	vmcs_write32(VM_EXIT_MSR_LOAD_COUNT, 0);
	vmcs_write32(VM_ENTRY_MSR_LOAD_COUNT, 0);

	vmcs_write64(VM_EXIT_MSR_LOAD_ADDR, __pa(vcpu->msr_autoload.host));
	vmcs_write64(VM_ENTRY_MSR_LOAD_ADDR, __pa(vcpu->msr_autoload.guest));
}

static inline void mark_all_dirty_orig(struct vmcb *vmcb)
{
	vmcb->control.clean = 0;
}

/* TPR and CR2 are always written before VMRUN */
#define VMCB_ALWAYS_DIRTY_MASK	((1U << VMCB_INTR) | (1U << VMCB_CR2))

static inline void mark_all_clean_orig(struct vmcb *vmcb)
{
	vmcb->control.clean = ((1 << VMCB_DIRTY_MAX) - 1)
			      & ~VMCB_ALWAYS_DIRTY_MASK;
}

static inline void mark_dirty_orig(struct vmcb *vmcb, int bit)
{
	vmcb->control.clean &= ~(1 << bit);
}

static void recalc_intercepts_orig(struct vcpu_svm *svm)
{
	struct vmcb_control_area *c, *h;
	struct nested_state *g;

	mark_dirty(svm->vmcb, VMCB_INTERCEPTS);

	if (!is_guest_mode(&svm->vcpu))
		return;

	c = &svm->vmcb->control;
	h = &svm->nested.hsave->control;
	g = &svm->nested;

	c->intercept_cr = h->intercept_cr | g->intercept_cr;
	c->intercept_dr = h->intercept_dr | g->intercept_dr;
	c->intercept_exceptions = h->intercept_exceptions | g->intercept_exceptions;
	c->intercept = h->intercept | g->intercept;
}

static inline struct vmcb *get_host_vmcb_orig(struct vcpu_svm *svm)
{
	if (is_guest_mode(&svm->vcpu))
		return svm->nested.hsave;
	else
		return svm->vmcb;
}

static inline void set_cr_intercept_orig(struct vcpu_svm *svm, int bit)
{
	struct vmcb *vmcb = get_host_vmcb_orig(svm);

	vmcb->control.intercept_cr |= (1U << bit);

	recalc_intercepts_orig(svm);
}

static inline void clr_cr_intercept_orig(struct vcpu_svm *svm, int bit)
{
	struct vmcb *vmcb = get_host_vmcb_orig(svm);

	vmcb->control.intercept_cr &= ~(1U << bit);

	recalc_intercepts_orig(svm);
}

static inline bool is_cr_intercept_orig(struct vcpu_svm *svm, int bit)
{
	struct vmcb *vmcb = get_host_vmcb_orig(svm);

	return vmcb->control.intercept_cr & (1U << bit);
}

static inline void set_exception_intercept_orig(struct vcpu_svm *svm, int bit)
{
	struct vmcb *vmcb = get_host_vmcb_orig(svm);

	vmcb->control.intercept_exceptions |= (1U << bit);

	recalc_intercepts_orig(svm);
}

static inline void clr_exception_intercept_orig(struct vcpu_svm *svm, int bit)
{
	struct vmcb *vmcb = get_host_vmcb_orig(svm);

	vmcb->control.intercept_exceptions &= ~(1U << bit);

	recalc_intercepts_orig(svm);
}

static inline void set_intercept_orig(struct vcpu_svm *svm, int bit)
{
	struct vmcb *vmcb = get_host_vmcb_orig(svm);

	vmcb->control.intercept |= (1ULL << bit);

	recalc_intercepts_orig(svm);
}

static inline void clr_intercept_orig(struct vcpu_svm *svm, int bit)
{
	struct vmcb *vmcb = get_host_vmcb_orig(svm);

	vmcb->control.intercept &= ~(1ULL << bit);

	recalc_intercepts_orig(svm);
}

static inline void enable_gif_orig(struct vcpu_svm *svm)
{
	svm->vcpu.arch.hflags |= HF_GIF_MASK;
}

static inline void disable_gif_orig(struct vcpu_svm *svm)
{
	svm->vcpu.arch.hflags &= ~HF_GIF_MASK;
}

static inline bool gif_set_orig(struct vcpu_svm *svm)
{
	return !!(svm->vcpu.arch.hflags & HF_GIF_MASK);
}

static void update_cr0_intercept_orig(struct vcpu_svm *svm)
{
	ulong gcr0 = svm->vcpu.arch.cr0;
	u64 *hcr0 = &svm->vmcb->save.cr0;

	*hcr0 = (*hcr0 & ~SVM_CR0_SELECTIVE_MASK)
		| (gcr0 & SVM_CR0_SELECTIVE_MASK);

	mark_dirty_orig(svm->vmcb, VMCB_CR);

	if (gcr0 == *hcr0) {
		clr_cr_intercept_orig(svm, INTERCEPT_CR0_READ);
		clr_cr_intercept_orig(svm, INTERCEPT_CR0_WRITE);
	} else {
		set_cr_intercept_orig(svm, INTERCEPT_CR0_READ);
		set_cr_intercept_orig(svm, INTERCEPT_CR0_WRITE);
	}
}

static void svm_set_cr0_orig(struct kvm_vcpu *vcpu, unsigned long cr0)
{
	struct vcpu_svm *svm = to_svm(vcpu);

#ifdef CONFIG_X86_64
	if (vcpu->arch.efer & EFER_LME) {
		if (!is_paging(vcpu) && (cr0 & X86_CR0_PG)) {
			vcpu->arch.efer |= EFER_LMA;
			svm->vmcb->save.efer |= EFER_LMA | EFER_LME;
		}

		if (is_paging(vcpu) && !(cr0 & X86_CR0_PG)) {
			vcpu->arch.efer &= ~EFER_LMA;
			svm->vmcb->save.efer &= ~(EFER_LMA | EFER_LME);
		}
	}
#endif
	vcpu->arch.cr0 = cr0;

	if (!npt_enabled)
		cr0 |= X86_CR0_PG | X86_CR0_WP;

	/*
	 * re-enable caching here because the QEMU bios
	 * does not do it - this results in some delay at
	 * reboot
	 */
	if (kvm_check_has_quirk(vcpu->kvm, KVM_X86_QUIRK_CD_NW_CLEARED))
		cr0 &= ~(X86_CR0_CD | X86_CR0_NW);
	svm->vmcb->save.cr0 = cr0;
	mark_dirty_orig(svm->vmcb, VMCB_CR);
	update_cr0_intercept_orig(svm);
}

static void init_seg_orig(struct vmcb_seg *seg)
{
	seg->selector = 0;
	seg->attrib = SVM_SELECTOR_P_MASK | SVM_SELECTOR_S_MASK |
		      SVM_SELECTOR_WRITE_MASK; /* Read/Write Data Segment */
	seg->limit = 0xffff;
	seg->base = 0;
}

static void init_sys_seg_orig(struct vmcb_seg *seg, uint32_t type)
{
	seg->selector = 0;
	seg->attrib = SVM_SELECTOR_P_MASK | type;
	seg->limit = 0xffff;
	seg->base = 0;
}

static void svm_set_efer_orig(struct kvm_vcpu *vcpu, u64 efer)
{
	vcpu->arch.efer = efer;
	if (!npt_enabled && !(efer & EFER_LMA))
		efer &= ~EFER_LME;

	to_svm(vcpu)->vmcb->save.efer = efer | EFER_SVME;
	mark_dirty_orig(to_svm(vcpu)->vmcb, VMCB_CR);
}

#define SEG_TYPE_LDT 2
#define SEG_TYPE_BUSY_TSS16 3

static void init_vmcb_orig(struct vcpu_svm *svm)
{
	struct vmcb_control_area *control = &svm->vmcb->control;
	struct vmcb_save_area *save = &svm->vmcb->save;

	svm->vcpu.arch.hflags = 0;

	set_cr_intercept_orig(svm, INTERCEPT_CR0_READ);
	set_cr_intercept_orig(svm, INTERCEPT_CR3_READ);
	set_cr_intercept_orig(svm, INTERCEPT_CR4_READ);
	set_cr_intercept_orig(svm, INTERCEPT_CR0_WRITE);
	set_cr_intercept_orig(svm, INTERCEPT_CR3_WRITE);
	set_cr_intercept_orig(svm, INTERCEPT_CR4_WRITE);
	if (!kvm_vcpu_apicv_active(&svm->vcpu))
		set_cr_intercept_orig(svm, INTERCEPT_CR8_WRITE);

	set_dr_intercepts_orig(svm);

	set_exception_intercept_orig(svm, PF_VECTOR);
	set_exception_intercept_orig(svm, UD_VECTOR);
	set_exception_intercept_orig(svm, MC_VECTOR);
	set_exception_intercept_orig(svm, AC_VECTOR);
	set_exception_intercept_orig(svm, DB_VECTOR);

	set_intercept_orig(svm, INTERCEPT_INTR);
	set_intercept_orig(svm, INTERCEPT_NMI);
	set_intercept_orig(svm, INTERCEPT_SMI);
	set_intercept_orig(svm, INTERCEPT_SELECTIVE_CR0);
	set_intercept_orig(svm, INTERCEPT_RDPMC);
	set_intercept_orig(svm, INTERCEPT_CPUID);
	set_intercept_orig(svm, INTERCEPT_INVD);
	set_intercept_orig(svm, INTERCEPT_HLT);
	set_intercept_orig(svm, INTERCEPT_INVLPG);
	set_intercept_orig(svm, INTERCEPT_INVLPGA);
	set_intercept_orig(svm, INTERCEPT_IOIO_PROT);
	set_intercept_orig(svm, INTERCEPT_MSR_PROT);
	set_intercept_orig(svm, INTERCEPT_TASK_SWITCH);
	set_intercept_orig(svm, INTERCEPT_SHUTDOWN);
	set_intercept_orig(svm, INTERCEPT_VMRUN);
	set_intercept_orig(svm, INTERCEPT_VMMCALL);
	set_intercept_orig(svm, INTERCEPT_VMLOAD);
	set_intercept_orig(svm, INTERCEPT_VMSAVE);
	set_intercept_orig(svm, INTERCEPT_STGI);
	set_intercept_orig(svm, INTERCEPT_CLGI);
	set_intercept_orig(svm, INTERCEPT_SKINIT);
	set_intercept_orig(svm, INTERCEPT_WBINVD);
	set_intercept_orig(svm, INTERCEPT_XSETBV);

	if (!kvm_mwait_in_guest()) {
		set_intercept_orig(svm, INTERCEPT_MONITOR);
		set_intercept_orig(svm, INTERCEPT_MWAIT);
	}

	control->iopm_base_pa = iopm_base;
	control->msrpm_base_pa = __pa(svm->msrpm);
	control->int_ctl = V_INTR_MASKING_MASK;

	init_seg_orig(&save->es);
	init_seg_orig(&save->ss);
	init_seg_orig(&save->ds);
	init_seg_orig(&save->fs);
	init_seg_orig(&save->gs);

	save->cs.selector = 0xf000;
	save->cs.base = 0xffff0000;
	/* Executable/Readable Code Segment */
	save->cs.attrib = SVM_SELECTOR_READ_MASK | SVM_SELECTOR_P_MASK |
			  SVM_SELECTOR_S_MASK | SVM_SELECTOR_CODE_MASK;
	save->cs.limit = 0xffff;

	save->gdtr.limit = 0xffff;
	save->idtr.limit = 0xffff;

	init_sys_seg_orig(&save->ldtr, SEG_TYPE_LDT);
	init_sys_seg_orig(&save->tr, SEG_TYPE_BUSY_TSS16);

	svm_set_efer_orig(&svm->vcpu, 0);
	save->dr6 = 0xffff0ff0;
	kvm_set_rflags(&svm->vcpu, 2);
	save->rip = 0x0000fff0;
	svm->vcpu.arch.regs[VCPU_REGS_RIP] = save->rip;

	/*
	 * svm_set_cr0() sets PG and WP and clears NW and CD on save->cr0.
	 * It also updates the guest-visible cr0 value.
	 */
	svm_set_cr0_orig(&svm->vcpu, X86_CR0_NW | X86_CR0_CD | X86_CR0_ET);
	kvm_mmu_reset_context(&svm->vcpu);

	save->cr4 = X86_CR4_PAE;
	/* rdx = ?? */

	if (npt_enabled) {
		/* Setup VMCB for Nested Paging */
		control->nested_ctl = 1;
		clr_intercept_orig(svm, INTERCEPT_INVLPG);
		clr_exception_intercept_orig(svm, PF_VECTOR);
		clr_cr_intercept_orig(svm, INTERCEPT_CR3_READ);
		clr_cr_intercept_orig(svm, INTERCEPT_CR3_WRITE);
		save->g_pat = svm->vcpu.arch.pat;
		save->cr3 = 0;
		save->cr4 = 0;
	}
	svm->asid_generation = 0;

	svm->nested.vmcb = 0;
	svm->vcpu.arch.hflags = 0;

	if (boot_cpu_has(X86_FEATURE_PAUSEFILTER)) {
		control->pause_filter_count = 3000;
		set_intercept_orig(svm, INTERCEPT_PAUSE);
	}

	if (avic)
		avic_init_vmcb(svm);

	mark_all_dirty_orig(svm->vmcb);

	enable_gif_orig(svm);

}

/**
 *  svm_setup_vmcs - configures the vmcs with starting parameters
 */
static void svm_setup_vmcs(struct svm_vcpu *vcpu)
{
	vmcs_write16(VIRTUAL_PROCESSOR_ID, vcpu->vpid);
	vmcs_write64(VMCS_LINK_POINTER, -1ull); /* 22.3.1.5 */

	/* Control */
	vmcs_write32(PIN_BASED_VM_EXEC_CONTROL,
		     vmcs_config.pin_based_exec_ctrl);

	vmcs_write32(CPU_BASED_VM_EXEC_CONTROL,
		     vmcs_config.cpu_based_exec_ctrl);

	if (cpu_has_secondary_exec_ctrls()) {
		vmcs_write32(SECONDARY_VM_EXEC_CONTROL,
			     vmcs_config.cpu_based_2nd_exec_ctrl);
	}

	vmcs_write64(EPT_POINTER, vcpu->nptp);

	vmcs_write32(PAGE_FAULT_ERROR_CODE_MASK, 0);
	vmcs_write32(PAGE_FAULT_ERROR_CODE_MATCH, 0);
	vmcs_write32(CR3_TARGET_COUNT, 0);           /* 22.2.1 */

	setup_msr(vcpu);
#if 0
	if (vmcs_config.vmentry_ctrl & VM_ENTRY_LOAD_IA32_PAT) {
		u32 msr_low, msr_high;
		u64 host_pat;
		rdmsr(MSR_IA32_CR_PAT, msr_low, msr_high);
		host_pat = msr_low | ((u64) msr_high << 32);
		/* Write the default value follow host pat */
		vmcs_write64(GUEST_IA32_PAT, host_pat);
		/* Keep arch.pat sync with GUEST_IA32_PAT */
		vmx->vcpu.arch.pat = host_pat;
	}

	for (i = 0; i < NR_VMX_MSR; ++i) {
		u32 index = vmx_msr_index[i];
		u32 data_low, data_high;
		int j = vmx->nmsrs;

		if (rdmsr_safe(index, &data_low, &data_high) < 0)
			continue;
		if (wrmsr_safe(index, data_low, data_high) < 0)
			continue;
		vmx->guest_msrs[j].index = i;
		vmx->guest_msrs[j].data = 0;
		vmx->guest_msrs[j].mask = -1ull;
		++vmx->nmsrs;
	}
#endif

	vmcs_config.vmentry_ctrl |= VM_ENTRY_IA32E_MODE;

	vmcs_write32(VM_EXIT_CONTROLS, vmcs_config.vmexit_ctrl);
	vmcs_write32(VM_ENTRY_CONTROLS, vmcs_config.vmentry_ctrl);

	vmcs_writel(CR0_GUEST_HOST_MASK, ~0ul);
	vmcs_writel(CR4_GUEST_HOST_MASK, ~0ul);

	//kvm_write_tsc(&vmx->vcpu, 0);
	vmcs_writel(TSC_OFFSET, 0);

	vmcs_write32(EXCEPTION_BITMAP, 1 << X86_TRAP_DB | 1 << X86_TRAP_BP);

	vmx_setup_constant_host_state();
}

static void new_asid_orig(struct vcpu_svm *svm, struct svm_cpu_data *sd)
{
	if (sd->next_asid > sd->max_asid) {
		++sd->asid_generation;
		sd->next_asid = 1;
		svm->vmcb->control.tlb_ctl = TLB_CONTROL_FLUSH_ALL_ASID;
	}

	svm->asid_generation = sd->asid_generation;
	svm->vmcb->control.asid = sd->next_asid++;

	mark_dirty(svm->vmcb, VMCB_ASID);
}

/**
 * svm_allocate_vpid - reserves a vpid and sets it in the VCPU
 * @vmx: the VCPU
 */
static int svm_allocate_vpid(struct svm_vcpu *svm)
{
	int vpid;

	svm->vpid = 0;

	spin_lock(&svm_vpid_lock);
	vpid = find_first_zero_bit(svm_vpid_bitmap, VMX_NR_VPIDS);
	if (vpid < VMX_NR_VPIDS) {
		svm->vpid = vpid;
		__set_bit(vpid, svm_vpid_bitmap);
	}
	spin_unlock(&svm_vpid_lock);

	return vpid >= VMX_NR_VPIDS;
}

/**
 * vmx_free_vpid - frees a vpid
 * @vmx: the VCPU
 */
static void svm_free_vpid(struct svm_vcpu *svm)
{
	spin_lock(&svm_vpid_lock);
	if (svm->vpid != 0)
		__clear_bit(svm->vpid, svm_vpid_bitmap);
	spin_unlock(&svm_vpid_lock);
}

/**
 * vmx_setup_registers - setup general purpose registers
 */
static void svm_setup_registers(struct svm_vcpu *vcpu, struct dune_config *conf)
{
	vcpu->regs[VCPU_REGS_RAX] = conf->rax;
	vcpu->regs[VCPU_REGS_RBX] = conf->rbx;
	vcpu->regs[VCPU_REGS_RCX] = conf->rcx;
	vcpu->regs[VCPU_REGS_RDX] = conf->rdx;
	vcpu->regs[VCPU_REGS_RSI] = conf->rsi;
	vcpu->regs[VCPU_REGS_RDI] = conf->rdi;
	vcpu->regs[VCPU_REGS_RBP] = conf->rbp;
	vcpu->regs[VCPU_REGS_R8]  = conf->r8;
	vcpu->regs[VCPU_REGS_R9]  = conf->r9;
	vcpu->regs[VCPU_REGS_R10] = conf->r10;
	vcpu->regs[VCPU_REGS_R11] = conf->r11;
	vcpu->regs[VCPU_REGS_R12] = conf->r12;
	vcpu->regs[VCPU_REGS_R13] = conf->r13;
	vcpu->regs[VCPU_REGS_R14] = conf->r14;
	vcpu->regs[VCPU_REGS_R15] = conf->r15;

	vmcs_writel(GUEST_RIP, conf->rip);
	vmcs_writel(GUEST_RSP, conf->rsp);
	vmcs_writel(GUEST_RFLAGS, conf->rflags);
}

/**
 * vmx_copy_registers_to_conf - copy registers to dune_config
 */
static void svm_copy_registers_to_conf(struct svm_vcpu *vcpu, struct dune_config *conf)
{
	conf->rax = vcpu->regs[VCPU_REGS_RAX];
	conf->rbx = vcpu->regs[VCPU_REGS_RBX];
	conf->rcx = vcpu->regs[VCPU_REGS_RCX];
	conf->rdx = vcpu->regs[VCPU_REGS_RDX];
	conf->rsi = vcpu->regs[VCPU_REGS_RSI];
	conf->rdi = vcpu->regs[VCPU_REGS_RDI];
	conf->rbp = vcpu->regs[VCPU_REGS_RBP];
	conf->r8 = vcpu->regs[VCPU_REGS_R8];
	conf->r9 = vcpu->regs[VCPU_REGS_R9];
	conf->r10 = vcpu->regs[VCPU_REGS_R10];
	conf->r11 = vcpu->regs[VCPU_REGS_R11];
	conf->r12 = vcpu->regs[VCPU_REGS_R12];
	conf->r13 = vcpu->regs[VCPU_REGS_R13];
	conf->r14 = vcpu->regs[VCPU_REGS_R14];
	conf->r15 = vcpu->regs[VCPU_REGS_R15];
	conf->rip = vmcs_readl(GUEST_RIP);
	conf->rsp = vmcs_readl(GUEST_RSP);
	conf->rflags = vmcs_readl(GUEST_RFLAGS);
}

static void svm_vcpu_init_msrpm_orig(u32 *msrpm)
{
	int i;

	memset(msrpm, 0xff, PAGE_SIZE * (1 << MSRPM_ALLOC_ORDER));

	for (i = 0; direct_access_msrs[i].index != MSR_INVALID; i++) {
		if (!direct_access_msrs[i].always)
			continue;

		set_msr_interception(msrpm, direct_access_msrs[i].index, 1, 1);
	}
}

static struct kvm_vcpu *svm_create_vcpu_orig(struct kvm *kvm, unsigned int id)
{
	struct vcpu_svm *svm;
	struct page *page;
	struct page *msrpm_pages;
	struct page *hsave_page;
	struct page *nested_msrpm_pages;
	int err;

	svm = kmem_cache_zalloc(kvm_vcpu_cache, GFP_KERNEL);
	if (!svm) {
		err = -ENOMEM;
		goto out;
	}

	err = kvm_vcpu_init(&svm->vcpu, kvm, id);
	if (err)
		goto free_svm;

	err = -ENOMEM;
	page = alloc_page(GFP_KERNEL);
	if (!page)
		goto uninit;

	msrpm_pages = alloc_pages(GFP_KERNEL, MSRPM_ALLOC_ORDER);
	if (!msrpm_pages)
		goto free_page1;

	nested_msrpm_pages = alloc_pages(GFP_KERNEL, MSRPM_ALLOC_ORDER);
	if (!nested_msrpm_pages)
		goto free_page2;

	hsave_page = alloc_page(GFP_KERNEL);
	if (!hsave_page)
		goto free_page3;

	if (avic) {
		err = avic_init_backing_page(&svm->vcpu);
		if (err)
			goto free_page4;

		INIT_LIST_HEAD(&svm->ir_list);
		spin_lock_init(&svm->ir_list_lock);
	}

	/* We initialize this flag to true to make sure that the is_running
	 * bit would be set the first time the vcpu is loaded.
	 */
	svm->avic_is_running = true;

	svm->nested.hsave = page_address(hsave_page);

	svm->msrpm = page_address(msrpm_pages);
	svm_vcpu_init_msrpm_orig(svm->msrpm);

	svm->nested.msrpm = page_address(nested_msrpm_pages);
	svm_vcpu_init_msrpm_orig(svm->nested.msrpm);

	svm->vmcb = page_address(page);
	clear_page(svm->vmcb);
	svm->vmcb_pa = page_to_pfn(page) << PAGE_SHIFT;
	svm->asid_generation = 0;
	init_vmcb_orig(svm);

	svm_init_osvw(&svm->vcpu);

	return &svm->vcpu;

	free_page4:
	__free_page(hsave_page);
	free_page3:
	__free_pages(nested_msrpm_pages, MSRPM_ALLOC_ORDER);
	free_page2:
	__free_pages(msrpm_pages, MSRPM_ALLOC_ORDER);
	free_page1:
	__free_page(page);
	uninit:
	kvm_vcpu_uninit(&svm->vcpu);
	free_svm:
	kmem_cache_free(kvm_vcpu_cache, svm);
	out:
	return ERR_PTR(err);
}

/**
 * svm_create_vcpu - allocates and initializes a new virtual cpu
 *
 * Returns: A new VCPU structure
 */
static struct svm_vcpu * svm_create_vcpu(struct dune_config *conf)
{
	struct svm_vcpu *vcpu;

	if (conf->vcpu) {
		/* This Dune configuration already has a VCPU. */
		vcpu = (struct svm_vcpu *) conf->vcpu;
		svm_get_cpu(vcpu);
		svm_setup_registers(vcpu, conf);
		svm_put_cpu(vcpu);
		return vcpu;
	}

	vcpu = kmalloc(sizeof(struct svm_vcpu), GFP_KERNEL);
	if (!vcpu)
		return NULL;

	memset(vcpu, 0, sizeof(*vcpu));

	list_add(&vcpu->list, &vcpus);

	vcpu->conf = conf;
	conf->vcpu = (u64) vcpu;

	vcpu->vmcs = svm_alloc_vmcs();
	if (!vcpu->vmcs)
		goto fail_vmcs;

	if (svm_allocate_vpid(vcpu))
		goto fail_vpid;

	vcpu->cpu = -1;
	vcpu->syscall_tbl = (void *) &dune_syscall_tbl;

	spin_lock_init(&vcpu->npt_lock);
	if (svm_init_npt(vcpu))
		goto fail_npt;
	vcpu->nptp = construct_nptp(vcpu->npt_root);

	svm_get_cpu(vcpu);
	svm_setup_vmcs(vcpu);
	svm_setup_initial_guest_state(conf);
	svm_setup_registers(vcpu, conf);
	svm_put_cpu(vcpu);

	if (cpu_has_svm_npt_ad_bits()) {
		vcpu->npt_ad_enabled = true;
		printk(KERN_INFO "svm: enabled NPT A/D bits");
	}
	if (svm_create_npt(vcpu))
		goto fail_npt;

	return vcpu;

	fail_npt:
	svm_free_vpid(vcpu);
	fail_vpid:
	svm_free_vmcs(vcpu->vmcs);
	fail_vmcs:
	kfree(vcpu);
	return NULL;
}

static void svm_vcpu_reset_orig(struct kvm_vcpu *vcpu, bool init_event)
{
	struct vcpu_svm *svm = to_svm(vcpu);
	u32 dummy;
	u32 eax = 1;

	if (!init_event) {
		svm->vcpu.arch.apic_base = APIC_DEFAULT_PHYS_BASE |
					   MSR_IA32_APICBASE_ENABLE;
		if (kvm_vcpu_is_reset_bsp(&svm->vcpu))
			svm->vcpu.arch.apic_base |= MSR_IA32_APICBASE_BSP;
	}
	init_vmcb_orig(svm);

	kvm_cpuid(vcpu, &eax, &dummy, &dummy, &dummy);
	kvm_register_write(vcpu, VCPU_REGS_RDX, eax);

	if (kvm_vcpu_apicv_active(vcpu) && !init_event)
		avic_update_vapic_bar(svm, APIC_DEFAULT_PHYS_BASE);
}

static void svm_free_vcpu_orig(struct kvm_vcpu *vcpu)
{
	struct vcpu_svm *svm = to_svm(vcpu);

	__free_page(pfn_to_page(svm->vmcb_pa >> PAGE_SHIFT));
	__free_pages(virt_to_page(svm->msrpm), MSRPM_ALLOC_ORDER);
	__free_page(virt_to_page(svm->nested.hsave));
	__free_pages(virt_to_page(svm->nested.msrpm), MSRPM_ALLOC_ORDER);
	kvm_vcpu_uninit(vcpu);
	kmem_cache_free(kvm_vcpu_cache, svm);
}

/**
 * svm_destroy_vcpu - destroys and frees an existing virtual cpu
 * @vcpu: the VCPU to destroy
 */
static void svm_destroy_vcpu(struct svm_vcpu *vcpu)
{
	svm_destroy_npt(vcpu);
	svm_get_cpu(vcpu);
	npt_sync_context(vcpu->nptp);
	vmcs_clear(vcpu->vmcs);
	this_cpu_write(local_vcpu, NULL);
	svm_put_cpu(vcpu);
	svm_free_vpid(vcpu);
	svm_free_vmcs(vcpu->vmcs);
	kfree(vcpu);
}

void svm_cleanup(void)
{
	struct svm_vcpu *vcpu, *tmp;

	list_for_each_entry_safe(vcpu, tmp, &vcpus, list) {
		printk(KERN_ERR "svm: destroying VCPU (VPID %d)\n",
		       vcpu->vpid);
		list_del(&vcpu->list);
		svm_destroy_vcpu(vcpu);
	}
}

static int dune_exit(int error_code)
{
	struct svm_vcpu *vcpu;

	/* FIXME: not totally safe depending on GCC */
	asm("movq %%r11, %0" : "=r"(vcpu));

	vcpu->shutdown = 1;
	vcpu->ret_code = DUNE_RET_EXIT;
	vcpu->conf->status = error_code;

	return 0;
}

static int dune_exit_group(int error_code)
{
	/* NOTE: we're supposed to send a signal to other threads before
	 * exiting. Because we don't yet support signals we do nothing
	 * extra for now.
	 */
	struct svm_vcpu *vcpu;

	/* FIXME: not totally safe depending on GCC */
	asm("movq %%r11, %0" : "=r"(vcpu));

	vcpu->shutdown = 1;
	vcpu->ret_code = DUNE_RET_EXIT;
	vcpu->conf->status = error_code;

	return 0;
}

static void make_pt_regs(struct svm_vcpu *vcpu, struct pt_regs *regs,
			 int sysnr)
{
	regs->ax = sysnr;
	regs->orig_ax = vcpu->regs[VCPU_REGS_RAX];
	regs->bx = vcpu->regs[VCPU_REGS_RBX];
	regs->cx = vcpu->regs[VCPU_REGS_RCX];
	regs->dx = vcpu->regs[VCPU_REGS_RDX];
	regs->si = vcpu->regs[VCPU_REGS_RSI];
	regs->di = vcpu->regs[VCPU_REGS_RDI];
	regs->r8 = vcpu->regs[VCPU_REGS_R8];
	regs->r9 = vcpu->regs[VCPU_REGS_R9];
	regs->r10 = vcpu->regs[VCPU_REGS_R10];
	regs->r11 = vcpu->regs[VCPU_REGS_R11];
	regs->r12 = vcpu->regs[VCPU_REGS_R12];
	regs->r13 = vcpu->regs[VCPU_REGS_R13];
	regs->r14 = vcpu->regs[VCPU_REGS_R14];
	regs->r15 = vcpu->regs[VCPU_REGS_R15];
	regs->bp = vcpu->regs[VCPU_REGS_RBP];

	svm_get_cpu(vcpu);
	regs->ip = vmcs_readl(GUEST_RIP);
	regs->sp = vmcs_readl(GUEST_RSP);
	/* FIXME: do we need to set up other flags? */
	regs->flags = (vmcs_readl(GUEST_RFLAGS) & 0xFF) |
		      X86_EFLAGS_IF | 0x2;
	svm_put_cpu(vcpu);

	/*
	 * NOTE: Since Dune processes use the kernel's LSTAR
	 * syscall address, we need special logic to handle
	 * certain system calls (fork, clone, etc.) The specifc
	 * issue is that we can not jump to a high address
	 * in a child process since it is not running in Dune.
	 * Our solution is to adopt a special Dune convention
	 * where the desired %RIP address is provided in %RCX.
	 */
	if (!(__addr_ok(regs->ip)))
		regs->ip = regs->cx;

	regs->cs = __USER_CS;
	regs->ss = __USER_DS;
}

#if LINUX_VERSION_CODE >= KERNEL_VERSION(4,1,0)
static long dune_sys_clone(unsigned long clone_flags, unsigned long newsp,
			   void __user *parent_tid, void __user *child_tid,
			   unsigned long tls)
{
	struct svm_vcpu *vcpu;
	struct pt_regs regs;

	asm("movq %%r11, %0" : "=r"(vcpu));

	make_pt_regs(vcpu, &regs, __NR_clone);
	if (!newsp)
		newsp = regs.sp;

	return dune_do_fork(clone_flags, newsp, &regs, 0, parent_tid, child_tid,
			    tls);
}
#else
static long dune_sys_clone(unsigned long clone_flags, unsigned long newsp,
		void __user *parent_tid, void __user *child_tid)
{
	struct svm_vcpu *vcpu;
	struct pt_regs regs;

	asm("movq %%r11, %0" : "=r"(vcpu));

	make_pt_regs(vcpu, &regs, __NR_clone);
	if (!newsp)
		newsp = regs.sp;

	return dune_do_fork(clone_flags, newsp, &regs, 0, parent_tid, child_tid,
			    0);
}
#endif

static long dune_sys_fork(void)
{
	struct svm_vcpu *vcpu;
	struct pt_regs regs;

	asm("movq %%r11, %0" : "=r"(vcpu));

	make_pt_regs(vcpu, &regs, __NR_fork);

	return dune_do_fork(SIGCHLD, regs.sp, &regs, 0, NULL, NULL, 0);
}

static long dune_sys_vfork(void)
{
	struct svm_vcpu *vcpu;
	struct pt_regs regs;

	asm("movq %%r11, %0" : "=r"(vcpu));

	make_pt_regs(vcpu, &regs, __NR_vfork);

	return dune_do_fork(CLONE_VFORK | CLONE_VM | SIGCHLD, regs.sp,
			    &regs, 0, NULL, NULL, 0);
}

static void svm_init_syscall(void)
{
	memcpy(dune_syscall_tbl, (void *) SYSCALL_TBL,
	       sizeof(sys_call_ptr_t) * NUM_SYSCALLS);

	dune_syscall_tbl[__NR_exit] = (void *) &dune_exit;
	dune_syscall_tbl[__NR_exit_group] = (void *) &dune_exit_group;
	dune_syscall_tbl[__NR_clone] = (void *) &dune_sys_clone;
	dune_syscall_tbl[__NR_fork] = (void *) &dune_sys_fork;
	dune_syscall_tbl[__NR_vfork] = (void *) &dune_sys_vfork;
}

static inline void clgi_orig(void)
{
	asm volatile (__ex(SVM_CLGI));
}

static inline void stgi_orig(void)
{
	asm volatile (__ex(SVM_STGI));
}

static void reload_tss_orig(struct kvm_vcpu *vcpu)
{
	int cpu = raw_smp_processor_id();

	struct svm_cpu_data *sd = per_cpu(svm_data, cpu);
	sd->tss_desc->type = 9; /* available 32/64-bit TSS */
	load_TR_desc();
}

static void pre_svm_run_orig(struct vcpu_svm *svm)
{
	int cpu = raw_smp_processor_id();

	struct svm_cpu_data *sd = per_cpu(svm_data, cpu);

	/* FIXME: handle wraparound of asid_generation */
	if (svm->asid_generation != sd->asid_generation)
		new_asid(svm, sd);
}

static void svm_vcpu_run_orig(struct kvm_vcpu *vcpu)
{
	struct vcpu_svm *svm = to_svm(vcpu);

	svm->vmcb->save.rax = vcpu->arch.regs[VCPU_REGS_RAX];
	svm->vmcb->save.rsp = vcpu->arch.regs[VCPU_REGS_RSP];
	svm->vmcb->save.rip = vcpu->arch.regs[VCPU_REGS_RIP];

	/*
	 * A vmexit emulation is required before the vcpu can be executed
	 * again.
	 */
	if (unlikely(svm->nested.exit_required))
		return;

	pre_svm_run_orig(svm);

	sync_lapic_to_cr8(vcpu);

	svm->vmcb->save.cr2 = vcpu->arch.cr2;

	clgi_orig();

	local_irq_enable();

	asm volatile (
	"push %%" _ASM_BP "; \n\t"
		"mov %c[rbx](%[svm]), %%" _ASM_BX " \n\t"
		"mov %c[rcx](%[svm]), %%" _ASM_CX " \n\t"
		"mov %c[rdx](%[svm]), %%" _ASM_DX " \n\t"
		"mov %c[rsi](%[svm]), %%" _ASM_SI " \n\t"
		"mov %c[rdi](%[svm]), %%" _ASM_DI " \n\t"
		"mov %c[rbp](%[svm]), %%" _ASM_BP " \n\t"
#ifdef CONFIG_X86_64
		"mov %c[r8](%[svm]),  %%r8  \n\t"
		"mov %c[r9](%[svm]),  %%r9  \n\t"
		"mov %c[r10](%[svm]), %%r10 \n\t"
		"mov %c[r11](%[svm]), %%r11 \n\t"
		"mov %c[r12](%[svm]), %%r12 \n\t"
		"mov %c[r13](%[svm]), %%r13 \n\t"
		"mov %c[r14](%[svm]), %%r14 \n\t"
		"mov %c[r15](%[svm]), %%r15 \n\t"
#endif

		/* Enter guest mode */
		"push %%" _ASM_AX " \n\t"
		"mov %c[vmcb](%[svm]), %%" _ASM_AX " \n\t"
	__ex(SVM_VMLOAD) "\n\t"
	__ex(SVM_VMRUN) "\n\t"
	__ex(SVM_VMSAVE) "\n\t"
		"pop %%" _ASM_AX " \n\t"

		/* Save guest registers, load host registers */
		"mov %%" _ASM_BX ", %c[rbx](%[svm]) \n\t"
		"mov %%" _ASM_CX ", %c[rcx](%[svm]) \n\t"
		"mov %%" _ASM_DX ", %c[rdx](%[svm]) \n\t"
		"mov %%" _ASM_SI ", %c[rsi](%[svm]) \n\t"
		"mov %%" _ASM_DI ", %c[rdi](%[svm]) \n\t"
		"mov %%" _ASM_BP ", %c[rbp](%[svm]) \n\t"
#ifdef CONFIG_X86_64
		"mov %%r8,  %c[r8](%[svm]) \n\t"
		"mov %%r9,  %c[r9](%[svm]) \n\t"
		"mov %%r10, %c[r10](%[svm]) \n\t"
		"mov %%r11, %c[r11](%[svm]) \n\t"
		"mov %%r12, %c[r12](%[svm]) \n\t"
		"mov %%r13, %c[r13](%[svm]) \n\t"
		"mov %%r14, %c[r14](%[svm]) \n\t"
		"mov %%r15, %c[r15](%[svm]) \n\t"
#endif
		"pop %%" _ASM_BP
	:
	: [svm]"a"(svm),
	[vmcb]"i"(offsetof(struct vcpu_svm, vmcb_pa)),
	[rbx]"i"(offsetof(struct vcpu_svm, vcpu.arch.regs[VCPU_REGS_RBX])),
	[rcx]"i"(offsetof(struct vcpu_svm, vcpu.arch.regs[VCPU_REGS_RCX])),
	[rdx]"i"(offsetof(struct vcpu_svm, vcpu.arch.regs[VCPU_REGS_RDX])),
	[rsi]"i"(offsetof(struct vcpu_svm, vcpu.arch.regs[VCPU_REGS_RSI])),
	[rdi]"i"(offsetof(struct vcpu_svm, vcpu.arch.regs[VCPU_REGS_RDI])),
	[rbp]"i"(offsetof(struct vcpu_svm, vcpu.arch.regs[VCPU_REGS_RBP]))
#ifdef CONFIG_X86_64
		, [r8]"i"(offsetof(struct vcpu_svm, vcpu.arch.regs[VCPU_REGS_R8])),
	[r9]"i"(offsetof(struct vcpu_svm, vcpu.arch.regs[VCPU_REGS_R9])),
	[r10]"i"(offsetof(struct vcpu_svm, vcpu.arch.regs[VCPU_REGS_R10])),
	[r11]"i"(offsetof(struct vcpu_svm, vcpu.arch.regs[VCPU_REGS_R11])),
	[r12]"i"(offsetof(struct vcpu_svm, vcpu.arch.regs[VCPU_REGS_R12])),
	[r13]"i"(offsetof(struct vcpu_svm, vcpu.arch.regs[VCPU_REGS_R13])),
	[r14]"i"(offsetof(struct vcpu_svm, vcpu.arch.regs[VCPU_REGS_R14])),
	[r15]"i"(offsetof(struct vcpu_svm, vcpu.arch.regs[VCPU_REGS_R15]))
#endif
	: "cc", "memory"
#ifdef CONFIG_X86_64
		, "rbx", "rcx", "rdx", "rsi", "rdi"
		, "r8", "r9", "r10", "r11" , "r12", "r13", "r14", "r15"
#else
	, "ebx", "ecx", "edx", "esi", "edi"
#endif
	);

#ifdef CONFIG_X86_64
	wrmsrl(MSR_GS_BASE, svm->host.gs_base);
#else
	loadsegment(fs, svm->host.fs);
#ifndef CONFIG_X86_32_LAZY_GS
	loadsegment(gs, svm->host.gs);
#endif
#endif

	reload_tss(vcpu);

	local_irq_disable();

	vcpu->arch.cr2 = svm->vmcb->save.cr2;
	vcpu->arch.regs[VCPU_REGS_RAX] = svm->vmcb->save.rax;
	vcpu->arch.regs[VCPU_REGS_RSP] = svm->vmcb->save.rsp;
	vcpu->arch.regs[VCPU_REGS_RIP] = svm->vmcb->save.rip;

	if (unlikely(svm->vmcb->control.exit_code == SVM_EXIT_NMI))
		kvm_before_handle_nmi(&svm->vcpu);

	stgi_orig();

	/* Any pending NMI will happen here */

	if (unlikely(svm->vmcb->control.exit_code == SVM_EXIT_NMI))
		kvm_after_handle_nmi(&svm->vcpu);

	sync_cr8_to_lapic(vcpu);

	svm->next_rip = 0;

	svm->vmcb->control.tlb_ctl = TLB_CONTROL_DO_NOTHING;

	/* if exit due to PF check for async PF */
	if (svm->vmcb->control.exit_code == SVM_EXIT_EXCP_BASE + PF_VECTOR)
		svm->apf_reason = kvm_read_and_reset_pf_reason();

	if (npt_enabled) {
		vcpu->arch.regs_avail &= ~(1 << VCPU_EXREG_PDPTR);
		vcpu->arch.regs_dirty &= ~(1 << VCPU_EXREG_PDPTR);
	}

	/*
	 * We need to handle MC intercepts here before the vcpu has a chance to
	 * change the physical cpu
	 */
	if (unlikely(svm->vmcb->control.exit_code ==
		     SVM_EXIT_EXCP_BASE + MC_VECTOR))
		svm_handle_mce(svm);

	mark_all_clean(svm->vmcb);
}

#ifdef CONFIG_X86_64
#define R "r"
#define Q "q"
#else
#define R "e"
#define Q "l"
#endif

/**
 * vmx_run_vcpu - launches the CPU into non-root mode
 * @vcpu: the vmx instance to launch
 */
static int __noclone svm_run_vcpu(struct svm_vcpu *vcpu)
{
	asm(
	/* Store host registers */
	"push %%"R"dx; push %%"R"bp;"
		"push %%"R"cx \n\t" /* placeholder for guest rcx */
		"push %%"R"cx \n\t"
		"cmp %%"R"sp, %c[host_rsp](%0) \n\t"
		"je 1f \n\t"
		"mov %%"R"sp, %c[host_rsp](%0) \n\t"
		ASM_VMX_VMWRITE_RSP_RDX "\n\t"
		"1: \n\t"
		/* Reload cr2 if changed */
		"mov %c[cr2](%0), %%"R"ax \n\t"
		"mov %%cr2, %%"R"dx \n\t"
		"cmp %%"R"ax, %%"R"dx \n\t"
		"je 2f \n\t"
		"mov %%"R"ax, %%cr2 \n\t"
		"2: \n\t"
		/* Check if vmlaunch of vmresume is needed */
		"cmpl $0, %c[launched](%0) \n\t"
		/* Load guest registers.  Don't clobber flags. */
		"mov %c[rax](%0), %%"R"ax \n\t"
		"mov %c[rbx](%0), %%"R"bx \n\t"
		"mov %c[rdx](%0), %%"R"dx \n\t"
		"mov %c[rsi](%0), %%"R"si \n\t"
		"mov %c[rdi](%0), %%"R"di \n\t"
		"mov %c[rbp](%0), %%"R"bp \n\t"
#ifdef CONFIG_X86_64
		"mov %c[r8](%0),  %%r8  \n\t"
		"mov %c[r9](%0),  %%r9  \n\t"
		"mov %c[r10](%0), %%r10 \n\t"
		"mov %c[r11](%0), %%r11 \n\t"
		"mov %c[r12](%0), %%r12 \n\t"
		"mov %c[r13](%0), %%r13 \n\t"
		"mov %c[r14](%0), %%r14 \n\t"
		"mov %c[r15](%0), %%r15 \n\t"
#endif
		"mov %c[rcx](%0), %%"R"cx \n\t" /* kills %0 (ecx) */

		/* Enter guest mode */
		"jne .Llaunched \n\t"
		ASM_VMX_VMLAUNCH "\n\t"
		"jmp .Lkvm_vmx_return \n\t"
		".Llaunched: " ASM_VMX_VMRESUME "\n\t"
		".Lkvm_vmx_return: "
		/* Save guest registers, load host registers, keep flags */
		"mov %0, %c[wordsize](%%"R"sp) \n\t"
		"pop %0 \n\t"
		"mov %%"R"ax, %c[rax](%0) \n\t"
		"mov %%"R"bx, %c[rbx](%0) \n\t"
		"pop"Q" %c[rcx](%0) \n\t"
		"mov %%"R"dx, %c[rdx](%0) \n\t"
		"mov %%"R"si, %c[rsi](%0) \n\t"
		"mov %%"R"di, %c[rdi](%0) \n\t"
		"mov %%"R"bp, %c[rbp](%0) \n\t"
#ifdef CONFIG_X86_64
		"mov %%r8,  %c[r8](%0) \n\t"
		"mov %%r9,  %c[r9](%0) \n\t"
		"mov %%r10, %c[r10](%0) \n\t"
		"mov %%r11, %c[r11](%0) \n\t"
		"mov %%r12, %c[r12](%0) \n\t"
		"mov %%r13, %c[r13](%0) \n\t"
		"mov %%r14, %c[r14](%0) \n\t"
		"mov %%r15, %c[r15](%0) \n\t"
#endif
		"mov %%rax, %%r10 \n\t"
		"mov %%rdx, %%r11 \n\t"

		"mov %%cr2, %%"R"ax   \n\t"
		"mov %%"R"ax, %c[cr2](%0) \n\t"

		"pop  %%"R"bp; pop  %%"R"dx \n\t"
		"setbe %c[fail](%0) \n\t"

		"mov $" __stringify(__USER_DS) ", %%rax \n\t"
		"mov %%rax, %%ds \n\t"
		"mov %%rax, %%es \n\t"
	: : "c"(vcpu), "d"((unsigned long)HOST_RSP),
	[launched]"i"(offsetof(struct svm_vcpu, launched)),
	[fail]"i"(offsetof(struct svm_vcpu, fail)),
	[host_rsp]"i"(offsetof(struct svm_vcpu, host_rsp)),
	[rax]"i"(offsetof(struct svm_vcpu, regs[VCPU_REGS_RAX])),
	[rbx]"i"(offsetof(struct svm_vcpu, regs[VCPU_REGS_RBX])),
	[rcx]"i"(offsetof(struct svm_vcpu, regs[VCPU_REGS_RCX])),
	[rdx]"i"(offsetof(struct svm_vcpu, regs[VCPU_REGS_RDX])),
	[rsi]"i"(offsetof(struct svm_vcpu, regs[VCPU_REGS_RSI])),
	[rdi]"i"(offsetof(struct svm_vcpu, regs[VCPU_REGS_RDI])),
	[rbp]"i"(offsetof(struct svm_vcpu, regs[VCPU_REGS_RBP])),
#ifdef CONFIG_X86_64
	[r8]"i"(offsetof(struct svm_vcpu, regs[VCPU_REGS_R8])),
	[r9]"i"(offsetof(struct svm_vcpu, regs[VCPU_REGS_R9])),
	[r10]"i"(offsetof(struct svm_vcpu, regs[VCPU_REGS_R10])),
	[r11]"i"(offsetof(struct svm_vcpu, regs[VCPU_REGS_R11])),
	[r12]"i"(offsetof(struct svm_vcpu, regs[VCPU_REGS_R12])),
	[r13]"i"(offsetof(struct svm_vcpu, regs[VCPU_REGS_R13])),
	[r14]"i"(offsetof(struct svm_vcpu, regs[VCPU_REGS_R14])),
	[r15]"i"(offsetof(struct svm_vcpu, regs[VCPU_REGS_R15])),
#endif
	[cr2]"i"(offsetof(struct svm_vcpu, cr2)),
	[wordsize]"i"(sizeof(ulong))
	: "cc", "memory"
		, R"ax", R"bx", R"di", R"si"
#ifdef CONFIG_X86_64
		, "r8", "r9", "r10", "r11", "r12", "r13", "r14", "r15"
#endif
	);

	vcpu->launched = 1;

	if (unlikely(vcpu->fail)) {
		printk(KERN_ERR "vmx: failure detected (err %x)\n",
		       vmcs_read32(VM_INSTRUCTION_ERROR));
		return VMX_EXIT_REASONS_FAILED_VMENTRY;
	}

	return vmcs_read32(VM_EXIT_REASON);

#if 0
	vmx->idt_vectoring_info = vmcs_read32(IDT_VECTORING_INFO_FIELD);
	vmx_complete_atomic_exit(vmx);
	vmx_recover_nmi_blocking(vmx);
	vmx_complete_interrupts(vmx);
#endif
}

static void svm_step_instruction(void)
{
	vmcs_writel(GUEST_RIP, vmcs_readl(GUEST_RIP) +
			       vmcs_read32(VM_EXIT_INSTRUCTION_LEN));
}

static int svm_handle_npt_violation(struct svm_vcpu *vcpu)
{
	unsigned long gva, gpa;
	int exit_qual, ret;

	svm_get_cpu(vcpu);
	exit_qual = vmcs_read32(EXIT_QUALIFICATION);
	gva = vmcs_readl(GUEST_LINEAR_ADDRESS);
	gpa = vmcs_read64(GUEST_PHYSICAL_ADDRESS);
	svm_put_cpu(vcpu);

	if (exit_qual & (1 << 6)) {
		printk(KERN_ERR "NPT: GPA 0x%lx exceeds GAW!\n", gpa);
		return -EINVAL;
	}

	if (!(exit_qual & (1 << 7))) {
		printk(KERN_ERR "NPT: linear address is not valid, GPA: 0x%lx!\n", gpa);
		return -EINVAL;
	}

	ret = svm_do_npt_fault(vcpu, gpa, gva, exit_qual);

	if (ret) {
		printk(KERN_ERR "svm: page fault failure "
			       "GPA: 0x%lx, GVA: 0x%lx\n",
		       gpa, gva);
		vcpu->ret_code = DUNE_RET_EPT_VIOLATION;
		svm_dump_cpu(vcpu);
	}

	return ret;
}

static void svm_handle_syscall(struct svm_vcpu *vcpu)
{
	__u64 orig_rax;

	if (unlikely(vcpu->regs[VCPU_REGS_RAX] > NUM_SYSCALLS)) {
		vcpu->regs[VCPU_REGS_RAX] = -EINVAL;
		return;
	}

	if (unlikely(vcpu->regs[VCPU_REGS_RAX] == __NR_sigaltstack ||
		     vcpu->regs[VCPU_REGS_RAX] == __NR_iopl)) {
		printk(KERN_INFO "svm: got unsupported syscall\n");
		vcpu->regs[VCPU_REGS_RAX] = -EINVAL;
		return;
	}

	orig_rax = vcpu->regs[VCPU_REGS_RAX];

	asm(
	"mov %c[rax](%0), %%"R"ax \n\t"
		"mov %c[rdi](%0), %%"R"di \n\t"
		"mov %c[rsi](%0), %%"R"si \n\t"
		"mov %c[rdx](%0), %%"R"dx \n\t"
		"mov %c[r8](%0),  %%r8  \n\t"
		"mov %c[r9](%0),  %%r9  \n\t"
		"mov %c[syscall](%0), %%r10 \n\t"
		"mov %0, %%r11 \n\t"
		"push %0 \n\t"
		"mov %c[r10](%0), %%"R"cx \n\t"
		"shl $3, %%rax \n\t"
		"add %%r10, %%rax\n\t"
		"call *(%%rax) \n\t"
		"pop %0 \n\t"
		"mov %%"R"ax, %c[rax](%0) \n\t"

	: : "c"(vcpu),
	[syscall]"i"(offsetof(struct svm_vcpu, syscall_tbl)),
	[rax]"i"(offsetof(struct svm_vcpu, regs[VCPU_REGS_RAX])),
	[rdi]"i"(offsetof(struct svm_vcpu, regs[VCPU_REGS_RDI])),
	[rsi]"i"(offsetof(struct svm_vcpu, regs[VCPU_REGS_RSI])),
	[rdx]"i"(offsetof(struct svm_vcpu, regs[VCPU_REGS_RDX])),
	[r10]"i"(offsetof(struct svm_vcpu, regs[VCPU_REGS_R10])),
	[r8]"i"(offsetof(struct svm_vcpu, regs[VCPU_REGS_R8])),
	[r9]"i"(offsetof(struct svm_vcpu, regs[VCPU_REGS_R9]))
	: "cc", "memory", R"ax", R"dx", R"di", R"si", "r8", "r9", "r10"
	);

	/* We apply the restart semantics as if no signal handler will be
	 * executed. */
	switch (vcpu->regs[VCPU_REGS_RAX]) {
		case -ERESTARTNOHAND:
		case -ERESTARTSYS:
		case -ERESTARTNOINTR:
			vcpu->regs[VCPU_REGS_RAX] = orig_rax;
			svm_get_cpu(vcpu);
			vmcs_writel(GUEST_RIP, vmcs_readl(GUEST_RIP) - 3);
			svm_put_cpu(vcpu);
			break;
		case -ERESTART_RESTARTBLOCK:
			vcpu->regs[VCPU_REGS_RAX] = __NR_restart_syscall;
			svm_get_cpu(vcpu);
			vmcs_writel(GUEST_RIP, vmcs_readl(GUEST_RIP) - 3);
			svm_put_cpu(vcpu);
			break;
	}
}

static void svm_handle_cpuid(struct svm_vcpu *vcpu)
{
	unsigned int eax, ebx, ecx, edx;

	eax = vcpu->regs[VCPU_REGS_RAX];
	ecx = vcpu->regs[VCPU_REGS_RCX];
	native_cpuid(&eax, &ebx, &ecx, &edx);
	vcpu->regs[VCPU_REGS_RAX] = eax;
	vcpu->regs[VCPU_REGS_RBX] = ebx;
	vcpu->regs[VCPU_REGS_RCX] = ecx;
	vcpu->regs[VCPU_REGS_RDX] = edx;
}

static int svm_handle_nmi_exception(struct svm_vcpu *vcpu)
{
	u32 intr_info;

	svm_get_cpu(vcpu);
	intr_info = vmcs_read32(VM_EXIT_INTR_INFO);
	svm_put_cpu(vcpu);

	if ((intr_info & INTR_INFO_INTR_TYPE_MASK) == INTR_TYPE_NMI_INTR)
		return 0;

	printk(KERN_ERR "svm: got interrupt, intr_info %x\n", intr_info);
	vcpu->ret_code = DUNE_RET_INTERRUPT;
	vcpu->conf->status = intr_info & INTR_INFO_VECTOR_MASK;
	return -EIO;
}

static int nmi_interception_orig(struct vcpu_svm *svm)
{
	return 1;
}

static int intr_interception_orig(struct vcpu_svm *svm)
{
	++svm->vcpu.stat.irq_exits;
	return 1;
}

static int pf_interception_orig(struct vcpu_svm *svm)
{
	u64 fault_address = svm->vmcb->control.exit_info_2;
	u64 error_code;
	int r = 1;

	switch (svm->apf_reason) {
		default:
			error_code = svm->vmcb->control.exit_info_1;

			trace_kvm_page_fault(fault_address, error_code);
			if (!npt_enabled && kvm_event_needs_reinjection(&svm->vcpu))
				kvm_mmu_unprotect_page_virt(&svm->vcpu, fault_address);
			r = kvm_mmu_page_fault(&svm->vcpu, fault_address, error_code,
					       svm->vmcb->control.insn_bytes,
					       svm->vmcb->control.insn_len);
			break;
		case KVM_PV_REASON_PAGE_NOT_PRESENT:
			svm->apf_reason = 0;
			local_irq_disable();
			kvm_async_pf_task_wait(fault_address);
			local_irq_enable();
			break;
		case KVM_PV_REASON_PAGE_READY:
			svm->apf_reason = 0;
			local_irq_disable();
			kvm_async_pf_task_wake(fault_address);
			local_irq_enable();
			break;
	}
	return r;
}

static int cpuid_interception_orig(struct vcpu_svm *svm)
{
	svm->next_rip = kvm_rip_read(&svm->vcpu) + 2;
	return kvm_emulate_cpuid(&svm->vcpu);
}

static int vmmcall_interception_orig(struct vcpu_svm *svm)
{
	svm->next_rip = kvm_rip_read(&svm->vcpu) + 3;
	return kvm_emulate_hypercall(&svm->vcpu);
}

static void svm_handle_external_intr_orig(struct kvm_vcpu *vcpu)
{
	local_irq_enable();
	/*
	 * We must have an instruction with interrupts enabled, so
	 * the timer interrupt isn't delayed by the interrupt shadow.
	 */
	asm("nop");
	local_irq_disable();
}

static void svm_get_exit_info_orig(struct kvm_vcpu *vcpu, u64 *info1, u64 *info2)
{
	struct vmcb_control_area *control = &to_svm(vcpu)->vmcb->control;

	*info1 = control->exit_info_1;
	*info2 = control->exit_info_2;
}

static int is_external_interrupt_orig(u32 info)
{
	info &= SVM_EVTINJ_TYPE_MASK | SVM_EVTINJ_VALID;
	return info == (SVM_EVTINJ_VALID | SVM_EVTINJ_TYPE_INTR);
}

static int handle_exit_orig(struct kvm_vcpu *vcpu)
{
	struct vcpu_svm *svm = to_svm(vcpu);
	struct kvm_run *kvm_run = vcpu->run;
	u32 exit_code = svm->vmcb->control.exit_code;

	trace_kvm_exit(exit_code, vcpu, KVM_ISA_SVM);

	vcpu->arch.gpa_available = (exit_code == SVM_EXIT_NPF);

	if (!is_cr_intercept(svm, INTERCEPT_CR0_WRITE))
		vcpu->arch.cr0 = svm->vmcb->save.cr0;
	if (npt_enabled)
		vcpu->arch.cr3 = svm->vmcb->save.cr3;

	if (unlikely(svm->nested.exit_required)) {
		nested_svm_vmexit(svm);
		svm->nested.exit_required = false;

		return 1;
	}

	if (is_guest_mode(vcpu)) {
		int vmexit;

		trace_kvm_nested_vmexit(svm->vmcb->save.rip, exit_code,
					svm->vmcb->control.exit_info_1,
					svm->vmcb->control.exit_info_2,
					svm->vmcb->control.exit_int_info,
					svm->vmcb->control.exit_int_info_err,
					KVM_ISA_SVM);

		vmexit = nested_svm_exit_special(svm);

		if (vmexit == NESTED_EXIT_CONTINUE)
			vmexit = nested_svm_exit_handled(svm);

		if (vmexit == NESTED_EXIT_DONE)
			return 1;
	}

	svm_complete_interrupts(svm);

	if (svm->vmcb->control.exit_code == SVM_EXIT_ERR) {
		kvm_run->exit_reason = KVM_EXIT_FAIL_ENTRY;
		kvm_run->fail_entry.hardware_entry_failure_reason
			= svm->vmcb->control.exit_code;
		pr_err("KVM: FAILED VMRUN WITH VMCB:\n");
		dump_vmcb(vcpu);
		return 0;
	}

	if (is_external_interrupt_orig(svm->vmcb->control.exit_int_info) &&
	    exit_code != SVM_EXIT_EXCP_BASE + PF_VECTOR &&
	    exit_code != SVM_EXIT_NPF && exit_code != SVM_EXIT_TASK_SWITCH &&
	    exit_code != SVM_EXIT_INTR && exit_code != SVM_EXIT_NMI)
		printk(KERN_ERR "%s: unexpected exit_int_info 0x%x "
			       "exit_code 0x%x\n",
		       __func__, svm->vmcb->control.exit_int_info,
		       exit_code);

	if (exit_code >= ARRAY_SIZE(svm_exit_handlers)
	    || !svm_exit_handlers[exit_code]) {
		WARN_ONCE(1, "svm: unexpected exit reason 0x%x\n", exit_code);
		kvm_queue_exception(vcpu, UD_VECTOR);
		return 1;
	}

	return svm_exit_handlers[exit_code](svm);
}

/**
 * svm_launch - the main loop for a SVM Dune process
 * @conf: the launch configuration
 */
int svm_launch(struct dune_config *conf, int64_t *ret_code)
{
	int ret, done = 0;
	u32 exit_intr_info;
	struct svm_vcpu *vcpu = svm_create_vcpu(conf);
	if (!vcpu)
		return -ENOMEM;

	printk(KERN_ERR "svm: created VCPU (VPID %d)\n",
	       vcpu->vpid);

	while (1) {
		svm_get_cpu(vcpu);

		/*
		 * We assume that a Dune process will always use
		 * the FPU whenever it is entered, and thus we go
		 * ahead and load FPU state here. The reason is
		 * that we don't monitor or trap FPU usage inside
		 * a Dune process.
		 */
		compat_fpu_restore();

		local_irq_disable();

		if (need_resched()) {
			local_irq_enable();
			svm_put_cpu(vcpu);
			cond_resched();
			continue;
		}

		if (signal_pending(current)) {

			local_irq_enable();
			svm_put_cpu(vcpu);


			vcpu->ret_code = DUNE_RET_SIGNAL;
			break;
		}

		setup_perf_msrs(vcpu);

		ret = svm_run_vcpu(vcpu);

		/* We need to handle NMIs before interrupts are enabled */
		exit_intr_info = vmcs_read32(VM_EXIT_INTR_INFO);
		if ((exit_intr_info & INTR_INFO_INTR_TYPE_MASK) == INTR_TYPE_NMI_INTR &&
		    (exit_intr_info & INTR_INFO_VALID_MASK)) {
			asm("int $2");
		}

		local_irq_enable();

		if (ret == EXIT_REASON_VMCALL ||
		    ret == EXIT_REASON_CPUID) {
			svm_step_instruction();
		}

		svm_put_cpu(vcpu);

		if (ret == EXIT_REASON_VMCALL)
			svm_handle_syscall(vcpu);
		else if (ret == EXIT_REASON_CPUID)
			svm_handle_cpuid(vcpu);
		else if (ret == EXIT_REASON_EPT_VIOLATION)
			done = svm_handle_npt_violation(vcpu);
		else if (ret == EXIT_REASON_EXCEPTION_NMI) {
			if (svm_handle_nmi_exception(vcpu))
				done = 1;
		} else if (ret != EXIT_REASON_EXTERNAL_INTERRUPT) {
			printk(KERN_INFO "svm: unhandled exit: reason %d, exit qualification %x\n",
			       ret, vmcs_read32(EXIT_QUALIFICATION));
			vcpu->ret_code = DUNE_RET_UNHANDLED_VMEXIT;
			svm_dump_cpu(vcpu);
			done = 1;
		}

		if (done || vcpu->shutdown)
			break;
	}

	printk(KERN_ERR "svm: stopping VCPU (VPID %d)\n",
	       vcpu->vpid);

	*ret_code = vcpu->ret_code;

	svm_copy_registers_to_conf(vcpu, conf);

	return 0;
}

static int svm_hardware_enable_orig(void)
{

	struct svm_cpu_data *sd;
	uint64_t efer;
	struct desc_struct *gdt;
	int me = raw_smp_processor_id();

	rdmsrl(MSR_EFER, efer);
	if (efer & EFER_SVME)
		return -EBUSY;

	if (!has_svm()) {
		pr_err("%s: err EOPNOTSUPP on %d\n", __func__, me);
		return -EINVAL;
	}
	sd = per_cpu(svm_data, me);
	if (!sd) {
		pr_err("%s: svm_data is NULL on %d\n", __func__, me);
		return -EINVAL;
	}

	sd->asid_generation = 1;
	sd->max_asid = cpuid_ebx(SVM_CPUID_FUNC) - 1;
	sd->next_asid = sd->max_asid + 1;

	gdt = get_current_gdt_rw();
	sd->tss_desc = (struct kvm_ldttss_desc *)(gdt + GDT_ENTRY_TSS);

	wrmsrl(MSR_EFER, efer | EFER_SVME);

	wrmsrl(MSR_VM_HSAVE_PA, page_to_pfn(sd->save_area) << PAGE_SHIFT);

	if (static_cpu_has(X86_FEATURE_TSCRATEMSR)) {
		wrmsrl(MSR_AMD64_TSC_RATIO, TSC_RATIO_DEFAULT);
		__this_cpu_write(current_tsc_ratio, TSC_RATIO_DEFAULT);
	}


	/*
	 * Get OSVW bits.
	 *
	 * Note that it is possible to have a system with mixed processor
	 * revisions and therefore different OSVW bits. If bits are not the same
	 * on different processors then choose the worst case (i.e. if erratum
	 * is present on one processor and not on another then assume that the
	 * erratum is present everywhere).
	 */
	if (cpu_has(&boot_cpu_data, X86_FEATURE_OSVW)) {
		uint64_t len, status = 0;
		int err;

		len = native_read_msr_safe(MSR_AMD64_OSVW_ID_LENGTH, &err);
		if (!err)
			status = native_read_msr_safe(MSR_AMD64_OSVW_STATUS,
						      &err);

		if (err)
			osvw_status = osvw_len = 0;
		else {
			if (len < osvw_len)
				osvw_len = len;
			osvw_status |= status;
			osvw_status &= (1ULL << osvw_len) - 1;
		}
	} else
		osvw_status = osvw_len = 0;

	svm_init_erratum_383();

	amd_pmu_enable_virt();

	return 0;
}

/**
 * __svm_enable - low-level enable of SVM mode on the current CPU
 * @vmxon_buf: an opaque buffer for use as the VMXON region
 */
static __init int __svm_enable(struct vmcs *vmxon_buf)
{
	u64 phys_addr = __pa(vmxon_buf);
	u64 old, test_bits;

	if (__read_cr4() & X86_CR4_VMXE)
		return -EBUSY;

	rdmsrl(MSR_IA32_FEATURE_CONTROL, old);

	test_bits = FEATURE_CONTROL_LOCKED;
	test_bits |= FEATURE_CONTROL_VMXON_ENABLED_OUTSIDE_SMX;
	if (tboot_enabled())
		test_bits |= FEATURE_CONTROL_VMXON_ENABLED_INSIDE_SMX;

	if ((old & test_bits) != test_bits) {
		/* enable and lock */
		wrmsrl(MSR_IA32_FEATURE_CONTROL, old | test_bits);
	}
	cr4_set_bits(X86_CR4_VMXE);

	__vmxon(phys_addr);
	vpid_sync_vcpu_global();
	ept_sync_global();

	return 0;
}

/**
 * svm_enable - enables SVM mode on the current CPU
 * @unused: not used (required for on_each_cpu())
 *
 * Sets up necessary state for enable (e.g. a scratchpad for VMXON.)
 */
static __init void svm_enable(void *unused)
{
	int ret;
	struct vmcs *vmxon_buf = __this_cpu_read(svmarea);

	if ((ret = __svm_enable(vmxon_buf)))
		goto failed;

	this_cpu_write(vmx_enabled, 1);
	native_store_gdt(this_cpu_ptr(&host_gdt));

	printk(KERN_INFO "svm: SMP enabled on CPU %d\n",
	       raw_smp_processor_id());
	return;

	failed:
	atomic_inc(&svm_enable_failed);
	printk(KERN_ERR "svm: failed to enable SVM, err = %d\n", ret);
}

static void svm_hardware_disable_orig(void)
{
	/* Make sure we clean up behind us */
	if (static_cpu_has(X86_FEATURE_TSCRATEMSR))
		wrmsrl(MSR_AMD64_TSC_RATIO, TSC_RATIO_DEFAULT);

	cpu_svm_disable();

	amd_pmu_disable_virt();
}

static void svm_cpu_uninit_orig(int cpu)
{
	struct svm_cpu_data *sd = per_cpu(svm_data, raw_smp_processor_id());

	if (!sd)
		return;

	per_cpu(svm_data, raw_smp_processor_id()) = NULL;
	__free_page(sd->save_area);
	kfree(sd);
}

static __exit void svm_hardware_unsetup_orig(void)
{
	int cpu;

	for_each_possible_cpu(cpu)
		svm_cpu_uninit_orig(cpu);

	__free_pages(pfn_to_page(iopm_base >> PAGE_SHIFT), IOPM_ALLOC_ORDER);
	iopm_base = 0;
}

/**
 * svm_disable - disables SVM mode on the current CPU
 */
static void svm_disable(void *unused)
{
	if (__this_cpu_read(svm_enabled)) {
		//__vmxoff();
		cr4_clear_bits(X86_CR4_VMXE);
		this_cpu_write(svm_enabled, 0);
	}
}

/**
 * svm_free_vmxon_areas - cleanup helper function to free all VMXON buffers
 */
static void svm_free_vmxon_areas(void)
{
	int cpu;

	for_each_possible_cpu(cpu) {
		if (per_cpu(svmarea, cpu)) {
			svm_free_vmcs(per_cpu(svmarea, cpu));
			per_cpu(svmarea, cpu) = NULL;
		}
	}
}

static const u32 msrpm_ranges[] = {0, 0xc0000000, 0xc0010000};

#define NUM_MSR_MAPS ARRAY_SIZE(msrpm_ranges)
#define MSRS_RANGE_SIZE 2048
#define MSRS_IN_RANGE (MSRS_RANGE_SIZE * 8 / 2)

static u32 svm_msrpm_offset_orig(u32 msr)
{
	u32 offset;
	int i;

	for (i = 0; i < NUM_MSR_MAPS; i++) {
		if (msr < msrpm_ranges[i] ||
		    msr >= msrpm_ranges[i] + MSRS_IN_RANGE)
			continue;

		offset  = (msr - msrpm_ranges[i]) / 4; /* 4 msrs per u8 */
		offset += (i * MSRS_RANGE_SIZE);       /* add range offset */

		/* Now we have the u8 offset - but need the u32 offset */
		return offset / 4;
	}

	/* MSR not in any range */
	return MSR_INVALID;
}

#define MSR_INVALID	0xffffffffU
#define MSRPM_OFFSETS	16
static u32 msrpm_offsets[MSRPM_OFFSETS] __read_mostly;

static void add_msr_offset_orig(u32 offset)
{
	int i;

	for (i = 0; i < MSRPM_OFFSETS; ++i) {

		/* Offset already in list? */
		if (msrpm_offsets[i] == offset)
			return;

		/* Slot used by another offset? */
		if (msrpm_offsets[i] != MSR_INVALID)
			continue;

		/* Add offset to list */
		msrpm_offsets[i] = offset;

		return;
	}

	/*
	 * If this BUG triggers the msrpm_offsets table has an overflow. Just
	 * increase MSRPM_OFFSETS in this case.
	 */
	BUG();
}

static void init_msrpm_offsets_orig(void)
{
	int i;

	memset(msrpm_offsets, 0xff, sizeof(msrpm_offsets));

	for (i = 0; direct_access_msrs[i].index != MSR_INVALID; i++) {
		u32 offset;

		offset = svm_msrpm_offset_orig(direct_access_msrs[i].index);
		BUG_ON(offset == MSR_INVALID);

		add_msr_offset_orig(offset);
	}
}

static int svm_cpu_init_orig(int cpu)
{
	struct svm_cpu_data *sd;
	int r;

	sd = kzalloc(sizeof(struct svm_cpu_data), GFP_KERNEL);
	if (!sd)
		return -ENOMEM;
	sd->cpu = cpu;
	sd->save_area = alloc_page(GFP_KERNEL);
	r = -ENOMEM;
	if (!sd->save_area)
		goto err_1;

	per_cpu(svm_data, cpu) = sd;

	return 0;

	err_1:
	kfree(sd);
	return r;

}

#define IOPM_ALLOC_ORDER 2
#define MSRPM_ALLOC_ORDER 1

static __init int svm_hardware_setup_orig(void)
{
	int cpu;
	struct page *iopm_pages;
	void *iopm_va;
	int r;

	iopm_pages = alloc_pages(GFP_KERNEL, IOPM_ALLOC_ORDER);

	if (!iopm_pages)
		return -ENOMEM;

	iopm_va = page_address(iopm_pages);
	memset(iopm_va, 0xff, PAGE_SIZE * (1 << IOPM_ALLOC_ORDER));
	iopm_base = page_to_pfn(iopm_pages) << PAGE_SHIFT;

	init_msrpm_offsets_orig();

	if (boot_cpu_has(X86_FEATURE_NX))
		kvm_enable_efer_bits(EFER_NX);

	if (boot_cpu_has(X86_FEATURE_FXSR_OPT))
		kvm_enable_efer_bits(EFER_FFXSR);

	if (boot_cpu_has(X86_FEATURE_TSCRATEMSR)) {
		kvm_has_tsc_control = true;
		kvm_max_tsc_scaling_ratio = TSC_RATIO_MAX;
		kvm_tsc_scaling_ratio_frac_bits = 32;
	}

	if (nested) {
		printk(KERN_INFO "kvm: Nested Virtualization enabled\n");
		kvm_enable_efer_bits(EFER_SVME | EFER_LMSLE);
	}

	for_each_possible_cpu(cpu) {
		r = svm_cpu_init_orig(cpu);
		if (r)
			goto err;
	}

	if (!boot_cpu_has(X86_FEATURE_NPT))
		npt_enabled = false;

	if (npt_enabled && !npt) {
		printk(KERN_INFO "kvm: Nested Paging disabled\n");
		npt_enabled = false;
	}

	if (npt_enabled) {
		printk(KERN_INFO "kvm: Nested Paging enabled\n");
		kvm_enable_tdp();
	} else
		kvm_disable_tdp();

	if (avic) {
		if (!npt_enabled ||
		    !boot_cpu_has(X86_FEATURE_AVIC) ||
		    !IS_ENABLED(CONFIG_X86_LOCAL_APIC)) {
			avic = false;
		} else {
			pr_info("AVIC enabled\n");

			amd_iommu_register_ga_log_notifier(&avic_ga_log_notifier);
		}
	}

	return 0;

	err:
	__free_pages(iopm_pages, IOPM_ALLOC_ORDER);
	iopm_base = 0;
	return r;
}

/**
 * svm_init - the main initialization routine for this driver
 */
__init int svm_init(void)
{
	int r, cpu;

	if (!cpu_has_svm()) {
		printk(KERN_ERR "svm: CPU does not support AMD-V (SVM)\n");
		return -EIO;
	}

	vmx_init_syscall();

	if (setup_vmcs_config(&vmcs_config) < 0)
		return -EIO;

	if (!cpu_has_svm_vpid()) {
		printk(KERN_ERR "svm: CPU is missing required feature 'VPID'\n");
		return -EIO;
	}

	if (!cpu_has_svm_npt()) {
		printk(KERN_ERR "svm: CPU is missing required feature 'NPT'\n");
		return -EIO;
	}

	if (!svm_capability.has_load_efer) {
		printk(KERN_ERR "svm: ability to load EFER register is required\n");
		return -EIO;
	}

	msr_bitmap = (unsigned long *)__get_free_page(GFP_KERNEL);
	if (!msr_bitmap) {
		return -ENOMEM;
	}
	/* FIXME: do we need APIC virtualization (flexpriority?) */

	memset(msr_bitmap, 0xff, PAGE_SIZE);
	__svm_disable_intercept_for_msr(msr_bitmap, MSR_FS_BASE);
	__svm_disable_intercept_for_msr(msr_bitmap, MSR_GS_BASE);
	__svm_disable_intercept_for_msr(msr_bitmap, MSR_PKG_ENERGY_STATUS);
	__svm_disable_intercept_for_msr(msr_bitmap, MSR_RAPL_POWER_UNIT);

	set_bit(0, svm_vpid_bitmap); /* 0 is reserved for host */

	for_each_possible_cpu(cpu) {
		struct vmcs *vmxon_buf;

		vmxon_buf = __svm_alloc_vmcs(cpu);
		if (!vmxon_buf) {
			svm_free_vmxon_areas();
			return -ENOMEM;
		}

		per_cpu(svmarea, cpu) = vmxon_buf;
	}

	atomic_set(&svm_enable_failed, 0);
	if (on_each_cpu(svm_enable, NULL, 1)) {
		printk(KERN_ERR "svm: timeout waiting for SVM mode enable.\n");
		r = -EIO;
		goto failed1; /* sadly we can't totally recover */
	}

	if (atomic_read(&svm_enable_failed)) {
		r = -EBUSY;
		goto failed2;
	}

	return 0;

	failed2:
	on_each_cpu(svm_disable, NULL, 1);
	failed1:
	svm_free_vmxon_areas();
	return r;
}

/**
 * svm_exit - the main removal routine for this driver
 */
void svm_exit(void)
{
	svm_cleanup();
	on_each_cpu(svm_disable, NULL, 1);
	//svm_free_vmxon_areas();
	free_page((unsigned long)msr_bitmap);
}
