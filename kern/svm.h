/*
 * svm.h - header file for AMD-V SVM driver.
 */

#include <linux/mmu_notifier.h>
#include <linux/types.h>
#include <asm/vmx.h>
#include <asm/svm.h>
#include <linux/kvm_types.h>

// ========================
// Start of KVM SVM defines
// ========================

struct vcpu_svm {
	struct kvm_vcpu vcpu;
	struct vmcb *vmcb;
	unsigned long vmcb_pa;
	struct svm_cpu_data *svm_data;
	uint64_t asid_generation;
	uint64_t sysenter_esp;
	uint64_t sysenter_eip;
	uint64_t tsc_aux;

	u64 next_rip;

	u64 host_user_msrs[NR_HOST_SAVE_USER_MSRS];
	struct {
		u16 fs;
		u16 gs;
		u16 ldt;
		u64 gs_base;
	} host;

	u32 *msrpm;

	ulong nmi_iret_rip;

	struct nested_state nested;

	bool nmi_singlestep;

	unsigned int3_injected;
	unsigned long int3_rip;
	u32 apf_reason;

	/* cached guest cpuid flags for faster access */
	bool nrips_enabled	: 1;

	u32 ldr_reg;
	struct page *avic_backing_page;
	u64 *avic_physical_id_cache;
	bool avic_is_running;

	/*
	 * Per-vcpu list of struct amd_svm_iommu_ir:
	 * This is used mainly to store interrupt remapping information used
	 * when update the vcpu affinity. This avoids the need to scan for
	 * IRTE and try to match ga_tag in the IOMMU driver.
	 */
	struct list_head ir_list;
	spinlock_t ir_list_lock;
};

struct svm_cpu_data {
	int cpu;

	u64 asid_generation;
	u32 max_asid;
	u32 next_asid;
	struct kvm_ldttss_desc *tss_desc;

	struct page *save_area;
};

enum {
	VMCB_INTERCEPTS, /* Intercept vectors, TSC offset,
			    pause filter count */
	VMCB_PERM_MAP,   /* IOPM Base and MSRPM Base */
	VMCB_ASID,	 /* ASID */
	VMCB_INTR,	 /* int_ctl, int_vector */
	VMCB_NPT,        /* npt_en, nCR3, gPAT */
	VMCB_CR,	 /* CR0, CR3, CR4, EFER */
	VMCB_DR,         /* DR6, DR7 */
	VMCB_DT,         /* GDT, IDT */
	VMCB_SEG,        /* CS, DS, SS, ES, CPL */
	VMCB_CR2,        /* CR2 only */
	VMCB_LBR,        /* DBGCTL, BR_FROM, BR_TO, LAST_EX_FROM, LAST_EX_TO */
	VMCB_AVIC,       /* AVIC APIC_BAR, AVIC APIC_BACKING_PAGE,
			  * AVIC PHYSICAL_TABLE pointer,
			  * AVIC LOGICAL_TABLE pointer
			  */
	VMCB_DIRTY_MAX,
};

// ======================
// End of KVM SVM defines
// ======================

DECLARE_PER_CPU(struct svm_vcpu *, local_vcpu);

struct vmcs {
	u32 revision_id;
	u32 abort;
	char data[0];
};

struct svm_capability {
	u32 ept;
	u32 vpid;
	int has_load_efer:1;
};

extern struct svm_capability svm_capability;

#define NR_AUTOLOAD_MSRS 8

enum svm_reg {
	VCPU_REGS_RAX = 0,
	VCPU_REGS_RCX = 1,
	VCPU_REGS_RDX = 2,
	VCPU_REGS_RBX = 3,
	VCPU_REGS_RSP = 4,
	VCPU_REGS_RBP = 5,
	VCPU_REGS_RSI = 6,
	VCPU_REGS_RDI = 7,
#ifdef CONFIG_X86_64
	VCPU_REGS_R8 = 8,
	VCPU_REGS_R9 = 9,
	VCPU_REGS_R10 = 10,
	VCPU_REGS_R11 = 11,
	VCPU_REGS_R12 = 12,
	VCPU_REGS_R13 = 13,
	VCPU_REGS_R14 = 14,
	VCPU_REGS_R15 = 15,
#endif
	VCPU_REGS_RIP,
	NR_VCPU_REGS
};

struct svm_vcpu {
	struct list_head list;
	int cpu;
	int vpid;
	int launched;

	struct mmu_notifier mmu_notifier;
	spinlock_t ept_lock;
	unsigned long ept_root;
	unsigned long eptp;
	bool ept_ad_enabled;

	u8  fail;
	u64 exit_reason;
	u64 host_rsp;
	u64 regs[NR_VCPU_REGS];
	u64 cr2;

	int shutdown;
	int ret_code;

	struct msr_autoload {
		unsigned nr;
		struct svm_msr_entry guest[NR_AUTOLOAD_MSRS];
		struct svm_msr_entry host[NR_AUTOLOAD_MSRS];
	} msr_autoload;

	struct vmcs *vmcs;
	void *syscall_tbl;
	struct dune_config *conf;
	unsigned long guest_kernel_gs_base;
};

extern __init int svm_init(void);
extern void svm_exit(void);
extern void svm_cleanup(void);

extern int svm_launch(struct dune_config *conf, int64_t *ret_code);

extern int svm_init_npt(struct svm_vcpu *vcpu);
extern int svm_create_npt(struct svm_vcpu *vcpu);
extern void svm_destroy_npt(struct svm_vcpu *vcpu);

extern int
svm_do_npt_fault(struct svm_vcpu *vcpu, unsigned long gpa,
		 unsigned long gva, int fault_flags);

extern void svm_npt_sync_vcpu(struct svm_vcpu *vcpu);
extern void svm_npt_sync_individual_addr(struct svm_vcpu *vcpu, gpa_t gpa);

static __always_inline unsigned long vmcs_readl(unsigned long field)
{
        unsigned long value;

        asm volatile (ASM_VMX_VMREAD_RDX_RAX
                      : "=a"(value) : "d"(field) : "cc");
        return value;
}
