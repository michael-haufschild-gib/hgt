import GaloisForLFunctions.HTGeometry.HardyDiskBlaschke

/-!
# The range of a Blaschke multiplication and its model space

`hardy-cyclicity-maximal-ht-field-blindness`, equation `(16)` and the codimension statement.

The reproducing kernel of `H²(D)` at a point `a` of the disk is the geometric coefficient sequence
`k_a(n) = conj(a)ⁿ`, and `⟪k_a, x⟫ = (hardyFun x)(a)`.  For a single Blaschke factor,

```text
range M_{b_a} = { x : (hardyFun x)(a) = 0 } = (ℂ ∙ k_a)ᗮ,
```

so the model space `H² ⊖ b_a H²` is the line `ℂ ∙ k_a`.  Multiplication by a finite Blaschke
product is an isometry, hence a closed embedding, so cyclic subspaces transport:
`[B·O] = B·[O] = B·H²`.
-/

open Complex Filter Metric Real Topology

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-! ## The reproducing kernel -/

/-- The coefficient sequence of the Szegő kernel at `a`. -/
def hardyKernelCoeff (a : ℂ) : ℕ → ℂ := fun n => ((starRingEnd ℂ) a) ^ n

theorem memlp_hardyKernel {a : ℂ} (ha : ‖a‖ < 1) : Memℓp (hardyKernelCoeff a) 2 := by
  rw [memℓp_gen_iff (by norm_num)]
  have hsum : Summable (fun n : ℕ => (‖a‖ ^ 2) ^ n) :=
    summable_geometric_of_lt_one (by positivity) (by nlinarith [norm_nonneg a])
  refine hsum.congr fun n => ?_
  rw [hardyKernelCoeff, norm_pow, RCLike.norm_conj]
  rw [show ((2 : ENNReal).toReal) = ((2:ℕ) : ℝ) by norm_num,
    Real.rpow_natCast (‖a‖ ^ n) 2]
  ring

/-- The Szegő reproducing kernel at `a`, as an element of `H²(D)`. -/
def hardyKernel {a : ℂ} (ha : ‖a‖ < 1) : HardyDisk := ⟨hardyKernelCoeff a, memlp_hardyKernel ha⟩

theorem hardyKernel_ne_zero {a : ℂ} (ha : ‖a‖ < 1) : hardyKernel ha ≠ 0 := by
  intro h
  have h0 : (hardyKernel ha) 0 = 0 := by rw [h]; rfl
  rw [show (hardyKernel ha) 0 = hardyKernelCoeff a 0 from rfl, hardyKernelCoeff, pow_zero] at h0
  exact one_ne_zero h0

/-- **The reproducing property.** -/
theorem inner_hardyKernel {a : ℂ} (ha : ‖a‖ < 1) (x : HardyDisk) :
    (inner ℂ (hardyKernel ha) x : ℂ) = hardyFun x a := by
  rw [lp.inner_eq_tsum, hardyFun]
  refine tsum_congr fun n => ?_
  rw [RCLike.inner_apply,
    show (hardyKernel ha) n = hardyKernelCoeff a n from rfl, hardyKernelCoeff, ← map_pow,
    Complex.conj_conj]

theorem mem_orthogonal_kernel_iff {a : ℂ} (ha : ‖a‖ < 1) (x : HardyDisk) :
    x ∈ (ℂ ∙ hardyKernel ha)ᗮ ↔ hardyFun x a = 0 := by
  rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
  constructor
  · intro h
    have h2 : (inner ℂ (hardyKernel ha) x : ℂ) = 0 := by
      rw [← inner_conj_symm, h, map_zero]
    rwa [inner_hardyKernel ha x] at h2
  · intro h
    have h2 : (inner ℂ (hardyKernel ha) x : ℂ) = 0 := by rw [inner_hardyKernel ha x, h]
    rw [← inner_conj_symm, h2, map_zero]

/-! ## The single Blaschke factor -/

/-- One Blaschke factor as finite Blaschke data. -/
def singleBlaschke {a : ℂ} (ha : ‖a‖ < 1) : FiniteBlaschke where
  deg := 1
  zeros := fun _ => a
  bound := ‖a‖
  bound_nonneg := norm_nonneg a
  bound_lt := ha
  zeros_le := fun _ => le_rfl

theorem singleBlaschke_fn {a : ℂ} (ha : ‖a‖ < 1) (z : ℂ) :
    (singleBlaschke ha).fn z = blaschkeFactor a z := by
  rw [FiniteBlaschke.fn, blaschkeProd]
  simp [singleBlaschke]

theorem blaschkeFactor_self {a : ℂ} (ha : ‖a‖ < 1) : blaschkeFactor a a = 0 := by
  rw [blaschkeFactor, sub_self, zero_div]

end GaloisForLFunctions.HTGeometry
