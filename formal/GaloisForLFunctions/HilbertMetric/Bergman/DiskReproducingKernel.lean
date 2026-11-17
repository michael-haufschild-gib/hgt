import GaloisForLFunctions.HilbertMetric.Bergman.DiskCoefficients

/-!
# The Bergman disk kernel and its sharp evaluation bound

Weighted geometric summation realizes the actual reproducing kernel
`(1 - conj(z) w)⁻²` in the coefficient Hilbert space. Its norm is exactly
`(1 - |z|²)⁻¹`, giving the sharp point-evaluation scale of the disk model.
-/

open Complex Filter Topology
open scoped ComplexConjugate
namespace GaloisForLFunctions.HilbertMetric.Bergman
open HTGeometry
noncomputable section

/-- A point of the open disk, with its geometric domain built into the type. -/
abbrev Point := {z : ℂ // ‖z‖ < 1}

private theorem weighted_geometric_summable' {𝕜 : Type*} [RCLike 𝕜] {q : 𝕜} (hq : ‖q‖ < 1) :
    Summable (fun n : ℕ => ((n : 𝕜) + 1) * q ^ n) := by
  have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 hq
  simp only [pow_one] at h1
  simpa only [add_mul, one_mul] using h1.add (summable_geometric_of_norm_lt_one hq)

private theorem weighted_geometric {𝕜 : Type*} [RCLike 𝕜] {q : 𝕜} (hq : ‖q‖ < 1) :
    (∑' n : ℕ, ((n : 𝕜) + 1) * q ^ n) = 1 / (1 - q) ^ 2 := by
  have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 hq
  simp only [pow_one] at h1
  have h0 := summable_geometric_of_norm_lt_one hq
  have hn : 1 - q ≠ 0 := by
    intro h
    have he : q = 1 := (sub_eq_zero.mp h).symm
    rw [he, norm_one] at hq
    exact (lt_irrefl 1) hq
  simp only [add_mul, one_mul]
  rw [h1.tsum_add h0, tsum_coe_mul_geometric_of_norm_lt_one hq,
    tsum_geometric_of_norm_lt_one hq]
  field_simp [hn]
  ring

/-- Hilbert coordinates of the kernel vector at one disk point. -/
def kernelCoeff (z : Point) (n : ℕ) : ℂ :=
  (Real.sqrt ((n : ℝ) + 1) : ℂ) * conj (z : ℂ) ^ n

private theorem kernelCoeff_norm_sq (z : Point) (n : ℕ) :
    ‖kernelCoeff z n‖ ^ 2 = ((n : ℝ) + 1) * (‖(z : ℂ)‖ ^ 2) ^ n := by
  rw [kernelCoeff, norm_mul, mul_pow, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (by positivity),
    norm_pow, Complex.norm_conj]
  rw [← pow_mul, ← pow_mul, Nat.mul_comm n 2]

private theorem memlp_kernelCoeff (z : Point) : Memℓp (kernelCoeff z) 2 := by
  rw [memℓp_gen_iff (by norm_num)]
  have hq : ‖‖(z : ℂ)‖ ^ 2‖ < 1 := by
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    nlinarith only [z.property, norm_nonneg (z : ℂ)]
  exact (weighted_geometric_summable' hq).congr fun n => by
    rw [show (2 : ENNReal).toReal = ((2 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast, kernelCoeff_norm_sq]

/-- The genuine square-summable Bergman reproducing vector. -/
def kernel (z : Point) : Disk := ⟨kernelCoeff z, memlp_kernelCoeff z⟩

@[simp] theorem kernel_apply (z : Point) (n : ℕ) : kernel z n = kernelCoeff z n := rfl

/-- Point evaluation is the actual Hilbert inner product with the kernel vector. -/
theorem inner_kernel (z : Point) (a : Disk) : inner ℂ (kernel z) a = diskFun a z := by
  rw [lp.inner_eq_tsum, diskFun]
  apply tsum_congr
  intro n
  rw [RCLike.inner_apply, kernel_apply, kernelCoeff, map_mul, Complex.conj_ofReal,
    ← map_pow, Complex.conj_conj, coefficient]
  ring

/-- The reproducing vector is the classical holomorphic Bergman kernel. -/
theorem diskFun_kernel (z w : Point) :
    diskFun (kernel z) w = 1 / (1 - conj (z : ℂ) * (w : ℂ)) ^ 2 := by
  have hq : ‖conj (z : ℂ) * (w : ℂ)‖ < 1 := by
    rw [norm_mul, Complex.norm_conj]
    have h := mul_le_mul_of_nonneg_left w.property.le (norm_nonneg (z : ℂ))
    rw [mul_one] at h
    exact h.trans_lt z.property
  have he (n : ℕ) : coefficient (kernel z) n * (w : ℂ) ^ n =
      ((n : ℂ) + 1) * (conj (z : ℂ) * (w : ℂ)) ^ n := by
    have hs : (Real.sqrt ((n : ℝ) + 1) : ℂ) ^ 2 = (n : ℂ) + 1 := by
      exact_mod_cast Real.sq_sqrt (show 0 ≤ (n : ℝ) + 1 by positivity)
    rw [coefficient, kernel_apply, kernelCoeff, mul_pow]
    calc
      _ = (Real.sqrt ((n : ℝ) + 1) : ℂ) ^ 2 *
          (conj (z : ℂ) ^ n * (w : ℂ) ^ n) := by ring
      _ = _ := by rw [hs]
  rw [diskFun, tsum_congr he]
  exact weighted_geometric hq

/-- The exact square of the evaluation functional's representing norm. -/
theorem kernel_norm_sq (z : Point) : ‖kernel z‖ ^ 2 = 1 / (1 - ‖(z : ℂ)‖ ^ 2) ^ 2 := by
  rw [hardyDisk_norm_sq]
  simp only [kernel_apply, kernelCoeff_norm_sq]
  apply weighted_geometric
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  nlinarith only [z.property, norm_nonneg (z : ℂ)]

/-- Exact blow-up rate of the Bergman evaluation kernel near the boundary. -/
theorem kernel_norm (z : Point) : ‖kernel z‖ = 1 / (1 - ‖(z : ℂ)‖ ^ 2) := by
  have hd : 0 < 1 - ‖(z : ℂ)‖ ^ 2 := by
    nlinarith only [z.property, norm_nonneg (z : ℂ)]
  have hs := kernel_norm_sq z
  have hn : 0 ≤ 1 / (1 - ‖(z : ℂ)‖ ^ 2) := (one_div_pos.mpr hd).le
  have he : 1 / (1 - ‖(z : ℂ)‖ ^ 2) ^ 2 = (1 / (1 - ‖(z : ℂ)‖ ^ 2)) ^ 2 := by
    rw [div_pow, one_pow]
  rw [he] at hs
  nlinarith only [hs, norm_nonneg (kernel z), hn]

/-- The pointwise Bergman bound follows from the actual reproducing identity. -/
theorem evaluation_bound (z : Point) (a : Disk) :
    ‖diskFun a z‖ ≤ ‖a‖ / (1 - ‖(z : ℂ)‖ ^ 2) := by
  rw [← inner_kernel]
  have h := norm_inner_le_norm (𝕜 := ℂ) (kernel z) a
  rw [kernel_norm] at h
  simpa only [one_div, div_eq_mul_inv, one_mul, mul_comm] using h

/-- Evaluation is a genuine continuous complex-linear functional on the full coefficient space. -/
def evaluation (z : Point) : Disk →L[ℂ] ℂ := innerSL ℂ (kernel z)

@[simp] theorem evaluation_apply (z : Point) (a : Disk) :
    evaluation z a = diskFun a z := inner_kernel z a

/-- The optimal evaluation constant is exactly the reciprocal boundary-distance factor. -/
theorem evaluation_norm (z : Point) : ‖evaluation z‖ = 1 / (1 - ‖(z : ℂ)‖ ^ 2) := by
  rw [evaluation, innerSL_apply_norm, kernel_norm]

#print axioms inner_kernel
#print axioms diskFun_kernel
#print axioms kernel_norm
#print axioms evaluation_bound
#print axioms evaluation_norm
end
end GaloisForLFunctions.HilbertMetric.Bergman
