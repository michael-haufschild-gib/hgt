import GaloisForLFunctions.RHTower.CriticalPrimeKernelSampling

/-!
# Radial moment Fock kernels

This file gives a literal coefficient Hilbert model for any positive radial moment sequence whose
point kernels are square-summable.  It constructs bounded evaluations, computes the kernel series,
normalizes the kernel vectors, and specializes them to the critical prime-log nodes.
-/

open scoped InnerProductSpace ComplexConjugate

namespace RHTower

noncomputable section

/-- Coefficient of the reproducing vector at `z` for a radial moment sequence. -/
def momentFockKernelCoeff (weight : ℕ → ℝ) (z : ℂ) (n : ℕ) : ℂ :=
  (starRingEnd ℂ z) ^ n / Real.sqrt (weight n)

/-- Positive moments whose coefficient kernels belong to complex `ℓ²` at every point. -/
structure MomentFockData where
  weight : ℕ → ℝ
  weight_pos : ∀ n, 0 < weight n
  kernel_summable : ∀ z : ℂ,
    Summable fun n => ‖momentFockKernelCoeff weight z n‖ ^ (2 : ℝ)

/-- Hilbert coefficient model of a radial moment Fock space. -/
abbrev MomentFock := lp (fun _ : ℕ => ℂ) 2

/-- Reproducing vector at `z`. -/
def momentFockKernel (d : MomentFockData) (z : ℂ) : MomentFock :=
  ⟨momentFockKernelCoeff d.weight z, memℓp_gen (d.kernel_summable z)⟩

@[simp] theorem momentFockKernel_apply (d : MomentFockData) (z : ℂ) (n : ℕ) :
    momentFockKernel d z n = momentFockKernelCoeff d.weight z n := rfl

theorem momentFockKernel_ne_zero (d : MomentFockData) (z : ℂ) :
    momentFockKernel d z ≠ 0 := by
  intro hzero
  have hcoord := congrArg (fun f : MomentFock => f 0) hzero
  have hsqrt : Real.sqrt (d.weight 0) ≠ 0 :=
    (Real.sqrt_pos.2 (d.weight_pos 0)).ne'
  simp [momentFockKernel, momentFockKernelCoeff, hsqrt] at hcoord

/-- Literal bounded point evaluation in the coefficient model. -/
def momentFockEvaluation (d : MomentFockData) (z : ℂ) : MomentFock →L[ℂ] ℂ :=
  innerSL ℂ (momentFockKernel d z)

@[simp] theorem momentFockEvaluation_apply
    (d : MomentFockData) (z : ℂ) (f : MomentFock) :
    momentFockEvaluation d z f = inner ℂ (momentFockKernel d z) f := rfl

theorem momentFockEvaluation_eq_tsum
    (d : MomentFockData) (z : ℂ) (f : MomentFock) :
    momentFockEvaluation d z f =
      ∑' n, z ^ n / Real.sqrt (d.weight n) * f n := by
  rw [momentFockEvaluation_apply, lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  simp [momentFockKernelCoeff, RCLike.inner_apply]
  ring

/-- Kernel pairing, with first argument the evaluation point. -/
def momentFockKernelValue (d : MomentFockData) (z w : ℂ) : ℂ :=
  inner ℂ (momentFockKernel d z) (momentFockKernel d w)

theorem momentFockKernelValue_eq_tsum
    (d : MomentFockData) (z w : ℂ) :
    momentFockKernelValue d z w =
      ∑' n, (z * (starRingEnd ℂ w)) ^ n / d.weight n := by
  rw [momentFockKernelValue, lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  have hsqrt : Real.sqrt (d.weight n) ≠ 0 :=
    (Real.sqrt_pos.2 (d.weight_pos n)).ne'
  simp only [momentFockKernel_apply, momentFockKernelCoeff, RCLike.inner_apply]
  rw [map_div₀, map_pow, starRingEnd_self_apply]
  have hstar : (starRingEnd ℂ) (Real.sqrt (d.weight n) : ℂ) =
      (Real.sqrt (d.weight n) : ℂ) := by simp
  have hsquare : (Real.sqrt (d.weight n) : ℂ) ^ (2 : ℕ) = (d.weight n : ℂ) := by
    exact_mod_cast Real.sq_sqrt (d.weight_pos n).le
  have hweight : (d.weight n : ℂ) ≠ 0 := by
    exact_mod_cast (d.weight_pos n).ne'
  rw [hstar]
  field_simp [hsqrt]
  rw [hsquare]
  field_simp [hweight]
  rw [mul_pow]
  ring

theorem momentFockEvaluation_kernel
    (d : MomentFockData) (z w : ℂ) :
    momentFockEvaluation d z (momentFockKernel d w) =
      momentFockKernelValue d z w := rfl

theorem norm_momentFockEvaluation_apply_le
    (d : MomentFockData) (z : ℂ) (f : MomentFock) :
    ‖momentFockEvaluation d z f‖ ≤ ‖momentFockKernel d z‖ * ‖f‖ := by
  rw [momentFockEvaluation_apply]
  exact norm_inner_le_norm _ _

/-- Coefficient vector representing the constant entire function `1`. -/
def momentFockOne (d : MomentFockData) : MomentFock :=
  lp.single 2 0 (Real.sqrt (d.weight 0) : ℂ)

theorem momentFockEvaluation_one
    (d : MomentFockData) (z : ℂ) :
    momentFockEvaluation d z (momentFockOne d) = 1 := by
  rw [momentFockEvaluation_apply, momentFockOne, lp.inner_single_right]
  have hsqrt : Real.sqrt (d.weight 0) ≠ 0 :=
    (Real.sqrt_pos.2 (d.weight_pos 0)).ne'
  simp only [momentFockKernel_apply, momentFockKernelCoeff, pow_zero, one_div,
    RCLike.inner_apply]
  have hstarInv : (starRingEnd ℂ) ((Real.sqrt (d.weight 0) : ℂ)⁻¹) =
      (Real.sqrt (d.weight 0) : ℂ)⁻¹ := by simp
  rw [hstarInv]
  field_simp [hsqrt]

theorem norm_momentFockOne (d : MomentFockData) :
    ‖momentFockOne d‖ = Real.sqrt (d.weight 0) := by
  rw [momentFockOne, lp.norm_single (by norm_num)]
  simp

/-- Unit reproducing vector at `z`. -/
def normalizedMomentFockKernel (d : MomentFockData) (z : ℂ) : MomentFock :=
  (‖momentFockKernel d z‖ : ℂ)⁻¹ • momentFockKernel d z

theorem norm_normalizedMomentFockKernel (d : MomentFockData) (z : ℂ) :
    ‖normalizedMomentFockKernel d z‖ = 1 := by
  rw [normalizedMomentFockKernel, norm_smul, norm_inv,
    Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr (momentFockKernel_ne_zero d z))

theorem inner_normalizedMomentFockKernel
    (d : MomentFockData) (z w : ℂ) :
    inner ℂ (normalizedMomentFockKernel d z) (normalizedMomentFockKernel d w) =
      (‖momentFockKernel d z‖ : ℂ)⁻¹ *
        (‖momentFockKernel d w‖ : ℂ)⁻¹ * momentFockKernelValue d z w := by
  simp only [normalizedMomentFockKernel]
  rw [inner_smul_left, inner_smul_right]
  change (starRingEnd ℂ) (‖momentFockKernel d z‖ : ℂ)⁻¹ *
      ((‖momentFockKernel d w‖ : ℂ)⁻¹ *
        inner ℂ (momentFockKernel d z) (momentFockKernel d w)) = _
  have hstar : (starRingEnd ℂ) (‖momentFockKernel d z‖ : ℂ)⁻¹ =
      (‖momentFockKernel d z‖ : ℂ)⁻¹ := by simp
  rw [hstar, momentFockKernelValue]
  ring

/-- The normalized critical-prime kernel family in any instantiated moment Fock space. -/
def criticalPrimeMomentFockKernel (d : MomentFockData) (p : Nat.Primes) : MomentFock :=
  normalizedMomentFockKernel d ((Real.log ((p : ℕ) : ℝ) : ℝ) : ℂ)

theorem norm_criticalPrimeMomentFockKernel (d : MomentFockData) (p : Nat.Primes) :
    ‖criticalPrimeMomentFockKernel d p‖ = 1 :=
  norm_normalizedMomentFockKernel d _

end

end RHTower
