import GaloisForLFunctions.RHTower.ComplexSignedGaussianHeat
import GaloisForLFunctions.RHTower.XiGaussianHeatTraceCriterion
import GaloisForLFunctions.RHTower.XiWeilFunctionalEquationParity

/-!
# Signed Gaussian heat reconstructs the actual Xi FE orientation

The complex source spectrum lies in the square-positive sectors. Its signed
Gaussian transform is therefore exactly the Deninger orientation, without
assuming spectral reality. Every truncated time window is uniformly bounded
over the entire multiplicity-exact divisor and reverses FE parity.
-/

open Complex MeasureTheory Set Filter
open scoped Topology

namespace RHTower

noncomputable section

/-- The complete signed heat integral is the actual Deninger orientation. -/
theorem xi_signed_gaussian_integral_eq_orientation (q : XiZeroCopy) :
    xiSpectralPoint q / (Real.sqrt Real.pi : ℂ) *
        (∫ t : ℝ, Complex.exp (-(xiSpectralPoint q ^ 2) * (t : ℂ) ^ 2)) =
      deningerArithmeticFEOrientation q := by
  have hp : (Real.sqrt Real.pi : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos))
  have hz := xiSpectralPoint_ne_zero q
  by_cases hpos : 0 < (xiSpectralPoint q).re
  · rw [integral_complexGaussian_sq_of_re_pos hpos (xiSpectralSq_re_pos q)]
    simp only [deningerArithmeticFEOrientation, if_pos hpos]
    field_simp [hp, hz]
  · have hneg : (xiSpectralPoint q).re < 0 := by
      have hgap := four_lt_abs_re_xiSpectralPoint q
      have hle : (xiSpectralPoint q).re ≤ 0 := le_of_not_gt hpos
      rw [abs_of_nonpos hle] at hgap
      linarith
    rw [integral_complexGaussian_sq_of_re_neg hneg (xiSpectralSq_re_pos q)]
    simp only [deningerArithmeticFEOrientation, if_neg hpos, if_pos hneg]
    field_simp [hp, hz]

/-- The signed heat multiplier at one finite symmetric time cutoff. -/
def xiSignedHeatOrientationWindow (N : ℕ) (q : XiZeroCopy) : ℂ :=
  complexSignedGaussianWindow N (xiSpectralPoint q)

/-- Uniform control over all time cutoffs and all actual Xi spectral copies. -/
theorem norm_xiSignedHeatOrientationWindow_le (N : ℕ) (q : XiZeroCopy) :
    ‖xiSignedHeatOrientationWindow N q‖ ≤ 2 := by
  apply (norm_complexSignedGaussianWindow_le N (xiSpectralSq_re_pos q)).trans
  have hA := Real.sqrt_pos.mpr (xiSpectralSq_re_pos q)
  apply (div_le_iff₀ hA).mpr
  have hsector := xiSpectralPoint_normSq_lt_two_mul_sq_re q
  rw [← Complex.sq_norm] at hsector
  have hs := Real.sq_sqrt (xiSpectralSq_re_pos q).le
  nlinarith [norm_nonneg (xiSpectralPoint q)]

/-- Pointwise convergence of signed heat to FE orientation, with all zero multiplicities retained. -/
theorem tendsto_xiSignedHeatOrientationWindow (q : XiZeroCopy) :
    Tendsto (fun N => xiSignedHeatOrientationWindow N q) atTop
      (𝓝 (deningerArithmeticFEOrientation q)) := by
  have h := tendsto_complexSignedGaussianWindow (xiSpectralSq_re_pos q)
  rw [xi_signed_gaussian_integral_eq_orientation q] at h
  exact h

/-- The source height gap gives a uniform lower bound for the real spectral square. -/
theorem two_le_re_sq_xiSpectralPoint (q : XiZeroCopy) :
    2 ≤ (xiSpectralPoint q ^ 2).re := by
  have hsector := xiSpectralPoint_normSq_lt_two_mul_sq_re q
  rw [Complex.normSq_apply] at hsector
  have hgap := four_lt_abs_re_xiSpectralPoint q
  rcases le_total 0 (xiSpectralPoint q).re with hpos | hneg
  · rw [abs_of_nonneg hpos] at hgap
    nlinarith [sq_nonneg ((xiSpectralPoint q).re - 4),
      sq_nonneg (xiSpectralPoint q).im]
  · rw [abs_of_nonpos hneg] at hgap
    nlinarith [sq_nonneg (-(xiSpectralPoint q).re - 4),
      sq_nonneg (xiSpectralPoint q).im]

/-- Gaussian convergence is uniform over the complete actual Xi spectrum. -/
theorem norm_xiSignedHeatOrientationWindow_sub_le (N : ℕ) (q : XiZeroCopy) :
    ‖xiSignedHeatOrientationWindow N q - deningerArithmeticFEOrientation q‖ ≤
      2 * Real.exp (-(N : ℝ) ^ 2) := by
  have hsector := (xiSpectralPoint_normSq_lt_two_mul_sq_re q).le
  rw [← Complex.sq_norm] at hsector
  have h := norm_complexSignedGaussianWindow_sub_le N
    (two_le_re_sq_xiSpectralPoint q) hsector
  rw [xi_signed_gaussian_integral_eq_orientation q] at h
  exact h

/-- Every finite signed heat window reverses pure FE parity. -/
theorem xiSignedHeatOrientationWindow_reflect (N : ℕ) (q : XiZeroCopy) :
    xiSignedHeatOrientationWindow N (xiZeroCopyReflectEquiv q) =
      -xiSignedHeatOrientationWindow N q := by
  simp only [xiSignedHeatOrientationWindow, xiSpectralPoint_reflect,
    complexSignedGaussianWindow_neg]

/-- Uniform square-summability bound for signed heat applied to any divisor Hilbert vector. -/
theorem summable_sq_xiSignedHeatOrientationWindow_mul
    (N : ℕ) (v : lp (fun _ : XiZeroCopy => ℂ) 2) :
    Summable (fun q => ‖xiSignedHeatOrientationWindow N q * v q‖ ^ (2 : ℕ)) := by
  refine Summable.of_nonneg_of_le (fun q => sq_nonneg _)
    (fun q => ?_) ((HilbertSchmidt.summable_coe_sq v).mul_left 4)
  rw [norm_mul, mul_pow]
  have h := norm_xiSignedHeatOrientationWindow_le N q
  have hs : ‖xiSignedHeatOrientationWindow N q‖ ^ 2 ≤ 4 := by
    nlinarith [norm_nonneg (xiSignedHeatOrientationWindow N q)]
  exact mul_le_mul_of_nonneg_right hs (sq_nonneg _)

/-- The bounded signed heat cutoff on the full Xi divisor Hilbert carrier. -/
def xiSignedHeatOrientationLp (N : ℕ) (v : lp (fun _ : XiZeroCopy => ℂ) 2) :
    lp (fun _ : XiZeroCopy => ℂ) 2 :=
  ⟨fun q => xiSignedHeatOrientationWindow N q * v q,
    HilbertSchmidt.memℓp_of_sq (summable_sq_xiSignedHeatOrientationWindow_mul N v)⟩

@[simp] theorem xiSignedHeatOrientationLp_apply
    (N : ℕ) (v : lp (fun _ : XiZeroCopy => ℂ) 2) (q : XiZeroCopy) :
    xiSignedHeatOrientationLp N v q = xiSignedHeatOrientationWindow N q * v q := rfl

theorem xiSignedHeatOrientationLp_parity
    (N : ℕ) {s : ℂ} {v : lp (fun _ : XiZeroCopy => ℂ) 2}
    (hv : XiFunctionalEquationParity s v) :
    XiFunctionalEquationParity (-s) (xiSignedHeatOrientationLp N v) := by
  intro q
  rw [xiSignedHeatOrientationLp_apply, xiSignedHeatOrientationLp_apply,
    xiSignedHeatOrientationWindow_reflect, hv q]
  ring

end

end RHTower
