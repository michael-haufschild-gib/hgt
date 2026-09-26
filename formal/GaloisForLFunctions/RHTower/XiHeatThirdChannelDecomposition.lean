import GaloisForLFunctions.RHTower.XiGaussianHeatHankelLadder
import GaloisForLFunctions.HTGeometry.RelativeGapChannelGauge
import GaloisForLFunctions.HTGeometry.QuadraticHeatPhaseDefect

/-!
# Total and contrast channels of the actual third Xi heat-Hankel form

The coefficient channels are the total, the endpoint difference, and the second
difference.  All three diagonal contributions and all three couplings are kept.
The same form is the full multiplicity-exact Xi sum of a positive norm energy
minus its imaginary-square defect.
-/

namespace RHTower
noncomputable section
open scoped BigOperators
open GaloisForLFunctions.HTGeometry

def xiHeatThirdPolynomial (a b c : ℝ) : Polynomial ℝ :=
  Polynomial.C a + Polynomial.C b * Polynomial.X + Polynomial.C c * Polynomial.X ^ 2

theorem eval_xiHeatThirdPolynomial (a b c : ℝ) (z : ℂ) :
    evalRealPolynomial (xiHeatThirdPolynomial a b c) z = quadraticHeatValue a b c z := by
  simp [evalRealPolynomial, xiHeatThirdPolynomial, quadraticHeatValue]

/-- The literal degree-two quadratic form of the five actual Gaussian Xi moments. -/
def xiHeatThirdQuadratic (a b c t : ℝ) : ℝ :=
  a ^ 2 * xiGaussianHeatMomentReal 0 t +
    2 * a * b * xiGaussianHeatMomentReal 1 t +
    (b ^ 2 + 2 * a * c) * xiGaussianHeatMomentReal 2 t +
    2 * b * c * xiGaussianHeatMomentReal 3 t +
    c ^ 2 * xiGaussianHeatMomentReal 4 t

theorem xiHeatThirdQuadratic_eq_hankel (a b c t : ℝ) :
    xiHeatThirdQuadratic a b c t =
      xiHeatHankelForm 3 (fun n => if n = 0 then a else if n = 1 then b else c) t := by
  simp [xiHeatThirdQuadratic, xiHeatHankelForm, Finset.sum_range_succ]
  ring

/-- The homogeneous contrasts of the three coefficient channels. -/
theorem xiHeatThird_coefficient_contrast (f : Fin 3 → ℝ) (i : Fin 3) :
    relativeChannelContrast id (fun _ : Fin 3 => (1 : ℝ)) f i =
      3 * f i - (f 0 + f 1 + f 2) := by
  simp [relativeChannelContrast, relativeChannelMass, relativeChannelScore,
    Fin.sum_univ_three]

/-- The two retained contrast coordinates are differences of drift-invariant channel contrasts. -/
theorem xiHeatThird_contrast_coordinates (f : Fin 3 → ℝ) :
    let k := relativeChannelContrast id (fun _ : Fin 3 => (1 : ℝ)) f
    (k 0 - k 2) / 3 = f 0 - f 2 ∧
      (k 0 - 2 * k 1 + k 2) / 3 = f 0 - 2 * f 1 + f 2 := by
  dsimp only
  simp only [xiHeatThird_coefficient_contrast]
  constructor <;> ring

/-- Inverting the total and the two contrasts loses no coefficient. -/
theorem xiHeatThird_total_contrast_reconstruction (a b c t : ℝ) :
    xiHeatThirdQuadratic a b c t =
      xiHeatThirdQuadratic
        ((a + b + c) / 3 + (a - c) / 2 + (a - 2 * b + c) / 6)
        ((a + b + c) / 3 - (a - 2 * b + c) / 3)
        ((a + b + c) / 3 - (a - c) / 2 + (a - 2 * b + c) / 6) t := by
  congr 1 <;> ring

/-- All diagonal and mixed terms in the total/contrast basis, with no discarded global mode. -/
theorem xiHeatThird_total_contrast_expansion (T U V t : ℝ) :
    xiHeatThirdQuadratic (T / 3 + U / 2 + V / 6) (T / 3 - V / 3)
        (T / 3 - U / 2 + V / 6) t =
      T ^ 2 / 9 * (xiGaussianHeatMomentReal 0 t + 2 * xiGaussianHeatMomentReal 1 t +
        3 * xiGaussianHeatMomentReal 2 t + 2 * xiGaussianHeatMomentReal 3 t +
        xiGaussianHeatMomentReal 4 t) +
      U ^ 2 / 4 * (xiGaussianHeatMomentReal 0 t - 2 * xiGaussianHeatMomentReal 2 t +
        xiGaussianHeatMomentReal 4 t) +
      V ^ 2 / 36 * (xiGaussianHeatMomentReal 0 t - 4 * xiGaussianHeatMomentReal 1 t +
        6 * xiGaussianHeatMomentReal 2 t - 4 * xiGaussianHeatMomentReal 3 t +
        xiGaussianHeatMomentReal 4 t) +
      T * U / 3 * (xiGaussianHeatMomentReal 0 t + xiGaussianHeatMomentReal 1 t -
        xiGaussianHeatMomentReal 3 t - xiGaussianHeatMomentReal 4 t) +
      T * V / 9 * (xiGaussianHeatMomentReal 0 t - xiGaussianHeatMomentReal 1 t -
        xiGaussianHeatMomentReal 3 t + xiGaussianHeatMomentReal 4 t) +
      U * V / 6 * (xiGaussianHeatMomentReal 0 t - 2 * xiGaussianHeatMomentReal 1 t +
        2 * xiGaussianHeatMomentReal 3 t - xiGaussianHeatMomentReal 4 t) := by
  unfold xiHeatThirdQuadratic
  ring

/-- Positive heat time is parametrized without an external positivity premise. -/
theorem xiHeatThirdQuadratic_eq_trace (a b c τ : ℝ) :
    xiHeatThirdQuadratic a b c (Real.exp τ) =
      xiPolynomialGaussianHeatTraceReal (xiHeatThirdPolynomial a b c) (Real.exp τ) := by
  rw [xiHeatThirdQuadratic_eq_hankel]
  rw [← xiPolynomialGaussianHeatTraceReal_rangeSum (Real.exp_pos τ)]
  congr 1
  simp [xiHeatThirdPolynomial, Finset.sum_range_succ]

def xiHeatThirdAmplitude (a b c τ : ℝ) (q : XiZeroCopy) : ℂ :=
  heatPhaseAmplitude (quadraticHeatValue a b c (xiSpectralPoint q ^ 2))
    (Real.exp τ) (xiSpectralPoint q ^ 2)

theorem xiHeatThirdAmplitude_sq (a b c τ : ℝ) (q : XiZeroCopy) :
    xiHeatThirdAmplitude a b c τ q ^ 2 =
      xiPolynomialGaussianHeatTerm (xiHeatThirdPolynomial a b c) (Real.exp τ) q := by
  rw [xiHeatThirdAmplitude, heatPhaseAmplitude_sq, xiPolynomialGaussianHeatTerm,
    eval_xiHeatThirdPolynomial, xiGaussianHeatTerm]

theorem xiHeatThirdAmplitude_norm_sq (a b c τ : ℝ) (q : XiZeroCopy) :
    ‖xiHeatThirdAmplitude a b c τ q‖ ^ 2 =
      ‖xiPolynomialGaussianHeatTerm (xiHeatThirdPolynomial a b c) (Real.exp τ) q‖ := by
  rw [← xiHeatThirdAmplitude_sq, norm_pow]

theorem summable_xiHeatThirdAmplitude_norm_sq (a b c τ : ℝ) :
    Summable (fun q => ‖xiHeatThirdAmplitude a b c τ q‖ ^ 2) := by
  simpa only [xiHeatThirdAmplitude_norm_sq] using
    (summable_xiPolynomialGaussianHeatTerm (Real.exp_pos τ)
      (xiHeatThirdPolynomial a b c)).norm

theorem summable_xiHeatThirdAmplitude_im_sq (a b c τ : ℝ) :
    Summable (fun q => (xiHeatThirdAmplitude a b c τ q).im ^ 2) := by
  exact Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
    (fun q => heatPhaseAmplitude_im_sq_le_norm_sq _ _ _)
    (summable_xiHeatThirdAmplitude_norm_sq a b c τ)

def xiHeatThirdNormEnergy (a b c τ : ℝ) : ℝ :=
  ∑' q, ‖xiHeatThirdAmplitude a b c τ q‖ ^ 2

def xiHeatThirdPhaseDebt (a b c τ : ℝ) : ℝ :=
  2 * ∑' q, (xiHeatThirdAmplitude a b c τ q).im ^ 2

theorem xiHeatThirdNormEnergy_nonneg (a b c τ : ℝ) :
    0 ≤ xiHeatThirdNormEnergy a b c τ := tsum_nonneg fun _ => sq_nonneg _

theorem xiHeatThirdPhaseDebt_nonneg (a b c τ : ℝ) :
    0 ≤ xiHeatThirdPhaseDebt a b c τ :=
  mul_nonneg (by positivity) (tsum_nonneg fun _ => sq_nonneg _)

/-- Exact full-divisor decomposition; all polynomial cross terms remain in each amplitude. -/
theorem xiHeatThirdQuadratic_eq_energy_sub_debt (a b c τ : ℝ) :
    xiHeatThirdQuadratic a b c (Real.exp τ) =
      xiHeatThirdNormEnergy a b c τ - xiHeatThirdPhaseDebt a b c τ := by
  rw [xiHeatThirdQuadratic_eq_trace, xiPolynomialGaussianHeatTraceReal,
    xiPolynomialGaussianHeatTrace,
    Complex.re_tsum (summable_xiPolynomialGaussianHeatTerm (Real.exp_pos τ) _)]
  have hatom : ∀ q : XiZeroCopy,
      (xiPolynomialGaussianHeatTerm (xiHeatThirdPolynomial a b c) (Real.exp τ) q).re =
        ‖xiHeatThirdAmplitude a b c τ q‖ ^ 2 -
          2 * (xiHeatThirdAmplitude a b c τ q).im ^ 2 := by
    intro q
    rw [← xiHeatThirdAmplitude_sq, Complex.sq_norm, Complex.normSq_apply,
      pow_two, Complex.mul_re]
    ring
  simp_rw [hatom]
  rw [Summable.tsum_sub (summable_xiHeatThirdAmplitude_norm_sq a b c τ)
    ((summable_xiHeatThirdAmplitude_im_sq a b c τ).mul_left 2), tsum_mul_left]
  rfl

end
end RHTower
