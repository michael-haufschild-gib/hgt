import GaloisForLFunctions.RHTower.CCMCoherentMidpointEnergy
import GaloisForLFunctions.RHTower.CCMActualHeadCoherentQuantileGammaPhaseSquare

/-!
# A continuous invisible direction of the actual prime--Gamma action

The midpoint half-sum can be scaled by any real parameter without changing
the signed current. Its energy cost is exactly quadratic. Subtracting that
cost from the reciprocal Gamma square gives an action constant along the
entire orbit, with the original arithmetic field at parameter one.

This is a proved field-parameter symmetry and its zero first variation.
It is not an assertion of a coercive time-evolution energy or source positivity.
-/

noncomputable section
open Complex MeasureTheory
open scoped InnerProduct BigOperators

namespace RHTower

theorem re_inner_ccmActualHeadMidpoint_odd_even_zero (T : ℝ) (N : ℕ)
    (f : SoninL2) (r : ℝ) :
    (inner ℂ (ccmActualHeadMidpointOddField T N f r)
      (ccmActualHeadMidpointEvenField T N f r)).re = 0 := by
  have h := norm_sq_ccmActualHeadCoherentField_midpoint_split T N f r
  conv_lhs at h => rw [ccmActualHeadCoherentField_eq_midpoint_parts T N f r]
  rw [norm_add_sq (𝕜 := ℂ), RCLike.re_eq_complex_re] at h
  linarith only [h]

def ccmActualHeadMidpointGaugeField (T : ℝ) (N : ℕ) (f : SoninL2)
    (r θ : ℝ) : SoninL2 :=
  ccmActualHeadMidpointOddField T N f r + (θ : ℂ) • ccmActualHeadMidpointEvenField T N f r

theorem ccmActualHeadMidpointGaugeField_one (T : ℝ) (N : ℕ) (f : SoninL2) (r : ℝ) :
    ccmActualHeadMidpointGaugeField T N f r 1 =
      ccmActualHeadQuantileCompletedCoherentField T N f r := by
  simp only [ccmActualHeadMidpointGaugeField, Complex.ofReal_one, one_smul]
  exact (ccmActualHeadCoherentField_eq_midpoint_parts T N f r).symm

theorem ccmActualHeadMidpointGaugeField_zero (T : ℝ) (N : ℕ) (f : SoninL2) (r : ℝ) :
    ccmActualHeadMidpointGaugeField T N f r 0 = ccmActualHeadMidpointOddField T N f r := by
  simp [ccmActualHeadMidpointGaugeField]

/-- The exact complete signed current is conserved along the real gauge orbit. -/
theorem re_inner_increment_midpointGauge (T : ℝ) (N : ℕ) (f : SoninL2) (r θ : ℝ) :
    (inner ℂ (logTranslationCLM r f - f) (ccmActualHeadMidpointGaugeField T N f r θ)).re =
      (inner ℂ (logTranslationCLM r f - f)
        (ccmActualHeadQuantileCompletedCoherentField T N f r)).re := by
  rw [ccmActualHeadMidpointGaugeField, inner_add_right, Complex.add_re,
    inner_smul_right, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, re_inner_increment_midpointEven_zero, mul_zero, add_zero]
  exact re_inner_increment_midpointOdd T N f r

/-- The invisible energy is the exact quadratic cost of the gauge parameter. -/
theorem norm_sq_ccmActualHeadMidpointGaugeField (T : ℝ) (N : ℕ)
    (f : SoninL2) (r θ : ℝ) :
    ‖ccmActualHeadMidpointGaugeField T N f r θ‖ ^ 2 =
      ‖ccmActualHeadMidpointOddField T N f r‖ ^ 2 +
        θ ^ 2 * ‖ccmActualHeadMidpointEvenField T N f r‖ ^ 2 := by
  rw [ccmActualHeadMidpointGaugeField, norm_add_sq (𝕜 := ℂ), RCLike.re_eq_complex_re, inner_smul_right,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    re_inner_ccmActualHeadMidpoint_odd_even_zero, mul_zero, mul_zero, add_zero,
    norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]

theorem ccmActualHeadMidpointOddField_minimizes_gauge_norm (T : ℝ) (N : ℕ)
    (f : SoninL2) (r θ : ℝ) :
    ‖ccmActualHeadMidpointOddField T N f r‖ ^ 2 ≤
      ‖ccmActualHeadMidpointGaugeField T N f r θ‖ ^ 2 := by
  rw [norm_sq_ccmActualHeadMidpointGaugeField]
  exact le_add_of_nonneg_right (mul_nonneg (sq_nonneg _) (sq_nonneg _))

/-- The phase square with its coherent self-energy subtracted. -/
def ccmActualHeadMidpointGaugeAction (T : ℝ) (N : ℕ) (f : SoninL2) (r θ : ℝ) : ℝ :=
  ‖(Real.sqrt (ccmGammaHigherBinetModeDensity |r|) : ℂ) • (logTranslationCLM r f - f) +
    (Real.sqrt (ccmGammaHigherBinetDualDensity |r|) : ℂ) •
      ccmActualHeadMidpointGaugeField T N f r θ‖ ^ 2 -
    ccmGammaHigherBinetDualDensity |r| * ‖ccmActualHeadMidpointGaugeField T N f r θ‖ ^ 2

private theorem gaugeAction_expansion (T : ℝ) (N : ℕ) (f : SoninL2) (r θ : ℝ) :
    ccmActualHeadMidpointGaugeAction T N f r θ =
      ‖(Real.sqrt (ccmGammaHigherBinetModeDensity |r|) : ℂ) • (logTranslationCLM r f - f)‖ ^ 2 +
        2 * (Real.sqrt (ccmGammaHigherBinetModeDensity |r|) *
          Real.sqrt (ccmGammaHigherBinetDualDensity |r|) *
            (inner ℂ (logTranslationCLM r f - f)
              (ccmActualHeadQuantileCompletedCoherentField T N f r)).re) := by
  have hnorm (v : SoninL2) :
      ‖(Real.sqrt (ccmGammaHigherBinetDualDensity |r|) : ℂ) • v‖ ^ 2 =
        ccmGammaHigherBinetDualDensity |r| * ‖v‖ ^ 2 := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs,
      Real.sq_sqrt (ccmGammaHigherBinetDualDensity_nonneg (abs_nonneg r))]
  rw [ccmActualHeadMidpointGaugeAction, norm_add_sq (𝕜 := ℂ), hnorm]
  simp only [RCLike.re_eq_complex_re, inner_smul_left, inner_smul_right, Complex.conj_ofReal, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    re_inner_increment_midpointGauge]
  ring

/-- Continuous field symmetry of the literal renormalized Gamma action. -/
theorem ccmActualHeadMidpointGaugeAction_invariant (T : ℝ) (N : ℕ)
    (f : SoninL2) (r θ η : ℝ) :
    ccmActualHeadMidpointGaugeAction T N f r θ =
      ccmActualHeadMidpointGaugeAction T N f r η := by
  rw [gaugeAction_expansion, gaugeAction_expansion]

/-- Vanishing first variation follows from the proved action symmetry. -/
theorem hasDerivAt_ccmActualHeadMidpointGaugeAction (T : ℝ) (N : ℕ)
    (f : SoninL2) (r θ : ℝ) :
    HasDerivAt (ccmActualHeadMidpointGaugeAction T N f r) 0 θ := by
  have he : ccmActualHeadMidpointGaugeAction T N f r =
      fun _ : ℝ => ccmActualHeadMidpointGaugeAction T N f r 0 :=
    funext fun η => ccmActualHeadMidpointGaugeAction_invariant T N f r η 0
  rw [he]
  exact hasDerivAt_const _ _

/-- The action is exactly the Gamma mode term plus the full signed current. -/
theorem ccmActualHeadMidpointGaugeAction_eq_actual_terms (T : ℝ) (N : ℕ)
    (f : SoninL2) (r θ : ℝ) :
    ccmActualHeadMidpointGaugeAction T N f r θ =
      ccmGammaHigherBinetModeDensity |r| * ccmActualHeadTranslationDefect |r| f +
        2 * (inner ℂ (logTranslationCLM r f - f)
          (ccmActualHeadQuantileCompletedCoherentField T N f r)).re := by
  rw [ccmActualHeadMidpointGaugeAction_invariant T N f r θ 1,
    ccmActualHeadMidpointGaugeAction, ccmActualHeadMidpointGaugeField_one,
    ccmActualHeadCoherentQuantileGammaPhaseSquare_integrand_eq]
  ring

end RHTower
