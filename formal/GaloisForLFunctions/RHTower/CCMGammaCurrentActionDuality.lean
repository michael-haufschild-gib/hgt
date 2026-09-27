import GaloisForLFunctions.RHTower.CCMCoherentMidpointGauge

/-!
# Signed current and renormalized Gamma action in both directions

The action of an arbitrary coherent field is the Gamma increment energy
plus twice its real signed current. Thus action invariance and current
conservation are equivalent. Its first variation identifies every invisible
direction, including the actual midpoint-even prime-plus-terminal field.

These are field-parameter variational identities. They do not presume an
Euler--Lagrange time evolution or a positive conserved energy for RH.
-/

noncomputable section
open Complex
open scoped InnerProduct

namespace RHTower

def ccmGammaIncrementAction (f : SoninL2) (r : ℝ) (v : SoninL2) : ℝ :=
  ‖(Real.sqrt (ccmGammaHigherBinetModeDensity |r|) : ℂ) • (logTranslationCLM r f - f) +
    (Real.sqrt (ccmGammaHigherBinetDualDensity |r|) : ℂ) • v‖ ^ 2 -
      ccmGammaHigherBinetDualDensity |r| * ‖v‖ ^ 2

/-- The literal reciprocal Gamma square reconstructs the signed current. -/
theorem ccmGammaIncrementAction_eq (f v : SoninL2) (r : ℝ) :
    ccmGammaIncrementAction f r v =
      ccmGammaHigherBinetModeDensity |r| * ccmActualHeadTranslationDefect |r| f +
        2 * (inner ℂ (logTranslationCLM r f - f) v).re := by
  by_cases hr : r = 0
  · subst r
    simp [ccmGammaIncrementAction, ccmGammaHigherBinetModeDensity,
      ccmGammaHigherBinetDualDensity, ccmActualHeadTranslationDefect, logTranslationCLM_zero_apply]
  have hm : 0 ≤ ccmGammaHigherBinetModeDensity |r| :=
    (ccmGammaHigherBinetModeDensity_pos (abs_pos.mpr hr)).le
  have hk : 0 ≤ ccmGammaHigherBinetDualDensity |r| :=
    ccmGammaHigherBinetDualDensity_nonneg (abs_nonneg r)
  have hsqrt : Real.sqrt (ccmGammaHigherBinetModeDensity |r|) *
      Real.sqrt (ccmGammaHigherBinetDualDensity |r|) = 1 := by
    rw [← Real.sqrt_mul hm, ccmGammaHigherBinetModeDensity_mul_dual (abs_pos.mpr hr), Real.sqrt_one]
  have hnorm (c : ℝ) (hc : 0 ≤ c) (w : SoninL2) :
      ‖(Real.sqrt c : ℂ) • w‖ ^ 2 = c * ‖w‖ ^ 2 := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs, Real.sq_sqrt hc]
  rw [ccmGammaIncrementAction, norm_add_sq (𝕜 := ℂ), RCLike.re_eq_complex_re,
    hnorm _ hm, hnorm _ hk, ccmActualHeadTranslationDefect_abs, ccmActualHeadTranslationDefect]
  simp only [inner_smul_left, inner_smul_right, Complex.conj_ofReal, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hscale := congrArg (fun x : ℝ => x * (inner ℂ (logTranslationCLM r f - f) v).re) hsqrt
  nlinarith only [hscale]

/-- Conservation of the current and invariance of the action are equivalent. -/
theorem ccmGammaIncrementAction_eq_iff_current_eq (f v w : SoninL2) (r : ℝ) :
    ccmGammaIncrementAction f r v = ccmGammaIncrementAction f r w ↔
      (inner ℂ (logTranslationCLM r f - f) v).re =
        (inner ℂ (logTranslationCLM r f - f) w).re := by
  rw [ccmGammaIncrementAction_eq, ccmGammaIncrementAction_eq]
  constructor <;> intro h <;> linarith only [h]

/-- Exact first-order change under an arbitrary real field displacement. -/
theorem ccmGammaIncrementAction_add_real_smul (f v z : SoninL2) (r θ : ℝ) :
    ccmGammaIncrementAction f r (v + (θ : ℂ) • z) =
      ccmGammaIncrementAction f r v + 2 * θ * (inner ℂ (logTranslationCLM r f - f) z).re := by
  rw [ccmGammaIncrementAction_eq, ccmGammaIncrementAction_eq, inner_add_right,
    Complex.add_re, inner_smul_right, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  ring

theorem hasDerivAt_ccmGammaIncrementAction_add_real_smul (f v z : SoninL2) (r θ : ℝ) :
    HasDerivAt (fun η : ℝ => ccmGammaIncrementAction f r (v + (η : ℂ) • z))
      (2 * (inner ℂ (logTranslationCLM r f - f) z).re) θ := by
  have he : (fun η : ℝ => ccmGammaIncrementAction f r (v + (η : ℂ) • z)) =
      fun η : ℝ => ccmGammaIncrementAction f r v +
        (2 * (inner ℂ (logTranslationCLM r f - f) z).re) * η := by
    funext η
    rw [ccmGammaIncrementAction_add_real_smul]
    ring
  rw [he]
  exact (hasDerivAt_const_mul (x := θ)
    (2 * (inner ℂ (logTranslationCLM r f - f) z).re)).const_add (ccmGammaIncrementAction f r v)

/-- Every continuous translation symmetry is exactly an invisible current direction. -/
theorem ccmGammaIncrementAction_translation_invariant_iff (f v z : SoninL2) (r : ℝ) :
    (∀ θ : ℝ, ccmGammaIncrementAction f r (v + (θ : ℂ) • z) = ccmGammaIncrementAction f r v) ↔
      (inner ℂ (logTranslationCLM r f - f) z).re = 0 := by
  constructor
  · intro h
    have h1 := h 1
    rw [ccmGammaIncrementAction_add_real_smul] at h1
    linarith only [h1]
  · intro hz θ
    rw [ccmGammaIncrementAction_add_real_smul, hz, mul_zero, add_zero]

/-- The midpoint construction is the same action on the literal arithmetic gauge field. -/
theorem ccmGammaIncrementAction_midpointGauge (T : ℝ) (N : ℕ) (f : SoninL2) (r θ : ℝ) :
    ccmGammaIncrementAction f r (ccmActualHeadMidpointGaugeField T N f r θ) =
      ccmActualHeadMidpointGaugeAction T N f r θ := rfl

/-- The arithmetic even channel supplies an explicit continuous action symmetry. -/
theorem ccmGammaIncrementAction_midpointEven_invariant (T : ℝ) (N : ℕ)
    (f v : SoninL2) (r θ : ℝ) :
    ccmGammaIncrementAction f r (v + (θ : ℂ) • ccmActualHeadMidpointEvenField T N f r) =
      ccmGammaIncrementAction f r v :=
  (ccmGammaIncrementAction_translation_invariant_iff f v
    (ccmActualHeadMidpointEvenField T N f r) r).mpr
      (re_inner_increment_midpointEven_zero T N f r) θ

end RHTower
