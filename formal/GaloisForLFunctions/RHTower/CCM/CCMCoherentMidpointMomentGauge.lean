import GaloisForLFunctions.RHTower.CCM.CCMCoherentMidpointSignedMoment
import GaloisForLFunctions.RHTower.CCM.CCMCoherentMidpointSpectralGamma
import GaloisForLFunctions.RHTower.CCM.CCMActualHeadApertureCosineGaugeQuotient

/-!
# Removing the signed first moment by an exact physical null direction

A translation pair beyond the aperture diameter has zero pairing with every
physical source. Its midpoint sine can therefore cancel the entire first
moment without changing the signed current. The resulting representative has
a global quartic bound. The explicit coefficient is not asserted to be uniform
in the arithmetic cutoff or aperture.
-/

noncomputable section
open MeasureTheory
open scoped InnerProduct

namespace RHTower

def ccmMidpointExteriorShift (a : SuzukiPositiveAperture) (r : ℝ) : ℝ :=
  2*a.1+|r|+1

def ccmMidpointExteriorFrequency (a : SuzukiPositiveAperture) (r : ℝ) : ℝ :=
  2*Real.pi*(ccmMidpointExteriorShift a r+r/2)

theorem ccmMidpointExteriorShift_ge (a : SuzukiPositiveAperture) (r : ℝ) :
    2*a.1 ≤ ccmMidpointExteriorShift a r ∧
      2*a.1 ≤ r+ccmMidpointExteriorShift a r := by
  unfold ccmMidpointExteriorShift
  constructor <;> linarith [abs_nonneg r, neg_abs_le r]

theorem ccmMidpointExteriorFrequency_pos (a : SuzukiPositiveAperture) (r : ℝ) :
    0 < ccmMidpointExteriorFrequency a r := by
  have ha := a.2
  have hs : 0 < ccmMidpointExteriorShift a r+r/2 := by
    unfold ccmMidpointExteriorShift
    linarith [abs_nonneg r, neg_abs_le r]
  exact mul_pos (mul_pos (by norm_num) Real.pi_pos) hs

def ccmMidpointExteriorCurrent (a : SuzukiPositiveAperture) (r ξ : ℝ) : ℝ :=
  -2*Real.sin (Real.pi*r*ξ)*Real.sin (ccmMidpointExteriorFrequency a r*ξ)

/-- The added sine current is a difference of two physically disjoint cosines. -/
theorem ccmMidpointExteriorCurrent_eq_cosine_sub (a : SuzukiPositiveAperture) (r ξ : ℝ) :
    ccmMidpointExteriorCurrent a r ξ =
      Real.cos (2*Real.pi*(r+ccmMidpointExteriorShift a r)*ξ) -
        Real.cos (2*Real.pi*ccmMidpointExteriorShift a r*ξ) := by
  have h₁ : 2*Real.pi*(r+ccmMidpointExteriorShift a r)*ξ =
      ccmMidpointExteriorFrequency a r*ξ+Real.pi*r*ξ := by
    unfold ccmMidpointExteriorFrequency
    ring
  have h₂ : 2*Real.pi*ccmMidpointExteriorShift a r*ξ =
      ccmMidpointExteriorFrequency a r*ξ-Real.pi*r*ξ := by
    unfold ccmMidpointExteriorFrequency
    ring
  rw [h₁, h₂, Real.cos_add, Real.cos_sub, ccmMidpointExteriorCurrent]
  ring

theorem integrable_ccmMidpointExteriorCurrent (a : SuzukiPositiveAperture)
    (f : SoninL2) (r : ℝ) :
    Integrable (fun ξ : ℝ => ccmMidpointExteriorCurrent a r ξ * ‖fourierUnitary f ξ‖^2) := by
  simp_rw [ccmMidpointExteriorCurrent_eq_cosine_sub, sub_mul]
  exact (integrable_ccmActualHeadCosineSpectralDensity _ f).sub
    (integrable_ccmActualHeadCosineSpectralDensity _ f)

/-- The exterior direction is exactly null for every physical aperture source. -/
theorem integral_ccmMidpointExteriorCurrent_zero (a : SuzukiPositiveAperture)
    (f : suzukiApertureHilbert a) (r : ℝ) :
    (∫ ξ : ℝ, ccmMidpointExteriorCurrent a r ξ * ‖fourierUnitary f.1 ξ‖^2) = 0 := by
  simp_rw [ccmMidpointExteriorCurrent_eq_cosine_sub, sub_mul]
  rw [integral_sub (integrable_ccmActualHeadCosineSpectralDensity _ f.1)
      (integrable_ccmActualHeadCosineSpectralDensity _ f.1),
    integral_ccmActualHeadCosineSpectralDensity_eq_zero_of_two_aperture_le a f
      (ccmMidpointExteriorShift_ge a r).2,
    integral_ccmActualHeadCosineSpectralDensity_eq_zero_of_two_aperture_le a f
      (ccmMidpointExteriorShift_ge a r).1, sub_self]

def ccmActualHeadMomentCancelledSine (a : SuzukiPositiveAperture) (N : ℕ) (r ξ : ℝ) : ℝ :=
  ccmActualHeadMidpointSineSymbol (2*a.1) N r ξ -
    (ccmActualHeadMidpointSignedMoment (2*a.1) N r/ccmMidpointExteriorFrequency a r)*
      Real.sin (ccmMidpointExteriorFrequency a r*ξ)

def ccmActualHeadMomentCancelledCurrent (a : SuzukiPositiveAperture) (N : ℕ) (r ξ : ℝ) : ℝ :=
  -2*Real.sin (Real.pi*r*ξ)*ccmActualHeadMomentCancelledSine a N r ξ

private theorem cancelled_current_eq (a : SuzukiPositiveAperture) (N : ℕ) (r ξ : ℝ) :
    ccmActualHeadMomentCancelledCurrent a N r ξ =
      ccmActualHeadMidpointCurrentSymbol (2*a.1) N r ξ -
        (ccmActualHeadMidpointSignedMoment (2*a.1) N r/ccmMidpointExteriorFrequency a r)*
          ccmMidpointExteriorCurrent a r ξ := by
  unfold ccmActualHeadMomentCancelledCurrent ccmActualHeadMomentCancelledSine
    ccmActualHeadMidpointCurrentSymbol ccmMidpointExteriorCurrent
  ring

theorem integrable_ccmActualHeadMomentCancelledCurrent (a : SuzukiPositiveAperture)
    (N : ℕ) (f : SoninL2) (r : ℝ) :
    Integrable (fun ξ : ℝ => ccmActualHeadMomentCancelledCurrent a N r ξ * ‖fourierUnitary f ξ‖^2) := by
  simp_rw [cancelled_current_eq, sub_mul, mul_assoc]
  exact (integrable_ccmActualHeadMidpointSpectralCurrent _ N f r).sub
    ((integrable_ccmMidpointExteriorCurrent a f r).const_mul _)

/-- Removing the first moment preserves the literal completed arithmetic current exactly. -/
theorem re_inner_increment_completed_eq_momentCancelled_spectral
    (a : SuzukiPositiveAperture) (N : ℕ) (f : suzukiApertureHilbert a) (r : ℝ) :
    (inner ℂ (logTranslationCLM r f.1-f.1)
      (ccmActualHeadQuantileCompletedCoherentField (2*a.1) N f.1 r)).re =
      ∫ ξ : ℝ, ccmActualHeadMomentCancelledCurrent a N r ξ * ‖fourierUnitary f.1 ξ‖^2 := by
  rw [re_inner_increment_completed_eq_midpoint_spectral]
  simp_rw [cancelled_current_eq, sub_mul, mul_assoc]
  rw [integral_sub (integrable_ccmActualHeadMidpointSpectralCurrent _ _ _ _)
      ((integrable_ccmMidpointExteriorCurrent a f.1 r).const_mul _),
    integral_const_mul, integral_ccmMidpointExteriorCurrent_zero, mul_zero, sub_zero]

def ccmActualHeadMomentCancelledCubicBudget (a : SuzukiPositiveAperture) (N : ℕ) (r : ℝ) : ℝ :=
  ccmActualHeadMidpointCubicMoment (2*a.1) N r +
    |ccmActualHeadMidpointSignedMoment (2*a.1) N r/ccmMidpointExteriorFrequency a r| *
      |ccmMidpointExteriorFrequency a r|^3

theorem ccmActualHeadMomentCancelledCubicBudget_nonneg
    (a : SuzukiPositiveAperture) (N : ℕ) (r : ℝ) :
    0 ≤ ccmActualHeadMomentCancelledCubicBudget a N r := by
  have h := ccmActualHeadMidpointCubicMoment_nonneg (2*a.1) N r
  unfold ccmActualHeadMomentCancelledCubicBudget
  positivity

/-- The entire linear term is removed by an explicit null correction. -/
theorem abs_ccmActualHeadMomentCancelledSine_le (a : SuzukiPositiveAperture)
    (N : ℕ) (r ξ : ℝ) :
    |ccmActualHeadMomentCancelledSine a N r ξ| ≤
      |ξ|^3/6 * ccmActualHeadMomentCancelledCubicBudget a N r := by
  let M := ccmActualHeadMidpointSignedMoment (2*a.1) N r
  let β := ccmMidpointExteriorFrequency a r
  have hβ : β ≠ 0 := ne_of_gt (ccmMidpointExteriorFrequency_pos a r)
  have he : ccmActualHeadMomentCancelledSine a N r ξ =
      (ccmActualHeadMidpointSineSymbol (2*a.1) N r ξ-ξ*M) -
        (M/β)*(Real.sin (β*ξ)-β*ξ) := by
    change ccmActualHeadMidpointSineSymbol (2*a.1) N r ξ -
      (M/β)*Real.sin (β*ξ) = _
    have hc : M/β*β = M := div_mul_cancel₀ M hβ
    linear_combination -ξ*hc
  rw [he]
  refine (abs_sub _ _).trans ?_
  have hsin := mul_le_mul_of_nonneg_left (Real.abs_sub_sin_le (β*ξ)) (abs_nonneg (M/β))
  rw [abs_sub_comm (β*ξ), abs_mul, mul_pow] at hsin
  rw [abs_mul]
  have hS := abs_ccmActualHeadMidpointSineSymbol_sub_moment_le (2*a.1) N r ξ
  have h := add_le_add hS hsin
  dsimp only [ccmActualHeadMomentCancelledCubicBudget, M, β] at h ⊢
  convert h using 1; ring

/-- A global quartic estimate for a representative of the exact signed current. -/
theorem abs_ccmActualHeadMomentCancelledCurrent_le (a : SuzukiPositiveAperture)
    (N : ℕ) (r ξ : ℝ) :
    |ccmActualHeadMomentCancelledCurrent a N r ξ| ≤
      (|Real.pi*r| / 3 * ccmActualHeadMomentCancelledCubicBudget a N r)*ξ^4 := by
  have hs : |Real.sin (Real.pi*r*ξ)| ≤ |Real.pi*r| * |ξ| := by
    simpa only [abs_mul] using Real.abs_sin_le_abs (x := Real.pi*r*ξ)
  have h := mul_le_mul (mul_le_mul_of_nonneg_left hs (by norm_num : (0:ℝ) ≤ 2))
    (abs_ccmActualHeadMomentCancelledSine_le a N r ξ) (abs_nonneg _)
      (by positivity : 0 ≤ 2*(|Real.pi*r| * |ξ|))
  have hpow : |ξ|^4 = ξ^4 := by
    rw [show (4 : ℕ) = 2*2 by norm_num, pow_mul, sq_abs, pow_mul]
  unfold ccmActualHeadMomentCancelledCurrent
  simp only [abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    _ ≤ 2*(|Real.pi*r| * |ξ|)*(|ξ|^3/6*ccmActualHeadMomentCancelledCubicBudget a N r) := h
    _ = (|Real.pi*r| / 3*ccmActualHeadMomentCancelledCubicBudget a N r)*|ξ|^4 := by ring
    _ = _ := by rw [hpow, abs_mul]

/-- The actual completed current can use the quartic representative at every displacement. -/
theorem ccmActualHeadCompletedQuantileCurrent_eq_momentCancelled_spectral
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) :
    ccmActualHeadCompletedQuantileCurrent a f =
      ∫ r : ℝ, ∫ ξ : ℝ,
        ccmActualHeadMomentCancelledCurrent a (Nat.floor (Real.exp (2*a.1))+1) r ξ *
          ‖fourierUnitary f.1 ξ‖^2 := by
  rw [ccmActualHeadCompletedQuantileCurrent_eq_midpoint_spectral]
  apply integral_congr_ae
  filter_upwards with r
  exact (re_inner_increment_completed_eq_midpoint_spectral _ _ _ _).symm.trans
    (re_inner_increment_completed_eq_momentCancelled_spectral a _ f r)

/-- The original Weil source is unchanged after exact first-moment cancellation. -/
theorem ccmRestrictedWeilSourceQuadratic_eq_momentCancelled_spectral
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    let f := ccmArchimedeanFormToAperture a u
    ccmRestrictedWeilSourceQuadratic a u =
      (2*gammaHardyPhaseRate 0+4)*‖f‖^2 + ccmActualHeadGammaHigherBinetModeEnergy f.1 +
        2*(∫ r : ℝ, ∫ ξ : ℝ,
          ccmActualHeadMomentCancelledCurrent a (Nat.floor (Real.exp (2*a.1))+1) r ξ *
            ‖fourierUnitary f.1 ξ‖^2) := by
  have h := ccmRestrictedWeilSourceQuadratic_eq_midpoint_spectral_current a u
  dsimp only at h ⊢
  rw [← ccmActualHeadCompletedQuantileCurrent_eq_midpoint_spectral,
    ccmActualHeadCompletedQuantileCurrent_eq_momentCancelled_spectral] at h
  exact h

end RHTower
