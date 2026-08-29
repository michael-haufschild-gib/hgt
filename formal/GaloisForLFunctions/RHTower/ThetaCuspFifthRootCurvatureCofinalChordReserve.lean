import GaloisForLFunctions.HTGeometry.InteriorIntegrationByParts
import GaloisForLFunctions.RHTower.ThetaCuspFifthRootCurvatureLikelihoodSlopeTax

/-!
# Cofinal chord reserve for theta fifth-root curvature

The first completed product fibre has an absolute-value seam, so its literal
two-sided derivative is not the correct endpoint density for a right-chamber
fundamental theorem of calculus.  This module constructs the smooth
positive-side representative and proves exact integral laws for the first
fibre, full reflected source, and cofinal higher tail.

After those endpoint drops are converted into chord data, the cofinal drift
budget factors through the product of the first and higher-tail drops.  More
strongly, all component drops cancel from the remaining C5 criterion: at every
positive modular-center radius,

`source C5 = integrated chord reserve - likelihood tax density`.

The tax density is strictly positive.  Thus any successful C5 proof must
produce a genuinely nonlocal reserve from accumulated full-source flux large
enough to pay both the likelihood-slope-square and likelihood-convexity taxes.
Local likelihood/Riccati sign data alone cannot supply this reserve.
-/

open Real Set Filter Topology MeasureTheory intervalIntegral

namespace RHTower

noncomputable section

/-- Smooth positive-side representative of the first completed fibre's decay flux. -/
def thetaCuspCompletedProductFiberFirstRightDecayFlux (t : ℝ) : ℝ :=
  -2 * thetaCuspSourceTerm t 1 *
    iteratedDeriv 1 (fun s => thetaCuspSourceTerm s 1) t

theorem continuous_thetaCuspCompletedProductFiberFirstRightDecayFlux :
    Continuous thetaCuspCompletedProductFiberFirstRightDecayFlux := by
  have hsource : Continuous (fun s : ℝ => thetaCuspSourceTerm s 1) :=
    continuous_thetaCuspSourceTerm_one
  have hjet : Continuous
      (fun s : ℝ => iteratedDeriv 1 (fun r => thetaCuspSourceTerm r 1) s) := by
    rw [continuous_iff_continuousAt]
    intro s
    exact (hasDerivAt_iteratedDeriv_thetaCuspSourceTerm 1 1 s).continuousAt
  exact (hsource.const_mul (-2)).mul hjet

theorem thetaCuspCompletedProductFiberFirstDecayFlux_zero_eq_right
    {t : ℝ} (ht : 0 < t) :
    thetaCuspCompletedProductFiberFirstDecayFlux 0 t =
      thetaCuspCompletedProductFiberFirstRightDecayFlux t := by
  have hsource := hasDerivAt_iteratedDeriv_thetaCuspSourceTerm 0 1 t
  rw [iteratedDeriv_zero] at hsource
  have hsquare := hsource.pow 2
  have hlocal :
      thetaCuspCompletedProductFiberAmplitude 1 0 =ᶠ[nhds t]
        (fun s => thetaCuspSourceTerm s 1) ^ 2 := by
    filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
    rw [thetaCuspCompletedProductFiberAmplitude_one_zero, abs_of_pos hs]
    rfl
  have hfirst := hasDerivAt_thetaCuspCompletedProductFiberAmplitude_one_zero ht
  have heq := hfirst.unique (hsquare.congr_of_eventuallyEq hlocal)
  norm_num at heq
  unfold thetaCuspCompletedProductFiberFirstRightDecayFlux
  rw [iteratedDeriv_one]
  linarith

theorem intervalIntegral_thetaCuspCompletedProductFiberFirstRightDecayFlux_eq_drop
    {t : ℝ} (ht : 0 < t) :
    (∫ s in 0..t, thetaCuspCompletedProductFiberFirstRightDecayFlux s) =
      thetaCuspCompletedProductFiberFirstDrop 0 t := by
  let F : ℝ → ℝ := thetaCuspCompletedProductFiberAmplitude 1 0
  let D : ℝ → ℝ := thetaCuspCompletedProductFiberFirstRightDecayFlux
  have hcont : Continuous F := by
    unfold F
    convert (continuous_thetaCuspSourceTerm_one.comp continuous_abs).pow 2 using 1
    funext s
    exact thetaCuspCompletedProductFiberAmplitude_one_zero s
  have hD : Continuous D :=
    continuous_thetaCuspCompletedProductFiberFirstRightDecayFlux
  have hderiv : ∀ s ∈ Ioo (0 : ℝ) t,
      HasDerivWithinAt F (-D s) (Ioi s) s := by
    intro s hs
    have hfirst := hasDerivAt_thetaCuspCompletedProductFiberAmplitude_one_zero hs.1
    rw [thetaCuspCompletedProductFiberFirstDecayFlux_zero_eq_right hs.1] at hfirst
    exact hfirst.hasDerivWithinAt
  have hftc := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le
    ht.le hcont.continuousOn hderiv (hD.neg.intervalIntegrable 0 t)
  rw [intervalIntegral.integral_neg] at hftc
  unfold F D thetaCuspCompletedProductFiberFirstDrop at *
  linarith

theorem continuous_thetaCuspReflectedSourceDecayFlux_zero :
    Continuous (thetaCuspReflectedSourceDecayFlux 0) := by
  rw [continuous_iff_continuousAt]
  intro s
  exact (hasDerivAt_thetaCuspReflectedSourceDecayFlux 0 s).continuousAt

theorem intervalIntegral_thetaCuspReflectedSourceDecayFlux_zero_eq_drop
    {t : ℝ} (ht : 0 < t) :
    (∫ s in 0..t, thetaCuspReflectedSourceDecayFlux 0 s) =
      thetaCuspReflectedSourceFirstDrop 0 t := by
  let F : ℝ → ℝ := thetaCuspReflectedSourceProduct 0
  let D : ℝ → ℝ := thetaCuspReflectedSourceDecayFlux 0
  have hcont : Continuous F := by
    rw [continuous_iff_continuousAt]
    intro s
    exact (hasDerivAt_thetaCuspReflectedSourceProduct 0 s).continuousAt
  have hD : Continuous D := continuous_thetaCuspReflectedSourceDecayFlux_zero
  have hderiv : ∀ s ∈ Ioo (0 : ℝ) t,
      HasDerivWithinAt F (-D s) (Ioi s) s := by
    intro s _hs
    exact (hasDerivAt_thetaCuspReflectedSourceProduct 0 s).hasDerivWithinAt
  have hftc := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le
    ht.le hcont.continuousOn hderiv (hD.neg.intervalIntegrable 0 t)
  rw [intervalIntegral.integral_neg] at hftc
  unfold F D thetaCuspReflectedSourceFirstDrop at *
  linarith

/-- Smooth right-chamber representative of the cofinal tail decay flux. -/
def thetaCuspCompletedProductFiberHigherTailRightDecayFlux (t : ℝ) : ℝ :=
  thetaCuspReflectedSourceDecayFlux 0 t -
    thetaCuspCompletedProductFiberFirstRightDecayFlux t

theorem continuous_thetaCuspCompletedProductFiberHigherTailRightDecayFlux :
    Continuous thetaCuspCompletedProductFiberHigherTailRightDecayFlux :=
  continuous_thetaCuspReflectedSourceDecayFlux_zero.sub
    continuous_thetaCuspCompletedProductFiberFirstRightDecayFlux

theorem thetaCuspCompletedProductFiberHigherTailDecayFlux_zero_eq_right
    {t : ℝ} (ht : 0 < t) :
    thetaCuspCompletedProductFiberHigherTailDecayFlux 0 t =
      thetaCuspCompletedProductFiberHigherTailRightDecayFlux t := by
  rw [thetaCuspCompletedProductFiberHigherTailDecayFlux_zero_eq_residual ht,
    thetaCuspCompletedProductFiberFirstDecayFlux_zero_eq_right ht]
  rfl

theorem intervalIntegral_thetaCuspCompletedProductFiberHigherTailRightDecayFlux_eq_drop
    {t : ℝ} (ht : 0 < t) :
    (∫ s in 0..t, thetaCuspCompletedProductFiberHigherTailRightDecayFlux s) =
      thetaCuspCompletedProductFiberHigherTailDrop 0 t := by
  have hsource : IntervalIntegrable (thetaCuspReflectedSourceDecayFlux 0)
      volume 0 t :=
    continuous_thetaCuspReflectedSourceDecayFlux_zero.intervalIntegrable 0 t
  have hfirst : IntervalIntegrable thetaCuspCompletedProductFiberFirstRightDecayFlux
      volume 0 t :=
    continuous_thetaCuspCompletedProductFiberFirstRightDecayFlux.intervalIntegrable 0 t
  unfold thetaCuspCompletedProductFiberHigherTailRightDecayFlux
  rw [intervalIntegral.integral_sub hsource hfirst,
    intervalIntegral_thetaCuspReflectedSourceDecayFlux_zero_eq_drop ht,
    intervalIntegral_thetaCuspCompletedProductFiberFirstRightDecayFlux_eq_drop ht]
  have hsplit :=
    thetaCuspReflectedSourceFirstDrop_eq_firstFiber_add_higherTail 0 t
  linarith

/-- Chord reserve left after likelihood curvature and pure slope square are removed. -/
def thetaCuspCompletedProductFiberCofinalLikelihoodDriftReserveAtZero
    (t : ℝ) : ℝ :=
  let A := thetaCuspReflectedSourceFirstDrop 0 t
  let d := thetaCuspCompletedProductFiberFirstDecayFlux 0 t
  let j := thetaCuspCompletedProductFiberFirstDecayFluxCurvature 0 t
  let F := thetaCuspCompletedProductFiberAmplitude 1 0 t
  let L := thetaCuspCompletedProductFiberCofinalLikelihoodFactor t
  let L₁ := thetaCuspCompletedProductFiberCofinalLikelihoodFactorJetOne t
  let D := d * (1 + L) - F * L₁
  24 * A ^ 2 - 9 * t * A * D + t ^ 2 *
    (5 * A * j * (1 + L) - 4 * d ^ 2 * (1 + L) ^ 2 +
      d * L₁ * (10 * A + 8 * F * (1 + L)))

/-- Positive likelihood tax density which the nonlocal chord reserve must dominate. -/
def thetaCuspCompletedProductFiberCofinalLikelihoodTaxDensityAtZero
    (t : ℝ) : ℝ :=
  let A := thetaCuspReflectedSourceFirstDrop 0 t
  let F := thetaCuspCompletedProductFiberAmplitude 1 0 t
  let L₁ := thetaCuspCompletedProductFiberCofinalLikelihoodFactorJetOne t
  let L₂ := thetaCuspCompletedProductFiberCofinalLikelihoodFactorJetTwo t
  4 * t ^ 2 * F ^ 2 * L₁ ^ 2 + 5 * t ^ 2 * A * F * L₂

/-- Same reserve with its sole endpoint drop replaced by accumulated source flux. -/
def thetaCuspCompletedProductFiberCofinalLikelihoodIntegralDriftReserveAtZero
    (t : ℝ) : ℝ :=
  let A := ∫ s in 0..t, thetaCuspReflectedSourceDecayFlux 0 s
  let d := thetaCuspCompletedProductFiberFirstDecayFlux 0 t
  let j := thetaCuspCompletedProductFiberFirstDecayFluxCurvature 0 t
  let F := thetaCuspCompletedProductFiberAmplitude 1 0 t
  let L := thetaCuspCompletedProductFiberCofinalLikelihoodFactor t
  let L₁ := thetaCuspCompletedProductFiberCofinalLikelihoodFactorJetOne t
  let D := d * (1 + L) - F * L₁
  24 * A ^ 2 - 9 * t * A * D + t ^ 2 *
    (5 * A * j * (1 + L) - 4 * d ^ 2 * (1 + L) ^ 2 +
      d * L₁ * (10 * A + 8 * F * (1 + L)))

theorem thetaCuspCompletedProductFiberCofinalLikelihoodDriftReserve_eq_integral
    {t : ℝ} (ht : 0 < t) :
    thetaCuspCompletedProductFiberCofinalLikelihoodDriftReserveAtZero t =
      thetaCuspCompletedProductFiberCofinalLikelihoodIntegralDriftReserveAtZero t := by
  unfold thetaCuspCompletedProductFiberCofinalLikelihoodDriftReserveAtZero
    thetaCuspCompletedProductFiberCofinalLikelihoodIntegralDriftReserveAtZero
  rw [intervalIntegral_thetaCuspReflectedSourceDecayFlux_zero_eq_drop ht]

theorem thetaCuspCompletedProductFiberCofinalLikelihoodDriftBudget_eq_drops_mul_reserve
    (t : ℝ) :
    thetaCuspCompletedProductFiberCofinalLikelihoodDriftAbsorptionBudgetAtZero t =
      thetaCuspCompletedProductFiberFirstDrop 0 t *
        thetaCuspCompletedProductFiberHigherTailDrop 0 t *
          thetaCuspCompletedProductFiberCofinalLikelihoodDriftReserveAtZero t := by
  unfold thetaCuspCompletedProductFiberCofinalLikelihoodDriftAbsorptionBudgetAtZero
    thetaCuspCompletedProductFiberHigherTailLikelihoodDriftFifthRootCurvatureNumeratorAtZero
    thetaCuspCompletedProductFiberCofinalLikelihoodDriftReserveAtZero
    HilbertMetric.fifthRootCurvatureJetForm
  rw [thetaCuspReflectedSourceFirstDrop_eq_firstFiber_add_higherTail]
  ring

theorem thetaCuspCompletedProductFiberCofinalLikelihoodTaxes_eq_neg_drops_mul_density
    (t : ℝ) :
    thetaCuspCompletedProductFiberCofinalLikelihoodSlopeSquareTaxAtZero t +
        thetaCuspCompletedProductFiberCofinalLikelihoodConvexityTaxAtZero t =
      -(thetaCuspCompletedProductFiberFirstDrop 0 t *
          thetaCuspCompletedProductFiberHigherTailDrop 0 t) *
        thetaCuspCompletedProductFiberCofinalLikelihoodTaxDensityAtZero t := by
  unfold thetaCuspCompletedProductFiberCofinalLikelihoodSlopeSquareTaxAtZero
    thetaCuspCompletedProductFiberCofinalLikelihoodConvexityTaxAtZero
    thetaCuspCompletedProductFiberCofinalLikelihoodTaxDensityAtZero
  ring

theorem thetaCuspCompletedProductFiberCofinalFunctionalBudget_eq_drops_mul_reserve_sub_tax
    {t : ℝ} (ht : 0 < t) :
    thetaCuspCompletedProductFiberCofinalFunctionalAbsorptionBudgetAtZero t =
      thetaCuspCompletedProductFiberFirstDrop 0 t *
        thetaCuspCompletedProductFiberHigherTailDrop 0 t *
          (thetaCuspCompletedProductFiberCofinalLikelihoodDriftReserveAtZero t -
            thetaCuspCompletedProductFiberCofinalLikelihoodTaxDensityAtZero t) := by
  rw [thetaCuspCompletedProductFiberCofinalFunctionalBudget_eq_drift_add_twoTaxes ht,
    thetaCuspCompletedProductFiberCofinalLikelihoodDriftBudget_eq_drops_mul_reserve,
    thetaCuspCompletedProductFiberCofinalLikelihoodTaxes_eq_neg_drops_mul_density]
  ring

/-- Exact all-positive-radius source identity: C5 equals nonlocal chord reserve minus the two
likelihood tax densities.  No first-fibre-rise hypothesis remains. -/
theorem thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_eq_reserve_sub_taxDensity
    {t : ℝ} (ht : 0 < t) :
    thetaCuspReflectedSourceFifthRootCurvatureNumerator 0 t =
      thetaCuspCompletedProductFiberCofinalLikelihoodDriftReserveAtZero t -
        thetaCuspCompletedProductFiberCofinalLikelihoodTaxDensityAtZero t := by
  rw [thetaCuspReflectedSourceFifthRootCurvatureNumerator_eq_jetForm,
    thetaCuspReflectedSourceDecayFlux_zero_eq_likelihoodProduct ht,
    thetaCuspReflectedSourceDecayFluxCurvature_zero_eq_likelihoodProduct ht]
  unfold thetaCuspCompletedProductFiberCofinalLikelihoodDriftReserveAtZero
    thetaCuspCompletedProductFiberCofinalLikelihoodTaxDensityAtZero
    HilbertMetric.fifthRootCurvatureJetForm
  ring

theorem thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_eq_integralReserve_sub_taxDensity
    {t : ℝ} (ht : 0 < t) :
    thetaCuspReflectedSourceFifthRootCurvatureNumerator 0 t =
      thetaCuspCompletedProductFiberCofinalLikelihoodIntegralDriftReserveAtZero t -
        thetaCuspCompletedProductFiberCofinalLikelihoodTaxDensityAtZero t := by
  rw [← thetaCuspCompletedProductFiberCofinalLikelihoodDriftReserve_eq_integral ht]
  exact
    thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_eq_reserve_sub_taxDensity ht

theorem thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_nonneg_iff_taxDensity_le_integralReserve
    {t : ℝ} (ht : 0 < t) :
    0 ≤ thetaCuspReflectedSourceFifthRootCurvatureNumerator 0 t ↔
      thetaCuspCompletedProductFiberCofinalLikelihoodTaxDensityAtZero t ≤
        thetaCuspCompletedProductFiberCofinalLikelihoodIntegralDriftReserveAtZero t := by
  rw [thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_eq_integralReserve_sub_taxDensity ht]
  exact sub_nonneg

theorem thetaCuspCompletedProductFiberCofinalLikelihoodTaxDensityAtZero_pos
    {t : ℝ} (ht : 0 < t) :
    0 < thetaCuspCompletedProductFiberCofinalLikelihoodTaxDensityAtZero t := by
  have hA := thetaCuspReflectedSourceFirstDrop_pos 0 ht
  have hF : 0 < thetaCuspCompletedProductFiberAmplitude 1 0 t := by
    rw [thetaCuspCompletedProductFiberAmplitude_one_zero, abs_of_pos ht]
    exact sq_pos_of_pos (thetaCuspSourceTerm_one_pos_of_pos ht)
  have hLone := thetaCuspCompletedProductFiberCofinalLikelihoodFactorJetOne_neg ht
  have hLtwo := thetaCuspCompletedProductFiberCofinalLikelihoodFactorJetTwo_pos ht
  unfold thetaCuspCompletedProductFiberCofinalLikelihoodTaxDensityAtZero
  have hslope : 0 <
      4 * t ^ 2 * thetaCuspCompletedProductFiberAmplitude 1 0 t ^ 2 *
        thetaCuspCompletedProductFiberCofinalLikelihoodFactorJetOne t ^ 2 := by
    positivity
  have hconv : 0 <
      5 * t ^ 2 * thetaCuspReflectedSourceFirstDrop 0 t *
        thetaCuspCompletedProductFiberAmplitude 1 0 t *
          thetaCuspCompletedProductFiberCofinalLikelihoodFactorJetTwo t := by
    positivity
  linarith

theorem thetaCuspCompletedProductFiberCofinalFunctionalBudget_nonpos_iff_taxDensity_le_reserve
    {t : ℝ} (ht : 0 < t)
    (hrise :
      thetaCuspCompletedProductFiberAmplitude 1 0 0 <
        thetaCuspCompletedProductFiberAmplitude 1 0 t) :
    thetaCuspCompletedProductFiberCofinalFunctionalAbsorptionBudgetAtZero t ≤ 0 ↔
      thetaCuspCompletedProductFiberCofinalLikelihoodTaxDensityAtZero t ≤
        thetaCuspCompletedProductFiberCofinalLikelihoodDriftReserveAtZero t := by
  have ha : thetaCuspCompletedProductFiberFirstDrop 0 t < 0 := by
    unfold thetaCuspCompletedProductFiberFirstDrop
    linarith
  have hsource := thetaCuspReflectedSourceFirstDrop_pos 0 ht
  have hsplit := thetaCuspReflectedSourceFirstDrop_eq_firstFiber_add_higherTail 0 t
  have hb : 0 < thetaCuspCompletedProductFiberHigherTailDrop 0 t := by
    linarith
  have hab :
      thetaCuspCompletedProductFiberFirstDrop 0 t *
          thetaCuspCompletedProductFiberHigherTailDrop 0 t < 0 :=
    mul_neg_of_neg_of_pos ha hb
  rw [thetaCuspCompletedProductFiberCofinalFunctionalBudget_eq_drops_mul_reserve_sub_tax ht]
  constructor
  · intro h
    by_contra hle
    have hsub :
        0 < thetaCuspCompletedProductFiberCofinalLikelihoodDriftReserveAtZero t -
          thetaCuspCompletedProductFiberCofinalLikelihoodTaxDensityAtZero t :=
      sub_pos.mpr (lt_of_not_ge hle)
    exact (not_lt_of_ge h) (mul_neg_of_neg_of_pos hab hsub)
  · intro h
    exact mul_nonpos_of_nonpos_of_nonneg hab.le (sub_nonneg.mpr h)

theorem thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_nonneg_iff_taxDensity_le_reserve
    {t : ℝ} (ht : 0 < t)
    (hrise :
      thetaCuspCompletedProductFiberAmplitude 1 0 0 <
        thetaCuspCompletedProductFiberAmplitude 1 0 t) :
    0 ≤ thetaCuspReflectedSourceFifthRootCurvatureNumerator 0 t ↔
      thetaCuspCompletedProductFiberCofinalLikelihoodTaxDensityAtZero t ≤
        thetaCuspCompletedProductFiberCofinalLikelihoodDriftReserveAtZero t := by
  rw [thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_nonneg_iff_cofinalFunctionalBudget_nonpos
      ht hrise]
  exact
    thetaCuspCompletedProductFiberCofinalFunctionalBudget_nonpos_iff_taxDensity_le_reserve
      ht hrise

end

end RHTower
