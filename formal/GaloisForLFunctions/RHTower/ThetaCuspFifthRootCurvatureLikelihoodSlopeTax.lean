import GaloisForLFunctions.RHTower.ThetaCuspFifthRootCurvatureLikelihoodTax

/-!
# Likelihood slope-square tax in theta fifth-root curvature

The complete higher/first likelihood ratio has strictly positive second jet
and is antitone. Hence its first jet is strictly negative: a zero first jet
would become positive immediately to its right. The cofinal factor inherits
this strict decrease.

Expanding the likelihood-base C5 budget in this first jet exposes a second
strictly positive tax, proportional to its square. The remaining drift budget
must pay both this slope-square tax and the likelihood-convexity tax.
-/

namespace RHTower

noncomputable section

open Set

/-- Antitonicity plus a strictly positive second jet forces the complete
higher-likelihood first jet to be strictly negative. -/
theorem thetaCuspHigherLikelihoodJetOne_neg
    {t : ℝ} (ht : 0 < t) :
    thetaCuspHigherLikelihoodJetOne t < 0 := by
  have hcont :
      ContinuousOn thetaCuspHigherLikelihoodJetOne (Ici t) := by
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le ht hx
    exact
      (hasDerivAt_thetaCuspHigherLikelihoodJetOne hxpos).continuousAt.continuousWithinAt
  have hstrict :
      StrictMonoOn thetaCuspHigherLikelihoodJetOne (Ici t) := by
    apply strictMonoOn_of_deriv_pos (D := Ici t) (convex_Ici t) hcont
    intro x hx
    have htx : t < x := by
      simpa only [interior_Ici, mem_Ioi] using hx
    have hxpos : 0 < x := lt_trans ht htx
    rw [(hasDerivAt_thetaCuspHigherLikelihoodJetOne hxpos).deriv]
    exact thetaCuspHigherLikelihoodJetTwo_pos hxpos
  have hinc :
      thetaCuspHigherLikelihoodJetOne t <
        thetaCuspHigherLikelihoodJetOne (t + 1) := by
    exact hstrict (by simp) (by simp) (by linarith)
  have hspos : 0 < t + 1 := by linarith
  have hR := hasDerivAt_thetaCuspHigherToFirstAtomLikelihoodRatio hspos
  have hnonpos : thetaCuspHigherLikelihoodJetOne (t + 1) ≤ 0 := by
    exact hR.hasDerivWithinAt.nonpos_of_antitoneOn
      (isOpen_Ioi.preperfect (t + 1) hspos)
      thetaCuspHigherToFirstAtomLikelihoodRatio_antitoneOn
  linarith

/-- The cofinal likelihood factor is strictly decreasing on the positive
half-line. -/
theorem thetaCuspCompletedProductFiberCofinalLikelihoodFactorJetOne_neg
    {t : ℝ} (ht : 0 < t) :
    thetaCuspCompletedProductFiberCofinalLikelihoodFactorJetOne t < 0 := by
  have hR := thetaCuspHigherToFirstAtomLikelihoodRatio_nonneg ht
  have hRone := thetaCuspHigherLikelihoodJetOne_neg ht
  unfold thetaCuspCompletedProductFiberCofinalLikelihoodFactorJetOne
  exact mul_neg_of_pos_of_neg (by positivity) hRone

/-- Tail curvature after expanding away the likelihood-slope square while
retaining every term linear in the likelihood slope. -/
def thetaCuspCompletedProductFiberHigherTailLikelihoodDriftFifthRootCurvatureNumeratorAtZero
    (t : ℝ) : ℝ :=
  let b := thetaCuspCompletedProductFiberHigherTailDrop 0 t
  let d := thetaCuspCompletedProductFiberFirstDecayFlux 0 t
  let j := thetaCuspCompletedProductFiberFirstDecayFluxCurvature 0 t
  let F := thetaCuspCompletedProductFiberAmplitude 1 0 t
  let L := thetaCuspCompletedProductFiberCofinalLikelihoodFactor t
  let L₁ := thetaCuspCompletedProductFiberCofinalLikelihoodFactorJetOne t
  24 * b ^ (2 : ℕ) - 9 * t * b * (d * L - F * L₁) +
    t ^ (2 : ℕ) * (5 * b * (j * L + 2 * d * L₁) -
      4 * d ^ (2 : ℕ) * L ^ (2 : ℕ) + 8 * d * L * F * L₁)

/-- Cofinal drift budget after both pure likelihood-curvature and
likelihood-slope-square terms are removed. -/
def thetaCuspCompletedProductFiberCofinalLikelihoodDriftAbsorptionBudgetAtZero
    (t : ℝ) : ℝ :=
  let a := thetaCuspCompletedProductFiberFirstDrop 0 t
  let b := thetaCuspCompletedProductFiberHigherTailDrop 0 t
  let A := thetaCuspReflectedSourceFirstDrop 0 t
  let d := thetaCuspCompletedProductFiberFirstDecayFlux 0 t
  let j := thetaCuspCompletedProductFiberFirstDecayFluxCurvature 0 t
  let F := thetaCuspCompletedProductFiberAmplitude 1 0 t
  let L := thetaCuspCompletedProductFiberCofinalLikelihoodFactor t
  let L₁ := thetaCuspCompletedProductFiberCofinalLikelihoodFactorJetOne t
  let M₀ := d * (a * L - b)
  b * A * HilbertMetric.fifthRootCurvatureJetForm t a d j +
    a * A *
      thetaCuspCompletedProductFiberHigherTailLikelihoodDriftFifthRootCurvatureNumeratorAtZero
        t +
    4 * t ^ (2 : ℕ) * (M₀ ^ (2 : ℕ) - 2 * a * F * M₀ * L₁)

/-- Pure likelihood-slope-square contribution to the cofinal budget. -/
def thetaCuspCompletedProductFiberCofinalLikelihoodSlopeSquareTaxAtZero
    (t : ℝ) : ℝ :=
  -4 * t ^ (2 : ℕ) *
    thetaCuspCompletedProductFiberFirstDrop 0 t *
    thetaCuspCompletedProductFiberHigherTailDrop 0 t *
    thetaCuspCompletedProductFiberAmplitude 1 0 t ^ (2 : ℕ) *
    thetaCuspCompletedProductFiberCofinalLikelihoodFactorJetOne t ^ (2 : ℕ)

/-- Exact split of likelihood-base budget into drift plus slope-square tax. -/
theorem thetaCuspCompletedProductFiberCofinalLikelihoodBaseBudget_eq_drift_add_slopeSquareTax
    (t : ℝ) :
    thetaCuspCompletedProductFiberCofinalLikelihoodBaseAbsorptionBudgetAtZero t =
      thetaCuspCompletedProductFiberCofinalLikelihoodDriftAbsorptionBudgetAtZero t +
        thetaCuspCompletedProductFiberCofinalLikelihoodSlopeSquareTaxAtZero t := by
  unfold thetaCuspCompletedProductFiberCofinalLikelihoodBaseAbsorptionBudgetAtZero
    thetaCuspCompletedProductFiberHigherTailLikelihoodBaseFifthRootCurvatureNumeratorAtZero
    thetaCuspCompletedProductFiberCofinalLikelihoodDriftAbsorptionBudgetAtZero
    thetaCuspCompletedProductFiberHigherTailLikelihoodDriftFifthRootCurvatureNumeratorAtZero
    thetaCuspCompletedProductFiberCofinalLikelihoodSlopeSquareTaxAtZero
    HilbertMetric.fifthRootCurvatureJetForm
  rw [thetaCuspReflectedSourceFirstDrop_eq_firstFiber_add_higherTail]
  ring

/-- In a first-fibre-rise chamber, slope-square tax is strictly positive. -/
theorem thetaCuspCompletedProductFiberCofinalLikelihoodSlopeSquareTaxAtZero_pos
    {t : ℝ} (ht : 0 < t)
    (hrise :
      thetaCuspCompletedProductFiberAmplitude 1 0 0 <
        thetaCuspCompletedProductFiberAmplitude 1 0 t) :
    0 <
      thetaCuspCompletedProductFiberCofinalLikelihoodSlopeSquareTaxAtZero t := by
  have ha : thetaCuspCompletedProductFiberFirstDrop 0 t < 0 := by
    unfold thetaCuspCompletedProductFiberFirstDrop
    linarith
  have hsource := thetaCuspReflectedSourceFirstDrop_pos 0 ht
  have hsplit :=
    thetaCuspReflectedSourceFirstDrop_eq_firstFiber_add_higherTail 0 t
  have hb : 0 < thetaCuspCompletedProductFiberHigherTailDrop 0 t := by
    linarith
  have hF : 0 < thetaCuspCompletedProductFiberAmplitude 1 0 t := by
    rw [thetaCuspCompletedProductFiberAmplitude_one_zero, abs_of_pos ht]
    rw [thetaCuspSourceTerm_one_eq_exp_firstAtomLogDensity ht.le]
    positivity
  have hLone :=
    thetaCuspCompletedProductFiberCofinalLikelihoodFactorJetOne_neg ht
  have hLsq :
      0 < thetaCuspCompletedProductFiberCofinalLikelihoodFactorJetOne t ^ (2 : ℕ) :=
    sq_pos_of_neg hLone
  have hminus : 0 < -thetaCuspCompletedProductFiberFirstDrop 0 t :=
    neg_pos.mpr ha
  unfold thetaCuspCompletedProductFiberCofinalLikelihoodSlopeSquareTaxAtZero
  rw [show
    -4 * t ^ (2 : ℕ) * thetaCuspCompletedProductFiberFirstDrop 0 t *
          thetaCuspCompletedProductFiberHigherTailDrop 0 t *
          thetaCuspCompletedProductFiberAmplitude 1 0 t ^ (2 : ℕ) *
          thetaCuspCompletedProductFiberCofinalLikelihoodFactorJetOne t ^ (2 : ℕ) =
      4 * t ^ (2 : ℕ) * (-thetaCuspCompletedProductFiberFirstDrop 0 t) *
          thetaCuspCompletedProductFiberHigherTailDrop 0 t *
          thetaCuspCompletedProductFiberAmplitude 1 0 t ^ (2 : ℕ) *
          thetaCuspCompletedProductFiberCofinalLikelihoodFactorJetOne t ^ (2 : ℕ) by ring]
  positivity

/-- Functional budget is drift plus two exact likelihood taxes. -/
theorem thetaCuspCompletedProductFiberCofinalFunctionalBudget_eq_drift_add_twoTaxes
    {t : ℝ} (ht : 0 < t) :
    thetaCuspCompletedProductFiberCofinalFunctionalAbsorptionBudgetAtZero t =
      thetaCuspCompletedProductFiberCofinalLikelihoodDriftAbsorptionBudgetAtZero t +
        thetaCuspCompletedProductFiberCofinalLikelihoodSlopeSquareTaxAtZero t +
        thetaCuspCompletedProductFiberCofinalLikelihoodConvexityTaxAtZero t := by
  rw [
    thetaCuspCompletedProductFiberCofinalFunctionalAbsorptionBudget_eq_likelihoodBudget
      ht,
    thetaCuspCompletedProductFiberCofinalLikelihoodAbsorptionBudget_eq_base_add_convexityTax,
    thetaCuspCompletedProductFiberCofinalLikelihoodBaseBudget_eq_drift_add_slopeSquareTax]

/-- Sharp surviving core: drift must pay both strictly positive taxes. -/
theorem
    thetaCuspCompletedProductFiberCofinalFunctionalBudget_nonpos_iff_drift_le_neg_twoTaxes
    {t : ℝ} (ht : 0 < t) :
    thetaCuspCompletedProductFiberCofinalFunctionalAbsorptionBudgetAtZero t ≤ 0 ↔
      thetaCuspCompletedProductFiberCofinalLikelihoodDriftAbsorptionBudgetAtZero t ≤
        -(thetaCuspCompletedProductFiberCofinalLikelihoodSlopeSquareTaxAtZero t +
          thetaCuspCompletedProductFiberCofinalLikelihoodConvexityTaxAtZero t) := by
  rw [thetaCuspCompletedProductFiberCofinalFunctionalBudget_eq_drift_add_twoTaxes ht]
  constructor <;> intro h <;> linarith

end

end RHTower
