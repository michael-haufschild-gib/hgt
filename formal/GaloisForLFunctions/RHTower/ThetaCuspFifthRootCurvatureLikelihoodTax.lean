import GaloisForLFunctions.RHTower.ThetaCuspFifthRootCurvatureTotalVariance

/-!
# Likelihood convexity tax in theta fifth-root curvature

At modular center, the complete higher product-fibre tail is the first
product fibre times the cofinal likelihood factor L = R(2 + R). Its first
two literal jets therefore contain no independent cofinal data.

Substitution into the exact fifth-root total-variance budget exposes a sharp
obstruction: strictly positive likelihood curvature contributes a strictly
positive tax in every first-fibre-rise chamber. Consequently known likelihood
signs cannot prove the required nonpositive budget. Remaining base term must
instead supply a strictly negative reserve at least as large as this tax.
-/

namespace RHTower

noncomputable section

/-- Full reflected-source decay flux in first-fibre/likelihood coordinates. -/
theorem thetaCuspReflectedSourceDecayFlux_zero_eq_likelihoodProduct
    {t : ℝ} (ht : 0 < t) :
    thetaCuspReflectedSourceDecayFlux 0 t =
      thetaCuspCompletedProductFiberFirstDecayFlux 0 t *
          (1 + thetaCuspCompletedProductFiberCofinalLikelihoodFactor t) -
        thetaCuspCompletedProductFiberAmplitude 1 0 t *
          thetaCuspCompletedProductFiberCofinalLikelihoodFactorJetOne t := by
  have hres :=
    thetaCuspCompletedProductFiberHigherTailDecayFlux_zero_eq_residual ht
  rw [thetaCuspCompletedProductFiberHigherTailDecayFlux_zero_eq_product ht] at hres
  linarith

/-- Second full reflected-source jet in first-fibre/likelihood coordinates. -/
theorem thetaCuspReflectedSourceDecayFluxCurvature_zero_eq_likelihoodProduct
    {t : ℝ} (ht : 0 < t) :
    thetaCuspReflectedSourceDecayFluxCurvature 0 t =
      thetaCuspCompletedProductFiberFirstDecayFluxCurvature 0 t *
          (1 + thetaCuspCompletedProductFiberCofinalLikelihoodFactor t) +
        2 * thetaCuspCompletedProductFiberFirstDecayFlux 0 t *
          thetaCuspCompletedProductFiberCofinalLikelihoodFactorJetOne t -
        thetaCuspCompletedProductFiberAmplitude 1 0 t *
          thetaCuspCompletedProductFiberCofinalLikelihoodFactorJetTwo t := by
  have hres :=
    thetaCuspCompletedProductFiberHigherTailDecayFluxCurvature_zero_eq_residual ht
  rw [thetaCuspCompletedProductFiberHigherTailDecayFluxCurvature_zero_eq_product ht]
    at hres
  linarith

/-- Higher-tail curvature numerator with likelihood curvature removed. -/
def thetaCuspCompletedProductFiberHigherTailLikelihoodBaseFifthRootCurvatureNumeratorAtZero
    (t : ℝ) : ℝ :=
  HilbertMetric.fifthRootCurvatureJetForm t
    (thetaCuspCompletedProductFiberHigherTailDrop 0 t)
    (thetaCuspCompletedProductFiberFirstDecayFlux 0 t *
        thetaCuspCompletedProductFiberCofinalLikelihoodFactor t -
      thetaCuspCompletedProductFiberAmplitude 1 0 t *
        thetaCuspCompletedProductFiberCofinalLikelihoodFactorJetOne t)
    (thetaCuspCompletedProductFiberFirstDecayFluxCurvature 0 t *
        thetaCuspCompletedProductFiberCofinalLikelihoodFactor t +
      2 * thetaCuspCompletedProductFiberFirstDecayFlux 0 t *
        thetaCuspCompletedProductFiberCofinalLikelihoodFactorJetOne t)

/-- Higher-tail curvature numerator entirely in likelihood product jets. -/
def thetaCuspCompletedProductFiberHigherTailLikelihoodFifthRootCurvatureNumeratorAtZero
    (t : ℝ) : ℝ :=
  HilbertMetric.fifthRootCurvatureJetForm t
    (thetaCuspCompletedProductFiberHigherTailDrop 0 t)
    (thetaCuspCompletedProductFiberFirstDecayFlux 0 t *
        thetaCuspCompletedProductFiberCofinalLikelihoodFactor t -
      thetaCuspCompletedProductFiberAmplitude 1 0 t *
        thetaCuspCompletedProductFiberCofinalLikelihoodFactorJetOne t)
    (thetaCuspCompletedProductFiberFirstDecayFluxCurvature 0 t *
        thetaCuspCompletedProductFiberCofinalLikelihoodFactor t +
      2 * thetaCuspCompletedProductFiberFirstDecayFlux 0 t *
        thetaCuspCompletedProductFiberCofinalLikelihoodFactorJetOne t -
      thetaCuspCompletedProductFiberAmplitude 1 0 t *
        thetaCuspCompletedProductFiberCofinalLikelihoodFactorJetTwo t)

/-- Likelihood curvature subtracts its exact weighted term from tail curvature. -/
theorem
    thetaCuspCompletedProductFiberHigherTailLikelihoodFifthRootCurvature_eq_base_sub_convexity
    (t : ℝ) :
    thetaCuspCompletedProductFiberHigherTailLikelihoodFifthRootCurvatureNumeratorAtZero t =
      thetaCuspCompletedProductFiberHigherTailLikelihoodBaseFifthRootCurvatureNumeratorAtZero t -
        5 * t ^ 2 * thetaCuspCompletedProductFiberHigherTailDrop 0 t *
          thetaCuspCompletedProductFiberAmplitude 1 0 t *
          thetaCuspCompletedProductFiberCofinalLikelihoodFactorJetTwo t := by
  unfold
    thetaCuspCompletedProductFiberHigherTailLikelihoodFifthRootCurvatureNumeratorAtZero
    thetaCuspCompletedProductFiberHigherTailLikelihoodBaseFifthRootCurvatureNumeratorAtZero
    HilbertMetric.fifthRootCurvatureJetForm
  ring

/-- Cofinal budget after replacing all infinite-tail jets by product laws. -/
def thetaCuspCompletedProductFiberCofinalLikelihoodAbsorptionBudgetAtZero
    (t : ℝ) : ℝ :=
  thetaCuspCompletedProductFiberHigherTailDrop 0 t *
      thetaCuspReflectedSourceFirstDrop 0 t *
      HilbertMetric.fifthRootCurvatureJetForm t
        (thetaCuspCompletedProductFiberFirstDrop 0 t)
        (thetaCuspCompletedProductFiberFirstDecayFlux 0 t)
        (thetaCuspCompletedProductFiberFirstDecayFluxCurvature 0 t) +
    thetaCuspCompletedProductFiberFirstDrop 0 t *
      thetaCuspReflectedSourceFirstDrop 0 t *
      thetaCuspCompletedProductFiberHigherTailLikelihoodFifthRootCurvatureNumeratorAtZero t +
    4 * t ^ 2 *
      (thetaCuspCompletedProductFiberFirstDrop 0 t *
          (thetaCuspCompletedProductFiberFirstDecayFlux 0 t *
              (1 + thetaCuspCompletedProductFiberCofinalLikelihoodFactor t) -
            thetaCuspCompletedProductFiberAmplitude 1 0 t *
              thetaCuspCompletedProductFiberCofinalLikelihoodFactorJetOne t) -
        thetaCuspReflectedSourceFirstDrop 0 t *
          thetaCuspCompletedProductFiberFirstDecayFlux 0 t) ^ 2

/-- Base absorption budget with adverse likelihood curvature removed. -/
def thetaCuspCompletedProductFiberCofinalLikelihoodBaseAbsorptionBudgetAtZero
    (t : ℝ) : ℝ :=
  thetaCuspCompletedProductFiberHigherTailDrop 0 t *
      thetaCuspReflectedSourceFirstDrop 0 t *
      HilbertMetric.fifthRootCurvatureJetForm t
        (thetaCuspCompletedProductFiberFirstDrop 0 t)
        (thetaCuspCompletedProductFiberFirstDecayFlux 0 t)
        (thetaCuspCompletedProductFiberFirstDecayFluxCurvature 0 t) +
    thetaCuspCompletedProductFiberFirstDrop 0 t *
      thetaCuspReflectedSourceFirstDrop 0 t *
      thetaCuspCompletedProductFiberHigherTailLikelihoodBaseFifthRootCurvatureNumeratorAtZero t +
    4 * t ^ 2 *
      (thetaCuspCompletedProductFiberFirstDrop 0 t *
          (thetaCuspCompletedProductFiberFirstDecayFlux 0 t *
              (1 + thetaCuspCompletedProductFiberCofinalLikelihoodFactor t) -
            thetaCuspCompletedProductFiberAmplitude 1 0 t *
              thetaCuspCompletedProductFiberCofinalLikelihoodFactorJetOne t) -
        thetaCuspReflectedSourceFirstDrop 0 t *
          thetaCuspCompletedProductFiberFirstDecayFlux 0 t) ^ 2

/-- Likelihood-convexity contribution to cofinal absorption budget. -/
def thetaCuspCompletedProductFiberCofinalLikelihoodConvexityTaxAtZero
    (t : ℝ) : ℝ :=
  -5 * t ^ 2 *
    thetaCuspCompletedProductFiberFirstDrop 0 t *
    thetaCuspReflectedSourceFirstDrop 0 t *
    thetaCuspCompletedProductFiberHigherTailDrop 0 t *
    thetaCuspCompletedProductFiberAmplitude 1 0 t *
    thetaCuspCompletedProductFiberCofinalLikelihoodFactorJetTwo t

/-- Exact decomposition into base contribution plus likelihood-convexity tax. -/
theorem thetaCuspCompletedProductFiberCofinalLikelihoodAbsorptionBudget_eq_base_add_convexityTax
    (t : ℝ) :
    thetaCuspCompletedProductFiberCofinalLikelihoodAbsorptionBudgetAtZero t =
      thetaCuspCompletedProductFiberCofinalLikelihoodBaseAbsorptionBudgetAtZero t +
        thetaCuspCompletedProductFiberCofinalLikelihoodConvexityTaxAtZero t := by
  unfold thetaCuspCompletedProductFiberCofinalLikelihoodAbsorptionBudgetAtZero
    thetaCuspCompletedProductFiberCofinalLikelihoodBaseAbsorptionBudgetAtZero
    thetaCuspCompletedProductFiberCofinalLikelihoodConvexityTaxAtZero
  rw [
    thetaCuspCompletedProductFiberHigherTailLikelihoodFifthRootCurvature_eq_base_sub_convexity]
  ring

/-- Functional budget equals its first-fibre/likelihood-coordinate form. -/
theorem thetaCuspCompletedProductFiberCofinalFunctionalAbsorptionBudget_eq_likelihoodBudget
    {t : ℝ} (ht : 0 < t) :
    thetaCuspCompletedProductFiberCofinalFunctionalAbsorptionBudgetAtZero t =
      thetaCuspCompletedProductFiberCofinalLikelihoodAbsorptionBudgetAtZero t := by
  rw [←
    thetaCuspCompletedProductFiberCofinalCurvatureAbsorptionBudget_zero_eq_functional ht]
  unfold thetaCuspCompletedProductFiberCofinalCurvatureAbsorptionBudget
    thetaCuspCompletedProductFiberFirstFifthRootCurvatureNumerator
    thetaCuspCompletedProductFiberHigherTailResidualFifthRootCurvatureNumerator
    thetaCuspCompletedProductFiberCofinalLikelihoodAbsorptionBudgetAtZero
    thetaCuspCompletedProductFiberHigherTailLikelihoodFifthRootCurvatureNumeratorAtZero
  rw [thetaCuspReflectedSourceDecayFlux_zero_eq_likelihoodProduct ht,
    thetaCuspReflectedSourceDecayFluxCurvature_zero_eq_likelihoodProduct ht]
  ring

/-- In every first-fibre-rise chamber, convexity tax is strictly positive. -/
theorem thetaCuspCompletedProductFiberCofinalLikelihoodConvexityTaxAtZero_pos
    {t : ℝ} (ht : 0 < t)
    (hrise :
      thetaCuspCompletedProductFiberAmplitude 1 0 0 <
        thetaCuspCompletedProductFiberAmplitude 1 0 t) :
    0 < thetaCuspCompletedProductFiberCofinalLikelihoodConvexityTaxAtZero t := by
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
  have hLtwo :=
    thetaCuspCompletedProductFiberCofinalLikelihoodFactorJetTwo_pos ht
  have hminus : 0 < -thetaCuspCompletedProductFiberFirstDrop 0 t :=
    neg_pos.mpr ha
  unfold thetaCuspCompletedProductFiberCofinalLikelihoodConvexityTaxAtZero
  rw [show
    -5 * t ^ 2 * thetaCuspCompletedProductFiberFirstDrop 0 t *
          thetaCuspReflectedSourceFirstDrop 0 t *
          thetaCuspCompletedProductFiberHigherTailDrop 0 t *
          thetaCuspCompletedProductFiberAmplitude 1 0 t *
          thetaCuspCompletedProductFiberCofinalLikelihoodFactorJetTwo t =
      5 * t ^ 2 * (-thetaCuspCompletedProductFiberFirstDrop 0 t) *
          thetaCuspReflectedSourceFirstDrop 0 t *
          thetaCuspCompletedProductFiberHigherTailDrop 0 t *
          thetaCuspCompletedProductFiberAmplitude 1 0 t *
          thetaCuspCompletedProductFiberCofinalLikelihoodFactorJetTwo t by ring]
  positivity

/-- Sharp replacement: base must pay the positive convexity tax exactly. -/
theorem
    thetaCuspCompletedProductFiberCofinalFunctionalBudget_nonpos_iff_base_le_neg_convexityTax
    {t : ℝ} (ht : 0 < t) :
    thetaCuspCompletedProductFiberCofinalFunctionalAbsorptionBudgetAtZero t ≤ 0 ↔
      thetaCuspCompletedProductFiberCofinalLikelihoodBaseAbsorptionBudgetAtZero t ≤
        -thetaCuspCompletedProductFiberCofinalLikelihoodConvexityTaxAtZero t := by
  rw [
    thetaCuspCompletedProductFiberCofinalFunctionalAbsorptionBudget_eq_likelihoodBudget
      ht,
    thetaCuspCompletedProductFiberCofinalLikelihoodAbsorptionBudget_eq_base_add_convexityTax]
  constructor <;> intro h <;> linarith

end

end RHTower
