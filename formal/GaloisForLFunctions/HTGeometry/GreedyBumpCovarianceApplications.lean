import GaloisForLFunctions.HTGeometry.BuresPositiveReporterIncidenceLaw

/-!
# Greedy-bump mismatch bias as a positive-reporter covariance energy

This file applies the paper's mismatch trace law to the corpus's finite complex
source-covariance construction.  Integrability and Hessian positivity are
carried by data, so every result is closed and unconditional.
-/

open MeasureTheory Matrix
open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Finite score field with an invertible positive Hessian and integrable covariance. -/
structure GreedyBumpCovarianceModel (X : Type*) [MeasurableSpace X] (D : ℕ) where
  measure : Measure X
  score : X → Fin D → ℂ
  hessian : Matrix (Fin D) (Fin D) ℂ
  hessianPosDef : hessian.PosDef
  pairIntegrable : ∀ i j, Integrable
    (fun x ↦ score x i * star (score x j)) measure

/-- Score covariance `Λ` of a finite mismatch model. -/
def GreedyBumpCovarianceModel.covariance
    {X : Type*} [MeasurableSpace X] {D : ℕ}
    (M : GreedyBumpCovarianceModel X D) : Matrix (Fin D) (Fin D) ℂ :=
  finitePositiveReporterSourceCovariance M.measure M.score

/-- Paper's mismatch penalty `1/2 Re tr(Λ H⁻¹)`. -/
def GreedyBumpCovarianceModel.traceBias
    {X : Type*} [MeasurableSpace X] {D : ℕ}
    (M : GreedyBumpCovarianceModel X D) : ℝ :=
  (1 / 2 : ℝ) * ((M.covariance * M.hessian⁻¹).trace).re

/-- Same mismatch penalty as integrated inverse-Hessian score energy. -/
def GreedyBumpCovarianceModel.integratedBias
    {X : Type*} [MeasurableSpace X] {D : ℕ}
    (M : GreedyBumpCovarianceModel X D) : ℝ :=
  (1 / 2 : ℝ) *
    ∫ x, finitePositiveReporterSourceEnergy M.hessian⁻¹ (M.score x) ∂M.measure

/-- Exact covariance-energy realization of the paper's mismatch trace formula. -/
theorem greedyBump_traceBias_eq_integratedBias
    {X : Type*} [MeasurableSpace X] {D : ℕ}
    (M : GreedyBumpCovarianceModel X D) :
    M.traceBias = M.integratedBias := by
  unfold GreedyBumpCovarianceModel.traceBias
    GreedyBumpCovarianceModel.integratedBias
    GreedyBumpCovarianceModel.covariance
  rw [finitePositiveReporter_re_trace_covariance_mul_eq_integral
    M.measure M.score M.hessian⁻¹ M.pairIntegrable]

/-- Every pointwise contribution to mismatch bias is nonnegative. -/
theorem greedyBump_inverseHessian_scoreEnergy_nonneg
    {X : Type*} [MeasurableSpace X] {D : ℕ}
    (M : GreedyBumpCovarianceModel X D) (x : X) :
    0 ≤ finitePositiveReporterSourceEnergy M.hessian⁻¹ (M.score x) := by
  exact finitePositiveReporterSourceEnergy_nonneg M.hessianPosDef.inv (M.score x)

/-- The integrated mismatch bias is nonnegative. -/
theorem greedyBump_integratedBias_nonneg
    {X : Type*} [MeasurableSpace X] {D : ℕ}
    (M : GreedyBumpCovarianceModel X D) :
    0 ≤ M.integratedBias := by
  unfold GreedyBumpCovarianceModel.integratedBias
  exact mul_nonneg (by norm_num) (integral_nonneg fun x ↦
    greedyBump_inverseHessian_scoreEnergy_nonneg M x)

/-- The covariance trace form of mismatch bias is therefore nonnegative. -/
theorem greedyBump_traceBias_nonneg
    {X : Type*} [MeasurableSpace X] {D : ℕ}
    (M : GreedyBumpCovarianceModel X D) :
    0 ≤ M.traceBias := by
  rw [greedyBump_traceBias_eq_integratedBias M]
  exact greedyBump_integratedBias_nonneg M

end

end GaloisForLFunctions.HTGeometry
