import GaloisForLFunctions.RHTower.CriticalPrimeFockSchattenExponent
import GaloisForLFunctions.RHTower.XiDeterminantSchattenAbscissa

/-!
# Critical-prime polynomial-Fock exclusion for an exact Xi determinant

This module separates the source-side analytic input from the determinant-side obstruction.  A
critical-prime polynomial-Fock incidence law identifies Schatten membership with integrability of
its adapted-tube density.  The exact integral calculation then gives abscissa `m / (m - 4) > 1`,
whereas every exact self-adjoint Xi determinant has abscissa one.  Abscissa uniqueness rules out
their being the same operator.
-/

open Complex Set Filter MeasureTheory
open HilbertSchmidt

namespace RHTower

noncomputable section

/-- Analytic interface supplied by the doubling-Fock Toeplitz theorem and the critical-prime
adapted-tube comparison. -/
def HasCriticalPrimeFockSchattenLaw {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : H →L[ℂ] H) (m : ℝ) : Prop :=
  ∀ {q : ℝ}, 0 < q →
    (MemSchattenClass q T ↔
      IntegrableOn
        (fun x : ℝ => x ^ criticalPrimeFockSchattenDensityExponent m q)
        (Ioi 1))

/-- The critical-prime polynomial-Fock density law has exact abscissa `m / (m - 4)`. -/
theorem HasCriticalPrimeFockSchattenLaw.hasExactSchattenAbscissa
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {T : H →L[ℂ] H} {m : ℝ}
    (hT : HasCriticalPrimeFockSchattenLaw T m) (hm : 4 < m) :
    HasExactSchattenAbscissa T (criticalPrimeFockSchattenThreshold m) := by
  intro q hq
  rw [hT hq, integrableOn_criticalPrimeFockSchattenDensity_iff hm]

/-- No finite superquartic critical-prime polynomial-Fock incidence operator can simultaneously
be an exact self-adjoint Hilbert--Carleman determinant carrier for `XiC`. -/
theorem exactXiDeterminant_not_hasCriticalPrimeFockSchattenLaw
    {ι : Type*} [DecidableEq ι]
    {K : ι × ι → ℂ} (hK : IsHS K)
    (hself : IsSelfAdjoint (toOperator hK))
    (H : ℂ → ℂ) (hHanalytic : Differentiable ℂ H)
    (hH : ∀ z, H z ≠ 0)
    (hXi : ∀ z, XiC z = H z *
      GaloisForLFunctions.HTGeometry.entireDet2 K z)
    {m : ℝ} (hm : 4 < m) :
    ¬ HasCriticalPrimeFockSchattenLaw (toOperator hK) m := by
  intro hFock
  exact exactXiDeterminant_not_hasExactSchattenAbscissa
    hK hself H hHanalytic hH hXi
    (criticalPrimeFockSchattenThreshold_gt_one hm)
    (hFock.hasExactSchattenAbscissa hm)

end

end RHTower
