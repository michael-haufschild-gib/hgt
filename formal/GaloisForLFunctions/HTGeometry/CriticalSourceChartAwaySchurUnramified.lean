import GaloisForLFunctions.HTGeometry.CriticalSourceChartSchurPrime
import GaloisForLFunctions.HTGeometry.LocalizationAtPrimeDivisorDVR

/-!
# The explicit critical source chart is unramified away from the Schur divisor

At a distinct height-one base prime, an element of the Schur divisor becomes invertible.  Since its
image is divisible by the source ramification generator, that generator and hence the Jacobian
determinant become units.  The Jacobian annihilator theorem then proves formal unramifiedness.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 2000000

variable (K : Type*) [Field K] [CharZero K] [IsAlgClosed K] {m n : ℕ}
variable [Fact (0 < m)] [Fact (0 < n)] [Fact (1 < m)] [Fact (1 < n)]

/-- The source chart, localized over a height-one observation prime distinct from the Schur
divisor, is formally unramified over the localized observation chart. -/
theorem criticalSourceChart_baseLocalization_formallyUnramified_of_ne_schur
    (P : Ideal (criticalObservationChartRing K m n)) [P.IsPrime]
    (hPheight : P.height = 1)
    (hP : P ≠ criticalSchurChartUnder K (m := m) (n := n)) :
    Algebra.FormallyUnramified (Localization.AtPrime P)
      (Localization (Algebra.algebraMapSubmonoid (criticalSourceChartRing K m n)
        P.primeCompl)) := by
  let A := criticalObservationChartRing K m n
  let S := criticalSourceChartRing K m n
  let T := Localization (Algebra.algebraMapSubmonoid S P.primeCompl)
  have hnotle : ¬ (criticalSchurChartUnder K (m := m) (n := n) ≤ P) := by
    intro hle
    have heq := (criticalSchurChartUnder K (m := m) (n := n)).eq_of_le_of_height_le
      hle (by rw [hPheight, criticalSchurChartUnder_height K])
    exact hP heq.symm
  obtain ⟨a, haSchur, haP⟩ := Set.not_subset.mp hnotle
  have haSource : algebraMap A S a ∈
      criticalSourceChartSchurPrime K (m := m) (n := n) := by
    change a ∈ (criticalSourceChartSchurPrime K (m := m) (n := n)).under A
    rw [criticalSourceChartSchurPrime_under K]
    exact haSchur
  rw [criticalSourceChartSchurPrime_eq_span_ramification K,
    Ideal.mem_span_singleton] at haSource
  obtain ⟨b, hb⟩ := haSource
  have haUnit : IsUnit (algebraMap S T (algebraMap A S a)) := by
    have ham : algebraMap A S a ∈
        Algebra.algebraMapSubmonoid S P.primeCompl := by
      exact Algebra.mem_algebraMapSubmonoid_of_mem
        (S := S) (⟨a, haP⟩ : P.primeCompl)
    exact IsLocalization.map_units T ⟨algebraMap A S a, ham⟩
  rw [hb, map_mul, IsUnit.mul_iff] at haUnit
  have hramUnit : IsUnit (algebraMap S T
      (criticalSourceChartRamificationElement K (m := m) (n := n))) := haUnit.1
  have hdetUnit : IsUnit (algebraMap S T
      (criticalSourceChartJacobian K (m := m) (n := n)).det) := by
    rw [det_criticalSourceChartJacobian_eq_unit_mul_ramification K, map_mul]
    exact (isUnit_criticalSourceChartJacobianUnitFactor K).map
      (algebraMap S T) |>.mul hramUnit
  haveI : Algebra.FormallyUnramified A T := by
    apply formallyUnramified_localization_of_mem_annihilator_of_isUnit
      (Algebra.algebraMapSubmonoid S P.primeCompl)
      (criticalSourceChartJacobian K (m := m) (n := n)).det
      (det_criticalSourceChartJacobian_mem_annihilator K)
    exact hdetUnit
  exact Algebra.FormallyUnramified.localization_base P.primeCompl

end
end GaloisForLFunctions.HTGeometry
