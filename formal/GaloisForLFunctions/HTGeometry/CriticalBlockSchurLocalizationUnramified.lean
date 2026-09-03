import GaloisForLFunctions.HTGeometry.CriticalBlockSchurNormalizationUnramified
import GaloisForLFunctions.HTGeometry.IntegralClosureLocalizationEquiv
import GaloisForLFunctions.HTGeometry.CriticalSchurCoordinateIntegral

/-!
# Formal unramifiedness of the Schur localization of a block normalization

Localization commutes with integral closure.  Consequently, the localization of the global block
normalization at the Schur divisor is the Schur-DVR normalization in the block fixed field.  The
ramification calculation for that DVR therefore transfers to the global model.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 2000000

variable (K : Type*) [Field K] [CharZero K] [IsAlgClosed K] {m n : ℕ}
variable [Fact (0 < m)] [Fact (0 < n)] [Fact (1 < m)] [Fact (1 < n)]

/-- Localization of the global block normalization at the Schur divisor is the integral closure
of the Schur DVR in the block fixed field. -/
noncomputable def criticalBlockSchurLocalizationEquiv
    (hm : 1 < m) (hn : 1 < n) (B : Set (criticalGeometricSheet K m n)) :
    Localization (Algebra.algebraMapSubmonoid (CriticalBlockNormalization K B)
      (criticalSchurChartUnder K (m := m) (n := n)).primeCompl) ≃ₐ[
        CriticalSchurNormalBaseRing K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn)]
      integralClosure
        (CriticalSchurNormalBaseRing K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn))
        (CriticalBlockFixedField K B) := by
  letI : IsScalarTower (criticalObservationChartRing K m n)
      (CriticalSchurNormalBaseRing K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn))
      (criticalNormalClosure K m n) := IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply
        (criticalObservationChartRing K m n) (criticalObservationField K m n)
        (criticalNormalClosure K m n),
      IsScalarTower.algebraMap_apply
        (CriticalSchurNormalBaseRing K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn))
        (criticalObservationField K m n) (criticalNormalClosure K m n),
      ← IsScalarTower.algebraMap_apply
        (criticalObservationChartRing K m n)
        (CriticalSchurNormalBaseRing K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn))
        (criticalObservationField K m n)]
  letI : IsScalarTower (criticalObservationChartRing K m n)
      (CriticalSchurNormalBaseRing K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn))
      (CriticalBlockFixedField K B) := IsScalarTower.of_algebraMap_eq fun x => by
    apply (algebraMap (CriticalBlockFixedField K B) (criticalNormalClosure K m n)).injective
    rw [← IsScalarTower.algebraMap_apply
        (criticalObservationChartRing K m n) (CriticalBlockFixedField K B)
        (criticalNormalClosure K m n),
      ← IsScalarTower.algebraMap_apply
        (CriticalSchurNormalBaseRing K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn))
        (CriticalBlockFixedField K B) (criticalNormalClosure K m n)]
    exact IsScalarTower.algebraMap_apply
      (criticalObservationChartRing K m n)
      (CriticalSchurNormalBaseRing K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn))
      (criticalNormalClosure K m n) x
  exact integralClosureLocalizationAlgEquiv
    (criticalSchurChartUnder K (m := m) (n := n)).primeCompl

/-- A non-singleton block normalization is formally unramified after localization at the Schur
divisor. -/
theorem criticalBlockSchurLocalization_formallyUnramified [DecidableEq K]
    (hm : 1 < m) (hn : 1 < n)
    {B : Set (criticalGeometricSheet K m n)}
    (hB : MulAction.IsBlock (criticalGeometricMonodromy K m n) B)
    (hB2 : ∃ x ∈ B, ∃ y ∈ B, x ≠ y) :
    Algebra.FormallyUnramified
      (CriticalSchurNormalBaseRing K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn))
      (Localization (Algebra.algebraMapSubmonoid (CriticalBlockNormalization K B)
        (criticalSchurChartUnder K (m := m) (n := n)).primeCompl)) := by
  exact (Algebra.FormallyUnramified.iff_of_equiv
    (criticalBlockSchurLocalizationEquiv K hm hn B)).mpr
      (criticalBlockSchurNormalization_formallyUnramified K hm hn hB hB2)

end
end GaloisForLFunctions.HTGeometry
