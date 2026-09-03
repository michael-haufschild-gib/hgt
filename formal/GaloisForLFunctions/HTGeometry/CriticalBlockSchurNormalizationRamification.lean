import GaloisForLFunctions.HTGeometry.CriticalBlockFieldAllSchurUnramified
import GaloisForLFunctions.HTGeometry.CriticalBlockFieldNormalization
import GaloisForLFunctions.HTGeometry.IntermediatePrimeValuationRealization

/-!
# Every nonzero Schur-local block prime has ramification index one

Every nonzero prime of the normalization of the Schur DVR in a non-singleton block field is
realized by a valuation of the normal closure.  Uniform Schur-inertia containment then makes its
ramification index exactly one.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 2000000

variable (K : Type*) [Field K] [CharZero K] [IsAlgClosed K] {m n : ℕ}
variable [Fact (0 < m)] [Fact (0 < n)] [Fact (1 < m)] [Fact (1 < n)]

/-- Every nonzero prime of the Schur-local normalization in a non-singleton block field has
ramification index one over the observation Schur DVR. -/
theorem criticalBlockSchurNormalization_ramificationIdx_eq_one [DecidableEq K]
    (hm : 1 < m) (hn : 1 < n)
    {B : Set (criticalGeometricSheet K m n)}
    (hB : MulAction.IsBlock (criticalGeometricMonodromy K m n) B)
    (hB2 : ∃ x ∈ B, ∃ y ∈ B, x ≠ y)
    (q : Ideal (integralClosure
      (CriticalSchurNormalBaseRing K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn))
      (CriticalBlockFixedField K B))) [q.IsPrime] (hq0 : q ≠ ⊥) :
    q.ramificationIdx
      (CriticalSchurNormalBaseRing K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn)) = 1 := by
  let hm0 := Nat.zero_lt_of_lt hm
  let hn0 := Nat.zero_lt_of_lt hn
  let R := CriticalSchurNormalBaseRing K hm0 hn0
  let F := criticalObservationField K m n
  let L := criticalNormalClosure K m n
  let M := CriticalBlockFixedField K B
  haveI : FiniteDimensional F L := criticalNormalClosure_finiteDimensional K hm0 hn0
  haveI : IsGalois F L := criticalNormalClosure_isGalois K hm0 hn0
  obtain ⟨W, hRW, hW, hqW⟩ :=
    ValuationInertia.exists_valuationSubring_intermediateCentre_eq M q hq0
  have hcent : ∀ r : R,
      (¬ IsUnit (⟨algebraMap R L r, hRW r⟩ : W)) ↔
        r ∈ IsLocalRing.maximalIdeal R :=
    ValuationInertia.base_centre_of_intermediateCentre_eq M q hq0 W hRW hqW
  have hram := criticalAllSchur_ramificationIdx_blockField_eq_one K hm hn hB hB2
    W hW hRW hcent
  have hqW' : ValuationInertia.intermediateCentre
      (IntermediateField.fixedField (criticalBlockStabilizer K B)) W hRW = q := hqW
  rw [hqW'] at hram
  exact hram

end
end GaloisForLFunctions.HTGeometry
