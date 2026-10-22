import GaloisForLFunctions.HTGeometry.Critical.Block.SchurNormalizationRamification
import GaloisForLFunctions.HTGeometry.Critical.Geometric.NormalClosureTower
import GaloisForLFunctions.HTGeometry.RamificationIndexOneFormalUnramified

/-!
# Formal unramifiedness of Schur-local block normalizations

The normalization of the observation Schur DVR in every non-singleton block field is formally
unramified.  The proof combines generic ramification index one, uniform index one at every nonzero
prime, and characteristic-zero residue fields.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 2000000

variable (K : Type*) [Field K] [CharZero K] [IsAlgClosed K] {m n : ℕ}
variable [Fact (0 < m)] [Fact (0 < n)] [Fact (1 < m)] [Fact (1 < n)]

/-- The Schur-local normalization in a non-singleton block fixed field is formally unramified. -/
theorem criticalBlockSchurNormalization_formallyUnramified [DecidableEq K]
    (hm : 1 < m) (hn : 1 < n)
    {B : Set (criticalGeometricSheet K m n)}
    (hB : MulAction.IsBlock (criticalGeometricMonodromy K m n) B)
    (hB2 : ∃ x ∈ B, ∃ y ∈ B, x ≠ y) :
    Algebra.FormallyUnramified
      (CriticalSchurNormalBaseRing K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn))
      (integralClosure
        (CriticalSchurNormalBaseRing K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn))
        (CriticalBlockFixedField K B)) := by
  let hm0 := Nat.zero_lt_of_lt hm
  let hn0 := Nat.zero_lt_of_lt hn
  let R := CriticalSchurNormalBaseRing K hm0 hn0
  let F := criticalObservationField K m n
  let L := criticalNormalClosure K m n
  let M := CriticalBlockFixedField K B
  let C := integralClosure R M
  haveI : FiniteDimensional F L := criticalNormalClosure_finiteDimensional K hm0 hn0
  haveI : IsGalois F L := criticalNormalClosure_isGalois K hm0 hn0
  haveI : Algebra.IsSeparable F M := Algebra.isSeparable_tower_bot_of_isSeparable F M L
  haveI : FiniteDimensional F M := by infer_instance
  haveI : Module.Finite R C := IsIntegralClosure.finite R F M C
  haveI : FaithfulSMul R C :=
    (faithfulSMul_iff_algebraMap_injective R C).2
      (ValuationInertia.injective_algebraMap_intermediateBase M)
  apply Algebra.formallyUnramified_of_ramificationIdx_eq_one
  · intro q hq
    letI : q.IsPrime := hq
    letI : CharZero (q.under R).ResidueField :=
      charZero_residueField_of_ringHom (q.under R)
        (criticalObservationSchurConstantBaseMap K hm0 hn0)
    infer_instance
  · intro q _ hq0
    exact criticalBlockSchurNormalization_ramificationIdx_eq_one K hm hn hB hB2 q hq0

end
end GaloisForLFunctions.HTGeometry
