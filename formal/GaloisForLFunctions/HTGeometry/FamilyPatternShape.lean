import GaloisForLFunctions.HTGeometry.FamilyPatternBridge
import GaloisForLFunctions.HTGeometry.AnalyticNevanlinnaCarrierRelationFree

/-!
# The family pattern has exactly the shape the bridge expects

The pattern attached to a family jet relation carries one shift slot per component and a uniform jet
depth, so its dependent jet type is definitionally the family bridge's sigma type.  Nothing needs to
be transported between the two descriptions.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions ClassicalAnalyticNevanlinnaCarrierFamily

noncomputable section

variable {m n : ℕ} (P : MvPolynomial (FamilyJetIndex m n) ℂ)

@[simp]
theorem familyPatternOfRelation_shiftCount :
    (familyPatternOfRelation m n P).shiftCount = m := rfl

@[simp]
theorem familyPatternOfRelation_orders (i : Fin m) :
    (familyPatternOfRelation m n P).orders i = n + 1 := rfl

theorem carrierPatternShift_familyPatternOfRelation :
    CarrierPatternShift (familyPatternOfRelation m n P) = Fin m := rfl

/-- The pattern's dependent jet type is the family bridge's sigma type, definitionally. -/
theorem familyPatternOfRelation_sigma :
    (Σ i : CarrierPatternShift (familyPatternOfRelation m n P),
        Fin ((familyPatternOfRelation m n P).orders i))
      = (Σ _ : Fin m, Fin (n + 1)) := rfl

end

end GaloisForLFunctions.HTGeometry
