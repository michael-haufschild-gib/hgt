import GaloisForLFunctions.HTGeometry.DifferentialOperatorMatroid

/-!
# Hasse detection for differential-operator localization

A polynomial differential-operator row can be recovered from its image in the fraction field of
the operator ring.  Equality is therefore detectable after pointwise localization.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

/-- Two polynomial operator rows agree exactly when their fraction-field localizations agree. -/
theorem localizeOperatorRow_congr_hasse_iff
    (C κ : Type u) [Field C] (v w : κ → Polynomial C) :
    localizeOperatorRow (C := C) v = localizeOperatorRow (C := C) w ↔ v = w := by
  constructor
  · intro h
    apply localizeOperatorRow_injective C κ
    simpa using h
  · exact congrArg _

/-- Pointwise equality in the localized operator field detects equality of the global polynomial
row. -/
theorem localizeOperatorRow_pointwise_congr_hasse_iff
    (C κ : Type u) [Field C] (v w : κ → Polynomial C) :
    (∀ j, algebraMap (Polynomial C) (FractionRing (Polynomial C)) (v j) =
      algebraMap (Polynomial C) (FractionRing (Polynomial C)) (w j)) ↔ v = w := by
  rw [← localizeOperatorRow_congr_hasse_iff C κ v w]
  exact ⟨fun h => funext h, fun h j => congrFun h j⟩

end


end GaloisForLFunctions.HTGeometry
