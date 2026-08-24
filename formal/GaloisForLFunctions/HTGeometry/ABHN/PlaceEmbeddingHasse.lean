import GaloisForLFunctions.HTGeometry.ABHN.Places

/-!
# One-place Hasse separation for number-field elements

Every completion embedding of a number field is faithful.  Thus, for field elements themselves,
one arbitrary place already gives a complete local profile; the all-place diagonal contains no
extra equality information.  This isolates the point where genuine ABHN content begins: local
Brauer invariants and their reciprocity relation, rather than scalar equality.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open NumberField

noncomputable section

universe u

/-- A number field is equivalent to the subfield profile actually realized inside any one
completion. -/
def placeEmbeddingHasseEquivRealizedProfile
    (K : Type u) [Field K] [NumberField K] (v : NumberFieldPlace K) :
    K ≃+* RingHom.range (placeEmbedding K v) :=
  RingEquiv.ofBijective (RingHom.rangeRestrict (placeEmbedding K v))
    ⟨fun _ _ h => placeEmbedding_injective K v (congrArg Subtype.val h),
      RingHom.rangeRestrict_surjective _⟩

/-- The realized-profile equivalence evaluates through the canonical completion embedding. -/
@[simp] theorem placeEmbeddingHasseEquivRealizedProfile_apply
    (K : Type u) [Field K] [NumberField K] (v : NumberFieldPlace K) (x : K) :
    (placeEmbeddingHasseEquivRealizedProfile K v x).1 = placeEmbedding K v x := rfl

/-- Equality of number-field elements is detected at any fixed completion. -/
theorem placeEmbedding_congr_hasse_iff
    (K : Type u) [Field K] [NumberField K] (v : NumberFieldPlace K) (x y : K) :
    placeEmbedding K v x = placeEmbedding K v y ↔ x = y :=
  (placeEmbedding_injective K v).eq_iff

/-- A number-field element vanishes exactly when its image at one fixed place vanishes. -/
theorem placeEmbedding_eq_zero_hasse_iff
    (K : Type u) [Field K] [NumberField K] (v : NumberFieldPlace K) (x : K) :
    placeEmbedding K v x = 0 ↔ x = 0 := by
  rw [← map_zero (placeEmbedding K v)]
  exact placeEmbedding_congr_hasse_iff K v x 0

/-- The all-place diagonal detects exactly the same scalar equalities as any one completion. -/
theorem placeDiagonal_congr_iff_at
    (K : Type u) [Field K] [NumberField K] (v : NumberFieldPlace K) (x y : K) :
    placeDiagonal K x = placeDiagonal K y ↔
      placeEmbedding K v x = placeEmbedding K v y := by
  rw [placeEmbedding_congr_hasse_iff]
  exact (placeDiagonal_injective K).eq_iff

end


end GaloisForLFunctions.HTGeometry.ABHN
