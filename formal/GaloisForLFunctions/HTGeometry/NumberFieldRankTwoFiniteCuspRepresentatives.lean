import GaloisForLFunctions.HTGeometry.NumberFieldRankTwoCuspTransitivity

/-!
# A finite complete family of rank-two number-field cusps

Only ideal classes actually attained by nonzero rank-two vectors are retained.  This range is
finite, and choice supplies one vector in every attained class.  Projective transitivity then sends
every nonzero vector to one of these finitely many representatives by an integral determinant-one
matrix and a nonzero field scalar.
-/

namespace GaloisForLFunctions.HTGeometry

open NumberField
open scoped Classical NumberField

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

/-- Finite type of ideal classes attained by rank-two projective cusps. -/
def numberFieldRankTwoCuspType :=
  Set.range (numberFieldRankTwoCuspClass K)

noncomputable instance numberFieldRankTwoCuspType_fintype :
    Fintype (numberFieldRankTwoCuspType K) :=
  (finite_range_numberFieldRankTwoCuspClass K).fintype

/-- One nonzero rank-two vector representing an attained cusp class. -/
def numberFieldRankTwoCuspRepresentative
    (c : numberFieldRankTwoCuspType K) :
    numberFieldRankTwoNonzeroVector K :=
  Classical.choose c.2

/-- The chosen vector has the prescribed cusp class. -/
@[simp]
theorem numberFieldRankTwoCuspRepresentative_class
    (c : numberFieldRankTwoCuspType K) :
    numberFieldRankTwoCuspClass K
      (numberFieldRankTwoCuspRepresentative K c) = c.1 :=
  Classical.choose_spec c.2

/-- **Finite complete rank-two cusp family.**  Every nonzero vector is projectively carried to one
chosen representative by `SL₂(𝓞_K)`. -/
theorem exists_numberFieldRankTwo_finiteCuspRepresentative_projectiveMap
    (v : numberFieldRankTwoNonzeroVector K) :
    ∃ c : numberFieldRankTwoCuspType K,
      ∃ g : Matrix.SpecialLinearGroup (Fin 2) (𝓞 K),
        ∃ a : K, a ≠ 0 ∧
          ∀ i, (numberFieldRankTwoMatrixBaseChange K
            (g : Matrix (Fin 2) (Fin 2) (𝓞 K))).mulVec v.1 i =
              a * (numberFieldRankTwoCuspRepresentative K c).1 i := by
  let c : numberFieldRankTwoCuspType K :=
    ⟨numberFieldRankTwoCuspClass K v, ⟨v, rfl⟩⟩
  have hc : numberFieldRankTwoCuspClass K v =
      numberFieldRankTwoCuspClass K (numberFieldRankTwoCuspRepresentative K c) := by
    rw [numberFieldRankTwoCuspRepresentative_class]
  obtain ⟨g, a, ha, hmap⟩ :=
    exists_numberFieldRankTwoSpecialLinear_projective_map_of_cuspClass_eq K
      v (numberFieldRankTwoCuspRepresentative K c) hc
  exact ⟨c, g, a, ha, hmap⟩

end

end GaloisForLFunctions.HTGeometry
