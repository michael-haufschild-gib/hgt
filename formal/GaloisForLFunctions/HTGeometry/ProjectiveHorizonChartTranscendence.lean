import GaloisForLFunctions.HTGeometry.ProjectiveHorizonRankSeparation

/-!
# Transcendence of a chart over its horizon

The chart field of an affine chart is generated over its derivative horizon by the zeroth-order
affine coordinates, and those coordinates are algebraically independent over the horizon.  There
are `N-1` of them, which is the rank-one instance `1·N-1` of the observer codimension.

The codimension itself is the parameter count of the observer group, whose block parametrisation
splits it into a unimodular chart block and a transverse shear: `(r²-1) + r(N-r) = rN-1`.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]

/-! ## The chart field over its horizon -/

omit [Fintype n] [DecidableEq n] in
/-- The positive-order affine jets are exactly the images of the positive jet orders. -/
theorem chartTailGenerators_eq_image (i : n) :
    chartTailGenerators i K =
      (fun p : ChartIndex i × ℕ => affineJet (K := K) i p.1.1 p.2) ''
        {p : ChartIndex i × ℕ | 1 ≤ p.2} := by
  ext f
  constructor
  · rintro ⟨k, hk, l, rfl⟩
    exact ⟨(⟨k, hk⟩, l + 1), by simp, rfl⟩
  · rintro ⟨⟨⟨k, hk⟩, l⟩, hl, rfl⟩
    simp only [Set.mem_setOf_eq] at hl
    obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
    exact ⟨k, hk, l', rfl⟩

omit [Fintype n] in
/-- The zeroth-order affine coordinates are algebraically independent over the algebra generated
by the positive-order ones. -/
theorem algebraicIndependent_affineCoord_over_adjoin (i : n) :
    AlgebraicIndependent (↥(Algebra.adjoin K (chartTailGenerators i K)))
      (fun p : ↥{p : ChartIndex i × ℕ | p.2 = 0} =>
        affineJet (K := K) i (p : ChartIndex i × ℕ).1.1 (p : ChartIndex i × ℕ).2) := by
  have hdisj : Disjoint {p : ChartIndex i × ℕ | 1 ≤ p.2} {p : ChartIndex i × ℕ | p.2 = 0} := by
    rw [Set.disjoint_left]
    rintro ⟨k, l⟩ hl h0
    simp only [Set.mem_setOf_eq] at hl h0
    omega
  have hsub := (algebraicIndependent_affineJet (K := K) i).adjoin_of_disjoint hdisj
  rwa [← chartTailGenerators_eq_image i] at hsub

/-- The chart of a projective source in dimension `N` has `N-1` affine coordinates. -/
theorem card_chartIndex (i : n) :
    Fintype.card (ChartIndex i) = Fintype.card n - 1 := by
  classical
  have hcompl := Fintype.card_subtype_compl (p := fun k : n => k = i)
  have hone : Fintype.card {k : n // k = i} = 1 := Fintype.card_subtype_eq i
  rw [hone] at hcompl
  exact hcompl

omit [Fintype n] in
/-- The zeroth-order chart jets are indexed by the chart directions. -/
def chartZeroEquiv (i : n) : ChartIndex i ≃ ↥{p : ChartIndex i × ℕ | p.2 = 0} where
  toFun k := ⟨(k, 0), rfl⟩
  invFun p := (p : ChartIndex i × ℕ).1
  left_inv _ := rfl
  right_inv p := by
    apply Subtype.ext
    obtain ⟨⟨k, l⟩, hl⟩ := p
    simp only [Set.mem_setOf_eq] at hl
    subst hl
    rfl

/-- **Rank-one observer codimension.**  The independent zeroth-order chart family has exactly
`N-1` members, the rank-one instance `1·N-1` of `rN-1`. -/
theorem card_chartZeroIndex (i : n) :
    Nat.card {p : ChartIndex i × ℕ | p.2 = 0} = Fintype.card n - 1 := by
  classical
  rw [Nat.card_congr (chartZeroEquiv i).symm, Nat.card_eq_fintype_card, card_chartIndex]

omit [Fintype n] in
/-- The chart field is generated over the constants by its derivative horizon together with the
zeroth-order affine coordinates. -/
theorem projectiveJetField_eq_adjoin_tail_union_coord (i : n) :
    projectiveJetField i K =
      IntermediateField.adjoin K
        (chartTailGenerators i K ∪
          Set.range fun k : ChartIndex i => affineCoord (K := K) i (k : n)) := by
  apply le_antisymm
  · rw [projectiveJetField, IntermediateField.adjoin_le_iff]
    rintro _ ⟨k, l, rfl⟩
    by_cases hk : k = i
    · rw [hk, affineJet_self]
      split
      · exact (IntermediateField.adjoin K _).one_mem
      · exact (IntermediateField.adjoin K _).zero_mem
    · cases l with
      | zero =>
          exact IntermediateField.subset_adjoin K _ (Or.inr ⟨⟨k, hk⟩, rfl⟩)
      | succ l =>
          exact IntermediateField.subset_adjoin K _ (Or.inl ⟨k, hk, l, rfl⟩)
  · rw [IntermediateField.adjoin_le_iff]
    rintro f (⟨k, hk, l, rfl⟩ | ⟨k, rfl⟩)
    · exact affineJet_mem_projectiveJetField i k (l + 1)
    · exact affineJet_mem_projectiveJetField i (k : n) 0

/-! ## The observer codimension -/

/-- **Observer codimension.**  The block parametrisation of the observer group splits its
parameter count into the unimodular chart block and the transverse shear, and the two add to the
codimension `rN-1` of the horizon field. -/
theorem observer_dimension (N r : ℤ) : (r * r - 1) + r * (N - r) = r * N - 1 := by
  ring

end

end GaloisForLFunctions.HTGeometry
