import GaloisForLFunctions.HTGeometry.ProjectiveHorizonFrameInvariants

/-!
# Reconstruction of the jet field from the horizon field of a span

The moving frame of a covector span reconstructs every jet coordinate from horizon observables and
the jet coordinates at the frame orders alone.  For a direction inside the span this is the frame
equation; for a direction outside it, it is the definition of the normalised transverse jet.

Consequently the jet field is generated over the horizon field of a span of rank `r` by the `rN`
jet coordinates of the initial block, which bounds the codimension of the horizon field.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]

/-- The jet coordinates of every direction at the frame orders of a span. -/
def initialJetBlock (t : Finset n) (K : Type*) [Field K] : Set (HomogeneousJetField n K) :=
  Set.range fun p : n × ↥t => freeCoordinate K (n × ℕ) (p.1, jetOrder t p.2)

omit [Fintype n] [DecidableEq n] in
theorem mem_initialJetBlock (t : Finset n) (k : n) (c : ↥t) :
    freeCoordinate K (n × ℕ) (k, jetOrder t c) ∈ initialJetBlock t K :=
  ⟨(k, c), rfl⟩

/-- The horizon field of a span together with the jet coordinates at its frame orders. -/
def frameAdaptedGenerators (t : Finset n) (K : Type*) [Field K] :
    Set (HomogeneousJetField n K) :=
  (horizonField (K := K) (↑t : Set n) : Set (HomogeneousJetField n K)) ∪ initialJetBlock t K

theorem horizonField_subset_frameAdaptedGenerators (t : Finset n) :
    (horizonField (K := K) (↑t : Set n) : Set (HomogeneousJetField n K)) ⊆
      frameAdaptedGenerators t K :=
  Set.subset_union_left

/-- **Reconstruction of a jet coordinate.**  Every jet coordinate is a horizon observable of the
span combined with jet coordinates at the frame orders. -/
theorem freeCoordinate_mem_frameAdaptedAdjoin (t : Finset n) (k : n) (l : ℕ) :
    freeCoordinate K (n × ℕ) (k, l) ∈
      IntermediateField.adjoin K (frameAdaptedGenerators t K) := by
  have hhor : ∀ f ∈ horizonField (K := K) (↑t : Set n),
      f ∈ IntermediateField.adjoin K (frameAdaptedGenerators t K) := fun f hf =>
    IntermediateField.subset_adjoin K _ (Or.inl hf)
  have hblock : ∀ (j : n) (c : ↥t), freeCoordinate K (n × ℕ) (j, jetOrder t c) ∈
      IntermediateField.adjoin K (frameAdaptedGenerators t K) := fun j c =>
    IntermediateField.subset_adjoin K _ (Or.inr (mem_initialJetBlock t j c))
  by_cases hk : k ∈ t
  · have h := congrFun (jetFrame_mulVec_frameCoord (K := K) t l) ⟨k, hk⟩
    rw [mulVec_apply_eq_sum] at h
    simp only [jetFrame, jetArray, jetColumn, Matrix.of_apply] at h
    rw [← h]
    exact sum_mem fun c _ => mul_mem (hblock k c) (hhor _ (frameCoord_mem_horizonField t l c))
  · have h : freeCoordinate K (n × ℕ) (k, l) = transverseNormal (K := K) t k l +
        ∑ c : ↥t, frameCoord t l c * freeCoordinate K (n × ℕ) (k, jetOrder t c) := by
      rw [transverseNormal]
      ring
    rw [h]
    refine add_mem (hhor _ (transverseNormal_mem_horizonField hk l))
      (sum_mem fun c _ => mul_mem ?_ (hblock k c))
    exact hhor _ (frameCoord_mem_horizonField t l c)

/-- **The jet field over the horizon field of a span.**  The horizon field of a covector span
together with the jet coordinates at the frame orders of that span generates the whole jet field.
For a span of rank `r` in `N` directions the block has `rN` elements, so this bounds the
codimension of the horizon field. -/
theorem frameAdaptedGenerators_adjoin_eq_top [CharZero K] (t : Finset n) :
    IntermediateField.adjoin K (frameAdaptedGenerators t K) = ⊤ := by
  refine le_antisymm le_top ?_
  rw [← freeCoordinateField_univ (C := K) (σ := n × ℕ), freeCoordinateField,
    IntermediateField.adjoin_le_iff]
  rintro _ ⟨⟨k, l⟩, -, rfl⟩
  exact freeCoordinate_mem_frameAdaptedAdjoin t k l

omit [DecidableEq n] in
/-- The initial block of a span of rank `r` in `N` directions has `rN` elements. -/
theorem card_initialJetBlock (t : Finset n) :
    Nat.card (n × ↥t) = Nat.card n * t.card := by
  rw [Nat.card_prod, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_coe]

end

end GaloisForLFunctions.HTGeometry
