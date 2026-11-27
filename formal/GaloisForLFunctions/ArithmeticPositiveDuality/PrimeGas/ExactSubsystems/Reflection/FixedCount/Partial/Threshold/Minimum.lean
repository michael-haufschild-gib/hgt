import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.FixedCount.Partial.Threshold.PrimeEdges

/-! # Exact first unpaired energy from at most two greedy values per prime -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.FixedCount.Partial.Threshold

open Finset

variable {S : Finset Nat.Primes} (c : S → ℕ) (m : ℕ)

def candidates := readings price c (center c m) m ∪ readings reversePrice c (center c m) m

theorem card_candidates : (candidates c m).card ≤ 2*S.card := by
  have h (e : S → ℝ) : (readings e c (center c m) m).card ≤ S.card :=
    (card_image_le).trans (by simpa only [Fintype.card_coe] using (active c (center c m) m).card_le_univ)
  exact (card_union_le _ _).trans (by linarith only [h price,h reversePrice])

theorem candidates_subset :
    ↑(candidates c m) ⊆ differences (lowerEdge c m) (upperEdge c m) := by
  obtain ⟨lo,hi⟩ := directed_differences c m
  rw [differences,lo,hi]
  intro z hz
  rcases mem_union.mp hz with h | h
  · exact Or.inl (readings_subset price (price_injective S) _ _ _ h)
  · exact Or.inr (readings_subset reversePrice (reversePrice_injective S) _ _ _ h)

theorem candidates_cover :
    ∀ z ∈ differences (lowerEdge c m) (upperEdge c m), ∃ y ∈ candidates c m, y ≤ z := by
  obtain ⟨lo,hi⟩ := directed_differences c m
  rw [differences,lo,hi]
  have left (i : S) : ordinary price c m i ≤ center c m i ∧ center c m i ≤ ordinary price c m i+c i := by
    have hr : ordinary reversePrice c m i ≤ c i := min_le_left _ _
    unfold center
    omega
  have right (i : S) : ordinary reversePrice c m i ≤ center c m i ∧ center c m i ≤ ordinary reversePrice c m i+c i := by
    have hl : ordinary price c m i ≤ c i := min_le_left _ _
    unfold center
    omega
  rintro z (hz | hz)
  · obtain ⟨y,hy,hle⟩ := readings_cover price (price_injective S) _ _ _ left z hz
    exact ⟨y,mem_union_left _ hy,hle⟩
  · obtain ⟨y,hy,hle⟩ := readings_cover reversePrice (reversePrice_injective S) _ _ _ right z hz
    exact ⟨y,mem_union_right _ hy,hle⟩

/-- At any candidate value its issuing list identifies the edge that contains it. -/
theorem candidate_side {z : ℝ} (hz : z ∈ candidates c m) :
    z ∈ readings price c (center c m) m ↔ z ∈ lowerEdge c m := by
  obtain ⟨lo,hi⟩ := directed_differences c m
  have fromLow (hl : z ∈ readings price c (center c m) m) : z ∈ lowerEdge c m := by
    have h := readings_subset price (price_injective S) c (center c m) m hl
    rw [← lo] at h
    exact h.1
  refine ⟨fromLow,?_⟩
  intro hl
  rcases mem_union.mp hz with left | right
  · exact left
  · have h := readings_subset reversePrice (reversePrice_injective S) c (center c m) m right
    rw [← hi] at h
    exact (h.2 hl).elim

theorem least_iff (z : ℝ) :
    IsLeast (differences (lowerEdge c m) (upperEdge c m)) z ↔ IsLeast (↑(candidates c m) : Set ℝ) z := by
  constructor
  · rintro ⟨hz,hmin⟩
    obtain ⟨y,hy,hle⟩ := candidates_cover c m z hz
    exact ⟨le_antisymm hle (hmin (candidates_subset c m hy)) ▸ hy,fun _ hu => hmin (candidates_subset c m hu)⟩
  · rintro ⟨hz,hmin⟩
    refine ⟨candidates_subset c m hz,?_⟩
    intro y hy
    obtain ⟨w,hw,hle⟩ := candidates_cover c m y hy
    exact (hmin hw).trans hle

/-- The explicit finite minimum is precisely the least offset present at only one edge. -/
theorem first_unpaired (h : (candidates c m).Nonempty) :
    IsLeast (differences (lowerEdge c m) (upperEdge c m)) ((candidates c m).min' h) :=
  (least_iff c m _).mpr ⟨min'_mem _ _,fun _ hx => min'_le _ _ hx⟩

/-- An empty list is equivalent to complete agreement, including infeasible and single-state sectors. -/
theorem no_candidates_iff :
    candidates c m = ∅ ↔ lowerEdge c m = upperEdge c m := by
  constructor
  · intro h
    ext z
    constructor <;> intro hz <;> by_contra hn
    · obtain ⟨_,hy,_⟩ := candidates_cover c m z (Or.inl ⟨hz,hn⟩)
      simp only [h,notMem_empty] at hy
    · obtain ⟨_,hy,_⟩ := candidates_cover c m z (Or.inr ⟨hz,hn⟩)
      simp only [h,notMem_empty] at hy
  · intro h
    apply eq_empty_iff_forall_notMem.mpr
    intro z hz
    have hh := candidates_subset c m hz
    simp only [h,differences,Set.sdiff_self,Set.union_self,Set.mem_empty_iff_false] at hh

#print axioms card_candidates
#print axioms candidate_side
#print axioms least_iff
#print axioms first_unpaired
#print axioms no_candidates_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.FixedCount.Partial.Threshold
