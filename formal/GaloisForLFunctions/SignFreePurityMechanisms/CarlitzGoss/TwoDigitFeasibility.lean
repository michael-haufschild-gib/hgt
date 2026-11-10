import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DeletionReduction
import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.BoundaryFeasibility

/-!
# Feasibility after deleting two digits

A non-strict inverse-content threshold reserves either deleted digit for the
last part after deleting the other. If that reserved power exceeds every
power in an optimal last part, deletion produces a smaller nongreedy optimum.
-/

open Finset
namespace GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition
variable {p s k : ℕ} [NeZero s] {S : Finset (Digit p)}

/-- A non-strict feasibility margin after deleting two digits reserves one of them for the last part. -/
theorem exists_last_mem_of_two_digit_threshold (hp : 2 ≤ p) {x y : Digit p}
    (hy : y ∈ S) (hxy : x ≠ y)
    (hge : ∀ h : ZMod s, ((k + 1 : ℕ) : ℚ) ≤ inverseContent (p : ℚ)
      (fun j => (tokenContent (fun t : Digit p => (t.1 : ZMod s)) (S \ {x, y}) j : ℚ)) h) :
    ∃ R : DigitComposition p s (k + 2) (S \ {x}), y ∈ R.parts (Fin.last (k + 1)) := by
  have hd : Disjoint (S \ {x, y}) {y} := by
    apply disjoint_left.mpr
    intro z hz hzy
    have he : z = y := mem_singleton.mp hzy
    subst z
    exact (mem_sdiff.mp hz).2 (mem_insert.mpr (Or.inr (mem_singleton_self y)))
  have hc : (S \ {x, y}) ∪ {y} = S \ {x} := by
    ext z
    constructor
    · intro hz
      rcases mem_union.mp hz with hz | hz
      · refine mem_sdiff.mpr ⟨(mem_sdiff.mp hz).1, ?_⟩
        intro hzx
        exact (mem_sdiff.mp hz).2 (mem_insert.mpr (Or.inl (mem_singleton.mp hzx)))
      · have he : z = y := mem_singleton.mp hz
        subst z
        exact mem_sdiff.mpr ⟨hy, fun h => hxy (mem_singleton.mp h).symm⟩
    · intro hz
      by_cases hzy : z = y
      · exact mem_union_right _ (mem_singleton.mpr hzy)
      · refine mem_union_left _ (mem_sdiff.mpr ⟨(mem_sdiff.mp hz).1, ?_⟩)
        intro hpair
        rcases mem_insert.mp hpair with hzx | hzy'
        · exact (mem_sdiff.mp hz).2 (mem_singleton.mpr hzx)
        · exact hzy (mem_singleton.mp hzy')
  rcases (nonempty_or_divisible_iff_inverseContent_ge (k := k) hp).mpr hge with hR | ⟨hR, hdiv⟩
  · obtain ⟨R⟩ := hR
    refine ⟨R.extendLast hd hc, ?_⟩
    rw [extendLast_parts, Fin.snoc_last]
    exact mem_union_right _ (mem_singleton_self y)
  · obtain ⟨R⟩ := hR
    refine ⟨R.appendLast hd (singleton_nonempty y) (R.all_divisible_of_total hdiv) hc, ?_⟩
    change y ∈ (Fin.snoc R.parts {y} : Fin (k + 2) → Finset (Digit p)) (Fin.last (k + 1))
    rw [Fin.snoc_last]
    exact mem_singleton_self y

/-- Reserving a power above the whole last part produces a smaller nongreedy optimum. -/
theorem exists_smaller_of_two_digit_threshold {C : DigitComposition p s (k + 2) S}
    (hp : 2 ≤ p) (hC : C.IsOptimal) {x y : Digit p}
    (hx : x ∈ C.parts (Fin.last (k + 1))) (hy : y ∈ S)
    (hbelow : ∀ z ∈ C.parts (Fin.last (k + 1)), z.1 < y.1)
    (hge : ∀ h : ZMod s, ((k + 1 : ℕ) : ℚ) ≤ inverseContent (p : ℚ)
      (fun j => (tokenContent (fun t : Digit p => (t.1 : ZMod s)) (S \ {x, y}) j : ℚ)) h) :
    ∃ O G : DigitComposition p s (k + 2) (S \ {x}),
      (S \ {x}).card < S.card ∧ O.IsOptimal ∧ G.IsGreedy ∧ O.value ≠ G.value := by
  have hxy : x ≠ y := by intro he; have hh := hbelow x hx; rw [he] at hh; exact (lt_irrefl _ hh)
  obtain ⟨R, hyR⟩ := exists_last_mem_of_two_digit_threshold hp hy hxy hge
  have hT : {x} ⊆ C.parts (Fin.last (k + 1)) := singleton_subset_iff.mpr hx
  have hrem : (C.parts (Fin.last (k + 1)) \ {x}).Nonempty :=
    (nonempty_sdiff_iff_last_nonempty hp (Or.inl hC) hT).mp ⟨R⟩
  let O := C.removeLast hT hrem
  have hO : O.IsOptimal := hC.removeLast hT hrem
  have hsmall : O.value (Fin.last (k + 1)) < (p : ℤ) ^ y.1 := by
    apply digitValue_lt_pow (by omega : 1 ≤ p)
    intro z hz
    change z ∈ (C.removeLast hT hrem).parts (Fin.last (k + 1)) at hz
    rw [removeLast_parts, Fin.snoc_last] at hz
    exact hbelow z (mem_sdiff.mp hz).1
  have hlarge : (p : ℤ) ^ y.1 ≤ R.value (Fin.last (k + 1)) := by
    have hh := tokenValue_subset p Prod.fst (singleton_subset_iff.mpr hyR)
    simpa only [tokenValue, sum_singleton, value, digitValue] using hh
  have hOn : ¬ O.IsGreedy := by
    intro hg
    have hm := hg.last_max R
    linarith only [hm, hsmall, hlarge]
  obtain ⟨G, hG⟩ := exists_greedy ⟨O⟩
  have hcard : (S \ {x}).card < S.card := by
    have he : S \ {x} = S.erase x := by
      ext z
      simp only [mem_sdiff, mem_singleton, mem_erase, and_comm]
    rw [he]
    exact card_erase_lt_of_mem (C.subset _ hx)
  refine ⟨O, G, hcard, hO, hG, ?_⟩
  intro hv
  exact hOn ((isGreedy_congr_values hv).mpr hG)

end GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition

#print axioms GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition.exists_smaller_of_two_digit_threshold
