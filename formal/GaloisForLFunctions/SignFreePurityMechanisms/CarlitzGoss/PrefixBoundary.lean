import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.GreedyWeightBounds

/-!
# The feasibility boundary of an optimal initial prefix

An extra admissible part in the proper initial prefix would improve either
weight or reverse lexicographic order. Hence its smallest inverse-content
coordinate equals its number of parts. Deleting digits from the last part
preserves feasibility exactly while that part remains nonempty.
-/

open Finset
namespace GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition
variable {p s k : ℕ} [NeZero s] {S T : Finset (Digit p)}

omit [NeZero s] in
/-- A greedy composition's proper initial prefix cannot support the same number of parts. -/
theorem IsGreedy.not_nonempty_prefix {C : DigitComposition p s (k + 2) S}
    (hC : C.IsGreedy) (hp : 2 ≤ p) :
    ¬ Nonempty (DigitComposition p s (k + 2) (C.prefixDigits (k + 1))) := by
  rintro ⟨R⟩
  let D := R.extendLast C.prefix_disjoint_last C.prefix_union_last
  have hmax := hC.last_max D
  have he := R.extendLast_last C.prefix_disjoint_last C.prefix_union_last
  have hpos := R.value_pos (by omega : 0 < p) (Fin.last (k + 1))
  change D.value (Fin.last (k + 1)) = R.value (Fin.last (k + 1)) + C.value (Fin.last (k + 1)) at he
  linarith only [hmax, he, hpos]

/-- An optimal composition's proper initial prefix cannot support the same number of parts. -/
theorem IsOptimal.not_nonempty_prefix {C : DigitComposition p s (k + 2) S}
    (hC : C.IsOptimal) (hp : 2 ≤ p) :
    ¬ Nonempty (DigitComposition p s (k + 2) (C.prefixDigits (k + 1))) := by
  intro hR
  obtain ⟨R, hRg⟩ := exists_greedy hR
  have hlower := greedy_weight_lower (k + 1) hp R hRg C.initial_total_divisible
  have hupper := C.initial.weight_le (by omega : 0 < p)
  let D := R.extendLast C.prefix_disjoint_last C.prefix_union_last
  have hD := hC D
  have heD := R.extendLast_weight C.prefix_disjoint_last C.prefix_union_last
  have heC := C.weight_eq_initial_add_last
  change D.weight = R.weight + ((k + 2 : ℕ) : ℤ) * C.value (Fin.last (k + 1)) at heD
  linarith only [hlower, hupper, hD, heD, heC]

theorem not_nonempty_prefix_of_optimal_or_greedy {C : DigitComposition p s (k + 2) S}
    (hp : 2 ≤ p) (hC : C.IsOptimal ∨ C.IsGreedy) :
    ¬ Nonempty (DigitComposition p s (k + 2) (C.prefixDigits (k + 1))) := by
  rcases hC with hC | hC
  · exact hC.not_nonempty_prefix hp
  · exact hC.not_nonempty_prefix hp

/-- The initial prefix lies exactly on the integral feasibility boundary. -/
theorem exists_prefix_inverse_eq {C : DigitComposition p s (k + 2) S}
    (hp : 2 ≤ p) (hC : C.IsOptimal ∨ C.IsGreedy) :
    ∃ h : ZMod s, inverseContent (p : ℚ)
      (fun j => (tokenContent (fun t : Digit p => (t.1 : ZMod s)) (C.prefixDigits (k + 1)) j : ℚ)) h =
        ((k + 1 : ℕ) : ℚ) := by
  have hge := C.initial.inverseContent_ge_length_of_total_divisible hp C.initial_total_divisible
  have hn := not_nonempty_prefix_of_optimal_or_greedy hp hC
  rw [nonempty_iff_inverseContent hp (k + 1)] at hn
  push Not at hn
  obtain ⟨h, hh⟩ := hn
  exact ⟨h, le_antisymm hh (hge h)⟩

omit [NeZero s] in
/-- Deleting the whole last block leaves exactly the initial prefix. -/
theorem sdiff_last_eq_prefix (C : DigitComposition p s (k + 1) S) :
    S \ C.parts (Fin.last k) = C.prefixDigits k := by
  ext x
  constructor
  · intro hx
    have hU : x ∈ C.prefixDigits k ∪ C.parts (Fin.last k) := by
      rw [C.prefix_union_last]
      exact (mem_sdiff.mp hx).1
    exact (mem_union.mp hU).resolve_right (mem_sdiff.mp hx).2
  · intro hx
    exact mem_sdiff.mpr ⟨C.prefix_subset k hx,
      fun hlast => disjoint_left.mp C.prefix_disjoint_last hx hlast⟩

/-- Deletion from the last block preserves feasibility exactly while that block stays nonempty. -/
theorem nonempty_sdiff_iff_last_nonempty {C : DigitComposition p s (k + 2) S}
    (hp : 2 ≤ p) (hC : C.IsOptimal ∨ C.IsGreedy) (hT : T ⊆ C.parts (Fin.last (k + 1))) :
    Nonempty (DigitComposition p s (k + 2) (S \ T)) ↔ (C.parts (Fin.last (k + 1)) \ T).Nonempty := by
  constructor
  · intro hR
    by_contra hn
    have heT : T = C.parts (Fin.last (k + 1)) := by
      apply Subset.antisymm hT
      intro x hx
      by_contra hxT
      exact hn ⟨x, mem_sdiff.mpr ⟨hx, hxT⟩⟩
    rw [heT, C.sdiff_last_eq_prefix] at hR
    exact not_nonempty_prefix_of_optimal_or_greedy hp hC hR
  · intro hne
    exact ⟨C.removeLast hT hne⟩

end GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition

#print axioms GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition.exists_prefix_inverse_eq
#print axioms GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition.nonempty_sdiff_iff_last_nonempty
