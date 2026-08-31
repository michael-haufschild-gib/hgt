import Mathlib

/-!
# Telescoping a stepwise decrease

If each step of a sequence either drops the value by a fixed `d` — on a marked set of indices — or
merely does not increase it, then the value at `N` is below the initial one by at least `d` times the
number of marked indices below `N`.

This is the accounting a Wiman–Valiron blow-up argument runs on a partition: the marked indices are
those intervals containing a radius outside the exceptional set, and the unmarked ones are wholly
bad.  Since the wholly bad intervals number at most `M/h`, the total drop is at least
`(N − M/h)·d`, which for `d` proportional to `h` is independent of `h`.
-/

namespace GaloisForLFunctions.HTGeometry

/-- **Telescoping a stepwise decrease.**  If each step either drops the value by `d` (on a marked set
of indices) or does not increase it, then the total drop is at least `d` times the number of marked
indices below `N`. -/
theorem le_sub_card_mul_of_stepwise {ψ : ℕ → ℝ} {d : ℝ} {G : Finset ℕ}
    (hG : ∀ i, i ∈ G → ψ (i + 1) ≤ ψ i - d)
    (hB : ∀ i, i ∉ G → ψ (i + 1) ≤ ψ i) :
    ∀ N : ℕ, ψ N ≤ ψ 0 - ((G.filter (fun i => i < N)).card : ℝ) * d := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
      by_cases hmem : N ∈ G
      · have hstep := hG N hmem
        have hcard : (G.filter (fun i => i < N + 1)).card
            = (G.filter (fun i => i < N)).card + 1 := by
          classical
          have hins : G.filter (fun i => i < N + 1)
              = insert N (G.filter (fun i => i < N)) := by
            ext i
            simp only [Finset.mem_filter, Finset.mem_insert]
            constructor
            · rintro ⟨hiG, hi⟩
              rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
              · exact Or.inr ⟨hiG, h⟩
              · exact Or.inl h
            · rintro (rfl | ⟨hiG, hi⟩)
              · exact ⟨hmem, Nat.lt_succ_self _⟩
              · exact ⟨hiG, Nat.lt_succ_of_lt hi⟩
          rw [hins, Finset.card_insert_of_notMem (by simp)]
        rw [hcard]
        push_cast
        linarith [ih, hstep]
      · have hstep := hB N hmem
        have hcard : (G.filter (fun i => i < N + 1)).card
            = (G.filter (fun i => i < N)).card := by
          classical
          congr 1
          ext i
          simp only [Finset.mem_filter]
          constructor
          · rintro ⟨hiG, hi⟩
            refine ⟨hiG, ?_⟩
            rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
            · exact h
            · exact absurd (h ▸ hiG) hmem
          · rintro ⟨hiG, hi⟩
            exact ⟨hiG, Nat.lt_succ_of_lt hi⟩
        rw [hcard]
        linarith [ih, hstep]

end GaloisForLFunctions.HTGeometry
