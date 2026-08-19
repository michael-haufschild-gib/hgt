import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Descent on a potential bounded below

A potential that is bounded below by a positive constant, and which can be strictly contracted by a
fixed factor from every non-terminal state, must reach a terminal state: iterating the contraction
drives the potential below the bound.

This is the termination scheme of lattice basis reduction.  The potential is `∏ₖ det Aₖ`, the
contraction is the Lovász swap, and terminality is the Siegel condition.

* `exists_terminal_of_contracting` : **a terminal state is reachable.**
-/

namespace GaloisForLFunctions.HTGeometry

/-- **Descent on a potential bounded below.**  If every non-terminal state admits a successor whose
potential is a fixed proportion `q < 1` of its own, and the potential never drops below a positive
`c`, then a terminal state exists. -/
theorem exists_terminal_of_contracting {α : Type*} (Φ : α → ℝ) (Red : α → Prop)
    {c q : ℝ} (hc : 0 < c) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hlow : ∀ a, c ≤ Φ a)
    (hstep : ∀ a, ¬ Red a → ∃ b, Φ b ≤ q * Φ a)
    (a : α) : ∃ b, Red b := by
  by_contra hcon
  push Not at hcon
  have hchain : ∀ N : ℕ, ∃ b, Φ b ≤ q ^ N * Φ a := by
    intro N
    induction N with
    | zero => exact ⟨a, by simp⟩
    | succ N ih =>
        obtain ⟨b, hb⟩ := ih
        obtain ⟨b', hb'⟩ := hstep b (hcon b)
        refine ⟨b', ?_⟩
        calc Φ b' ≤ q * Φ b := hb'
          _ ≤ q * (q ^ N * Φ a) := mul_le_mul_of_nonneg_left hb hq0
          _ = q ^ (N + 1) * Φ a := by ring
  have hlim : Filter.Tendsto (fun N : ℕ => q ^ N * Φ a) Filter.atTop (nhds (0 * Φ a)) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const _
  rw [zero_mul] at hlim
  obtain ⟨N, hN⟩ := (hlim.eventually (eventually_lt_nhds hc)).exists
  obtain ⟨b, hb⟩ := hchain N
  exact absurd (hlow b) (not_le.2 (lt_of_le_of_lt hb hN))

end GaloisForLFunctions.HTGeometry
