import GaloisForLFunctions.RHTower.Sieve.WindowCell
import GaloisForLFunctions.RHTower.Sieve.GoodStartFibreWindow

/-!
# From a good cofactor window to the marker's cell

The corpus's step-1 conclusion is a sign count on a half-open window `(t, t+L]` at an integer start.
A marker prime `p` accepts as cofactors exactly the `a` with `X < a·p ≤ X+H`, that is
`Sieve/WindowCell.windowCell X H p`, whose start is `⌊X/p⌋`.  So a good window at the marker's start,
short enough to fit inside the cell, transfers its sign count to the cell verbatim.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

/-- The floor start is below the window. -/
theorem lt_succ_div_mul {X p : ℕ} (hp : 0 < p) : X < (X / p + 1) * p := by
  have h : X / p < X / p + 1 := Nat.lt_succ_self _
  exact (Nat.div_lt_iff_lt_mul hp).1 h

/-- **A window at the marker's start fits inside its cell.** -/
theorem Ioc_subset_windowCell {X H p t L : ℕ} (hstart : X < (t + 1) * p)
    (hend : (t + L) * p ≤ X + H) :
    Finset.Ioc t (t + L) ⊆ windowCell X H p := by
  classical
  intro a ha
  rw [Finset.mem_Ioc] at ha
  have hp : 0 < p := by
    rcases Nat.eq_zero_or_pos p with rfl | h
    · simp at hstart
    · exact h
  rw [mem_windowCell_iff hp]
  constructor
  · exact lt_of_lt_of_le hstart (Nat.mul_le_mul_right p (by omega))
  · exact le_trans (Nat.mul_le_mul_right p ha.2) hend

/-- **The sign count transfers to the cell.** -/
theorem card_sign_windowCell_ge {X H p t L : ℕ} {σ : ℤ} {c : ℝ}
    (hsub : Finset.Ioc t (t + L) ⊆ windowCell X H p)
    (hgood : c ≤ (((Finset.Ioc t (t + L)).filter (fun b => moebius b = σ)).card : ℝ)) :
    c ≤ (((windowCell X H p).filter (fun a => moebius a = σ)).card : ℝ) := by
  classical
  refine hgood.trans ?_
  exact Nat.cast_le.2 (Finset.card_le_card (Finset.filter_subset_filter _ hsub))

end RHTower.Sieve
