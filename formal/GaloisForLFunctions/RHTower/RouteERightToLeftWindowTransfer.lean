import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

/-!
# Route E right-to-left short-window transfer

An all-right short-interval supply theorem already contains a numerically downward supply theorem.
At height `y`, apply the right-window theorem at `y - 2 * h y`.  Monotonicity of `h` places that
entire window strictly below `y`, without changing its counted predicate.  This separates numerical
direction from Möbius-grade direction in cutoff-dependent factorization relations.
-/

namespace RHTower

open Finset

/-- Real-scale form used when the structured token centre is a quotient such as `n / t`. -/
theorem routeE_real_rightWindow_subset_leftWindow
    (h : ℝ → ℝ) (hmono : Monotone h) {y : ℝ}
    (hpos : 0 < h y) :
    Set.Ioc (y - 2 * h y) ((y - 2 * h y) + h (y - 2 * h y)) ⊆
      Set.Ioo (y - 2 * h y) y := by
  intro m hm
  refine ⟨hm.1, ?_⟩
  have hbase : y - 2 * h y ≤ y := by linarith
  have hwindow : h (y - 2 * h y) ≤ h y := hmono hbase
  linarith [hm.2]

/-- The right window based at `y - 2h(y)` lies inside the left window of radius `2h(y)` at `y`. -/
theorem routeE_rightWindow_subset_leftWindow
    (h : ℕ → ℕ) (hmono : Monotone h) {y : ℕ}
    (hfit : 2 * h y ≤ y) :
    Finset.Ioc (y - 2 * h y) ((y - 2 * h y) + h (y - 2 * h y)) ⊆
      Finset.Ioo (y - 2 * h y) y := by
  intro m hm
  rw [Finset.mem_Ioc] at hm
  rw [Finset.mem_Ioo]
  refine ⟨hm.1, ?_⟩
  have hbase : y - 2 * h y ≤ y := Nat.sub_le _ _
  have hwindow : h (y - 2 * h y) ≤ h y := hmono hbase
  omega

/-- Every counted right-window lower bound transfers unchanged to the corresponding left window. -/
theorem routeE_leftWindow_card_ge_rightWindow_card
    (h : ℕ → ℕ) (hmono : Monotone h) (A : ℕ → Prop) [DecidablePred A]
    {y D : ℕ} (hfit : 2 * h y ≤ y)
    (hsupply : D ≤
      ((Finset.Ioc (y - 2 * h y) ((y - 2 * h y) + h (y - 2 * h y))).filter A).card) :
    D ≤ ((Finset.Ioo (y - 2 * h y) y).filter A).card := by
  refine hsupply.trans (Finset.card_le_card ?_)
  exact Finset.filter_subset_filter _ (routeE_rightWindow_subset_leftWindow h hmono hfit)

/-- A nonempty all-right supply gives a predicate-preserving numerical predecessor within `2h(y)`. -/
theorem routeE_exists_leftWindow_of_rightWindow
    (h : ℕ → ℕ) (hmono : Monotone h) (A : ℕ → Prop) [DecidablePred A]
    {y : ℕ} (hfit : 2 * h y ≤ y)
    (hsupply : 0 <
      ((Finset.Ioc (y - 2 * h y) ((y - 2 * h y) + h (y - 2 * h y))).filter A).card) :
    ∃ m, A m ∧ y - 2 * h y < m ∧ m < y := by
  have hcard : 0 < ((Finset.Ioo (y - 2 * h y) y).filter A).card :=
    routeE_leftWindow_card_ge_rightWindow_card h hmono A hfit hsupply
  obtain ⟨m, hm⟩ := Finset.card_pos.mp hcard
  rw [Finset.mem_filter, Finset.mem_Ioo] at hm
  exact ⟨m, hm.2, hm.1.1, hm.1.2⟩

end RHTower
