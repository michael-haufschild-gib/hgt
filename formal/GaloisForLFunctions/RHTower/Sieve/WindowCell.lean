import GaloisForLFunctions.RHTower.Sieve.IntervalMultiples

/-!
# The cofactor cell of a marker

For a marker `p` the natural cell is the set of cofactors placing the product in the window:

`windowCell X H p = {a : X < a·p ≤ X + H}`,

realised as the multiples of `p` in `(X, X+H]` divided by `p`.  Its size is the interval count of
those multiples, hence within one of `H/p`.

This turns the cells of the matching argument from abstract data into a construction whose four
required properties — positivity, an upper bound, a size lower bound, and the window condition —
are all theorems.
-/

namespace RHTower.Sieve

open Finset

/-- The cofactors placing `a · p` in the window `(X, X + H]`. -/
def windowCell (X H p : ℕ) : Finset ℕ :=
  ({x ∈ Finset.Ioc X (X + H) | p ∣ x}).image (fun x => x / p)

/-- Membership in the cell is exactly the window condition on the product. -/
theorem mem_windowCell_iff {X H p a : ℕ} (hp : 0 < p) :
    a ∈ windowCell X H p ↔ X < a * p ∧ a * p ≤ X + H := by
  classical
  constructor
  · intro ha
    rw [windowCell, Finset.mem_image] at ha
    obtain ⟨x, hx, rfl⟩ := ha
    rw [Finset.mem_filter, Finset.mem_Ioc] at hx
    obtain ⟨⟨hx1, hx2⟩, hdvd⟩ := hx
    rw [Nat.div_mul_cancel hdvd]
    exact ⟨hx1, hx2⟩
  · intro ha
    rw [windowCell, Finset.mem_image]
    refine ⟨a * p, ?_, Nat.mul_div_cancel a hp⟩
    rw [Finset.mem_filter, Finset.mem_Ioc]
    exact ⟨⟨ha.1, ha.2⟩, dvd_mul_left p a⟩

/-- Cell members are positive. -/
theorem pos_of_mem_windowCell {X H p a : ℕ} (hp : 0 < p) (ha : a ∈ windowCell X H p) : 0 < a := by
  have h := (mem_windowCell_iff hp).1 ha
  rcases Nat.eq_zero_or_pos a with rfl | h'
  · simp at h
  · exact h'

/-- The cell has the cardinality of the multiples of `p` in the window. -/
theorem card_windowCell (X H p : ℕ) :
    (windowCell X H p).card = (#{x ∈ Finset.Ioc X (X + H) | p ∣ x} : ℕ) := by
  classical
  refine Finset.card_image_of_injOn ?_
  intro x hx y hy hxy
  rw [Finset.coe_filter, Set.mem_setOf_eq] at hx hy
  have hx' : p * (x / p) = x := Nat.mul_div_cancel' hx.2
  have hy' : p * (y / p) = y := Nat.mul_div_cancel' hy.2
  dsimp only at hxy
  rw [← hx', ← hy', hxy]

/-- **The cell is large.**  Its size exceeds `H/p − 1`. -/
theorem card_windowCell_gt (X H p : ℕ) (hp : 0 < p) :
    (H : ℝ) / p - 1 < (((windowCell X H p).card : ℕ) : ℝ) := by
  have hab : X ≤ X + H := Nat.le_add_right X H
  have hbound := abs_card_filter_dvd_Ioc_sub_lt p X (X + H) hp hab
  have hlen : (((X + H : ℕ) : ℝ) - (X : ℝ)) = (H : ℝ) := by push_cast; ring
  rw [hlen] at hbound
  rw [card_windowCell X H p]
  have := abs_lt.1 hbound
  linarith [this.1]

end RHTower.Sieve
