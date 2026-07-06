/-
Weighted charge parity for reflected saddle/grid collisions.

`ReflectedGridParity` shows that the unit collision count has one possible odd source:
the square fixed point of the divisor-antidiagonal reflection.  Physical event charge is
weighted, not just counted.  This file proves the weighted statement the reflection route
needs: if the charge is invariant under factor-swap reflection and the fixed diagonal charge
is even, then the total reflected grid charge is even.  Equivalently, the deck reduction at
level two is trivial.
-/
import GaloisForLFunctions.RHTower.ReflectedGridParity

open Complex Real
open scoped BigOperators

namespace RHTower

/-- The weighted charge of the reflected saddle/grid collision carrier. -/
def reflectedGridWeightedCharge (C : ℕ) (q : ℕ × ℕ → ℕ) : ℕ :=
  ∑ x ∈ reflectedGridCollisions C, q x

/-- **Weighted reflected collision parity.**  If the collision weight is invariant under the
factor-swap reflection and every fixed diagonal collision carries even weight, then the total
reflected grid charge is even. -/
theorem reflectedGridWeightedCharge_even_of_swap_invariant_even_fixed {C : ℕ}
    {q : ℕ × ℕ → ℕ}
    (hsym : ∀ x ∈ reflectedGridCollisions C, q (reflectedGridSwap x) = q x)
    (hfixed : ∀ x ∈ reflectedGridCollisions C, x.1 = x.2 → Even (q x)) :
    Even (reflectedGridWeightedCharge C q) := by
  unfold reflectedGridWeightedCharge
  let p : ℕ × ℕ → Prop := fun x => x.1 = x.2
  have hdiag : Even (∑ x ∈ (reflectedGridCollisions C).filter p, q x) := by
    rw [even_iff_two_dvd]
    refine Finset.dvd_sum (s := (reflectedGridCollisions C).filter p) (f := q) (a := 2) ?_
    intro x hx
    rw [Finset.mem_filter] at hx
    exact (hfixed x hx.1 hx.2).two_dvd
  have hnon : Even (∑ x ∈ (reflectedGridCollisions C).filter (fun x => ¬ p x), q x) := by
    apply even_sum_of_fpf_involution
      ((reflectedGridCollisions C).filter fun x : ℕ × ℕ => ¬ p x)
      (fun x : ℕ × ℕ => reflectedGridSwap x) q
    · intro x hx
      rw [Finset.mem_filter] at hx ⊢
      refine ⟨reflectedGridSwap_mem hx.1, ?_⟩
      intro h
      apply hx.2
      simpa [p, reflectedGridSwap] using h.symm
    · intro x hx
      exact reflectedGridSwap_involutive x
    · intro x hx hfix
      rw [Finset.mem_filter] at hx
      have h21 : x.2 = x.1 := congrArg Prod.fst hfix
      exact hx.2 h21.symm
    · intro x hx
      rw [Finset.mem_filter] at hx
      exact hsym x hx.1
  have hsplit := Finset.sum_filter_add_sum_filter_not (reflectedGridCollisions C) p q
  rw [← hsplit]
  exact hdiag.add hnon

/-- The weighted reflected grid charge is invisible to the level-two deck reduction under
the same reflection-invariant/even-fixed hypotheses. -/
theorem reflectedGridWeightedCharge_deckRed_two_eq_one_of_swap_invariant_even_fixed {C : ℕ}
    {q : ℕ × ℕ → ℕ}
    (hsym : ∀ x ∈ reflectedGridCollisions C, q (reflectedGridSwap x) = q x)
    (hfixed : ∀ x ∈ reflectedGridCollisions C, x.1 = x.2 → Even (q x)) :
    deckRed 2 (↑(reflectedGridWeightedCharge C q)) = 1 := by
  rw [deckRed_two_eq_one_iff]
  exact_mod_cast reflectedGridWeightedCharge_even_of_swap_invariant_even_fixed hsym hfixed

/-- If the normalized height has no positive square fixed point, swap-invariance alone makes
the weighted reflected grid charge even. -/
theorem reflectedGridWeightedCharge_even_of_swap_invariant_no_fixed {C : ℕ}
    {q : ℕ × ℕ → ℕ}
    (hsym : ∀ x ∈ reflectedGridCollisions C, q (reflectedGridSwap x) = q x)
    (hnsq : ∀ n : ℕ, 0 < n → n * n ≠ C) :
    Even (reflectedGridWeightedCharge C q) := by
  apply reflectedGridWeightedCharge_even_of_swap_invariant_even_fixed hsym
  intro x hx hdiag
  rw [reflectedGridCollision_mem_iff] at hx
  have hsquare : x.1 * x.1 = C := by simpa [hdiag] using hx.1
  have hpos : 0 < x.1 := by
    by_contra hnot
    have hz : x.1 = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hz] at hsquare
    simp at hsquare
    exact hx.2 hsquare.symm
  exact False.elim (hnsq x.1 hpos hsquare)

/-- No positive square fixed point makes the weighted reflected grid charge deck-trivial at
level two. -/
theorem reflectedGridWeightedCharge_deckRed_two_eq_one_of_swap_invariant_no_fixed {C : ℕ}
    {q : ℕ × ℕ → ℕ}
    (hsym : ∀ x ∈ reflectedGridCollisions C, q (reflectedGridSwap x) = q x)
    (hnsq : ∀ n : ℕ, 0 < n → n * n ≠ C) :
    deckRed 2 (↑(reflectedGridWeightedCharge C q)) = 1 := by
  rw [deckRed_two_eq_one_iff]
  exact_mod_cast reflectedGridWeightedCharge_even_of_swap_invariant_no_fixed hsym hnsq

/-- If `C=r²`, it is enough to prove that the single square fixed-point charge is even. -/
theorem reflectedGridWeightedCharge_even_of_swap_invariant_square_fixed_even {C r : ℕ}
    {q : ℕ × ℕ → ℕ} (hrpos : 0 < r) (hr : r * r = C)
    (hsym : ∀ x ∈ reflectedGridCollisions C, q (reflectedGridSwap x) = q x)
    (hrfixed : Even (q (r, r))) :
    Even (reflectedGridWeightedCharge C q) := by
  apply reflectedGridWeightedCharge_even_of_swap_invariant_even_fixed hsym
  intro x hx hdiag
  have hsingle := reflectedGridCollisions_fixed_eq_singleton (C := C) hrpos hr
  have hxfilter : x ∈ (reflectedGridCollisions C).filter (fun y : ℕ × ℕ => y.1 = y.2) := by
    rw [Finset.mem_filter]
    exact ⟨hx, hdiag⟩
  rw [hsingle] at hxfilter
  rw [Finset.mem_singleton] at hxfilter
  rw [hxfilter]
  exact hrfixed

/-- Square fixed-point evenness also makes the weighted reflected grid charge deck-trivial at
level two. -/
theorem reflectedGridWeightedCharge_deckRed_two_eq_one_of_swap_invariant_square_fixed_even {C r : ℕ}
    {q : ℕ × ℕ → ℕ} (hrpos : 0 < r) (hr : r * r = C)
    (hsym : ∀ x ∈ reflectedGridCollisions C, q (reflectedGridSwap x) = q x)
    (hrfixed : Even (q (r, r))) :
    deckRed 2 (↑(reflectedGridWeightedCharge C q)) = 1 := by
  rw [deckRed_two_eq_one_iff]
  exact_mod_cast reflectedGridWeightedCharge_even_of_swap_invariant_square_fixed_even
    hrpos hr hsym hrfixed

end RHTower
