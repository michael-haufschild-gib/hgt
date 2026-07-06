/-
Analytic local-order charge for reflected saddle/grid collisions.

`ReflectedGridCharge` reduces weighted parity to two inputs: factor-swap invariance of
the weight, and even weight at fixed diagonal collisions.  This file supplies the fixed
diagonal input when the weight is an analytic vanishing order.  At a diagonal fixed point,
reflection symmetry of the local germ forces the analytic order to be even by
`analyticOrderAt_even_of_reflection`.
-/
import GaloisForLFunctions.RHTower.ReflectedGridCharge

open Complex Real
open scoped BigOperators

namespace RHTower

/-- The reflected grid charge whose weight is the local analytic order of a germ attached to
each grid collision. -/
noncomputable def reflectedGridAnalyticCharge (C : ℕ) (F : ℕ × ℕ → ℂ → ℂ)
    (center : ℕ × ℕ → ℂ) : ℕ :=
  reflectedGridWeightedCharge C fun x => (analyticOrderAt (F x) (center x)).toNat

/-- If analytic local orders are invariant under the factor-swap reflection and every fixed
diagonal germ is reflection-symmetric with finite order, then the reflected analytic charge is
even. -/
theorem reflectedGridAnalyticCharge_even_of_swap_order_even_fixed {C : ℕ}
    {F : ℕ × ℕ → ℂ → ℂ} {center : ℕ × ℕ → ℂ}
    (hswap : ∀ x ∈ reflectedGridCollisions C,
      (analyticOrderAt (F (reflectedGridSwap x)) (center (reflectedGridSwap x))).toNat =
        (analyticOrderAt (F x) (center x)).toNat)
    (hfixed_an : ∀ x ∈ reflectedGridCollisions C, x.1 = x.2 →
      AnalyticOnNhd ℂ (F x) Set.univ)
    (hfixed_sym : ∀ x ∈ reflectedGridCollisions C, x.1 = x.2 →
      ∀ s, F x (2 * center x - s) = F x s)
    (hfixed_finite : ∀ x ∈ reflectedGridCollisions C, x.1 = x.2 →
      analyticOrderAt (F x) (center x) ≠ ⊤) :
    Even (reflectedGridAnalyticCharge C F center) := by
  unfold reflectedGridAnalyticCharge
  apply reflectedGridWeightedCharge_even_of_swap_invariant_even_fixed
  · intro x hx
    exact hswap x hx
  · intro x hx hdiag
    exact analyticOrderAt_even_of_reflection (hfixed_an x hx hdiag)
      (hfixed_sym x hx hdiag) (hfixed_finite x hx hdiag)

/-- Deck form of `reflectedGridAnalyticCharge_even_of_swap_order_even_fixed`. -/
theorem reflectedGridAnalyticCharge_deckRed_two_eq_one_of_swap_order_even_fixed {C : ℕ}
    {F : ℕ × ℕ → ℂ → ℂ} {center : ℕ × ℕ → ℂ}
    (hswap : ∀ x ∈ reflectedGridCollisions C,
      (analyticOrderAt (F (reflectedGridSwap x)) (center (reflectedGridSwap x))).toNat =
        (analyticOrderAt (F x) (center x)).toNat)
    (hfixed_an : ∀ x ∈ reflectedGridCollisions C, x.1 = x.2 →
      AnalyticOnNhd ℂ (F x) Set.univ)
    (hfixed_sym : ∀ x ∈ reflectedGridCollisions C, x.1 = x.2 →
      ∀ s, F x (2 * center x - s) = F x s)
    (hfixed_finite : ∀ x ∈ reflectedGridCollisions C, x.1 = x.2 →
      analyticOrderAt (F x) (center x) ≠ ⊤) :
    deckRed 2 (↑(reflectedGridAnalyticCharge C F center)) = 1 := by
  rw [deckRed_two_eq_one_iff]
  exact_mod_cast reflectedGridAnalyticCharge_even_of_swap_order_even_fixed
    hswap hfixed_an hfixed_sym hfixed_finite

/-- In the square case `C=r²`, it is enough to check reflection symmetry of the single
diagonal germ `(r,r)`. -/
theorem reflectedGridAnalyticCharge_even_of_swap_order_square_reflection {C r : ℕ}
    {F : ℕ × ℕ → ℂ → ℂ} {center : ℕ × ℕ → ℂ}
    (hrpos : 0 < r) (hr : r * r = C)
    (hswap : ∀ x ∈ reflectedGridCollisions C,
      (analyticOrderAt (F (reflectedGridSwap x)) (center (reflectedGridSwap x))).toNat =
        (analyticOrderAt (F x) (center x)).toNat)
    (hfixed_an : AnalyticOnNhd ℂ (F (r, r)) Set.univ)
    (hfixed_sym : ∀ s, F (r, r) (2 * center (r, r) - s) = F (r, r) s)
    (hfixed_finite : analyticOrderAt (F (r, r)) (center (r, r)) ≠ ⊤) :
    Even (reflectedGridAnalyticCharge C F center) := by
  unfold reflectedGridAnalyticCharge
  apply reflectedGridWeightedCharge_even_of_swap_invariant_square_fixed_even hrpos hr
  · intro x hx
    exact hswap x hx
  · exact analyticOrderAt_even_of_reflection hfixed_an hfixed_sym hfixed_finite

/-- Deck form of the square fixed-germ reflection theorem. -/
theorem reflectedGridAnalyticCharge_deckRed_two_eq_one_of_swap_order_square_reflection {C r : ℕ}
    {F : ℕ × ℕ → ℂ → ℂ} {center : ℕ × ℕ → ℂ}
    (hrpos : 0 < r) (hr : r * r = C)
    (hswap : ∀ x ∈ reflectedGridCollisions C,
      (analyticOrderAt (F (reflectedGridSwap x)) (center (reflectedGridSwap x))).toNat =
        (analyticOrderAt (F x) (center x)).toNat)
    (hfixed_an : AnalyticOnNhd ℂ (F (r, r)) Set.univ)
    (hfixed_sym : ∀ s, F (r, r) (2 * center (r, r) - s) = F (r, r) s)
    (hfixed_finite : analyticOrderAt (F (r, r)) (center (r, r)) ≠ ⊤) :
    deckRed 2 (↑(reflectedGridAnalyticCharge C F center)) = 1 := by
  rw [deckRed_two_eq_one_iff]
  exact_mod_cast reflectedGridAnalyticCharge_even_of_swap_order_square_reflection
    hrpos hr hswap hfixed_an hfixed_sym hfixed_finite

end RHTower
