/-
# The two ξ deck charges are one object

The ladder rung carries a deck charge at a right-half ξ-zero in two encodings:

* the **additive** avatar `ladderCharge k ρ = ord_ρ(ξ) mod 2^k ∈ ℤ/2^k`, built on the
  abstract `wCharge`/`deckRed` calculus;
* the **multiplicative, geometric** avatar `xiDeckCharge k ρ = exp(2πi·ord_ρ(ξ)/2^k) ∈ μ_{2^k}`,
  built to *be* the deck class (monodromy) of actual `2^k`-th-root chart branches of ξ
  (`xiDeckCharge_eq_chart_deckClass`).

They are the same object.  `xiDeckCharge` is the abstract multiplicative deck value
`deckRed` evaluated at ξ's vanishing order, hence the deck character of the additive
`ladderCharge`, and its triviality is the additive charge's vanishing.  So the algebraic
charge calculus (conservation, reflection-depth invisibility) and the geometric monodromy
realization (chart-root deck class, the argument-principle-free ladder) are two faces of
one `μ_{2^k}`-valued observable on the ξ-divisor.
-/
import GaloisForLFunctions.RHTower.XiDeckCharge
import GaloisForLFunctions.RHTower.DeckChargeLadder
import GaloisForLFunctions.RHTower.CarrierDeckCharge

namespace RHTower

open Complex

/-- The geometric charge is the abstract multiplicative deck value at ξ's order. -/
theorem xiDeckCharge_eq_deckRed (k : ℕ) (ρ : ℂ) :
    xiDeckCharge k ρ = deckRed (2 ^ k) ((analyticOrderAt xi ρ).toNat : ℤ) := by
  unfold xiDeckCharge deckRed
  rw [Int.cast_natCast]

/-- **ξ's charge is the general carrier charge at `f = ξ`.**  Everything in `XiDeckCharge`
is the `f = ξ` instance of `carrierCharge`; the ξ-specific work adds only the geometric
realization (chart-root deck class) and the connection to mathlib's `RiemannHypothesis`. -/
theorem xiDeckCharge_eq_carrierCharge (k : ℕ) (ρ : ℂ) :
    xiDeckCharge k ρ = carrierCharge xi k ρ := by
  rw [xiDeckCharge_eq_deckRed]
  rfl

/-- The geometric charge is the deck character of the additive ladder charge: the two
avatars agree on ξ's divisor. -/
theorem xiDeckCharge_eq_deckChar_ladderCharge (k : ℕ) (ρ : ℂ) :
    xiDeckCharge k ρ = deckChar (2 ^ k) (ladderCharge k ρ) := by
  haveI : NeZero (2 ^ k) := ⟨pow_ne_zero k (by norm_num)⟩
  rw [xiDeckCharge_eq_deckRed, ladderCharge, deckChar_wCharge]

/-- **The two vanishing criteria coincide.**  The geometric charge is trivial (`= 1`,
a global chart root glues) exactly when the additive charge vanishes (`= 0`, divisibility):
the two agents' rung conditions are one condition. -/
theorem xiDeckCharge_eq_one_iff_ladderCharge_zero (k : ℕ) (ρ : ℂ) :
    xiDeckCharge k ρ = 1 ↔ ladderCharge k ρ = 0 := by
  haveI : NeZero (2 ^ k) := ⟨pow_ne_zero k (by norm_num)⟩
  rw [xiDeckCharge_eq_deckRed, ladderCharge, wCharge_eq_zero_iff_deckRed_eq_one]

/-- Rung `k` read through either avatar is the same statement. -/
theorem rhLadder_iff_xiDeckCharge_one_iff_ladderCharge_zero (k : ℕ) :
    (∀ ρ ∈ rightHalf, xi ρ = 0 → xiDeckCharge k ρ = 1) ↔
      (∀ ρ ∈ rightHalf, xi ρ = 0 → ladderCharge k ρ = 0) :=
  forall₃_congr fun ρ _ _ => xiDeckCharge_eq_one_iff_ladderCharge_zero k ρ

end RHTower
