import GaloisForLFunctions.RHTower.UPlaneWindingCircle
import GaloisForLFunctions.RHTower.DeckChargeBridge

/-!
# Xi-descent circle aggregate-cancellation universality

For an arbitrary zero-avoiding circle, local dyadic carrier charges can cancel even when individual
enclosed zeros have nontrivial charge.  The cancellation is exact: additive loop-charge vanishing
and multiplicative local-charge-product triviality are both equivalent to divisibility of the total
enclosed Xi-descent multiplicity by the dyadic sheet number.
-/

open Complex Set Metric Filter

namespace RHTower

noncomputable section

/-- **Xi-descent circle aggregate-cancellation universality law.** Every zero-avoiding circle has
an exact finite enclosed-zero census for which additive global-charge vanishing and multiplicative
local-charge cancellation are simultaneously classified by divisibility of total enclosed order. -/
theorem xiDescent_circle_aggregateCancellation
    (c : ℂ) {r : ℝ} (hr : 0 < r)
    (havoid : ∀ z, ‖z - c‖ = r → xiDescent z ≠ 0) (k : ℕ) :
    ∃ t : Finset ℂ,
      (∀ w, w ∈ t ↔ ‖w - c‖ < r ∧ xiDescent w = 0) ∧
      (loopCharge k
          (fun θ => xiDescent (c + ↑r * exp (I * ↑θ)))
          0 (2 * Real.pi) = 0 ↔
        ((2 ^ k : ℕ) : ℤ) ∣
          ∑ w ∈ t, ((analyticOrderAt xiDescent w).toNat : ℤ)) ∧
      ((∏ w ∈ t, carrierCharge xiDescent k w) = 1 ↔
        ((2 ^ k : ℕ) : ℤ) ∣
          ∑ w ∈ t, ((analyticOrderAt xiDescent w).toNat : ℤ)) := by
  haveI : NeZero (2 ^ k) := ⟨pow_ne_zero k (by norm_num)⟩
  obtain ⟨t, ht, hloop⟩ :=
    loopCharge_xiDescent_circle c hr havoid k
  have hdeck :
      deckChar (2 ^ k)
          (loopCharge k
            (fun θ => xiDescent (c + ↑r * exp (I * ↑θ)))
            0 (2 * Real.pi)) =
        ∏ w ∈ t, carrierCharge xiDescent k w := by
    rw [hloop, wCharge_sum, deckChar_sum]
    simp_rw [deckChar_wCharge]
    rfl
  refine ⟨t, ht, ?_, ?_⟩
  · rw [hloop, wCharge_eq_zero_iff]
  · rw [← hdeck]
    constructor
    · intro h
      have hzero :
          loopCharge k
              (fun θ => xiDescent (c + ↑r * exp (I * ↑θ)))
              0 (2 * Real.pi) = 0 := by
        apply deckChar_injective
        simpa using h
      rw [hloop, wCharge_eq_zero_iff] at hzero
      exact hzero
    · intro hdvd
      have hzero :
          loopCharge k
              (fun θ => xiDescent (c + ↑r * exp (I * ↑θ)))
              0 (2 * Real.pi) = 0 := by
        rw [hloop, wCharge_eq_zero_iff]
        exact hdvd
      rw [hzero, deckChar_zero]

end

end RHTower
