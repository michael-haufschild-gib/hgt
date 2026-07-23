import GaloisForLFunctions.RHTower.UPlaneWindingCircle
import GaloisForLFunctions.RHTower.DeckChargeBridge

/-!
# Xi-descent circle local/global deck-charge universality

Every zero-avoiding circle has an exact finite Xi-descent zero census. At each dyadic rung, its
global additive loop charge is the sum of the enclosed local charges, and its multiplicative deck
character is the product of the enclosed local carrier charges.
-/

open Complex Set Metric Filter

namespace RHTower

noncomputable section

/-- **Xi-descent circle local/global deck-charge universality law.** For every zero-avoiding
circle and dyadic rung, the unconditional enclosed-zero census simultaneously gives the additive
local-charge sum and its multiplicative local-carrier-charge factorization. -/
theorem xiDescent_circle_localGlobalDeckCharge
    (c : ℂ) {r : ℝ} (hr : 0 < r)
    (havoid : ∀ z, ‖z - c‖ = r → xiDescent z ≠ 0) (k : ℕ) :
    ∃ t : Finset ℂ,
      (∀ w, w ∈ t ↔ ‖w - c‖ < r ∧ xiDescent w = 0) ∧
      loopCharge k
          (fun θ => xiDescent (c + ↑r * exp (I * ↑θ)))
          0 (2 * Real.pi) =
        ∑ w ∈ t,
          wCharge (2 ^ k) ((analyticOrderAt xiDescent w).toNat : ℤ) ∧
      deckChar (2 ^ k)
          (loopCharge k
            (fun θ => xiDescent (c + ↑r * exp (I * ↑θ)))
            0 (2 * Real.pi)) =
        ∏ w ∈ t, carrierCharge xiDescent k w := by
  haveI : NeZero (2 ^ k) := ⟨pow_ne_zero k (by norm_num)⟩
  obtain ⟨t, ht, hloop⟩ :=
    loopCharge_xiDescent_circle c hr havoid k
  refine ⟨t, ht, ?_, ?_⟩
  · rw [hloop, wCharge_sum]
  · rw [hloop, wCharge_sum, deckChar_sum]
    simp_rw [deckChar_wCharge]
    rfl

end

end RHTower
