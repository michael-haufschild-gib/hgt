import GaloisForLFunctions.RHTower.UPlaneWinding
import GaloisForLFunctions.RHTower.DeckChargeBridge

/-!
# Xi-descent all-rung local-loop deck-charge universality

At every dyadic rung, Xi's local analytic carrier charge, the descended carrier charge, and the
deck character of every sufficiently small descended loop are one observable. This upgrades the
existing rung-one descent transport and integer winding comparison to a complete all-rung triangle.
-/

open Complex Set

namespace RHTower

/-- Descent preserves the local carrier charge at every dyadic rung. -/
theorem carrierCharge_xiDescent_center_sq_allRungs {ρ : ℂ} (hρ : ρ ∈ rightHalf)
    (k : ℕ) :
    carrierCharge xiDescent k ((ρ - (1 / 2 : ℂ)) ^ 2) = carrierCharge xi k ρ := by
  unfold carrierCharge
  rw [analyticOrderAt_xiDescent_center_sq hρ]

/-- **Xi-descent all-rung local-loop deck-charge universality law.** Around every right-half point,
all sufficiently small circles about its descended image have a loop charge whose multiplicative
deck character equals both the descended carrier charge and Xi's original carrier charge, at every
dyadic rung. -/
theorem deckChar_loopCharge_xiDescent_center_sq {ρ : ℂ} (hρ : ρ ∈ rightHalf)
    (k : ℕ) :
    ∃ R₀ > 0, ∀ r : ℝ, 0 < r → r < R₀ →
      deckChar (2 ^ k)
          (loopCharge k
            (fun θ => xiDescent ((ρ - (1 / 2 : ℂ)) ^ 2 +
              (r : ℂ) * exp (I * (θ : ℂ)))) 0 (2 * Real.pi)) =
        carrierCharge xiDescent k ((ρ - (1 / 2 : ℂ)) ^ 2) ∧
      deckChar (2 ^ k)
          (loopCharge k
            (fun θ => xiDescent ((ρ - (1 / 2 : ℂ)) ^ 2 +
              (r : ℂ) * exp (I * (θ : ℂ)))) 0 (2 * Real.pi)) =
        carrierCharge xi k ρ := by
  haveI : NeZero (2 ^ k) := ⟨pow_ne_zero k (by norm_num)⟩
  obtain ⟨R₀, hR₀, hwind⟩ := windingNumber_xiDescent_center_sq hρ
  refine ⟨R₀, hR₀, fun r hr hrR => ?_⟩
  have hloop :
      deckChar (2 ^ k)
          (loopCharge k
            (fun θ => xiDescent ((ρ - (1 / 2 : ℂ)) ^ 2 +
              (r : ℂ) * exp (I * (θ : ℂ)))) 0 (2 * Real.pi)) =
        carrierCharge xi k ρ := by
    rw [loopCharge, hwind r hr hrR, deckChar_wCharge]
    rfl
  exact ⟨hloop.trans (carrierCharge_xiDescent_center_sq_allRungs hρ k).symm, hloop⟩

end RHTower
