import GaloisForLFunctions.RHTower.UPlaneWindingCircle
import GaloisForLFunctions.RHTower.DeckChargeBridge
import GaloisForLFunctions.RHTower.XiDescentAllRungLocalLoopDeckChargeUniversalityLaw

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

/-- **Xi-descent local/global complete deck-charge universality law.**  The all-rung local
small-loop triangle and the arbitrary-circle global law form one certificate.  One exact enclosed
zero census simultaneously carries additive factorization, multiplicative factorization, and both
aggregate-cancellation classifications. -/
theorem xiDescent_localGlobalCompleteDeckChargeUniversality :
    (∀ {ρ : ℂ}, ρ ∈ rightHalf → ∀ k : ℕ,
      ∃ R₀ > 0, ∀ r : ℝ, 0 < r → r < R₀ →
        deckChar (2 ^ k)
            (loopCharge k
              (fun θ => xiDescent ((ρ - (1 / 2 : ℂ)) ^ (2 : ℕ) +
                (r : ℂ) * exp (I * (θ : ℂ)))) 0 (2 * Real.pi)) =
          carrierCharge xiDescent k ((ρ - (1 / 2 : ℂ)) ^ (2 : ℕ)) ∧
        deckChar (2 ^ k)
            (loopCharge k
              (fun θ => xiDescent ((ρ - (1 / 2 : ℂ)) ^ (2 : ℕ) +
                (r : ℂ) * exp (I * (θ : ℂ)))) 0 (2 * Real.pi)) =
          carrierCharge xi k ρ) ∧
    ∀ (c : ℂ) {r : ℝ}, 0 < r →
      (∀ z, ‖z - c‖ = r → xiDescent z ≠ 0) → ∀ k : ℕ,
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
          ∏ w ∈ t, carrierCharge xiDescent k w ∧
        (loopCharge k
            (fun θ => xiDescent (c + ↑r * exp (I * ↑θ)))
            0 (2 * Real.pi) = 0 ↔
          ((2 ^ k : ℕ) : ℤ) ∣
            ∑ w ∈ t, ((analyticOrderAt xiDescent w).toNat : ℤ)) ∧
        ((∏ w ∈ t, carrierCharge xiDescent k w) = 1 ↔
          ((2 ^ k : ℕ) : ℤ) ∣
            ∑ w ∈ t, ((analyticOrderAt xiDescent w).toNat : ℤ)) := by
  refine ⟨?_, ?_⟩
  · intro ρ hρ k
    exact deckChar_loopCharge_xiDescent_center_sq hρ k
  · intro c r hr havoid k
    haveI : NeZero (2 ^ k) := ⟨pow_ne_zero k (by norm_num)⟩
    obtain ⟨t, ht, hsum, hproduct⟩ :=
      xiDescent_circle_localGlobalDeckCharge c hr havoid k
    have hadd :
        loopCharge k
            (fun θ => xiDescent (c + ↑r * exp (I * ↑θ)))
            0 (2 * Real.pi) = 0 ↔
          ((2 ^ k : ℕ) : ℤ) ∣
            ∑ w ∈ t, ((analyticOrderAt xiDescent w).toNat : ℤ) := by
      rw [hsum, ← wCharge_sum, wCharge_eq_zero_iff]
    have hmul :
        (∏ w ∈ t, carrierCharge xiDescent k w) = 1 ↔
          ((2 ^ k : ℕ) : ℤ) ∣
            ∑ w ∈ t, ((analyticOrderAt xiDescent w).toNat : ℤ) := by
      rw [← hproduct]
      constructor
      · intro h
        have hzero :
            loopCharge k
                (fun θ => xiDescent (c + ↑r * exp (I * ↑θ)))
                0 (2 * Real.pi) = 0 := by
          apply deckChar_injective
          simpa using h
        exact hadd.mp hzero
      · intro hdvd
        rw [hadd.mpr hdvd, deckChar_zero]
    exact ⟨t, ht, hsum, hproduct, hadd, hmul⟩

end

end RHTower
