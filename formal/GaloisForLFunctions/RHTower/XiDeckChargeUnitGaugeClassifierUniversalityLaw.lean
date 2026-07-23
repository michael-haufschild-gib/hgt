import GaloisForLFunctions.RHTower.DeckChargeInvariant

/-!
# Xi deck-charge unit-gauge classifier universality

The full Xi charge tower remains an RH classifier after multiplication by any analytic unit on the
right half-plane. The same divisor invariant is nevertheless blind to differential-algebraic class.
-/

open Complex

namespace RHTower

/-- RH is invariantly characterized by the deck-charge tower of every analytic-unit twist of Xi. -/
theorem riemannHypothesis_iff_unitTwistedXiDeckCharge
    (u : ℂ → ℂ)
    (hu : ∀ ρ ∈ rightHalf, AnalyticAt ℂ u ρ)
    (hu0 : ∀ ρ ∈ rightHalf, u ρ ≠ 0) :
    RiemannHypothesis ↔
      ∀ k, ∀ ρ ∈ rightHalf, (xi * u) ρ = 0 → deckCharge (xi * u) k ρ = 1 := by
  constructor
  · intro hRH k ρ hρ hzero
    change xi ρ * u ρ = 0 at hzero
    have hxzero : xi ρ = 0 := (mul_eq_zero.mp hzero).resolve_right (hu0 ρ hρ)
    rw [deckCharge_mul_unit k (xi_differentiable.analyticAt ρ) (hu ρ hρ) (hu0 ρ hρ)]
    rw [← xiDeckCharge_eq_deckCharge]
    exact (rh_iff_xiDeckCharge.mp hRH) k ρ hρ hxzero
  · intro htwist
    apply rh_iff_xiDeckCharge.mpr
    intro k ρ hρ hzero
    rw [xiDeckCharge_eq_deckCharge]
    rw [← deckCharge_mul_unit k (xi_differentiable.analyticAt ρ) (hu ρ hρ) (hu0 ρ hρ)]
    exact htwist k ρ hρ (by simp [hzero])

/-- **Xi deck-charge unit-gauge classifier universality law.** The Xi charge tower is an RH-complete
classifier throughout the full analytic-unit gauge orbit, but the same invariant cannot distinguish
a nowhere-zero hypertranscendental carrier from the differentially algebraic constant one. -/
theorem xiDeckCharge_unitGaugeRHClassifier_and_classBlindness
    (u : ℂ → ℂ)
    (hu : ∀ ρ ∈ rightHalf, AnalyticAt ℂ u ρ)
    (hu0 : ∀ ρ ∈ rightHalf, u ρ ≠ 0)
    (h : ℂ → ℂ) (hne : ∀ ρ, h ρ ≠ 0)
    (hHT : GaloisForLFunctions.Hypertranscendental h) :
    (RiemannHypothesis ↔
      ∀ k, ∀ ρ ∈ rightHalf, (xi * u) ρ = 0 → deckCharge (xi * u) k ρ = 1) ∧
      GaloisForLFunctions.DifferentiallyAlgebraic (fun _ : ℂ => (1 : ℂ)) ∧
      GaloisForLFunctions.Hypertranscendental h ∧
      ∀ k ρ, deckCharge h k ρ = deckCharge (fun _ : ℂ => (1 : ℂ)) k ρ := by
  refine ⟨riemannHypothesis_iff_unitTwistedXiDeckCharge u hu hu0, ?_⟩
  exact deckCharge_blind_to_class h hne hHT

end RHTower
