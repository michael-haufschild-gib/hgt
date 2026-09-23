import GaloisForLFunctions.RHTower.XiMassConjugatedHolomorphy

/-!
# The caustic iterate family

The caustic operator acting on the conjugated carrier is

`L f = c₀·f + c₁·f′ − f″`,   `c₀ = symbol + a(1/Z − w²/Z³)`,  `c₁ = 2a·w/Z`,

and its iterates are defined by the obvious recursion.  Each stays holomorphic on the region: a
function holomorphic on an open subset of `ℂ` is analytic there, so all of its derivatives are
holomorphic there too, and the coefficients are holomorphic by construction.

Holomorphy is exactly the hypothesis the Cauchy iteration consumes, and this is where the passage
from "the profile is an explicit Bessel state" to "the profile is bounded by the symbol to a power"
is made.
-/

open Complex Metric

namespace RHTower

noncomputable section

/-- The caustic iterate family on the conjugated carrier. -/
def xiCausticIterate (a : ℝ) (τ : ℂ) : ℕ → ℂ → ℂ
  | 0 => xiMassConjugatedCarrier a τ
  | k + 1 => fun ζ => xiCausticCoeffZero a τ ζ * xiCausticIterate a τ k ζ
      + xiCausticCoeffOne a τ ζ * deriv (xiCausticIterate a τ k) ζ
      - deriv (deriv (xiCausticIterate a τ k)) ζ

theorem xiCausticIterate_zero (a : ℝ) (τ : ℂ) :
    xiCausticIterate a τ 0 = xiMassConjugatedCarrier a τ := rfl

theorem xiCausticIterate_succ (a : ℝ) (τ : ℂ) (k : ℕ) (ζ : ℂ) :
    xiCausticIterate a τ (k + 1) ζ
      = xiCausticCoeffZero a τ ζ * xiCausticIterate a τ k ζ
        + xiCausticCoeffOne a τ ζ * deriv (xiCausticIterate a τ k) ζ
        - deriv (deriv (xiCausticIterate a τ k)) ζ := rfl

/-- **Every iterate is holomorphic on the region.** -/
theorem differentiableOn_xiCausticIterate {a : ℝ} (ha : 0 < a) (τ : ℂ) (k : ℕ) :
    DifferentiableOn ℂ (xiCausticIterate a τ k) (xiMassHeightRegion τ) := by
  induction k with
  | zero => exact differentiableOn_xiMassConjugatedCarrier ha τ
  | succ k ih =>
      have hopen := isOpen_xiMassHeightRegion τ
      have hana : AnalyticOnNhd ℂ (xiCausticIterate a τ k) (xiMassHeightRegion τ) :=
        ih.analyticOnNhd hopen
      have hd1 : DifferentiableOn ℂ (deriv (xiCausticIterate a τ k)) (xiMassHeightRegion τ) :=
        hana.deriv.differentiableOn
      have hd2 : DifferentiableOn ℂ (deriv (deriv (xiCausticIterate a τ k)))
          (xiMassHeightRegion τ) :=
        hana.deriv.deriv.differentiableOn
      have hc0 : DifferentiableOn ℂ (xiCausticCoeffZero a τ) (xiMassHeightRegion τ) :=
        fun _ hw => (differentiableAt_xiCausticCoeffZero hw).differentiableWithinAt
      have hc1 : DifferentiableOn ℂ (xiCausticCoeffOne a τ) (xiMassHeightRegion τ) :=
        fun _ hw => (differentiableAt_xiCausticCoeffOne hw).differentiableWithinAt
      exact ((hc0.mul ih).add (hc1.mul hd1)).sub hd2

/-- **A closed disc inside the region gives the Cauchy hypothesis.** -/
theorem diffContOnCl_xiCausticIterate {a : ℝ} (ha : 0 < a) {τ ζ : ℂ} {δ : ℝ} (k : ℕ)
    (hsub : closedBall ζ δ ⊆ xiMassHeightRegion τ) :
    DiffContOnCl ℂ (xiCausticIterate a τ k) (ball ζ δ) := by
  have hd := differentiableOn_xiCausticIterate ha τ k
  refine ⟨hd.mono (le_trans ball_subset_closedBall hsub), ?_⟩
  exact hd.continuousOn.mono (le_trans closure_ball_subset_closedBall hsub)

/-- **The Cauchy iteration for the caustic operator.**  The value of the `n`-th caustic iterate at
the centre is bounded by the base sup norm times the `n`-th power of the step factor. -/
theorem norm_xiCausticIterate_le {a : ℝ} (ha : 0 < a) {τ z₀ : ℂ} {δ M ε γ : ℝ} (n : ℕ)
    (hδ : 0 < δ) (hM : 0 ≤ M)
    (hsub : ∀ ζ : ℂ, ‖ζ - z₀‖ ≤ (n : ℝ) * δ → closedBall ζ δ ⊆ xiMassHeightRegion τ)
    (hc₀ : ∀ ζ : ℂ, ‖ζ - z₀‖ ≤ (n : ℝ) * δ → ‖xiCausticCoeffZero a τ ζ‖ ≤ ε)
    (hc₁ : ∀ ζ : ℂ, ‖ζ - z₀‖ ≤ (n : ℝ) * δ → ‖xiCausticCoeffOne a τ ζ‖ ≤ γ)
    (hbase : ∀ ζ : ℂ, ‖ζ - z₀‖ ≤ (n : ℝ) * δ → ‖xiMassConjugatedCarrier a τ ζ‖ ≤ M) :
    ‖xiCausticIterate a τ n z₀‖ ≤ M * (ε + γ / δ + 2 / δ ^ (2 : ℕ)) ^ n :=
  HTGeometry.norm_secondOrderIterate_le n hδ hM
    (fun k ζ hζ => diffContOnCl_xiCausticIterate ha k (hsub ζ hζ))
    (fun k ζ => xiCausticIterate_succ a τ k ζ) hc₀ hc₁ hbase

end

end RHTower
