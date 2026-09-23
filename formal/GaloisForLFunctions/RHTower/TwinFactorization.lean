import GaloisForLFunctions.RHTower.RHLadderTheory

/-!
# The twin-factorization reading of the base rung

The base rung demands an analytic square root of ξ on `Re s > ½`.  This file trades the square
for a strictly more flexible object: a **twin factorization** — two analytic factors on the
right half-plane whose pointwise product is ξ and whose vanishing orders agree at every
right-half point, while the factors themselves are free to differ.  A square root is the
diagonal twin (`a = d`); conversely equal orders force every right-half order of ξ to be a
doubled order, which is the base rung.  So `RHLadder 1` is exactly the existence of a twin
factorization.

The gain over the square-root form is where the freedom sits: the factors are constrained only
through their divisors on the open half-plane, so they may differ — as functions and in their
divisors — on the critical line, which is exactly where the odd part of ξ's divisor is expected
to live.  The rung thereby becomes a factorization statement with the line anomaly built into
the format: split ξ into two arithmetically given factors that share the off-line divisor
equally and disagree only on the seam.
-/

open Complex

namespace RHTower

/-- A twin factorization of ξ on the right half-plane: two analytic factors with pointwise
product ξ and equal vanishing orders at every right-half point.  The factors are otherwise
unconstrained — in particular they may differ on the critical line. -/
def TwinFactorization : Prop :=
  ∃ a d : ℂ → ℂ, AnalyticOnNhd ℂ a rightHalf ∧ AnalyticOnNhd ℂ d rightHalf ∧
    (∀ s ∈ rightHalf, a s * d s = xi s) ∧
    ∀ ρ ∈ rightHalf, analyticOrderAt a ρ = analyticOrderAt d ρ

/-- **The base rung is exactly the existence of a twin factorization.**  A square root is the
diagonal twin; equal orders double every right-half vanishing order of ξ. -/
theorem rhLadder_one_iff_twinFactorization : RHLadder 1 ↔ TwinFactorization := by
  constructor
  · intro h
    obtain ⟨g, hg, hgsq⟩ := rhLadder_one_iff_sqrt_rightHalf.mp h
    exact ⟨g, g, hg, hg, fun s hs => by rw [← hgsq s hs]; ring, fun ρ _ => rfl⟩
  · rintro ⟨a, d, ha, hd, hprod, hord⟩
    intro ρ hρ hzero
    have hev : xi =ᶠ[nhds ρ] (a * d) := by
      filter_upwards [isOpen_rightHalf.mem_nhds hρ] with s hs
      exact (hprod s hs).symm
    have h1 : analyticOrderAt xi ρ = analyticOrderAt a ρ + analyticOrderAt d ρ := by
      rw [analyticOrderAt_congr hev]
      exact analyticOrderAt_mul (ha ρ hρ) (hd ρ hρ)
    have h2 : ((2 ^ (1 : ℕ) : ℕ) : ℕ∞) = 2 := by norm_num
    rw [h1, ← hord ρ hρ, h2, ← two_mul]
    exact dvd_mul_right 2 _

/-- RH discharges the twin-factorization interface on the open right half-plane. -/
theorem twinFactorization_of_riemannHypothesis
    (hRH : RiemannHypothesis) : TwinFactorization :=
  rhLadder_one_iff_twinFactorization.1
    ((rh_iff_forall_ladder.1 hRH) 1)

end RHTower
