import GaloisForLFunctions.RHTower.ChebyshevKoebeFiniteAtoms
import GaloisForLFunctions.RHTower.ChebyshevMomentCorpusBridge

/-!
# Koebe resolvent form for arithmetic theta packets and finite sets of ξ zeros

This module specializes the finite Chebyshev-to-Koebe identity to two concrete node families.
For the centered arithmetic theta nodes of stage `k`, with unit weights and node `x`, and for a
finite set `S` of zeros `ρ` of `ξ`, with weight the divisor multiplicity and node the centered
reciprocal square `θ_ρ = -(ρ - 1/2)^(-2)`, the Chebyshev generating sum equals
`(1 - v²)/(4v)` times a Koebe resolvent sum with poles at `K(v) = -(27/4)/θ`, for all `v ≠ 0`
near `0`.

## Main results

- `thetaArithmeticChebyshevKoebe_eventually`: the identity for the stage-`k` arithmetic theta
  nodes.
- `xiFiniteChebyshevKoebe_eventually`: the identity for any finite set of ξ zeros with their
  multiplicities.

## Hypotheses

Unconditional; the finite set `S` is arbitrary and nothing is assumed about the location of the
zeros.
-/

open Filter Topology
open scoped BigOperators

namespace RHTower

/-- For the stage-`k` centered arithmetic theta nodes `x`, and all `v ≠ 0` near `0`,
`∑ x(1 - v²)/(1 - 2v(1 - 2x) + v²) = (1 - v²)/(4v) · ∑_{x ≠ 0} K(v)/(K(v) + (27/4)/x)`. -/
theorem thetaArithmeticChebyshevKoebe_eventually (k : ℕ) :
    ∀ᶠ v in 𝓝 (0 : ℂ), v ≠ 0 →
      (∑ x ∈ thetaArithmeticCenteredNodes k,
        (x : ℂ) * (1 - v ^ (2 : ℕ)) /
          (1 - 2 * v * (1 - 2 * (x : ℂ)) + v ^ (2 : ℕ))) =
        (1 - v ^ (2 : ℕ)) / (4 * v) *
          ∑ x ∈ thetaArithmeticCenteredNodes k,
            if (x : ℂ) = 0 then 0 else
              chebyshevTraceKoebeMap v /
                (chebyshevTraceKoebeMap v - (-(27 / 4 : ℂ) / (x : ℂ))) := by
  have h := finiteChebyshevCenteredRational_eq_koebe_eventually
    (thetaArithmeticCenteredNodes k) (fun _ : ℝ => (1 : ℂ)) (fun x => (x : ℂ))
  filter_upwards [h] with v hv hv0
  simpa only [finiteChebyshevCenteredRational, finiteKoebeResolvent,
    one_mul] using hv hv0

/-- For any finite set `S` of ξ zeros, weighted by multiplicity with nodes `θ_ρ = -(ρ - 1/2)^(-2)`,
the Chebyshev generating sum equals `(1 - v²)/(4v)` times the Koebe resolvent sum, for `v ≠ 0` near `0`. -/
theorem xiFiniteChebyshevKoebe_eventually (S : Finset XiDivisorSupport) :
    ∀ᶠ v in 𝓝 (0 : ℂ), v ≠ 0 →
      (∑ ρ ∈ S,
        (((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) : ℂ) *
          xiCentralReciprocalSquare (ρ : ℂ) * (1 - v ^ (2 : ℕ)) /
            (1 - 2 * v * (1 - 2 * xiCentralReciprocalSquare (ρ : ℂ)) +
              v ^ (2 : ℕ))) =
        (1 - v ^ (2 : ℕ)) / (4 * v) *
          ∑ ρ ∈ S,
            (((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) : ℂ) *
              (chebyshevTraceKoebeMap v /
                (chebyshevTraceKoebeMap v -
                  (-(27 / 4 : ℂ) / xiCentralReciprocalSquare (ρ : ℂ)))) := by
  let w : XiDivisorSupport → ℂ := fun ρ =>
    (((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) : ℂ)
  let θ : XiDivisorSupport → ℂ := fun ρ => xiCentralReciprocalSquare (ρ : ℂ)
  have h := finiteChebyshevCenteredRational_eq_koebe_eventually S w θ
  filter_upwards [h] with v hv hv0
  have hres : finiteKoebeResolvent S w θ v =
      ∑ ρ ∈ S, w ρ *
        (chebyshevTraceKoebeMap v /
          (chebyshevTraceKoebeMap v - (-(27 / 4 : ℂ) / θ ρ))) := by
    classical
    rw [finiteKoebeResolvent]
    apply Finset.sum_congr rfl
    intro ρ hρ
    rw [if_neg (xiCentralReciprocalSquare_ne_zero ρ)]
  rw [hres] at hv
  simpa only [finiteChebyshevCenteredRational, w, θ] using hv hv0

end RHTower
