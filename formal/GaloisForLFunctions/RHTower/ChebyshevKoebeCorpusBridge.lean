import GaloisForLFunctions.RHTower.ChebyshevKoebeFiniteAtoms
import GaloisForLFunctions.RHTower.ChebyshevMomentCorpusBridge

open Filter Topology
open scoped BigOperators

namespace RHTower

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
