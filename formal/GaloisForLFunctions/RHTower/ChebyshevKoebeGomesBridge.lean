import GaloisForLFunctions.RHTower.ChebyshevKoebeFiniteAtoms

open Filter Topology
open scoped BigOperators

namespace RHTower

/-- The squared-weight atoms of `gomesChebyshevMomentTrace_eq_nodes` obey the
finite Koebe resolvent identity near the origin. -/
theorem gomesAtomicChebyshevKoebe_eventually
    (S : Finset ℝ) (w : ℝ → ℝ) :
    ∀ᶠ v in 𝓝 (0 : ℂ), v ≠ 0 →
      (∑ x ∈ S,
        ((w x ^ (2 : ℕ) : ℝ) : ℂ) * (x : ℂ) * (1 - v ^ (2 : ℕ)) /
          (1 - 2 * v * (1 - 2 * (x : ℂ)) + v ^ (2 : ℕ))) =
        (1 - v ^ (2 : ℕ)) / (4 * v) *
          ∑ x ∈ S,
            if (x : ℂ) = 0 then 0 else
              ((w x ^ (2 : ℕ) : ℝ) : ℂ) *
                (chebyshevTraceKoebeMap v /
                  (chebyshevTraceKoebeMap v - (-(27 / 4 : ℂ) / (x : ℂ)))) := by
  have h := finiteChebyshevCenteredRational_eq_koebe_eventually
    S (fun x : ℝ => ((w x ^ (2 : ℕ) : ℝ) : ℂ)) (fun x => (x : ℂ))
  filter_upwards [h] with v hv hv0
  exact hv hv0

end RHTower
