import GaloisForLFunctions.HTGeometry.PhaseRankDimensionBound
import GaloisForLFunctions.HTGeometry.HullJetEmbedding

/-!
# The jet embedding bounds the phase rank

A continuous injective jet-sample map of the phase carrier into `ℂ^N` is a closed embedding into a
real space of dimension `2N`, so the frequency group of the underlying almost periodic function has
rational rank at most `2N`.

This is the last link of the finite-phase chain: an algebraic differential equation supplies the
finite jet sample, the jet sample embeds the carrier in finite dimension, and the dimension bounds
the number of rationally independent frequencies.
-/

open Topology

open scoped BoundedContinuousFunction

namespace GaloisForLFunctions

variable {f : ℝ →ᵇ ℂ}

/-- **The frequency rank is at most twice the number of jet coordinates.** -/
theorem rank_bohrHullFrequencies_le_two_mul (hf : UniformContinuous (fun x => f x))
    (htb : HasTotallyBoundedOrbit (fun x => f x))
    [MeasurableSpace (BohrHull f)] [BorelSpace (BohrHull f)] {N : ℕ}
    {J : BohrHull f → (Fin N → ℂ)} (hJcont : Continuous J) (hJinj : Function.Injective J) :
    Module.rank ℤ (bohrHullFrequencies f) ≤ ((2 * N : ℕ) : Cardinal) := by
  have hdim : Module.finrank ℝ (Fin N → ℂ) = 2 * N := by
    simp [Module.finrank_pi_fintype, Complex.finrank_real_complex]
    ring
  have h := rank_bohrHullFrequencies_le hf htb hJcont hJinj
  rwa [hdim] at h

/-- The same bound stated through the closed embedding of the carrier. -/
theorem rank_bohrHullFrequencies_le_of_isClosedEmbedding (hf : UniformContinuous (fun x => f x))
    (htb : HasTotallyBoundedOrbit (fun x => f x))
    [MeasurableSpace (BohrHull f)] [BorelSpace (BohrHull f)] {N : ℕ}
    {J : BohrHull f → (Fin N → ℂ)} (hJ : IsClosedEmbedding J) :
    Module.rank ℤ (bohrHullFrequencies f) ≤ ((2 * N : ℕ) : Cardinal) :=
  rank_bohrHullFrequencies_le_two_mul hf htb hJ.continuous hJ.injective

end GaloisForLFunctions
