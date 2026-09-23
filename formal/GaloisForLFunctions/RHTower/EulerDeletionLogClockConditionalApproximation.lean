import GaloisForLFunctions.RHTower.EulerDeletionLogClockProducerReduction

/-!
# One-clock conditional approximation of the complete EDQ drift

All chronological energy above a logarithmic cutoff is a vanishing
orthogonal residual. The remaining hard carrier is exactly one conditional
projection, not a collection of unrelated layer estimates.
-/

noncomputable section
set_option autoImplicit false
open Finset Filter Topology

namespace RHTower.DeletionResidueMartingale

/-- The low-clock producer is exactly the energy of one literal chronological
conditional projection of the full signed drift. -/
theorem lowClockProducerEnergy_eq_historyProjection_norm_sq (N : ℕ) :
    lowClockProducerEnergy N =
      ‖(historySpace (min (logarithmicClockThreshold N) N)).starProjection
        (predictableDrift N)‖ ^ (2 : ℕ) := by
  rw [history_projection_norm_sq_eq_layer_sum]
  rfl

/-- Exact Pythagorean identification of the discarded moving high-clock field. -/
theorem predictableDrift_logClockProjection_error_norm_sq_eq_highClock (N : ℕ) :
    ‖predictableDrift N -
        (historySpace (min (logarithmicClockThreshold N) N)).starProjection
          (predictableDrift N)‖ ^ (2 : ℕ) =
      ∑ l ∈ Ico (logarithmicClockThreshold N) N,
        ‖historyLayer l (predictableDrift N)‖ ^ (2 : ℕ) := by
  have hp := Submodule.norm_sq_eq_add_norm_sq_starProjection
    (predictableDrift N) (historySpace (min (logarithmicClockThreshold N) N))
  have hfull := predictableDrift_norm_sq_eq_lowClock_add_highClock N
  rw [lowClockProducerEnergy_eq_historyProjection_norm_sq] at hfull
  nlinarith

/-- The full EDQ drift differs from its single signed logarithmic-clock
conditional expectation by squared physical energy at most `110/(N+1)`. -/
theorem predictableDrift_logClockProjection_error_norm_sq_le (N : ℕ) :
    ‖predictableDrift N -
        (historySpace (min (logarithmicClockThreshold N) N)).starProjection
          (predictableDrift N)‖ ^ (2 : ℕ) ≤ 110 / ((N : ℝ) + 1) := by
  rw [predictableDrift_logClockProjection_error_norm_sq_eq_highClock]
  simpa only [Nat.cast_add, Nat.cast_one] using
    predictableDrift_logarithmic_highClock_energy_le N

/-- The approximation is strong in physical `L²`, though its moving
conditional projections need not converge or have bounded energy. -/
theorem predictableDrift_logClockProjection_error_norm_tendsto_zero :
    Tendsto (fun N : ℕ => ‖predictableDrift N -
      (historySpace (min (logarithmicClockThreshold N) N)).starProjection
        (predictableDrift N)‖) atTop (𝓝 0) := by
  have hsq : Tendsto (fun N : ℕ => ‖predictableDrift N -
      (historySpace (min (logarithmicClockThreshold N) N)).starProjection
        (predictableDrift N)‖ ^ (2 : ℕ)) atTop (𝓝 0) := by
    simpa only [predictableDrift_logClockProjection_error_norm_sq_eq_highClock] using
      predictableDrift_logarithmic_highClock_energy_tendsto_zero
  have hsqrt := hsq.sqrt
  simpa only [Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hsqrt

end RHTower.DeletionResidueMartingale
