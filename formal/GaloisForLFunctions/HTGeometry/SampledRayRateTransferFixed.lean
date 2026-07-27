import GaloisForLFunctions.HTGeometry.SampledWindowDecay
import GaloisForLFunctions.HTGeometry.SampledRayRateTransferHalfplane

/-!
# Fixed-order ray rate transfer

The oversampling principle at a fixed interpolation order: an entire
function whose order-`N+1` derivative decays like `e^{-δR}` on each unit
window `[R, R+1]`, and which is `≤ C e^{-σR}` at `N+1` canonically
separated sample points of each window, decays along the whole ray at the
rate `min σ δ` with the explicit constant
`2e^{6(N+1)}·C·e^σ + 2K·e^δ/(N+1)!`.

Unlike the growing-order transfer, the node count here is a fixed `N+1`
per window — matching node supplies that provide, for each fixed `N`, all
windows past a threshold.  The rate is capped at `δ` instead of paying
the `6c` loss; applications recover any target rate below the sampled
rate by taking `δ` (the carrier depth) at least `σ`.
-/

noncomputable section

namespace HTGeometry

open Set

/-- **Fixed-order ray rate transfer**: window-sampled exponential decay at
`N+1` separated nodes per window propagates to ray decay at rate
`min σ δ`. -/
theorem norm_le_ray_of_sampled_decay_fixed
    {H : ℂ → ℂ} (hH : Differentiable ℂ H)
    {R₀ δ K σ C : ℝ} {N : ℕ}
    (hR₀0 : 0 ≤ R₀) (hK : 0 ≤ K) (hC : 0 ≤ C) (hσ0 : 0 ≤ σ)
    (hδ0 : 0 ≤ δ)
    (hder : ∀ R : ℝ, R₀ ≤ R → ∀ x ∈ Set.Icc R (R + 1),
      ‖iteratedDeriv (N + 1) H (x : ℂ)‖ ≤ K * Real.exp (-(δ * R)))
    (hnodes : ∀ R : ℝ, R₀ ≤ R → ∃ s : Finset ℝ,
      s.card = N + 1 ∧ ↑s ⊆ Set.Icc R (R + 1) ∧
      (∀ t ∈ s, ∀ u ∈ s, t ≠ u →
        1 / (4 * ((N : ℝ) + 1)) ≤ |t - u|) ∧
      (∀ t ∈ s, ‖H (t : ℂ)‖ ≤ C * Real.exp (-(σ * R)))) :
    ∀ x : ℝ, R₀ + 1 ≤ x →
      ‖H (x : ℂ)‖ ≤ (2 * Real.exp (6 * ((N : ℝ) + 1)) * C * Real.exp σ
          + 2 * K * Real.exp δ / (N + 1).factorial)
        * Real.exp (-(min σ δ * x)) :=
  norm_le_ray_of_sampled_decay_fixed_halfplane (T := R₀ - 1)
    (fun t _ => hH.analyticAt (t : ℂ)) (by linarith) hR₀0 hK hC hσ0 hδ0 hder hnodes

end HTGeometry
