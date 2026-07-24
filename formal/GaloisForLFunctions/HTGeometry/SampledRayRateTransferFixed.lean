import GaloisForLFunctions.HTGeometry.SampledWindowDecay

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
        * Real.exp (-(min σ δ * x)) := by
  intro x hx
  have hRR₀ : R₀ ≤ x - 1 := by linarith
  have hx0 : 0 ≤ x := by linarith
  obtain ⟨s, hcard, hsub, hsep, hsamp⟩ := hnodes (x - 1) hRR₀
  have hxmem : x ∈ Set.Icc (x - 1) (x - 1 + 1) := by
    constructor <;> linarith
  have hwin := norm_le_window_of_sampled hH hcard hsub hsep
    (hder (x - 1) hRR₀) (by positivity) hsamp hxmem
  have hmin : 0 ≤ min σ δ := le_min hσ0 hδ0
  -- interpolant term at the `min`-rate
  have hA : 2 * Real.exp (6 * ((N : ℝ) + 1)) * (C * Real.exp (-(σ * (x - 1))))
      ≤ 2 * Real.exp (6 * ((N : ℝ) + 1)) * C * Real.exp σ
        * Real.exp (-(min σ δ * x)) := by
    have h1 : Real.exp (-(σ * (x - 1)))
        ≤ Real.exp σ * Real.exp (-(min σ δ * x)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.2
      have h2 : min σ δ * x ≤ σ * x :=
        mul_le_mul_of_nonneg_right (min_le_left σ δ) hx0
      linarith
    calc 2 * Real.exp (6 * ((N : ℝ) + 1)) * (C * Real.exp (-(σ * (x - 1))))
        ≤ 2 * Real.exp (6 * ((N : ℝ) + 1))
          * (C * (Real.exp σ * Real.exp (-(min σ δ * x)))) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_left h1 hC
      _ = 2 * Real.exp (6 * ((N : ℝ) + 1)) * C * Real.exp σ
          * Real.exp (-(min σ δ * x)) := by ring
  -- remainder term at the `min`-rate
  have hB : 2 * (K * Real.exp (-(δ * (x - 1))) / (N + 1).factorial)
      ≤ 2 * K * Real.exp δ / (N + 1).factorial
        * Real.exp (-(min σ δ * x)) := by
    have h1 : Real.exp (-(δ * (x - 1)))
        ≤ Real.exp δ * Real.exp (-(min σ δ * x)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.2
      have h2 : min σ δ * x ≤ δ * x :=
        mul_le_mul_of_nonneg_right (min_le_right σ δ) hx0
      linarith
    have hfac0 : (0 : ℝ) < ((N + 1).factorial : ℝ) := by
      exact_mod_cast Nat.factorial_pos (N + 1)
    calc 2 * (K * Real.exp (-(δ * (x - 1))) / (N + 1).factorial)
        ≤ 2 * (K * (Real.exp δ * Real.exp (-(min σ δ * x)))
            / (N + 1).factorial) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply div_le_div_of_nonneg_right _ hfac0.le
          exact mul_le_mul_of_nonneg_left h1 hK
      _ = 2 * K * Real.exp δ / (N + 1).factorial
          * Real.exp (-(min σ δ * x)) := by ring
  calc ‖H (x : ℂ)‖
      ≤ 2 * Real.exp (6 * ((N : ℝ) + 1))
          * (C * Real.exp (-(σ * (x - 1))))
        + 2 * (K * Real.exp (-(δ * (x - 1))) / (N + 1).factorial) := hwin
    _ ≤ 2 * Real.exp (6 * ((N : ℝ) + 1)) * C * Real.exp σ
          * Real.exp (-(min σ δ * x))
        + 2 * K * Real.exp δ / (N + 1).factorial
          * Real.exp (-(min σ δ * x)) := add_le_add hA hB
    _ = (2 * Real.exp (6 * ((N : ℝ) + 1)) * C * Real.exp σ
          + 2 * K * Real.exp δ / (N + 1).factorial)
        * Real.exp (-(min σ δ * x)) := by ring

end HTGeometry
