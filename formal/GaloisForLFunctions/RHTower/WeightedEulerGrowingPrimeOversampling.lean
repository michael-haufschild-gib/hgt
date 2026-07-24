import GaloisForLFunctions.RHTower.GrowingOrderPrimeLogNodes
import GaloisForLFunctions.HTGeometry.SampledRayRateTransfer

/-!
# Growing-order prime-log oversampling

Pairing the growing-order separated prime-log node families with the
growing-order ray-rate transfer: an entire `H` whose window
derivatives at order `⌊cR⌋ + 1` decay like `e^{-δR}` and whose values
at every prime logarithm decay like `p^{-σ}` also decays along the
whole ray at rate `σ'` for any `σ' + 6c ≤ σ`.

The `6c` interpolation loss is what the fixed-order transfer cannot
overcome; the growing node count `⌊cR⌋ + 1` — available only from the
power-log prime number theorem — is exactly what removes the cap.
-/

noncomputable section

namespace RHTower

open scoped Classical

/-- **Growing-order prime-log oversampling**: prime-sampled decay
`‖H(log p)‖ ≤ C·p^{-σ}` plus window derivative decay at order
`⌊cR⌋ + 1` gives ray decay at every rate `σ'` with `σ' + 6c ≤ σ`. -/
theorem norm_le_ray_of_primeLog_sampled_decay_growing
    {H : ℂ → ℂ} (hH : Differentiable ℂ H)
    {R₀ δ K c σ C σ' : ℝ}
    (hδ : 0 < δ) (hK : 0 ≤ K) (hc : 0 < c) (hC : 0 ≤ C)
    (hσ0 : 0 ≤ σ) (hσ'0 : 0 ≤ σ') (hσ' : σ' + 6 * c ≤ σ)
    (hder : ∀ R : ℝ, R₀ ≤ R → ∀ x ∈ Set.Icc R (R + 1),
      ‖iteratedDeriv (⌊c * R⌋₊ + 1) H (x : ℂ)‖ ≤ K * Real.exp (-(δ * R)))
    (hsamp : ∀ p : ℕ, p.Prime →
      ‖H (Real.log p : ℂ)‖ ≤ C * Real.exp (-(σ * Real.log p))) :
    ∃ C' R₁ : ℝ, ∀ x : ℝ, R₁ ≤ x →
      ‖H (x : ℂ)‖ ≤ C' * Real.exp (-(σ' * x)) := by
  obtain ⟨Rn, hRn⟩ := exists_separated_primeLog_nodes_growing hc
  refine HTGeometry.norm_le_ray_of_sampled_decay (R₀ := max R₀ Rn) hH
    hδ hK hc hC hσ'0 hσ' ?_ ?_
  · intro R hR
    exact hder R (le_trans (le_max_left _ _) hR)
  · intro R hR
    obtain ⟨s, hcard, hsub, hsep, hlog⟩ :=
      hRn R (le_trans (le_max_right _ _) hR)
    refine ⟨s, hcard, hsub, hsep, fun t ht => ?_⟩
    obtain ⟨p, hp, rfl⟩ := hlog t ht
    have h2 : R ≤ Real.log p := (hsub ht).1
    have h3 : Real.exp (-(σ * Real.log p)) ≤ Real.exp (-(σ * R)) := by
      apply Real.exp_le_exp.2
      have := mul_le_mul_of_nonneg_left h2 hσ0
      linarith
    calc ‖H (Real.log p : ℂ)‖
        ≤ C * Real.exp (-(σ * Real.log p)) := hsamp p hp
      _ ≤ C * Real.exp (-(σ * R)) := mul_le_mul_of_nonneg_left h3 hC

end RHTower
