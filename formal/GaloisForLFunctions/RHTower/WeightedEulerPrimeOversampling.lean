import GaloisForLFunctions.RHTower.PrimeWindowSupply
import GaloisForLFunctions.HTGeometry.SampledRayRateTransferFixed

/-!
# The unconditional prime-log oversampling lemma

Sampled decay of an entire function at the prime logarithms upgrades to
genuine ray decay, with the prime nodes supplied unconditionally by the
elementary prime number theorem:

if `‖H^{(N+1)}‖ ≤ K e^{-δR}` on windows and `‖H(log p)‖ ≤ C p^{-σ}` at
every prime, then `‖H(x)‖ ≤ C' e^{-min σ δ·x}` for all large `x`.

This is the card's oversampling estimate (8a) with the node hypothesis
discharged: the separated prime-log families exist in every unit window
far enough right by `exists_separated_primeLog_nodes_unconditional`.
-/

noncomputable section

namespace RHTower

open Set

/-- **Unconditional prime-log oversampling**: derivative-window decay
plus sampled decay at the prime logarithms forces ray decay at rate
`min σ δ`. -/
theorem norm_le_ray_of_primeLog_sampled_decay
    {H : ℂ → ℂ} (hH : Differentiable ℂ H)
    {R₀ δ K σ C : ℝ} {N : ℕ}
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hσ0 : 0 ≤ σ) (hδ0 : 0 ≤ δ)
    (hder : ∀ R : ℝ, R₀ ≤ R → ∀ x ∈ Set.Icc R (R + 1),
      ‖iteratedDeriv (N + 1) H (x : ℂ)‖ ≤ K * Real.exp (-(δ * R)))
    (hsamp : ∀ p : ℕ, p.Prime →
      ‖H (Real.log p : ℂ)‖ ≤ C * Real.exp (-(σ * Real.log p))) :
    ∃ C' R₁ : ℝ, ∀ x : ℝ, R₁ ≤ x →
      ‖H (x : ℂ)‖ ≤ C' * Real.exp (-(min σ δ * x)) := by
  obtain ⟨Rn, hRn⟩ := exists_separated_primeLog_nodes_unconditional N
  refine ⟨2 * Real.exp (6 * ((N : ℝ) + 1)) * C * Real.exp σ
      + 2 * K * Real.exp δ / (N + 1).factorial,
    max R₀ (max Rn 0) + 1, fun x hx => ?_⟩
  have hR₀0 : (0 : ℝ) ≤ max R₀ (max Rn 0) :=
    le_trans (le_max_right Rn 0) (le_max_right _ _)
  apply HTGeometry.norm_le_ray_of_sampled_decay_fixed hH hR₀0 hK hC hσ0 hδ0
    (fun R hR => hder R (le_trans (le_max_left _ _) hR)) ?_ x hx
  intro R hR
  obtain ⟨s, hcard, hsub, hsep, hlog⟩ :=
    hRn R (le_trans (le_trans (le_max_left Rn 0) (le_max_right _ _)) hR)
  refine ⟨s, hcard, hsub, hsep, fun t ht => ?_⟩
  obtain ⟨p, hp, rfl⟩ := hlog t ht
  have h1 := hsamp p hp
  have h2 : R ≤ Real.log p := (hsub ht).1
  have h3 : Real.exp (-(σ * Real.log p)) ≤ Real.exp (-(σ * R)) := by
    apply Real.exp_le_exp.2
    have := mul_le_mul_of_nonneg_left h2 hσ0
    linarith
  calc ‖H (Real.log p : ℂ)‖
      ≤ C * Real.exp (-(σ * Real.log p)) := h1
    _ ≤ C * Real.exp (-(σ * R)) :=
      mul_le_mul_of_nonneg_left h3 hC

end RHTower
