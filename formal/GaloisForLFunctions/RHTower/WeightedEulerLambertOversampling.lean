import GaloisForLFunctions.RHTower.PrimeWindowSupply
import GaloisForLFunctions.RHTower.WeightedEulerLambertWindowDerivativesFixed
import GaloisForLFunctions.HTGeometry.SampledRayRateTransferHalfplane

/-!
# The unconditional Lambert oversampling estimate

The card's oversampling lemma (8a) for the actual compact-carrier
Lambert transform, with every hypothesis discharged:

sampled decay `‖Λ_L(log p)‖ ≤ C·p^{-σ}` at the prime logarithms forces
`‖Λ_L(x)‖ ≤ C'·e^{-min(σ, δ/2)·x}` along the whole ray —

analyticity at real points from the contractive exponential test,
window derivative bounds from the fixed-order Cauchy estimate, and the
separated prime-log nodes from the elementary prime number theorem.
-/

noncomputable section

namespace RHTower

open Set

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

/-- **Unconditional Lambert oversampling (8a)**: prime-log sampled decay
of the compact-carrier Lambert transform upgrades to ray decay at rate
`min σ (δ/2)`. -/
theorem norm_le_ray_of_primeLog_sampled_lambert
    (L : C(K, ℂ) →L[ℂ] ℂ) (s : C(K, ℂ)) {δ M σ C : ℝ} (N : ℕ)
    (hδ : 0 < δ) (hδM : δ ≤ M)
    (hre : ∀ k, δ ≤ (s k).re) (hnorm : ∀ k, ‖s k‖ ≤ M)
    (hσ0 : 0 ≤ σ) (hC : 0 ≤ C)
    (hsamp : ∀ p : ℕ, p.Prime →
      ‖compactCarrierLambertTransform L s (Real.log p : ℂ)‖
        ≤ C * Real.exp (-(σ * Real.log p))) :
    ∃ C' R₁ : ℝ, ∀ x : ℝ, R₁ ≤ x →
      ‖compactCarrierLambertTransform L s (x : ℂ)‖
        ≤ C' * Real.exp (-(min σ (δ / 2) * x)) := by
  have hM0 : 0 < M := lt_of_lt_of_le hδ hδM
  -- analyticity at real points of the positive axis
  have hH : ∀ t : ℝ, (0 : ℝ) < t →
      AnalyticAt ℂ (compactCarrierLambertTransform L s) (t : ℂ) := by
    intro t ht
    apply compactCarrierLambertTransform_analyticAt
    apply norm_compactExponentialTest_lt_one_of_re_pos s _ (t * δ)
      (by positivity)
    intro k
    have h1 : ((t : ℂ) * s k).re = t * (s k).re := by
      simp [Complex.mul_re]
    rw [h1]
    exact mul_le_mul_of_nonneg_left (hre k) ht.le
  -- the prime-log node families
  obtain ⟨Rn, hRn⟩ := exists_separated_primeLog_nodes_unconditional N
  -- the combined threshold
  refine ⟨2 * Real.exp (6 * ((N : ℝ) + 1)) * C * Real.exp σ
      + 2 * (4 * ‖L‖) * Real.exp (δ / 2) / (N + 1).factorial,
    max (max (4 * M * ((N : ℝ) + 1) / δ) (2 * Real.log 2 / δ))
      (max Rn 1) + 1, fun x hx => ?_⟩
  have hR₀1 : (1 : ℝ) ≤ max (max (4 * M * ((N : ℝ) + 1) / δ)
      (2 * Real.log 2 / δ)) (max Rn 1) :=
    le_trans (le_max_right Rn 1) (le_max_right _ _)
  apply HTGeometry.norm_le_ray_of_sampled_decay_fixed_halfplane
    (T := 0) hH (by linarith) (by linarith) (by positivity) hC hσ0
    (by linarith) ?_ ?_ x hx
  · -- window derivative bounds at fixed order
    intro R hR y hy
    exact lambert_derivative_window_bound_fixed L s N hδ hδM hre hnorm R
      (le_trans (le_max_left _ _) hR) y hy
  · -- separated prime-log nodes with sampled decay
    intro R hR
    obtain ⟨t, hcard, hsub, hsep, hlog⟩ := hRn R
      (le_trans (le_trans (le_max_left Rn 1) (le_max_right _ _)) hR)
    refine ⟨t, hcard, hsub, hsep, fun u hu => ?_⟩
    obtain ⟨p, hp, rfl⟩ := hlog u hu
    have h1 := hsamp p hp
    have h2 : R ≤ Real.log p := (hsub hu).1
    have h3 : Real.exp (-(σ * Real.log p)) ≤ Real.exp (-(σ * R)) := by
      apply Real.exp_le_exp.2
      have := mul_le_mul_of_nonneg_left h2 hσ0
      linarith
    calc ‖compactCarrierLambertTransform L s (Real.log p : ℂ)‖
        ≤ C * Real.exp (-(σ * Real.log p)) := h1
      _ ≤ C * Real.exp (-(σ * R)) :=
        mul_le_mul_of_nonneg_left h3 hC

end RHTower
