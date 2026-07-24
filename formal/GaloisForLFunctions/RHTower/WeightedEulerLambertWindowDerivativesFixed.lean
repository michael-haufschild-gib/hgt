import GaloisForLFunctions.RHTower.WeightedEulerLambertDerivativeBound

/-!
# Fixed-order window derivative bounds for the Lambert transform

The Cauchy derivative estimate packaged at a fixed order: for a carrier
with real-part floor `δ` and norm ceiling `M`, the order-`(N+1)`
derivative of the compact-carrier Lambert transform is bounded by
`4‖L‖·e^{-(δ/2)R}` uniformly on `[R, R+1]`, for every
`R ≥ max(4M(N+1)/δ, 2log2/δ)` — the window form consumed by the
fixed-order sampled-ray rate transfer.
-/

noncomputable section

namespace RHTower

open Set

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

/-- **Fixed-order window derivative bound** for the compact-carrier
Lambert transform. -/
theorem lambert_derivative_window_bound_fixed
    (L : C(K, ℂ) →L[ℂ] ℂ) (s : C(K, ℂ)) {δ M : ℝ} (N : ℕ)
    (hδ : 0 < δ) (hδM : δ ≤ M)
    (hre : ∀ k, δ ≤ (s k).re) (hnorm : ∀ k, ‖s k‖ ≤ M) :
    ∀ R : ℝ, max (4 * M * ((N : ℝ) + 1) / δ) (2 * Real.log 2 / δ) ≤ R →
      ∀ x ∈ Set.Icc R (R + 1),
        ‖iteratedDeriv (N + 1)
            (compactCarrierLambertTransform L s) (x : ℂ)‖
          ≤ (4 * ‖L‖) * Real.exp (-(δ / 2 * R)) := by
  intro R hR x hx
  have hM0 : 0 < M := lt_of_lt_of_le hδ hδM
  have h4M : (0 : ℝ) < 4 * M := by linarith
  have hRN : 4 * M * ((N : ℝ) + 1) / δ ≤ R := le_trans (le_max_left _ _) hR
  have hRlog : 2 * Real.log 2 / δ ≤ R := le_trans (le_max_right _ _) hR
  have hR0 : 0 < R := by
    have h1 : (0 : ℝ) < 4 * M * ((N : ℝ) + 1) / δ := by positivity
    linarith
  have hxR : R ≤ x := hx.1
  have hx0 : 0 < x := lt_of_lt_of_le hR0 hxR
  -- the exponential test is contractive at `x`
  have hcontr : Real.exp (-(x * δ / 2)) ≤ 1 / 2 := by
    have h1 : 2 * Real.log 2 ≤ δ * R := by
      rw [div_le_iff₀ hδ] at hRlog
      linarith
    have hlog : Real.log 2 ≤ x * δ / 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hxR hδ.le]
    calc Real.exp (-(x * δ / 2)) ≤ Real.exp (-(Real.log 2)) :=
          Real.exp_le_exp.2 (by linarith)
      _ = 1 / 2 := by
          rw [Real.exp_neg, Real.exp_log two_pos]
          norm_num
  -- the fixed derivative order is admissible past the linear threshold
  have hN : ((N + 1 : ℕ) : ℝ) ≤ δ * x / (4 * M) := by
    have h1 : 4 * M * ((N : ℝ) + 1) ≤ δ * R := by
      rw [div_le_iff₀ hδ] at hRN
      linarith
    have h2 : δ * R ≤ δ * x := mul_le_mul_of_nonneg_left hxR hδ.le
    rw [le_div_iff₀ h4M]
    push_cast
    nlinarith
  have h4a := norm_iteratedDeriv_compactCarrierLambertTransform_le L s hδ
    hδM hre hnorm hx0 hcontr hN
  refine le_trans h4a ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.2
  nlinarith [mul_le_mul_of_nonneg_left hxR hδ.le]

end RHTower
