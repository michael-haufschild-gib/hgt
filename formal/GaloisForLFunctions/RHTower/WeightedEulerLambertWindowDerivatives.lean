import GaloisForLFunctions.RHTower.WeightedEulerLambertDerivativeBound

/-!
# Window derivative bounds for the compact-carrier Lambert transform

Packaging of the Cauchy derivative estimate into the window form consumed by
the sampled-ray rate transfer: for a carrier with real-part floor `δ` and
norm ceiling `M`, and any node density `0 < c ≤ δ/(8M)`, the derivative of
order `⌊cR⌋ + 1` of the Lambert transform is bounded by `4‖L‖·e^{-(δ/2)R}`
uniformly on the window `[R, R+1]`, for every
`R ≥ max (8M/δ) (2 log 2/δ)`.

The two threshold conditions make the derivative order admissible for the
Cauchy estimate and the exponential test contractive.
-/

noncomputable section

namespace RHTower

open Set

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

/-- **Window derivative bound**: the Cauchy estimate for the Lambert
transform, at derivative order `⌊cR⌋ + 1`, uniformly on `[R, R+1]`. -/
theorem lambert_derivative_window_bound
    (L : C(K, ℂ) →L[ℂ] ℂ) (s : C(K, ℂ)) {δ M c : ℝ}
    (hδ : 0 < δ) (hδM : δ ≤ M)
    (hre : ∀ k, δ ≤ (s k).re) (hnorm : ∀ k, ‖s k‖ ≤ M)
    (hc0 : 0 < c) (hc : c ≤ δ / (8 * M)) :
    ∀ R : ℝ, max (8 * M / δ) (2 * Real.log 2 / δ) ≤ R →
      ∀ x ∈ Set.Icc R (R + 1),
        ‖iteratedDeriv (⌊c * R⌋₊ + 1)
            (compactCarrierLambertTransform L s) (x : ℂ)‖
          ≤ (4 * ‖L‖) * Real.exp (-(δ / 2 * R)) := by
  intro R hR x hx
  have hM0 : 0 < M := lt_of_lt_of_le hδ hδM
  have h4M : (0:ℝ) < 4 * M := by linarith
  have h8M : (0:ℝ) < 8 * M := by linarith
  have hR8 : 8 * M / δ ≤ R := le_trans (le_max_left _ _) hR
  have hRlog : 2 * Real.log 2 / δ ≤ R := le_trans (le_max_right _ _) hR
  have hR0 : 0 < R := lt_of_lt_of_le (by positivity) hR8
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
  -- the derivative order is admissible
  have hN : ((⌊c * R⌋₊ + 1 : ℕ) : ℝ) ≤ δ * x / (4 * M) := by
    have hcR0 : 0 ≤ c * R := by positivity
    have hfloor : ((⌊c * R⌋₊ : ℕ) : ℝ) ≤ c * R := Nat.floor_le hcR0
    have h1 : c * R ≤ δ * R / (8 * M) := by
      calc c * R ≤ δ / (8 * M) * R := mul_le_mul_of_nonneg_right hc hR0.le
        _ = δ * R / (8 * M) := by ring
    have h2 : (1:ℝ) ≤ δ * R / (8 * M) := by
      rw [le_div_iff₀ h8M]
      rw [div_le_iff₀ hδ] at hR8
      linarith
    have h4 : δ * R / (4 * M) ≤ δ * x / (4 * M) := by
      rw [div_le_div_iff₀ h4M h4M]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hxR hδ.le) h4M.le
    push_cast
    have h3 : δ * R / (8 * M) + δ * R / (8 * M) = δ * R / (4 * M) := by
      ring
    linarith
  have h4a := norm_iteratedDeriv_compactCarrierLambertTransform_le L s hδ hδM
    hre hnorm hx0 hcontr hN
  refine le_trans h4a ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.2
  nlinarith [mul_le_mul_of_nonneg_left hxR hδ.le]

end RHTower
