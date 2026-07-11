/-
# The two-budget splice: zero-free balls from a center value and a sphere bound

The averaged zero-repulsion inequality `A(r₂) − A(r₁) < log r₂ − log r₁` that decides the
sub-unit slope criterion splits into two one-sided budgets, each already a theorem shape:

* **center floor** (`xi_log_norm_center_le_circleAverage`) — at a nonvanishing center Jensen's
  formula writes `A(r)` as `log ‖ξ(ρ)‖` plus a nonnegative divisor sum, so
  `log ‖ξ(ρ)‖ ≤ A(r)` at every radius;
* **sphere cap** (`xi_circleAverage_le_log_sup`) — a sup bound `M` for `‖ξ‖` on the outer
  circle caps `A(r₂) ≤ log M`.

Splicing the two (`modulusSlope_lt_one_of_center_sup_budget`) shows the slope is below `1` as
soon as `log M − log ‖ξ(ρ)‖ < log r₂ − log r₁`, and quantization then certifies the whole inner
closed ball ξ-zero-free (`xi_zeroFree_closedBall_of_center_sup_budget`).  Solving the budget for
the inner radius gives the **effective isolation radius**
`r₁ = r₂ · ‖ξ(ρ)‖ / (2M)` (`xi_zeroFree_closedBall_effective_radius`): two modulus data — one
point value, one circle bound — produce an explicit zero-free ball.

On the real segment of the critical strip the center data is unconditional: `ξ(σ)` is a strictly
positive real for `σ ∈ (0,1)`, so every real anchor carries an explicit zero-free ball
(`xi_zeroFree_closedBall_real_anchor`), and taking the sup over the compact outer circle makes
the certificate hypothesis-free (`exists_xi_zeroFree_closedBall_real_anchor`) — strip boxes
certified zero-free by the field alone.  The residual open input for boxes OFF the real axis is
exactly the numeric pair (center value, circle sup) at the chosen box.
-/
import GaloisForLFunctions.RHTower.ModulusSlopeQuantization
import GaloisForLFunctions.RHTower.XiRealAnchorPositive

open Complex Metric

namespace RHTower

noncomputable section

/-- **Center floor.**  At a nonvanishing center, every circle average of `log ‖ξ‖` sits above
the center value: the divisor correction in Jensen's formula is nonnegative. -/
theorem xi_log_norm_center_le_circleAverage {ρ : ℂ} {r : ℝ} (hr : 0 < r) (hρ : xi ρ ≠ 0) :
    Real.log ‖xi ρ‖ ≤ Real.circleAverage (fun z => Real.log ‖xi z‖) ρ r := by
  have hJ := AnalyticOnNhd.circleAverage_log_norm (c := ρ) (R := r) hr.ne'
    (xi_analyticOnNhd _) hρ
  rw [hJ]
  have hfin : 0 ≤ ∑ᶠ u, ((MeromorphicOn.divisor xi (closedBall ρ |r|)) u : ℝ) *
      Real.log (r * ‖ρ - u‖⁻¹) := by
    apply finsum_nonneg
    intro u
    by_cases hu : u ∈ closedBall ρ |r|
    · by_cases huρ : u = ρ
      · subst huρ
        simp
      · refine mul_nonneg ?_ ?_
        · rw [xi_divisor_closedBall_eq_order_toNat hu]
          positivity
        · have hnorm : 0 < ‖ρ - u‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm huρ))
          have hle : ‖ρ - u‖ ≤ r := by
            rw [mem_closedBall, dist_comm, dist_eq_norm, abs_of_pos hr] at hu
            exact hu
          have hone : (1 : ℝ) ≤ r / ‖ρ - u‖ := (one_le_div hnorm).mpr hle
          rw [div_eq_mul_inv] at hone
          exact Real.log_nonneg hone
    · rw [xi_divisor_closedBall_eq_zero_of_notMem hu]
      simp
  linarith

/-- **Sphere cap.**  A sup bound for `‖ξ‖` on the circle caps the circle average of `log ‖ξ‖`.
The bound `1 ≤ M` absorbs circle points where ξ vanishes (`log 0 = 0`). -/
theorem xi_circleAverage_le_log_sup {ρ : ℂ} {r M : ℝ} (hr : 0 < r) (hM : 1 ≤ M)
    (hbound : ∀ z ∈ sphere ρ r, ‖xi z‖ ≤ M) :
    Real.circleAverage (fun z => Real.log ‖xi z‖) ρ r ≤ Real.log M := by
  apply Real.circleAverage_mono_on_of_le_circle
  · exact ((xi_analyticOnNhd _).meromorphicOn).circleIntegrable_log_norm
  · intro z hz
    rw [abs_of_pos hr] at hz
    rcases eq_or_ne (xi z) 0 with h0 | h0
    · simp only [h0, norm_zero, Real.log_zero]
      exact Real.log_nonneg hM
    · exact Real.log_le_log (norm_pos_iff.mpr h0) (hbound z hz)

/-- **The two-budget splice.**  A nonvanishing center value and an outer-circle sup bound whose
logarithmic gap is below the radius-ratio budget force a sub-unit slope sample. -/
theorem modulusSlope_lt_one_of_center_sup_budget {ρ : ℂ} {r₁ r₂ M : ℝ}
    (hr₁ : 0 < r₁) (h₁₂ : r₁ < r₂) (hρ : xi ρ ≠ 0) (hM : 1 ≤ M)
    (hbound : ∀ z ∈ sphere ρ r₂, ‖xi z‖ ≤ M)
    (hbudget : Real.log M - Real.log ‖xi ρ‖ < Real.log r₂ - Real.log r₁) :
    modulusSlope ρ r₁ r₂ < 1 := by
  have hΔ : 0 < Real.log r₂ - Real.log r₁ := sub_pos.mpr (Real.log_lt_log hr₁ h₁₂)
  have hA₁ := xi_log_norm_center_le_circleAverage hr₁ hρ
  have hA₂ := xi_circleAverage_le_log_sup (hr₁.trans h₁₂) hM hbound
  rw [modulusSlope, div_lt_one hΔ]
  linarith

/-- A center value and an outer-circle sup bound within the radius-ratio budget certify the
inner closed ball ξ-zero-free. -/
theorem xi_zeroFree_closedBall_of_center_sup_budget {ρ : ℂ} {r₁ r₂ M : ℝ}
    (hr₁ : 0 < r₁) (h₁₂ : r₁ < r₂) (hρ : xi ρ ≠ 0) (hM : 1 ≤ M)
    (hbound : ∀ z ∈ sphere ρ r₂, ‖xi z‖ ≤ M)
    (hbudget : Real.log M - Real.log ‖xi ρ‖ < Real.log r₂ - Real.log r₁) :
    ∀ z ∈ closedBall ρ r₁, xi z ≠ 0 :=
  xi_zeroFree_closedBall_of_modulusSlope_lt_one hr₁ h₁₂
    (modulusSlope_lt_one_of_center_sup_budget hr₁ h₁₂ hρ hM hbound hbudget)

/-- **Effective isolation radius.**  Two modulus data — the center value `‖ξ(ρ)‖` and a circle
bound `M` at radius `r₂` — certify the explicit ball of radius `r₂ · ‖ξ(ρ)‖ / (2M)` around `ρ`
to be ξ-zero-free. -/
theorem xi_zeroFree_closedBall_effective_radius {ρ : ℂ} {r₂ M : ℝ}
    (hr₂ : 0 < r₂) (hρ : xi ρ ≠ 0) (hM : 1 ≤ M) (hcM : ‖xi ρ‖ ≤ M)
    (hbound : ∀ z ∈ sphere ρ r₂, ‖xi z‖ ≤ M) :
    ∀ z ∈ closedBall ρ (r₂ * ‖xi ρ‖ / (2 * M)), xi z ≠ 0 := by
  have hnorm : 0 < ‖xi ρ‖ := norm_pos_iff.mpr hρ
  have hMpos : (0 : ℝ) < M := lt_of_lt_of_le one_pos hM
  have hr₁pos : 0 < r₂ * ‖xi ρ‖ / (2 * M) := by positivity
  have h₁₂ : r₂ * ‖xi ρ‖ / (2 * M) < r₂ := by
    rw [div_lt_iff₀ (by positivity)]
    have h2M : ‖xi ρ‖ < 2 * M := by linarith
    calc r₂ * ‖xi ρ‖ < r₂ * (2 * M) := by
          exact mul_lt_mul_of_pos_left h2M hr₂
      _ = r₂ * (2 * M) := rfl
  refine xi_zeroFree_closedBall_of_center_sup_budget hr₁pos h₁₂ hρ hM hbound ?_
  have hlog : Real.log (r₂ * ‖xi ρ‖ / (2 * M)) =
      Real.log r₂ + Real.log ‖xi ρ‖ - (Real.log 2 + Real.log M) := by
    rw [Real.log_div (by positivity) (by positivity),
      Real.log_mul hr₂.ne' hnorm.ne', Real.log_mul two_ne_zero hMpos.ne']
  rw [hlog]
  have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  linarith

/-- The completed ξ does not vanish on the real segment of the critical strip. -/
theorem xi_ne_zero_real_anchor {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) : xi (σ : ℂ) ≠ 0 := by
  intro h
  have hre := xi_pos_on_real_anchor h0 h1
  rw [h] at hre
  simp at hre

/-- On the real segment of the strip the modulus of ξ is its (positive) real part. -/
theorem xi_norm_real_anchor {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    ‖xi (σ : ℂ)‖ = (xi (σ : ℂ)).re := by
  have him := xi_real_on_real_anchor h0 h1
  have hre := xi_pos_on_real_anchor h0 h1
  have hz : xi (σ : ℂ) = (((xi (σ : ℂ)).re : ℝ) : ℂ) :=
    Complex.ext (Complex.ofReal_re _).symm (by rw [Complex.ofReal_im, him])
  calc ‖xi (σ : ℂ)‖ = ‖(((xi (σ : ℂ)).re : ℝ) : ℂ)‖ := by rw [← hz]
    _ = |(xi (σ : ℂ)).re| := Complex.norm_real _
    _ = (xi (σ : ℂ)).re := abs_of_pos hre

/-- **Explicit strip boxes at real anchors.**  For every `σ ∈ (0,1)` and every outer radius with
circle bound `M`, the ball of explicit radius `r₂ · ξ(σ).re / (2M)` around the real anchor `σ`
is ξ-zero-free — an unconditional strip box certified by the field from one circle bound. -/
theorem xi_zeroFree_closedBall_real_anchor {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1)
    {r₂ M : ℝ} (hr₂ : 0 < r₂) (hM : 1 ≤ M) (hcM : ‖xi (σ : ℂ)‖ ≤ M)
    (hbound : ∀ z ∈ sphere (σ : ℂ) r₂, ‖xi z‖ ≤ M) :
    ∀ z ∈ closedBall (σ : ℂ) (r₂ * (xi (σ : ℂ)).re / (2 * M)), xi z ≠ 0 := by
  rw [← xi_norm_real_anchor h0 h1]
  exact xi_zeroFree_closedBall_effective_radius hr₂ (xi_ne_zero_real_anchor h0 h1) hM hcM hbound

/-- **Hypothesis-free strip boxes.**  Every real anchor of the strip carries a zero-free closed
ball certified by the field alone: the outer-circle sup exists by compactness, and the
effective-radius formula turns it into a concrete inner radius. -/
theorem exists_xi_zeroFree_closedBall_real_anchor {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1)
    {r₂ : ℝ} (hr₂ : 0 < r₂) :
    ∃ r₁ > 0, ∀ z ∈ closedBall (σ : ℂ) r₁, xi z ≠ 0 := by
  obtain ⟨z₀, hz₀mem, hz₀max⟩ := (isCompact_sphere (σ : ℂ) r₂).exists_isMaxOn
    (NormedSpace.sphere_nonempty.mpr hr₂.le)
    ((xi_differentiable.continuous.norm).continuousOn)
  have hρ : xi (σ : ℂ) ≠ 0 := xi_ne_zero_real_anchor h0 h1
  have hM1 : (1 : ℝ) ≤ max 1 (max ‖xi z₀‖ ‖xi (σ : ℂ)‖) := le_max_left _ _
  have hbound : ∀ z ∈ sphere (σ : ℂ) r₂,
      ‖xi z‖ ≤ max 1 (max ‖xi z₀‖ ‖xi (σ : ℂ)‖) := fun z hz =>
    le_trans (hz₀max hz) (le_trans (le_max_left _ _) (le_max_right _ _))
  have hcM : ‖xi (σ : ℂ)‖ ≤ max 1 (max ‖xi z₀‖ ‖xi (σ : ℂ)‖) :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨r₂ * ‖xi (σ : ℂ)‖ / (2 * max 1 (max ‖xi z₀‖ ‖xi (σ : ℂ)‖)), ?_,
    xi_zeroFree_closedBall_effective_radius hr₂ hρ hM1 hcM hbound⟩
  have hnorm : 0 < ‖xi (σ : ℂ)‖ := norm_pos_iff.mpr hρ
  have hMpos : (0 : ℝ) < max 1 (max ‖xi z₀‖ ‖xi (σ : ℂ)‖) := lt_of_lt_of_le one_pos hM1
  positivity

end

end RHTower
