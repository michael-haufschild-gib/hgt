import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Truncated powers

A truncation argument comparing `∫ xᵏ dν` across a family of measures needs a bounded continuous
function agreeing with `xᵏ` on a ball.  Clamping the argument before raising it to the power,

`truncPow R k x = (max (min x R) (-R))ᵏ`,

supplies one directly: it is continuous as a composition of lattice operations with a power, it is
bounded by `Rᵏ` because the clamp lands in `[-R, R]`, and it agrees with `xᵏ` on `[-R, R]` because
the clamp is the identity there.  No bump function or partition of unity is involved.
-/

open scoped BigOperators

namespace HTGeometry

/-- The `k`-th power of the argument clamped to `[-R, R]`. -/
noncomputable def truncPow (R : ℝ) (k : ℕ) (x : ℝ) : ℝ := (max (min x R) (-R)) ^ k

theorem continuous_truncPow (R : ℝ) (k : ℕ) : Continuous (truncPow R k) :=
  ((continuous_id.min continuous_const).max continuous_const).pow k

/-- The clamp lands in `[-R, R]`. -/
theorem abs_clamp_le (hR : 0 ≤ R) (x : ℝ) : |max (min x R) (-R)| ≤ R := by
  refine abs_le.mpr ⟨le_max_right _ _, max_le (min_le_right _ _) (by linarith)⟩

theorem abs_truncPow_le (hR : 0 ≤ R) (k : ℕ) (x : ℝ) : |truncPow R k x| ≤ R ^ k := by
  rw [truncPow, abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (abs_clamp_le hR x) k

/-- On the ball the truncation is the honest power. -/
theorem truncPow_eq_of_mem_Icc (R : ℝ) (k : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (-R) R) :
    truncPow R k x = x ^ k := by
  obtain ⟨hlo, hhi⟩ := hx
  rw [truncPow, min_eq_left hhi, max_eq_left hlo]

/-- Outside the ball the truncation is dominated by the honest power. -/
theorem abs_truncPow_le_abs_pow (hR : 0 ≤ R) (k : ℕ) {x : ℝ} (hx : R ≤ |x|) :
    |truncPow R k x| ≤ |x| ^ k :=
  le_trans (abs_truncPow_le hR k x) (pow_le_pow_left₀ hR hx k)

/-- The truncated power packaged as a bounded continuous function. -/
noncomputable def truncPowBCF (R : ℝ) (hR : 0 ≤ R) (k : ℕ) : BoundedContinuousFunction ℝ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (truncPow R k) (continuous_truncPow R k) (R ^ k)
    fun x => by simpa [Real.norm_eq_abs] using abs_truncPow_le hR k x

@[simp] theorem truncPowBCF_apply (R : ℝ) (hR : 0 ≤ R) (k : ℕ) (x : ℝ) :
    truncPowBCF R hR k x = truncPow R k x := rfl

/-! ## The comparison estimate

The gap between the honest power and its truncation is supported outside the ball, and there it is
at most twice the honest power.  This single pointwise bound is what drives the truncation argument:
integrating it against any measure turns a tail estimate for that measure into a bound on how far
the truncated integral can be from the true one. -/

/-- **Pointwise comparison.**  The error vanishes on `[-R, R]` and is at most `2|x|ᵏ` off it. -/
theorem abs_pow_sub_truncPow_le (hR : 0 ≤ R) (k : ℕ) (x : ℝ) :
    |x ^ k - truncPow R k x|
      ≤ ((Set.Icc (-R) R)ᶜ).indicator (fun y => 2 * |y| ^ k) x := by
  by_cases hx : x ∈ Set.Icc (-R) R
  · rw [truncPow_eq_of_mem_Icc R k hx, sub_self, abs_zero,
      Set.indicator_of_notMem (not_not_intro hx)]
  · have hxabs : R ≤ |x| := by
      simp only [Set.mem_Icc, ← abs_le, not_le] at hx
      exact hx.le
    rw [Set.indicator_of_mem hx]
    have htri : |x ^ k - truncPow R k x| ≤ |x ^ k| + |truncPow R k x| := by
      have h := norm_sub_le (x ^ k) (truncPow R k x)
      simpa [Real.norm_eq_abs] using h
    calc |x ^ k - truncPow R k x|
        ≤ |x ^ k| + |truncPow R k x| := htri
      _ ≤ |x| ^ k + |x| ^ k := by
          rw [abs_pow]
          linarith [abs_truncPow_le_abs_pow hR k hxabs]
      _ = 2 * |x| ^ k := by ring

/-- The comparison error is supported outside the ball. -/
theorem abs_pow_sub_truncPow_eq_zero_of_mem (R : ℝ) (k : ℕ) {x : ℝ}
    (hx : x ∈ Set.Icc (-R) R) : x ^ k - truncPow R k x = 0 := by
  rw [truncPow_eq_of_mem_Icc R k hx, sub_self]

/-! ## An indicator-free bound

On the tail `Rᵏ ≤ |x|ᵏ`, so `|x|ᵏ ≤ |x|^{2k} / Rᵏ` there, while on the ball the error is zero and
the
right-hand side is still nonnegative.  The two cases are therefore covered by a *single* bound with
no indicator and no tail set at all — and since `x^{2k}` is already the quantity the even-moment
estimates control, no Cauchy--Schwarz step is needed to connect them. -/

/-- **Indicator-free comparison.**  The truncation error is controlled by the even moment. -/
theorem abs_pow_sub_truncPow_le_even (hR : 0 < R) (k : ℕ) (x : ℝ) :
    |x ^ k - truncPow R k x| ≤ 2 * x ^ (2 * k) / R ^ k := by
  have hRk : (0 : ℝ) < R ^ k := pow_pos hR k
  have hsq : x ^ (2 * k) = (x ^ k) ^ (2 : ℕ) := by rw [mul_comm, pow_mul]
  have hxk2 : (x ^ k) ^ (2 : ℕ) = (|x| ^ k) ^ (2 : ℕ) := by rw [← abs_pow, sq_abs]
  by_cases hx : x ∈ Set.Icc (-R) R
  · rw [abs_pow_sub_truncPow_eq_zero_of_mem R k hx, abs_zero, hsq]
    positivity
  · have hxabs : R ≤ |x| := by
      simp only [Set.mem_Icc, ← abs_le, not_le] at hx
      exact hx.le
    have hRk_le : R ^ k ≤ |x| ^ k := pow_le_pow_left₀ hR.le hxabs k
    have habs : (0 : ℝ) ≤ |x| ^ k := pow_nonneg (abs_nonneg x) k
    have htri : |x ^ k - truncPow R k x| ≤ |x| ^ k + |x| ^ k := by
      have h := norm_sub_le (x ^ k) (truncPow R k x)
      rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, abs_pow] at h
      linarith [abs_truncPow_le_abs_pow hR.le k hxabs]
    rw [hsq, hxk2, le_div_iff₀ hRk]
    nlinarith [htri, hRk_le, habs, abs_nonneg (x ^ k - truncPow R k x)]

open MeasureTheory in
/-- **The integrated comparison.**  Against any measure, the truncated integral differs from the
true one by at most `2 · (even moment) / Rᵏ`. -/
theorem abs_integral_sub_integral_truncPow_le {μ : Measure ℝ} (hR : 0 < R) (k : ℕ)
    (h1 : Integrable (fun x : ℝ => x ^ k) μ) (h2 : Integrable (truncPow R k) μ)
    (h3 : Integrable (fun x : ℝ => x ^ (2 * k)) μ) :
    |∫ x, x ^ k ∂μ - ∫ x, truncPow R k x ∂μ| ≤ 2 * (∫ x, x ^ (2 * k) ∂μ) / R ^ k := by
  have hsub : Integrable (fun x : ℝ => x ^ k - truncPow R k x) μ := h1.sub h2
  have hbd : Integrable (fun x : ℝ => 2 * x ^ (2 * k) / R ^ k) μ :=
    (h3.const_mul 2).div_const (R ^ k)
  calc |∫ x, x ^ k ∂μ - ∫ x, truncPow R k x ∂μ|
      = |∫ x, (x ^ k - truncPow R k x) ∂μ| := by rw [integral_sub h1 h2]
    _ ≤ ∫ x, |x ^ k - truncPow R k x| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ x, 2 * x ^ (2 * k) / R ^ k ∂μ :=
        integral_mono hsub.abs hbd fun x => abs_pow_sub_truncPow_le_even hR k x
    _ = 2 * (∫ x, x ^ (2 * k) ∂μ) / R ^ k := by
        rw [integral_div, integral_const_mul]

end HTGeometry
