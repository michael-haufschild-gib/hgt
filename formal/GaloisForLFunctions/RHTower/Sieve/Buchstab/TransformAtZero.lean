import GaloisForLFunctions.RHTower.MertensProductLaplace
import GaloisForLFunctions.RHTower.ExponentialIntegralE1Quantile
import GaloisForLFunctions.RHTower.PrimeVacuumPoleCancellation

/-!
# The Buchstab transform and the prime aperture

The positive-axis expression in Weingartner's Lemma 1 (arXiv:2607.21883)
is `exp(E₁(s)) - 1`. Removing its pole gives a differentiable extension
whose slope determines the finite part. Taking its reciprocal gives the
slope of the prime-aperture retention quantile at zero.
-/

namespace RHTower.Sieve.Buchstab
open RHTower Set Filter Topology

noncomputable section

/-- The positive-axis transform expression in terms of the exponential integral. -/
def transform (s : ℝ) : ℝ := Real.exp (expIntegralOne s) - 1

/-- Regularization of `s * (1 + transform s)` through the origin. -/
def regular (s : ℝ) : ℝ := Real.exp (einCompare s - Real.eulerMascheroniConstant)

theorem expIntegralOne_eq_regular_log {s : ℝ} (hs : 0 < s) :
    expIntegralOne s = einCompare s - Real.eulerMascheroniConstant - Real.log s := by
  rw [einCompare_eq_ein hs.le, expIntegralOne]
  rcases le_total s 1 with h | h
  · rw [integral_expNegDiv_Ioi_small hs h]
    ring
  · rw [ein_eq_eulerMascheroni_add_log_add_tail h]
    ring

/-- Exact desingularization for every positive real argument. -/
theorem regular_eq_mul (s : Set.Ioi (0 : ℝ)) :
    regular s = s.val * (1 + transform s) := by
  simp only [transform, add_sub_cancel]
  rw [expIntegralOne_eq_regular_log s.property, Real.exp_sub, Real.exp_log s.property]
  change regular s.val = s.val * (regular s.val / s.val)
  field_simp [s.property.ne']

theorem regular_zero : regular 0 = Real.exp (-Real.eulerMascheroniConstant) := by
  simp [regular, einCompare]

/-- The desingularized transform solves an ordinary differential equation across zero. -/
theorem hasDerivAt_regular (s : ℝ) :
    HasDerivAt regular (regular s * einKernel s) s :=
  ((hasDerivAt_einCompare s).sub_const Real.eulerMascheroniConstant).exp

theorem hasDerivAt_regular_zero :
    HasDerivAt regular (Real.exp (-Real.eulerMascheroniConstant)) 0 := by
  simpa [regular_zero, einKernel, logIntegralKernel_zero] using hasDerivAt_regular 0

/-- The residue of the transform on the positive ray. -/
theorem tendsto_mul_transform_zero :
    Tendsto (fun s => s * transform s) (𝓝[>] 0) (𝓝 (Real.exp (-Real.eulerMascheroniConstant))) := by
  have h := (hasDerivAt_regular_zero.sub (hasDerivAt_id (0 : ℝ))).continuousAt.tendsto
  rw [id_eq, sub_zero, regular_zero] at h
  refine (h.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  change regular s - s = s * transform s
  rw [regular_eq_mul ⟨s, hs⟩]
  ring

/-- The constant term after subtracting the pole is its residue minus one. -/
theorem tendsto_transform_finitePart :
    Tendsto (fun s => transform s - Real.exp (-Real.eulerMascheroniConstant) / s)
      (𝓝[>] 0) (𝓝 (Real.exp (-Real.eulerMascheroniConstant) - 1)) := by
  have h := hasDerivAt_regular_zero.tendsto_slope_zero_right
  refine (h.sub_const 1).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs0 : 0 < s := hs
  have he := regular_eq_mul ⟨s, hs0⟩
  change (s⁻¹ • (regular (0 + s) - regular 0)) - 1 =
    transform s - Real.exp (-Real.eulerMascheroniConstant) / s
  rw [zero_add, regular_zero, smul_eq_mul, he]
  field_simp [hs0.ne']
  <;> ring

/-- The retention quantile is the reciprocal of the shifted transform. -/
theorem retention_mul_transform (s : ℝ) :
    retentionQuantile s * (1 + transform s) = 1 := by
  simp only [retentionQuantile, transform, add_sub_cancel]
  rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]

/-- Analytic normalization gives the right-hand slope of the retention quantile. -/
theorem tendsto_retention_div_argument :
    Tendsto (fun s => retentionQuantile s / s) (𝓝[>] 0)
      (𝓝 (Real.exp Real.eulerMascheroniConstant)) := by
  have h := (hasDerivAt_regular_zero.hasDerivWithinAt (s := Ioi (0:ℝ))).continuousWithinAt.tendsto
  rw [regular_zero] at h
  have hi := h.inv₀ (Real.exp_pos _).ne'
  rw [← Real.exp_neg, neg_neg] at hi
  refine hi.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hr := retention_mul_transform s
  have hpos : 0 < 1 + transform s := by simpa [transform] using Real.exp_pos (expIntegralOne s)
  rw [regular_eq_mul ⟨s, hs⟩, mul_inv_rev]
  have he : (1 + transform s)⁻¹ = retentionQuantile s :=
    (eq_inv_of_mul_eq_one_left hr).symm
  rw [he, div_eq_mul_inv]

end
end RHTower.Sieve.Buchstab
