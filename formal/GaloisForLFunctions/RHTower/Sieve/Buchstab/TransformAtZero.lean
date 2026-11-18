import GaloisForLFunctions.RHTower.MertensProductLaplace
import GaloisForLFunctions.RHTower.ExponentialIntegralE1Quantile
import GaloisForLFunctions.RHTower.PrimeVacuumPoleCancellation
import Mathlib.Analysis.Convex.Deriv

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

private theorem one_add_transform (s : ℝ) : 1 + transform s = Real.exp (expIntegralOne s) := by
  unfold transform
  ring

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
  have hs : 0 < s.val := s.property
  rw [one_add_transform]
  rw [expIntegralOne_eq_regular_log s.property, Real.exp_sub, Real.exp_log s.property]
  change regular s.val = s.val * (regular s.val / s.val)
  field_simp [hs.ne']

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
  change Tendsto (fun s : ℝ => regular s-s) (𝓝 0) (𝓝 (regular 0-0)) at h
  rw [sub_zero, regular_zero] at h
  refine (h.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
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
  ring

/-- The retention quantile is the reciprocal of the shifted transform. -/
theorem retention_mul_transform (s : ℝ) :
    retentionQuantile s * (1 + transform s) = 1 := by
  rw [one_add_transform, retentionQuantile, ← Real.exp_add, neg_add_cancel, Real.exp_zero]

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
  rw [regular_eq_mul ⟨s, hs⟩, one_add_transform, mul_inv_rev, retentionQuantile,
    Real.exp_neg, div_eq_mul_inv]

/-- The desingularized retention quantile on the entire real line. -/
def apertureExtension (s : ℝ) : ℝ := s / regular s

/-- The positive-axis aperture density, continued through zero. -/
def apertureDensity (s : ℝ) : ℝ := Real.exp (-s) / regular s

private theorem regular_pos (s : ℝ) : 0 < regular s := Real.exp_pos _

theorem apertureExtension_eq_retention (s : Ioi (0:ℝ)) :
    apertureExtension s = retentionQuantile s := by
  rw [apertureExtension, div_eq_iff (regular_pos _).ne', regular_eq_mul s,
    mul_left_comm, retention_mul_transform, mul_one]

private theorem kernel_identity (s : ℝ) : 1-s*einKernel s = Real.exp (-s) := by
  by_cases hs : s = 0
  · simp [hs]
  · rw [einKernel,logIntegralKernel_of_ne hs]
    have he : Real.exp (-s)*Real.exp s = 1 := by rw [← Real.exp_add,neg_add_cancel,Real.exp_zero]
    calc
      _ = 1 - Real.exp (-s)*(Real.exp s-1) := by field_simp [hs]
      _ = _ := by linear_combination -he

/-- The reciprocal pole factor gives a globally positive derivative. -/
theorem hasDerivAt_apertureExtension (s : ℝ) : HasDerivAt apertureExtension (apertureDensity s) s := by
  have hh : HasDerivAt apertureExtension
      ((1 * regular s - s * (regular s * einKernel s)) / regular s ^ 2) s :=
    (hasDerivAt_id s).div (hasDerivAt_regular s) (regular_pos s).ne'
  convert hh using 1
  rw [apertureDensity, ← kernel_identity]
  field_simp [(regular_pos s).ne']

/-- The logarithmic decay rate of the aperture density is exactly `1 + Ein'(s)`. -/
theorem hasDerivAt_apertureDensity (s : ℝ) :
    HasDerivAt apertureDensity (-(apertureDensity s) * (1+einKernel s)) s := by
  have hh : HasDerivAt apertureDensity
      ((Real.exp (-s)*(-1) * regular s - Real.exp (-s) * (regular s * einKernel s)) /
        regular s ^ 2) s :=
    (hasDerivAt_id s).neg.exp.div (hasDerivAt_regular s) (regular_pos s).ne'
  convert hh using 1
  rw [apertureDensity]
  field_simp [(regular_pos s).ne']
  ring

theorem apertureDensity_strictAnti : StrictAnti apertureDensity := by
  apply strictAnti_of_deriv_neg
  intro s
  rw [(hasDerivAt_apertureDensity s).deriv]
  exact mul_neg_of_neg_of_pos (neg_lt_zero.mpr (div_pos (Real.exp_pos _) (regular_pos _)))
    (add_pos zero_lt_one (einKernel_pos s))

/-- The full real continuation is strictly concave, including across the pole location. -/
theorem apertureExtension_strictConcave : StrictConcaveOn ℝ univ apertureExtension := by
  apply strictConcaveOn_univ_of_deriv2_neg (continuous_iff_continuousAt.mpr
    fun x => (hasDerivAt_apertureExtension x).continuousAt)
  have hd : deriv apertureExtension = apertureDensity := funext fun x => (hasDerivAt_apertureExtension x).deriv
  intro x
  change deriv (deriv apertureExtension) x < 0
  rw [hd, (hasDerivAt_apertureDensity x).deriv]
  exact mul_neg_of_neg_of_pos (neg_lt_zero.mpr (div_pos (Real.exp_pos _) (regular_pos _)))
    (add_pos zero_lt_one (einKernel_pos x))

/-- The mass on a finite positive interval is the original retention fraction. -/
theorem apertureDensity_cumulative (s : Ioi (0:ℝ)) :
    (∫ x in (0:ℝ)..s.val, apertureDensity x) = retentionQuantile s := by
  have hc := continuous_iff_continuousAt.mpr (fun x => (hasDerivAt_apertureDensity x).continuousAt)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hasDerivAt_apertureExtension x) (hc.intervalIntegrable 0 s.val)]
  simp only [apertureExtension_eq_retention s, show apertureExtension 0 = 0 by simp [apertureExtension], sub_zero]

/-- Total positive-axis mass is one. -/
theorem tendsto_apertureDensity_cumulative :
    Tendsto (fun s => ∫ x in (0:ℝ)..s, apertureDensity x) atTop (𝓝 1) := by
  refine tendsto_retentionQuantile_atTop.congr' ?_
  filter_upwards [eventually_gt_atTop (0:ℝ)] with s hs
  exact (apertureDensity_cumulative ⟨s,hs⟩).symm

/-- The second derivative at the origin fixes the quadratic correction to retention. -/
theorem apertureDensity_slope_zero : HasDerivAt apertureDensity (-2*Real.exp Real.eulerMascheroniConstant) 0 := by
  have he : apertureDensity 0 = Real.exp Real.eulerMascheroniConstant := by
    simp [apertureDensity,regular_zero,Real.exp_neg]
  convert hasDerivAt_apertureDensity 0 using 1
  rw [he]
  simp [einKernel,logIntegralKernel_zero]
  ring

#print axioms tendsto_mul_transform_zero
#print axioms tendsto_transform_finitePart
#print axioms retention_mul_transform
#print axioms tendsto_retention_div_argument
#print axioms apertureExtension_strictConcave
#print axioms tendsto_apertureDensity_cumulative
#print axioms apertureDensity_slope_zero

end
end RHTower.Sieve.Buchstab
