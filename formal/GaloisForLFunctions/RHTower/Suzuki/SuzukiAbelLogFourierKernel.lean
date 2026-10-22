import GaloisForLFunctions.HTGeometry.HyperbolicLevyKhintchine
import GaloisForLFunctions.HTGeometry.WaveTraceLaplace

/-!
# Abel-regularized logarithmic Fourier kernel

Suzuki's proof of the logarithmic finite-part identity invokes the Fourier transform of
`|t|⁻¹ 1_{|t| > ε}`.  That kernel is not integrable at infinity, so its Fourier transform is not an
ordinary Lebesgue Fourier integral.  This module supplies the rigorous Abel replacement:

`∫₀∞ exp (-δt) (1 - cos (bt)) / t dt = 1/2 log (1 + (b/δ)²)`.

Cancellation at the origin and exponential decay make every integral literal.  The proof
differentiates under the integral sign, evaluates the resulting sine Laplace transform, and fixes
the integration constant at frequency zero.
-/

open Complex Filter MeasureTheory Set
open scoped Topology

namespace RHTower

noncomputable section

/-- Positive Abel regularization scale, packaged so public endpoints carry no proof premise. -/
abbrev SuzukiAbelPositiveScale := {delta : ℝ // 0 < delta}

/-- Abel-regularized logarithmic kernel at frequency `b` and positive time `t`. -/
def abelLogKernelIntegrand (delta b t : ℝ) : ℝ :=
  Real.exp (-(delta * t)) * (1 - Real.cos (b * t)) / t

/-- Frequency derivative of `abelLogKernelIntegrand` away from `t = 0`. -/
def abelLogKernelDerivIntegrand (delta b t : ℝ) : ℝ :=
  Real.exp (-(delta * t)) * Real.sin (b * t)

/-- Abel-regularized logarithmic multiplier. -/
def abelLogKernelIntegral (delta b : ℝ) : ℝ :=
  ∫ t : ℝ in Ioi 0, abelLogKernelIntegrand delta b t

private theorem integrableOn_id_mul_exp_neg {delta : ℝ} (hdelta : 0 < delta) :
    IntegrableOn (fun t : ℝ => t * Real.exp (-(delta * t))) (Ioi 0) := by
  have hvalue := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (2 : ℝ)) (r := delta) (by norm_num) hdelta
  have hne :
      (∫ t : ℝ in Ioi 0, t ^ ((2 : ℝ) - 1) * Real.exp (-(delta * t))) ≠ 0 := by
    rw [hvalue]
    positivity
  have hint : IntegrableOn
      (fun t : ℝ => t ^ ((2 : ℝ) - 1) * Real.exp (-(delta * t))) (Ioi 0) :=
    Integrable.of_integral_ne_zero hne
  convert hint using 1
  funext t
  norm_num [Real.rpow_one]

/-- Cancellation at the origin and Abel decay make the logarithmic kernel integrable. -/
theorem integrableOn_abelLogKernelIntegrand {delta b : ℝ} (hdelta : 0 < delta) :
    IntegrableOn (abelLogKernelIntegrand delta b) (Ioi 0) := by
  have hdom := (integrableOn_id_mul_exp_neg hdelta).const_mul (|b| ^ 2 / 2)
  refine hdom.mono' ?_ ?_
  · exact (by
      unfold abelLogKernelIntegrand
      measurability : Measurable _).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htpos : 0 < t := ht
    have ht0 : 0 ≤ t := htpos.le
    have hexp0 : 0 ≤ Real.exp (-(delta * t)) := (Real.exp_pos _).le
    have hnum0 : 0 ≤ 1 - Real.cos (b * t) := sub_nonneg.mpr (Real.cos_le_one _)
    rw [abelLogKernelIntegrand, Real.norm_eq_abs, abs_div, abs_mul,
      abs_of_pos (Real.exp_pos _), abs_of_nonneg hnum0, abs_of_pos ht]
    have hquad := HTGeometry.one_sub_cos_le_sq_div_two (b * t)
    calc
      Real.exp (-(delta * t)) * (1 - Real.cos (b * t)) / t ≤
          Real.exp (-(delta * t)) * ((b * t) ^ 2 / 2) / t := by gcongr
      _ = |b| ^ 2 / 2 * (t * Real.exp (-(delta * t))) := by
        rw [sq_abs]
        field_simp [htpos.ne']

/-- The frequency derivative of the Abel kernel is integrable on the positive ray. -/
theorem integrableOn_abelLogKernelDerivIntegrand {delta b : ℝ} (hdelta : 0 < delta) :
    IntegrableOn (abelLogKernelDerivIntegrand delta b) (Ioi 0) := by
  have hdom : IntegrableOn (fun t : ℝ => Real.exp (-delta * t)) (Ioi 0) :=
    exp_neg_integrableOn_Ioi 0 hdelta
  refine hdom.mono' ?_ ?_
  · exact (by
      unfold abelLogKernelDerivIntegrand
      measurability : Measurable _).aestronglyMeasurable
  · filter_upwards with t
    rw [abelLogKernelDerivIntegrand, Real.norm_eq_abs, abs_mul,
      abs_of_pos (Real.exp_pos _)]
    have hsin := Real.abs_sin_le_one (b * t)
    simpa only [neg_mul, mul_one] using
      mul_le_mul_of_nonneg_left hsin (Real.exp_pos (-(delta * t))).le

/-- Pointwise frequency derivative of the Abel kernel. -/
theorem hasDerivAt_abelLogKernelIntegrand {delta b t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun x => abelLogKernelIntegrand delta x t)
      (abelLogKernelDerivIntegrand delta b t) b := by
  unfold abelLogKernelIntegrand abelLogKernelDerivIntegrand
  have hlin : HasDerivAt (fun x : ℝ => x * t) t b :=
    by simpa only [id_eq, one_mul] using (hasDerivAt_id b).mul_const t
  have hnum := (hasDerivAt_const b (1 : ℝ)).sub hlin.cos
  have hprod := (hnum.const_mul (Real.exp (-(delta * t)))).div_const t
  refine hprod.congr_deriv ?_
  field_simp [ht.ne']
  ring

/-- Differentiation under the Abel logarithmic integral. -/
theorem hasDerivAt_abelLogKernelIntegral {delta b : ℝ} (hdelta : 0 < delta) :
    HasDerivAt (abelLogKernelIntegral delta)
      (∫ t : ℝ in Ioi 0, abelLogKernelDerivIntegrand delta b t) b := by
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi 0))
    (F := fun x t => abelLogKernelIntegrand delta x t)
    (F' := fun x t => abelLogKernelDerivIntegrand delta x t)
    (bound := fun t => Real.exp (-(delta * t)))
    (x₀ := b) (s := Set.univ)
    Filter.univ_mem
    (Filter.Eventually.of_forall fun x => (by
      unfold abelLogKernelIntegrand
      measurability : Measurable _).aestronglyMeasurable)
    (integrableOn_abelLogKernelIntegrand hdelta)
    ((by
      unfold abelLogKernelDerivIntegrand
      measurability : Measurable _).aestronglyMeasurable)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      intro x hx
      rw [abelLogKernelDerivIntegrand, Real.norm_eq_abs, abs_mul,
        abs_of_pos (Real.exp_pos _)]
      exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_sin_le_one _))
    (by
      change IntegrableOn (fun t : ℝ => Real.exp (-(delta * t))) (Ioi 0)
      convert exp_neg_integrableOn_Ioi 0 hdelta using 1
      ring_nf)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      intro x hx
      exact hasDerivAt_abelLogKernelIntegrand ht)
  exact h.2

/-- Exact real sine Laplace transform, obtained from the already formalized complex transform. -/
theorem integral_Ioi_exp_neg_mul_sin {delta b : ℝ} (hdelta : 0 < delta) :
    (∫ t : ℝ in Ioi 0, Real.exp (-(delta * t)) * Real.sin (b * t)) =
      b / (delta ^ 2 + b ^ 2) := by
  have h := GaloisForLFunctions.HTGeometry.integral_sin_mul_exp
    (gamma := (b : ℂ)) (s := (delta : ℂ)) (by simpa using hdelta)
  have hpoint :
      (fun t : ℝ => Complex.sin ((b : ℂ) * (t : ℂ)) *
        Complex.exp (-(delta : ℂ) * (t : ℂ))) =
      (fun t : ℝ => ((Real.exp (-(delta * t)) * Real.sin (b * t) : ℝ) : ℂ)) := by
    funext t
    push_cast
    ring
  rw [hpoint, integral_complex_ofReal] at h
  have hre := congrArg Complex.re h
  norm_cast at hre

/-- The differentiated Abel multiplier is the elementary resolvent frequency. -/
theorem integral_abelLogKernelDerivIntegrand {delta b : ℝ} (hdelta : 0 < delta) :
    (∫ t : ℝ in Ioi 0, abelLogKernelDerivIntegrand delta b t) =
      b / (delta ^ 2 + b ^ 2) := by
  simpa only [abelLogKernelDerivIntegrand] using integral_Ioi_exp_neg_mul_sin hdelta

private theorem hasDerivAt_half_log_one_add_div_sq {delta b : ℝ} (hdelta : 0 < delta) :
    HasDerivAt (fun x : ℝ => (1 / 2 : ℝ) * Real.log (1 + (x / delta) ^ 2))
      (b / (delta ^ 2 + b ^ 2)) b := by
  have hlin : HasDerivAt (fun x : ℝ => x / delta) (1 / delta) b :=
    (hasDerivAt_id b).div_const delta
  have hinnerRaw := (hasDerivAt_const b (1 : ℝ)).add (hlin.pow 2)
  have hinnerDeriv : HasDerivAt _ (2 * (b / delta) * (1 / delta)) b :=
    hinnerRaw.congr_deriv (by norm_num)
  have hinner : HasDerivAt (fun x : ℝ => 1 + (x / delta) ^ 2)
      (2 * (b / delta) * (1 / delta)) b :=
    hinnerDeriv.congr_of_eventuallyEq
      (f₁ := fun x : ℝ => 1 + (x / delta) ^ 2)
      (Filter.Eventually.of_forall fun x => rfl)
  have hpos : 0 < 1 + (b / delta) ^ 2 := by positivity
  have hlog : HasDerivAt (fun x : ℝ => Real.log (1 + (x / delta) ^ 2))
      ((2 * (b / delta) * (1 / delta)) / (1 + (b / delta) ^ 2)) b :=
    hinner.log hpos.ne'
  have hhalf : HasDerivAt
      (fun x : ℝ => (1 / 2 : ℝ) * Real.log (1 + (x / delta) ^ 2))
      ((1 / 2 : ℝ) *
        ((2 * (b / delta) * (1 / delta)) / (1 + (b / delta) ^ 2))) b :=
    hlog.const_mul (1 / 2 : ℝ)
  refine hhalf.congr_deriv ?_
  field_simp [hdelta.ne']

/-- Abel-regularized logarithmic Fourier kernel (Frullani identity). -/
theorem integral_abelLogKernel_eq_half_log_one_add_div_sq_of_pos
    {delta : ℝ} (hdelta : 0 < delta) (b : ℝ) :
    abelLogKernelIntegral delta b =
      (1 / 2 : ℝ) * Real.log (1 + (b / delta) ^ 2) := by
  let f : ℝ → ℝ := abelLogKernelIntegral delta
  let g : ℝ → ℝ := fun x => (1 / 2 : ℝ) * Real.log (1 + (x / delta) ^ 2)
  have hfderiv : ∀ x, HasDerivAt f (x / (delta ^ 2 + x ^ 2)) x := by
    intro x
    have h := hasDerivAt_abelLogKernelIntegral (b := x) hdelta
    rw [integral_abelLogKernelDerivIntegrand hdelta] at h
    exact h
  have hgderiv : ∀ x, HasDerivAt g (x / (delta ^ 2 + x ^ 2)) x := by
    intro x
    exact hasDerivAt_half_log_one_add_div_sq hdelta
  have hf : Differentiable ℝ f := fun x => (hfderiv x).differentiableAt
  have hg : Differentiable ℝ g := fun x => (hgderiv x).differentiableAt
  have hfd : ∀ x, fderiv ℝ f x = fderiv ℝ g x := by
    intro x
    ext
    rw [fderiv_eq_smul_deriv, fderiv_eq_smul_deriv,
      (hfderiv x).deriv, (hgderiv x).deriv]
  have hzero : f 0 = g 0 := by
    simp [f, g, abelLogKernelIntegral, abelLogKernelIntegrand]
  have heq := eq_of_fderiv_eq hf hg hfd 0 hzero
  exact congrFun heq b

/-- Premise-free positive-scale form of the Abel logarithmic kernel identity. -/
theorem integral_abelLogKernel_eq_half_log_one_add_div_sq
    (delta : SuzukiAbelPositiveScale) (b : ℝ) :
    abelLogKernelIntegral delta.1 b =
      (1 / 2 : ℝ) * Real.log (1 + (b / delta.1) ^ 2) :=
  integral_abelLogKernel_eq_half_log_one_add_div_sq_of_pos delta.2 b

/-- The renormalized Abel multiplier is exactly a nonsingular logarithmic multiplier. -/
theorem abelLogKernelIntegral_add_log_eq_half_log_add_sq_of_pos
    {delta : ℝ} (hdelta : 0 < delta) (b : ℝ) :
    abelLogKernelIntegral delta b + Real.log delta =
      (1 / 2 : ℝ) * Real.log (delta ^ 2 + b ^ 2) := by
  rw [integral_abelLogKernel_eq_half_log_one_add_div_sq_of_pos hdelta]
  have hfrac : 1 + (b / delta) ^ 2 = (delta ^ 2 + b ^ 2) / delta ^ 2 := by
    field_simp [hdelta.ne']
  rw [hfrac, Real.log_div (by positivity) (by positivity), Real.log_pow]
  ring

/-- Nonzero frequency packaged so the logarithmic boundary limit is unconditional. -/
abbrev SuzukiNonzeroFrequency := {b : ℝ // b ≠ 0}

/-- The renormalized Abel multiplier converges to the exact logarithmic Fourier multiplier. -/
theorem tendsto_abelLogKernelIntegral_add_log_nhdsGT_zero
    (b : SuzukiNonzeroFrequency) :
    Tendsto (fun delta : ℝ => abelLogKernelIntegral delta b.1 + Real.log delta)
      (𝓝[>] 0) (𝓝 (Real.log |b.1|)) := by
  have hcongr :
      (fun delta : ℝ => abelLogKernelIntegral delta b.1 + Real.log delta) =ᶠ[𝓝[>] 0]
        (fun delta : ℝ => (1 / 2 : ℝ) * Real.log (delta ^ 2 + b.1 ^ 2)) := by
    filter_upwards [self_mem_nhdsWithin] with delta hdelta
    exact abelLogKernelIntegral_add_log_eq_half_log_add_sq_of_pos hdelta b.1
  have hb2 : b.1 ^ 2 ≠ 0 := pow_ne_zero 2 b.2
  have hinside : ContinuousAt (fun delta : ℝ => delta ^ 2 + b.1 ^ 2) 0 := by
    fun_prop
  have hinside0 : (fun delta : ℝ => delta ^ 2 + b.1 ^ 2) 0 = b.1 ^ 2 := by
    norm_num
  have hcont : ContinuousAt
      (fun delta : ℝ => (1 / 2 : ℝ) * Real.log (delta ^ 2 + b.1 ^ 2)) 0 :=
    continuousAt_const.mul
      ((Real.continuousAt_log hb2).comp_of_eq hinside hinside0)
  have hvalue :
      (1 / 2 : ℝ) * Real.log ((0 : ℝ) ^ 2 + b.1 ^ 2) = Real.log |b.1| := by
    rw [zero_pow (by norm_num : 2 ≠ 0), zero_add, Real.log_pow, Real.log_abs]
    ring
  have hlim : Tendsto
      (fun delta : ℝ => (1 / 2 : ℝ) * Real.log (delta ^ 2 + b.1 ^ 2))
      (𝓝[>] 0) (𝓝 (Real.log |b.1|)) := by
    rw [← hvalue]
    exact hcont.continuousWithinAt
  exact (tendsto_congr' hcongr).2 hlim

end

end RHTower
