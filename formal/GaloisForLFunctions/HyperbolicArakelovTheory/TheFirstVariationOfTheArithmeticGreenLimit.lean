import GaloisForLFunctions.HyperbolicArakelovTheory.TheArithmeticGreenLimitIsAnOrderedSobolevLimit

/-!
# The first variation of the arithmetic Green limit

The normalized defect of the coupled Green energy converges to a positive
jump form with kernel `exp(-5|t|/2)/(1-exp(-2|t|))²`. Its value is bounded
by half the derivative energy and is strictly positive on every nonzero
compact smooth packet. Thus the linear damping-error scale is intrinsic.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set
open scoped Topology CompactlySupported

namespace GaloisForLFunctions.HyperbolicArakelovTheory
open SurfaceOfSpecZ _root_.RHTower _root_.RHTower.ArchimedeanAnomaly
open _root_.RHTower.ArchimedeanExactForm

/-- The divided Green difference, including its limiting value at damping one. -/
def greenResponseKernel (r x : ℝ) : ℝ :=
  Real.exp (-|x| / 2) * Real.exp (-2 * |x|) /
    ((1 - Real.exp (-2 * |x|)) * (1 - r ^ 2 * Real.exp (-2 * |x|)))

/-- The quadratic first variation of the renormalized Green energy. -/
def greenResponse (f : ℝ → ℝ) : ℝ :=
  ∫ x, greenResponseKernel 1 x * (autocorr f 0 - autocorr f x)

private theorem response_den_pos {x : ℝ} (hx : x ≠ 0) :
    0 < 1 - Real.exp (-2 * |x|) := by
  apply sub_pos.mpr
  rw [Real.exp_lt_one_iff]
  nlinarith only [abs_pos.mpr hx]

private theorem damping_gap_pos {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    0 < 1 - r ^ 2 := by
  nlinarith only [hr1, mul_nonneg hr0 (sub_pos.mpr hr1).le]

private theorem response_damped_den_pos {r x : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    0 < 1 - r ^ 2 * Real.exp (-2 * |x|) := by
  have he : Real.exp (-2 * |x|) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith only [abs_nonneg x])
  have h := mul_le_mul_of_nonneg_left he (sq_nonneg r)
  nlinarith only [h, damping_gap_pos hr0 hr1]

private theorem greenResponseKernel_eq {r x : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hx : x ≠ 0) :
    greenResponseKernel r x = (archProfile |x| - archDamped r x) / (1 - r ^ 2) := by
  apply (eq_div_iff (damping_gap_pos hr0 hr1).ne').mpr
  rw [greenResponseKernel, archProfile, archDamped,
    div_sub_div _ _ (response_den_pos hx).ne' (response_damped_den_pos hr0 hr1 (x := x)).ne',
    div_mul_eq_mul_div]
  congr 1
  ring

private theorem response_deficit_nonneg {f : ℝ → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (x : ℝ) : 0 ≤ autocorr f 0 - autocorr f x := by
  have h : (0 : ℝ) ≤ ∫ u : ℝ, (f u - f (u + x)) ^ 2 :=
    integral_nonneg (fun u => sq_nonneg (f u - f (u + x)))
  rw [integral_sub_shift_sq hfc hf] at h
  linarith only [h]

private theorem response_measurable {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (r : ℝ) :
    AEStronglyMeasurable (fun x => greenResponseKernel r x * (autocorr f 0 - autocorr f x)) := by
  have hk : Measurable (greenResponseKernel r) := by
    unfold greenResponseKernel
    fun_prop
  exact hk.aestronglyMeasurable.mul
    (continuous_const.sub (continuous_autocorr hf hfc)).aestronglyMeasurable

private theorem response_integrand_bounds (f : C_c(ℝ, ℝ))
    (hf : ContDiff ℝ 2 (f : ℝ → ℝ)) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (x : ℝ) :
    0 ≤ greenResponseKernel r x * (autocorr f 0 - autocorr f x) ∧
      greenResponseKernel r x * (autocorr f 0 - autocorr f x) ≤
        (∫ u, (deriv (f : ℝ → ℝ) u) ^ 2) / 8 * Real.exp (-(1 / 2 * |x|)) := by
  by_cases hx : x = 0
  · subst x
    simp only [sub_self, mul_zero, le_refl, true_and, abs_zero, mul_zero, neg_zero,
      Real.exp_zero, mul_one]
    exact div_nonneg (integral_nonneg fun _ => sq_nonneg _) (by norm_num)
  have hk : 0 ≤ archProfile |x| - archDamped r x :=
    sub_nonneg.mpr (archDamped_le_archProfile hr0 hr1.le hx)
  have hδ := damping_gap_pos hr0 hr1
  rw [greenResponseKernel_eq hr0 hr1 hx]
  constructor
  · exact mul_nonneg (div_nonneg hk hδ.le)
      (response_deficit_nonneg f.continuous f.hasCompactSupport x)
  · have hd := BiScaleUncertainty.autocorr_origin_deficit_le_derivative_energy f hf x
    have hm := mul_le_mul_of_nonneg_left hd hk
    have hH : 0 ≤ ∫ u, (deriv (f : ℝ → ℝ) u) ^ 2 :=
      integral_nonneg fun _ => sq_nonneg _
    have hb := mul_le_mul_of_nonneg_right (sq_mul_archProfile_sub_archDamped_le hr0 hr1 x) hH
    rw [div_mul_eq_mul_div, div_le_iff₀ hδ]
    rw [show -(1 / 2 * |x|) = -|x| / 2 by ring]
    nlinarith only [hm, hb]

private theorem tendsto_response_integrand (f : ℝ → ℝ) (x : ℝ) :
    Tendsto (fun r => greenResponseKernel r x * (autocorr f 0 - autocorr f x))
      (𝓝[<] 1) (𝓝 (greenResponseKernel 1 x * (autocorr f 0 - autocorr f x))) := by
  by_cases hx : x = 0
  · subst x
    simpa only [sub_self, mul_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[<] 1) (𝓝 0))
  have hd : (1 - Real.exp (-2 * |x|)) * (1 - (1 : ℝ) ^ 2 * Real.exp (-2 * |x|)) ≠ 0 := by
    simpa only [one_pow, one_mul] using mul_ne_zero (response_den_pos hx).ne'
      (response_den_pos hx).ne'
  have hc : ContinuousAt (fun r => greenResponseKernel r x) 1 := by
    unfold greenResponseKernel
    exact continuousAt_const.div (by fun_prop) hd
  exact (hc.tendsto.mono_left nhdsWithin_le_nhds).mul_const _

private theorem eventually_damping : ∀ᶠ r : ℝ in 𝓝[<] 1, 0 ≤ r ∧ r < 1 := by
  have h0 : ∀ᶠ r : ℝ in 𝓝[<] 1, 0 < r :=
    nhdsWithin_le_nhds (lt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [h0, self_mem_nhdsWithin] with r hr0 hr1
  exact ⟨hr0.le, hr1⟩

private theorem response_limit_bounds (f : C_c(ℝ, ℝ))
    (hf : ContDiff ℝ 2 (f : ℝ → ℝ)) (x : ℝ) :
    0 ≤ greenResponseKernel 1 x * (autocorr f 0 - autocorr f x) ∧
      greenResponseKernel 1 x * (autocorr f 0 - autocorr f x) ≤
        (∫ u, (deriv (f : ℝ → ℝ) u) ^ 2) / 8 * Real.exp (-(1 / 2 * |x|)) := by
  have h := eventually_damping.mono fun r hr => response_integrand_bounds f hf hr.1 hr.2 x
  exact ⟨ge_of_tendsto (tendsto_response_integrand f x) (h.mono fun _ h => h.1),
    le_of_tendsto (tendsto_response_integrand f x) (h.mono fun _ h => h.2)⟩

theorem integrable_greenResponse (f : C_c(ℝ, ℝ)) (hf : ContDiff ℝ 2 (f : ℝ → ℝ)) :
    Integrable (fun x => greenResponseKernel 1 x * (autocorr f 0 - autocorr f x)) := by
  apply ((integrable_exp_neg_mul_abs (a := 1 / 2) (by norm_num)).const_mul
    ((∫ u, (deriv (f : ℝ → ℝ) u) ^ 2) / 8)).mono'
    (response_measurable hf f.hasCompactSupport 1)
  exact Eventually.of_forall fun x => by
    rw [Real.norm_of_nonneg (response_limit_bounds f hf x).1]
    exact (response_limit_bounds f hf x).2

/-- The first variation is finite and bounded by half the derivative energy. -/
theorem greenResponse_bounds (f : C_c(ℝ, ℝ)) (hf : ContDiff ℝ 2 (f : ℝ → ℝ)) :
    0 ≤ greenResponse f ∧ greenResponse f ≤ (∫ u, (deriv (f : ℝ → ℝ) u) ^ 2) / 2 := by
  refine ⟨integral_nonneg fun x => (response_limit_bounds f hf x).1, ?_⟩
  have h := integral_mono (integrable_greenResponse f hf)
    ((integrable_exp_neg_mul_abs (a := 1 / 2) (by norm_num)).const_mul
      ((∫ u, (deriv (f : ℝ → ℝ) u) ^ 2) / 8))
    (fun x => (response_limit_bounds f hf x).2)
  rw [integral_const_mul,
    SurfaceOfSpecZ.integral_exp_neg_mul_abs (by norm_num : (0 : ℝ) < 1 / 2)] at h
  change greenResponse f ≤ _ at h
  linarith only [h]

private theorem integral_response_eq (f : C_c(ℝ, ℝ)) (hf : ContDiff ℝ 2 (f : ℝ → ℝ))
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∫ x, greenResponseKernel r x * (autocorr f 0 - autocorr f x)) =
      (levyEnergy f - dampedJumpEnergy r f) / (1 - r ^ 2) := by
  have he (x : ℝ) : greenResponseKernel r x * (autocorr f 0 - autocorr f x) =
      (archProfile |x| * (autocorr f 0 - autocorr f x) -
        archDamped r x * (autocorr f 0 - autocorr f x)) / (1 - r ^ 2) := by
    by_cases hx : x = 0
    · subst x; simp only [sub_self, mul_zero, zero_div]
    · rw [greenResponseKernel_eq hr0 hr1 hx]
      ring
  simp_rw [he]
  rw [integral_div, integral_sub (smoothGreen_deficit f hf f.hasCompactSupport).1
    (integrable_dampedJump hf f.hasCompactSupport hr0 hr1),
    (smoothGreen_deficit f hf f.hasCompactSupport).2]
  rfl

/-- Dividing by the damping gap reveals a nontrivial limiting jump form. -/
theorem tendsto_normalized_Green_deficit (f : C_c(ℝ, ℝ))
    (hf : ContDiff ℝ 2 (f : ℝ → ℝ)) :
    Tendsto (fun r => (levyEnergy f - dampedJumpEnergy r f) / (1 - r ^ 2))
      (𝓝[<] 1) (𝓝 (greenResponse f)) := by
  have h := tendsto_integral_filter_of_dominated_convergence
    (fun x => (∫ u, (deriv (f : ℝ → ℝ) u) ^ 2) / 8 * Real.exp (-(1 / 2 * |x|)))
    (Eventually.of_forall fun r => response_measurable hf f.hasCompactSupport r)
    (eventually_damping.mono fun r hr => Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (response_integrand_bounds f hf hr.1 hr.2 x).1]
      exact (response_integrand_bounds f hf hr.1 hr.2 x).2)
    ((integrable_exp_neg_mul_abs (a := 1 / 2) (by norm_num)).const_mul _)
    (Eventually.of_forall (tendsto_response_integrand f))
  exact h.congr' (eventually_damping.mono fun r hr => integral_response_eq f hf hr.1 hr.2)

/-- Every nonzero compact packet has positive first variation, including sign-changing packets. -/
theorem greenResponse_pos (f : C_c(ℝ, ℝ)) (hf : ContDiff ℝ 2 (f : ℝ → ℝ))
    (hne : f ≠ 0) : 0 < greenResponse f := by
  have hmass := BiScaleUncertainty.nyquistSourceMass_pos f hne
  obtain ⟨B, hB⟩ := (hasCompactSupport_autocorr f.hasCompactSupport).bddAbove
  let a := max B 0 + 1
  have hs : Ioo a (a + 1) ⊆ Function.support
      (fun x => greenResponseKernel 1 x * (autocorr f 0 - autocorr f x)) := by
    intro x hx
    have hx0 : 0 < x := by
      have h := le_max_right B 0
      dsimp only [a] at hx
      linarith only [hx.1, h]
    have hxB : B < x := by
      have h := le_max_left B 0
      dsimp only [a] at hx
      linarith only [hx.1, h]
    have hz : autocorr f x = 0 := by
      by_contra hn
      exact (not_le_of_gt hxB) (hB (subset_closure (Function.mem_support.mpr hn)))
    have hk : 0 < greenResponseKernel 1 x := by
      unfold greenResponseKernel
      simp only [one_pow, one_mul]
      exact div_pos (mul_pos (Real.exp_pos _) (Real.exp_pos _))
        (mul_pos (response_den_pos hx0.ne') (response_den_pos hx0.ne'))
    exact Function.mem_support.mpr (by rw [hz, sub_zero]; exact (mul_pos hk hmass).ne')
  apply (integral_pos_iff_support_of_nonneg
    (fun x => (response_limit_bounds f hf x).1) (integrable_greenResponse f hf)).mpr
  have hI : (Ioo a (a + 1)).Nonempty := ⟨a + 1 / 2, by constructor <;> linarith⟩
  exact (isOpen_Ioo.measure_pos volume hI).trans_le (measure_mono hs)

namespace PrimeSuspension
open SpacingScaleHarmonicAnalysis

/-- Arithmetic locking preserves the exact first variation of the hyperbolic Green channel. -/
theorem tendsto_normalized_coupledGreen_defect (f : C_c(ℝ, ℝ))
    (hf : ContDiff ℝ 2 (f : ℝ → ℝ)) :
    Tendsto (fun r => (weilQuad f - coupledGreenEnergy r f) / (1 - r ^ 2))
      (𝓝[<] 1) (𝓝 (greenResponse f)) := by
  obtain ⟨R, _, hR⟩ := f.hasCompactSupport.exists_pos_le_norm
  have hfR : SupportedIn R f := fun x hx => hR x (by simpa only [Real.norm_eq_abs] using hx.le)
  have hc := tendsto_arithmeticClock_atTop.eventually
    (eventually_ge_atTop (cumulativeCapacity (lagRange R)))
  apply (tendsto_normalized_Green_deficit f hf).congr'
  filter_upwards [eventually_damping, hc] with r hr hclock
  rw [weilQuad_sub_coupledGreenEnergy_eq hf f.hasCompactSupport hfR hr.1 hr.2 hclock]

/-- On each nonzero packet the damping gap is the exact order of the Weil error. -/
theorem coupledGreen_defect_exact_order (f : C_c(ℝ, ℝ))
    (hf : ContDiff ℝ 2 (f : ℝ → ℝ)) (hne : f ≠ 0) :
    ∀ᶠ r : ℝ in 𝓝[<] 1,
      (1 - r ^ 2) * (greenResponse f / 2) < weilQuad f - coupledGreenEnergy r f ∧
        weilQuad f - coupledGreenEnergy r f < (1 - r ^ 2) * (2 * greenResponse f) := by
  have hpos := greenResponse_pos f hf hne
  have h := (tendsto_normalized_coupledGreen_defect f hf).eventually
    (Ioo_mem_nhds (by linarith only [hpos] : greenResponse f / 2 < greenResponse f)
      (by linarith only [hpos] : greenResponse f < 2 * greenResponse f))
  filter_upwards [h, eventually_damping] with r hb hr
  have hδ := damping_gap_pos hr.1 hr.2
  exact ⟨by simpa only [mul_comm] using (lt_div_iff₀ hδ).mp hb.1,
    by simpa only [mul_comm] using (div_lt_iff₀ hδ).mp hb.2⟩

end PrimeSuspension

#print axioms greenResponse_bounds
#print axioms greenResponse_pos
#print axioms PrimeSuspension.tendsto_normalized_coupledGreen_defect
#print axioms PrimeSuspension.coupledGreen_defect_exact_order

end GaloisForLFunctions.HyperbolicArakelovTheory
