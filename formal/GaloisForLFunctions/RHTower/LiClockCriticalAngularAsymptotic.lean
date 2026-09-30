import GaloisForLFunctions.RHTower.LiClockCriticalAngularKernel
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Exact scalar angular bounds and asymptotics for the complete factorial kernels.
The Gaussian integral is admitted through genuine integrability and dominated
convergence; no finite-source, Gaussian probability or zero-location premise enters.
-/

open MeasureTheory Filter Set
open scoped Topology
noncomputable section
namespace RHTower

private theorem aa_summable_real (w : ℝ) :
    Summable (fun n : ℕ => w^n / ((n.factorial : ℝ)^2)) := by
  apply Complex.summable_ofReal.mp
  simpa only [Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_natCast] using
    (summable_norm_liClockCriticalScalarTermComplex (w : ℂ)).of_norm

private theorem aa_positive_ge_one {w : ℝ} (hw : 0 ≤ w) :
    1 ≤ liClockCriticalPositiveKernel w := by
  simpa [liClockCriticalPositiveKernel] using
    (aa_summable_real w).le_tsum 0 (fun n _ => by positivity)

private theorem aa_angular_continuous (q : ℝ) :
    Continuous (fun θ : ℝ => Real.exp (q*Real.cos θ)) := by fun_prop

private theorem aa_halfAngular (q : ℝ) :
    (∫ θ in (0:ℝ)..Real.pi, Real.exp (q*Real.cos θ)) =
      Real.pi*liClockCriticalPositiveKernel (q^2/4) := by
  have hs := intervalIntegral.integral_add_adjacent_intervals
    ((aa_angular_continuous q).intervalIntegrable (μ := volume) (-Real.pi) 0)
    ((aa_angular_continuous q).intervalIntegrable (μ := volume) 0 Real.pi)
  have hr : (∫ θ in (-Real.pi)..0, Real.exp (q*Real.cos θ)) =
      (∫ θ in (0:ℝ)..Real.pi, Real.exp (q*Real.cos θ)) := by
    simpa using (intervalIntegral.integral_comp_neg
      (a := (0:ℝ)) (b := Real.pi) (fun θ => Real.exp (q*Real.cos θ))).symm
  rw [hr, liClockCriticalAngularIntegral_real_exp] at hs
  linarith

theorem liClockCriticalPositiveKernel_halfAngular
    {q : ℝ} (hq : 0 ≤ q) :
    (∫ θ in (0:ℝ)..Real.pi, Real.exp (q*Real.cos θ)) =
      Real.pi*liClockCriticalPositiveKernel (q^2/4) := by
  rcases hq.eq_or_lt with hq | hq
  · subst q; exact aa_halfAngular 0
  · exact aa_halfAngular q

theorem liClockCriticalEvenKernel_le_positive
    {w : ℝ} (hw : 0 ≤ w) :
    liClockCriticalEvenKernel w ≤ liClockCriticalPositiveKernel w := by
  rw [liClockCriticalEvenKernel_eq_half]
  have hH := aa_positive_ge_one hw
  have hJ := (le_abs_self (liClockCriticalOscillatoryKernel w)).trans
    (abs_liClockCriticalOscillatoryKernel_le_one hw)
  linarith

theorem liClockCriticalPositiveKernel_le_exp
    {q : ℝ} (hq : 0 ≤ q) :
    liClockCriticalPositiveKernel (q^2/4) ≤ Real.exp q := by
  have h := intervalIntegral.integral_mono_on Real.pi_pos.le
    ((aa_angular_continuous q).intervalIntegrable (μ := volume) 0 Real.pi)
    (continuous_const.intervalIntegrable (μ := volume) 0 Real.pi)
    (fun θ _ => Real.exp_le_exp.mpr (by nlinarith [Real.cos_le_one θ]))
  rw [liClockCriticalPositiveKernel_halfAngular hq] at h
  simpa using (mul_le_mul_iff_right₀ Real.pi_pos).mp (by simpa [mul_comm] using h)

private def aa_rescaled (q u : ℝ) : ℝ :=
  (Ioc (0:ℝ) (Real.pi*Real.sqrt q)).indicator
    (fun u => Real.exp (-q*(1-Real.cos (u/Real.sqrt q)))) u

private theorem aa_rescaled_meas (q : ℝ) :
    AEStronglyMeasurable (aa_rescaled q) (volume.restrict (Ioi 0)) := by
  exact (show Continuous (fun u : ℝ =>
    Real.exp (-q*(1-Real.cos (u/Real.sqrt q)))) by fun_prop).aestronglyMeasurable.indicator
      measurableSet_Ioc

private theorem aa_rescaled_nonneg (q u : ℝ) : 0 ≤ aa_rescaled q u := by
  unfold aa_rescaled
  by_cases hu : u ∈ Ioc (0:ℝ) (Real.pi*Real.sqrt q)
  · rw [indicator_of_mem hu]; positivity
  · rw [indicator_of_notMem hu]

private theorem aa_rescaled_le_gaussian {q : ℝ} (hq : 0<q) (u : ℝ) :
    ‖aa_rescaled q u‖ ≤ Real.exp (-(2/Real.pi^2)*u^2) := by
  rw [Real.norm_eq_abs, abs_of_nonneg (aa_rescaled_nonneg q u)]
  unfold aa_rescaled
  by_cases hu : u ∈ Ioc (0:ℝ) (Real.pi*Real.sqrt q)
  · rw [indicator_of_mem hu]
    have hs : 0<Real.sqrt q := Real.sqrt_pos.mpr hq
    have ht0 : 0 ≤ u/Real.sqrt q := div_nonneg hu.1.le hs.le
    have htπ : u/Real.sqrt q ≤ Real.pi := (div_le_iff₀ hs).mpr hu.2
    have hc := Real.cos_le_one_sub_mul_cos_sq
      (x := u/Real.sqrt q) (by rwa [abs_of_nonneg ht0])
    have he : q*(u/Real.sqrt q)^2 = u^2 := by
      rw [div_pow, ← mul_div_assoc, Real.sq_sqrt hq.le]
      field_simp
    have hl : (2/Real.pi^2)*u^2 ≤ q*(1-Real.cos (u/Real.sqrt q)) := by
      calc
        (2/Real.pi^2)*u^2 = q*((2/Real.pi^2)*(u/Real.sqrt q)^2) := by
          rw [← he]; ring
        _ ≤ q*(1-Real.cos (u/Real.sqrt q)) :=
          mul_le_mul_of_nonneg_left (by linarith [hc]) hq.le
    exact Real.exp_le_exp.mpr (by linarith)
  · rw [indicator_of_notMem hu]
    positivity

private theorem aa_gaussian_integrable :
    IntegrableOn (fun u : ℝ => Real.exp (-(2/Real.pi^2)*u^2)) (Ioi 0) := by
  exact (integrable_exp_neg_mul_sq (by positivity : 0<(2/Real.pi^2:ℝ))).integrableOn

private theorem aa_rescaled_integrable {q : ℝ} (hq : 0<q) :
    IntegrableOn (aa_rescaled q) (Ioi 0) := by
  exact aa_gaussian_integrable.mono' (aa_rescaled_meas q)
    (Filter.Eventually.of_forall (aa_rescaled_le_gaussian hq))

private theorem aa_rescaled_integral {q : ℝ} (hq : 0<q) :
    (∫ u in Ioi (0:ℝ), aa_rescaled q u) =
      Real.pi*(Real.sqrt q*Real.exp (-q)*liClockCriticalPositiveKernel (q^2/4)) := by
  have hs : 0<Real.sqrt q := Real.sqrt_pos.mpr hq
  have hsub : Ioc (0:ℝ) (Real.pi*Real.sqrt q) ⊆ Ioi 0 := fun _ h => h.1
  unfold aa_rescaled
  rw [integral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
    inter_eq_left.mpr hsub, ← intervalIntegral.integral_of_le (by positivity)]
  have he : (∫ u in (0:ℝ)..Real.pi*Real.sqrt q,
      Real.exp (-q*(1-Real.cos (u/Real.sqrt q)))) =
      Real.sqrt q*(∫ θ in (0:ℝ)..Real.pi, Real.exp (-q*(1-Real.cos θ))) := by
    simpa only [zero_div, mul_div_cancel_right₀ _ hs.ne', smul_eq_mul] using
      intervalIntegral.integral_comp_div
        (a := (0:ℝ)) (b := Real.pi*Real.sqrt q)
        (fun θ => Real.exp (-q*(1-Real.cos θ))) hs.ne'
  rw [he]
  have hf : (fun θ : ℝ => Real.exp (-q*(1-Real.cos θ))) =
      (fun θ => Real.exp (-q)*Real.exp (q*Real.cos θ)) := by
    funext θ
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hf, intervalIntegral.integral_const_mul,
    liClockCriticalPositiveKernel_halfAngular hq.le]
  ring

private theorem aa_gaussian_mass :
    (∫ u in Ioi (0:ℝ), Real.exp (-(2/Real.pi^2)*u^2)) =
      Real.pi*Real.sqrt Real.pi/(2*Real.sqrt 2) := by
  rw [integral_gaussian_Ioi]
  have he : Real.pi/(2/Real.pi^2) = Real.pi^2*(Real.pi/2) := by field_simp
  rw [he, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs,
    abs_of_pos Real.pi_pos, Real.sqrt_div Real.pi_pos.le]
  ring

theorem liClockCriticalPositiveKernel_le_exp_div_sqrt
    {q : ℝ} (hq : 0<q) :
    liClockCriticalPositiveKernel (q^2/4) ≤
      (Real.sqrt Real.pi/(2*Real.sqrt 2))*Real.exp q/Real.sqrt q := by
  have h := integral_mono_ae (aa_rescaled_integrable hq) aa_gaussian_integrable
    (Filter.Eventually.of_forall (fun u =>
      (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using
        (aa_rescaled_le_gaussian hq u))))
  rw [aa_rescaled_integral hq, aa_gaussian_mass] at h
  have hs : 0<Real.sqrt q := Real.sqrt_pos.mpr hq
  have he : Real.exp (-q)*Real.exp q = 1 := by rw [← Real.exp_add]; simp
  apply (le_div_iff₀ hs).mpr
  have hr : Real.pi*Real.sqrt Real.pi/(2*Real.sqrt 2) =
      Real.pi*(Real.sqrt Real.pi/(2*Real.sqrt 2)) := by ring
  rw [hr] at h
  have h1 := (mul_le_mul_iff_right₀ Real.pi_pos).mp h
  have h2 := mul_le_mul_of_nonneg_right h1 (Real.exp_pos q).le
  have hl : Real.sqrt q*Real.exp (-q)*liClockCriticalPositiveKernel (q^2/4)*Real.exp q =
      liClockCriticalPositiveKernel (q^2/4)*Real.sqrt q := by
    calc
      _ = (Real.exp (-q)*Real.exp q)*(liClockCriticalPositiveKernel (q^2/4)*Real.sqrt q) := by ring
      _ = _ := by rw [he]; ring
  rwa [hl] at h2

private theorem aa_tendsto_sqrt :
    Tendsto Real.sqrt atTop atTop := by
  change Tendsto (fun q : ℝ => Real.sqrt q) atTop atTop
  simp_rw [Real.sqrt_eq_rpow]
  exact tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/2)

private theorem aa_sinc_exponent {q : ℝ} (hq : 0<q) (u : ℝ) :
    q*(1-Real.cos (u/Real.sqrt q)) =
      (u^2/2)*(Real.sinc (u/(2*Real.sqrt q)))^2 := by
  by_cases hu : u=0
  · simp [hu]
  have hs : 0<Real.sqrt q := Real.sqrt_pos.mpr hq
  have harg : u/(2*Real.sqrt q) ≠ 0 := div_ne_zero hu (by positivity)
  have hcos : 1-Real.cos (u/Real.sqrt q) =
      2*(Real.sin (u/(2*Real.sqrt q)))^2 := by
    have hc := Real.sin_sq_eq_half_sub (u/(2*Real.sqrt q))
    have he : 2*(u/(2*Real.sqrt q)) = u/Real.sqrt q := by ring
    rw [he] at hc
    linarith
  rw [hcos, Real.sinc_of_ne_zero harg, div_pow]
  field_simp
  nlinarith [Real.sq_sqrt hq.le]

private theorem aa_rescaled_tendsto {u : ℝ} (hu : 0<u) :
    Tendsto (fun q : ℝ => aa_rescaled q u) atTop
      (nhds (Real.exp (-u^2/2))) := by
  have harg : Tendsto (fun q : ℝ => u/(2*Real.sqrt q)) atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using
      (aa_tendsto_sqrt.const_mul_atTop (by norm_num : (0:ℝ)<2)).inv_tendsto_atTop.const_mul u
  have hsinc : Tendsto (fun q : ℝ => Real.sinc (u/(2*Real.sqrt q)))
      atTop (nhds 1) := by
    simpa only [Function.comp_def, Real.sinc_zero] using
      (Real.continuous_sinc.continuousAt (x := 0)).tendsto.comp harg
  have hlim : Tendsto (fun q : ℝ => Real.exp (-((u^2/2)*(Real.sinc (u/(2*Real.sqrt q)))^2)))
      atTop (nhds (Real.exp (-u^2/2))) := by
    simpa only [Function.comp_def, one_pow, mul_one, neg_div] using
      Real.continuous_exp.continuousAt.tendsto.comp (((hsinc.pow 2).const_mul (u^2/2)).neg)
  have hcut : ∀ᶠ q : ℝ in atTop, u ≤ Real.pi*Real.sqrt q :=
    (aa_tendsto_sqrt.const_mul_atTop Real.pi_pos).eventually (eventually_ge_atTop u)
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ), hcut] with q hq hcut
  simp only [aa_rescaled, indicator_of_mem (show u ∈ Ioc (0:ℝ) (Real.pi*Real.sqrt q)
    from ⟨hu, hcut⟩)]
  rw [neg_mul, aa_sinc_exponent hq u]

private theorem aa_limit_gaussian_mass :
    (∫ u in Ioi (0:ℝ), Real.exp (-u^2/2)) =
      Real.sqrt (2*Real.pi)/2 := by
  have he : (fun u : ℝ => Real.exp (-u^2/2)) =
      (fun u => Real.exp (-(1/2)*u^2)) := by funext u; congr 1; ring
  rw [he, integral_gaussian_Ioi]
  congr 2
  ring

private theorem aa_rescaled_integral_tendsto :
    Tendsto (fun q : ℝ => ∫ u in Ioi (0:ℝ), aa_rescaled q u)
      atTop (nhds (Real.sqrt (2*Real.pi)/2)) := by
  rw [← aa_limit_gaussian_mass]
  apply tendsto_integral_filter_of_dominated_convergence
    (fun u => Real.exp (-(2/Real.pi^2)*u^2))
    (Filter.Eventually.of_forall aa_rescaled_meas)
    ?_ aa_gaussian_integrable ?_
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with q hq
    exact Filter.Eventually.of_forall (aa_rescaled_le_gaussian hq)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact aa_rescaled_tendsto hu

theorem tendsto_liClockCriticalPositiveKernel_scaled :
    Tendsto (fun q : ℝ => Real.sqrt q*Real.exp (-q)*
      liClockCriticalPositiveKernel (q^2/4)) atTop
        (nhds (1/Real.sqrt (2*Real.pi))) := by
  have h := aa_rescaled_integral_tendsto.const_mul (1/Real.pi)
  have he : (1/Real.pi)*(Real.sqrt (2*Real.pi)/2) =
      1/Real.sqrt (2*Real.pi) := by
    have hs : (Real.sqrt (2*Real.pi))^2 = 2*Real.pi := Real.sq_sqrt (by positivity)
    have hsp : 0<Real.sqrt (2*Real.pi) := by positivity
    apply (eq_div_iff hsp.ne').mpr
    calc
      _ = (Real.sqrt (2*Real.pi))^2/(2*Real.pi) := by ring
      _ = 1 := by rw [hs]; field_simp
  rw [he] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with q hq
  rw [aa_rescaled_integral hq]
  field_simp

private theorem aa_quarter_power {w : ℝ} (hw : 0≤w) :
    Real.sqrt (Real.sqrt w) = w^(1/4:ℝ) := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hw]
  norm_num

private theorem aa_sqrt_double_sqrt {w : ℝ} (hw : 0≤w) :
    Real.sqrt (2*Real.sqrt w) = Real.sqrt 2*w^(1/4:ℝ) := by
  rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤2), aa_quarter_power hw]

private theorem aa_even_constant :
    (1/(2*Real.sqrt 2))*(1/Real.sqrt (2*Real.pi)) =
      1/(4*Real.sqrt Real.pi) := by
  rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤2)]
  have h2 : (Real.sqrt 2)^2 = (2:ℝ) := Real.sq_sqrt (by norm_num)
  have h2p : 0<Real.sqrt (2:ℝ) := by positivity
  have hπp : 0<Real.sqrt Real.pi := by positivity
  field_simp
  nlinarith [mul_pos h2p hπp, congrArg (fun x : ℝ => x*Real.sqrt Real.pi) h2]

private theorem aa_positive_half_scaled :
    Tendsto (fun w : ℝ => w^(1/4:ℝ)*Real.exp (-2*Real.sqrt w)*
      liClockCriticalPositiveKernel w/2) atTop (nhds (1/(4*Real.sqrt Real.pi))) := by
  have h := (tendsto_liClockCriticalPositiveKernel_scaled.comp
    (aa_tendsto_sqrt.const_mul_atTop (by norm_num : (0:ℝ)<2))).const_mul (1/(2*Real.sqrt 2))
  rw [aa_even_constant] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (0:ℝ)] with w hw
  have he : (2*Real.sqrt w)^2/4 = w := by nlinarith [Real.sq_sqrt hw]
  simp only [Function.comp_def]
  rw [he, aa_sqrt_double_sqrt hw]
  field_simp

private theorem aa_quarter_exp_tendsto_zero :
    Tendsto (fun w : ℝ => w^(1/4:ℝ)*Real.exp (-2*Real.sqrt w)) atTop (nhds 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1/2:ℝ) 2 (by norm_num)).comp
    aa_tendsto_sqrt
  apply h.congr'
  filter_upwards [eventually_ge_atTop (0:ℝ)] with w hw
  simp only [Function.comp_def]
  rw [← Real.sqrt_eq_rpow, aa_quarter_power hw]

private theorem aa_oscillatory_half_scaled_zero :
    Tendsto (fun w : ℝ => w^(1/4:ℝ)*Real.exp (-2*Real.sqrt w)*
      liClockCriticalOscillatoryKernel w/2) atTop (nhds 0) := by
  apply squeeze_zero_norm'
    (a := fun w : ℝ => (w^(1/4:ℝ)*Real.exp (-2*Real.sqrt w))/2)
    ?_ (by simpa using aa_quarter_exp_tendsto_zero.div_const 2)
  filter_upwards [eventually_ge_atTop (0:ℝ)] with w hw
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg hw _), abs_of_pos (Real.exp_pos _), abs_of_pos (by norm_num : (0:ℝ)<2)]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  exact mul_le_of_le_one_right (by positivity)
    (abs_liClockCriticalOscillatoryKernel_le_one hw)

theorem tendsto_liClockCriticalEvenKernel_scaled :
    Tendsto (fun w : ℝ => w^(1/4:ℝ)*Real.exp (-2*Real.sqrt w)*
      liClockCriticalEvenKernel w) atTop (nhds (1/(4*Real.sqrt Real.pi))) := by
  have h := aa_positive_half_scaled.add aa_oscillatory_half_scaled_zero
  simp only [add_zero] at h
  convert h using 1
  funext w
  rw [liClockCriticalEvenKernel_eq_half]
  ring

theorem liClockCriticalEvenKernel_le_exp
    {w : ℝ} (hw : 0 ≤ w) :
    liClockCriticalEvenKernel w ≤ Real.exp (2*Real.sqrt w) := by
  have he : (2*Real.sqrt w)^2/4 = w := by nlinarith [Real.sq_sqrt hw]
  exact (liClockCriticalEvenKernel_le_positive hw).trans
    (by simpa [he] using (liClockCriticalPositiveKernel_le_exp
      (q := 2*Real.sqrt w) (by positivity)))

end RHTower
