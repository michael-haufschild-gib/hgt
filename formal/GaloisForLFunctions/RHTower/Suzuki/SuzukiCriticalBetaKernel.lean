import GaloisForLFunctions.RHTower.Suzuki.SuzukiCanonicalKernelMellin
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# The literal Suzuki Beta density at the critical shift

The primary part of Suzuki's source, pulled back to logarithmic coordinates at
the critical Mellin line. Its mass is a Gamma ratio, and its compensated density
is dominated by the archimedean Lévy weight uniformly down to positive shift zero.
No innerness or positivity of the complete Weil form is assumed.
-/

open MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

/-- Critical log-coordinate density of the literal primary Suzuki kernel. -/
def suzukiCriticalPrimaryDensity (omega t : ℝ) : ℝ :=
  Real.pi ^ omega * Real.exp (-t / 2) *
    (suzukiPrimaryBetaKernel omega (Real.exp (-t))).re

/-- Exact total mass of the critical primary density. -/
def suzukiCriticalPrimaryMass (omega : ℝ) : ℝ :=
  Real.pi ^ omega * Real.Gamma (5 / 4 - omega / 2) /
    Real.Gamma (5 / 4 + omega / 2)

/-- The regular Gamma coefficient after removing the vanishing factor `omega`. -/
def suzukiCriticalPrimaryScale (omega : ℝ) : ℝ :=
  Real.pi ^ omega / Real.Gamma (omega + 1)

theorem measurable_suzukiCriticalPrimaryDensity (omega : ℝ) :
    Measurable (suzukiCriticalPrimaryDensity omega) := by
  unfold suzukiCriticalPrimaryDensity
  exact (measurable_const.mul (by fun_prop)).mul
    ((measurable_suzukiPrimaryBetaKernel omega).comp (by fun_prop)).re

private theorem primary_eq_ofReal {omega x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    suzukiPrimaryBetaKernel omega x =
      ((2 / Real.Gamma omega * x ^ (2 - omega) *
        (1 - x ^ 2) ^ (omega - 1) : ℝ) : ℂ) := by
  rw [suzukiPrimaryBetaKernel_eq_source omega hx hx1, Complex.Gamma_ofReal]
  have hb : 0 ≤ 1 - x ^ 2 := by nlinarith
  push_cast
  rw [Complex.ofReal_cpow hx.le, Complex.ofReal_cpow hb]
  push_cast
  rfl

/-- The singularity at the source endpoint is exactly the positive Beta singularity. -/
theorem suzukiCriticalPrimaryDensity_eq {omega t : ℝ} (ht : 0 < t) :
    suzukiCriticalPrimaryDensity omega t =
      2 * Real.pi ^ omega / Real.Gamma omega *
        Real.exp (-(5 / 2 - omega) * t) *
          (1 - Real.exp (-2 * t)) ^ (omega - 1) := by
  have hx := Real.exp_pos (-t)
  have hx1 : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  rw [suzukiCriticalPrimaryDensity, primary_eq_ofReal hx hx1, Complex.ofReal_re]
  have hs : Real.exp (-t) ^ (2 : ℕ) = Real.exp (-2 * t) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [hs, ← Real.exp_mul, ← mul_assoc, ← mul_assoc]
  calc
    _ = 2 * Real.pi ^ omega / Real.Gamma omega *
        (Real.exp (-t / 2) * Real.exp (-t * (2 - omega))) *
          (1 - Real.exp (-2 * t)) ^ (omega - 1) := by ring
    _ = _ := by rw [← Real.exp_add]; congr 3; ring

theorem suzukiCriticalPrimaryDensity_pos {omega t : ℝ}
    (homega : 0 < omega) (ht : 0 < t) :
    0 < suzukiCriticalPrimaryDensity omega t := by
  rw [suzukiCriticalPrimaryDensity_eq ht]
  have hb : 0 < 1 - Real.exp (-2 * t) := by
    have := Real.exp_lt_one_iff.mpr (show -2 * t < 0 by linarith)
    linarith
  exact mul_pos
    (mul_pos (div_pos (mul_pos (by norm_num) (Real.rpow_pos_of_pos Real.pi_pos _))
      (Real.Gamma_pos_of_pos homega)) (Real.exp_pos _))
    (Real.rpow_pos_of_pos hb _)

/-- Removing `omega` exposes a Gamma coefficient continuous at zero. -/
theorem suzukiCriticalPrimaryDensity_div_eq {omega t : ℝ}
    (homega : 0 < omega) (ht : 0 < t) :
    suzukiCriticalPrimaryDensity omega t / omega =
      suzukiCriticalPrimaryScale omega *
        (2 * Real.exp (-(5 / 2 - omega) * t) *
          (1 - Real.exp (-2 * t)) ^ omega / (1 - Real.exp (-2 * t))) := by
  rw [suzukiCriticalPrimaryDensity_eq ht, suzukiCriticalPrimaryScale,
    Real.Gamma_add_one homega.ne']
  have hb : 0 < 1 - Real.exp (-2 * t) := by
    have := Real.exp_lt_one_iff.mpr (show -2 * t < 0 by linarith)
    linarith
  rw [Real.rpow_sub hb, Real.rpow_one]
  ring

/-- Uniform domination by the full archimedean Lévy density, for small positive shifts. -/
theorem suzukiCriticalPrimaryDensity_div_le {omega t : ℝ}
    (homega : 0 < omega) (homega2 : omega ≤ 2) (ht : 0 < t) :
    suzukiCriticalPrimaryDensity omega t / omega ≤
      suzukiCriticalPrimaryScale omega *
        (2 * Real.exp (-t / 2) / (1 - Real.exp (-2 * t))) := by
  have hb : 0 < 1 - Real.exp (-2 * t) := by
    have := Real.exp_lt_one_iff.mpr (show -2 * t < 0 by linarith)
    linarith
  have hb1 : 1 - Real.exp (-2 * t) ≤ 1 := by linarith [Real.exp_pos (-2 * t)]
  have hp := Real.rpow_le_one hb.le hb1 homega.le
  have he : Real.exp (-(5 / 2 - omega) * t) ≤ Real.exp (-t / 2) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have ha : 0 ≤ suzukiCriticalPrimaryScale omega := by
    unfold suzukiCriticalPrimaryScale
    exact div_nonneg (Real.rpow_nonneg Real.pi_pos.le _)
      (Real.Gamma_pos_of_pos (by linarith)).le
  rw [suzukiCriticalPrimaryDensity_div_eq homega ht]
  apply mul_le_mul_of_nonneg_left _ ha
  apply div_le_div_of_nonneg_right _ hb.le
  calc
    _ ≤ 2 * Real.exp (-(5 / 2 - omega) * t) * 1 :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ ≤ 2 * Real.exp (-t / 2) := by nlinarith

private theorem image_exp_neg_positive :
    (fun t : ℝ => Real.exp (-t)) '' Ioi 0 = Ioo 0 1 := by
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr (neg_neg_of_pos ht)⟩
  · intro hx
    refine ⟨-Real.log x, neg_pos.mpr (Real.log_neg hx.1 hx.2), ?_⟩
    simpa only [neg_neg] using Real.exp_log hx.1

private theorem primary_log_pullback (omega t : ℝ) :
    Real.exp (-t) • ((Real.exp (-t) : ℂ) ^ ((1 / 2 : ℂ) - 1) *
      suzukiPrimaryBetaKernel omega (Real.exp (-t))) =
        (Real.exp (-t / 2) : ℂ) * suzukiPrimaryBetaKernel omega (Real.exp (-t)) := by
  have hp : (Real.exp (-t) : ℂ) ^ ((1 / 2 : ℂ) - 1) =
      (Real.exp (t / 2) : ℂ) := by
    rw [show (1 / 2 : ℂ) - 1 = ((-1 / 2 : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_cpow (Real.exp_pos _).le, ← Real.exp_mul]
    congr 2
    ring
  rw [Complex.real_smul, hp, ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
  congr 2
  ring

private theorem primary_log_has_integral {omega : ℝ}
    (homega : 0 < omega) (homega5 : omega < 5 / 2) :
    IntegrableOn (fun t : ℝ => (Real.exp (-t / 2) : ℂ) *
      suzukiPrimaryBetaKernel omega (Real.exp (-t))) (Ioi 0) ∧
    (∫ t : ℝ in Ioi 0, (Real.exp (-t / 2) : ℂ) *
      suzukiPrimaryBetaKernel omega (Real.exp (-t))) =
        ((Real.Gamma (5 / 4 - omega / 2) / Real.Gamma (5 / 4 + omega / 2) : ℝ) : ℂ) := by
  let F : ℝ → ℂ := fun x => (x : ℂ) ^ ((1 / 2 : ℂ) - 1) *
    suzukiPrimaryBetaKernel omega x
  have hm := hasMellin_suzukiPrimaryBetaKernel homega
    (s := (1 / 2 : ℂ)) (by norm_num; linarith)
  have hF : IntegrableOn F (Ioi 0) := by
    simpa only [MellinConvergent, smul_eq_mul, F] using hm.1
  have hd : ∀ t ∈ Ioi (0 : ℝ), HasDerivWithinAt (fun t : ℝ => Real.exp (-t))
      (-Real.exp (-t)) (Ioi 0) t := by
    intro t _
    simpa using ((hasDerivAt_id t).neg.exp).hasDerivWithinAt
  have hinj : InjOn (fun t : ℝ => Real.exp (-t)) (Ioi 0) :=
    (Real.exp_injective.comp neg_injective).injOn
  have hi := (integrableOn_image_iff_integrableOn_abs_deriv_smul
    measurableSet_Ioi hd hinj F)
  rw [image_exp_neg_positive] at hi
  have hlog := hi.mp (hF.mono_set (fun _ hx => hx.1))
  simp only [abs_neg, abs_of_pos (Real.exp_pos _), F, primary_log_pullback] at hlog
  refine ⟨hlog, ?_⟩
  have he := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hd hinj F
  rw [image_exp_neg_positive] at he
  simp only [abs_neg, abs_of_pos (Real.exp_pos _), F, primary_log_pullback] at he
  rw [← he, ← integral_Ioc_eq_integral_Ioo]
  have hs : (∫ x in Ioi 0, F x) = ∫ x in Ioc 0 1, F x := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (fun _ hx => hx.1)
    intro x hx
    have hx1 : 1 < x := by
      have hnot : ¬x ≤ 1 := fun hx1 => hx.2 ⟨hx.1, hx1⟩
      exact lt_of_not_ge hnot
    simp [F, suzukiPrimaryBetaKernel_eq_zero_of_one_lt omega hx1]
  change (∫ x in Ioc 0 1, F x) = _
  rw [← hs]
  have ha : ((1 / 2 : ℂ) - (omega : ℂ)) / 2 + 1 =
      ((5 / 4 - omega / 2 : ℝ) : ℂ) := by push_cast; ring
  have hb : ((1 / 2 : ℂ) + (omega : ℂ)) / 2 + 1 =
      ((5 / 4 + omega / 2 : ℝ) : ℂ) := by push_cast; ring
  simpa only [mellin, smul_eq_mul, F, ha, hb, Complex.Gamma_ofReal,
    Complex.ofReal_div] using hm.2

/-- The literal primary source is integrable at every shift below the critical Mellin endpoint. -/
theorem integrableOn_suzukiCriticalPrimaryDensity {omega : ℝ}
    (homega : 0 < omega) (homega5 : omega < 5 / 2) :
    IntegrableOn (suzukiCriticalPrimaryDensity omega) (Ioi 0) := by
  have h := ((primary_log_has_integral homega homega5).1.re).const_mul (Real.pi ^ omega)
  change Integrable (fun t => Real.pi ^ omega * Real.exp (-t / 2) *
    (suzukiPrimaryBetaKernel omega (Real.exp (-t))).re) (volume.restrict (Ioi 0))
  simpa only [RCLike.re_eq_complex_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, mul_assoc] using h

/-- Exact Gamma-ratio mass, including the atom that forms at positive shift zero. -/
theorem integral_suzukiCriticalPrimaryDensity {omega : ℝ}
    (homega : 0 < omega) (homega5 : omega < 5 / 2) :
    (∫ t in Ioi 0, suzukiCriticalPrimaryDensity omega t) =
      suzukiCriticalPrimaryMass omega := by
  obtain ⟨hi, he⟩ := primary_log_has_integral homega homega5
  have hr := congrArg Complex.re he
  have hir : (∫ t in Ioi 0, ((Real.exp (-t / 2) : ℂ) *
      suzukiPrimaryBetaKernel omega (Real.exp (-t))).re) =
      (∫ t in Ioi 0, (Real.exp (-t / 2) : ℂ) *
        suzukiPrimaryBetaKernel omega (Real.exp (-t))).re := by
    simpa only [RCLike.re_eq_complex_re] using integral_re hi
  rw [← hir] at hr
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero] at hr
  calc
    _ = Real.pi ^ omega *
        ∫ t in Ioi 0, Real.exp (-t / 2) *
          (suzukiPrimaryBetaKernel omega (Real.exp (-t))).re := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with t
      simp only [suzukiCriticalPrimaryDensity]
      ring
    _ = _ := by rw [hr]; unfold suzukiCriticalPrimaryMass; ring

theorem continuousAt_suzukiCriticalPrimaryScale :
    ContinuousAt suzukiCriticalPrimaryScale 0 := by
  have hG : ContinuousAt Real.Gamma (0 + 1 : ℝ) :=
    (Real.differentiableAt_Gamma (fun m => by
      have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      norm_num
      linarith)).continuousAt
  exact (Real.continuousAt_const_rpow Real.pi_ne_zero).div
    (hG.comp (f := fun omega : ℝ => omega + 1)
      (continuousAt_id.add continuousAt_const)) (by norm_num)

theorem tendsto_suzukiCriticalPrimaryScale :
    Tendsto suzukiCriticalPrimaryScale (𝓝 0) (𝓝 1) := by
  simpa [suzukiCriticalPrimaryScale] using continuousAt_suzukiCriticalPrimaryScale.tendsto

theorem continuousAt_suzukiCriticalPrimaryMass :
    ContinuousAt suzukiCriticalPrimaryMass 0 := by
  have hG : ContinuousAt Real.Gamma (5 / 4 : ℝ) :=
    (Real.differentiableAt_Gamma (fun m => by
      have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith)).continuousAt
  have hn : ContinuousAt (fun omega : ℝ => Real.Gamma (5 / 4 - omega / 2)) 0 := by
    have hG' : ContinuousAt Real.Gamma (5 / 4 - (0 : ℝ) / 2) := by simpa using hG
    exact hG'.comp (f := fun omega : ℝ => 5 / 4 - omega / 2) (by fun_prop)
  have hd : ContinuousAt (fun omega : ℝ => Real.Gamma (5 / 4 + omega / 2)) 0 := by
    have hG' : ContinuousAt Real.Gamma (5 / 4 + (0 : ℝ) / 2) := by simpa using hG
    exact hG'.comp (f := fun omega : ℝ => 5 / 4 + omega / 2) (by fun_prop)
  exact ((Real.continuousAt_const_rpow Real.pi_ne_zero).mul hn).div hd
    (by simpa using (Real.Gamma_pos_of_pos (show (0 : ℝ) < 5 / 4 by norm_num)).ne')

theorem tendsto_suzukiCriticalPrimaryMass :
    Tendsto suzukiCriticalPrimaryMass (𝓝 0) (𝓝 1) := by
  have hn := (Real.Gamma_pos_of_pos (show (0 : ℝ) < 5 / 4 by norm_num)).ne'
  simpa [suzukiCriticalPrimaryMass, hn] using continuousAt_suzukiCriticalPrimaryMass.tendsto

private theorem hasDerivAt_realGamma_of_pos {x : ℝ} (hx : 0 < x) :
    HasDerivAt Real.Gamma (Real.Gamma x * (Complex.digamma (x : ℂ)).re) x := by
  have hc : DifferentiableAt ℂ Complex.Gamma (x : ℂ) :=
    Complex.differentiableAt_Gamma _ (fun m hm => by
      have hr := congrArg Complex.re hm
      norm_num at hr
      have hn : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith)
  have hr : HasDerivAt Real.Gamma (deriv Complex.Gamma (x : ℂ)).re x :=
    hc.hasDerivAt.real_of_complex
  apply hr.congr_deriv
  rw [Complex.digamma_def, logDeriv_apply, Complex.Gamma_ofReal, Complex.div_ofReal_re]
  field_simp [(Real.Gamma_pos_of_pos hx).ne']

/-- First variation of the forming Gamma atom, with its actual digamma constant. -/
theorem hasDerivAt_suzukiCriticalPrimaryMass :
    HasDerivAt suzukiCriticalPrimaryMass
      (Real.log Real.pi - (Complex.digamma ((5 / 4 : ℝ) : ℂ)).re) 0 := by
  have hG := hasDerivAt_realGamma_of_pos (show (0 : ℝ) < 5 / 4 by norm_num)
  have hn : HasDerivAt (fun omega : ℝ => Real.Gamma (5 / 4 - omega / 2))
      (-(Real.Gamma (5 / 4) * (Complex.digamma ((5 / 4 : ℝ) : ℂ)).re) / 2) 0 := by
    have hG' : HasDerivAt Real.Gamma
        (Real.Gamma (5 / 4) * (Complex.digamma ((5 / 4 : ℝ) : ℂ)).re)
        (5 / 4 - (0 : ℝ) / 2) := by simpa using hG
    have hi : HasDerivAt (fun omega : ℝ => 5 / 4 - omega / 2) (-(1 / 2)) 0 :=
      ((hasDerivAt_id 0).div_const 2).const_sub (5 / 4)
    apply (hG'.comp 0 hi).congr_deriv
    ring
  have hd : HasDerivAt (fun omega : ℝ => Real.Gamma (5 / 4 + omega / 2))
      ((Real.Gamma (5 / 4) * (Complex.digamma ((5 / 4 : ℝ) : ℂ)).re) / 2) 0 := by
    have hG' : HasDerivAt Real.Gamma
        (Real.Gamma (5 / 4) * (Complex.digamma ((5 / 4 : ℝ) : ℂ)).re)
        (5 / 4 + (0 : ℝ) / 2) := by simpa using hG
    have hi : HasDerivAt (fun omega : ℝ => 5 / 4 + omega / 2) (1 / 2) 0 :=
      ((hasDerivAt_id 0).div_const 2).const_add (5 / 4)
    apply (hG'.comp 0 hi).congr_deriv
    ring
  have hp : HasDerivAt (fun omega : ℝ => Real.pi ^ omega) (Real.log Real.pi) 0 := by
    simpa using (Real.hasStrictDerivAt_const_rpow Real.pi_pos 0).hasDerivAt
  have hne := (Real.Gamma_pos_of_pos (show (0 : ℝ) < 5 / 4 by norm_num)).ne'
  have h := (hp.mul hn).div hd (by simpa using hne)
  apply h.congr_deriv
  simp only [Pi.mul_apply, Real.rpow_zero, zero_div, sub_zero, add_zero, one_mul]
  field_simp [hne]
  ring

theorem tendsto_suzukiCriticalPrimaryMass_secant :
    Tendsto (fun omega : ℝ => (suzukiCriticalPrimaryMass omega - 1) / omega)
      (𝓝[>] 0) (𝓝 (Real.log Real.pi - (Complex.digamma ((5 / 4 : ℝ) : ℂ)).re)) := by
  have hne := (Real.Gamma_pos_of_pos (show (0 : ℝ) < 5 / 4 by norm_num)).ne'
  have hzero : suzukiCriticalPrimaryMass 0 = 1 := by simp [suzukiCriticalPrimaryMass, hne]
  simpa only [zero_add, hzero, smul_eq_mul, div_eq_mul_inv, mul_comm] using
    hasDerivAt_suzukiCriticalPrimaryMass.tendsto_slope_zero_right

/-- Pointwise tangent away from the atom at the origin. -/
theorem tendsto_suzukiCriticalPrimaryDensity_div {t : ℝ} (ht : 0 < t) :
    Tendsto (fun omega : ℝ => suzukiCriticalPrimaryDensity omega t / omega)
      (𝓝[>] 0) (𝓝 (2 * Real.exp (-(5 / 2 : ℝ) * t) / (1 - Real.exp (-2 * t)))) := by
  have hb : 0 < 1 - Real.exp (-2 * t) := by
    have := Real.exp_lt_one_iff.mpr (show -2 * t < 0 by linarith)
    linarith
  have hc : ContinuousAt (fun omega : ℝ => suzukiCriticalPrimaryScale omega *
      (2 * Real.exp (-(5 / 2 - omega) * t) *
        (1 - Real.exp (-2 * t)) ^ omega / (1 - Real.exp (-2 * t)))) 0 :=
    continuousAt_suzukiCriticalPrimaryScale.mul
      (((continuousAt_const.mul (by fun_prop)).mul
        (Real.continuousAt_const_rpow hb.ne')).div_const _)
  have hl := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  simp only [suzukiCriticalPrimaryScale, Real.rpow_zero, zero_add, Real.Gamma_one,
    div_one, sub_zero, mul_one, one_mul] at hl
  apply hl.congr'
  filter_upwards [self_mem_nhdsWithin] with omega homega
  exact (suzukiCriticalPrimaryDensity_div_eq homega ht).symm

/-- Compensation by any nonnegative finite-Lévy-energy profile permits the critical limit. -/
theorem tendsto_integral_compensated_suzukiCriticalPrimaryDensity {D : ℝ → ℝ}
    (hDm : AEStronglyMeasurable D (volume.restrict (Ioi 0)))
    (hDnn : ∀ᵐ t ∂volume.restrict (Ioi 0), 0 ≤ D t)
    (hD : IntegrableOn (fun t => D t *
      (2 * Real.exp (-t / 2) / (1 - Real.exp (-2 * t)))) (Ioi 0)) :
    Tendsto (fun omega : ℝ => ∫ t in Ioi 0,
      D t * (suzukiCriticalPrimaryDensity omega t / omega)) (𝓝[>] 0)
      (𝓝 (∫ t in Ioi 0,
        D t * (2 * Real.exp (-(5 / 2 : ℝ) * t) / (1 - Real.exp (-2 * t))))) := by
  have ha : ∀ᶠ omega in 𝓝[>] (0 : ℝ), suzukiCriticalPrimaryScale omega < 2 :=
    (tendsto_suzukiCriticalPrimaryScale.mono_left nhdsWithin_le_nhds).eventually
      (Iio_mem_nhds (show (1 : ℝ) < 2 by norm_num))
  have ho : ∀ᶠ omega in 𝓝[>] (0 : ℝ), omega < 2 :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0 : ℝ) < 2 by norm_num))
  apply tendsto_integral_filter_of_dominated_convergence
    (fun t => 2 * (D t * (2 * Real.exp (-t / 2) / (1 - Real.exp (-2 * t)))))
  · exact Filter.Eventually.of_forall fun omega =>
      hDm.mul ((measurable_suzukiCriticalPrimaryDensity omega).div
        measurable_const).aestronglyMeasurable
  · filter_upwards [ha, ho, self_mem_nhdsWithin] with omega ha ho homega
    filter_upwards [hDnn, ae_restrict_mem measurableSet_Ioi] with t hDt ht
    change 0 < omega at homega
    change 0 < t at ht
    have hpos := (suzukiCriticalPrimaryDensity_pos homega ht).le
    have hb : 0 < 1 - Real.exp (-2 * t) := by
      have := Real.exp_lt_one_iff.mpr (show -2 * t < 0 by linarith)
      linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hDt (div_nonneg hpos homega.le))]
    calc
      _ ≤ D t * (suzukiCriticalPrimaryScale omega *
          (2 * Real.exp (-t / 2) / (1 - Real.exp (-2 * t)))) :=
        mul_le_mul_of_nonneg_left
          (suzukiCriticalPrimaryDensity_div_le homega ho.le ht) hDt
      _ ≤ D t * (2 * (2 * Real.exp (-t / 2) / (1 - Real.exp (-2 * t)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ha.le (by positivity)) hDt
      _ = _ := by ring
  · exact hD.const_mul 2
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (tendsto_suzukiCriticalPrimaryDensity_div ht).const_mul (D t)

/-- Complete first variation of the literal primary density, including its forming atom.
The hypotheses are precisely the bounded-correlation and finite-Lévy-energy estimates. -/
theorem tendsto_suzukiCriticalPrimaryPairing_firstVariation {C : ℝ → ℝ}
    (hCm : AEStronglyMeasurable C (volume.restrict (Ioi 0)))
    (hCb : ∀ᵐ t ∂volume.restrict (Ioi 0), |C t| ≤ C 0)
    (hClev : IntegrableOn (fun t => (C 0 - C t) *
      (2 * Real.exp (-t / 2) / (1 - Real.exp (-2 * t)))) (Ioi 0)) :
    Tendsto (fun omega : ℝ =>
      ((∫ t in Ioi 0, C t * suzukiCriticalPrimaryDensity omega t) - C 0) / omega)
      (𝓝[>] 0)
      (𝓝 ((Real.log Real.pi - (Complex.digamma ((5 / 4 : ℝ) : ℂ)).re) * C 0 -
        ∫ t in Ioi 0, (C 0 - C t) *
          (2 * Real.exp (-(5 / 2 : ℝ) * t) / (1 - Real.exp (-2 * t))))) := by
  have hnn : ∀ᵐ t ∂volume.restrict (Ioi 0), 0 ≤ C 0 - C t := by
    filter_upwards [hCb] with t ht
    linarith [le_abs_self (C t)]
  have hc := tendsto_integral_compensated_suzukiCriticalPrimaryDensity
    (D := fun t => C 0 - C t)
    (aestronglyMeasurable_const.sub hCm) hnn hClev
  have hl := (tendsto_suzukiCriticalPrimaryMass_secant.mul_const (C 0)).sub hc
  apply hl.congr'
  have ho : ∀ᶠ omega in 𝓝[>] (0 : ℝ), omega < 2 :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0 : ℝ) < 2 by norm_num))
  filter_upwards [self_mem_nhdsWithin, ho] with omega homega ho
  have hi := integrableOn_suzukiCriticalPrimaryDensity homega (by linarith : omega < 5 / 2)
  have hprod : IntegrableOn (fun t => C t * suzukiCriticalPrimaryDensity omega t) (Ioi 0) :=
    hi.bdd_mul hCm (by simpa only [Real.norm_eq_abs] using hCb)
  have he : (∫ t in Ioi 0, (C 0 - C t) * (suzukiCriticalPrimaryDensity omega t / omega)) =
      (C 0 * suzukiCriticalPrimaryMass omega -
        ∫ t in Ioi 0, C t * suzukiCriticalPrimaryDensity omega t) / omega := by
    calc
      _ = (∫ t in Ioi 0, C 0 * suzukiCriticalPrimaryDensity omega t -
          C t * suzukiCriticalPrimaryDensity omega t) / omega := by
        rw [← integral_div]
        apply integral_congr_ae
        filter_upwards with t
        ring
      _ = _ := by
        rw [integral_sub (hi.const_mul _) hprod, integral_const_mul,
          integral_suzukiCriticalPrimaryDensity homega (by linarith)]
  rw [he]
  ring

end
end RHTower
