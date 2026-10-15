import GaloisForLFunctions.RHTower.LogSineClockTransform
import GaloisForLFunctions.RHTower.LogSineConductanceMoments
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import GaloisForLFunctions.RHTower.OrderOneEvenLaguerrePolya
import GaloisForLFunctions.RHTower.XiIntervalLaguerrePolyaRH
import GaloisForLFunctions.HTGeometry.CompactFourierEntire

/-!
# Positive Hankel conductances with nonreal quantile-transform zeros

The literal regularized clock transforms converge uniformly on bounded real
windows to pi/cosh(pi*x/2). If arbitrarily small positive regularizations had
only real zeros, their order-one growth would place them in the Laguerre–Pólya
class. The existing window compactness theorem would then give an entire limit
of their reflected products. Multiplication by cosh(pi*z/2)^2 and the identity
theorem force that product to equal pi^2 everywhere, contradicting its value at i.

Thus every sufficiently small positive regularization has a nonreal zero.
The complete change of variables transfers those zeros to the original quantile
transform. The final theorem pairs them with strict concavity and every shifted
conductance Hankel inequality for the same literal profile. This obstructs a bare
Hankel-positivity criterion; no pinned-inverse eigenvector, theta-specific conclusion,
or RH proof is asserted.
-/

open MeasureTheory Set Filter Topology
namespace RHTower
noncomputable section


private theorem clock_phase_difference (a b : ℝ) :
    ‖Complex.exp (Complex.I * (a : ℂ)) - Complex.exp (Complex.I * (b : ℂ))‖ ≤ |a - b| := by
  have he : Complex.exp (Complex.I * (a : ℂ)) - Complex.exp (Complex.I * (b : ℂ)) =
      Complex.exp (Complex.I * (b : ℂ)) *
        (Complex.exp (Complex.I * ((a - b : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, ← Complex.exp_add, mul_one]
    congr 1
    push_cast
    ring
  have hn : ‖Complex.exp (Complex.I * (b : ℂ))‖ = 1 := by
    rw [mul_comm]
    exact Complex.norm_exp_ofReal_mul_I b
  rw [he, norm_mul, hn, one_mul]
  simpa only [Real.norm_eq_abs] using Real.norm_exp_I_mul_ofReal_sub_one_le (x := a - b)

private theorem clock_real_integrand_norm (δ x u : ℝ) :
    ‖Complex.exp (Complex.I * (x : ℂ) * (logSineClock δ u : ℂ)) /
      (Real.cosh u : ℂ)‖ = 1 / Real.cosh u := by
  rw [norm_div, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.cosh_pos u)]
  have he : (Complex.I * (x : ℂ) * (logSineClock δ u : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [he, Real.exp_zero]

private theorem integrable_clock_real_integrand {δ : ℝ} (hδ : 0 ≤ δ) (x : ℝ) :
    Integrable (fun u : ℝ => Complex.exp (Complex.I * (x : ℂ) * (logSineClock δ u : ℂ)) /
      (Real.cosh u : ℂ)) := by
  have hi : Integrable (fun u : ℝ => 1 / Real.cosh u) := by
    simpa only [pow_zero] using integrable_logSineSech_abs_pow 0
  apply hi.mono'
  · have hc : Continuous (fun u : ℝ =>
        Complex.exp (Complex.I * (x : ℂ) * (logSineClock δ u : ℂ)) /
          (Real.cosh u : ℂ)) := by
      apply Continuous.div
      · exact Complex.continuous_exp.comp (continuous_const.mul
          (Complex.continuous_ofReal.comp (continuous_logSineClock hδ)))
      · exact Complex.continuous_ofReal.comp Real.continuous_cosh
      · intro u
        exact Complex.ofReal_ne_zero.mpr (Real.cosh_pos u).ne'
    exact hc.aestronglyMeasurable
  · filter_upwards with u
    exact (clock_real_integrand_norm δ x u).le

private theorem clock_difference_bound {δ : ℝ} (hδ : 0 ≤ δ) (u : ℝ) :
    |logSineClock δ u - u| / Real.cosh u ≤ 2 * (|u| / Real.cosh u) := by
  have hs := norm_sub_le (logSineClock δ u) u
  simp only [Real.norm_eq_abs] at hs
  have hb : |logSineClock δ u - u| ≤ 2 * |u| := by
    linarith [abs_logSineClock_le hδ u]
  calc
    _ ≤ (2 * |u|) / Real.cosh u := div_le_div_of_nonneg_right hb (Real.cosh_pos u).le
    _ = _ := by ring

private theorem integrable_clock_difference {δ : ℝ} (hδ : 0 ≤ δ) :
    Integrable (fun u : ℝ => |logSineClock δ u - u| / Real.cosh u) := by
  have hi : Integrable (fun u : ℝ => 2 * (|u| / Real.cosh u)) := by
    simpa only [pow_one] using (integrable_logSineSech_abs_pow 1).const_mul 2
  apply hi.mono'
  · exact (((continuous_logSineClock hδ).sub continuous_id).abs.div
      Real.continuous_cosh (fun u => (Real.cosh_pos u).ne')).aestronglyMeasurable
  · filter_upwards with u
    rw [Real.norm_of_nonneg (div_nonneg (abs_nonneg _) (Real.cosh_pos u).le)]
    exact clock_difference_bound hδ u

private theorem tendsto_clock_difference {d : ℕ → ℝ} (hd : ∀ n, 0 ≤ d n)
    (hlim : Tendsto d atTop (𝓝 0)) :
    Tendsto (fun n => ∫ u : ℝ, |logSineClock (d n) u - u| / Real.cosh u) atTop (𝓝 0) := by
  have hw : Tendsto d atTop (𝓝[≥] (0 : ℝ)) :=
    tendsto_inf.mpr ⟨hlim, tendsto_principal.mpr (Filter.Eventually.of_forall hd)⟩
  have hi : Integrable (fun u : ℝ => 2 * (|u| / Real.cosh u)) := by
    simpa only [pow_one] using (integrable_logSineSech_abs_pow 1).const_mul 2
  have hm : ∀ᶠ n in atTop,
      AEStronglyMeasurable (fun u : ℝ => |logSineClock (d n) u - u| / Real.cosh u) volume :=
    Filter.Eventually.of_forall fun n => (integrable_clock_difference (hd n)).aestronglyMeasurable
  have hb : ∀ᶠ n in atTop, ∀ᵐ u : ℝ ∂volume,
      ‖|logSineClock (d n) u - u| / Real.cosh u‖ ≤ 2 * (|u| / Real.cosh u) := by
    filter_upwards with n
    filter_upwards with u
    rw [Real.norm_of_nonneg (div_nonneg (abs_nonneg _) (Real.cosh_pos u).le)]
    exact clock_difference_bound (hd n) u
  have hp : ∀ᵐ u : ℝ ∂volume, Tendsto
      (fun n => |logSineClock (d n) u - u| / Real.cosh u) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards with u
    have h := (tendsto_logSineClock_parameter_zero u).comp hw
    simpa only [sub_self, abs_zero, zero_div] using! (h.sub_const u).abs.div_const (Real.cosh u)
  have h := tendsto_integral_filter_of_dominated_convergence
    (fun u : ℝ => 2 * (|u| / Real.cosh u)) hm hb hi hp
  simpa only [integral_zero] using h

private theorem norm_clock_transform_difference {δ : ℝ} (hδ : 0 ≤ δ) (x : ℝ) :
    ‖logSineClockTransform δ x - logSineClockTransform 0 x‖ ≤
      |x| * ∫ u : ℝ, |logSineClock δ u - u| / Real.cosh u := by
  unfold logSineClockTransform
  rw [← integral_sub (integrable_clock_real_integrand hδ x)
    (integrable_clock_real_integrand le_rfl x)]
  calc
    _ ≤ ∫ u : ℝ, ‖Complex.exp (Complex.I * (x : ℂ) * (logSineClock δ u : ℂ)) /
        (Real.cosh u : ℂ) - Complex.exp (Complex.I * (x : ℂ) * (logSineClock 0 u : ℂ)) /
          (Real.cosh u : ℂ)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ u : ℝ, |x| * (|logSineClock δ u - u| / Real.cosh u) := by
      apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun u => norm_nonneg _)
        ((integrable_clock_difference hδ).const_mul |x|)
      filter_upwards with u
      rw [logSineClock_zero_parameter, ← sub_div, norm_div, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (Real.cosh_pos u)]
      have hp := clock_phase_difference (x * logSineClock δ u) (x * u)
      simp only [Complex.ofReal_mul, ← mul_assoc] at hp
      rw [← mul_sub, abs_mul] at hp
      calc
        _ ≤ (|x| * |logSineClock δ u - u|) / Real.cosh u :=
          div_le_div_of_nonneg_right hp (Real.cosh_pos u).le
        _ = _ := by ring
    _ = _ := integral_const_mul _ _

/-- The literal transforms converge uniformly on every bounded real window as the
positive regularization tends to zero. -/
theorem tendstoUniformlyOn_logSineClockTransform {d : ℕ → ℝ} (hd : ∀ n, 0 ≤ d n)
    (hlim : Tendsto d atTop (𝓝 0)) (R : ℝ) :
    TendstoUniformlyOn (fun n (x : ℝ) => logSineClockTransform (d n) x)
      (fun x : ℝ => logSineClockTransform 0 x) atTop (Icc (-R) R) := by
  have hD := tendsto_clock_difference hd hlim
  have hRD : Tendsto (fun n => R * ∫ u : ℝ, |logSineClock (d n) u - u| / Real.cosh u)
      atTop (𝓝 0) := by simpa only [mul_zero] using hD.const_mul R
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [hRD.eventually (gt_mem_nhds hε)] with n hn x hx
  have hxR : |x| ≤ R := abs_le.mpr ⟨hx.1, hx.2⟩
  have hD0 : 0 ≤ ∫ u : ℝ, |logSineClock (d n) u - u| / Real.cosh u :=
    integral_nonneg fun u => div_nonneg (abs_nonneg _) (Real.cosh_pos u).le
  have hb := (norm_clock_transform_difference (hd n) x).trans
    (mul_le_mul_of_nonneg_right hxR hD0)
  rw [dist_eq_norm, norm_sub_rev]
  exact hb.trans_lt hn


/-- The degenerate clock has the exact meromorphic sech transform on the real axis. -/
theorem logSineClockTransform_zero_parameter (x : ℝ) :
    logSineClockTransform 0 x = (Real.pi : ℂ) / Complex.cosh (Real.pi * (x : ℂ) / 2) := by
  have h := GaloisForLFunctions.HTGeometry.integral_cexp_div_cosh
    (z := -(x : ℂ)) (by simp)
  have he : (fun u : ℝ => Complex.exp (-(-(x : ℂ) * (u : ℂ)) * Complex.I) /
      (Real.cosh u : ℂ)) = fun u : ℝ =>
      Complex.exp (Complex.I * (x : ℂ) * (logSineClock 0 u : ℂ)) / (Real.cosh u : ℂ) := by
    funext u
    rw [logSineClock_zero_parameter]
    congr 2
    ring
  rw [he] at h
  have hc : (Real.pi : ℂ) * -(x : ℂ) / 2 = -(Real.pi * (x : ℂ) / 2) := by ring
  rw [hc, Complex.cosh_neg] at h
  exact h

private theorem clock_laguerrePolya_of_realZeros {δ : ℝ} (hδ : 0 < δ)
    (hreal : ∀ z, logSineClockTransform δ z = 0 → z.im = 0) :
    GaloisForLFunctions.HTGeometry.LaguerrePolya (logSineClockTransform δ) := by
  obtain ⟨K, hK, hb⟩ := logSineClockTransform_order_one hδ
  have hf := analyticOnNhd_logSineClockTransform hδ
  have h0 : logSineClockTransform δ 0 ≠ 0 := by
    rw [logSineClockTransform_zero]
    exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have horder : ∀ z, analyticOrderAt (logSineClockTransform δ) z ≠ ⊤ := by
    intro z hz
    have he := (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero z (fun z => hf z (mem_univ z))).mp hz
    exact h0 (congrFun he 0)
  exact OrderOneHadamard.laguerrePolya_of_even_of_realZeros hK hf h0
    (by rw [logSineClockTransform_zero]; exact Complex.ofReal_im _)
    horder (logSineClockTransform_even δ) hb hreal

private theorem cosh_real_scale_ne_zero (x : ℝ) :
    Complex.cosh (Real.pi * (x : ℂ) / 2) ≠ 0 := by
  have he : (Real.pi : ℂ) * (x : ℂ) / 2 = ((Real.pi * x / 2 : ℝ) : ℂ) := by push_cast; rfl
  rw [he, ← Complex.ofReal_cosh]
  exact Complex.ofReal_ne_zero.mpr (Real.cosh_pos _).ne'

private theorem clock_no_real_zero_sequence {d : ℕ → ℝ} (hd : ∀ n, 0 < d n)
    (hlim : Tendsto d atTop (𝓝 0))
    (hreal : ∀ n z, logSineClockTransform (d n) z = 0 → z.im = 0) : False := by
  let G : ℂ → ℂ := fun z => (Real.pi : ℂ) / Complex.cosh (Real.pi * z / 2)
  have hLP : ∀ n, GaloisForLFunctions.HTGeometry.LaguerrePolya
      (logSineClockTransform (d n)) := fun n => clock_laguerrePolya_of_realZeros (hd n) (hreal n)
  have hc : ContinuousOn (fun x : ℝ => G x) (Icc (-1) 1) := by
    apply Continuous.continuousOn
    exact continuous_const.div (Complex.continuous_cosh.comp
      ((continuous_const.mul Complex.continuous_ofReal).div_const 2)) cosh_real_scale_ne_zero
  have hn : ∀ x : ℝ, |x| ≤ 1 → G x ≠ 0 := by
    intro x _
    exact div_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) (cosh_real_scale_ne_zero x)
  have hconv : TendstoUniformlyOn (fun n (x : ℝ) => logSineClockTransform (d n) x)
      (fun x : ℝ => G x) atTop (Icc (-1) 1) := by
    simpa only [logSineClockTransform_zero_parameter] using
      tendstoUniformlyOn_logSineClockTransform (fun n => (hd n).le) hlim 1
  obtain ⟨σ, g, _, hg, _, hmatch⟩ :=
    IntervalLaguerrePolya.exists_subseq_reflectProduct_tendstoLocallyUniformly_of_window
      hLP (by norm_num : (0 : ℝ) < 1) hc hn hconv
  have hid : ∀ z : ℂ, g z * Complex.cosh (Real.pi * z / 2) ^ 2 - (Real.pi : ℂ) ^ 2 = 0 := by
    apply GaloisForLFunctions.HTGeometry.entire_eq_zero_of_vanishing_on_real_interval
      ((hg.mul ((Complex.differentiable_cosh.comp
        (((differentiable_const (Real.pi : ℂ)).mul differentiable_id).div_const 2)).pow 2)).sub
        (differentiable_const ((Real.pi : ℂ) ^ 2)))
      (t₀ := 0) (r := 1) (by norm_num)
    intro t ht
    have ht1 : |t| < 1 := by simpa only [sub_zero] using ht
    change g (t : ℂ) * Complex.cosh (Real.pi * (t : ℂ) / 2) ^ 2 - (Real.pi : ℂ) ^ 2 = 0
    rw [hmatch t (abs_le.mp ht1.le)]
    dsimp only [G]
    rw [show (Real.pi : ℂ) * -(t : ℂ) / 2 = -(Real.pi * (t : ℂ) / 2) by ring,
      Complex.cosh_neg]
    field_simp [cosh_real_scale_ne_zero t]; ring
  have hz : Complex.cosh ((Real.pi : ℂ) * Complex.I / 2) = 0 := by
    rw [show (Real.pi : ℂ) * Complex.I / 2 = ((Real.pi : ℂ) / 2) * Complex.I by ring,
      Complex.cosh_mul_I, Complex.cos_pi_div_two]
  have hbad := hid Complex.I
  rw [hz, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_sub, neg_eq_zero] at hbad
  exact pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) hbad

/-- Every sufficiently small positive regularization has a nonreal zero. -/
theorem exists_nonreal_zero_logSineClockTransform :
    ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ → δ < η →
      ∃ z : ℂ, logSineClockTransform δ z = 0 ∧ z.im ≠ 0 := by
  classical
  by_contra h
  push Not at h
  have hb : ∀ n : ℕ, ∃ δ : ℝ, 0 < δ ∧ δ < 1 / ((n : ℝ) + 1) ∧
      ∀ z : ℂ, logSineClockTransform δ z = 0 → z.im = 0 := by
    intro n
    exact h (1 / ((n : ℝ) + 1)) (by positivity)
  choose d hd hsmall hreal using hb
  have hlim : Tendsto d atTop (𝓝 0) := squeeze_zero (fun n => (hd n).le)
    (fun n => (hsmall n).le) tendsto_one_div_add_atTop_nhds_zero_nat
  exact clock_no_real_zero_sequence hd hlim hreal



/-- The fixed base coordinate covers the complete open quantile interval. -/
theorem logSineBaseCoordinate_image_univ :
    logSineBaseCoordinate '' univ = Ioo (0 : ℝ) 1 := by
  ext t
  constructor
  · rintro ⟨u, _, rfl⟩
    exact logSineBaseCoordinate_mem u
  · intro ht
    have ha : 0 < Real.pi * t / 2 := div_pos (mul_pos Real.pi_pos ht.1) (by norm_num)
    have hb : Real.pi * t / 2 < Real.pi / 2 := by nlinarith [Real.pi_pos, ht.2]
    have htan := Real.tan_pos_of_pos_of_lt_pi_div_two ha hb
    refine ⟨Real.log (Real.tan (Real.pi * t / 2)), mem_univ _, ?_⟩
    unfold logSineBaseCoordinate
    rw [Real.exp_log htan, Real.arctan_tan (by linarith [Real.pi_pos]) hb]
    field_simp

theorem logSineBaseCoordinate_injective : Function.Injective logSineBaseCoordinate := by
  intro u v h
  apply Real.exp_injective
  apply Real.arctan_injective
  unfold logSineBaseCoordinate at h
  field_simp at h
  linarith

/-- Fourier transform of the literal reciprocal-profile quantile clock. -/
def logSineQuantileTransform (δ : ℝ) (z : ℂ) : ℂ :=
  ∫ t in Ioo (0 : ℝ) 1, Complex.exp (Complex.I * z * (logSineQuantileClock δ t : ℂ))

/-- Exact whole-line change of variables; the normalization and spectral scale are retained. -/
theorem logSineQuantileTransform_eq_clockTransform {δ : ℝ} (hδ : 0 ≤ δ) (z : ℂ) :
    logSineQuantileTransform δ z = logSineClockTransform δ (z / Real.pi) / Real.pi := by
  have hs := integral_image_eq_integral_abs_deriv_smul (f := logSineBaseCoordinate)
    (f' := fun u => 1 / (Real.pi * Real.cosh u)) MeasurableSet.univ
    (fun u _ => (hasDerivAt_logSineBaseCoordinate u).hasDerivWithinAt)
    logSineBaseCoordinate_injective.injOn
    (fun t : ℝ => Complex.exp (Complex.I * z * (logSineQuantileClock δ t : ℂ)))
  rw [logSineBaseCoordinate_image_univ, setIntegral_univ] at hs
  unfold logSineQuantileTransform
  rw [hs]
  have he : (fun u : ℝ => |1 / (Real.pi * Real.cosh u)| •
      Complex.exp (Complex.I * z * (logSineQuantileClock δ (logSineBaseCoordinate u) : ℂ))) =
      fun u : ℝ => (Real.pi : ℂ)⁻¹ *
        (Complex.exp (Complex.I * (z / Real.pi) * (logSineClock δ u : ℂ)) /
          (Real.cosh u : ℂ)) := by
    funext u
    rw [abs_of_pos (by positivity), logSineQuantileClock_baseCoordinate hδ,
      Complex.real_smul]
    push_cast
    have hexp : Complex.I * z * ((logSineClock δ u : ℂ) / Real.pi) =
        Complex.I * (z / Real.pi) * (logSineClock δ u : ℂ) := by ring
    rw [hexp]
    ring
  rw [he, integral_const_mul]
  unfold logSineClockTransform
  ring

/-- The pole obstruction holds for the original reciprocal-profile quantile transform. -/
theorem exists_nonreal_zero_logSineQuantileTransform :
    ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ → δ < η →
      ∃ z : ℂ, logSineQuantileTransform δ z = 0 ∧ z.im ≠ 0 := by
  obtain ⟨η, hη, hz⟩ := exists_nonreal_zero_logSineClockTransform
  refine ⟨η, hη, fun δ hδ hsmall => ?_⟩
  obtain ⟨z, hz0, hzne⟩ := hz δ hδ hsmall
  refine ⟨(Real.pi : ℂ) * z, ?_, ?_⟩
  · rw [logSineQuantileTransform_eq_clockTransform hδ.le]
    have he : (Real.pi : ℂ) * z / Real.pi = z := by field_simp
    rw [he, hz0, zero_div]
  · simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero] using
      mul_ne_zero Real.pi_ne_zero hzne

/-- Source-level obstruction: strict concavity, positive conductances and every
finite shifted Hankel inequality coexist with a nonreal zero of the literal transform. -/
theorem logSine_positive_hankel_nonreal_zero :
    ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ → δ < η →
      StrictConcaveOn ℝ (Ioo (0 : ℝ) 1) (logSineProfile δ) ∧
      (∀ n : ℕ, 0 < logSineConductance δ (n + 1)) ∧
      (∀ (shift : ℕ) (F : Finset ℕ) (c : ℕ → ℝ),
        0 ≤ ∑ m ∈ F, ∑ n ∈ F, c m * c n * logSineConductance δ (m + n + shift + 1)) ∧
      ∃ z : ℂ, logSineQuantileTransform δ z = 0 ∧ z.im ≠ 0 := by
  obtain ⟨η, hη, hz⟩ := exists_nonreal_zero_logSineQuantileTransform
  exact ⟨η, hη, fun δ hδ hsmall => ⟨strictConcaveOn_logSineProfile hδ.le,
    logSineConductance_succ_pos hδ.le, logSineConductance_hankel_nonneg hδ.le,
    hz δ hδ hsmall⟩⟩

end
end RHTower
