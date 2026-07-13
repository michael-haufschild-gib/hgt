import GaloisForLFunctions.RHTower.ThetaCuspTiltedSchwartz
import GaloisForLFunctions.RHTower.ThetaCuspSchwartzFourierXi
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Fourier–Laplace reconstruction of the theta-cusp source

The Fourier transform of the theta-cusp Schwartz source extends to a Fourier–Laplace transform
on the open strip `|im w| < 1`.  A direct dominated-differentiation argument proves that this
extension is analytic there.  Since its restriction to the real axis is `XiC`, the identity
theorem identifies the whole strip with `XiC`.

Consequently, the genuine exponentially tilted source has the exact horizontal-line transform
`XiC (b + a * I)`.  No moment determinacy or abstract reconstruction interface is assumed: the
source, its integrability, strip analyticity, and Fourier identity are all constructed here.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped FourierTransform SchwartzMap

noncomputable section

namespace RHTower

def thetaCuspFourierLaplaceIntegrand (w : ℂ) (x : ℝ) : ℂ :=
  Complex.exp (-I * w * (x : ℂ)) * (thetaCuspFullSource x : ℂ)

def thetaCuspFourierLaplace (w : ℂ) : ℂ :=
  ∫ x : ℝ, thetaCuspFourierLaplaceIntegrand w x

theorem integrable_exp_neg_mul_abs {c : ℝ} (hc : 0 < c) :
    Integrable (fun x : ℝ => Real.exp (-c * |x|)) := by
  have hpos : IntegrableOn (fun x : ℝ => Real.exp (-c * |x|)) (Ioi 0) := by
    have h := integrableOn_exp_mul_Ioi (a := -c) (neg_lt_zero.mpr hc) 0
    exact h.congr_fun
      (fun x hx => by rw [abs_of_pos hx])
      measurableSet_Ioi
  have hneg : IntegrableOn (fun x : ℝ => Real.exp (-c * |x|)) (Iic 0) := by
    have h := integrableOn_exp_mul_Iic (a := c) hc 0
    exact h.congr_fun
      (fun x hx => by rw [abs_of_nonpos hx]; ring_nf)
      measurableSet_Iic
  simpa [Ioi_union_Iic] using hpos.union hneg

theorem norm_thetaCuspFourierLaplaceIntegrand_le
    (w : ℂ) (x : ℝ) :
    ‖thetaCuspFourierLaplaceIntegrand w x‖ ≤
      thetaCuspDerivativeExpConstant 0 *
        Real.exp (-(1 - |w.im|) * |x|) := by
  have hk := abs_iteratedDeriv_thetaCuspFullSource_le_exp_neg_abs 0 x
  rw [iteratedDeriv_zero] at hk
  have himx : w.im * x ≤ |w.im| * |x| := by
    calc
      w.im * x ≤ |w.im * x| := le_abs_self _
      _ = |w.im| * |x| := abs_mul _ _
  rw [thetaCuspFourierLaplaceIntegrand, norm_mul, Complex.norm_exp,
    norm_real, Real.norm_eq_abs]
  have hre : (-I * w * (x : ℂ)).re = w.im * x := by
    simp [mul_re]
  rw [hre]
  calc
    Real.exp (w.im * x) * |thetaCuspFullSource x| ≤
        Real.exp (|w.im| * |x|) *
          (thetaCuspDerivativeExpConstant 0 * Real.exp (-|x|)) := by
      gcongr
    _ = thetaCuspDerivativeExpConstant 0 *
        Real.exp (-(1 - |w.im|) * |x|) := by
      rw [show Real.exp (|w.im| * |x|) *
          (thetaCuspDerivativeExpConstant 0 * Real.exp (-|x|)) =
        thetaCuspDerivativeExpConstant 0 *
          (Real.exp (|w.im| * |x|) * Real.exp (-|x|)) by ring,
        ← Real.exp_add]
      congr 1
      ring

theorem integrable_thetaCuspFourierLaplaceIntegrand
    {w : ℂ} (hw : |w.im| < 1) :
    Integrable (thetaCuspFourierLaplaceIntegrand w) := by
  let c : ℝ := 1 - |w.im|
  have hc : 0 < c := by dsimp [c]; linarith
  have hmajor : Integrable (fun x : ℝ =>
      thetaCuspDerivativeExpConstant 0 * Real.exp (-c * |x|)) :=
    (integrable_exp_neg_mul_abs hc).const_mul _
  apply hmajor.mono
  · unfold thetaCuspFourierLaplaceIntegrand
    have hk : Continuous thetaCuspFullSource :=
      contDiff_thetaCuspFullSource.continuous
    exact (by fun_prop (disch := assumption) : Continuous (fun x : ℝ =>
      Complex.exp (-I * w * (x : ℂ)) *
        (thetaCuspFullSource x : ℂ))).aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · simpa [c] using norm_thetaCuspFourierLaplaceIntegrand_le w x
    · exact mul_nonneg (thetaCuspDerivativeExpConstant_nonneg 0)
        (Real.exp_pos _).le

theorem thetaCuspFourierLaplace_ofReal (t : ℝ) :
    thetaCuspFourierLaplace (t : ℂ) = XiC (t : ℂ) := by
  rw [thetaCuspFourierLaplace]
  calc
    (∫ x : ℝ, thetaCuspFourierLaplaceIntegrand (t : ℂ) x) =
        FourierTransform.fourier (fun x : ℝ => thetaCuspSchwartz x)
          (t / (2 * Real.pi)) := by
      rw [Real.fourier_real_eq_integral_exp_smul]
      apply integral_congr_ae
      filter_upwards with x
      rw [thetaCuspSchwartz_apply]
      simp only [thetaCuspFourierLaplaceIntegrand, smul_eq_mul]
      congr 1
      push_cast
      field_simp [Real.pi_ne_zero]
    _ = XiC (t : ℂ) := fourier_thetaCuspSchwartz_scaled t

def thetaCuspFourierLaplaceDerivativeIntegrand (w : ℂ) (x : ℝ) : ℂ :=
  (-I * (x : ℂ)) * thetaCuspFourierLaplaceIntegrand w x

theorem hasDerivAt_thetaCuspFourierLaplaceIntegrand (w : ℂ) (x : ℝ) :
    HasDerivAt (fun z : ℂ => thetaCuspFourierLaplaceIntegrand z x)
      (thetaCuspFourierLaplaceDerivativeIntegrand w x) w := by
  have hlin : HasDerivAt (fun z : ℂ => -I * z * (x : ℂ))
      (-I * (x : ℂ)) w := by
    convert (((hasDerivAt_id w).const_mul (-I)).mul_const (x : ℂ)) using 1 <;> ring
  have hexp := hlin.cexp
  convert hexp.mul_const (thetaCuspFullSource x : ℂ) using 1 <;>
    simp [thetaCuspFourierLaplaceIntegrand,
      thetaCuspFourierLaplaceDerivativeIntegrand] <;> ring

theorem integrable_abs_mul_exp_neg_mul_abs {c : ℝ} (hc : 0 < c) :
    Integrable (fun x : ℝ => |x| * Real.exp (-c * |x|)) := by
  let d : ℝ := c / 2
  let A : ℝ := (Nat.factorial 1 : ℝ) / d
  have hd : 0 < d := by dsimp [d]; linarith
  have hmajor : Integrable (fun x : ℝ => A * Real.exp (-d * |x|)) :=
    (integrable_exp_neg_mul_abs hd).const_mul A
  apply hmajor.mono
  · exact (by fun_prop : Continuous (fun x : ℝ =>
      |x| * Real.exp (-c * |x|))).aestronglyMeasurable
  · filter_upwards with x
    have hp := pow_mul_exp_neg_mul_le_factorial_div 1 hd (abs_nonneg x)
    have hpA : |x| ^ 1 * Real.exp (-d * |x|) ≤ A := by
      simpa [A] using hp
    have hA : 0 ≤ A := by dsimp [A]; positivity
    have he : Real.exp (-c * |x|) =
        Real.exp (-d * |x|) * Real.exp (-d * |x|) := by
      rw [← Real.exp_add]
      congr 1
      dsimp [d]
      ring
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · rw [he]
      calc
        |x| * (Real.exp (-d * |x|) * Real.exp (-d * |x|)) =
            (|x| ^ 1 * Real.exp (-d * |x|)) *
              Real.exp (-d * |x|) := by ring
        _ ≤ A * Real.exp (-d * |x|) := by
          exact mul_le_mul_of_nonneg_right hpA (Real.exp_pos _).le
        _ = ‖A * Real.exp (-d * |x|)‖ := by
          have hnon : 0 ≤ A * Real.exp (-d * |x|) :=
            mul_nonneg hA (Real.exp_pos _).le
          rw [Real.norm_eq_abs, abs_of_nonneg hnon]
    · exact mul_nonneg (abs_nonneg x) (Real.exp_pos _).le

theorem hasDerivAt_thetaCuspFourierLaplace
    {w₀ : ℂ} (hw₀ : |w₀.im| < 1) :
    HasDerivAt thetaCuspFourierLaplace
      (∫ x : ℝ, thetaCuspFourierLaplaceDerivativeIntegrand w₀ x) w₀ := by
  let ε : ℝ := (1 - |w₀.im|) / 4
  let B : ℝ := |w₀.im| + ε
  let c : ℝ := 1 - B
  let bound : ℝ → ℝ := fun x =>
    thetaCuspDerivativeExpConstant 0 *
      (|x| * Real.exp (-c * |x|))
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hc : 0 < c := by dsimp [c, B, ε]; linarith
  have hB : B < 1 := by dsimp [B, ε]; linarith
  have him {z : ℂ} (hz : z ∈ Metric.ball w₀ ε) : |z.im| ≤ B := by
    have hdist : ‖z - w₀‖ < ε := by
      rw [← dist_eq_norm]
      exact Metric.mem_ball.mp hz
    have himdiff : |z.im - w₀.im| ≤ ‖z - w₀‖ := by
      simpa only [Complex.sub_im] using Complex.abs_im_le_norm (z - w₀)
    calc
      |z.im| = |w₀.im + (z.im - w₀.im)| := by ring_nf
      _ ≤ |w₀.im| + |z.im - w₀.im| := abs_add_le _ _
      _ ≤ |w₀.im| + ε := by linarith
      _ = B := by rfl
  have hbound : Integrable bound := by
    exact (integrable_abs_mul_exp_neg_mul_abs hc).const_mul
      (thetaCuspDerivativeExpConstant 0)
  have hFmeas : ∀ z : ℂ,
      AEStronglyMeasurable (thetaCuspFourierLaplaceIntegrand z) := by
    intro z
    have hk : Continuous thetaCuspFullSource :=
      contDiff_thetaCuspFullSource.continuous
    unfold thetaCuspFourierLaplaceIntegrand
    exact (by fun_prop (disch := assumption) : Continuous (fun x : ℝ =>
      Complex.exp (-I * z * (x : ℂ)) *
        (thetaCuspFullSource x : ℂ))).aestronglyMeasurable
  have hF'meas : AEStronglyMeasurable
      (thetaCuspFourierLaplaceDerivativeIntegrand w₀) := by
    have hk : Continuous thetaCuspFullSource :=
      contDiff_thetaCuspFullSource.continuous
    unfold thetaCuspFourierLaplaceDerivativeIntegrand
      thetaCuspFourierLaplaceIntegrand
    exact (by fun_prop (disch := assumption) : Continuous (fun x : ℝ =>
      (-I * (x : ℂ)) *
        (Complex.exp (-I * w₀ * (x : ℂ)) *
          (thetaCuspFullSource x : ℂ)))).aestronglyMeasurable
  have hdom : ∀ᵐ x : ℝ, ∀ z ∈ Metric.ball w₀ ε,
      ‖thetaCuspFourierLaplaceDerivativeIntegrand z x‖ ≤ bound x := by
    filter_upwards with x
    intro z hz
    have hzB := him hz
    have hzstrip : |z.im| < 1 := lt_of_le_of_lt hzB hB
    have hbase := norm_thetaCuspFourierLaplaceIntegrand_le z x
    have hC : 0 ≤ thetaCuspDerivativeExpConstant 0 :=
      thetaCuspDerivativeExpConstant_nonneg 0
    have hrate : 1 - |z.im| ≥ c := by
      dsimp [c]
      linarith
    have hexp : Real.exp (-(1 - |z.im|) * |x|) ≤
        Real.exp (-c * |x|) := by
      apply Real.exp_le_exp.mpr
      nlinarith [abs_nonneg x]
    rw [thetaCuspFourierLaplaceDerivativeIntegrand, norm_mul,
      norm_mul, norm_neg, norm_I, one_mul, norm_real, Real.norm_eq_abs]
    dsimp [bound]
    calc
      |x| * ‖thetaCuspFourierLaplaceIntegrand z x‖ ≤
          |x| * (thetaCuspDerivativeExpConstant 0 *
            Real.exp (-(1 - |z.im|) * |x|)) := by gcongr
      _ ≤ |x| * (thetaCuspDerivativeExpConstant 0 *
            Real.exp (-c * |x|)) := by
        gcongr
      _ = thetaCuspDerivativeExpConstant 0 *
          (|x| * Real.exp (-c * |x|)) := by ring
  have hresult := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := thetaCuspFourierLaplaceIntegrand)
    (F' := thetaCuspFourierLaplaceDerivativeIntegrand)
    (x₀ := w₀) (s := Metric.ball w₀ ε) (bound := bound)
    (Metric.ball_mem_nhds w₀ hε)
    (Filter.Eventually.of_forall hFmeas)
    (integrable_thetaCuspFourierLaplaceIntegrand hw₀)
    hF'meas hdom hbound
    (by
      filter_upwards with x
      intro z hz
      exact hasDerivAt_thetaCuspFourierLaplaceIntegrand z x)
  simpa only [thetaCuspFourierLaplace] using hresult.2

theorem differentiableAt_thetaCuspFourierLaplace
    {w₀ : ℂ} (hw₀ : |w₀.im| < 1) :
    DifferentiableAt ℂ thetaCuspFourierLaplace w₀ :=
  (hasDerivAt_thetaCuspFourierLaplace hw₀).differentiableAt

def thetaCuspFourierLaplaceStrip : Set ℂ :=
  {w : ℂ | -1 < w.im ∧ w.im < 1}

theorem isOpen_thetaCuspFourierLaplaceStrip :
    IsOpen thetaCuspFourierLaplaceStrip := by
  rw [thetaCuspFourierLaplaceStrip]
  change IsOpen ({w : ℂ | -1 < w.im} ∩ {w : ℂ | w.im < 1})
  exact (isOpen_lt continuous_const (by fun_prop)).inter
    (isOpen_lt (by fun_prop) continuous_const)

theorem isPreconnected_thetaCuspFourierLaplaceStrip :
    IsPreconnected thetaCuspFourierLaplaceStrip := by
  rw [thetaCuspFourierLaplaceStrip]
  change IsPreconnected ({w : ℂ | -1 < w.im} ∩ {w : ℂ | w.im < 1})
  exact ((convex_halfSpace_im_gt (-1)).inter
    (convex_halfSpace_im_lt 1)).isPreconnected

theorem analyticOnNhd_thetaCuspFourierLaplace :
    AnalyticOnNhd ℂ thetaCuspFourierLaplace thetaCuspFourierLaplaceStrip := by
  have hd : DifferentiableOn ℂ thetaCuspFourierLaplace
      thetaCuspFourierLaplaceStrip := by
    intro w hw
    exact (differentiableAt_thetaCuspFourierLaplace
      (abs_lt.mpr hw)).differentiableWithinAt
  exact hd.analyticOnNhd isOpen_thetaCuspFourierLaplaceStrip

theorem thetaCuspFourierLaplace_eq_XiC_on_strip :
    Set.EqOn thetaCuspFourierLaplace XiC thetaCuspFourierLaplaceStrip := by
  let F : ℂ → ℂ := fun w => thetaCuspFourierLaplace w - XiC w
  have hF : AnalyticOnNhd ℂ F thetaCuspFourierLaplaceStrip :=
    analyticOnNhd_thetaCuspFourierLaplace.sub
      (XiC_analytic.mono fun _ _ => Set.mem_univ _)
  have hzeroReal (t : ℝ) : F (t : ℂ) = 0 := by
    dsimp [F]
    rw [thetaCuspFourierLaplace_ofReal]
    ring
  let u : ℕ → ℂ := fun n =>
    ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)
  have hu_tend : Tendsto u atTop (𝓝 0) := by
    have hreal : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hcomp := Complex.continuous_ofReal.continuousAt.tendsto.comp hreal
    simpa [u, Function.comp_def] using hcomp
  have hu_ne (n : ℕ) : u n ≠ 0 := by
    dsimp [u]
    norm_cast
    positivity
  have hu_within : Tendsto u atTop (nhdsWithin 0 ({0} : Set ℂ)ᶜ) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hu_tend, Filter.Eventually.of_forall (fun n => by simpa using hu_ne n)⟩
  have hu_zero : ∀ n : ℕ, F (u n) = 0 := by
    intro n
    exact hzeroReal (1 / ((n : ℝ) + 1))
  have hfreq : ∃ᶠ w in nhdsWithin 0 ({0} : Set ℂ)ᶜ, F w = 0 :=
    hu_within.frequently (Filter.Eventually.of_forall hu_zero).frequently
  have h0mem : (0 : ℂ) ∈ thetaCuspFourierLaplaceStrip := by
    simp [thetaCuspFourierLaplaceStrip]
  have hzero : Set.EqOn F 0 thetaCuspFourierLaplaceStrip :=
    hF.eqOn_zero_of_preconnected_of_frequently_eq_zero
      isPreconnected_thetaCuspFourierLaplaceStrip h0mem hfreq
  intro w hw
  have := hzero hw
  dsimp [F] at this
  exact sub_eq_zero.mp this

theorem fourier_thetaCuspTiltedSchwartz_scaled
    {a : ℝ} (ha : |a| < 1) (b : ℝ) :
    FourierTransform.fourier (thetaCuspTiltedSchwartz a ha)
        (b / (2 * Real.pi)) =
      XiC ((b : ℂ) + (a : ℂ) * I) := by
  rw [SchwartzMap.fourier_coe,
    Real.fourier_real_eq_integral_exp_smul]
  have hIntegral :
      (∫ x : ℝ,
        Complex.exp (↑(-2 * Real.pi * x * (b / (2 * Real.pi))) * I) •
          thetaCuspTiltedSchwartz a ha x) =
        thetaCuspFourierLaplace ((b : ℂ) + (a : ℂ) * I) := by
    rw [thetaCuspFourierLaplace]
    apply integral_congr_ae
    filter_upwards with x
    rw [thetaCuspTiltedSchwartz_apply]
    simp only [smul_eq_mul, thetaCuspFourierLaplaceIntegrand]
    rw [show ((Real.exp (a * x) * thetaCuspFullSource x : ℝ) : ℂ) =
        (Real.exp (a * x) : ℂ) * (thetaCuspFullSource x : ℂ) by norm_cast,
      Complex.ofReal_exp]
    rw [← mul_assoc, ← Complex.exp_add]
    congr 1
    push_cast
    field_simp [Real.pi_ne_zero]
    congr 1
    simp [mul_add, mul_assoc]
    simp [← mul_assoc, I_mul_I]
    ring
  rw [hIntegral]
  apply thetaCuspFourierLaplace_eq_XiC_on_strip
  simp only [thetaCuspFourierLaplaceStrip, Set.mem_setOf_eq,
    add_im, ofReal_im, mul_im, I_re, I_im, zero_add, mul_one]
  have ha' : -1 < a ∧ a < 1 := abs_lt.mp ha
  simpa using ha'

end RHTower
