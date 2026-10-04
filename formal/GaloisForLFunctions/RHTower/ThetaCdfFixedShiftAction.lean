import GaloisForLFunctions.RHTower.HedenmalmIntervalAnomaly
import GaloisForLFunctions.RHTower.HedenmalmQuantileNormalForm
import GaloisForLFunctions.RHTower.ThetaCuspKernelLogConcavity
import GaloisForLFunctions.RHTower.CausalThetaHalfLaplace
import GaloisForLFunctions.RHTower.HedenmalmThetaSourceUnconditional

/-!
# The theta CDF action: hazard, endpoint ratio and the fixed-shift law

`k` is the positive even theta density, `M = ∫ k`, `F` its CDF, `q = M/k(Q)` the quantile speed.
The hazard `h = k'/k` is strictly decreasing (strict log-concavity), odd, and tends to `±∞` at
`∓∞` (double-exponential tails).  The tangent bound `k(y) ≤ k(x)e^{h(x)(y−x)}` gives
`I(x) = ∫_{−∞}^x k ≤ k(x)/h(x)`, so the endpoint ratio `r = I/k` (`= t q(t)` at `t = F(x)`) is
nondecreasing with integrable derivative `1 − r h` and tends to `0` at `−∞`.

The action `Φ_n = ∫₀¹ q(t)(1 − cos 2πnt) dt = ∫ (1 − cos 2πnF(x)) dx` then satisfies, for every fixed
integer `a`, `Φ_{n+a} − Φ_n = o(1/n)`, and `Φ_n → ∞`.
-/

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

open HedenmalmThetaSource

noncomputable section

/-! ## The hazard -/

/-- The hazard `h = k'/k = (log k)'`. -/
def thetaLogHazard (x : ℝ) : ℝ := deriv thetaCuspFullSource x / thetaCuspFullSource x

theorem hasDerivAt_thetaCuspLogSource_hazard (x : ℝ) :
    HasDerivAt thetaCuspLogSource (thetaLogHazard x) x := by
  have h := hasDerivAt_thetaCuspLogSource x
  rwa [iteratedDeriv_one] at h

theorem deriv_thetaCuspLogSource : deriv thetaCuspLogSource = thetaLogHazard :=
  funext fun x => (hasDerivAt_thetaCuspLogSource_hazard x).deriv

theorem strictAnti_thetaLogHazard : StrictAnti thetaLogHazard := by
  have h := strictConcaveOn_thetaCuspLogSource.strictAntiOn_deriv
    (fun x _ => (hasDerivAt_thetaCuspLogSource_hazard x).differentiableAt)
  rw [deriv_thetaCuspLogSource] at h
  exact fun x y hxy => h (mem_univ x) (mem_univ y) hxy

theorem deriv_thetaCuspFullSource_neg (x : ℝ) :
    deriv thetaCuspFullSource (-x) = -deriv thetaCuspFullSource x := by
  have h1 := (differentiable_thetaCuspFullSource (-x)).hasDerivAt.comp x (hasDerivAt_neg x)
  have h2 : (thetaCuspFullSource ∘ fun y => -y) = thetaCuspFullSource :=
    funext fun y => thetaCuspFullSource_neg y
  rw [h2] at h1
  have := h1.unique (differentiable_thetaCuspFullSource x).hasDerivAt
  linarith

theorem thetaLogHazard_neg (x : ℝ) : thetaLogHazard (-x) = -thetaLogHazard x := by
  rw [thetaLogHazard, thetaLogHazard, deriv_thetaCuspFullSource_neg, thetaCuspFullSource_neg, neg_div]

theorem thetaLogHazard_zero : thetaLogHazard 0 = 0 := by
  have h := thetaLogHazard_neg 0
  rw [neg_zero] at h
  linarith

theorem thetaLogHazard_nonneg_of_nonpos {x : ℝ} (hx : x ≤ 0) : 0 ≤ thetaLogHazard x := by
  rw [← thetaLogHazard_zero]; exact strictAnti_thetaLogHazard.antitone hx

theorem deriv_thetaCuspFullSource_eq (x : ℝ) :
    deriv thetaCuspFullSource x = thetaLogHazard x * thetaCuspFullSource x := by
  rw [thetaLogHazard, div_mul_cancel₀ _ (thetaCuspFullSource_pos_all x).ne']

/-- **Double-exponential tails force an unbounded hazard.** -/
theorem exists_thetaLogHazard_le (L : ℝ) : ∃ x : ℝ, 0 ≤ x ∧ thetaLogHazard x ≤ -L := by
  by_contra hcon
  push Not at hcon
  obtain ⟨C, hC0, hC⟩ := exists_abs_thetaCuspFullSource_le (L + 1)
  have hk0 := thetaCuspFullSource_pos_all 0
  have hlow : ∀ x : ℝ, 0 < x → Real.log (thetaCuspFullSource 0) - L * x ≤
      Real.log (thetaCuspFullSource x) := by
    intro x hx
    obtain ⟨c, hc, hceq⟩ := exists_hasDerivAt_eq_slope thetaCuspLogSource thetaLogHazard hx
      (fun y _ => (hasDerivAt_thetaCuspLogSource_hazard y).continuousAt.continuousWithinAt)
      (fun y _ => hasDerivAt_thetaCuspLogSource_hazard y)
    have h1 := hcon c hc.1.le
    rw [hceq, sub_zero, lt_div_iff₀ hx] at h1
    simp only [thetaCuspLogSource] at h1
    linarith
  set x : ℝ := Real.log (C / thetaCuspFullSource 0 + 1) + 1
  have hx : 0 < x := by
    have : 0 ≤ Real.log (C / thetaCuspFullSource 0 + 1) :=
      Real.log_nonneg (by linarith [show (0 : ℝ) ≤ C / thetaCuspFullSource 0 from by positivity])
    linarith
  have h1 := hlow x hx
  have h2 := hC x
  rw [abs_of_pos (thetaCuspFullSource_pos_all x), abs_of_pos hx] at h2
  have h3 : thetaCuspFullSource 0 * Real.exp (-(L * x)) ≤ C * Real.exp (-((L + 1) * x)) := by
    calc thetaCuspFullSource 0 * Real.exp (-(L * x))
        = Real.exp (Real.log (thetaCuspFullSource 0) - L * x) := by
          rw [Real.exp_sub, Real.exp_log hk0, div_eq_mul_inv, ← Real.exp_neg]
      _ ≤ Real.exp (Real.log (thetaCuspFullSource x)) := Real.exp_le_exp.2 h1
      _ = thetaCuspFullSource x := Real.exp_log (thetaCuspFullSource_pos_all x)
      _ ≤ _ := h2
  have h4 : Real.exp x ≤ C / thetaCuspFullSource 0 := by
    rw [le_div_iff₀ hk0]
    have hsplit : Real.exp (-((L + 1) * x)) = Real.exp (-(L * x)) * Real.exp (-x) := by
      rw [← Real.exp_add]; ring_nf
    rw [hsplit] at h3
    have he := Real.exp_pos (-(L * x))
    have h3' : thetaCuspFullSource 0 ≤ C * Real.exp (-x) :=
      le_of_mul_le_mul_right (h3.trans_eq (by ring)) he
    have hex : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
    calc Real.exp x * thetaCuspFullSource 0 ≤ Real.exp x * (C * Real.exp (-x)) :=
          mul_le_mul_of_nonneg_left h3' (Real.exp_pos x).le
      _ = C * (Real.exp x * Real.exp (-x)) := by ring
      _ = C := by rw [hex, mul_one]
  have h5 : C / thetaCuspFullSource 0 + 1 < Real.exp x := by
    calc C / thetaCuspFullSource 0 + 1 = Real.exp (Real.log (C / thetaCuspFullSource 0 + 1)) :=
          (Real.exp_log (by linarith [show (0 : ℝ) ≤ C / thetaCuspFullSource 0 from by positivity])).symm
      _ < Real.exp x := Real.exp_lt_exp.2 (by linarith)
  linarith

theorem tendsto_thetaLogHazard_atTop : Tendsto thetaLogHazard atTop atBot := by
  refine tendsto_atTop_atBot.2 fun b => ?_
  obtain ⟨x, -, hx⟩ := exists_thetaLogHazard_le (-b)
  exact ⟨x, fun y hy => (strictAnti_thetaLogHazard.antitone hy).trans (by linarith)⟩

theorem tendsto_thetaLogHazard_atBot : Tendsto thetaLogHazard atBot atTop := by
  have h := tendsto_neg_atBot_atTop.comp (tendsto_thetaLogHazard_atTop.comp tendsto_neg_atBot_atTop)
  refine h.congr fun x => ?_
  simp [Function.comp, thetaLogHazard_neg]

/-- **Tangent bound from log-concavity.**  `k(y) ≤ k(x) e^{h(x)(y−x)}`. -/
theorem thetaCuspFullSource_le_tangent (x y : ℝ) :
    thetaCuspFullSource y ≤ thetaCuspFullSource x * Real.exp (thetaLogHazard x * (y - x)) := by
  have hlog : thetaCuspLogSource y ≤ thetaCuspLogSource x + thetaLogHazard x * (y - x) := by
    rcases lt_trichotomy y x with hyx | rfl | hxy
    · obtain ⟨c, hc, hceq⟩ := exists_hasDerivAt_eq_slope thetaCuspLogSource thetaLogHazard hyx
        (fun z _ => (hasDerivAt_thetaCuspLogSource_hazard z).continuousAt.continuousWithinAt)
        (fun z _ => hasDerivAt_thetaCuspLogSource_hazard z)
      have hmono : thetaLogHazard x ≤ thetaLogHazard c := strictAnti_thetaLogHazard.antitone hc.2.le
      rw [hceq, le_div_iff₀ (by linarith)] at hmono
      nlinarith
    · simp
    · obtain ⟨c, hc, hceq⟩ := exists_hasDerivAt_eq_slope thetaCuspLogSource thetaLogHazard hxy
        (fun z _ => (hasDerivAt_thetaCuspLogSource_hazard z).continuousAt.continuousWithinAt)
        (fun z _ => hasDerivAt_thetaCuspLogSource_hazard z)
      have hmono : thetaLogHazard c ≤ thetaLogHazard x := strictAnti_thetaLogHazard.antitone hc.1.le
      rw [hceq, div_le_iff₀ (by linarith)] at hmono
      linarith
  have hx := thetaCuspFullSource_pos_all x
  calc thetaCuspFullSource y = Real.exp (thetaCuspLogSource y) :=
        (Real.exp_log (thetaCuspFullSource_pos_all y)).symm
    _ ≤ Real.exp (thetaCuspLogSource x + thetaLogHazard x * (y - x)) := Real.exp_le_exp.2 hlog
    _ = _ := by rw [Real.exp_add, thetaCuspLogSource, Real.exp_log hx]

/-! ## The left mass and the endpoint ratio -/

/-- `I(x) = ∫_{−∞}^x k`. -/
def thetaLeftMass (x : ℝ) : ℝ := ∫ y in Iic x, thetaCuspFullSource y

theorem thetaLeftMass_nonneg (x : ℝ) : 0 ≤ thetaLeftMass x :=
  setIntegral_nonneg measurableSet_Iic fun y _ => (thetaCuspFullSource_pos_all y).le

theorem hasDerivAt_thetaLeftMass (x : ℝ) : HasDerivAt thetaLeftMass (thetaCuspFullSource x) x :=
  thetaSource.hasDerivAt_integral_Iic x

theorem thetaLeftMass_eq_mass_mul_cdf (x : ℝ) : thetaLeftMass x = thetaSource.mass * thetaSource.cdfFun x := by
  rw [thetaLeftMass, PositiveDensitySource.cdfFun, mul_div_cancel₀ _ thetaSource.mass_ne_zero]
  rfl

theorem integral_Iic_exp_mul_sub {s : ℝ} (hs : 0 < s) (x : ℝ) :
    ∫ y in Iic x, Real.exp (s * (y - x)) = 1 / s := by
  have hderiv : ∀ y ∈ Iio x, HasDerivAt (fun y => Real.exp (s * (y - x)) / s)
      (Real.exp (s * (y - x))) y := fun y _ => by
    have := (((hasDerivAt_id y).sub_const x).const_mul s).exp.div_const s
    exact this.congr_deriv (by simp only [id]; field_simp)
  have hint : IntegrableOn (fun y => Real.exp (s * (y - x))) (Iic x) := by
    have : IntegrableOn (fun y => Real.exp (s * y) * Real.exp (-(s * x))) (Iic x) :=
      (integrableOn_exp_mul_Iic hs x).mul_const _
    refine this.congr_fun (fun y _ => ?_) measurableSet_Iic
    simp only
    rw [← Real.exp_add]; ring_nf
  have hlim : Tendsto (fun y => Real.exp (s * (y - x)) / s) atBot (𝓝 0) := by
    have h1 : Tendsto (fun y => s * (y - x)) atBot atBot :=
      (tendsto_atBot_add_const_right _ (-x) tendsto_id).const_mul_atBot hs
    have := (Real.tendsto_exp_atBot.comp h1).div_const s
    simpa using this
  rw [integral_Iic_of_hasDerivAt_of_tendsto (by fun_prop) hderiv hint hlim]
  simp

/-- **`I(x) ≤ k(x)/h(x)`** wherever `h(x) > 0`. -/
theorem thetaLeftMass_le {x : ℝ} (hx : 0 < thetaLogHazard x) :
    thetaLeftMass x ≤ thetaCuspFullSource x / thetaLogHazard x := by
  have hint : IntegrableOn (fun y => thetaCuspFullSource x * Real.exp (thetaLogHazard x * (y - x))) (Iic x) := by
    have : IntegrableOn (fun y => thetaCuspFullSource x * (Real.exp (thetaLogHazard x * y) *
        Real.exp (-(thetaLogHazard x * x)))) (Iic x) :=
      ((integrableOn_exp_mul_Iic hx x).mul_const _).const_mul _
    refine this.congr_fun (fun y _ => ?_) measurableSet_Iic
    simp only
    rw [← Real.exp_add]; ring_nf
  calc thetaLeftMass x ≤ ∫ y in Iic x, thetaCuspFullSource x * Real.exp (thetaLogHazard x * (y - x)) :=
        setIntegral_mono_on (thetaSource.integrable_k.integrableOn) hint measurableSet_Iic
          fun y _ => thetaCuspFullSource_le_tangent x y
    _ = thetaCuspFullSource x / thetaLogHazard x := by
        rw [integral_const_mul, integral_Iic_exp_mul_sub hx]; ring

/-- The endpoint ratio `r = I/k` (`= t q(t)` at `t = F(x)`). -/
def thetaEndpointRatio (x : ℝ) : ℝ := thetaLeftMass x / thetaCuspFullSource x

theorem thetaEndpointRatio_nonneg (x : ℝ) : 0 ≤ thetaEndpointRatio x :=
  div_nonneg (thetaLeftMass_nonneg x) (thetaCuspFullSource_pos_all x).le

theorem hasDerivAt_thetaEndpointRatio (x : ℝ) :
    HasDerivAt thetaEndpointRatio (1 - thetaEndpointRatio x * thetaLogHazard x) x := by
  have hk := thetaCuspFullSource_pos_all x
  have h := (hasDerivAt_thetaLeftMass x).div (differentiable_thetaCuspFullSource x).hasDerivAt hk.ne'
  refine h.congr_deriv ?_
  rw [deriv_thetaCuspFullSource_eq, thetaEndpointRatio]
  field_simp

/-- **`r h ≤ 1`**, i.e. `r` is nondecreasing. -/
theorem thetaEndpointRatio_mul_hazard_le (x : ℝ) : thetaEndpointRatio x * thetaLogHazard x ≤ 1 := by
  rcases le_or_gt (thetaLogHazard x) 0 with hh | hh
  · nlinarith [thetaEndpointRatio_nonneg x]
  · have := thetaLeftMass_le hh
    rw [thetaEndpointRatio, div_mul_eq_mul_div, div_le_one (thetaCuspFullSource_pos_all x)]
    rwa [le_div_iff₀ hh] at this

theorem tendsto_thetaEndpointRatio_atBot : Tendsto thetaEndpointRatio atBot (𝓝 0) := by
  have hinv : Tendsto (fun x => (thetaLogHazard x)⁻¹) atBot (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_thetaLogHazard_atBot
  refine squeeze_zero' (Eventually.of_forall thetaEndpointRatio_nonneg) ?_ hinv
  filter_upwards [tendsto_thetaLogHazard_atBot.eventually_gt_atTop 0] with x hx
  have := thetaEndpointRatio_mul_hazard_le x
  calc thetaEndpointRatio x = thetaEndpointRatio x * thetaLogHazard x * (thetaLogHazard x)⁻¹ := by
        field_simp
    _ ≤ 1 * (thetaLogHazard x)⁻¹ := mul_le_mul_of_nonneg_right this (inv_nonneg.2 hx.le)
    _ = (thetaLogHazard x)⁻¹ := one_mul _

theorem continuous_thetaLeftMass : Continuous thetaLeftMass :=
  continuous_iff_continuousAt.2 fun x => (hasDerivAt_thetaLeftMass x).continuousAt

theorem continuous_thetaEndpointRatio : Continuous thetaEndpointRatio :=
  continuous_iff_continuousAt.2 fun x => (hasDerivAt_thetaEndpointRatio x).continuousAt

theorem continuous_thetaLogHazard : Continuous thetaLogHazard :=
  continuous_deriv_thetaCuspFullSource.div continuous_thetaCuspFullSource
    fun x => (thetaCuspFullSource_pos_all x).ne'

/-- `I` is integrable on every left half-line. -/
theorem integrableOn_thetaLeftMass_Iic (b : ℝ) : IntegrableOn thetaLeftMass (Iic b) := by
  obtain ⟨x1, hx1⟩ := eventually_atBot.1 (tendsto_thetaLogHazard_atBot.eventually_ge_atTop 1)
  set x0 := min x1 b
  have hle : ∀ x ≤ x0, thetaLeftMass x ≤ thetaCuspFullSource x := fun x hx => by
    have hh : 1 ≤ thetaLogHazard x := hx1 x (hx.trans (min_le_left _ _))
    have := thetaLeftMass_le (by linarith : 0 < thetaLogHazard x)
    have hk := thetaCuspFullSource_pos_all x
    calc thetaLeftMass x ≤ thetaCuspFullSource x / thetaLogHazard x := this
      _ ≤ thetaCuspFullSource x := div_le_self hk.le hh
  have h1 : IntegrableOn thetaLeftMass (Iic x0) :=
    (thetaSource.integrable_k.integrableOn).mono' continuous_thetaLeftMass.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Iic).2 (Eventually.of_forall fun x hx => by
        rw [Real.norm_eq_abs, abs_of_nonneg (thetaLeftMass_nonneg x)]
        exact hle x hx))
  have h2 : IntegrableOn thetaLeftMass (Icc x0 b) := continuous_thetaLeftMass.integrableOn_Icc
  rw [← Iic_union_Icc_eq_Iic (min_le_right x1 b)]
  exact h1.union h2

/-- `r' = 1 − rh ≥ 0` is integrable on every left half-line. -/
theorem integrableOn_thetaEndpointRatio_deriv_Iic (b : ℝ) :
    IntegrableOn (fun x => 1 - thetaEndpointRatio x * thetaLogHazard x) (Iic b) := by
  have hd : ∀ x ∈ Ioi (-b), HasDerivAt (fun y => thetaEndpointRatio (-y))
      (-(1 - thetaEndpointRatio (-x) * thetaLogHazard (-x))) x := fun x _ => by
    have := (hasDerivAt_thetaEndpointRatio (-x)).comp x (hasDerivAt_neg x)
    exact this.congr_deriv (by ring)
  have hlim : Tendsto (fun y => thetaEndpointRatio (-y)) atTop (𝓝 0) :=
    tendsto_thetaEndpointRatio_atBot.comp tendsto_neg_atTop_atBot
  have h := integrableOn_Ioi_deriv_of_nonpos
    (continuous_thetaEndpointRatio.comp continuous_neg).continuousAt.continuousWithinAt hd
    (fun x _ => by have := thetaEndpointRatio_mul_hazard_le (-x); linarith) hlim
  have h1 : IntegrableOn (fun x => 1 - thetaEndpointRatio (-x) * thetaLogHazard (-x)) (Ioi (-b)) := by
    refine h.neg.congr_fun (fun x _ => ?_) measurableSet_Ioi
    simp only [Pi.neg_apply, neg_neg]
  have h2 := h1.comp_neg
  simp only [neg_neg, Set.neg_Ioi] at h2
  exact (integrableOn_Iic_iff_integrableOn_Iio).2 h2

/-! ## The CDF action -/

/-- The theta CDF action `Φ_n = ∫ (1 − cos 2πnF(x)) dx`. -/
def cdfAction (n : ℤ) : ℝ :=
  ∫ x, (1 - Real.cos (2 * Real.pi * n * thetaSource.cdfFun x))

theorem cdfAction_neg (n : ℤ) : cdfAction (-n) = cdfAction n := by
  simp only [cdfAction, Int.cast_neg, mul_neg, neg_mul, Real.cos_neg]

/-- The card's quantile form: `Φ_n = ∫₀¹ q(t)(1 − cos 2πnt) dt`. -/
theorem cdfAction_eq_quantileSpeed (n : ℤ) :
    cdfAction n = ∫ t in Ioo (0 : ℝ) 1,
      HedenmalmQuantile.quantileSpeed thetaSource t * (1 - Real.cos (2 * Real.pi * n * t)) := by
  set g : ℝ → ℝ := fun x => thetaSource.mass / thetaSource.k x *
    (1 - Real.cos (2 * Real.pi * n * thetaSource.cdfFun x))
  have hgm : AEStronglyMeasurable g volume :=
    ((continuous_const.div thetaSource.continuous_k fun x => (thetaSource.pos_k x).ne').mul
      (continuous_const.sub (Real.continuous_cos.comp (continuous_const.mul
        thetaSource.continuous_cdfFun)))).aestronglyMeasurable
  have h := HedenmalmQuantile.integral_comp_quantile thetaSource g hgm
  have hleft : (∫ u in Ioo (0 : ℝ) 1, g (thetaSource.quantileFun u)) = ∫ t in Ioo (0 : ℝ) 1,
      HedenmalmQuantile.quantileSpeed thetaSource t * (1 - Real.cos (2 * Real.pi * n * t)) := by
    refine setIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
    simp only [g, HedenmalmQuantile.quantileSpeed, thetaSource.cdfFun_quantile hu]
  have hright : (∫ x, thetaSource.normalized x • g x) = cdfAction n := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [g, smul_eq_mul, PositiveDensitySource.normalized]
    have hk := thetaSource.pos_k x
    have hM := thetaSource.mass_pos
    field_simp
  rw [← hright, ← h, hleft]

/-! ## Two-sided tail weight -/

/-- `τ(x) = min(F(x), 1 − F(x))`. -/
def cdfTailWeight (x : ℝ) : ℝ := min (thetaSource.cdfFun x) (1 - thetaSource.cdfFun x)

theorem cdfFun_thetaSource_neg (x : ℝ) : thetaSource.cdfFun (-x) = 1 - thetaSource.cdfFun x :=
  HedenmalmIntervalAnomaly.cdfFun_neg thetaSource thetaSource_even x

theorem cdfFun_thetaSource_eq (x : ℝ) : thetaSource.cdfFun x = thetaLeftMass x / thetaSource.mass := by
  rw [thetaLeftMass_eq_mass_mul_cdf, mul_div_cancel_left₀ _ thetaSource.mass_ne_zero]

theorem cdfTailWeight_nonneg (x : ℝ) : 0 ≤ cdfTailWeight x :=
  le_min (thetaSource.cdfFun_mem_Ioo x).1.le (by linarith [(thetaSource.cdfFun_mem_Ioo x).2])

theorem integrable_cdfTailWeight : Integrable cdfTailWeight := by
  have hc : Continuous cdfTailWeight :=
    thetaSource.continuous_cdfFun.min (continuous_const.sub thetaSource.continuous_cdfFun)
  have hF0 : ∀ x, 0 ≤ thetaSource.cdfFun x := fun x => (thetaSource.cdfFun_mem_Ioo x).1.le
  have hF1 : ∀ x, thetaSource.cdfFun x ≤ 1 := fun x => (thetaSource.cdfFun_mem_Ioo x).2.le
  have h1 : IntegrableOn cdfTailWeight (Iic 0) := by
    have hI := (integrableOn_thetaLeftMass_Iic 0).div_const thetaSource.mass
    refine hI.mono' hc.aestronglyMeasurable ((ae_restrict_iff' measurableSet_Iic).2
      (Eventually.of_forall fun x _ => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (cdfTailWeight_nonneg x), cdfTailWeight, ← cdfFun_thetaSource_eq]
    exact min_le_left _ _
  have h2 : IntegrableOn cdfTailWeight (Ioi 0) := by
    have hI0 : IntegrableOn (fun x => thetaLeftMass x / thetaSource.mass) (Iic 0) :=
      (integrableOn_thetaLeftMass_Iic 0).div_const thetaSource.mass
    have hI := hI0.comp_neg
    simp only [Set.neg_Iic, neg_zero] at hI
    refine (hI.mono_set Ioi_subset_Ici_self).mono'
      hc.aestronglyMeasurable ((ae_restrict_iff' measurableSet_Ioi).2
        (Eventually.of_forall fun x _ => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (cdfTailWeight_nonneg x), cdfTailWeight,
      ← cdfFun_thetaSource_eq, cdfFun_thetaSource_neg]
    exact min_le_right _ _
  have := h1.union h2
  rwa [Iic_union_Ioi, integrableOn_univ] at this

/-- `|1 − e^{2πiaF}| ≤ 2π|a| τ`. -/
theorem norm_one_sub_cexp_cdf_le (a : ℤ) (x : ℝ) :
    ‖1 - Complex.exp (2 * Real.pi * Complex.I * a * thetaSource.cdfFun x)‖ ≤
      2 * Real.pi * |(a : ℝ)| * cdfTailWeight x := by
  set F := thetaSource.cdfFun x
  have h1 : ‖1 - Complex.exp (2 * Real.pi * Complex.I * a * F)‖ ≤ 2 * Real.pi * |(a : ℝ)| * F := by
    have hθ : (2 * Real.pi * Complex.I * a * F : ℂ) = Complex.I * ((2 * Real.pi * a * F : ℝ) : ℂ) := by
      push_cast; ring
    rw [hθ, norm_sub_rev]
    refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans (le_of_eq ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_pos Real.pi_pos,
      abs_of_nonneg (thetaSource.cdfFun_mem_Ioo x).1.le]; norm_num
    exact Or.inl rfl
  have h2 : ‖1 - Complex.exp (2 * Real.pi * Complex.I * a * F)‖ ≤
      2 * Real.pi * |(a : ℝ)| * (1 - F) := by
    have hper : Complex.exp (2 * Real.pi * Complex.I * a * F) =
        Complex.exp (Complex.I * ((2 * Real.pi * a * (F - 1) : ℝ) : ℂ)) := by
      have : Complex.exp (2 * Real.pi * Complex.I * a) = 1 := by
        rw [show (2 * Real.pi * Complex.I * a : ℂ) = (a : ℂ) * (2 * Real.pi * Complex.I) by ring]
        exact Complex.exp_int_mul_two_pi_mul_I a
      calc Complex.exp (2 * Real.pi * Complex.I * a * F)
          = Complex.exp (Complex.I * ((2 * Real.pi * a * (F - 1) : ℝ) : ℂ)) *
              Complex.exp (2 * Real.pi * Complex.I * a) := by
            rw [← Complex.exp_add]; push_cast; ring_nf
        _ = _ := by rw [this, mul_one]
    rw [hper, norm_sub_rev]
    refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans (le_of_eq ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_pos Real.pi_pos,
      abs_of_nonpos (by linarith [(thetaSource.cdfFun_mem_Ioo x).2] : F - 1 ≤ 0)]
    ring
  rw [cdfTailWeight]
  rcases min_choice (thetaSource.cdfFun x) (1 - thetaSource.cdfFun x) with h | h <;> rw [h]
  · exact h1
  · exact h2

/-- The CDF action integrand is integrable. -/
theorem integrable_cdfAction_integrand (n : ℤ) :
    Integrable fun x => 1 - Real.cos (2 * Real.pi * n * thetaSource.cdfFun x) := by
  refine (integrable_cdfTailWeight.const_mul (2 * Real.pi * |(n : ℝ)|)).mono'
    (continuous_const.sub (Real.continuous_cos.comp (continuous_const.mul
      thetaSource.continuous_cdfFun))).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  have h := norm_one_sub_cexp_cdf_le n x
  have hre : 1 - Real.cos (2 * Real.pi * n * thetaSource.cdfFun x) =
      (1 - Complex.exp (2 * Real.pi * Complex.I * n * thetaSource.cdfFun x)).re := by
    rw [Complex.sub_re, Complex.one_re, show (2 * Real.pi * Complex.I * n * thetaSource.cdfFun x : ℂ) =
      ((2 * Real.pi * n * thetaSource.cdfFun x : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_ofReal_mul_I_re]
  rw [Real.norm_eq_abs, hre]
  exact (Complex.abs_re_le_norm _).trans h

/-! ## Riemann–Lebesgue along the CDF phase -/

/-- The phase `E_n(x) = e^{2πinF(x)}`. -/
def cdfPhase (n : ℝ) (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * n * thetaSource.cdfFun x)

theorem norm_cdfPhase (n x : ℝ) : ‖cdfPhase n x‖ = 1 := by
  rw [cdfPhase, show (2 * Real.pi * Complex.I * n * thetaSource.cdfFun x : ℂ) =
    ((2 * Real.pi * n * thetaSource.cdfFun x : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

theorem continuous_cdfPhase (n : ℝ) : Continuous (cdfPhase n) :=
  Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
    thetaSource.continuous_cdfFun))

/-- **Riemann–Lebesgue along the CDF phase.**  For integrable `ψ`,
`∫ ψ(x) e^{2πinF(x)} dx → 0`. -/
theorem tendsto_integral_mul_cdfPhase {ψ : ℝ → ℂ} (hψ : Integrable ψ) :
    Tendsto (fun n : ℕ => ∫ x, ψ x * cdfPhase n x) atTop (𝓝 0) := by
  set g : ℝ → ℂ := fun x => ((thetaSource.mass / thetaSource.k x : ℝ) : ℂ) * ψ x
  have hgm : AEStronglyMeasurable g volume :=
    (Complex.continuous_ofReal.comp (continuous_const.div thetaSource.continuous_k
      fun x => (thetaSource.pos_k x).ne')).aestronglyMeasurable.mul hψ.aestronglyMeasurable
  have hng : ∀ x, thetaSource.normalized x • g x = ψ x := fun x => by
    simp only [g, PositiveDensitySource.normalized, Complex.real_smul]
    have hk := thetaSource.pos_k x
    have hM := thetaSource.mass_pos
    rw [← mul_assoc, ← Complex.ofReal_mul]
    rw [show thetaSource.k x / thetaSource.mass * (thetaSource.mass / thetaSource.k x) = 1 by
      field_simp]
    simp
  have hint : IntegrableOn (fun u => g (thetaSource.quantileFun u)) (Ioo (0 : ℝ) 1) := by
    rw [thetaSource.integrableOn_comp_quantileFun_iff hgm]
    exact hψ.congr (Eventually.of_forall fun x => (hng x).symm)
  set f : ℝ → ℂ := (Ioo (0 : ℝ) 1).indicator fun u => g (thetaSource.quantileFun u)
  have hf : Integrable f := (integrable_indicator_iff measurableSet_Ioo).2 hint
  have hchange : ∀ n : ℕ, (∫ x, ψ x * cdfPhase n x) =
      ∫ v, Real.fourierChar (-(v * (-(n : ℝ)))) • f v := by
    intro n
    have hgn : AEStronglyMeasurable (fun x => g x * cdfPhase n x) volume :=
      hgm.mul (continuous_cdfPhase n).aestronglyMeasurable
    have h := HedenmalmQuantile.integral_comp_quantile thetaSource (fun x => g x * cdfPhase n x) hgn
    have h1 : (∫ x, thetaSource.normalized x • (g x * cdfPhase n x)) = ∫ x, ψ x * cdfPhase n x := by
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only
      rw [← smul_mul_assoc, hng]
    have h2 : (∫ v, Real.fourierChar (-(v * (-(n : ℝ)))) • f v) =
        ∫ u in Ioo (0 : ℝ) 1, g (thetaSource.quantileFun u) * cdfPhase n (thetaSource.quantileFun u) := by
      rw [← integral_indicator measurableSet_Ioo]
      refine integral_congr_ae (Eventually.of_forall fun u => ?_)
      by_cases hu : u ∈ Ioo (0 : ℝ) 1
      · simp only [f, Set.indicator_of_mem hu, cdfPhase, thetaSource.cdfFun_quantile hu,
          Circle.smul_def, Real.fourierChar_apply, smul_eq_mul]
        rw [mul_comm]; congr 1; push_cast; ring_nf
      · simp [f, Set.indicator_of_notMem hu]
    rw [h2, h, h1]
  have hneg : Tendsto (fun n : ℕ => -(n : ℝ)) atTop (Filter.cocompact ℝ) :=
    (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop).mono_right atBot_le_cocompact
  have := (Real.tendsto_integral_exp_smul_cocompact f).comp hneg
  refine this.congr fun n => ?_
  simp only [Function.comp]
  rw [hchange]

/-! ## The action weight `w_a = M(1 − e^{2πiaF})/k` -/

/-- `w_a(x) = M(1 − e^{2πiaF(x)})/k(x)`. -/
def actionWeight (a : ℤ) (x : ℝ) : ℂ :=
  ((thetaSource.mass / thetaCuspFullSource x : ℝ) : ℂ) * (1 - cdfPhase a x)

/-- `w_a' = −2πia e^{2πiaF} − M(1 − e^{2πiaF}) h/k`. -/
def actionWeightDeriv (a : ℤ) (x : ℝ) : ℂ :=
  -(2 * Real.pi * Complex.I * a) * cdfPhase a x -
    ((thetaSource.mass * thetaLogHazard x / thetaCuspFullSource x : ℝ) : ℂ) * (1 - cdfPhase a x)

theorem hasDerivAt_cdfPhase (n : ℝ) (x : ℝ) :
    HasDerivAt (cdfPhase n) (2 * Real.pi * Complex.I * n *
      ((thetaCuspFullSource x / thetaSource.mass : ℝ) : ℂ) * cdfPhase n x) x := by
  have hF : HasDerivAt thetaSource.cdfFun (thetaCuspFullSource x / thetaSource.mass) x :=
    thetaSource.hasDerivAt_cdfFun x
  have h := ((hF.ofReal_comp).const_mul (2 * Real.pi * Complex.I * n)).cexp
  refine h.congr_deriv ?_
  simp only [cdfPhase]
  ring

theorem hasDerivAt_actionWeight (a : ℤ) (x : ℝ) :
    HasDerivAt (actionWeight a) (actionWeightDeriv a x) x := by
  have hk := thetaCuspFullSource_pos_all x
  have hM := thetaSource.mass_pos
  have h1 : HasDerivAt (fun y => ((thetaSource.mass / thetaCuspFullSource y : ℝ) : ℂ))
      ((-(thetaSource.mass * thetaLogHazard x / thetaCuspFullSource x) : ℝ) : ℂ) x := by
    have := ((hasDerivAt_const x thetaSource.mass).div (differentiable_thetaCuspFullSource x).hasDerivAt
      hk.ne').ofReal_comp
    refine this.congr_deriv ?_
    rw [deriv_thetaCuspFullSource_eq]
    push_cast
    field_simp
    ring
  have h2 := h1.fun_mul ((hasDerivAt_const x (1 : ℂ)).fun_sub (hasDerivAt_cdfPhase a x))
  refine h2.congr_deriv ?_
  have hkC : (thetaCuspFullSource x : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have hMC : (thetaSource.mass : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  simp only [actionWeightDeriv]
  push_cast
  field_simp
  ring

/-- **Reflection** `w_a(−x) = w_{−a}(x)`. -/
theorem cdfPhase_neg_int (a : ℤ) (x : ℝ) : cdfPhase a (-x) = cdfPhase (-a : ℤ) x := by
  have hper : Complex.exp (2 * Real.pi * Complex.I * a) = 1 := by
    rw [show (2 * Real.pi * Complex.I * a : ℂ) = (a : ℂ) * (2 * Real.pi * Complex.I) by ring]
    exact Complex.exp_int_mul_two_pi_mul_I a
  rw [cdfPhase, cdfPhase, cdfFun_thetaSource_neg]
  push_cast
  rw [show (2 * Real.pi * Complex.I * a * (1 - (thetaSource.cdfFun x : ℂ)) : ℂ) =
    2 * Real.pi * Complex.I * a + 2 * Real.pi * Complex.I * (-a) * thetaSource.cdfFun x by ring,
    Complex.exp_add, hper, one_mul]

theorem actionWeight_neg (a : ℤ) (x : ℝ) : actionWeight a (-x) = actionWeight (-a) x := by
  rw [actionWeight, actionWeight, thetaCuspFullSource_neg, cdfPhase_neg_int]

theorem actionWeightDeriv_neg (a : ℤ) (x : ℝ) :
    actionWeightDeriv a (-x) = -actionWeightDeriv (-a) x := by
  rw [actionWeightDeriv, actionWeightDeriv, thetaCuspFullSource_neg, thetaLogHazard_neg, cdfPhase_neg_int]
  push_cast
  ring

/-! ## Integrability of `w_a'` and decay of `w_a` -/

theorem norm_cexp_I_mul_sub_one_sub_le (θ : ℝ) :
    ‖Complex.exp (Complex.I * θ) - 1 - Complex.I * θ‖ ≤ 2 * θ ^ 2 := by
  rcases le_or_gt |θ| 1 with h | h
  · have hn : ‖Complex.I * (θ : ℂ)‖ = |θ| := by
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    have := Complex.norm_exp_sub_one_sub_id_le (x := Complex.I * θ) (by rw [hn]; exact h)
    rw [hn, sq_abs] at this
    nlinarith [sq_nonneg θ]
  · have h1 := Real.norm_exp_I_mul_ofReal_sub_one_le (x := θ)
    have h2 : ‖Complex.I * (θ : ℂ)‖ = |θ| := by
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    calc ‖Complex.exp (Complex.I * θ) - 1 - Complex.I * θ‖
        ≤ ‖Complex.exp (Complex.I * θ) - 1‖ + ‖Complex.I * (θ : ℂ)‖ := norm_sub_le _ _
      _ ≤ |θ| + |θ| := by rw [h2]; exact add_le_add (by simpa [Real.norm_eq_abs] using h1) le_rfl
      _ ≤ 2 * θ ^ 2 := by nlinarith [sq_abs θ, abs_nonneg θ]

theorem cdfPhase_eq_exp_I (a : ℤ) (x : ℝ) :
    cdfPhase a x = Complex.exp (Complex.I * ((2 * Real.pi * a * thetaSource.cdfFun x : ℝ) : ℂ)) := by
  rw [cdfPhase]; push_cast; ring_nf

theorem thetaEndpointRatio_eq (x : ℝ) :
    thetaEndpointRatio x = thetaSource.mass * thetaSource.cdfFun x / thetaCuspFullSource x := by
  rw [thetaEndpointRatio, thetaLeftMass_eq_mass_mul_cdf]

theorem re_integral_complex {f : ℝ → ℂ} (hf : Integrable f) : (∫ x, f x).re = ∫ x, (f x).re :=
  (integral_re hf).symm

/-- The decomposition `w_a' = −2πia(1 − rh) − 2πia(e^{iθ} − 1) + (Mh/k)(e^{iθ} − 1 − iθ)`. -/
theorem actionWeightDeriv_eq_decomp (a : ℤ) (x : ℝ) :
    actionWeightDeriv a x =
      -(2 * Real.pi * Complex.I * a) * ((1 - thetaEndpointRatio x * thetaLogHazard x : ℝ) : ℂ) -
        (2 * Real.pi * Complex.I * a) *
          (Complex.exp (Complex.I * ((2 * Real.pi * a * thetaSource.cdfFun x : ℝ) : ℂ)) - 1) +
          ((thetaSource.mass * thetaLogHazard x / thetaCuspFullSource x : ℝ) : ℂ) *
            (Complex.exp (Complex.I * ((2 * Real.pi * a * thetaSource.cdfFun x : ℝ) : ℂ)) - 1 -
              Complex.I * ((2 * Real.pi * a * thetaSource.cdfFun x : ℝ) : ℂ)) := by
  rw [actionWeightDeriv, cdfPhase_eq_exp_I, thetaEndpointRatio_eq]
  have hkC : (thetaCuspFullSource x : ℂ) ≠ 0 := by exact_mod_cast (thetaCuspFullSource_pos_all x).ne'
  push_cast
  field_simp
  ring

/-- **Pointwise bound on the left half-line.**
`‖w_a'(x)‖ ≤ 2π|a|(1 − rh) + 12π²a² F(x)` for `x ≤ 0`. -/
theorem norm_actionWeightDeriv_le {x : ℝ} (hx : x ≤ 0) (a : ℤ) :
    ‖actionWeightDeriv a x‖ ≤ 2 * Real.pi * |(a : ℝ)| * (1 - thetaEndpointRatio x * thetaLogHazard x) +
      12 * Real.pi ^ 2 * (a : ℝ) ^ 2 * thetaSource.cdfFun x := by
  set θ : ℝ := 2 * Real.pi * a * thetaSource.cdfFun x
  set F := thetaSource.cdfFun x
  set M := thetaSource.mass
  set k := thetaCuspFullSource x
  set h := thetaLogHazard x
  have hk : 0 < k := thetaCuspFullSource_pos_all x
  have hM : 0 < M := thetaSource.mass_pos
  have hh : 0 ≤ h := thetaLogHazard_nonneg_of_nonpos hx
  have hF : 0 ≤ F := (thetaSource.cdfFun_mem_Ioo x).1.le
  have hr : thetaEndpointRatio x = M * F / k := thetaEndpointRatio_eq x
  have hrh : thetaEndpointRatio x * h ≤ 1 := thetaEndpointRatio_mul_hazard_le x
  have hrh0 : 0 ≤ thetaEndpointRatio x * h := mul_nonneg (thetaEndpointRatio_nonneg x) hh
  have hid : actionWeightDeriv a x =
      -(2 * Real.pi * Complex.I * a) * ((1 - thetaEndpointRatio x * h : ℝ) : ℂ) -
        (2 * Real.pi * Complex.I * a) * (Complex.exp (Complex.I * θ) - 1) +
          ((M * h / k : ℝ) : ℂ) * (Complex.exp (Complex.I * θ) - 1 - Complex.I * θ) :=
    actionWeightDeriv_eq_decomp a x
  have hI : ‖(2 * Real.pi * Complex.I * a : ℂ)‖ = 2 * Real.pi * |(a : ℝ)| := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos, Complex.norm_intCast]; ring
  have hθ : |θ| = 2 * Real.pi * |(a : ℝ)| * F := by
    simp only [θ]; rw [abs_mul, abs_mul, abs_mul, abs_of_pos Real.pi_pos, abs_of_nonneg hF]; norm_num
  have e1 : ‖Complex.exp (Complex.I * θ) - 1‖ ≤ |θ| := by
    simpa [Real.norm_eq_abs] using Real.norm_exp_I_mul_ofReal_sub_one_le (x := θ)
  have e2 := norm_cexp_I_mul_sub_one_sub_le θ
  have e3 : M * h / k * (2 * θ ^ 2) ≤ 8 * Real.pi ^ 2 * (a : ℝ) ^ 2 * F := by
    have hθ2 : θ ^ 2 = 4 * Real.pi ^ 2 * (a : ℝ) ^ 2 * F ^ 2 := by simp only [θ]; ring
    have : M * h / k * F = thetaEndpointRatio x * h := by rw [hr]; field_simp
    rw [hθ2]
    calc M * h / k * (2 * (4 * Real.pi ^ 2 * (a : ℝ) ^ 2 * F ^ 2))
        = 8 * Real.pi ^ 2 * (a : ℝ) ^ 2 * F * (M * h / k * F) := by ring
      _ = 8 * Real.pi ^ 2 * (a : ℝ) ^ 2 * F * (thetaEndpointRatio x * h) := by rw [this]
      _ ≤ 8 * Real.pi ^ 2 * (a : ℝ) ^ 2 * F * 1 := mul_le_mul_of_nonneg_left hrh (by positivity)
      _ = _ := by ring
  have hMhk : 0 ≤ M * h / k := by positivity
  have t1 : ‖-(2 * Real.pi * Complex.I * a) * ((1 - thetaEndpointRatio x * h : ℝ) : ℂ)‖ =
      2 * Real.pi * |(a : ℝ)| * (1 - thetaEndpointRatio x * h) := by
    rw [norm_mul, norm_neg, hI, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith : 0 ≤ 1 - thetaEndpointRatio x * h)]
  have t2 : ‖(2 * Real.pi * Complex.I * a) * (Complex.exp (Complex.I * θ) - 1)‖ ≤
      2 * Real.pi * |(a : ℝ)| * |θ| := by
    rw [norm_mul, hI]; exact mul_le_mul_of_nonneg_left e1 (by positivity)
  have t3 : ‖((M * h / k : ℝ) : ℂ) * (Complex.exp (Complex.I * θ) - 1 - Complex.I * θ)‖ ≤
      M * h / k * (2 * θ ^ 2) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hMhk]
    exact mul_le_mul_of_nonneg_left e2 hMhk
  have e4 : 2 * Real.pi * |(a : ℝ)| * |θ| = 4 * Real.pi ^ 2 * (a : ℝ) ^ 2 * F := by
    rw [hθ, ← sq_abs (a : ℝ)]; ring
  rw [hid]
  calc ‖-(2 * Real.pi * Complex.I * a) * ((1 - thetaEndpointRatio x * h : ℝ) : ℂ) -
        (2 * Real.pi * Complex.I * a) * (Complex.exp (Complex.I * θ) - 1) +
          ((M * h / k : ℝ) : ℂ) * (Complex.exp (Complex.I * θ) - 1 - Complex.I * θ)‖
      ≤ ‖-(2 * Real.pi * Complex.I * a) * ((1 - thetaEndpointRatio x * h : ℝ) : ℂ)‖ +
          ‖(2 * Real.pi * Complex.I * a) * (Complex.exp (Complex.I * θ) - 1)‖ +
          ‖((M * h / k : ℝ) : ℂ) * (Complex.exp (Complex.I * θ) - 1 - Complex.I * θ)‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ _ := by linarith [t1, t2, t3, e3, e4]

theorem continuous_actionWeightDeriv (a : ℤ) : Continuous (actionWeightDeriv a) := by
  unfold actionWeightDeriv
  exact (continuous_const.mul (continuous_cdfPhase a)).sub
    ((Complex.continuous_ofReal.comp ((continuous_const.mul continuous_thetaLogHazard).div
      continuous_thetaCuspFullSource fun x => (thetaCuspFullSource_pos_all x).ne')).mul
        (continuous_const.sub (continuous_cdfPhase a)))

theorem integrableOn_actionWeightDeriv_Iic (a : ℤ) : IntegrableOn (actionWeightDeriv a) (Iic 0) := by
  have hF : IntegrableOn (fun x => thetaSource.cdfFun x) (Iic 0) := by
    have : IntegrableOn (fun x => thetaLeftMass x / thetaSource.mass) (Iic 0) :=
      (integrableOn_thetaLeftMass_Iic 0).div_const thetaSource.mass
    exact this.congr_fun (fun x _ => (cdfFun_thetaSource_eq x).symm) measurableSet_Iic
  have hmaj := ((integrableOn_thetaEndpointRatio_deriv_Iic 0).const_mul (2 * Real.pi * |(a : ℝ)|)).add
    (hF.const_mul (12 * Real.pi ^ 2 * (a : ℝ) ^ 2))
  exact hmaj.mono' (continuous_actionWeightDeriv a).aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Iic).2 (Eventually.of_forall fun x hx =>
      norm_actionWeightDeriv_le hx a))

theorem integrable_actionWeightDeriv (a : ℤ) : Integrable (actionWeightDeriv a) := by
  have h1 := integrableOn_actionWeightDeriv_Iic a
  have h2 : IntegrableOn (actionWeightDeriv a) (Ici 0) := by
    have := (integrableOn_actionWeightDeriv_Iic (-a)).comp_neg
    simp only [Set.neg_Iic, neg_zero] at this
    refine this.neg.congr_fun (fun x _ => ?_) measurableSet_Ici
    have := actionWeightDeriv_neg a (-x)
    rw [neg_neg] at this
    simp only [Pi.neg_apply, this]
  have := h1.union h2
  rwa [Iic_union_Ici, integrableOn_univ] at this

theorem norm_actionWeight_le_of_nonpos {x : ℝ} (_hx : x ≤ 0) (a : ℤ) :
    ‖actionWeight a x‖ ≤ 2 * Real.pi * |(a : ℝ)| * thetaEndpointRatio x := by
  have hk := thetaCuspFullSource_pos_all x
  have hM := thetaSource.mass_pos
  have h := norm_one_sub_cexp_cdf_le a x
  have hτ : cdfTailWeight x ≤ thetaSource.cdfFun x := min_le_left _ _
  rw [actionWeight, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos hM hk),
    thetaEndpointRatio_eq]
  have h1 : ‖1 - cdfPhase a x‖ ≤ 2 * Real.pi * |(a : ℝ)| * thetaSource.cdfFun x := by
    refine le_trans ?_ (h.trans (mul_le_mul_of_nonneg_left hτ (by positivity)))
    rw [cdfPhase]; push_cast; exact le_rfl
  calc thetaSource.mass / thetaCuspFullSource x * ‖1 - cdfPhase a x‖
      ≤ thetaSource.mass / thetaCuspFullSource x * (2 * Real.pi * |(a : ℝ)| * thetaSource.cdfFun x) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = _ := by ring

theorem tendsto_actionWeight_atBot (a : ℤ) : Tendsto (actionWeight a) atBot (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hlim := tendsto_thetaEndpointRatio_atBot.const_mul (2 * Real.pi * |(a : ℝ)|)
  rw [mul_zero] at hlim
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [eventually_le_atBot 0] with x hx
  exact norm_actionWeight_le_of_nonpos hx a

theorem tendsto_actionWeight_atTop (a : ℤ) : Tendsto (actionWeight a) atTop (𝓝 0) := by
  have h := (tendsto_actionWeight_atBot (-a)).comp tendsto_neg_atTop_atBot
  refine h.congr fun x => ?_
  simp only [Function.comp]
  rw [actionWeight_neg, neg_neg]

/-! ## The fixed-shift law (1) -/

/-- **Integration by parts against the CDF phase.**
`∫ (1 − e^{2πiaF}) e^{2πinF} = −(2πin)^{−1} ∫ w_a' e^{2πinF}`. -/
theorem integral_one_sub_cdfPhase_mul_cdfPhase (a : ℤ) {n : ℕ} (hn : 0 < n) :
    (∫ x, (1 - cdfPhase a x) * cdfPhase n x) =
      -(1 / (2 * Real.pi * Complex.I * n)) * ∫ x, actionWeightDeriv a x * cdfPhase n x := by
  have hderiv : ∀ x, HasDerivAt (fun x => actionWeight a x * cdfPhase n x)
      (actionWeightDeriv a x * cdfPhase n x +
        2 * Real.pi * Complex.I * n * ((1 - cdfPhase a x) * cdfPhase n x)) x := by
    intro x
    have h := (hasDerivAt_actionWeight a x).mul (hasDerivAt_cdfPhase n x)
    refine h.congr_deriv ?_
    have hk := thetaCuspFullSource_pos_all x
    have hM := thetaSource.mass_pos
    have hkC : (thetaCuspFullSource x : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
    have hMC : (thetaSource.mass : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
    simp only [actionWeight]
    push_cast
    field_simp
  have hi1 : Integrable fun x => actionWeightDeriv a x * cdfPhase n x :=
    (integrable_actionWeightDeriv a).mul_of_top_left
      ((memLp_top_of_bound (continuous_cdfPhase n).aestronglyMeasurable 1
        (Eventually.of_forall fun x => (norm_cdfPhase n x).le)))
  have hi2 : Integrable fun x => (1 - cdfPhase a x) * cdfPhase n x := by
    refine (integrable_cdfTailWeight.const_mul (2 * Real.pi * |(a : ℝ)|)).mono'
      (((continuous_const.sub (continuous_cdfPhase a)).mul (continuous_cdfPhase n)).aestronglyMeasurable)
      (Eventually.of_forall fun x => ?_)
    rw [norm_mul, norm_cdfPhase, mul_one]
    have := norm_one_sub_cexp_cdf_le a x
    rw [cdfPhase]; push_cast at this ⊢; exact this
  have hlimBot : Tendsto (fun x => actionWeight a x * cdfPhase n x) atBot (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have := (tendsto_actionWeight_atBot a).norm
    rw [norm_zero] at this
    refine this.congr fun x => ?_
    rw [norm_mul, norm_cdfPhase, mul_one]
  have hlimTop : Tendsto (fun x => actionWeight a x * cdfPhase n x) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have := (tendsto_actionWeight_atTop a).norm
    rw [norm_zero] at this
    refine this.congr fun x => ?_
    rw [norm_mul, norm_cdfPhase, mul_one]
  have h := integral_of_hasDerivAt_of_tendsto hderiv (hi1.add (hi2.const_mul _)) hlimBot hlimTop
  rw [integral_add hi1 (hi2.const_mul _), integral_const_mul, sub_zero] at h
  have hnC : (2 * Real.pi * Complex.I * n : ℂ) ≠ 0 := by
    have : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
    simp [hπ, this, Complex.I_ne_zero]
  have hnC' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hcY : (2 * Real.pi * Complex.I * n : ℂ) * ∫ x, (1 - cdfPhase a x) * cdfPhase n x =
      -∫ x, actionWeightDeriv a x * cdfPhase n x := by linear_combination h
  calc (∫ x, (1 - cdfPhase a x) * cdfPhase n x)
      = (1 / (2 * Real.pi * Complex.I * n)) * ((2 * Real.pi * Complex.I * n : ℂ) *
          ∫ x, (1 - cdfPhase a x) * cdfPhase n x) := by field_simp
    _ = _ := by rw [hcY]; ring

theorem re_one_sub_cdfPhase_mul (a : ℤ) (n : ℕ) (x : ℝ) :
    ((1 - cdfPhase a x) * cdfPhase n x).re =
      Real.cos (2 * Real.pi * ((n : ℤ) : ℝ) * thetaSource.cdfFun x) -
        Real.cos (2 * Real.pi * (((n : ℤ) + a : ℤ) : ℝ) * thetaSource.cdfFun x) := by
  have e1 : (2 * Real.pi * Complex.I * ((n : ℝ) : ℂ) * thetaSource.cdfFun x : ℂ) =
      ((2 * Real.pi * ((n : ℤ) : ℝ) * thetaSource.cdfFun x : ℝ) : ℂ) * Complex.I := by push_cast; ring
  have e2 : (2 * Real.pi * Complex.I * ((a : ℝ) : ℂ) * thetaSource.cdfFun x +
      2 * Real.pi * Complex.I * ((n : ℝ) : ℂ) * thetaSource.cdfFun x : ℂ) =
      ((2 * Real.pi * (((n : ℤ) + a : ℤ) : ℝ) * thetaSource.cdfFun x : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  simp only [cdfPhase]
  rw [sub_mul, one_mul, ← Complex.exp_add, e2, e1, Complex.sub_re, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_re]

/-- `Φ_{n+a} − Φ_n = Re ∫ (1 − e^{2πiaF}) e^{2πinF}`. -/
theorem cdfAction_add_sub_eq (a : ℤ) (n : ℕ) :
    cdfAction (n + a) - cdfAction n = (∫ x, (1 - cdfPhase a x) * cdfPhase n x).re := by
  have hi2 : Integrable fun x => (1 - cdfPhase a x) * cdfPhase n x := by
    refine (integrable_cdfTailWeight.const_mul (2 * Real.pi * |(a : ℝ)|)).mono'
      (((continuous_const.sub (continuous_cdfPhase a)).mul (continuous_cdfPhase n)).aestronglyMeasurable)
      (Eventually.of_forall fun x => ?_)
    rw [norm_mul, norm_cdfPhase, mul_one]
    have := norm_one_sub_cexp_cdf_le a x
    rw [cdfPhase]; push_cast at this ⊢; exact this
  rw [re_integral_complex hi2, cdfAction, cdfAction, ← integral_sub (integrable_cdfAction_integrand _)
    (integrable_cdfAction_integrand _)]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  dsimp only
  rw [re_one_sub_cdfPhase_mul]
  ring

/-- **(1) The fixed-shift action law.**  For every fixed integer `a`, `Φ_{n+a} − Φ_n = o(1/n)`. -/
theorem tendsto_mul_cdfAction_add_sub (a : ℤ) :
    Tendsto (fun n : ℕ => (n : ℝ) * (cdfAction (n + a) - cdfAction n)) atTop (𝓝 0) := by
  have hRL := tendsto_integral_mul_cdfPhase (integrable_actionWeightDeriv a)
  have hc := hRL.const_mul (-(1 / (2 * Real.pi * Complex.I)))
  rw [mul_zero] at hc
  have h := (Complex.continuous_re.tendsto 0).comp hc
  rw [Complex.zero_re] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  simp only [Function.comp]
  rw [cdfAction_add_sub_eq, integral_one_sub_cdfPhase_mul_cdfPhase a hn]
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [← Complex.re_ofReal_mul]
  congr 1
  push_cast
  field_simp

/-- **`Φ_n → ∞`.** -/
theorem tendsto_cdfAction_atTop : Tendsto (fun n : ℕ => cdfAction n) atTop atTop := by
  refine tendsto_atTop.2 fun b => ?_
  set R : ℝ := max b 0 + 1
  have hR : 0 < R := by positivity
  have hRL := tendsto_integral_mul_cdfPhase
    ((integrable_indicator_iff measurableSet_Icc).2
      (continuous_const.integrableOn_Icc : IntegrableOn (fun _ : ℝ => (1 : ℂ)) (Icc (-R) R)))
  have hev := (Complex.continuous_re.tendsto 0).comp hRL
  rw [Complex.zero_re] at hev
  filter_upwards [hev.eventually (Iio_mem_nhds hR)] with n hn
  simp only [Function.comp] at hn
  have hint := integrable_cdfAction_integrand n
  have hnonneg : ∀ x, 0 ≤ 1 - Real.cos (2 * Real.pi * (n : ℤ) * thetaSource.cdfFun x) :=
    fun x => by linarith [Real.cos_le_one (2 * Real.pi * (n : ℤ) * thetaSource.cdfFun x)]
  have h1 : (∫ x in Icc (-R) R, (1 - Real.cos (2 * Real.pi * (n : ℤ) * thetaSource.cdfFun x))) ≤
      cdfAction n := setIntegral_le_integral hint (Eventually.of_forall hnonneg)
  have hcos : (∫ x in Icc (-R) R, Real.cos (2 * Real.pi * (n : ℤ) * thetaSource.cdfFun x)) =
      (∫ x, (Icc (-R) R).indicator (fun _ => (1 : ℂ)) x * cdfPhase n x).re := by
    rw [re_integral_complex, ← integral_indicator measurableSet_Icc]
    · refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      by_cases hx : x ∈ Icc (-R) R
      · simp only [Set.indicator_of_mem hx, one_mul, cdfPhase]
        rw [show (2 * Real.pi * Complex.I * (n : ℝ) * thetaSource.cdfFun x : ℂ) =
          ((2 * Real.pi * ((n : ℤ) : ℝ) * thetaSource.cdfFun x : ℝ) : ℂ) * Complex.I by push_cast; ring,
          Complex.exp_ofReal_mul_I_re]
      · simp [Set.indicator_of_notMem hx]
    · exact ((integrable_indicator_iff measurableSet_Icc).2
        (continuous_const.integrableOn_Icc : IntegrableOn (fun _ : ℝ => (1 : ℂ)) (Icc (-R) R))).mul_of_top_left
        (memLp_top_of_bound (continuous_cdfPhase n).aestronglyMeasurable 1
          (Eventually.of_forall fun x => (norm_cdfPhase n x).le))
  have h2 : (∫ x in Icc (-R) R, (1 - Real.cos (2 * Real.pi * (n : ℤ) * thetaSource.cdfFun x))) =
      2 * R - ∫ x in Icc (-R) R, Real.cos (2 * Real.pi * (n : ℤ) * thetaSource.cdfFun x) := by
    have hcI : IntegrableOn (fun x => Real.cos (2 * Real.pi * ((n : ℤ) : ℝ) * thetaSource.cdfFun x))
        (Icc (-R) R) :=
      (Real.continuous_cos.comp (continuous_const.mul thetaSource.continuous_cdfFun)).integrableOn_Icc
    rw [integral_sub (by exact continuous_const.integrableOn_Icc) (by exact hcI),
      setIntegral_const, Real.volume_real_Icc_of_le (by linarith), smul_eq_mul, mul_one]
    ring
  have hle : (∫ x in Icc (-R) R, Real.cos (2 * Real.pi * (n : ℤ) * thetaSource.cdfFun x)) < R := by
    rw [hcos]; exact hn
  have : b ≤ R - 1 := by simp only [R]; linarith [le_max_left b 0]
  linarith

/-! ## The card's quantile-coordinate forms -/

/-- **(2)** `t q(t) = I(x)/k(x)` at `t = F(x)`: the endpoint ratio in quantile coordinates. -/
theorem mul_quantileSpeed_eq_thetaEndpointRatio {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    t * HedenmalmQuantile.quantileSpeed thetaSource t =
      thetaEndpointRatio (thetaSource.quantileFun t) := by
  have hF := thetaSource.cdfFun_quantile ht
  have hM := thetaSource.mass_pos
  rw [HedenmalmQuantile.quantileSpeed, thetaEndpointRatio_eq, hF]
  simp only [thetaSource_k]
  ring

/-- `tq(t)` is nondecreasing on `(0,1)` and tends to `0` at `0`. -/
theorem monotoneOn_mul_quantileSpeed :
    MonotoneOn (fun t => t * HedenmalmQuantile.quantileSpeed thetaSource t) (Ioo (0 : ℝ) 1) := by
  have hmono : Monotone thetaEndpointRatio :=
    monotone_of_deriv_nonneg (fun x => (hasDerivAt_thetaEndpointRatio x).differentiableAt)
      fun x => by
        rw [(hasDerivAt_thetaEndpointRatio x).deriv]
        linarith [thetaEndpointRatio_mul_hazard_le x]
  intro s hs t ht hst
  simp only
  rw [mul_quantileSpeed_eq_thetaEndpointRatio hs, mul_quantileSpeed_eq_thetaEndpointRatio ht]
  exact hmono (thetaSource.strictMonoOn_quantileFun.monotoneOn hs ht hst)

/-- `w_a = g_a ∘ F` with `g_a(t) = q(t)(1 − e^{2πiat})`. -/
theorem actionWeight_eq_quantile (a : ℤ) (x : ℝ) :
    actionWeight a x = (HedenmalmQuantile.quantileSpeed thetaSource (thetaSource.cdfFun x) : ℂ) *
      (1 - Complex.exp (2 * Real.pi * Complex.I * a * thetaSource.cdfFun x)) := by
  rw [actionWeight, HedenmalmQuantile.quantileSpeed, thetaSource.quantile_cdfFun]
  rfl

/-- The fixed-shift difference in the card's form `Re ∫₀¹ g_a(t) e^{2πint} dt`. -/
theorem integral_one_sub_cdfPhase_mul_eq_quantile (a : ℤ) (n : ℕ) :
    (∫ x, (1 - cdfPhase a x) * cdfPhase n x) = ∫ t in Ioo (0 : ℝ) 1,
      (HedenmalmQuantile.quantileSpeed thetaSource t : ℂ) *
        (1 - Complex.exp (2 * Real.pi * Complex.I * a * t)) *
          Complex.exp (2 * Real.pi * Complex.I * n * t) := by
  set g : ℝ → ℂ := fun x => ((thetaSource.mass / thetaSource.k x : ℝ) : ℂ) *
    ((1 - cdfPhase a x) * cdfPhase n x)
  have hgm : AEStronglyMeasurable g volume :=
    ((Complex.continuous_ofReal.comp (continuous_const.div thetaSource.continuous_k
      fun x => (thetaSource.pos_k x).ne')).mul ((continuous_const.sub (continuous_cdfPhase a)).mul
        (continuous_cdfPhase n))).aestronglyMeasurable
  have h := HedenmalmQuantile.integral_comp_quantile thetaSource g hgm
  have h1 : (∫ x, thetaSource.normalized x • g x) = ∫ x, (1 - cdfPhase a x) * cdfPhase n x := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [g, PositiveDensitySource.normalized, Complex.real_smul]
    have hk := thetaSource.pos_k x
    have hM := thetaSource.mass_pos
    rw [← mul_assoc, ← Complex.ofReal_mul,
      show thetaSource.k x / thetaSource.mass * (thetaSource.mass / thetaSource.k x) = 1 by field_simp]
    simp
  rw [← h1, ← h]
  refine setIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
  simp only [g, cdfPhase, thetaSource.cdfFun_quantile hu, HedenmalmQuantile.quantileSpeed]
  push_cast
  ring

end

end RHTower
