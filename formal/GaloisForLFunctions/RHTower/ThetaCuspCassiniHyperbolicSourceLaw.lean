import GaloisForLFunctions.RHTower.XiSquaredSeamCassiniResolventSourceLaw
import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodModularSeam

/-!
# Hyperbolic carrier law for the theta--Cassini boundary response

The negative-imaginary Fourier--Laplace trace is written first as a full-line inward Esscher
partition.  Reflection of the even theta-cusp source then turns its value and logarithmic flux
into strictly positive half-line `cosh` and `sinh` integrals.  The resulting ratio is the genuine
Cassini boundary response on `u = 1 - t^2`.

This construction is unconditional and source-built.  It does not assert the still-open
all-order claim that the moving hyperbolic carrier collapses to one fixed compact Markov measure.
-/

open Complex Real MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

def thetaCuspInwardPartition (t : ℝ) : ℝ :=
  ∫ x : ℝ, Real.exp (-t * x) * thetaCuspFullSource x

def thetaCuspInwardFlux (t : ℝ) : ℝ :=
  -(∫ x : ℝ, x * Real.exp (-t * x) * thetaCuspFullSource x)

def thetaCuspHyperbolicPartition (t : ℝ) : ℝ :=
  2 * ∫ x : ℝ in Ioi 0,
    Real.cosh (t * x) * thetaCuspFullSource x

def thetaCuspHyperbolicFlux (t : ℝ) : ℝ :=
  2 * ∫ x : ℝ in Ioi 0,
    x * Real.sinh (t * x) * thetaCuspFullSource x

/-- Normalized positive half-line hyperbolic carrier.  The carrier depends on `t`; this
dependence is the remaining obstruction to a fixed Markov measure. -/
def thetaCuspHyperbolicExpectation (t : ℝ) (f : ℝ → ℝ) : ℝ :=
  (2 * ∫ x : ℝ in Ioi 0,
    f x * Real.cosh (t * x) * thetaCuspFullSource x) /
      thetaCuspHyperbolicPartition t

/-- Pointwise flux observable of the hyperbolic carrier. -/
def thetaCuspHyperbolicFluxObservable (t x : ℝ) : ℝ :=
  x * Real.tanh (t * x) / t

/-- Density of the normalized half-line carrier relative to Lebesgue measure. -/
def thetaCuspHyperbolicCarrierDensity (t x : ℝ) : ℝ :=
  2 * Real.cosh (t * x) * thetaCuspFullSource x /
    thetaCuspHyperbolicPartition t

theorem integrable_thetaCuspInwardPartition
    {t : ℝ} (ht : |t| < 1) :
    Integrable (fun x : ℝ => Real.exp (-t * x) * thetaCuspFullSource x) := by
  have htilt : |-t| < 1 := by simpa using ht
  have h :=
    (thetaCuspTiltedSchwartzReal (-t) htilt).integrable (μ := (volume : Measure ℝ))
  apply h.congr
  filter_upwards with x
  simp [thetaCuspTiltedSchwartzReal_apply, thetaCuspTiltedSource]

theorem integrable_thetaCuspInwardFlux
    {t : ℝ} (ht : |t| < 1) :
    Integrable (fun x : ℝ => x * Real.exp (-t * x) * thetaCuspFullSource x) := by
  have htilt : |-t| < 1 := by simpa using ht
  have hmajor :=
    (thetaCuspTiltedSchwartzReal (-t) htilt).integrable_pow_mul
      (volume : Measure ℝ) 1
  apply hmajor.mono
  · exact (((continuous_id.mul (Real.continuous_exp.comp
      (continuous_const.mul continuous_id))).mul
        contDiff_thetaCuspFullSource.continuous).aestronglyMeasurable)
  · filter_upwards with x
    simp [thetaCuspTiltedSchwartzReal_apply, thetaCuspTiltedSource,
      Real.norm_eq_abs]
    rw [mul_assoc]

theorem integrableOn_cosh_mul_thetaCuspFullSource
    {t : ℝ} (ht : |t| < 1) :
    IntegrableOn (fun x : ℝ =>
      Real.cosh (t * x) * thetaCuspFullSource x) (Ioi 0) := by
  have hp : IntegrableOn (fun x : ℝ =>
      Real.exp (t * x) * thetaCuspFullSource x) (Ioi 0) := by
    simpa using (integrable_thetaCuspInwardPartition (t := -t) (by simpa using ht)).integrableOn
  have hm : IntegrableOn (fun x : ℝ =>
      Real.exp (-t * x) * thetaCuspFullSource x) (Ioi 0) :=
    (integrable_thetaCuspInwardPartition ht).integrableOn
  have hhalf := (hp.add hm).const_mul (1 / 2 : ℝ)
  apply hhalf.congr
  filter_upwards with x
  rw [Real.cosh_eq]
  simp only [Pi.add_apply]
  ring

theorem integrableOn_mul_sinh_mul_thetaCuspFullSource
    {t : ℝ} (ht : |t| < 1) :
    IntegrableOn (fun x : ℝ =>
      x * Real.sinh (t * x) * thetaCuspFullSource x) (Ioi 0) := by
  have hp : IntegrableOn (fun x : ℝ =>
      x * Real.exp (t * x) * thetaCuspFullSource x) (Ioi 0) := by
    simpa using (integrable_thetaCuspInwardFlux (t := -t) (by simpa using ht)).integrableOn
  have hm : IntegrableOn (fun x : ℝ =>
      x * Real.exp (-t * x) * thetaCuspFullSource x) (Ioi 0) :=
    (integrable_thetaCuspInwardFlux ht).integrableOn
  have hhalf := (hp.sub hm).const_mul (1 / 2 : ℝ)
  apply hhalf.congr
  filter_upwards with x
  rw [Real.sinh_eq]
  simp only [Pi.sub_apply]
  ring

theorem thetaCuspInwardPartition_eq_hyperbolicPartition
    {t : ℝ} (ht : |t| < 1) :
    thetaCuspInwardPartition t = thetaCuspHyperbolicPartition t := by
  let p : ℝ → ℝ := fun x =>
    Real.exp (t * x) * thetaCuspFullSource x
  let m : ℝ → ℝ := fun x =>
    Real.exp (-t * x) * thetaCuspFullSource x
  have hp : Integrable p := by
    simpa only [p, neg_neg] using
      (integrable_thetaCuspInwardPartition (t := -t) (by simpa using ht))
  have hm : Integrable m := by
    simpa only [m] using integrable_thetaCuspInwardPartition ht
  have hp_eq_neg : p = fun x => m (-x) := by
    funext x
    simp only [p, m]
    rw [thetaCuspFullSource_neg]
    congr 2
    ring
  have href : (∫ x : ℝ in Ioi 0, p x) =
      ∫ x : ℝ in Iic 0, m x := by
    rw [hp_eq_neg, integral_comp_neg_Ioi]
    norm_num
  calc
    thetaCuspInwardPartition t = ∫ x : ℝ, m x := by
      rfl
    _ = (∫ x : ℝ in Iic 0, m x) + (∫ x : ℝ in Ioi 0, m x) :=
      (intervalIntegral.integral_Iic_add_Ioi hm.integrableOn hm.integrableOn).symm
    _ = (∫ x : ℝ in Ioi 0, p x) + (∫ x : ℝ in Ioi 0, m x) := by
      rw [href]
    _ = ∫ x : ℝ in Ioi 0, p x + m x := by
      rw [integral_add hp.integrableOn hm.integrableOn]
    _ = ∫ x : ℝ in Ioi 0,
        2 * (Real.cosh (t * x) * thetaCuspFullSource x) := by
      apply integral_congr_ae
      filter_upwards with x
      simp only [p, m]
      rw [Real.cosh_eq]
      ring
    _ = thetaCuspHyperbolicPartition t := by
      rw [integral_const_mul]
      rfl

theorem thetaCuspInwardFlux_eq_hyperbolicFlux
    {t : ℝ} (ht : |t| < 1) :
    thetaCuspInwardFlux t = thetaCuspHyperbolicFlux t := by
  let p : ℝ → ℝ := fun x =>
    x * Real.exp (t * x) * thetaCuspFullSource x
  let m : ℝ → ℝ := fun x =>
    x * Real.exp (-t * x) * thetaCuspFullSource x
  have hp : Integrable p := by
    simpa only [p, neg_neg] using
      (integrable_thetaCuspInwardFlux (t := -t) (by simpa using ht))
  have hm : Integrable m := by
    simpa only [m] using integrable_thetaCuspInwardFlux ht
  have hm_reflect : (fun x => m (-x)) = fun x => -p x := by
    funext x
    simp only [p, m]
    rw [thetaCuspFullSource_neg]
    ring
  have href : (∫ x : ℝ in Iic 0, m x) =
      -(∫ x : ℝ in Ioi 0, p x) := by
    calc
      (∫ x : ℝ in Iic 0, m x) = ∫ x : ℝ in Ioi 0, m (-x) := by
        simpa using (integral_comp_neg_Ioi 0 m).symm
      _ = ∫ x : ℝ in Ioi 0, -p x := by rw [hm_reflect]
      _ = -(∫ x : ℝ in Ioi 0, p x) := by rw [integral_neg]
  calc
    thetaCuspInwardFlux t = -(∫ x : ℝ, m x) := by rfl
    _ = -((∫ x : ℝ in Iic 0, m x) + (∫ x : ℝ in Ioi 0, m x)) := by
      rw [intervalIntegral.integral_Iic_add_Ioi hm.integrableOn hm.integrableOn]
    _ = (∫ x : ℝ in Ioi 0, p x) - (∫ x : ℝ in Ioi 0, m x) := by
      rw [href]
      ring
    _ = ∫ x : ℝ in Ioi 0, p x - m x := by
      rw [integral_sub hp.integrableOn hm.integrableOn]
    _ = ∫ x : ℝ in Ioi 0,
        2 * (x * Real.sinh (t * x) * thetaCuspFullSource x) := by
      apply integral_congr_ae
      filter_upwards with x
      simp only [p, m]
      rw [Real.sinh_eq]
      ring
    _ = thetaCuspHyperbolicFlux t := by
      rw [integral_const_mul]
      rfl

theorem thetaCuspHyperbolicPartition_pos
    {t : ℝ} (ht : |t| < 1) :
    0 < thetaCuspHyperbolicPartition t := by
  let f : ℝ → ℝ := fun x =>
    Real.cosh (t * x) * thetaCuspFullSource x
  have hfcont : Continuous f := by
    dsimp only [f]
    exact (Real.continuous_cosh.comp
      (continuous_const.mul continuous_id)).mul
        contDiff_thetaCuspFullSource.continuous
  have hfint : IntegrableOn f (Ioi 0) := by
    simpa only [f] using integrableOn_cosh_mul_thetaCuspFullSource ht
  have hfnn : 0 ≤ᵐ[volume.restrict (Ioi 0)] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact mul_nonneg (Real.cosh_pos _).le
      (thetaCuspFullSource_pos_of_pos hx).le
  rw [thetaCuspHyperbolicPartition]
  apply mul_pos (by norm_num)
  apply (setIntegral_pos_iff_support_of_nonneg_ae hfnn hfint).2
  have hopen : IsOpen (Function.support f ∩ Ioi (0 : ℝ)) :=
    hfcont.isOpen_support.inter isOpen_Ioi
  apply hopen.measure_pos (volume : Measure ℝ)
  refine ⟨1, ?_, by norm_num⟩
  change f 1 ≠ 0
  exact (mul_pos (Real.cosh_pos _)
    (thetaCuspFullSource_pos_of_pos zero_lt_one)).ne'

theorem thetaCuspHyperbolicFlux_pos
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    0 < thetaCuspHyperbolicFlux t := by
  have ht : |t| < 1 := by rw [abs_of_pos ht0]; exact ht1
  let f : ℝ → ℝ := fun x =>
    x * Real.sinh (t * x) * thetaCuspFullSource x
  have hfcont : Continuous f := by
    dsimp only [f]
    exact ((continuous_id.mul (Real.continuous_sinh.comp
      (continuous_const.mul continuous_id))).mul
        contDiff_thetaCuspFullSource.continuous)
  have hfint : IntegrableOn f (Ioi 0) := by
    simpa only [f] using integrableOn_mul_sinh_mul_thetaCuspFullSource ht
  have hfnn : 0 ≤ᵐ[volume.restrict (Ioi 0)] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact mul_nonneg
      (mul_nonneg hx.le (Real.sinh_pos_iff.mpr (mul_pos ht0 hx)).le)
      (thetaCuspFullSource_pos_of_pos hx).le
  rw [thetaCuspHyperbolicFlux]
  apply mul_pos (by norm_num)
  apply (setIntegral_pos_iff_support_of_nonneg_ae hfnn hfint).2
  have hopen : IsOpen (Function.support f ∩ Ioi (0 : ℝ)) :=
    hfcont.isOpen_support.inter isOpen_Ioi
  apply hopen.measure_pos (volume : Measure ℝ)
  refine ⟨1, ?_, by norm_num⟩
  change f 1 ≠ 0
  exact (mul_pos
    (mul_pos zero_lt_one (Real.sinh_pos_iff.mpr (by simpa using ht0)))
    (thetaCuspFullSource_pos_of_pos zero_lt_one)).ne'

theorem thetaCuspHyperbolicExpectation_one
    {t : ℝ} (ht : |t| < 1) :
    thetaCuspHyperbolicExpectation t (fun _ => 1) = 1 := by
  rw [thetaCuspHyperbolicExpectation]
  have hpartition :
      2 * (∫ x : ℝ in Ioi 0,
        (1 : ℝ) * Real.cosh (t * x) * thetaCuspFullSource x) =
        thetaCuspHyperbolicPartition t := by
    rw [thetaCuspHyperbolicPartition]
    congr 2
    funext x
    ring
  rw [hpartition]
  exact div_self (thetaCuspHyperbolicPartition_pos ht).ne'

theorem thetaCuspHyperbolicExpectation_fluxObservable
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    thetaCuspHyperbolicExpectation t
        (thetaCuspHyperbolicFluxObservable t) =
      thetaCuspHyperbolicFlux t /
        (t * thetaCuspHyperbolicPartition t) := by
  have htne : t ≠ 0 := ht0.ne'
  have hintegral :
      (∫ x : ℝ in Ioi 0,
        thetaCuspHyperbolicFluxObservable t x * Real.cosh (t * x) *
          thetaCuspFullSource x) =
      (∫ x : ℝ in Ioi 0,
        x * Real.sinh (t * x) * thetaCuspFullSource x) / t := by
    calc
      _ = ∫ x : ℝ in Ioi 0,
          (x * Real.sinh (t * x) * thetaCuspFullSource x) / t := by
        apply integral_congr_ae
        filter_upwards with x
        rw [thetaCuspHyperbolicFluxObservable, Real.tanh_eq_sinh_div_cosh]
        field_simp [htne, (Real.cosh_pos (t * x)).ne']
      _ = _ := by
        simpa using (integral_div (μ := volume.restrict (Ioi 0)) t
          (fun x : ℝ => x * Real.sinh (t * x) * thetaCuspFullSource x))
  rw [thetaCuspHyperbolicExpectation, hintegral, thetaCuspHyperbolicFlux]
  have ht : |t| < 1 := by rw [abs_of_pos ht0]; exact ht1
  have hZne : thetaCuspHyperbolicPartition t ≠ 0 :=
    (thetaCuspHyperbolicPartition_pos ht).ne'
  field_simp [htne, hZne]
  apply integral_congr_ae
  filter_upwards with x
  rw [mul_comm x t]

private theorem thetaCuspSourceTerm_zero_nonneg_for_carrier (n : ℕ) :
    0 ≤ thetaCuspSourceTerm 0 n := by
  have hcontinuous : Continuous (fun x : ℝ => thetaCuspSourceTerm x n) := by
    unfold thetaCuspSourceTerm thetaCuspSeed
    fun_prop
  have hlimit : Tendsto (fun k : ℕ =>
      thetaCuspSourceTerm (1 / ((k : ℝ) + 1)) n) atTop
      (𝓝 (thetaCuspSourceTerm 0 n)) :=
    hcontinuous.continuousAt.tendsto.comp tendsto_one_div_add_atTop_nhds_zero_nat
  exact ge_of_tendsto' hlimit fun k =>
    thetaCuspSourceTerm_nonneg_of_pos (by positivity) n

private theorem thetaCuspSourceTerm_one_zero_pos_for_carrier :
    0 < thetaCuspSourceTerm 0 1 := by
  let u : ℝ := Real.exp 0
  have hu : 1 ≤ u := by dsimp [u]; exact Real.one_le_exp le_rfl
  have hcore : 0 < 2 * Real.pi * u ^ 2 - 3 := by
    nlinarith [Real.pi_gt_three, sq_nonneg u]
  rw [thetaCuspSourceTerm, thetaCuspSeed]
  simp only [Nat.cast_one, one_mul]
  rw [show 2 * Real.pi * u ^ 4 - 3 * u ^ 2 =
    u ^ 2 * (2 * Real.pi * u ^ 2 - 3) by ring]
  positivity

private theorem thetaCuspFullSource_zero_pos_for_carrier :
    0 < thetaCuspFullSource 0 := by
  rw [thetaCuspFullSource]
  exact (summable_thetaCuspSourceTerm 0).tsum_pos
    thetaCuspSourceTerm_zero_nonneg_for_carrier 1
    thetaCuspSourceTerm_one_zero_pos_for_carrier

/-- **Carrier-motion rigidity.**  Distinct positive strip apertures give distinct normalized
hyperbolic theta carriers.  Thus the pointwise Stieltjes structure of the flux observable cannot
be integrated against one of these carriers after silently freezing its aperture. -/
theorem thetaCuspHyperbolicCarrierDensity_injOn :
    Set.InjOn (fun t : ℝ => thetaCuspHyperbolicCarrierDensity t) (Ioo 0 1) := by
  intro t ht s hs heq
  have htAbs : |t| < 1 := by rw [abs_of_pos ht.1]; exact ht.2
  have hsAbs : |s| < 1 := by rw [abs_of_pos hs.1]; exact hs.2
  have hZt : 0 < thetaCuspHyperbolicPartition t :=
    thetaCuspHyperbolicPartition_pos htAbs
  have hZs : 0 < thetaCuspHyperbolicPartition s :=
    thetaCuspHyperbolicPartition_pos hsAbs
  have hPhi0 : 0 < thetaCuspFullSource 0 :=
    thetaCuspFullSource_zero_pos_for_carrier
  have hzero := congrFun heq 0
  have hZeq : thetaCuspHyperbolicPartition t =
      thetaCuspHyperbolicPartition s := by
    simp only [thetaCuspHyperbolicCarrierDensity, mul_zero, Real.cosh_zero,
      mul_one] at hzero
    field_simp [hZt.ne', hZs.ne'] at hzero
    nlinarith
  have hone := congrFun heq 1
  have hcosh : Real.cosh t = Real.cosh s := by
    simp only [thetaCuspHyperbolicCarrierDensity, mul_one] at hone
    rw [hZeq] at hone
    field_simp [hZs.ne'] at hone
    nlinarith [thetaCuspFullSource_pos_of_pos zero_lt_one]
  exact Real.cosh_injOn ht.1.le hs.1.le hcosh

theorem thetaCuspFourierLaplace_neg_mul_I_eq_inwardPartition
    (t : ℝ) :
    thetaCuspFourierLaplace (-((t : ℂ) * I)) =
      (thetaCuspInwardPartition t : ℂ) := by
  rw [thetaCuspFourierLaplace]
  have hfun : thetaCuspFourierLaplaceIntegrand (-((t : ℂ) * I)) =
      fun x : ℝ =>
        ((Real.exp (-t * x) * thetaCuspFullSource x : ℝ) : ℂ) := by
    funext x
    rw [thetaCuspFourierLaplaceIntegrand]
    have harg : -I * (-((t : ℂ) * I)) * (x : ℂ) =
        (((-t * x : ℝ)) : ℂ) := by
      push_cast
      rw [show -I * (-((t : ℂ) * I)) * (x : ℂ) =
        (t : ℂ) * (I * I) * (x : ℂ) by ring, I_mul_I]
      ring
    rw [harg, ← Complex.ofReal_exp]
    norm_cast
  rw [hfun, thetaCuspInwardPartition]
  exact integral_ofReal

theorem deriv_thetaCuspFourierLaplace_neg_mul_I_eq_inwardFlux
    {t : ℝ} (ht : |t| < 1) :
    deriv thetaCuspFourierLaplace (-((t : ℂ) * I)) =
      I * (thetaCuspInwardFlux t : ℂ) := by
  have hw : |(-((t : ℂ) * I)).im| < 1 := by
    simpa using ht
  rw [(hasDerivAt_thetaCuspFourierLaplace hw).deriv]
  have hfun : thetaCuspFourierLaplaceDerivativeIntegrand (-((t : ℂ) * I)) =
      fun x : ℝ => -I *
        ((x * Real.exp (-t * x) * thetaCuspFullSource x : ℝ) : ℂ) := by
    funext x
    rw [thetaCuspFourierLaplaceDerivativeIntegrand,
      thetaCuspFourierLaplaceIntegrand]
    have harg : -I * (-((t : ℂ) * I)) * (x : ℂ) =
        (((-t * x : ℝ)) : ℂ) := by
      push_cast
      rw [show -I * (-((t : ℂ) * I)) * (x : ℂ) =
        (t : ℂ) * (I * I) * (x : ℂ) by ring, I_mul_I]
      ring
    rw [harg, ← Complex.ofReal_exp]
    push_cast
    ring
  rw [hfun, integral_const_mul]
  have hcoe := integral_ofReal (X := ℝ) (μ := (volume : Measure ℝ)) (𝕜 := ℂ)
    (f := fun x : ℝ => x * Real.exp (-t * x) * thetaCuspFullSource x)
  calc
    -I * (∫ x : ℝ,
        ((x * Real.exp (-t * x) * thetaCuspFullSource x : ℝ) : ℂ)) =
        -I * ((∫ x : ℝ,
          x * Real.exp (-t * x) * thetaCuspFullSource x : ℝ) : ℂ) :=
      congrArg (fun z : ℂ => -I * z) hcoe
    _ = I * (thetaCuspInwardFlux t : ℂ) := by
      simp only [thetaCuspInwardFlux, Complex.ofReal_neg]
      ring

theorem thetaCuspCassiniInwardCoordinateResponse_one_sub_sq_eq_inwardFluxRatio
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    thetaCuspCassiniInwardCoordinateResponse (1 - t ^ 2) =
      ((thetaCuspInwardFlux t /
        (t * thetaCuspInwardPartition t) : ℝ) : ℂ) := by
  have ht : |t| < 1 := by rw [abs_of_pos ht0]; exact ht1
  have hsqrt : Real.sqrt (1 - (1 - t ^ 2)) = t := by
    rw [show 1 - (1 - t ^ 2) = t ^ 2 by ring, Real.sqrt_sq_eq_abs,
      abs_of_pos ht0]
  have hvalue := thetaCuspFourierLaplace_neg_mul_I_eq_inwardPartition t
  have hderiv := deriv_thetaCuspFourierLaplace_neg_mul_I_eq_inwardFlux ht
  have hstrip : -((t : ℂ) * I) ∈ thetaCuspFourierLaplaceStrip := by
    rw [thetaCuspFourierLaplaceStrip]
    simp
    constructor <;> linarith
  have hnonzero : thetaCuspInwardPartition t ≠ 0 := by
    apply Complex.ofReal_ne_zero.mp
    rw [← hvalue, thetaCuspFourierLaplace_eq_XiC_on_strip hstrip]
    exact XiC_neg_imaginaryAxis_ne_zero ht0
  rw [thetaCuspCassiniInwardCoordinateResponse, hsqrt, logDeriv_apply,
    hvalue, hderiv]
  push_cast
  field_simp [ht0.ne', hnonzero]
  rw [I_sq]
  ring

theorem thetaCuspCassiniInwardCoordinateResponse_one_sub_sq_eq_hyperbolicFluxRatio
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    thetaCuspCassiniInwardCoordinateResponse (1 - t ^ 2) =
      ((thetaCuspHyperbolicFlux t /
        (t * thetaCuspHyperbolicPartition t) : ℝ) : ℂ) := by
  have ht : |t| < 1 := by rw [abs_of_pos ht0]; exact ht1
  rw [← thetaCuspInwardPartition_eq_hyperbolicPartition ht,
    ← thetaCuspInwardFlux_eq_hyperbolicFlux ht]
  exact thetaCuspCassiniInwardCoordinateResponse_one_sub_sq_eq_inwardFluxRatio ht0 ht1

theorem thetaCuspCassiniInwardCoordinateResponse_one_sub_sq_eq_hyperbolicExpectation
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    thetaCuspCassiniInwardCoordinateResponse (1 - t ^ 2) =
      (thetaCuspHyperbolicExpectation t
        (thetaCuspHyperbolicFluxObservable t) : ℂ) := by
  rw [thetaCuspHyperbolicExpectation_fluxObservable ht0 ht1]
  exact thetaCuspCassiniInwardCoordinateResponse_one_sub_sq_eq_hyperbolicFluxRatio ht0 ht1

theorem thetaCuspCassiniInwardCoordinateResponse_one_sub_sq_re_pos
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    0 < (thetaCuspCassiniInwardCoordinateResponse (1 - t ^ 2)).re := by
  rw [thetaCuspCassiniInwardCoordinateResponse_one_sub_sq_eq_hyperbolicFluxRatio ht0 ht1]
  simp only [ofReal_re]
  exact div_pos (thetaCuspHyperbolicFlux_pos ht0 ht1)
    (mul_pos ht0 (thetaCuspHyperbolicPartition_pos (by
      rw [abs_of_pos ht0]
      exact ht1)))

theorem thetaCuspCassiniInwardCoordinateResponse_one_sub_sq_im_eq_zero
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    (thetaCuspCassiniInwardCoordinateResponse (1 - t ^ 2)).im = 0 := by
  rw [thetaCuspCassiniInwardCoordinateResponse_one_sub_sq_eq_hyperbolicFluxRatio ht0 ht1]
  exact ofReal_im _

/-! ## Fixed likelihood carrier behind the Cassini response -/

/-- The fixed positive higher-tail likelihood partition at the intrinsic coordinate of `x`. -/
def thetaCuspCassiniLikelihoodFactor (x : ℝ) : ℝ :=
  1 + ∫ r : ℝ, Real.exp (-thetaCuspLikelihoodCoordinate x * r)
    ∂thetaCuspHigherLikelihoodSpectralMeasure

/-- Aperture-independent half-line density obtained from the first theta atom and the fixed
higher-tail likelihood measure. -/
def thetaCuspCassiniLikelihoodBaseDensity (x : ℝ) : ℝ :=
  2 * thetaCuspSourceTerm x 1 * thetaCuspCassiniLikelihoodFactor x

/-- Hyperbolic partition formed from the fixed likelihood base density. -/
def thetaCuspCassiniLikelihoodPartition (t : ℝ) : ℝ :=
  ∫ x : ℝ in Ioi 0,
    Real.cosh (t * x) * thetaCuspCassiniLikelihoodBaseDensity x

/-- Hyperbolic flux formed from the same fixed likelihood base density. -/
def thetaCuspCassiniLikelihoodFlux (t : ℝ) : ℝ :=
  ∫ x : ℝ in Ioi 0,
    x * Real.sinh (t * x) * thetaCuspCassiniLikelihoodBaseDensity x

/-- The explicit likelihood integral is the existing positive likelihood partition. -/
theorem thetaCuspCassiniLikelihoodFactor_eq_partition
    {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspCassiniLikelihoodFactor x =
      thetaCuspLikelihoodPartition (thetaCuspLikelihoodCoordinate x) := by
  have hB : 0 < thetaCuspLikelihoodCoordinate x :=
    thetaCuspLikelihoodCoordinate_pos hx
  rw [thetaCuspCassiniLikelihoodFactor, thetaCuspLikelihoodPartition,
    integral_exp_neg_mul_thetaCuspHigherLikelihoodSpectralMeasure hB]

/-- The fixed likelihood density is exactly twice the genuine theta source on the positive
half-line. -/
theorem thetaCuspCassiniLikelihoodBaseDensity_eq_two_mul_fullSource
    {x : ℝ} (hx : 0 < x) :
    thetaCuspCassiniLikelihoodBaseDensity x =
      2 * thetaCuspFullSource x := by
  have hB : 0 < thetaCuspLikelihoodCoordinate x :=
    thetaCuspLikelihoodCoordinate_pos hx.le
  rw [thetaCuspCassiniLikelihoodBaseDensity,
    thetaCuspCassiniLikelihoodFactor,
    thetaCuspFullSource_eq_first_mul_one_add_spectralIntegral_of_coordinate_pos hB]
  ring

/-- The likelihood base density is strictly positive at every positive source point. -/
theorem thetaCuspCassiniLikelihoodBaseDensity_pos
    {x : ℝ} (hx : 0 < x) :
    0 < thetaCuspCassiniLikelihoodBaseDensity x := by
  rw [thetaCuspCassiniLikelihoodBaseDensity_eq_two_mul_fullSource hx]
  exact mul_pos (by norm_num) (thetaCuspFullSource_pos_of_pos hx)

/-- The fixed carrier already carries the source's strict all-order likelihood Hankel hierarchy
at every positive source point. -/
theorem thetaCuspCassiniLikelihoodBaseDensity_pos_and_spectralHankel
    {x : ℝ} (hx : 0 < x) :
    0 < thetaCuspCassiniLikelihoodBaseDensity x ∧
      ∀ q : ℕ,
        (HTGeometry.momentHankelMatrix
          (thetaCuspHigherLikelihoodSpectralMoment
            (thetaCuspLikelihoodCoordinate x)) q).PosDef := by
  have hB : 0 < thetaCuspLikelihoodCoordinate x :=
    thetaCuspLikelihoodCoordinate_pos hx.le
  exact ⟨thetaCuspCassiniLikelihoodBaseDensity_pos hx,
    (thetaCuspHigherLikelihoodSpectralMasterLaw hB).2⟩

/-- The Cassini hyperbolic partition is the `cosh` transform of one fixed positive likelihood
base density. -/
theorem thetaCuspCassiniLikelihoodPartition_eq_hyperbolicPartition
    (t : ℝ) :
    thetaCuspCassiniLikelihoodPartition t =
      thetaCuspHyperbolicPartition t := by
  rw [thetaCuspCassiniLikelihoodPartition, thetaCuspHyperbolicPartition]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [thetaCuspCassiniLikelihoodBaseDensity_eq_two_mul_fullSource hx]
  ring

/-- The Cassini hyperbolic flux is the `x sinh(tx)` transform of the same fixed likelihood base
density. -/
theorem thetaCuspCassiniLikelihoodFlux_eq_hyperbolicFlux
    (t : ℝ) :
    thetaCuspCassiniLikelihoodFlux t = thetaCuspHyperbolicFlux t := by
  rw [thetaCuspCassiniLikelihoodFlux, thetaCuspHyperbolicFlux]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [thetaCuspCassiniLikelihoodBaseDensity_eq_two_mul_fullSource hx]
  ring

/-- Exact source/response intertwiner: the RH-facing Cassini response is a ratio of two transforms
of the explicit aperture-independent likelihood carrier. -/
theorem thetaCuspCassiniInwardCoordinateResponse_one_sub_sq_eq_likelihoodCarrierRatio
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    thetaCuspCassiniInwardCoordinateResponse (1 - t ^ 2) =
      ((thetaCuspCassiniLikelihoodFlux t /
        (t * thetaCuspCassiniLikelihoodPartition t) : ℝ) : ℂ) := by
  rw [thetaCuspCassiniLikelihoodFlux_eq_hyperbolicFlux,
    thetaCuspCassiniLikelihoodPartition_eq_hyperbolicPartition]
  exact
    thetaCuspCassiniInwardCoordinateResponse_one_sub_sq_eq_hyperbolicFluxRatio ht0 ht1

end RHTower
