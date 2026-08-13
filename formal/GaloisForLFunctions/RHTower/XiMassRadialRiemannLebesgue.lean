import GaloisForLFunctions.RHTower.XiMassKleinGordonConnection
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Timelike Riemann--Lebesgue decay on the Xi mass shell

The positive-energy mass shell `sqrt (x^2 + a^2)` is not a linear Fourier phase in the spectral
coordinate `x`.  Pushing the two real sheets `x > 0` and `x < 0` onto energy `y > a` produces the
exact threshold density

`y / sqrt (y^2-a^2) * (f(sqrt (y^2-a^2)) + f(-sqrt (y^2-a^2)))`.

This file proves that density is integrable whenever `f` is integrable, identifies the radial
oscillatory integral with its ordinary Fourier transform, and obtains vertical-time decay from the
Riemann--Lebesgue lemma.  No stationary-phase estimate or asymptotic expansion is assumed.
-/

open Complex Filter MeasureTheory Set Topology

namespace RHTower

noncomputable section

/-- Positive spatial momentum as a function of mass-shell energy. -/
def xiMassRadialInverse (a y : ℝ) : ℝ :=
  Real.sqrt (y ^ 2 - a ^ 2)

/-- Jacobian of the positive-energy-to-positive-momentum map. -/
def xiMassRadialJacobian (a y : ℝ) : ℝ :=
  y / Real.sqrt (y ^ 2 - a ^ 2)

/-- Full two-sheet pushforward density on the positive mass shell, extended by zero. -/
def xiMassRadialPushforwardDensity (a : ℝ) (f : ℝ → ℂ) (y : ℝ) : ℂ :=
  (Ioi a).indicator
    (fun v => xiMassRadialJacobian a v •
      (f (xiMassRadialInverse a v) + f (-xiMassRadialInverse a v))) y

theorem xiMassRadialInverse_pos {a y : ℝ} (ha : 0 < a) (hy : a < y) :
    0 < xiMassRadialInverse a y := by
  rw [xiMassRadialInverse, Real.sqrt_pos]
  nlinarith

theorem xiMassRadialInverse_sq {a y : ℝ} (ha : 0 < a) (hy : a < y) :
    xiMassRadialInverse a y ^ 2 = y ^ 2 - a ^ 2 := by
  rw [xiMassRadialInverse, Real.sq_sqrt]
  nlinarith

theorem xiMassRadialFrequency_inverse {a y : ℝ} (ha : 0 < a) (hy : a < y) :
    xiMassRadialFrequency a (xiMassRadialInverse a y) = y := by
  rw [xiMassRadialFrequency, xiMassRadialInverse_sq ha hy]
  have hy0 : 0 ≤ y := le_of_lt (lt_trans ha hy)
  rw [show y ^ 2 - a ^ 2 + a ^ 2 = y ^ 2 by ring, Real.sqrt_sq hy0]

theorem xiMassRadialInverse_frequency {a x : ℝ} (hx : 0 < x) :
    xiMassRadialInverse a (xiMassRadialFrequency a x) = x := by
  rw [xiMassRadialInverse]
  have hfreq := xiMassRadialFrequency_sq (a := a) x
  rw [hfreq, show x ^ 2 + a ^ 2 - a ^ 2 = x ^ 2 by ring,
    Real.sqrt_sq hx.le]

theorem xiMassRadialFrequency_gt_mass {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    a < xiMassRadialFrequency a x := by
  have hfreq := xiMassRadialFrequency_sq (a := a) x
  have hnonneg : 0 ≤ xiMassRadialFrequency a x := Real.sqrt_nonneg _
  nlinarith [sq_pos_of_pos hx]

theorem image_xiMassRadialInverse_Ioi {a : ℝ} (ha : 0 < a) :
    xiMassRadialInverse a '' Ioi a = Ioi 0 := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact xiMassRadialInverse_pos ha hy
  · intro hx
    refine ⟨xiMassRadialFrequency a x, xiMassRadialFrequency_gt_mass ha hx, ?_⟩
    exact xiMassRadialInverse_frequency hx

theorem injOn_xiMassRadialInverse_Ioi {a : ℝ} (ha : 0 < a) :
    InjOn (xiMassRadialInverse a) (Ioi a) := by
  intro y₁ hy₁ y₂ hy₂ h
  have hsq := congrArg (fun z : ℝ => z ^ 2) h
  rw [xiMassRadialInverse_sq ha hy₁, xiMassRadialInverse_sq ha hy₂] at hsq
  have hy₁0 : 0 < y₁ := lt_trans ha hy₁
  have hy₂0 : 0 < y₂ := lt_trans ha hy₂
  nlinarith

theorem hasDerivAt_xiMassRadialInverse {a y : ℝ} (ha : 0 < a) (hy : a < y) :
    HasDerivAt (xiMassRadialInverse a) (xiMassRadialJacobian a y) y := by
  have harg : 0 < y ^ 2 - a ^ 2 := by nlinarith
  have hinner : HasDerivAt (fun v : ℝ => v * v - a ^ 2) (y + y) y := by
    simpa only [Pi.mul_apply, id_eq, one_mul, mul_one] using
      (((hasDerivAt_id y).mul (hasDerivAt_id y)).sub_const (a ^ 2))
  have hsqrt : HasDerivAt (fun v : ℝ => Real.sqrt (v ^ 2 - a ^ 2))
      ((2 * y) / (2 * Real.sqrt (y ^ 2 - a ^ 2))) y := by
    have harg' : y * y - a ^ 2 ≠ 0 := by nlinarith
    simpa only [pow_two, two_mul] using hinner.sqrt harg'
  change HasDerivAt (fun v : ℝ => Real.sqrt (v ^ 2 - a ^ 2))
    (y / Real.sqrt (y ^ 2 - a ^ 2)) y
  convert hsqrt using 1
  field_simp [ne_of_gt (Real.sqrt_pos.2 harg)]

theorem xiMassRadialJacobian_pos {a y : ℝ} (ha : 0 < a) (hy : a < y) :
    0 < xiMassRadialJacobian a y := by
  rw [xiMassRadialJacobian]
  exact div_pos (lt_trans ha hy) (xiMassRadialInverse_pos ha hy)

private theorem integral_eq_integral_Ioi_add_reflect_radial
    {f : ℝ → ℂ} (hf : Integrable f) :
    (∫ x : ℝ, f x) = ∫ x : ℝ in Ioi 0, (f x + f (-x)) := by
  have hsplit := integral_add_compl (s := Ioi (0 : ℝ)) measurableSet_Ioi hf
  simp only [compl_Ioi] at hsplit
  have hneg : (∫ x : ℝ in Iic 0, f x) = ∫ x : ℝ in Ioi 0, f (-x) := by
    simpa only [neg_zero] using (integral_comp_neg_Ioi 0 f).symm
  rw [← hsplit, hneg, ← integral_add hf.integrableOn hf.comp_neg.integrableOn]

theorem integrable_xiMassRadialPushforwardDensity
    {a : ℝ} (ha : 0 < a) {f : ℝ → ℂ} (hf : Integrable f) :
    Integrable (xiMassRadialPushforwardDensity a f) := by
  let G : ℝ → ℂ := fun x => f x + f (-x)
  have hG : IntegrableOn G (Ioi 0) :=
    (hf.add hf.comp_neg).integrableOn
  have hderiv : ∀ y ∈ Ioi a,
      HasDerivWithinAt (xiMassRadialInverse a) (xiMassRadialJacobian a y) (Ioi a) y := by
    intro y hy
    exact (hasDerivAt_xiMassRadialInverse ha hy).hasDerivWithinAt
  have hiff := MeasureTheory.integrableOn_image_iff_integrableOn_abs_deriv_smul
    measurableSet_Ioi hderiv (injOn_xiMassRadialInverse_Ioi ha) G
  rw [image_xiMassRadialInverse_Ioi ha] at hiff
  have hpush : IntegrableOn
      (fun y => xiMassRadialJacobian a y •
        (f (xiMassRadialInverse a y) + f (-xiMassRadialInverse a y))) (Ioi a) := by
    have hraw := hiff.mp hG
    refine hraw.congr_fun ?_ measurableSet_Ioi
    intro y hy
    change |xiMassRadialJacobian a y| •
        (f (xiMassRadialInverse a y) + f (-xiMassRadialInverse a y)) = _
    rw [abs_of_pos (xiMassRadialJacobian_pos ha hy)]
  exact hpush.integrable_indicator measurableSet_Ioi

theorem integral_exp_radialFrequency_mul_eq_pushforward
    {a : ℝ} (ha : 0 < a) {f : ℝ → ℂ} (hf : Integrable f) (u : ℝ) :
    (∫ x : ℝ,
      Complex.exp (-(I * (u : ℂ) * (xiMassRadialFrequency a x : ℂ))) * f x) =
      ∫ y : ℝ,
        Complex.exp (-(I * (u : ℂ) * (y : ℂ))) *
          xiMassRadialPushforwardDensity a f y := by
  let P : ℝ → ℂ := fun x =>
    Complex.exp (-(I * (u : ℂ) * (xiMassRadialFrequency a x : ℂ))) * f x
  have hP : Integrable P := by
    apply hf.bdd_mul (c := 1)
    · exact ((continuous_const.mul continuous_const).mul
        (Complex.continuous_ofReal.comp
          (continuous_xiMassRadialFrequency a))).neg.cexp.aestronglyMeasurable
    · filter_upwards with x
      rw [Complex.norm_exp]
      simp [Complex.mul_re]
  rw [show (∫ x : ℝ,
      Complex.exp (-(I * (u : ℂ) * (xiMassRadialFrequency a x : ℂ))) * f x) =
      ∫ x : ℝ, P x by rfl,
    integral_eq_integral_Ioi_add_reflect_radial hP]
  have hfreq_neg : ∀ x : ℝ,
      xiMassRadialFrequency a (-x) = xiMassRadialFrequency a x := by
    intro x
    unfold xiMassRadialFrequency
    congr 1
    ring
  have hpositive :
      (∫ x : ℝ in Ioi 0, (P x + P (-x))) =
        ∫ y : ℝ in Ioi a,
          Complex.exp (-(I * (u : ℂ) * (y : ℂ))) *
            (xiMassRadialJacobian a y •
              (f (xiMassRadialInverse a y) + f (-xiMassRadialInverse a y))) := by
    let G : ℝ → ℂ := fun x => P x + P (-x)
    have hderiv : ∀ y ∈ Ioi a,
        HasDerivWithinAt (xiMassRadialInverse a) (xiMassRadialJacobian a y) (Ioi a) y := by
      intro y hy
      exact (hasDerivAt_xiMassRadialInverse ha hy).hasDerivWithinAt
    have hchange := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
      measurableSet_Ioi hderiv (injOn_xiMassRadialInverse_Ioi ha) G
    rw [image_xiMassRadialInverse_Ioi ha] at hchange
    rw [hchange]
    apply integral_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with y hy
    rw [abs_of_pos (xiMassRadialJacobian_pos ha hy)]
    dsimp only [G, P]
    rw [xiMassRadialFrequency_inverse ha hy, hfreq_neg,
      xiMassRadialFrequency_inverse ha hy]
    simp only [Complex.real_smul]
    ring
  rw [hpositive]
  rw [← MeasureTheory.integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  filter_upwards with y
  by_cases hy : y ∈ Ioi a
  · simp only [xiMassRadialPushforwardDensity, indicator_of_mem hy]
  · simp only [xiMassRadialPushforwardDensity, Set.indicator_of_notMem hy, mul_zero]

/-- Every integrable positive-mass shell packet decays along future vertical time. -/
theorem tendsto_integral_exp_radialFrequency_mul_atTop_zero
    {a : ℝ} (ha : 0 < a) {f : ℝ → ℂ} (hf : Integrable f) :
    Tendsto (fun u : ℝ => ∫ x : ℝ,
      Complex.exp (-(I * (u : ℂ) * (xiMassRadialFrequency a x : ℂ))) * f x)
      atTop (𝓝 0) := by
  let F : ℝ → ℂ := xiMassRadialPushforwardDensity a f
  have hRL := Real.tendsto_integral_exp_smul_cocompact (f := F)
  have hscale : Tendsto (fun u : ℝ => u / (2 * Real.pi)) atTop atTop := by
    simp only [div_eq_mul_inv]
    exact tendsto_id.atTop_mul_const
      (show (0 : ℝ) < (2 * Real.pi)⁻¹ by positivity)
  have hco : Tendsto (fun u : ℝ => u / (2 * Real.pi)) atTop (cocompact ℝ) :=
    hscale.mono_right (le_trans le_sup_right
      (le_of_eq cocompact_eq_atBot_atTop.symm))
  have hcomp := hRL.comp hco
  refine hcomp.congr fun u => ?_
  rw [integral_exp_radialFrequency_mul_eq_pushforward ha hf]
  apply integral_congr_ae
  filter_upwards with y
  show (Real.fourierChar (-(y * (u / (2 * Real.pi)))) : Circle) • F y =
    Complex.exp (-(I * (u : ℂ) * (y : ℂ))) * F y
  rw [Circle.smul_def, smul_eq_mul, Real.fourierChar_apply]
  congr 2
  push_cast
  field_simp [Real.pi_ne_zero]

/-- The fixed-frequency Xi mass Fourier base is integrable. -/
theorem integrable_xiMassRadialFourierBase
    {a σ : ℝ} (hσ : 0 < σ) (h : ℝ) :
    Integrable (fun x : ℝ =>
      Complex.exp ((-(σ * xiMassRadialFrequency a x) : ℝ)) *
        Complex.exp (-(I * (h : ℂ) * (x : ℂ)))) := by
  apply Integrable.mono' (integrable_exp_neg_mul_abs hσ)
  · have hfirst : Continuous (fun x : ℝ =>
        ((-(σ * xiMassRadialFrequency a x) : ℝ) : ℂ)) := by
      fun_prop
    have hsecond : Continuous (fun x : ℝ =>
        -(I * (h : ℂ) * (x : ℂ))) := by
      fun_prop
    exact ((Complex.continuous_exp.comp hfirst).mul
      (Complex.continuous_exp.comp hsecond)).aestronglyMeasurable
  · filter_upwards with x
    rw [norm_mul, Complex.norm_exp, Complex.norm_exp]
    have hspatial : (-(I * (h : ℂ) * (x : ℂ))).re = 0 := by
      simp [Complex.mul_re]
    rw [hspatial, Real.exp_zero, mul_one]
    simp only [Complex.ofReal_re]
    apply Real.exp_le_exp.mpr
    have hx := abs_le_xiMassRadialFrequency (a := a) x
    nlinarith

/-- Fixed real spatial frequency does not obstruct future vertical-time extinction. -/
theorem tendsto_stripFourier_xiMassAnalyticTest_vertical_atTop_zero
    {a σ : ℝ} (ha : 0 < a) (hσ : 0 < σ) (h : ℝ) :
    Tendsto (fun u : ℝ =>
      stripFourier (xiMassAnalyticTest a ((σ : ℂ) + u * I)) (h : ℂ))
      atTop (𝓝 0) := by
  let f : ℝ → ℂ := fun x =>
    Complex.exp ((-(σ * xiMassRadialFrequency a x) : ℝ)) *
      Complex.exp (-(I * (h : ℂ) * (x : ℂ)))
  have hf : Integrable f := integrable_xiMassRadialFourierBase hσ h
  have hradial := tendsto_integral_exp_radialFrequency_mul_atTop_zero ha hf
  refine hradial.congr fun u => ?_
  rw [stripFourier]
  apply integral_congr_ae
  filter_upwards with x
  rw [xiMassAnalyticTest_ofReal_eq_radial_time ha]
  dsimp only [f]
  rw [show ((-(σ * xiMassRadialFrequency a x) : ℝ) : ℂ) =
      -((σ * xiMassRadialFrequency a x : ℝ) : ℂ) by push_cast; rfl]
  ring

/-- Every fixed centered von-Mangoldt atom becomes extinct in future vertical time. -/
theorem tendsto_xiMassCenteredPrimeAtom_vertical_atTop_zero
    {a σ : ℝ} (ha : 0 < a) (hσ : 0 < σ) (n : ℕ) :
    Tendsto (fun u : ℝ =>
      xiMassCenteredPrimeAtom a ((σ : ℂ) + u * I) n) atTop (𝓝 0) := by
  unfold xiMassCenteredPrimeAtom
  simpa only [mul_zero] using
    (tendsto_stripFourier_xiMassAnalyticTest_vertical_atTop_zero
      ha hσ (Real.log n)).const_mul
        (LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ))
          (1 / 2 : ℂ) n)

end

end RHTower
