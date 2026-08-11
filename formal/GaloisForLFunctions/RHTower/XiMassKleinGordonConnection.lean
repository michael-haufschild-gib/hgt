import GaloisForLFunctions.RHTower.XiMassCriticalPrimeTailGreenStokes
import GaloisForLFunctions.HTGeometry.KleinGordonSynthesis

/-!
# Klein--Gordon law of the Xi mass connection kernel

The vertical mass time `u` and prime-log frequency `h` are not independent parameters.  The real
mass shell `r(x)=sqrt(x^2+a^2)` gives `r^2-x^2=a^2`, so the mass Fourier profile satisfies the
massive Klein--Gordon equation

`partial_u^2 F - partial_h^2 F + a^2 F = 0`.

All derivatives below are actual Bochner-integral derivatives.  This identifies the higher
two-direction connection law behind the timelike/glancing Route T obstruction; it is not an
asymptotic or formal-symbol computation.
-/

open Complex Filter MeasureTheory Set Topology

namespace RHTower

noncomputable section

/-- Positive radial mass-shell frequency. -/
def xiMassRadialFrequency (a x : ℝ) : ℝ :=
  Real.sqrt (x ^ 2 + a ^ 2)

@[fun_prop]
theorem continuous_xiMassRadialFrequency (a : ℝ) :
    Continuous (xiMassRadialFrequency a) := by
  unfold xiMassRadialFrequency
  fun_prop

theorem continuous_xiMassAnalyticTest_real
    {a : ℝ} (ha : 0 < a) (τ : ℂ) :
    Continuous (fun x : ℝ => xiMassAnalyticTest a τ (x : ℂ)) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hmem : (x : ℂ) ∈ xiMassStrip a := by
    change |((x : ℂ)).im| < a
    simpa using ha
  exact (hasDerivAt_xiMassAnalyticTest ha τ hmem).continuousAt.comp
    Complex.continuous_ofReal.continuousAt

theorem xiMassRadialFrequency_pos {a : ℝ} (ha : 0 < a) (x : ℝ) :
    0 < xiMassRadialFrequency a x := by
  rw [xiMassRadialFrequency, Real.sqrt_pos]
  nlinarith [sq_pos_of_pos ha]

theorem xiMassRadialFrequency_sq {a : ℝ} (_ha : 0 < a) (x : ℝ) :
    xiMassRadialFrequency a x ^ 2 = x ^ 2 + a ^ 2 := by
  rw [xiMassRadialFrequency, Real.sq_sqrt]
  positivity

theorem abs_le_xiMassRadialFrequency {a : ℝ} (x : ℝ) :
    |x| ≤ xiMassRadialFrequency a x := by
  have hsq : x ^ 2 ≤ x ^ 2 + a ^ 2 := by nlinarith [sq_nonneg a]
  rw [xiMassRadialFrequency]
  have h := Real.sqrt_le_sqrt hsq
  simpa [Real.sqrt_sq_eq_abs] using h

theorem xiMassRadialFrequency_le_abs_add
    {a : ℝ} (ha : 0 ≤ a) (x : ℝ) :
    xiMassRadialFrequency a x ≤ |x| + a := by
  have hleft : 0 ≤ xiMassRadialFrequency a x := Real.sqrt_nonneg _
  have hright : 0 ≤ |x| + a := add_nonneg (abs_nonneg _) ha
  have hsquare : xiMassRadialFrequency a x ^ 2 ≤ (|x| + a) ^ 2 := by
    rw [xiMassRadialFrequency, Real.sq_sqrt (by positivity)]
    have hxSq : |x| ^ 2 = x ^ 2 := sq_abs x
    nlinarith [mul_nonneg (abs_nonneg x) ha]
  nlinarith [sq_nonneg (xiMassRadialFrequency a x + (|x| + a))]

/-- Every polynomial radial moment remains integrable against fixed positive mass damping. -/
theorem integrable_xiMassRadialMoment
    {a σ : ℝ} (ha : 0 < a) (hσ : 0 < σ) (k : ℕ) :
    Integrable (fun x : ℝ =>
      xiMassRadialFrequency a x ^ k *
        Real.exp (-(σ * xiMassRadialFrequency a x))) := by
  let C : ℝ := xiMassShiftedMomentConstant σ a k
  have hmajor : Integrable (fun x : ℝ => C * Real.exp (-(σ / 2 * |x|))) :=
    (integrable_exp_neg_mul_abs (by positivity : 0 < σ / 2)).const_mul C
  apply hmajor.mono'
  · exact (((continuous_xiMassRadialFrequency a).pow k).mul
      (Real.continuous_exp.comp
        (continuous_const.mul (continuous_xiMassRadialFrequency a)).neg)).aestronglyMeasurable
  · filter_upwards with x
    have hr0 : 0 ≤ xiMassRadialFrequency a x := Real.sqrt_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg hr0 _)
      (Real.exp_nonneg _))]
    have hrle := xiMassRadialFrequency_le_abs_add ha.le x
    have hxle := abs_le_xiMassRadialFrequency (a := a) x
    have hpow : xiMassRadialFrequency a x ^ k ≤ (|x| + a) ^ k :=
      pow_le_pow_left₀ (Real.sqrt_nonneg _) hrle k
    have hexp : Real.exp (-(σ * xiMassRadialFrequency a x)) ≤
        Real.exp (-(σ * |x|)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    calc
      xiMassRadialFrequency a x ^ k *
          Real.exp (-(σ * xiMassRadialFrequency a x)) ≤
        (|x| + a) ^ k * Real.exp (-(σ * |x|)) :=
          mul_le_mul hpow hexp (Real.exp_nonneg _) (by positivity)
      _ ≤ C * Real.exp (-(σ / 2 * |x|)) := by
        simpa only [C] using shifted_moment_absorption hσ ha.le k x

/-- `k`th vertical-time moment of the Xi mass profile. -/
def xiMassTemporalCrossMoment
    (a σ u : ℝ) (k : ℕ) (h : ℝ) : ℂ :=
  ∫ x : ℝ,
    ((-(I * (xiMassRadialFrequency a x : ℂ))) ^ k *
      Complex.exp (-(I * (u : ℂ) * (xiMassRadialFrequency a x : ℂ)))) *
      (Complex.exp (-(σ * xiMassRadialFrequency a x : ℝ)) *
        Complex.exp (-(I * (h : ℂ) * (x : ℂ))))

theorem xiMassAnalyticTest_ofReal_eq_radial_time
    {a : ℝ} (ha : 0 < a) (σ u x : ℝ) :
    xiMassAnalyticTest a ((σ : ℂ) + u * I) (x : ℂ) =
      Complex.exp (-(σ * xiMassRadialFrequency a x : ℝ)) *
        Complex.exp (-(I * (u : ℂ) * (xiMassRadialFrequency a x : ℂ))) := by
  rw [xiMassAnalyticTest, xiMassAnalyticSqrt_ofReal_eq ha]
  have hr : Real.sqrt (x ^ 2 + a ^ 2) = xiMassRadialFrequency a x := rfl
  rw [hr]
  rw [show (-((σ : ℂ) + (u : ℂ) * I)) *
      (xiMassRadialFrequency a x : ℂ) =
      (-(σ * xiMassRadialFrequency a x : ℝ) : ℂ) +
        (-(I * (u : ℂ) * (xiMassRadialFrequency a x : ℂ))) by
    push_cast
    ring, Complex.exp_add]

theorem xiMassTemporalCrossMoment_eq_integral
    {a : ℝ} (ha : 0 < a) (σ u : ℝ) (k : ℕ) (h : ℝ) :
    xiMassTemporalCrossMoment a σ u k h =
      ∫ x : ℝ,
        xiMassAnalyticTest a ((σ : ℂ) + u * I) (x : ℂ) *
          (-(I * (xiMassRadialFrequency a x : ℂ))) ^ k *
          Complex.exp (-(I * (h : ℂ) * (x : ℂ))) := by
  rw [xiMassTemporalCrossMoment]
  apply integral_congr_ae
  filter_upwards with x
  rw [xiMassAnalyticTest_ofReal_eq_radial_time ha]
  ring

@[simp]
theorem xiMassTemporalCrossMoment_zero
    {a : ℝ} (ha : 0 < a) (σ u h : ℝ) :
    xiMassTemporalCrossMoment a σ u 0 h =
      xiMassSpectralCrossMoment a σ u 0 h := by
  rw [xiMassTemporalCrossMoment_eq_integral ha, xiMassSpectralCrossMoment]
  simp

theorem integrable_xiMassTemporalCrossMoment_integrand
    {a σ : ℝ} (ha : 0 < a) (hσ : 0 < σ) (u : ℝ) (k : ℕ) (h : ℝ) :
    Integrable (fun x : ℝ =>
      ((-(I * (xiMassRadialFrequency a x : ℂ))) ^ k *
        Complex.exp (-(I * (u : ℂ) * (xiMassRadialFrequency a x : ℂ)))) *
        (Complex.exp (-(σ * xiMassRadialFrequency a x : ℝ)) *
          Complex.exp (-(I * (h : ℂ) * (x : ℂ))))) := by
  apply (integrable_xiMassRadialMoment ha hσ k).mono'
  · exact (((((continuous_const.mul
      (Complex.continuous_ofReal.comp (continuous_xiMassRadialFrequency a))).neg.pow k).mul
        (Complex.continuous_exp.comp (by fun_prop))).mul
          ((Complex.continuous_exp.comp (by fun_prop)).mul
            (Complex.continuous_exp.comp (by fun_prop)))).aestronglyMeasurable)
  · filter_upwards with x
    simp only [norm_mul, norm_pow, norm_neg, Complex.norm_I, one_mul,
      Complex.norm_real, Complex.norm_exp, Complex.norm_exp, Complex.norm_exp,
      Real.norm_eq_abs]
    have hr0 := (xiMassRadialFrequency_pos ha x).le
    rw [abs_of_nonneg hr0]
    have htime : (-(I * (u : ℂ) * (xiMassRadialFrequency a x : ℂ))).re = 0 := by simp
    have hspace : (-(I * (h : ℂ) * (x : ℂ))).re = 0 := by simp
    simp [htime, hspace]

/-- Vertical-time differentiation stays in the temporal moment tower. -/
theorem hasDerivAt_xiMassTemporalCrossMoment
    {a σ : ℝ} (ha : 0 < a) (hσ : 0 < σ)
    (u : ℝ) (k : ℕ) (h : ℝ) :
    HasDerivAt (fun v : ℝ => xiMassTemporalCrossMoment a σ v k h)
      (xiMassTemporalCrossMoment a σ u (k + 1) h) u := by
  let r : ℝ → ℝ := xiMassRadialFrequency a
  let m : ℝ → ℝ → ℂ := fun v x =>
    (-(I * (r x : ℂ))) ^ k * Complex.exp (-(I * (v : ℂ) * (r x : ℂ)))
  let m' : ℝ → ℝ → ℂ := fun v x =>
    (-(I * (r x : ℂ))) ^ (k + 1) * Complex.exp (-(I * (v : ℂ) * (r x : ℂ)))
  let density : ℝ → ℂ := fun x =>
    Complex.exp (-(σ * r x : ℝ)) * Complex.exp (-(I * (h : ℂ) * (x : ℂ)))
  have hmeas : ∀ v : ℝ, AEStronglyMeasurable (fun x => m v x * density x) := by
    intro v
    dsimp only [m, density, r]
    exact (((((continuous_const.mul
      (Complex.continuous_ofReal.comp (continuous_xiMassRadialFrequency a))).neg.pow k).mul
        (Complex.continuous_exp.comp (by fun_prop))).mul
          ((Complex.continuous_exp.comp (by fun_prop)).mul
            (Complex.continuous_exp.comp (by fun_prop)))).aestronglyMeasurable)
  have hint : Integrable (fun x => m u x * density x) := by
    simpa only [m, density, r] using
      integrable_xiMassTemporalCrossMoment_integrand ha hσ u k h
  have hmeas' : AEStronglyMeasurable (fun x => m' u x * density x) := by
    dsimp only [m', density, r]
    exact (((((continuous_const.mul
      (Complex.continuous_ofReal.comp (continuous_xiMassRadialFrequency a))).neg.pow (k + 1)).mul
        (Complex.continuous_exp.comp (by fun_prop))).mul
          ((Complex.continuous_exp.comp (by fun_prop)).mul
            (Complex.continuous_exp.comp (by fun_prop)))).aestronglyMeasurable)
  have hderiv : ∀ (v x : ℝ), HasDerivAt (fun q : ℝ => m q x) (m' v x) v := by
    intro v x
    dsimp only [m, m', r]
    let c : ℂ := -(I * (xiMassRadialFrequency a x : ℂ))
    have hfun : (fun q : ℝ => -(I * (q : ℂ) * (xiMassRadialFrequency a x : ℂ))) =
        fun q : ℝ => c * (q : ℂ) := by
      funext q
      dsimp only [c]
      ring
    have hlin : HasDerivAt
        (fun q : ℝ => -(I * (q : ℂ) * (xiMassRadialFrequency a x : ℂ)))
        (-(I * (xiMassRadialFrequency a x : ℂ))) v := by
      rw [hfun]
      simpa [c, Complex.ofRealCLM_apply] using
        (Complex.ofRealCLM.hasDerivAt.const_mul c)
    have hexp := hlin.cexp
    apply (hexp.const_mul
      ((-(I * (xiMassRadialFrequency a x : ℂ))) ^ k)).congr_deriv
    rw [pow_succ]
    ring
  have hbound : ∀ (v x : ℝ), ‖m' v x‖ ≤ xiMassRadialFrequency a x ^ (k + 1) := by
    intro v x
    dsimp only [m', r]
    rw [norm_mul, norm_pow, norm_neg, norm_mul, Complex.norm_I, one_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (xiMassRadialFrequency_pos ha x),
      Complex.norm_exp]
    have hphase : (-(I * (v : ℂ) * (xiMassRadialFrequency a x : ℂ))).re = 0 := by simp
    rw [hphase, Real.exp_zero, mul_one]
  have hdensityNorm (x : ℝ) :
      ‖density x‖ = Real.exp (-(σ * xiMassRadialFrequency a x)) := by
    dsimp only [density, r]
    rw [norm_mul, Complex.norm_exp, Complex.norm_exp]
    have hphase : (-(I * (h : ℂ) * (x : ℂ))).re = 0 := by simp
    simp [hphase]
  have hg : Integrable (fun x =>
      xiMassRadialFrequency a x ^ (k + 1) * ‖density x‖) := by
    apply (integrable_xiMassRadialMoment ha hσ (k + 1)).congr
    filter_upwards with x
    rw [hdensityNorm]
  have hmain := GaloisForLFunctions.HTGeometry.hasDerivAt_integral_symbol
    (μ := (volume : Measure ℝ)) (m := m) (m' := m') (h := density)
    (g := fun x => xiMassRadialFrequency a x ^ (k + 1)) u
    hmeas hint hmeas' hderiv hbound hg
  simpa only [xiMassTemporalCrossMoment, m, m', density, r] using hmain

/-- Algebraic mass-shell identity between the second temporal and spatial moments. -/
theorem xiMassTemporal_sub_spatial_second_eq_mass
    {a σ : ℝ} (ha : 0 < a) (hσ : 0 < σ) (u h : ℝ) :
    xiMassTemporalCrossMoment a σ u 2 h -
        xiMassSpectralCrossMoment a σ u 2 h =
      -(a : ℂ) ^ 2 * xiMassSpectralCrossMoment a σ u 0 h := by
  have htime := integrable_xiMassTemporalCrossMoment_integrand ha hσ u 2 h
  have hspace : Integrable (fun x : ℝ =>
      xiMassAnalyticTest a ((σ : ℂ) + u * I) x * (-(I * (x : ℂ))) ^ 2 *
        Complex.exp (-(I * (h : ℂ) * x))) := by
    apply ((integrable_exp_neg_mul_abs (show 0 < σ / 2 by positivity)).const_mul
      ((2 / σ) ^ 2 * (Nat.factorial 2 : ℝ))).mono'
    · exact (((continuous_xiMassAnalyticTest_real ha
          ((σ : ℂ) + u * I)).mul (by fun_prop)).mul (by fun_prop)).aestronglyMeasurable
    · filter_upwards with x
      have hphase : (-(I * (h : ℂ) * (x : ℂ))).re = 0 := by simp
      rw [norm_mul, Complex.norm_exp, hphase, Real.exp_zero, mul_one]
      simpa only [norm_mul] using
        norm_xiMassSpectralCrossMomentAmplitude_le ha hσ u 2 x
  have htime' : Integrable (fun x : ℝ =>
      xiMassAnalyticTest a ((σ : ℂ) + u * I) x *
        (-(I * (xiMassRadialFrequency a x : ℂ))) ^ 2 *
          Complex.exp (-(I * (h : ℂ) * x))) := by
    apply htime.congr
    filter_upwards with x
    rw [xiMassAnalyticTest_ofReal_eq_radial_time ha]
    ring
  rw [xiMassTemporalCrossMoment_eq_integral ha]
  simp only [xiMassSpectralCrossMoment]
  rw [← integral_sub htime' hspace]
  calc
    (∫ x : ℝ,
        xiMassAnalyticTest a ((σ : ℂ) + u * I) x *
              (-(I * (xiMassRadialFrequency a x : ℂ))) ^ 2 *
              Complex.exp (-(I * (h : ℂ) * x)) -
            xiMassAnalyticTest a ((σ : ℂ) + u * I) x *
              (-(I * (x : ℂ))) ^ 2 *
              Complex.exp (-(I * (h : ℂ) * x))) =
        ∫ x : ℝ, (-(a : ℂ) ^ 2) *
          (xiMassAnalyticTest a ((σ : ℂ) + u * I) x *
            Complex.exp (-(I * (h : ℂ) * x))) := by
      apply integral_congr_ae
      filter_upwards with x
      have hrSq := xiMassRadialFrequency_sq ha x
      have hrSqC : (xiMassRadialFrequency a x : ℂ) ^ 2 =
          (x : ℂ) ^ 2 + (a : ℂ) ^ 2 := by
        exact_mod_cast hrSq
      rw [show (-(I * (xiMassRadialFrequency a x : ℂ))) ^ 2 =
          -((xiMassRadialFrequency a x : ℂ) ^ 2) by
            rw [neg_sq, mul_pow, Complex.I_sq]
            ring,
        show (-(I * (x : ℂ))) ^ 2 = -((x : ℂ) ^ 2) by
            rw [neg_sq, mul_pow, Complex.I_sq]
            ring,
        hrSqC]
      ring
    _ = -(a : ℂ) ^ 2 *
        ∫ x : ℝ, xiMassAnalyticTest a ((σ : ℂ) + u * I) x *
          Complex.exp (-(I * (h : ℂ) * x)) := by
      rw [integral_const_mul]
    _ = -(a : ℂ) ^ 2 *
        ∫ x : ℝ, xiMassAnalyticTest a ((σ : ℂ) + u * I) x *
          (-(I * (x : ℂ))) ^ 0 * Complex.exp (-(I * (h : ℂ) * x)) := by simp

/-- **Xi mass Klein--Gordon equation.** Vertical mass time and prime-log position form one massive
Lorentz plane. -/
theorem xiMassProfile_kleinGordon
    {a σ : ℝ} (ha : 0 < a) (hσ : 0 < σ) (u h : ℝ) :
    deriv (deriv (fun v : ℝ =>
      xiMassSpectralCrossMoment a σ v 0 h)) u -
        deriv (deriv (xiMassSpectralCrossMoment a σ u 0)) h +
      (a : ℂ) ^ 2 * xiMassSpectralCrossMoment a σ u 0 h = 0 := by
  have htime0 (v : ℝ) :
      deriv (fun q : ℝ => xiMassSpectralCrossMoment a σ q 0 h) v =
        xiMassTemporalCrossMoment a σ v 1 h := by
    rw [show (fun q : ℝ => xiMassSpectralCrossMoment a σ q 0 h) =
        fun q : ℝ => xiMassTemporalCrossMoment a σ q 0 h by
      funext q
      exact (xiMassTemporalCrossMoment_zero ha σ q h).symm]
    exact (hasDerivAt_xiMassTemporalCrossMoment ha hσ v 0 h).deriv
  have htime1 := (hasDerivAt_xiMassTemporalCrossMoment ha hσ u 1 h).deriv
  have hspace0 (y : ℝ) :
      deriv (xiMassSpectralCrossMoment a σ u 0) y =
        xiMassSpectralCrossMoment a σ u 1 y :=
    (hasDerivAt_xiMassSpectralCrossMoment ha hσ u 0 y).deriv
  have hspace1 := (hasDerivAt_xiMassSpectralCrossMoment ha hσ u 1 h).deriv
  rw [show deriv (fun v : ℝ =>
      deriv (fun q : ℝ => xiMassSpectralCrossMoment a σ q 0 h) v) u =
      xiMassTemporalCrossMoment a σ u 2 h by
        rw [show (fun v : ℝ => deriv
          (fun q : ℝ => xiMassSpectralCrossMoment a σ q 0 h) v) =
          fun v : ℝ => xiMassTemporalCrossMoment a σ v 1 h by
            funext v
            exact htime0 v]
        exact htime1,
    show deriv (fun y : ℝ =>
      deriv (xiMassSpectralCrossMoment a σ u 0) y) h =
      xiMassSpectralCrossMoment a σ u 2 h by
        rw [show (fun y : ℝ => deriv
          (xiMassSpectralCrossMoment a σ u 0) y) =
          xiMassSpectralCrossMoment a σ u 1 by
            funext y
            exact hspace0 y]
        exact hspace1]
  linear_combination xiMassTemporal_sub_spatial_second_eq_mass ha hσ u h

end

end RHTower
