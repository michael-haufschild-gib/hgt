import GaloisForLFunctions.RHTower.XiCTaylorThetaTailFiniteTranslationBounds
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailFiniteTranslationDefectCurrent

/-!
# Signed finite translation-packet bounds

The crossed arithmetic channel uses the positive finite phase at a negative displacement.  These
estimates retain that signed polynomial packet and use the absolute displacement only in its
norm majorant.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial

namespace RHTower

noncomputable section

theorem norm_eval_finitePositivePhaseTranslationPacket_le_abs_exp_norm
    (d R : ℕ) (x a : ℝ) (z : ℂ)
    (hx : 0 ≤ x) (hz : ‖z‖ ≤ R) :
    ‖(finitePositivePhaseTranslationPacket d x a).eval z‖ ≤
      Real.exp ((R : ℝ) * (x + |a|)) := by
  have hxphase := norm_eval_finitePositivePhasePolynomial_le_exp_norm d x z
  have haphase := norm_eval_finitePositivePhasePolynomial_le_exp_norm d a z
  have hxnorm : ‖(x : ℂ) * I * z‖ ≤ (R : ℝ) * x := by
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_I, mul_one,
      abs_of_nonneg hx]
    nlinarith [mul_le_mul_of_nonneg_left hz hx]
  have hanorm : ‖(a : ℂ) * I * z‖ ≤ (R : ℝ) * |a| := by
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_I, mul_one]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hz (abs_nonneg a)
  unfold finitePositivePhaseTranslationPacket
  rw [eval_mul, norm_mul]
  calc
    _ ≤ Real.exp ‖(x : ℂ) * I * z‖ * Real.exp ‖(a : ℂ) * I * z‖ :=
      mul_le_mul hxphase haphase (norm_nonneg _) (Real.exp_pos _).le
    _ ≤ Real.exp ((R : ℝ) * x) * Real.exp ((R : ℝ) * |a|) := by gcongr
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem norm_eval_derivative_finitePositivePhaseTranslationPacket_le_abs_exp_norm
    (d R : ℕ) (x a : ℝ) (z : ℂ)
    (hx : 0 ≤ x) (hz : ‖z‖ ≤ R) :
    ‖(finitePositivePhaseTranslationPacket d x a).derivative.eval z‖ ≤
      (x + |a|) * Real.exp ((R : ℝ) * (x + |a|)) := by
  have hxv := norm_eval_finitePositivePhasePolynomial_le_exp_norm d x z
  have hav := norm_eval_finitePositivePhasePolynomial_le_exp_norm d a z
  have hxd := norm_eval_derivative_finitePositivePhasePolynomial_le_exp_norm d x z
  have had := norm_eval_derivative_finitePositivePhasePolynomial_le_exp_norm d a z
  have hxnorm : ‖(x : ℂ) * I * z‖ ≤ (R : ℝ) * x := by
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_I, mul_one,
      abs_of_nonneg hx]
    nlinarith [mul_le_mul_of_nonneg_left hz hx]
  have hanorm : ‖(a : ℂ) * I * z‖ ≤ (R : ℝ) * |a| := by
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_I, mul_one]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hz (abs_nonneg a)
  have hxd' : ‖(finitePositivePhasePolynomial d x).derivative.eval z‖ ≤
      x * Real.exp ((R : ℝ) * x) := by
    calc
      _ ≤ ‖(x : ℂ) * I‖ * Real.exp ‖(x : ℂ) * I * z‖ := hxd
      _ = x * Real.exp ‖(x : ℂ) * I * z‖ := by
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_I, mul_one,
          abs_of_nonneg hx]
      _ ≤ x * Real.exp ((R : ℝ) * x) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hxnorm) hx
  have had' : ‖(finitePositivePhasePolynomial d a).derivative.eval z‖ ≤
      |a| * Real.exp ((R : ℝ) * |a|) := by
    calc
      _ ≤ ‖(a : ℂ) * I‖ * Real.exp ‖(a : ℂ) * I * z‖ := had
      _ = |a| * Real.exp ‖(a : ℂ) * I * z‖ := by
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_I, mul_one]
      _ ≤ |a| * Real.exp ((R : ℝ) * |a|) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hanorm) (abs_nonneg a)
  have hxv' : ‖(finitePositivePhasePolynomial d x).eval z‖ ≤
      Real.exp ((R : ℝ) * x) := hxv.trans (Real.exp_le_exp.mpr hxnorm)
  have hav' : ‖(finitePositivePhasePolynomial d a).eval z‖ ≤
      Real.exp ((R : ℝ) * |a|) := hav.trans (Real.exp_le_exp.mpr hanorm)
  unfold finitePositivePhaseTranslationPacket
  rw [derivative_mul, eval_add, eval_mul, eval_mul]
  calc
    _ ≤ ‖(finitePositivePhasePolynomial d x).derivative.eval z *
          (finitePositivePhasePolynomial d a).eval z‖ +
        ‖(finitePositivePhasePolynomial d x).eval z *
          (finitePositivePhasePolynomial d a).derivative.eval z‖ := norm_add_le _ _
    _ = ‖(finitePositivePhasePolynomial d x).derivative.eval z‖ *
          ‖(finitePositivePhasePolynomial d a).eval z‖ +
        ‖(finitePositivePhasePolynomial d x).eval z‖ *
          ‖(finitePositivePhasePolynomial d a).derivative.eval z‖ := by rw [norm_mul, norm_mul]
    _ ≤ (x * Real.exp ((R : ℝ) * x)) * Real.exp ((R : ℝ) * |a|) +
        Real.exp ((R : ℝ) * x) * (|a| * Real.exp ((R : ℝ) * |a|)) := by gcongr
    _ = _ := by
      have hexp : Real.exp ((R : ℝ) * x) * Real.exp ((R : ℝ) * |a|) =
          Real.exp ((R : ℝ) * (x + |a|)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [show x * Real.exp ((R : ℝ) * x) * Real.exp ((R : ℝ) * |a|) =
          x * (Real.exp ((R : ℝ) * x) * Real.exp ((R : ℝ) * |a|)) by ring,
        show Real.exp ((R : ℝ) * x) * (|a| * Real.exp ((R : ℝ) * |a|)) =
          |a| * (Real.exp ((R : ℝ) * x) * Real.exp ((R : ℝ) * |a|)) by ring,
        hexp]
      ring

/-- The signed complete finite phase packet has the same integrated exponential envelope as the
nonnegative channel, with `|a|` replacing `a`. -/
theorem thetaCuspTailPhaseTranslationPacketIntegratedNorm_le_abs
    (d R : ℕ) (hR : 1 ≤ R) (a : ℝ) (z : ℂ) (hz : ‖z‖ ≤ R) :
    thetaCuspTailPhaseTranslationPacketIntegratedNorm d z a ≤
      4 * thetaCuspTailDerivativeNatExpConstant 2 (1 + R) *
        ((R : ℝ) + 1) * Real.exp (((1 + R : ℕ) : ℝ) * |a|) := by
  let f0 : ℝ → ℝ := fun x =>
    |thetaCuspTailDerivative 2 x| *
      ((((R : ℝ) * (x + |a|)) ^ (0 : ℕ) / ((0 : ℕ).factorial : ℕ)) *
        Real.exp ((R : ℝ) * (x + |a|)))
  let f1 : ℝ → ℝ := fun x =>
    |thetaCuspTailDerivative 2 x| *
      ((((R : ℝ) * (x + |a|)) ^ (1 : ℕ) / ((1 : ℕ).factorial : ℕ)) *
        Real.exp ((R : ℝ) * (x + |a|)))
  have ha : 0 ≤ |a| := abs_nonneg a
  have hf0int : IntegrableOn f0 (Ioi 0) := by
    simpa only [f0] using
      integrableOn_abs_thetaCuspTailDerivative_mul_shiftedFactorialEnvelope
        2 0 1 R (by omega) ha
  have hf1int : IntegrableOn f1 (Ioi 0) := by
    simpa only [f1] using
      integrableOn_abs_thetaCuspTailDerivative_mul_shiftedFactorialEnvelope
        2 1 1 R (by omega) ha
  have hVmeas : AEStronglyMeasurable (fun x : ℝ =>
      |thetaCuspTailSecondDensity x| * ‖(finitePositivePhaseTranslationPacket d x a).eval z‖)
      (volume.restrict (Ioi 0)) :=
    (continuous_abs_thetaCuspTailSecondDensity.mul
      (continuous_eval_finitePositivePhaseTranslationPacket d z a).norm).aestronglyMeasurable.restrict
  have hDmeas : AEStronglyMeasurable (fun x : ℝ =>
      |thetaCuspTailSecondDensity x| *
        ‖(finitePositivePhaseTranslationPacket d x a).derivative.eval z‖)
      (volume.restrict (Ioi 0)) :=
    (continuous_abs_thetaCuspTailSecondDensity.mul
      (continuous_eval_derivative_finitePositivePhaseTranslationPacket d z a).norm).aestronglyMeasurable.restrict
  have hVpoint (x : ℝ) (hx : 0 ≤ x) :
      |thetaCuspTailSecondDensity x| * ‖(finitePositivePhaseTranslationPacket d x a).eval z‖ ≤
        4 * f0 x := by
    have hp := norm_eval_finitePositivePhaseTranslationPacket_le_abs_exp_norm d R x a z hx hz
    dsimp only [f0]
    unfold thetaCuspTailSecondDensity
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num only [Nat.factorial_zero, Nat.cast_one, div_one, pow_zero, one_mul]
    calc
      4 * |thetaCuspTailDerivative 2 x| * ‖eval z (finitePositivePhaseTranslationPacket d x a)‖ ≤
          4 * |thetaCuspTailDerivative 2 x| *
            Real.exp ((R : ℝ) * (x + |a|)) :=
        mul_le_mul_of_nonneg_left hp (mul_nonneg (by norm_num) (abs_nonneg _))
      _ = 4 * (|thetaCuspTailDerivative 2 x| *
            Real.exp ((R : ℝ) * (x + |a|))) := by ring
  have hDpoint (x : ℝ) (hx : 0 ≤ x) :
      |thetaCuspTailSecondDensity x| *
          ‖(finitePositivePhaseTranslationPacket d x a).derivative.eval z‖ ≤ 4 * f1 x := by
    have hp :=
      norm_eval_derivative_finitePositivePhaseTranslationPacket_le_abs_exp_norm d R x a z hx hz
    have hxa : 0 ≤ x + |a| := add_nonneg hx ha
    have hscale : (x + |a|) * Real.exp ((R : ℝ) * (x + |a|)) ≤
        (R : ℝ) * (x + |a|) * Real.exp ((R : ℝ) * (x + |a|)) := by
      have hRreal : (1 : ℝ) ≤ R := by exact_mod_cast hR
      have hxaScale : x + |a| ≤ (R : ℝ) * (x + |a|) := by nlinarith
      exact mul_le_mul_of_nonneg_right hxaScale (Real.exp_pos _).le
    dsimp only [f1]
    unfold thetaCuspTailSecondDensity
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num only [Nat.factorial_one, Nat.cast_one, div_one, pow_one]
    have hp' := hp.trans hscale
    calc
      4 * |thetaCuspTailDerivative 2 x| *
          ‖eval z (derivative (finitePositivePhaseTranslationPacket d x a))‖ ≤
          4 * |thetaCuspTailDerivative 2 x| *
            ((R : ℝ) * (x + |a|) * Real.exp ((R : ℝ) * (x + |a|))) :=
        mul_le_mul_of_nonneg_left hp' (mul_nonneg (by norm_num) (abs_nonneg _))
      _ = 4 * (|thetaCuspTailDerivative 2 x| *
            ((R : ℝ) * (x + |a|) * Real.exp ((R : ℝ) * (x + |a|)))) := by ring
  have hVint : IntegrableOn (fun x : ℝ =>
      |thetaCuspTailSecondDensity x| * ‖(finitePositivePhaseTranslationPacket d x a).eval z‖)
      (Ioi 0) := by
    apply (hf0int.const_mul 4).mono' hVmeas
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hnon : 0 ≤ |thetaCuspTailSecondDensity x| *
        ‖(finitePositivePhaseTranslationPacket d x a).eval z‖ := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hnon]
    exact hVpoint x hx.le
  have hDint : IntegrableOn (fun x : ℝ =>
      |thetaCuspTailSecondDensity x| *
        ‖(finitePositivePhaseTranslationPacket d x a).derivative.eval z‖) (Ioi 0) := by
    apply (hf1int.const_mul 4).mono' hDmeas
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hnon : 0 ≤ |thetaCuspTailSecondDensity x| *
        ‖(finitePositivePhaseTranslationPacket d x a).derivative.eval z‖ := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hnon]
    exact hDpoint x hx.le
  have hV : (∫ x : ℝ in Ioi 0,
      |thetaCuspTailSecondDensity x| * ‖(finitePositivePhaseTranslationPacket d x a).eval z‖) ≤
      4 * thetaCuspTailDerivativeNatExpConstant 2 (1 + R) *
        Real.exp (((1 + R : ℕ) : ℝ) * |a|) := by
    calc
      _ ≤ ∫ x : ℝ in Ioi 0, 4 * f0 x := by
        apply MeasureTheory.integral_mono_ae hVint (hf0int.const_mul 4)
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        exact hVpoint x hx.le
      _ = 4 * ∫ x : ℝ in Ioi 0, f0 x := by rw [integral_const_mul]
      _ ≤ 4 * (thetaCuspTailDerivativeNatExpConstant 2 (1 + R) *
          Real.exp (((1 + R : ℕ) : ℝ) * |a|)) := by
        gcongr
        simpa only [f0, Nat.factorial_zero, Nat.cast_one, div_one, pow_zero,
          one_mul, one_pow, mul_one] using
          integral_abs_thetaCuspTailDerivative_mul_shiftedFactorialEnvelope_le
            2 0 1 R (by omega) ha
      _ = _ := by ring
  have hD : (∫ x : ℝ in Ioi 0,
      |thetaCuspTailSecondDensity x| *
        ‖(finitePositivePhaseTranslationPacket d x a).derivative.eval z‖) ≤
      4 * thetaCuspTailDerivativeNatExpConstant 2 (1 + R) * (R : ℝ) *
        Real.exp (((1 + R : ℕ) : ℝ) * |a|) := by
    calc
      _ ≤ ∫ x : ℝ in Ioi 0, 4 * f1 x := by
        apply MeasureTheory.integral_mono_ae hDint (hf1int.const_mul 4)
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        exact hDpoint x hx.le
      _ = 4 * ∫ x : ℝ in Ioi 0, f1 x := by rw [integral_const_mul]
      _ ≤ 4 * (thetaCuspTailDerivativeNatExpConstant 2 (1 + R) * (R : ℝ) *
          Real.exp (((1 + R : ℕ) : ℝ) * |a|)) := by
        gcongr
        simpa only [f1, Nat.factorial_one, Nat.cast_one, div_one, pow_one,
          one_pow] using
          integral_abs_thetaCuspTailDerivative_mul_shiftedFactorialEnvelope_le
            2 1 1 R (by omega) ha
      _ = _ := by ring
  unfold thetaCuspTailPhaseTranslationPacketIntegratedNorm
  calc
    _ ≤ 4 * thetaCuspTailDerivativeNatExpConstant 2 (1 + R) *
          Real.exp (((1 + R : ℕ) : ℝ) * |a|) +
        4 * thetaCuspTailDerivativeNatExpConstant 2 (1 + R) * (R : ℝ) *
          Real.exp (((1 + R : ℕ) : ℝ) * |a|) := add_le_add hV hD
    _ = _ := by ring

end

end RHTower
