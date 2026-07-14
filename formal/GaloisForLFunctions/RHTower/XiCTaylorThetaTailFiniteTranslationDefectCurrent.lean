import GaloisForLFunctions.RHTower.XiCTaylorThetaTailLogarithmicHaarEdge

/-!
# Complete current of the finite theta-tail translation defect

The exact finite phase translation law has one self-current and two mixed packet--edge currents.
This module keeps all three terms together and proves that their density-integrated sum is
super-polynomially small at logarithmic Haar depth.  Reflection transports the result to the
second cosine--sine channel without reflecting the one-sided anisotropic mesh.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial
namespace RHTower
noncomputable section

def finitePositivePhaseTranslationPacket (d : ℕ) (x a : ℝ) : Polynomial ℂ :=
  finitePositivePhasePolynomial d x * finitePositivePhasePolynomial d a

theorem norm_eval_finitePositivePhaseTranslationPacket_le_exp_norm
    (d R : ℕ) (x a : ℝ) (z : ℂ)
    (hx : 0 ≤ x) (ha : 0 ≤ a) (hz : ‖z‖ ≤ R) :
    ‖(finitePositivePhaseTranslationPacket d x a).eval z‖ ≤
      Real.exp ((R : ℝ) * (x + a)) := by
  have hxphase := norm_eval_finitePositivePhasePolynomial_le_exp_norm d x z
  have haphase := norm_eval_finitePositivePhasePolynomial_le_exp_norm d a z
  have hxnorm : ‖(x : ℂ) * I * z‖ ≤ (R : ℝ) * x := by
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_I, mul_one,
      abs_of_nonneg hx]
    nlinarith [mul_le_mul_of_nonneg_left hz hx]
  have hanorm : ‖(a : ℂ) * I * z‖ ≤ (R : ℝ) * a := by
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_I, mul_one,
      abs_of_nonneg ha]
    nlinarith [mul_le_mul_of_nonneg_left hz ha]
  unfold finitePositivePhaseTranslationPacket
  rw [eval_mul, norm_mul]
  calc
    _ ≤ Real.exp ‖(x : ℂ) * I * z‖ * Real.exp ‖(a : ℂ) * I * z‖ :=
      mul_le_mul hxphase haphase (norm_nonneg _) (Real.exp_pos _).le
    _ ≤ Real.exp ((R : ℝ) * x) * Real.exp ((R : ℝ) * a) := by gcongr
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem norm_eval_derivative_finitePositivePhaseTranslationPacket_le_exp_norm
    (d R : ℕ) (x a : ℝ) (z : ℂ)
    (hx : 0 ≤ x) (ha : 0 ≤ a) (hz : ‖z‖ ≤ R) :
    ‖(finitePositivePhaseTranslationPacket d x a).derivative.eval z‖ ≤
      (x + a) * Real.exp ((R : ℝ) * (x + a)) := by
  have hxv := norm_eval_finitePositivePhasePolynomial_le_exp_norm d x z
  have hav := norm_eval_finitePositivePhasePolynomial_le_exp_norm d a z
  have hxd := norm_eval_derivative_finitePositivePhasePolynomial_le_exp_norm d x z
  have had := norm_eval_derivative_finitePositivePhasePolynomial_le_exp_norm d a z
  have hxnorm : ‖(x : ℂ) * I * z‖ ≤ (R : ℝ) * x := by
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_I, mul_one,
      abs_of_nonneg hx]
    nlinarith [mul_le_mul_of_nonneg_left hz hx]
  have hanorm : ‖(a : ℂ) * I * z‖ ≤ (R : ℝ) * a := by
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_I, mul_one,
      abs_of_nonneg ha]
    nlinarith [mul_le_mul_of_nonneg_left hz ha]
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
      a * Real.exp ((R : ℝ) * a) := by
    calc
      _ ≤ ‖(a : ℂ) * I‖ * Real.exp ‖(a : ℂ) * I * z‖ := had
      _ = a * Real.exp ‖(a : ℂ) * I * z‖ := by
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_I, mul_one,
          abs_of_nonneg ha]
      _ ≤ a * Real.exp ((R : ℝ) * a) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hanorm) ha
  have hxv' : ‖(finitePositivePhasePolynomial d x).eval z‖ ≤
      Real.exp ((R : ℝ) * x) := hxv.trans (Real.exp_le_exp.mpr hxnorm)
  have hav' : ‖(finitePositivePhasePolynomial d a).eval z‖ ≤
      Real.exp ((R : ℝ) * a) := hav.trans (Real.exp_le_exp.mpr hanorm)
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
    _ ≤ (x * Real.exp ((R : ℝ) * x)) * Real.exp ((R : ℝ) * a) +
        Real.exp ((R : ℝ) * x) * (a * Real.exp ((R : ℝ) * a)) := by gcongr
    _ = _ := by
      have hexp : Real.exp ((R : ℝ) * x) * Real.exp ((R : ℝ) * a) =
          Real.exp ((R : ℝ) * (x + a)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [show x * Real.exp ((R : ℝ) * x) * Real.exp ((R : ℝ) * a) =
          x * (Real.exp ((R : ℝ) * x) * Real.exp ((R : ℝ) * a)) by ring,
        show Real.exp ((R : ℝ) * x) * (a * Real.exp ((R : ℝ) * a)) =
          a * (Real.exp ((R : ℝ) * x) * Real.exp ((R : ℝ) * a)) by ring,
        hexp]
      ring

end
end RHTower

namespace RHTower
noncomputable section
open Complex Real MeasureTheory Set Filter Topology Polynomial

def thetaCuspTailPhaseTranslationPacketIntegratedNorm (d : ℕ) (z : ℂ) (a : ℝ) : ℝ :=
  (∫ x : ℝ in Ioi 0,
    |thetaCuspTailSecondDensity x| * ‖(finitePositivePhaseTranslationPacket d x a).eval z‖) +
  (∫ x : ℝ in Ioi 0,
    |thetaCuspTailSecondDensity x| * ‖(finitePositivePhaseTranslationPacket d x a).derivative.eval z‖)

lemma continuous_eval_finitePositivePhaseTranslationPacket (d : ℕ) (z : ℂ) (a : ℝ) :
    Continuous (fun x : ℝ => (finitePositivePhaseTranslationPacket d x a).eval z) := by
  have hx := continuous_eval_finitePositivePhasePolynomial d z
  simpa only [finitePositivePhaseTranslationPacket, eval_mul] using
    hx.mul (continuous_const : Continuous (fun _ : ℝ =>
      (finitePositivePhasePolynomial d a).eval z))

lemma continuous_eval_derivative_finitePositivePhaseTranslationPacket (d : ℕ) (z : ℂ) (a : ℝ) :
    Continuous (fun x : ℝ => (finitePositivePhaseTranslationPacket d x a).derivative.eval z) := by
  have hx := continuous_eval_finitePositivePhasePolynomial d z
  have hdx := continuous_eval_derivative_finitePositivePhasePolynomial d z
  simpa only [finitePositivePhaseTranslationPacket, derivative_mul, eval_add, eval_mul] using
    (hdx.mul (continuous_const : Continuous (fun _ : ℝ =>
      (finitePositivePhasePolynomial d a).eval z))).add
      (hx.mul (continuous_const : Continuous (fun _ : ℝ =>
        (finitePositivePhasePolynomial d a).derivative.eval z)))

lemma continuous_abs_thetaCuspTailSecondDensity : Continuous (fun x : ℝ => |thetaCuspTailSecondDensity x|) := by
  unfold thetaCuspTailSecondDensity
  exact (continuous_const.mul
    (differentiable_thetaCuspTailDerivative 2).continuous).abs

theorem thetaCuspTailPhaseTranslationPacketIntegratedNorm_le
    (d R : ℕ) (hR : 1 ≤ R) (a : ℝ) (ha : 0 ≤ a) (z : ℂ) (hz : ‖z‖ ≤ R) :
    thetaCuspTailPhaseTranslationPacketIntegratedNorm d z a ≤
      4 * thetaCuspTailDerivativeNatExpConstant 2 (1 + R) *
        ((R : ℝ) + 1) * Real.exp (((1 + R : ℕ) : ℝ) * a) := by
  let f0 : ℝ → ℝ := fun x =>
    |thetaCuspTailDerivative 2 x| *
      ((((R : ℝ) * (x + a)) ^ 0 / ((0 : ℕ).factorial : ℕ)) *
        Real.exp ((R : ℝ) * (x + a)))
  let f1 : ℝ → ℝ := fun x =>
    |thetaCuspTailDerivative 2 x| *
      ((((R : ℝ) * (x + a)) ^ 1 / ((1 : ℕ).factorial : ℕ)) *
        Real.exp ((R : ℝ) * (x + a)))
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
    (continuous_abs_thetaCuspTailSecondDensity.mul (continuous_eval_finitePositivePhaseTranslationPacket d z a).norm).aestronglyMeasurable.restrict
  have hDmeas : AEStronglyMeasurable (fun x : ℝ =>
      |thetaCuspTailSecondDensity x| * ‖(finitePositivePhaseTranslationPacket d x a).derivative.eval z‖)
      (volume.restrict (Ioi 0)) :=
    (continuous_abs_thetaCuspTailSecondDensity.mul (continuous_eval_derivative_finitePositivePhaseTranslationPacket d z a).norm).aestronglyMeasurable.restrict
  have hVpoint (x : ℝ) (hx : 0 ≤ x) :
      |thetaCuspTailSecondDensity x| * ‖(finitePositivePhaseTranslationPacket d x a).eval z‖ ≤
        4 * f0 x := by
    have hp := norm_eval_finitePositivePhaseTranslationPacket_le_exp_norm d R x a z hx ha hz
    dsimp only [f0]
    unfold thetaCuspTailSecondDensity
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num only [Nat.factorial_zero, Nat.cast_one, div_one, pow_zero, one_mul]
    calc
      4 * |thetaCuspTailDerivative 2 x| * ‖eval z (finitePositivePhaseTranslationPacket d x a)‖ ≤
          4 * |thetaCuspTailDerivative 2 x| *
            Real.exp ((R : ℝ) * (x + a)) :=
        mul_le_mul_of_nonneg_left hp (mul_nonneg (by norm_num) (abs_nonneg _))
      _ = 4 * (|thetaCuspTailDerivative 2 x| *
            Real.exp ((R : ℝ) * (x + a))) := by ring
  have hDpoint (x : ℝ) (hx : 0 ≤ x) :
      |thetaCuspTailSecondDensity x| *
          ‖(finitePositivePhaseTranslationPacket d x a).derivative.eval z‖ ≤ 4 * f1 x := by
    have hp := norm_eval_derivative_finitePositivePhaseTranslationPacket_le_exp_norm d R x a z hx ha hz
    have hxa : 0 ≤ x + a := add_nonneg hx ha
    have hscale : (x + a) * Real.exp ((R : ℝ) * (x + a)) ≤
        (R : ℝ) * (x + a) * Real.exp ((R : ℝ) * (x + a)) := by
      have hRreal : (1 : ℝ) ≤ R := by exact_mod_cast hR
      have hxaScale : x + a ≤ (R : ℝ) * (x + a) := by nlinarith
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
            ((R : ℝ) * (x + a) * Real.exp ((R : ℝ) * (x + a))) :=
        mul_le_mul_of_nonneg_left hp' (mul_nonneg (by norm_num) (abs_nonneg _))
      _ = 4 * (|thetaCuspTailDerivative 2 x| *
            ((R : ℝ) * (x + a) * Real.exp ((R : ℝ) * (x + a)))) := by ring
  have hVint : IntegrableOn (fun x : ℝ =>
      |thetaCuspTailSecondDensity x| * ‖(finitePositivePhaseTranslationPacket d x a).eval z‖) (Ioi 0) := by
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
        Real.exp (((1 + R : ℕ) : ℝ) * a) := by
    calc
      _ ≤ ∫ x : ℝ in Ioi 0, 4 * f0 x := by
        apply MeasureTheory.integral_mono_ae hVint (hf0int.const_mul 4)
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        exact hVpoint x hx.le
      _ = 4 * ∫ x : ℝ in Ioi 0, f0 x := by rw [integral_const_mul]
      _ ≤ 4 * (thetaCuspTailDerivativeNatExpConstant 2 (1 + R) *
          Real.exp (((1 + R : ℕ) : ℝ) * a)) := by
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
        Real.exp (((1 + R : ℕ) : ℝ) * a) := by
    calc
      _ ≤ ∫ x : ℝ in Ioi 0, 4 * f1 x := by
        apply MeasureTheory.integral_mono_ae hDint (hf1int.const_mul 4)
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        exact hDpoint x hx.le
      _ = 4 * ∫ x : ℝ in Ioi 0, f1 x := by rw [integral_const_mul]
      _ ≤ 4 * (thetaCuspTailDerivativeNatExpConstant 2 (1 + R) * (R : ℝ) *
          Real.exp (((1 + R : ℕ) : ℝ) * a)) := by
        gcongr
        simpa only [f1, Nat.factorial_one, Nat.cast_one, div_one, pow_one,
          one_pow] using
          integral_abs_thetaCuspTailDerivative_mul_shiftedFactorialEnvelope_le
            2 1 1 R (by omega) ha
      _ = _ := by ring
  unfold thetaCuspTailPhaseTranslationPacketIntegratedNorm
  calc
    _ ≤ 4 * thetaCuspTailDerivativeNatExpConstant 2 (1 + R) *
          Real.exp (((1 + R : ℕ) : ℝ) * a) +
        4 * thetaCuspTailDerivativeNatExpConstant 2 (1 + R) * (R : ℝ) *
          Real.exp (((1 + R : ℕ) : ℝ) * a) := add_le_add hV hD
    _ = _ := by ring

end
end RHTower

namespace RHTower
noncomputable section
open Complex Real MeasureTheory Set Filter Topology Polynomial

def thetaCuspTailPhaseTranslationPacketAverage (d : ℕ) (z : ℂ) (a : ℝ) : ℂ :=
  ∫ x : ℝ in Ioi 0,
    (thetaCuspTailSecondDensity x : ℂ) * (finitePositivePhaseTranslationPacket d x a).eval z

def thetaCuspTailPhaseTranslationPacketDerivativeAverage (d : ℕ) (z : ℂ) (a : ℝ) : ℂ :=
  ∫ x : ℝ in Ioi 0,
    (thetaCuspTailSecondDensity x : ℂ) * (finitePositivePhaseTranslationPacket d x a).derivative.eval z

def thetaCuspTailPhaseTranslationFullDefectIntegratedCurrent (d : ℕ) (z : ℂ) (a : ℝ) : ℝ :=
  -((thetaCuspTailPhaseTranslationPacketDerivativeAverage d z a *
      (starRingEnd ℂ) (thetaCuspTailPhaseTranslationEdgeAverage d z a)).im) -
    ((thetaCuspTailPhaseTranslationEdgeDerivativeAverage d z a *
      (starRingEnd ℂ) (thetaCuspTailPhaseTranslationPacketAverage d z a)).im) +
    thetaCuspTailPhaseTranslationEdgeIntegratedCurrent d z a

lemma norm_thetaCuspTailPhaseTranslationPacketAverage_le (d : ℕ) (z : ℂ) (a : ℝ) :
    ‖thetaCuspTailPhaseTranslationPacketAverage d z a‖ ≤
      ∫ x : ℝ in Ioi 0,
        |thetaCuspTailSecondDensity x| * ‖(finitePositivePhaseTranslationPacket d x a).eval z‖ := by
  unfold thetaCuspTailPhaseTranslationPacketAverage
  calc
    _ ≤ ∫ x : ℝ in Ioi 0,
      ‖(thetaCuspTailSecondDensity x : ℂ) * (finitePositivePhaseTranslationPacket d x a).eval z‖ :=
        norm_integral_le_integral_norm _
    _ = _ := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with x
      simp

lemma norm_thetaCuspTailPhaseTranslationPacketDerivativeAverage_le (d : ℕ) (z : ℂ) (a : ℝ) :
    ‖thetaCuspTailPhaseTranslationPacketDerivativeAverage d z a‖ ≤
      ∫ x : ℝ in Ioi 0,
        |thetaCuspTailSecondDensity x| *
          ‖(finitePositivePhaseTranslationPacket d x a).derivative.eval z‖ := by
  unfold thetaCuspTailPhaseTranslationPacketDerivativeAverage
  calc
    _ ≤ ∫ x : ℝ in Ioi 0,
      ‖(thetaCuspTailSecondDensity x : ℂ) *
        (finitePositivePhaseTranslationPacket d x a).derivative.eval z‖ := norm_integral_le_integral_norm _
    _ = _ := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with x
      simp

theorem abs_thetaCuspTailPhaseTranslationFullDefectIntegratedCurrent_le
    (d : ℕ) (z : ℂ) (a : ℝ) :
    |thetaCuspTailPhaseTranslationFullDefectIntegratedCurrent d z a| ≤
      thetaCuspTailPhaseTranslationPacketIntegratedNorm d z a *
        thetaCuspTailPhaseTranslationEdgeIntegratedNorm d z a +
      thetaCuspTailPhaseTranslationEdgeIntegratedNorm d z a ^ 2 := by
  let PV : ℝ := ∫ x : ℝ in Ioi 0,
    |thetaCuspTailSecondDensity x| * ‖(finitePositivePhaseTranslationPacket d x a).eval z‖
  let PD : ℝ := ∫ x : ℝ in Ioi 0,
    |thetaCuspTailSecondDensity x| * ‖(finitePositivePhaseTranslationPacket d x a).derivative.eval z‖
  let EV : ℝ := ∫ x : ℝ in Ioi 0,
    |thetaCuspTailSecondDensity x| *
      ‖(finitePositivePhaseTranslationTopEdge d x a).eval z‖
  let ED : ℝ := ∫ x : ℝ in Ioi 0,
    |thetaCuspTailSecondDensity x| *
      ‖(finitePositivePhaseTranslationTopEdge d x a).derivative.eval z‖
  let A : ℝ := (thetaCuspTailPhaseTranslationPacketDerivativeAverage d z a *
    (starRingEnd ℂ) (thetaCuspTailPhaseTranslationEdgeAverage d z a)).im
  let B : ℝ := (thetaCuspTailPhaseTranslationEdgeDerivativeAverage d z a *
    (starRingEnd ℂ) (thetaCuspTailPhaseTranslationPacketAverage d z a)).im
  let J : ℝ := thetaCuspTailPhaseTranslationEdgeIntegratedCurrent d z a
  have hPV : ‖thetaCuspTailPhaseTranslationPacketAverage d z a‖ ≤ PV := norm_thetaCuspTailPhaseTranslationPacketAverage_le d z a
  have hPD : ‖thetaCuspTailPhaseTranslationPacketDerivativeAverage d z a‖ ≤ PD :=
    norm_thetaCuspTailPhaseTranslationPacketDerivativeAverage_le d z a
  have hEV : ‖thetaCuspTailPhaseTranslationEdgeAverage d z a‖ ≤ EV :=
    norm_thetaCuspTailPhaseTranslationEdgeAverage_le d z a
  have hED : ‖thetaCuspTailPhaseTranslationEdgeDerivativeAverage d z a‖ ≤ ED :=
    norm_thetaCuspTailPhaseTranslationEdgeDerivativeAverage_le d z a
  have hPV0 : 0 ≤ PV := by dsimp [PV]; positivity
  have hPD0 : 0 ≤ PD := by dsimp [PD]; positivity
  have hEV0 : 0 ≤ EV := by dsimp [EV]; positivity
  have hED0 : 0 ≤ ED := by dsimp [ED]; positivity
  have hA : |A| ≤ PD * EV := by
    dsimp [A]
    calc
      _ ≤ ‖thetaCuspTailPhaseTranslationPacketDerivativeAverage d z a *
          (starRingEnd ℂ) (thetaCuspTailPhaseTranslationEdgeAverage d z a)‖ :=
        Complex.abs_im_le_norm _
      _ = ‖thetaCuspTailPhaseTranslationPacketDerivativeAverage d z a‖ *
          ‖thetaCuspTailPhaseTranslationEdgeAverage d z a‖ := by simp
      _ ≤ PD * EV := mul_le_mul hPD hEV (norm_nonneg _) hPD0
  have hB : |B| ≤ ED * PV := by
    dsimp [B]
    calc
      _ ≤ ‖thetaCuspTailPhaseTranslationEdgeDerivativeAverage d z a *
          (starRingEnd ℂ) (thetaCuspTailPhaseTranslationPacketAverage d z a)‖ := Complex.abs_im_le_norm _
      _ = ‖thetaCuspTailPhaseTranslationEdgeDerivativeAverage d z a‖ *
          ‖thetaCuspTailPhaseTranslationPacketAverage d z a‖ := by simp
      _ ≤ ED * PV := mul_le_mul hED hPV (norm_nonneg _) hED0
  have hJ : |J| ≤ (EV + ED) ^ 2 := by
    dsimp [J, EV, ED]
    exact abs_thetaCuspTailPhaseTranslationEdgeIntegratedCurrent_le_sq d z a
  have habs : |-A - B + J| ≤ |A| + |B| + |J| := by
    simpa only [sub_eq_add_neg, abs_neg] using abs_add_three (-A) (-B) J
  unfold thetaCuspTailPhaseTranslationFullDefectIntegratedCurrent
  change |-A - B + J| ≤ _
  calc
    _ ≤ |A| + |B| + |J| := habs
    _ ≤ PD * EV + ED * PV + (EV + ED) ^ 2 := by linarith
    _ ≤ (PV + PD) * (EV + ED) + (EV + ED) ^ 2 := by
      nlinarith [mul_nonneg hPV0 hED0, mul_nonneg hPD0 hEV0]
    _ = _ := by
      unfold thetaCuspTailPhaseTranslationPacketIntegratedNorm thetaCuspTailPhaseTranslationEdgeIntegratedNorm
      dsimp [PV, PD, EV, ED]

end
end RHTower

namespace RHTower
noncomputable section
open Complex Real MeasureTheory Set Filter Topology Polynomial

theorem thetaCuspTailPhaseTranslationPacketIntegratedNorm_le_logarithmicMajorant
    (A d R n : ℕ) (hR : 1 ≤ R) (z : ℂ) (hz : ‖z‖ ≤ R) :
    thetaCuspTailPhaseTranslationPacketIntegratedNorm d z (xiCTaylorLogarithmicHaarDisplacement A n) ≤
      4 * thetaCuspTailDerivativeNatExpConstant 2 (1 + R) *
        ((R : ℝ) + 1) *
          (2 * ((n + 1 : ℕ) : ℝ)) ^ (A * (2 * (R + 1))) := by
  have ha : 0 ≤ xiCTaylorLogarithmicHaarDisplacement A n := by
    unfold xiCTaylorLogarithmicHaarDisplacement
    positivity
  have hp := thetaCuspTailPhaseTranslationPacketIntegratedNorm_le d R hR
    (xiCTaylorLogarithmicHaarDisplacement A n) ha z hz
  have hexp : Real.exp (((1 + R : ℕ) : ℝ) *
      xiCTaylorLogarithmicHaarDisplacement A n) ≤
      (2 * ((n + 1 : ℕ) : ℝ)) ^ (A * (2 * (R + 1))) := by
    unfold xiCTaylorLogarithmicHaarDisplacement
    convert exp_logarithmicHaarDepth_le_pow A (2 * (R + 1)) n using 1
    push_cast
    ring
  have htailC : 0 ≤ thetaCuspTailDerivativeNatExpConstant 2 (1 + R) := by
    unfold thetaCuspTailDerivativeNatExpConstant
    exact mul_nonneg
      (mul_nonneg (thetaCuspCoeffMass_nonneg _) (Real.exp_pos _).le)
      (tsum_nonneg fun _ => mul_nonneg (pow_nonneg (by positivity) _)
        (Real.exp_pos _).le)
  have hC : 0 ≤ 4 * thetaCuspTailDerivativeNatExpConstant 2 (1 + R) *
      ((R : ℝ) + 1) := by positivity
  calc
    _ ≤ 4 * thetaCuspTailDerivativeNatExpConstant 2 (1 + R) *
        ((R : ℝ) + 1) *
          Real.exp (((1 + R : ℕ) : ℝ) *
            xiCTaylorLogarithmicHaarDisplacement A n) := hp
    _ ≤ _ := mul_le_mul_of_nonneg_left hexp hC

lemma thetaCuspTailPhaseTranslationPacketIntegratedNorm_nonneg (d : ℕ) (z : ℂ) (a : ℝ) :
    0 ≤ thetaCuspTailPhaseTranslationPacketIntegratedNorm d z a := by
  unfold thetaCuspTailPhaseTranslationPacketIntegratedNorm
  apply add_nonneg <;>
    exact MeasureTheory.integral_nonneg fun x =>
      mul_nonneg (abs_nonneg _) (norm_nonneg _)

theorem tendsto_thetaCuspTailPhaseTranslationFullDefectIntegratedCurrent_mul_pow_zero
    (A M R : ℕ) (hR : 1 ≤ R) (d : ℕ → ℕ) (hd : ∀ n, n ≤ d n)
    (z : ℕ → ℂ) (hz : ∀ᶠ n : ℕ in atTop, ‖z n‖ ≤ R) :
    Tendsto (fun n : ℕ =>
      |thetaCuspTailPhaseTranslationFullDefectIntegratedCurrent (d n) (z n)
          (xiCTaylorLogarithmicHaarDisplacement A n)| *
        (((n + 1 : ℕ) : ℝ) ^ M)) atTop (nhds 0) := by
  let E : ℕ → ℝ := fun n =>
    thetaCuspTailPhaseTranslationEdgeIntegratedNorm (d n) (z n)
      (xiCTaylorLogarithmicHaarDisplacement A n)
  let Q : ℕ → ℝ := fun n =>
    thetaCuspTailPhaseTranslationPacketIntegratedNorm (d n) (z n)
      (xiCTaylorLogarithmicHaarDisplacement A n)
  let K : ℕ := A * (2 * (R + 1))
  let C : ℝ := 4 * thetaCuspTailDerivativeNatExpConstant 2 (1 + R) *
    ((R : ℝ) + 1) * (2 : ℝ) ^ K
  have hEM : Tendsto (fun n => E n * (((n + 1 : ℕ) : ℝ) ^ M))
      atTop (nhds 0) := by
    simpa only [E] using
      tendsto_thetaCuspTailPhaseTranslationEdgeIntegratedNorm_mul_pow_zero
        A M R hR d hd z hz
  have hEKM : Tendsto (fun n => E n * (((n + 1 : ℕ) : ℝ) ^ (K + M)))
      atTop (nhds 0) := by
    simpa only [E] using
      tendsto_thetaCuspTailPhaseTranslationEdgeIntegratedNorm_mul_pow_zero
        A (K + M) R hR d hd z hz
  have hE0 : Tendsto E atTop (nhds 0) := by
    simpa only [E, pow_zero, mul_one] using
      tendsto_thetaCuspTailPhaseTranslationEdgeIntegratedNorm_mul_pow_zero
        A 0 R hR d hd z hz
  have hcrossMajor : Tendsto (fun n => C *
      (E n * (((n + 1 : ℕ) : ℝ) ^ (K + M)))) atTop (nhds 0) := by
    simpa using hEKM.const_mul C
  have hcross : Tendsto (fun n =>
      (Q n * E n) * (((n + 1 : ℕ) : ℝ) ^ M)) atTop (nhds 0) := by
    apply squeeze_zero'
    · exact Eventually.of_forall fun n => mul_nonneg
        (mul_nonneg (by dsimp [Q]; exact thetaCuspTailPhaseTranslationPacketIntegratedNorm_nonneg _ _ _)
          (thetaCuspTailPhaseTranslationEdgeIntegratedNorm_nonneg _ _ _))
        (pow_nonneg (by positivity) _)
    · filter_upwards [hz] with n hzn
      have hQ := thetaCuspTailPhaseTranslationPacketIntegratedNorm_le_logarithmicMajorant A (d n) R n hR (z n) hzn
      have hE0n : 0 ≤ E n := by
        dsimp [E]
        exact thetaCuspTailPhaseTranslationEdgeIntegratedNorm_nonneg _ _ _
      have hpowM : 0 ≤ (((n + 1 : ℕ) : ℝ) ^ M) := by positivity
      have hq : Q n ≤ C * (((n + 1 : ℕ) : ℝ) ^ K) := by
        calc
          Q n ≤ 4 * thetaCuspTailDerivativeNatExpConstant 2 (1 + R) *
              ((R : ℝ) + 1) *
                (2 * ((n + 1 : ℕ) : ℝ)) ^ K := by
            simpa only [Q, K] using hQ
          _ = C * (((n + 1 : ℕ) : ℝ) ^ K) := by
            dsimp [C]
            rw [mul_pow]
            ring
      calc
        (Q n * E n) * ((n + 1 : ℕ) : ℝ) ^ M ≤
            ((C * ((n + 1 : ℕ) : ℝ) ^ K) * E n) *
              ((n + 1 : ℕ) : ℝ) ^ M := by gcongr
        _ = C * (E n * ((n + 1 : ℕ) : ℝ) ^ (K + M)) := by
          rw [pow_add]
          ring
    · exact hcrossMajor
  have hself : Tendsto (fun n => E n *
      (E n * (((n + 1 : ℕ) : ℝ) ^ M))) atTop (nhds 0) := by
    simpa using hE0.mul hEM
  have hmajor : Tendsto (fun n =>
      (Q n * E n) * (((n + 1 : ℕ) : ℝ) ^ M) +
        E n * (E n * (((n + 1 : ℕ) : ℝ) ^ M))) atTop (nhds 0) :=
    by simpa using hcross.add hself
  apply squeeze_zero'
  · exact Eventually.of_forall fun n => mul_nonneg (abs_nonneg _)
      (pow_nonneg (by positivity) _)
  · filter_upwards [] with n
    have hdef := abs_thetaCuspTailPhaseTranslationFullDefectIntegratedCurrent_le (d n) (z n)
      (xiCTaylorLogarithmicHaarDisplacement A n)
    have hpow : 0 ≤ (((n + 1 : ℕ) : ℝ) ^ M) := by positivity
    calc
      |thetaCuspTailPhaseTranslationFullDefectIntegratedCurrent (d n) (z n)
          (xiCTaylorLogarithmicHaarDisplacement A n)| *
          ((n + 1 : ℕ) : ℝ) ^ M ≤
        (Q n * E n + E n ^ 2) * ((n + 1 : ℕ) : ℝ) ^ M := by
          exact mul_le_mul_of_nonneg_right hdef hpow
      _ = (Q n * E n) * ((n + 1 : ℕ) : ℝ) ^ M +
          E n * (E n * ((n + 1 : ℕ) : ℝ) ^ M) := by ring
  · exact hmajor

end
end RHTower


namespace RHTower

noncomputable section

/-- The three terms in `thetaCuspTailPhaseTranslationFullDefectIntegratedCurrent` are exactly the
current difference between the integrated finite translation packet minus its edge and the packet
itself.  No estimate or sign is used in this identity. -/
theorem thetaCuspTailPhaseTranslationIntegratedCurrent_sub_exact
    (d : ℕ) (z : ℂ) (a : ℝ) :
    ((thetaCuspTailPhaseTranslationPacketDerivativeAverage d z a -
        thetaCuspTailPhaseTranslationEdgeDerivativeAverage d z a) *
      (starRingEnd ℂ)
        (thetaCuspTailPhaseTranslationPacketAverage d z a -
          thetaCuspTailPhaseTranslationEdgeAverage d z a)).im =
      (thetaCuspTailPhaseTranslationPacketDerivativeAverage d z a *
        (starRingEnd ℂ) (thetaCuspTailPhaseTranslationPacketAverage d z a)).im +
        thetaCuspTailPhaseTranslationFullDefectIntegratedCurrent d z a := by
  unfold thetaCuspTailPhaseTranslationFullDefectIntegratedCurrent
    thetaCuspTailPhaseTranslationEdgeIntegratedCurrent
  simp only [map_sub, sub_mul, mul_sub, Complex.sub_im]
  ring

/-- On an anisotropic Taylor schedule the complete positive-channel finite translation defect,
including both mixed currents, beats twice the local Xi-order. -/
theorem tendsto_scheduled_thetaCuspTailPhaseTranslationFullDefectIntegratedCurrent_localOrder
    {D : ℕ → ℕ} (hD : XiCTaylorOddThetaTailSuperaccurateSchedule D)
    (A : ℕ) (sigma : ℂ) :
    Tendsto (fun n : ℕ =>
      |thetaCuspTailPhaseTranslationFullDefectIntegratedCurrent
          (D (xiCTaylorAnisotropicScheduleStage sigma n) + 1)
          (xiCTaylorAnisotropicCenteredPoint sigma n)
          (xiCTaylorLogarithmicHaarDisplacement A n)| *
        (((n + 1 : ℕ) : ℝ) ^
          (2 * (analyticOrderAt xi sigma).toNat))) atTop (nhds 0) := by
  obtain ⟨R, hR, hz⟩ :=
    exists_eventually_xiCTaylorAnisotropicCenteredPoint_norm_le_nat sigma
  exact
    tendsto_thetaCuspTailPhaseTranslationFullDefectIntegratedCurrent_mul_pow_zero
      A (2 * (analyticOrderAt xi sigma).toNat) R hR
        (fun n => D (xiCTaylorAnisotropicScheduleStage sigma n) + 1)
        (le_xiCTaylorScheduledThetaTailDepth hD sigma)
        (xiCTaylorAnisotropicCenteredPoint sigma) hz

/-- **Complete positive-channel edge theorem.**  The self-current and both exact mixed currents of
the finite translation edge are jointly `o(n)|P|^2` on every source-selected anisotropic mesh. -/
theorem eventually_abs_scheduled_thetaCuspTailPhaseTranslationFullDefectIntegratedCurrent_lt_scaled_normSq
    {D : ℕ → ℕ} (hD : XiCTaylorOddThetaTailSuperaccurateSchedule D)
    (A : ℕ) (sigma : ℂ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ n : ℕ in atTop,
      |thetaCuspTailPhaseTranslationFullDefectIntegratedCurrent
          (D (xiCTaylorAnisotropicScheduleStage sigma n) + 1)
          (xiCTaylorAnisotropicCenteredPoint sigma n)
          (xiCTaylorLogarithmicHaarDisplacement A n)| <
        (epsilon * ((n + 1 : ℕ) : ℝ)) *
          Complex.normSq
            ((xiCTaylorPolynomial
              (xiCTaylorOddDegreeSchedule D
                (xiCTaylorAnisotropicScheduleStage sigma n))).eval
                  (xiCTaylorAnisotropicCenteredPoint sigma n)) := by
  apply eventually_remainder_lt_scaled_xiCTaylor_normSq_of_tendsto_localOrder
    hD sigma (fun n =>
      |thetaCuspTailPhaseTranslationFullDefectIntegratedCurrent
        (D (xiCTaylorAnisotropicScheduleStage sigma n) + 1)
        (xiCTaylorAnisotropicCenteredPoint sigma n)
        (xiCTaylorLogarithmicHaarDisplacement A n)|)
  · exact
      tendsto_scheduled_thetaCuspTailPhaseTranslationFullDefectIntegratedCurrent_localOrder
        hD A sigma
  · exact hepsilon

/-- The complete negative finite phase packet. -/
def finiteNegativePhaseTranslationPacket
    (d : ℕ) (x a : ℝ) : Polynomial ℂ :=
  finiteNegativePhasePolynomial d x * finiteNegativePhasePolynomial d a

/-- Reflection transports the complete negative packet to the positive packet. -/
theorem finiteNegativePhaseTranslationPacket_eq_positive_comp_neg_X
    (d : ℕ) (x a : ℝ) :
    finiteNegativePhaseTranslationPacket d x a =
      (finitePositivePhaseTranslationPacket d x a).comp (-X) := by
  unfold finiteNegativePhaseTranslationPacket finitePositivePhaseTranslationPacket
  rw [finiteNegativePhasePolynomial_eq_positive_comp_neg_X,
    finiteNegativePhasePolynomial_eq_positive_comp_neg_X, mul_comp]

/-- Value reflection for the complete finite phase packet. -/
theorem finiteNegativePhaseTranslationPacket_eval_eq_positive_eval_neg
    (d : ℕ) (x a : ℝ) (z : ℂ) :
    (finiteNegativePhaseTranslationPacket d x a).eval z =
      (finitePositivePhaseTranslationPacket d x a).eval (-z) := by
  rw [finiteNegativePhaseTranslationPacket_eq_positive_comp_neg_X, eval_comp]
  simp

/-- Derivative reflection for the complete finite phase packet. -/
theorem finiteNegativePhaseTranslationPacket_derivative_eval_eq_neg_positive_derivative_eval_neg
    (d : ℕ) (x a : ℝ) (z : ℂ) :
    (finiteNegativePhaseTranslationPacket d x a).derivative.eval z =
      -((finitePositivePhaseTranslationPacket d x a).derivative.eval (-z)) := by
  rw [finiteNegativePhaseTranslationPacket_eq_positive_comp_neg_X, derivative_comp]
  simp

/-- Density-integrated negative finite phase packet. -/
def thetaCuspTailNegativePhaseTranslationPacketAverage
    (d : ℕ) (z : ℂ) (a : ℝ) : ℂ :=
  ∫ x : ℝ in Ioi 0,
    (thetaCuspTailSecondDensity x : ℂ) *
      (finiteNegativePhaseTranslationPacket d x a).eval z

/-- Density-integrated derivative of the negative finite phase packet. -/
def thetaCuspTailNegativePhaseTranslationPacketDerivativeAverage
    (d : ℕ) (z : ℂ) (a : ℝ) : ℂ :=
  ∫ x : ℝ in Ioi 0,
    (thetaCuspTailSecondDensity x : ℂ) *
      (finiteNegativePhaseTranslationPacket d x a).derivative.eval z

/-- Negative packet values are reflected positive packet values. -/
theorem thetaCuspTailNegativePhaseTranslationPacketAverage_eq_positive_neg
    (d : ℕ) (z : ℂ) (a : ℝ) :
    thetaCuspTailNegativePhaseTranslationPacketAverage d z a =
      thetaCuspTailPhaseTranslationPacketAverage d (-z) a := by
  unfold thetaCuspTailNegativePhaseTranslationPacketAverage
    thetaCuspTailPhaseTranslationPacketAverage
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with x
  rw [finiteNegativePhaseTranslationPacket_eval_eq_positive_eval_neg]

/-- Negative packet derivatives acquire exactly the reflection chain-rule sign. -/
theorem thetaCuspTailNegativePhaseTranslationPacketDerivativeAverage_eq_neg_positive_neg
    (d : ℕ) (z : ℂ) (a : ℝ) :
    thetaCuspTailNegativePhaseTranslationPacketDerivativeAverage d z a =
      -thetaCuspTailPhaseTranslationPacketDerivativeAverage d (-z) a := by
  unfold thetaCuspTailNegativePhaseTranslationPacketDerivativeAverage
    thetaCuspTailPhaseTranslationPacketDerivativeAverage
  rw [← MeasureTheory.integral_neg]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with x
  rw [finiteNegativePhaseTranslationPacket_derivative_eval_eq_neg_positive_derivative_eval_neg]
  ring

/-- The complete negative-channel finite translation current defect: both mixed currents and the
edge self-current are retained. -/
def thetaCuspTailNegativePhaseTranslationFullDefectIntegratedCurrent
    (d : ℕ) (z : ℂ) (a : ℝ) : ℝ :=
  -((thetaCuspTailNegativePhaseTranslationPacketDerivativeAverage d z a *
      (starRingEnd ℂ)
        (thetaCuspTailNegativePhaseTranslationEdgeAverage d z a)).im) -
    ((thetaCuspTailNegativePhaseTranslationEdgeDerivativeAverage d z a *
      (starRingEnd ℂ)
        (thetaCuspTailNegativePhaseTranslationPacketAverage d z a)).im) +
    thetaCuspTailNegativePhaseTranslationEdgeIntegratedCurrent d z a

/-- The complete two-component defect, including its mixed currents, is reflection-odd. -/
theorem thetaCuspTailNegativePhaseTranslationFullDefectIntegratedCurrent_eq_neg_positive_neg
    (d : ℕ) (z : ℂ) (a : ℝ) :
    thetaCuspTailNegativePhaseTranslationFullDefectIntegratedCurrent d z a =
      -thetaCuspTailPhaseTranslationFullDefectIntegratedCurrent d (-z) a := by
  rw [thetaCuspTailNegativePhaseTranslationFullDefectIntegratedCurrent,
    thetaCuspTailPhaseTranslationFullDefectIntegratedCurrent,
    thetaCuspTailNegativePhaseTranslationPacketAverage_eq_positive_neg,
    thetaCuspTailNegativePhaseTranslationPacketDerivativeAverage_eq_neg_positive_neg,
    thetaCuspTailNegativePhaseTranslationEdgeAverage_eq_positive_neg,
    thetaCuspTailNegativePhaseTranslationEdgeDerivativeAverage_eq_neg_positive_neg,
    thetaCuspTailNegativePhaseTranslationEdgeIntegratedCurrent_eq_neg_positive_neg]
  simp
  ring

/-- The complete negative-channel defect beats twice the local Xi-order on the original one-sided
anisotropic mesh. -/
theorem tendsto_scheduled_thetaCuspTailNegativePhaseTranslationFullDefectIntegratedCurrent_localOrder
    {D : ℕ → ℕ} (hD : XiCTaylorOddThetaTailSuperaccurateSchedule D)
    (A : ℕ) (sigma : ℂ) :
    Tendsto (fun n : ℕ =>
      |thetaCuspTailNegativePhaseTranslationFullDefectIntegratedCurrent
          (D (xiCTaylorAnisotropicScheduleStage sigma n) + 1)
          (xiCTaylorAnisotropicCenteredPoint sigma n)
          (xiCTaylorLogarithmicHaarDisplacement A n)| *
        (((n + 1 : ℕ) : ℝ) ^
          (2 * (analyticOrderAt xi sigma).toNat))) atTop (nhds 0) := by
  obtain ⟨R, hR, hz⟩ :=
    exists_eventually_xiCTaylorAnisotropicCenteredPoint_norm_le_nat sigma
  have hzneg : ∀ᶠ n : ℕ in atTop,
      ‖-xiCTaylorAnisotropicCenteredPoint sigma n‖ ≤ R := by
    simpa only [norm_neg] using hz
  have hpos :=
    tendsto_thetaCuspTailPhaseTranslationFullDefectIntegratedCurrent_mul_pow_zero
      A (2 * (analyticOrderAt xi sigma).toNat) R hR
        (fun n => D (xiCTaylorAnisotropicScheduleStage sigma n) + 1)
        (le_xiCTaylorScheduledThetaTailDepth hD sigma)
        (fun n => -xiCTaylorAnisotropicCenteredPoint sigma n) hzneg
  convert hpos using 1
  funext n
  rw [thetaCuspTailNegativePhaseTranslationFullDefectIntegratedCurrent_eq_neg_positive_neg,
    abs_neg]

/-- **Complete negative-channel edge theorem.**  Both reflected mixed currents and the edge
self-current are jointly `o(n)|P|^2` on the same anisotropic Taylor denominator. -/
theorem eventually_abs_scheduled_thetaCuspTailNegativePhaseTranslationFullDefectIntegratedCurrent_lt_scaled_normSq
    {D : ℕ → ℕ} (hD : XiCTaylorOddThetaTailSuperaccurateSchedule D)
    (A : ℕ) (sigma : ℂ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ n : ℕ in atTop,
      |thetaCuspTailNegativePhaseTranslationFullDefectIntegratedCurrent
          (D (xiCTaylorAnisotropicScheduleStage sigma n) + 1)
          (xiCTaylorAnisotropicCenteredPoint sigma n)
          (xiCTaylorLogarithmicHaarDisplacement A n)| <
        (epsilon * ((n + 1 : ℕ) : ℝ)) *
          Complex.normSq
            ((xiCTaylorPolynomial
              (xiCTaylorOddDegreeSchedule D
                (xiCTaylorAnisotropicScheduleStage sigma n))).eval
                  (xiCTaylorAnisotropicCenteredPoint sigma n)) := by
  apply eventually_remainder_lt_scaled_xiCTaylor_normSq_of_tendsto_localOrder
    hD sigma (fun n =>
      |thetaCuspTailNegativePhaseTranslationFullDefectIntegratedCurrent
        (D (xiCTaylorAnisotropicScheduleStage sigma n) + 1)
        (xiCTaylorAnisotropicCenteredPoint sigma n)
        (xiCTaylorLogarithmicHaarDisplacement A n)|)
  · exact
      tendsto_scheduled_thetaCuspTailNegativePhaseTranslationFullDefectIntegratedCurrent_localOrder
        hD A sigma
  · exact hepsilon

/-- **Finite translation/Haar capstone.**  At one explicit local-order logarithmic depth, the
cofinal Haar row and the complete current defects of both finite cosine--sine channels are all
`o(n)|P|^2` on the anisotropic rational mesh. -/
theorem eventually_logarithmicHaarTopRow_and_twoPhaseFullDefectCurrents_lt_scaled_normSq
    {D : ℕ → ℕ} (hD : XiCTaylorOddThetaTailSuperaccurateSchedule D)
    (sigma : ℂ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ n : ℕ in atTop,
      |∫ p : ℝ × ℝ,
          xiCTaylorThetaTailCoreDyadicHaarRemainderKernel
            (D (xiCTaylorAnisotropicScheduleStage sigma n))
            (xiCTaylorAnisotropicCenteredPoint sigma n)
            (xiCTaylorLogarithmicHaarDepth
              (2 * (analyticOrderAt xi sigma).toNat + 1) n) p
            ∂((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0)))| <
        (epsilon * ((n + 1 : ℕ) : ℝ)) *
          Complex.normSq
            ((xiCTaylorPolynomial
              (xiCTaylorOddDegreeSchedule D
                (xiCTaylorAnisotropicScheduleStage sigma n))).eval
                  (xiCTaylorAnisotropicCenteredPoint sigma n)) ∧
      |thetaCuspTailPhaseTranslationFullDefectIntegratedCurrent
          (D (xiCTaylorAnisotropicScheduleStage sigma n) + 1)
          (xiCTaylorAnisotropicCenteredPoint sigma n)
          (xiCTaylorLogarithmicHaarDisplacement
            (2 * (analyticOrderAt xi sigma).toNat + 1) n)| <
        (epsilon * ((n + 1 : ℕ) : ℝ)) *
          Complex.normSq
            ((xiCTaylorPolynomial
              (xiCTaylorOddDegreeSchedule D
                (xiCTaylorAnisotropicScheduleStage sigma n))).eval
                  (xiCTaylorAnisotropicCenteredPoint sigma n)) ∧
      |thetaCuspTailNegativePhaseTranslationFullDefectIntegratedCurrent
          (D (xiCTaylorAnisotropicScheduleStage sigma n) + 1)
          (xiCTaylorAnisotropicCenteredPoint sigma n)
          (xiCTaylorLogarithmicHaarDisplacement
            (2 * (analyticOrderAt xi sigma).toNat + 1) n)| <
        (epsilon * ((n + 1 : ℕ) : ℝ)) *
          Complex.normSq
            ((xiCTaylorPolynomial
              (xiCTaylorOddDegreeSchedule D
                (xiCTaylorAnisotropicScheduleStage sigma n))).eval
                  (xiCTaylorAnisotropicCenteredPoint sigma n)) := by
  have htop := eventually_logarithmicHaarTopRow_and_phaseEdgeCurrent_lt_scaled_normSq
    hD sigma hepsilon
  have hpositive :=
    eventually_abs_scheduled_thetaCuspTailPhaseTranslationFullDefectIntegratedCurrent_lt_scaled_normSq
      hD (2 * (analyticOrderAt xi sigma).toNat + 1) sigma hepsilon
  have hnegative :=
    eventually_abs_scheduled_thetaCuspTailNegativePhaseTranslationFullDefectIntegratedCurrent_lt_scaled_normSq
      hD (2 * (analyticOrderAt xi sigma).toNat + 1) sigma hepsilon
  filter_upwards [htop, hpositive, hnegative] with n hrow hpos hneg
  exact ⟨hrow.1, hpos, hneg⟩

end

end RHTower
