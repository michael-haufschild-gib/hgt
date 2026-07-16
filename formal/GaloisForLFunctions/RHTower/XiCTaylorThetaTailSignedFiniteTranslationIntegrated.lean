import GaloisForLFunctions.RHTower.XiCTaylorThetaTailSignedFiniteTranslationEdge

/-!
# Signed integrated finite translation-edge bounds

The exact theta density integrates the signed coefficient-level envelopes with the same degree
decay as in the nonnegative-displacement channel.  The displacement occurs only through its
absolute value in the majorant; the polynomial edge itself retains its original sign.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial

namespace RHTower

noncomputable section

/-- The signed value edge remains geometrically small after integration against `rho = 4 T''`. -/
theorem integral_abs_thetaCuspTailSecondDensity_mul_phaseTranslationTopEdge_norm_le_abs
    (d R p : ℕ) (hp : 0 < p) (a : ℝ)
    (z : ℂ) (hz : ‖z‖ ≤ R) :
    (∫ x : ℝ in Ioi 0,
      |thetaCuspTailSecondDensity x| *
        ‖(finitePositivePhaseTranslationTopEdge d x a).eval z‖) ≤
      12 * thetaCuspTailDerivativeNatExpConstant 2 (p + R) *
        ((R : ℝ) ^ (2 * d + 1) / (p : ℝ) ^ (2 * d + 2)) *
          Real.exp (((p + R : ℕ) : ℝ) * |a|) := by
  let N : ℕ := 2 * d + 1
  let E : ℝ → ℝ := fun x =>
    (((R : ℝ) * (x + |a|)) ^ N / N.factorial) *
      Real.exp ((R : ℝ) * (x + |a|))
  have ha : 0 ≤ |a| := abs_nonneg a
  have hEnvInt : IntegrableOn (fun x : ℝ =>
      |thetaCuspTailDerivative 2 x| * E x) (Ioi 0) := by
    simpa only [E, N] using
      integrableOn_abs_thetaCuspTailDerivative_mul_shiftedFactorialEnvelope
        2 N p R hp ha
  have hmajorInt : IntegrableOn (fun x : ℝ =>
      12 * (|thetaCuspTailDerivative 2 x| * E x)) (Ioi 0) :=
    hEnvInt.const_mul 12
  have hedgeCont := continuous_eval_finitePositivePhaseTranslationTopEdge d a z
  have hminorMeas : AEStronglyMeasurable (fun x : ℝ =>
      |thetaCuspTailSecondDensity x| *
        ‖(finitePositivePhaseTranslationTopEdge d x a).eval z‖)
      (volume.restrict (Ioi 0)) := by
    exact ((((differentiable_thetaCuspTailDerivative 2).continuous.const_mul 4).abs).mul
      hedgeCont.norm).aestronglyMeasurable.restrict
  have hpoint (x : ℝ) (hx0 : 0 ≤ x) :
      |thetaCuspTailSecondDensity x| *
          ‖(finitePositivePhaseTranslationTopEdge d x a).eval z‖ ≤
        12 * (|thetaCuspTailDerivative 2 x| * E x) := by
    have hedge :=
      norm_eval_finitePositivePhaseTranslationTopEdge_le_absShiftedFactorialEnvelope
        d R x a z hx0 hz
    have hrho : |thetaCuspTailSecondDensity x| =
        4 * |thetaCuspTailDerivative 2 x| := by
      simp [thetaCuspTailSecondDensity, abs_mul]
    rw [hrho]
    change 4 * |thetaCuspTailDerivative 2 x| *
        ‖(finitePositivePhaseTranslationTopEdge d x a).eval z‖ ≤
      12 * (|thetaCuspTailDerivative 2 x| * E x)
    change ‖(finitePositivePhaseTranslationTopEdge d x a).eval z‖ ≤ 3 * E x at hedge
    nlinarith [abs_nonneg (thetaCuspTailDerivative 2 x)]
  have hminorInt : IntegrableOn (fun x : ℝ =>
      |thetaCuspTailSecondDensity x| *
        ‖(finitePositivePhaseTranslationTopEdge d x a).eval z‖) (Ioi 0) := by
    apply hmajorInt.mono' hminorMeas
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hnon : 0 ≤ |thetaCuspTailSecondDensity x| *
        ‖(finitePositivePhaseTranslationTopEdge d x a).eval z‖ := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hnon]
    exact hpoint x hx.le
  calc
    (∫ x : ℝ in Ioi 0,
      |thetaCuspTailSecondDensity x| *
        ‖(finitePositivePhaseTranslationTopEdge d x a).eval z‖) ≤
      ∫ x : ℝ in Ioi 0,
        12 * (|thetaCuspTailDerivative 2 x| * E x) := by
      apply MeasureTheory.integral_mono_ae hminorInt hmajorInt
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact hpoint x hx.le
    _ = 12 * (∫ x : ℝ in Ioi 0,
        |thetaCuspTailDerivative 2 x| * E x) := by rw [integral_const_mul]
    _ ≤ 12 * (thetaCuspTailDerivativeNatExpConstant 2 (p + R) *
        ((R : ℝ) ^ N / (p : ℝ) ^ (N + 1)) *
          Real.exp (((p + R : ℕ) : ℝ) * |a|)) := by
      gcongr
      simpa only [E] using
        integral_abs_thetaCuspTailDerivative_mul_shiftedFactorialEnvelope_le
          2 N p R hp ha
    _ = _ := by dsimp [N]; ring

/-- The derivative of the signed edge has the same integrated geometric decay. -/
theorem integral_abs_thetaCuspTailSecondDensity_mul_phaseTranslationTopEdgeDerivative_norm_le_abs
    (d R p : ℕ) (hRone : 1 ≤ R) (hp : 0 < p) (a : ℝ)
    (z : ℂ) (hz : ‖z‖ ≤ R) :
    (∫ x : ℝ in Ioi 0,
      |thetaCuspTailSecondDensity x| *
        ‖(finitePositivePhaseTranslationTopEdge d x a).derivative.eval z‖) ≤
      12 * (2 * d + 1 : ℕ) *
          (thetaCuspTailDerivativeNatExpConstant 2 (p + R) *
            ((R : ℝ) ^ (2 * d + 1) / (p : ℝ) ^ (2 * d + 2)) *
              Real.exp (((p + R : ℕ) : ℝ) * |a|)) +
        8 * (2 * d + 2 : ℕ) *
          (thetaCuspTailDerivativeNatExpConstant 2 (p + R) *
            ((R : ℝ) ^ (2 * d + 2) / (p : ℝ) ^ (2 * d + 3)) *
              Real.exp (((p + R : ℕ) : ℝ) * |a|)) := by
  let N : ℕ := 2 * d + 1
  let N1 : ℕ := 2 * d + 2
  let E : ℕ → ℝ → ℝ := fun m x =>
    (((R : ℝ) * (x + |a|)) ^ m / m.factorial) *
      Real.exp ((R : ℝ) * (x + |a|))
  let A : ℝ := 12 * N
  let B : ℝ := 8 * N1
  let fN : ℝ → ℝ := fun x => |thetaCuspTailDerivative 2 x| * E N x
  let fN1 : ℝ → ℝ := fun x => |thetaCuspTailDerivative 2 x| * E N1 x
  let major : ℝ → ℝ := fun x => A * fN x + B * fN1 x
  have ha : 0 ≤ |a| := abs_nonneg a
  have hNInt : IntegrableOn fN (Ioi 0) := by
    simpa only [fN, E] using
      integrableOn_abs_thetaCuspTailDerivative_mul_shiftedFactorialEnvelope
        2 N p R hp ha
  have hN1Int : IntegrableOn fN1 (Ioi 0) := by
    simpa only [fN1, E] using
      integrableOn_abs_thetaCuspTailDerivative_mul_shiftedFactorialEnvelope
        2 N1 p R hp ha
  have hmajorInt : IntegrableOn major (Ioi 0) :=
    (hNInt.const_mul A).add (hN1Int.const_mul B)
  have hedgeCont :=
    continuous_eval_derivative_finitePositivePhaseTranslationTopEdge d a z
  have hminorMeas : AEStronglyMeasurable (fun x : ℝ =>
      |thetaCuspTailSecondDensity x| *
        ‖(finitePositivePhaseTranslationTopEdge d x a).derivative.eval z‖)
      (volume.restrict (Ioi 0)) := by
    exact ((((differentiable_thetaCuspTailDerivative 2).continuous.const_mul 4).abs).mul
      hedgeCont.norm).aestronglyMeasurable.restrict
  have hpoint (x : ℝ) (hx0 : 0 ≤ x) :
      |thetaCuspTailSecondDensity x| *
          ‖(finitePositivePhaseTranslationTopEdge d x a).derivative.eval z‖ ≤
        major x := by
    have hedge :=
      norm_eval_derivative_finitePositivePhaseTranslationTopEdge_le_absShiftedFactorialEnvelope
        d R x a z hRone hx0 hz
    have hrho : |thetaCuspTailSecondDensity x| =
        4 * |thetaCuspTailDerivative 2 x| := by
      simp [thetaCuspTailSecondDensity, abs_mul]
    rw [hrho]
    change 4 * |thetaCuspTailDerivative 2 x| *
        ‖(finitePositivePhaseTranslationTopEdge d x a).derivative.eval z‖ ≤
      A * fN x + B * fN1 x
    have hedge' : ‖(finitePositivePhaseTranslationTopEdge d x a).derivative.eval z‖ ≤
        3 * N * E N x + 2 * N1 * E N1 x := by
      simpa only [N, N1, E] using hedge
    dsimp only [major, A, B, fN, fN1]
    nlinarith [hedge', abs_nonneg (thetaCuspTailDerivative 2 x)]
  have hminorInt : IntegrableOn (fun x : ℝ =>
      |thetaCuspTailSecondDensity x| *
        ‖(finitePositivePhaseTranslationTopEdge d x a).derivative.eval z‖) (Ioi 0) := by
    apply hmajorInt.mono' hminorMeas
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hnon : 0 ≤ |thetaCuspTailSecondDensity x| *
        ‖(finitePositivePhaseTranslationTopEdge d x a).derivative.eval z‖ := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hnon]
    exact hpoint x hx.le
  have hNBound : (∫ x : ℝ in Ioi 0, fN x) ≤
      thetaCuspTailDerivativeNatExpConstant 2 (p + R) *
        ((R : ℝ) ^ N / (p : ℝ) ^ (N + 1)) *
          Real.exp (((p + R : ℕ) : ℝ) * |a|) := by
    simpa only [fN, E] using
      integral_abs_thetaCuspTailDerivative_mul_shiftedFactorialEnvelope_le
        2 N p R hp ha
  have hN1Bound : (∫ x : ℝ in Ioi 0, fN1 x) ≤
      thetaCuspTailDerivativeNatExpConstant 2 (p + R) *
        ((R : ℝ) ^ N1 / (p : ℝ) ^ (N1 + 1)) *
          Real.exp (((p + R : ℕ) : ℝ) * |a|) := by
    simpa only [fN1, E] using
      integral_abs_thetaCuspTailDerivative_mul_shiftedFactorialEnvelope_le
        2 N1 p R hp ha
  calc
    (∫ x : ℝ in Ioi 0,
      |thetaCuspTailSecondDensity x| *
        ‖(finitePositivePhaseTranslationTopEdge d x a).derivative.eval z‖) ≤
      ∫ x : ℝ in Ioi 0, major x := by
      apply MeasureTheory.integral_mono_ae hminorInt hmajorInt
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact hpoint x hx.le
    _ = A * (∫ x : ℝ in Ioi 0, fN x) +
        B * (∫ x : ℝ in Ioi 0, fN1 x) := by
      dsimp only [major]
      rw [integral_add (hNInt.const_mul A) (hN1Int.const_mul B),
        integral_const_mul, integral_const_mul]
    _ ≤ A * (thetaCuspTailDerivativeNatExpConstant 2 (p + R) *
          ((R : ℝ) ^ N / (p : ℝ) ^ (N + 1)) *
            Real.exp (((p + R : ℕ) : ℝ) * |a|)) +
        B * (thetaCuspTailDerivativeNatExpConstant 2 (p + R) *
          ((R : ℝ) ^ N1 / (p : ℝ) ^ (N1 + 1)) *
            Real.exp (((p + R : ℕ) : ℝ) * |a|)) := by
      gcongr
    _ = _ := by
      dsimp only [A, B]

end

end RHTower
