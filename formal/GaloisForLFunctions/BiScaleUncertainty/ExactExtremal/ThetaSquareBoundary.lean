import GaloisForLFunctions.BiScaleUncertainty.ExactExtremal.PowerDivisorCapacity
import GaloisForLFunctions.RHTower.ThetaTailCapacitySharpness
import Mathlib.Analysis.Convolution

/-!
# The theta square attains the full squared-divisor capacity

Convolving the literal theta source with itself gives transform `Ξ²` and
double-exponential exponent one. The multiplicity bound excludes every larger
exponent. This source is strictly positive at every point, including every
integer logarithm: sharp divisor capacity alone does not produce blindness.
-/

open MeasureTheory Set Filter Topology Complex

namespace GaloisForLFunctions.BiScaleUncertainty.ExactExtremal

open _root_.RHTower

noncomputable section

/-- The convolution of two completed theta sources. -/
def thetaSquareSource : ℝ → ℂ :=
  convolution thetaSourceC thetaSourceC (ContinuousLinearMap.mul ℝ ℂ) volume

private theorem theta_bound : ∃ A : ℝ, 0 ≤ A ∧ ∀ x,
    ‖thetaSourceC x‖ ≤ A * Real.exp (-Real.exp (2 * |x|)) := by
  obtain ⟨A, hA⟩ := exists_norm_thetaCapacityPacket_le 0 1
    (a := 1) (by linarith [Real.pi_gt_three])
  have hbound : ∀ x, ‖thetaSourceC x‖ ≤ A * Real.exp (-Real.exp (2 * |x|)) := by
    intro x
    simpa [thetaCapacityPacket, thetaDerivSourceC, thetaSourceC] using hA x
  refine ⟨A, ?_, hbound⟩
  exact nonneg_of_mul_nonneg_left ((norm_nonneg _).trans (hbound 0)) (Real.exp_pos _)

private theorem theta_bounded : BddAbove (range fun x => ‖thetaSourceC x‖) := by
  obtain ⟨A, hA, hbound⟩ := theta_bound
  refine ⟨A, ?_⟩
  rintro _ ⟨x, rfl⟩
  exact (hbound x).trans (mul_le_of_le_one_right hA
    (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Real.exp_pos _).le)))

theorem continuous_thetaSquareSource : Continuous thetaSquareSource :=
  theta_bounded.continuous_convolution_left_of_integrable (ContinuousLinearMap.mul ℝ ℂ)
    expMomentSource_thetaSourceC.continuous expMomentSource_thetaSourceC.integrable

private theorem integrable_theta_product (x : ℝ) :
    Integrable (fun t => thetaSourceC t * thetaSourceC (x - t)) := by
  obtain ⟨A, hA⟩ := theta_bounded
  have hc : Continuous (fun t => thetaSourceC t * thetaSourceC (x - t)) :=
    expMomentSource_thetaSourceC.continuous.mul
      (expMomentSource_thetaSourceC.continuous.comp (continuous_const.sub continuous_id))
  refine (expMomentSource_thetaSourceC.integrable.norm.mul_const A).mono'
    hc.aestronglyMeasurable (Eventually.of_forall fun t => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hA (mem_range_self (x - t))) (norm_nonneg _)

/-- The source is strictly positive; no nonzero logarithm is a blind node. -/
theorem thetaSquareSource_re_pos (x : ℝ) : 0 < (thetaSquareSource x).re := by
  have hi := integrable_theta_product x
  have hr : Integrable (fun t => thetaCuspFullSource t * thetaCuspFullSource (x - t)) := by
    simpa only [RCLike.re_eq_complex_re, thetaSourceC, ← Complex.ofReal_mul,
      Complex.ofReal_re] using hi.re
  have hpos : ∀ t, 0 < thetaCuspFullSource t * thetaCuspFullSource (x - t) :=
    fun t => mul_pos (thetaCuspFullSource_pos t) (thetaCuspFullSource_pos (x - t))
  have hmass : 0 < ∫ t, thetaCuspFullSource t * thetaCuspFullSource (x - t) := by
    rw [integral_pos_iff_support_of_nonneg (fun t => (hpos t).le) hr]
    have hs : Function.support (fun t => thetaCuspFullSource t * thetaCuspFullSource (x - t)) =
        univ := Set.eq_univ_of_forall fun t => (hpos t).ne'
    rw [hs, Real.volume_univ]
    exact ENNReal.zero_lt_top
  have hre := integral_re hi
  simp only [RCLike.re_eq_complex_re, thetaSourceC, ← Complex.ofReal_mul,
    Complex.ofReal_re] at hre
  simpa only [thetaSquareSource, convolution_def, ContinuousLinearMap.mul_apply', thetaSourceC,
    Complex.ofReal_mul]
    using hmass.trans_eq hre

/-- Exponential twisting commutes with convolution, so the transform is exactly `Ξ²`. -/
theorem sourceTransform_thetaSquareSource (z : ℂ) :
    sourceTransform thetaSquareSource z = XiC z ^ 2 := by
  let f : ℝ → ℂ := fun t => cexp (-I * z * t) * thetaSourceC t
  have hf : Integrable f := expMomentSource_thetaSourceC.integrable_cexp z
  have htwist : ∀ x, convolution f f (ContinuousLinearMap.mul ℝ ℂ) volume x =
      cexp (-I * z * x) * thetaSquareSource x := by
    intro x
    rw [convolution_def, thetaSquareSource, convolution_def, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with t
    simp only [ContinuousLinearMap.mul_apply', f]
    have he : cexp (-I * z * t) * cexp (-I * z * ((x - t : ℝ) : ℂ)) =
        cexp (-I * z * x) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    calc
      (cexp (-I * z * t) * thetaSourceC t) *
          (cexp (-I * z * ((x - t : ℝ) : ℂ)) * thetaSourceC (x - t)) =
          (cexp (-I * z * t) * cexp (-I * z * ((x - t : ℝ) : ℂ))) *
            (thetaSourceC t * thetaSourceC (x - t)) := by ring
      _ = _ := by rw [he]
  unfold sourceTransform
  simp_rw [← htwist]
  rw [integral_convolution (ContinuousLinearMap.mul ℝ ℂ) hf hf]
  change sourceTransform thetaSourceC z * sourceTransform thetaSourceC z = _
  rw [sourceTransform_thetaSourceC, pow_two]

/-- The theta square has the boundary exponent one. -/
theorem exists_thetaSquareSource_bound : ∃ C : ℝ, ∀ x,
    ‖thetaSquareSource x‖ ≤ C * Real.exp (-Real.exp |x|) := by
  obtain ⟨A, hA, hbound⟩ := theta_bound
  let v : ℝ → ℝ := fun t => Real.exp (-(1 / 2 : ℝ) * Real.exp (2 * |t|))
  have hv : Integrable v := integrable_exp_neg_doubleExp (by positivity) (by positivity)
  refine ⟨A ^ 2 * ∫ t, v t, fun x => ?_⟩
  have hpt : ∀ t, ‖thetaSourceC t * thetaSourceC (x - t)‖ ≤
      (A ^ 2 * Real.exp (-Real.exp |x|)) * v t := by
    intro t
    have htri : |x| ≤ |t| + |x - t| := by
      calc |x| = |t + (x - t)| := by congr 1; ring
        _ ≤ |t| + |x - t| := abs_add_le _ _
    have hprod : Real.exp |x| ≤ Real.exp |t| * Real.exp |x - t| := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr htri
    have hsq (y : ℝ) : Real.exp (2 * |y|) = Real.exp |y| ^ 2 := by
      rw [show 2 * |y| = |y| + |y| by ring, Real.exp_add, pow_two]
    have hsum : Real.exp |x| + Real.exp (2 * |t|) / 2 ≤
        Real.exp (2 * |t|) + Real.exp (2 * |x - t|) := by
      rw [hsq, hsq]
      nlinarith [sq_nonneg (Real.exp |t| - Real.exp |x - t|), sq_nonneg (Real.exp |x - t|)]
    rw [norm_mul]
    calc
      ‖thetaSourceC t‖ * ‖thetaSourceC (x - t)‖ ≤
          (A * Real.exp (-Real.exp (2 * |t|))) *
            (A * Real.exp (-Real.exp (2 * |x - t|))) :=
        mul_le_mul (hbound t) (hbound (x - t)) (norm_nonneg _) (by positivity)
      _ = A ^ 2 * Real.exp (-Real.exp (2 * |t|) - Real.exp (2 * |x - t|)) := by
        simp only [Real.exp_sub, Real.exp_neg]
        ring
      _ ≤ A ^ 2 * Real.exp (-Real.exp |x| - Real.exp (2 * |t|) / 2) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (sq_nonneg A)
      _ = (A ^ 2 * Real.exp (-Real.exp |x|)) * v t := by
        dsimp only [v]
        rw [show -Real.exp |x| - Real.exp (2 * |t|) / 2 =
          -Real.exp |x| + (-(1 / 2 : ℝ) * Real.exp (2 * |t|)) by ring, Real.exp_add]
        ring
  rw [thetaSquareSource, convolution_def]
  have hn := norm_integral_le_of_norm_le
    (hv.const_mul (A ^ 2 * Real.exp (-Real.exp |x|))) (Eventually.of_forall hpt)
  simp only [ContinuousLinearMap.mul_apply']
  refine hn.trans_eq ?_
  rw [integral_const_mul]
  ring

/-- A strictly positive node value rules out integer blindness at every node. -/
theorem thetaSquareSource_log_ne_zero (n : ℕ) : thetaSquareSource (Real.log n) ≠ 0 := by
  intro h
  have := thetaSquareSource_re_pos (Real.log n)
  rw [h, Complex.zero_re] at this
  exact (lt_irrefl 0) this

/-- The boundary example admits no double-exponential tail with exponent greater than one. -/
theorem not_faster_thetaSquareSource {a b C : ℝ} (ha : 0 < a) (hb : 1 < b) :
    ¬ ∀ x, ‖thetaSquareSource x‖ ≤ C * Real.exp (-a * Real.exp (b * |x|)) := by
  intro hbound
  have hz := ae_eq_zero_of_doubleExp_XiC_pow_divisor
    continuous_thetaSquareSource.aestronglyMeasurable ha (by linarith : 0 < b)
    (k := 2) (by norm_num; linarith) hbound (fun z => by
      have hfun : sourceTransform thetaSquareSource = fun w => XiC w ^ 2 :=
        funext sourceTransform_thetaSquareSource
      rw [hfun])
  have heq : thetaSquareSource = 0 :=
    (continuous_thetaSquareSource.ae_eq_iff_eq volume continuous_const).mp hz
  exact thetaSquareSource_log_ne_zero 1 (by simpa using congrFun heq (Real.log 1))

end

end GaloisForLFunctions.BiScaleUncertainty.ExactExtremal

