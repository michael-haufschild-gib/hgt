import GaloisForLFunctions.RHTower.BurnolSoninContinuousEvaluation
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Finite Mellin jets on the literal Burnol Sonine carrier

This module begins the missing higher-jet closure step for Burnol's extended
Sonine space.  It uses the literal Mellin kernel and will derive the finite
jet evaluators from dominated differentiation, rather than postulating their
boundedness.
-/

open Complex Real MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

/-- The first spectral derivative of the literal right Mellin kernel. -/
def soninMellinDerivativeKernel (w : ℂ) (t : ℝ) : ℂ :=
  -(Real.log t : ℂ) * soninMellinKernel w t

/-- Differentiating `t ↦ t^{-w}` in its spectral parameter produces the
literal logarithmic Mellin kernel. -/
theorem hasDerivAt_soninMellinKernel {t : ℝ} (ht : 0 < t) (w : ℂ) :
    HasDerivAt (fun z : ℂ => soninMellinKernel z t)
      (soninMellinDerivativeKernel w t) w := by
  have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht)
  change HasDerivAt (fun z : ℂ => (t : ℂ) ^ (-z)) _ w
  have h := (hasDerivAt_neg w).const_cpow (c := (t : ℂ)) (Or.inl ht0)
  convert h using 1
  dsimp only [soninMellinDerivativeKernel, soninMellinKernel]
  rw [Complex.ofReal_log ht.le]
  ring

/-- Exact norm of the first spectral derivative kernel. -/
theorem norm_soninMellinDerivativeKernel {t : ℝ} (ht : 0 < t) (w : ℂ) :
    ‖soninMellinDerivativeKernel w t‖ = |Real.log t| * t ^ (-w.re) := by
  rw [soninMellinDerivativeKernel, norm_mul, norm_neg, Complex.norm_real,
    norm_soninMellinKernel ht, Real.norm_eq_abs]

/-- Measurability of the first derivative kernel on the critical aperture tail. -/
theorem aestronglyMeasurable_soninMellinDerivativeKernel (w : ℂ) :
    AEStronglyMeasurable (soninMellinDerivativeKernel w)
      (volume.restrict (Ioi (1 : ℝ))) := by
  have hlog : AEStronglyMeasurable (fun t : ℝ => (Real.log t : ℂ))
      (volume.restrict (Ioi (1 : ℝ))) := by
    refine (Complex.continuous_ofReal.comp_continuousOn ?_).aestronglyMeasurable measurableSet_Ioi
    exact Real.continuousOn_log.mono
      (fun t ht => ne_of_gt (lt_trans zero_lt_one (mem_Ioi.mp ht)))
  have hkernel : AEStronglyMeasurable (soninMellinKernel w)
      (volume.restrict (Ioi (1 : ℝ))) :=
    aestronglyMeasurable_soninMellinKernel w measurableSet_Ioi
      (fun t ht => lt_trans zero_lt_one (mem_Ioi.mp ht))
  change AEStronglyMeasurable (fun t => -(Real.log t : ℂ) * soninMellinKernel w t)
    (volume.restrict (Ioi (1 : ℝ)))
  have hfun : (fun t : ℝ => -(Real.log t : ℂ) * soninMellinKernel w t) =
      (-fun t : ℝ => (Real.log t : ℂ)) * soninMellinKernel w := by
    funext t
    rfl
  rw [hfun]
  exact hlog.neg.mul hkernel

/-- The first logarithmic Mellin kernel remains square-integrable on the
critical aperture tail.  The strict right-strip margin absorbs the logarithm. -/
theorem memLp_soninMellinDerivativeKernel_Ioi_one {w : ℂ}
    (hlo : 1 / 2 < w.re) :
    MemLp (soninMellinDerivativeKernel w) 2 (volume.restrict (Ioi (1 : ℝ))) := by
  let delta : ℝ := (w.re - 1 / 2) / 2
  have hdelta : 0 < delta := by
    dsimp [delta]
    linarith
  let w' : ℂ := w - delta
  have hw' : 1 / 2 < w'.re := by
    dsimp [w', delta]
    norm_num
    linarith
  have hbase : MemLp (soninMellinKernel w') 2 (volume.restrict (Ioi (1 : ℝ))) :=
    memLp_soninMellinKernel_Ioi hw' zero_lt_one
  refine (hbase.const_mul ((delta⁻¹ : ℝ) : ℂ)).mono
    (aestronglyMeasurable_soninMellinDerivativeKernel w) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht1 : 1 < t := mem_Ioi.mp ht
  have ht0 : 0 < t := lt_trans zero_lt_one ht1
  rw [norm_soninMellinDerivativeKernel ht0, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (inv_nonneg.mpr hdelta.le), norm_soninMellinKernel ht0]
  rw [abs_of_nonneg (Real.log_nonneg ht1.le)]
  have hlog := Real.log_le_rpow_div (le_trans zero_le_one ht1.le) hdelta
  have hpow : 0 ≤ t ^ (-w.re) := Real.rpow_nonneg ht0.le _
  have hmul : Real.log t * t ^ (-w.re) ≤
      (t ^ delta / delta) * t ^ (-w.re) :=
    mul_le_mul_of_nonneg_right hlog hpow
  calc
    Real.log t * t ^ (-w.re) ≤ (t ^ delta / delta) * t ^ (-w.re) := hmul
    _ = delta⁻¹ * t ^ (-w'.re) := by
      rw [div_eq_mul_inv]
      calc
        t ^ delta * delta⁻¹ * t ^ (-w.re) = delta⁻¹ * (t ^ delta * t ^ (-w.re)) := by
          ring
        _ = delta⁻¹ * t ^ (delta + -w.re) := by rw [← Real.rpow_add ht0]
        _ = delta⁻¹ * t ^ (-w'.re) := by
          congr 2
          dsimp [w']
          norm_num
          ring

/-- A literal `L²` tail can be paired with the first derivative kernel. -/
theorem integrableOn_tail_mul_soninMellinDerivativeKernel {w : ℂ}
    (hlo : 1 / 2 < w.re) {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Ioi (0 : ℝ)))) :
    IntegrableOn (fun t => f t * soninMellinDerivativeKernel w t) (Ioi (1 : ℝ)) := by
  have hsub : (volume : Measure ℝ).restrict (Ioi (1 : ℝ)) =
      ((volume : Measure ℝ).restrict (Ioi (0 : ℝ))).restrict (Ioi (1 : ℝ)) := by
    rw [Measure.restrict_restrict measurableSet_Ioi,
      inter_eq_self_of_subset_left
        (fun t ht => mem_Ioi.mpr (lt_trans zero_lt_one (mem_Ioi.mp ht)))]
  have hf1 : MemLp f 2 (volume.restrict (Ioi (1 : ℝ))) := by
    rw [hsub]
    exact hf.restrict (Ioi 1)
  have hkernel : MemLp (soninMellinDerivativeKernel w) 2
      (volume.restrict (Ioi (1 : ℝ))) :=
    memLp_soninMellinDerivativeKernel_Ioi_one hlo
  exact (hf1.integrable_mul hkernel).congr (Filter.Eventually.of_forall fun t => rfl)

/-- A fixed strict strip margin gives one `L²` majorant for the first
derivative kernel throughout a spectral ball.  This is the local domination
needed for differentiation of the literal tail integral; no regularized
kernel is introduced. -/
theorem norm_soninMellinDerivativeKernel_le_tail_majorant
    {w z : ℂ} {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hz : z ∈ Metric.ball w epsilon) {t : ℝ} (ht : 1 < t) :
    ‖soninMellinDerivativeKernel z t‖ ≤
      epsilon⁻¹ * ‖soninMellinKernel (w - (2 * epsilon : ℝ)) t‖ := by
  have ht0 : 0 < t := lt_trans zero_lt_one ht
  have hdist : ‖w - z‖ < epsilon := by
    rw [Metric.mem_ball, dist_eq_norm] at hz
    calc
      ‖w - z‖ = ‖z - w‖ := by
        rw [← norm_neg (w - z)]
        congr 1
        ring
      _ < epsilon := hz
  have hlower : w.re - epsilon < z.re := by
    have h := (Complex.abs_re_le_norm (w - z)).trans_lt hdist
    rw [abs_lt] at h
    simp only [Complex.sub_re] at h
    linarith
  rw [norm_soninMellinDerivativeKernel ht0,
    norm_soninMellinKernel ht0]
  rw [abs_of_nonneg (Real.log_nonneg ht.le)]
  have hlog := Real.log_le_rpow_div (le_trans zero_le_one ht.le) hepsilon
  have hpow : 0 ≤ t ^ (-z.re) := Real.rpow_nonneg ht0.le _
  have hmul : Real.log t * t ^ (-z.re) ≤
      (t ^ epsilon / epsilon) * t ^ (-z.re) :=
    mul_le_mul_of_nonneg_right hlog hpow
  have hexp : -z.re ≤ -(w.re - epsilon) := by
    linarith
  have hmon : t ^ (-z.re) ≤ t ^ (-(w.re - epsilon)) :=
    Real.rpow_le_rpow_of_exponent_le ht.le hexp
  calc
    Real.log t * t ^ (-z.re) ≤ (t ^ epsilon / epsilon) * t ^ (-z.re) := hmul
    _ ≤ (t ^ epsilon / epsilon) * t ^ (-(w.re - epsilon)) := by
      exact mul_le_mul_of_nonneg_left hmon (by positivity)
    _ = epsilon⁻¹ * t ^ (-((w - (2 * epsilon : ℝ)).re)) := by
      rw [div_eq_mul_inv]
      calc
        t ^ epsilon * epsilon⁻¹ * t ^ (-(w.re - epsilon)) =
            epsilon⁻¹ * (t ^ epsilon * t ^ (-(w.re - epsilon))) := by ring
        _ = epsilon⁻¹ * t ^ (epsilon + -(w.re - epsilon)) := by
          rw [← Real.rpow_add ht0]
        _ = epsilon⁻¹ * t ^ (-((w - (2 * epsilon : ℝ)).re)) := by
          congr 2
          norm_num
          ring

/-- Literal tail Mellin transform based at the critical aperture `1`. -/
def soninMellinTailIntegral (f : SoninL2) (w : ℂ) : ℂ :=
  ∫ t in Ioi (1 : ℝ), f t * soninMellinKernel w t

/-- Differentiation under the literal Mellin tail integral.  The proof uses a
single nearby kernel with a strictly smaller real exponent as a common
majorant, so it is a genuine local analytic theorem rather than a pointwise
formal derivative. -/
theorem hasDerivAt_soninMellinTailIntegral {w : ℂ}
    (hlo : 1 / 2 < w.re) (f : SoninL2) :
    HasDerivAt (soninMellinTailIntegral f)
      (∫ t in Ioi (1 : ℝ), f t * soninMellinDerivativeKernel w t) w := by
  let epsilon : ℝ := (w.re - 1 / 2) / 4
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon]
    linarith
  let w' : ℂ := w - (2 * epsilon : ℝ)
  have hw' : 1 / 2 < w'.re := by
    dsimp [w', epsilon]
    norm_num
    linarith
  let bound : ℝ → ℝ := fun t => ‖f t‖ *
    (epsilon⁻¹ * ‖soninMellinKernel w' t‖)
  have hbound : Integrable bound (volume.restrict (Ioi (1 : ℝ))) := by
    have hf : MemLp (f : ℝ → ℂ) 2 (volume.restrict (Ioi (1 : ℝ))) := by
      have hrestrict := (memLp_restrict_Ioi f).restrict (Ioi (1 : ℝ))
      rw [Measure.restrict_restrict measurableSet_Ioi,
        inter_eq_self_of_subset_left
          (fun t ht => mem_Ioi.mpr (lt_trans zero_lt_one (mem_Ioi.mp ht)))] at hrestrict
      exact hrestrict
    have hk : MemLp (soninMellinKernel w') 2
        (volume.restrict (Ioi (1 : ℝ))) :=
      memLp_soninMellinKernel_Ioi hw' zero_lt_one
    have hprod : Integrable ((fun t => ‖f t‖) *
        (fun t => (epsilon⁻¹ : ℝ) * ‖soninMellinKernel w' t‖))
        (volume.restrict (Ioi (1 : ℝ))) :=
      hf.norm.integrable_mul (hk.norm.const_mul epsilon⁻¹)
    convert hprod using 1
    ext t
    simp only [bound, Pi.mul_apply]
  have hderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (1 : ℝ)))
    (F := fun z t => f t * soninMellinKernel z t)
    (F' := fun z t => f t * soninMellinDerivativeKernel z t)
    (x₀ := w) (bound := bound)
    (Metric.ball_mem_nhds w hepsilon)
    (Filter.Eventually.of_forall fun z =>
      ((Lp.aestronglyMeasurable f).restrict).mul
        (aestronglyMeasurable_soninMellinKernel z measurableSet_Ioi
          (fun t ht => lt_trans zero_lt_one (mem_Ioi.mp ht))))
    (integrableOn_tail_mul_kernel hlo zero_lt_one (memLp_restrict_Ioi f))
    (((Lp.aestronglyMeasurable f).restrict).mul
      (aestronglyMeasurable_soninMellinDerivativeKernel w))
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      intro z hz
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left
        (norm_soninMellinDerivativeKernel_le_tail_majorant hepsilon hz (mem_Ioi.mp ht))
        (norm_nonneg _))
    hbound
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      intro z hz
      exact (hasDerivAt_soninMellinKernel
        (lt_trans zero_lt_one (mem_Ioi.mp ht)) z).const_mul (f t))
  change HasDerivAt
    (fun z : ℂ => ∫ t in Ioi (1 : ℝ), (f : ℝ → ℂ) t * soninMellinKernel z t)
    (∫ t in Ioi (1 : ℝ), (f : ℝ → ℂ) t * soninMellinDerivativeKernel w t) w
  exact hderiv.2

/-- The bounded functional represented by the literal first logarithmic
kernel on the tail.  Conjugating the representing vector is forced by the
complex Hilbert-space convention; it is not a change of coefficient. -/
def soninMellinTailDerivativeEvaluation (w : ℂ)
    (hlo : 1 / 2 < w.re) : SoninL2 →L[ℂ] ℂ :=
  (innerSL ℂ
      ((memLp_soninMellinDerivativeKernel_Ioi_one hlo).star.toLp
        (star (soninMellinDerivativeKernel w)))).comp
    (LpToLpRestrictCLM ℝ ℂ ℂ (volume : Measure ℝ) 2 (Ioi (1 : ℝ)))

/-- The Hilbert representation evaluates to the literal tail derivative
integral. -/
theorem soninMellinTailDerivativeEvaluation_apply (w : ℂ)
    (hlo : 1 / 2 < w.re) (f : SoninL2) :
    soninMellinTailDerivativeEvaluation w hlo f =
      ∫ t in Ioi (1 : ℝ), (f : ℝ → ℂ) t * soninMellinDerivativeKernel w t := by
  rw [soninMellinTailDerivativeEvaluation, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [LpToLpRestrictCLM_coeFn ℂ (Ioi (1 : ℝ)) f,
    (memLp_soninMellinDerivativeKernel_Ioi_one hlo).star.coeFn_toLp] with t hf hk
  rw [RCLike.inner_apply, hf, hk]
  change (f : ℝ → ℂ) t * star (star (soninMellinDerivativeKernel w t)) =
    (f : ℝ → ℂ) t * soninMellinDerivativeKernel w t
  rw [star_star]

/-- The spectral derivative of the literal tail Mellin transform is a
continuous linear functional of the source vector. -/
theorem hasDerivAt_soninMellinTailIntegral_eq_tailDerivativeEvaluation {w : ℂ}
    (hlo : 1 / 2 < w.re) (f : SoninL2) :
    HasDerivAt (soninMellinTailIntegral f)
      (soninMellinTailDerivativeEvaluation w hlo f) w := by
  rw [soninMellinTailDerivativeEvaluation_apply]
  exact hasDerivAt_soninMellinTailIntegral hlo f

end RHTower
