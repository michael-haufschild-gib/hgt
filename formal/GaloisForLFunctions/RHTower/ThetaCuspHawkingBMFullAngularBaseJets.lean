import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullAngularCircleGreen

/-! Literal base-coordinate jets of the full circular response.

These are the actual `X` and logarithmic-height derivatives of the original
theta-circle average.  They are the angular diagonal entries used by the HB-B2
stream master.  No radial/time interchange with the seed tail, cap limit, or
left-QNM comparison is asserted here.
-/

namespace RHTower.D4BMFullAngularCircleBaseJets

open Set Filter Topology MeasureTheory
open scoped ContDiff
open D4BMHorizon D4BMModularCore D4BMGlobalAngularResponse D4BMNativeCircle D4BMCausalKernel
open D4BMFullAngularCircle

noncomputable section
set_option autoImplicit false

private def baseParameterDerivative (F : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  deriv (fun t => F (t, p.2)) p.1

private theorem basePartialSlice {F : ℝ × ℝ → ℂ} (hF : ContDiff ℝ ∞ F)
    (t theta : ℝ) :
    HasDerivAt (fun r => F (r, theta)) (fderiv ℝ F (t, theta) (1, 0)) t :=
  ((hF.contDiffAt.differentiableAt (by simp)).hasFDerivAt).comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t theta))

private theorem basePartialSmooth {F : ℝ × ℝ → ℂ} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (baseParameterDerivative F) := by
  have hdef : baseParameterDerivative F = fun p => fderiv ℝ F p (1, 0) :=
    funext fun p => (basePartialSlice hF p.1 p.2).deriv
  rw [hdef]
  apply contDiff_iff_contDiffAt.mpr
  intro p
  exact (hF.contDiffAt.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const

private theorem baseAverage_hasDerivAt {F : ℝ × ℝ → ℂ} (hF : ContDiff ℝ ∞ F)
    (t : ℝ) :
    HasDerivAt (fun r => D4BMNativeCircle.average (fun theta => F (r, theta)))
      (D4BMNativeCircle.average (fun theta => baseParameterDerivative F (t, theta))) t := by
  have hD := basePartialSmooth hF
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (hD.continuous.continuousOn : ContinuousOn (baseParameterDerivative F)
      (Icc (t - 1) (t + 1) ×ˢ Icc 0 (2 * Real.pi)))
  have hN : Ioo (t - 1) (t + 1) ∈ 𝓝 t := Ioo_mem_nhds (by linarith) (by linarith)
  have hC0 (r : ℝ) : Continuous (fun theta => F (r, theta)) :=
    hF.continuous.comp (continuous_const.prodMk continuous_id)
  have hD0 (r : ℝ) : Continuous (fun theta => baseParameterDerivative F (r, theta)) :=
    hD.continuous.comp (continuous_const.prodMk continuous_id)
  have h := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioc 0 (2 * Real.pi)))
    (F := fun r theta => F (r, theta))
    (F' := fun r theta => baseParameterDerivative F (r, theta))
    (bound := fun _ => C) hN
    (Filter.Eventually.of_forall fun r => (hC0 r).aestronglyMeasurable.restrict)
    ((hC0 t).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    ((hD0 t).aestronglyMeasurable.restrict)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with theta htheta
      intro r hr
      exact hC (r, theta) ⟨⟨hr.1.le, hr.2.le⟩, ⟨htheta.1.le, htheta.2⟩⟩)
    (integrable_const C)
    (by
      filter_upwards with theta
      intro r hr
      exact (basePartialSlice hF r theta).differentiableAt.hasDerivAt)).2
  exact h.const_mul (1 / (2 * Real.pi : ℂ))

private theorem horizontalFamily (q : XiZeroCopy) (branch : Bool) (d k : ℝ) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => angularSource q branch d p.2 p.1 k) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  have hp : 0 < logCircle d p.2 p.1 k 1 := by
    dsimp [logCircle, circle, height]
    exact mul_pos (Real.exp_pos _) (one_div_pos.mpr (denominator_pos _ _))
  have hF := fullAngularField_smooth q branch (logCircle d p.2 p.1 k) hp
  apply hF.comp p
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i <;> dsimp [logCircle, circle, offset, height, denominator]
  all_goals fun_prop (disch := exact (denominator_pos _ _).ne')

private theorem heightFamily (q : XiZeroCopy) (branch : Bool) (d X : ℝ) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => angularSource q branch d p.2 X p.1) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  have hp : 0 < logCircle d p.2 X p.1 1 := by
    dsimp [logCircle, circle, height]
    exact mul_pos (Real.exp_pos _) (one_div_pos.mpr (denominator_pos _ _))
  have hF := fullAngularField_smooth q branch (logCircle d p.2 X p.1) hp
  apply hF.comp p
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i <;> dsimp [logCircle, circle, offset, height, denominator]
  all_goals fun_prop (disch := exact (denominator_pos _ _).ne')

/-- Literal horizontal derivative of the full theta-circle response. -/
def angularMeanHorizontalFirst (q : XiZeroCopy) (branch : Bool) (d X k : ℝ) : ℂ :=
  D4BMNativeCircle.average
    (fun theta => deriv (fun x => angularSource q branch d theta x k) X)

/-- Literal ordered horizontal second derivative of the full theta-circle response. -/
def angularMeanHorizontalSecond (q : XiZeroCopy) (branch : Bool) (d X k : ℝ) : ℂ :=
  D4BMNativeCircle.average
    (fun theta => deriv (deriv (fun x => angularSource q branch d theta x k)) X)

/-- Literal logarithmic-height derivative of the full theta-circle response. -/
def angularMeanHeightFirst (q : XiZeroCopy) (branch : Bool) (d X k : ℝ) : ℂ :=
  D4BMNativeCircle.average
    (fun theta => deriv (fun u => angularSource q branch d theta X u) k)

/-- Literal ordered logarithmic-height second derivative of the full theta-circle response. -/
def angularMeanHeightSecond (q : XiZeroCopy) (branch : Bool) (d X k : ℝ) : ℂ :=
  D4BMNativeCircle.average
    (fun theta => deriv (deriv (fun u => angularSource q branch d theta X u)) k)

/-- HB-B2 angular master input: the full circle mean has its actual horizontal first jet. -/
theorem angularMean_horizontal_hasDerivAt (q : XiZeroCopy) (branch : Bool) (d X k : ℝ) :
    HasDerivAt (fun x => angularMean q branch d x k)
      (angularMeanHorizontalFirst q branch d X k) X := by
  simpa only [angularMean, angularMeanHorizontalFirst, baseParameterDerivative]
    using baseAverage_hasDerivAt (horizontalFamily q branch d k) X

/-- HB-B2 angular master input: the full circle mean has its actual horizontal second jet. -/
theorem angularMean_horizontal_second_hasDerivAt (q : XiZeroCopy) (branch : Bool)
    (d X k : ℝ) :
    HasDerivAt (fun x => deriv (fun y => angularMean q branch d y k) x)
      (angularMeanHorizontalSecond q branch d X k) X := by
  have hfirst : (fun x => deriv (fun y => angularMean q branch d y k) x) =
      fun x => angularMeanHorizontalFirst q branch d x k :=
    funext fun x => (angularMean_horizontal_hasDerivAt q branch d x k).deriv
  rw [hfirst]
  simpa only [angularMeanHorizontalFirst, angularMeanHorizontalSecond,
    baseParameterDerivative] using
    baseAverage_hasDerivAt (basePartialSmooth (horizontalFamily q branch d k)) X

/-- HB-B2 angular master input: the full circle mean has its actual height first jet. -/
theorem angularMean_height_hasDerivAt (q : XiZeroCopy) (branch : Bool) (d X k : ℝ) :
    HasDerivAt (fun u => angularMean q branch d X u)
      (angularMeanHeightFirst q branch d X k) k := by
  simpa only [angularMean, angularMeanHeightFirst, baseParameterDerivative]
    using baseAverage_hasDerivAt (heightFamily q branch d X) k

/-- HB-B2 angular master input: the full circle mean has its actual height second jet. -/
theorem angularMean_height_second_hasDerivAt (q : XiZeroCopy) (branch : Bool)
    (d X k : ℝ) :
    HasDerivAt (fun u => deriv (fun v => angularMean q branch d X v) u)
      (angularMeanHeightSecond q branch d X k) k := by
  have hfirst : (fun u => deriv (fun v => angularMean q branch d X v) u) =
      fun u => angularMeanHeightFirst q branch d X u :=
    funext fun u => (angularMean_height_hasDerivAt q branch d X u).deriv
  rw [hfirst]
  simpa only [angularMeanHeightFirst, angularMeanHeightSecond,
    baseParameterDerivative] using
    baseAverage_hasDerivAt (basePartialSmooth (heightFamily q branch d X)) k

end
end RHTower.D4BMFullAngularCircleBaseJets
