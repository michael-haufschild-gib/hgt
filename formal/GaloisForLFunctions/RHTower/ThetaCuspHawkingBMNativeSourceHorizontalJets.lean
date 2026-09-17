import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativeCuspTransport

/-!
# Literal horizontal jets of the native source mean

The HB--B2 Peierls cap needs base-coordinate jets before any horizon-tail
estimate can be attempted.  This module records the exact first and second
horizontal jets of the *unmodified* native source circle mean and proves that
the transported cusp principal has no horizontal contribution.  It makes no
growth, cap-limit, QNM, or action assertion.

Proof-chain role:
`source horizontal jets -> differentiated radial Darboux estimate -> base-jet
tail bound -> corrected-future two-jet -> cyclic Peierls action/contact test`.
-/

namespace RHTower.D4BMNativeCircle

open Set Filter Topology MeasureTheory
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
open D4BMHorizon D4BMModularCore D4BMGlobalAngularResponse
open scoped ContDiff

noncomputable section
set_option autoImplicit false

private def horizontalParameterDerivative (F : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  deriv (fun t => F (t, p.2)) p.1

private theorem horizontalPartialSlice {F : ℝ × ℝ → ℂ} (hF : ContDiff ℝ ∞ F)
    (t theta : ℝ) :
    HasDerivAt (fun r => F (r, theta)) (fderiv ℝ F (t, theta) (1, 0)) t :=
  ((hF.contDiffAt.differentiableAt (by simp)).hasFDerivAt).comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t theta))

private theorem horizontalParameterDerivative_smooth {F : ℝ × ℝ → ℂ}
    (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (horizontalParameterDerivative F) := by
  have hdef : horizontalParameterDerivative F = fun p => fderiv ℝ F p (1, 0) :=
    funext fun p => (horizontalPartialSlice hF p.1 p.2).deriv
  rw [hdef]
  apply contDiff_iff_contDiffAt.mpr
  intro p
  exact (hF.contDiffAt.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const

private theorem average_horizontal_hasDerivAt {F : ℝ × ℝ → ℂ} (hF : ContDiff ℝ ∞ F)
    (t : ℝ) :
    HasDerivAt (fun r => average (fun theta => F (r, theta)))
      (average (fun theta => horizontalParameterDerivative F (t, theta))) t := by
  have hD := horizontalParameterDerivative_smooth hF
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (hD.continuous.continuousOn : ContinuousOn (horizontalParameterDerivative F)
      (Icc (t - 1) (t + 1) ×ˢ Icc 0 (2 * Real.pi)))
  have hN : Ioo (t - 1) (t + 1) ∈ 𝓝 t := Ioo_mem_nhds (by linarith) (by linarith)
  have hC0 (r : ℝ) : Continuous (fun theta => F (r, theta)) :=
    hF.continuous.comp (continuous_const.prodMk continuous_id)
  have hD0 (r : ℝ) : Continuous (fun theta => horizontalParameterDerivative F (r, theta)) :=
    hD.continuous.comp (continuous_const.prodMk continuous_id)
  have h := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioc 0 (2 * Real.pi)))
    (F := fun r theta => F (r, theta))
    (F' := fun r theta => horizontalParameterDerivative F (r, theta))
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
      exact (horizontalPartialSlice hF r theta).differentiableAt.hasDerivAt)).2
  exact h.const_mul (1 / (2 * Real.pi : ℂ))

private theorem sourceHorizontalFamily (q : XiZeroCopy) (d k : ℝ) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => source q d p.2 p.1 k) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  have hp : 0 < logCircle d p.2 p.1 k 1 := by
    dsimp [logCircle, circle, height]
    exact mul_pos (Real.exp_pos _) (one_div_pos.mpr (denominator_pos _ _))
  have hF : ContDiffAt ℝ ∞ (fullSquarePotential q) (logCircle d p.2 p.1 k) :=
    contDiffAt_infty.mpr (fun n => fullSquarePotential_smooth q _ hp n)
  apply hF.comp p
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i <;> dsimp [logCircle, circle, offset, height, denominator]
  all_goals fun_prop (disch := exact (denominator_pos _ _).ne')

/-- Literal first horizontal jet of the complete native source mean. -/
def sourceMeanHorizontalFirst (q : XiZeroCopy) (d X k : ℝ) : ℂ :=
  average (fun theta => deriv (fun x => source q d theta x k) X)

/-- Literal ordered second horizontal jet of the complete native source mean. -/
def sourceMeanHorizontalSecond (q : XiZeroCopy) (d X k : ℝ) : ℂ :=
  average (fun theta => deriv (deriv (fun x => source q d theta x k)) X)

/-- First horizontal differentiation commutes with the original finite native circle average. -/
theorem mean_horizontal_hasDerivAt (q : XiZeroCopy) (d X k : ℝ) :
    HasDerivAt (fun x => mean q d x k) (sourceMeanHorizontalFirst q d X k) X := by
  simpa only [mean, sourceMeanHorizontalFirst, horizontalParameterDerivative] using
    average_horizontal_hasDerivAt (sourceHorizontalFamily q d k) X

/-- Second horizontal differentiation commutes with the original finite native circle average. -/
theorem mean_horizontal_second_hasDerivAt (q : XiZeroCopy) (d X k : ℝ) :
    HasDerivAt (fun x => deriv (fun y => mean q d y k) x)
      (sourceMeanHorizontalSecond q d X k) X := by
  have hfirst : (fun x => deriv (fun y => mean q d y k) x) =
      fun x => sourceMeanHorizontalFirst q d x k :=
    funext fun x => (mean_horizontal_hasDerivAt q d x k).deriv
  rw [hfirst]
  simpa only [sourceMeanHorizontalFirst, sourceMeanHorizontalSecond,
    horizontalParameterDerivative] using
    average_horizontal_hasDerivAt
      (horizontalParameterDerivative_smooth (sourceHorizontalFamily q d k)) X

/-- The transported three-mode cusp principal contributes no horizontal jet;
the first native horizontal jet is therefore exactly a cusp-remainder jet. -/
theorem cuspMeanRemainder_horizontal_hasDerivAt (q : XiZeroCopy) (d X k : ℝ) :
    HasDerivAt (fun x => cuspMeanRemainder q d x k)
      (sourceMeanHorizontalFirst q d X k) X := by
  unfold cuspMeanRemainder
  exact (mean_horizontal_hasDerivAt q d X k).sub (hasDerivAt_const X _)

/-- The ordered second native horizontal jet is likewise entirely residual:
the transported cusp principal has zero horizontal first and second jet. -/
theorem cuspMeanRemainder_horizontal_second_hasDerivAt (q : XiZeroCopy) (d X k : ℝ) :
    HasDerivAt (fun x => deriv (fun y => cuspMeanRemainder q d y k) x)
      (sourceMeanHorizontalSecond q d X k) X := by
  have hfirst : (fun x => deriv (fun y => cuspMeanRemainder q d y k) x) =
      fun x => sourceMeanHorizontalFirst q d x k :=
    funext fun x => (cuspMeanRemainder_horizontal_hasDerivAt q d x k).deriv
  rw [hfirst]
  exact mean_horizontal_second_hasDerivAt q d X k

end

end RHTower.D4BMNativeCircle
