import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullAngularCircleGreen

/-! Literal radial--base mixed jets of the full circular response.

These are the `dX` and `dk` entries of the actual full theta-circle mean.  They
are needed by the HB-B2 stream current.  This file proves only pointwise
derivative identities; it asserts neither a global tail bound nor interchange
with seed transport, cap limits, or the left-QNM contact comparison.
-/

namespace RHTower.D4BMFullAngularCircleMixedJets

open Set Filter Topology MeasureTheory
open scoped ContDiff
open D4BMHorizon D4BMModularCore D4BMGlobalAngularResponse D4BMNativeCircle D4BMCausalKernel
open D4BMFullAngularCircle

noncomputable section
set_option autoImplicit false

private def circleSource (q : XiZeroCopy) (branch : Bool) (d theta X k : ℝ) : ℂ :=
  fullAngularField q branch (logCircle d theta X k)

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
      (D4BMNativeCircle.average
        (fun theta => baseParameterDerivative F (t, theta))) t := by
  have hD := basePartialSmooth hF
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (hD.continuous.continuousOn : ContinuousOn (baseParameterDerivative F)
      (Icc (t - 1) (t + 1) ×ˢ Icc 0 (2 * Real.pi)))
  have hN : Ioo (t - 1) (t + 1) ∈ 𝓝 t := Ioo_mem_nhds (by linarith) (by linarith)
  have hC0 (r : ℝ) : Continuous (fun theta => F (r, theta)) :=
    hF.continuous.comp (continuous_const.prodMk continuous_id)
  have hD0 (r : ℝ) : Continuous
      (fun theta => baseParameterDerivative F (r, theta)) :=
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

private def radialParameterDerivative {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (F : ℝ × P → ℂ) (d : ℝ) (p : P) : ℂ :=
  deriv (fun r => F (r, p)) d

private theorem radialParameterDerivative_smooth {P : Type*} [NormedAddCommGroup P]
    [NormedSpace ℝ P] (F : ℝ × P → ℂ) (d : ℝ) (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (radialParameterDerivative F d) := by
  have hd : ContDiff ℝ ∞ (fun p : P => (d, p)) :=
    contDiff_const.prodMk contDiff_id
  have hdf : ContDiff ℝ ∞ (fun p : P => fderiv ℝ F (d, p)) := by
    apply contDiff_iff_contDiffAt.mpr
    intro p
    exact ((hF.contDiffAt.fderiv_right (m := ∞) (by simp)).comp p hd.contDiffAt)
  have hdef : radialParameterDerivative F d =
      fun p => fderiv ℝ F (d, p) (1, 0) := by
    funext p
    exact ((hF.contDiffAt.differentiableAt (by simp)).hasFDerivAt).comp_hasDerivAt d
      ((hasDerivAt_id d).prodMk (hasDerivAt_const d p)) |>.deriv
  rw [hdef]
  exact hdf.clm_apply contDiff_const

private theorem radialHorizontalSourceFamily (q : XiZeroCopy) (branch : Bool) (k : ℝ) :
    ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) =>
      circleSource q branch p.1 p.2.2 p.2.1 k) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  have hp : 0 < logCircle p.1 p.2.2 p.2.1 k 1 := by
    dsimp [logCircle, circle, height]
    exact mul_pos (Real.exp_pos _) (one_div_pos.mpr (denominator_pos _ _))
  have hF := fullAngularField_smooth q branch (logCircle p.1 p.2.2 p.2.1 k) hp
  apply hF.comp p
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i <;> dsimp [logCircle, circle, offset, height, denominator]
  all_goals fun_prop (disch := exact (denominator_pos _ _).ne')

private theorem radialHeightSourceFamily (q : XiZeroCopy) (branch : Bool) (X : ℝ) :
    ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) =>
      circleSource q branch p.1 p.2.2 X p.2.1) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  have hp : 0 < logCircle p.1 p.2.2 X p.2.1 1 := by
    dsimp [logCircle, circle, height]
    exact mul_pos (Real.exp_pos _) (one_div_pos.mpr (denominator_pos _ _))
  have hF := fullAngularField_smooth q branch (logCircle p.1 p.2.2 X p.2.1) hp
  apply hF.comp p
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i <;> dsimp [logCircle, circle, offset, height, denominator]
  all_goals fun_prop (disch := exact (denominator_pos _ _).ne')

private theorem radialSliceFamily (q : XiZeroCopy) (branch : Bool) (X k : ℝ) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => circleSource q branch p.1 p.2 X k) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  have hp : 0 < logCircle p.1 p.2 X k 1 := by
    dsimp [logCircle, circle, height]
    exact mul_pos (Real.exp_pos _) (one_div_pos.mpr (denominator_pos _ _))
  have hF := fullAngularField_smooth q branch (logCircle p.1 p.2 X k) hp
  apply hF.comp p
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i <;> dsimp [logCircle, circle, offset, height, denominator]
  all_goals fun_prop (disch := exact (denominator_pos _ _).ne')

def angularMeanRadialHorizontal (q : XiZeroCopy) (branch : Bool)
    (d X k : ℝ) : ℂ :=
  D4BMNativeCircle.average (fun theta =>
    deriv (fun x => deriv (fun r =>
      fullAngularField q branch (logCircle r theta x k)) d) X)

def angularMeanRadialHeight (q : XiZeroCopy) (branch : Bool)
    (d X k : ℝ) : ℂ :=
  D4BMNativeCircle.average (fun theta =>
    deriv (fun u => deriv (fun r =>
      fullAngularField q branch (logCircle r theta X u)) d) k)

private theorem angularMean_radial_eq_average (q : XiZeroCopy) (branch : Bool)
    (d X k : ℝ) :
    deriv (fun r => angularMean q branch r X k) d =
      D4BMNativeCircle.average (fun theta =>
        deriv (fun r => circleSource q branch r theta X k) d) := by
  simpa only [angularMean, circleSource] using
    (baseAverage_hasDerivAt (radialSliceFamily q branch X k) d).deriv

/-- Literal radial--horizontal mixed jet of the full circular response. -/
theorem angularMean_radial_horizontal_hasDerivAt (q : XiZeroCopy) (branch : Bool)
    (d X k : ℝ) :
    HasDerivAt (fun x => deriv (fun r => angularMean q branch r x k) d)
      (angularMeanRadialHorizontal q branch d X k) X := by
  let F : ℝ × ℝ → ℂ := radialParameterDerivative
    (fun p : ℝ × (ℝ × ℝ) => circleSource q branch p.1 p.2.2 p.2.1 k) d
  have hF : ContDiff ℝ ∞ F := by
    dsimp only [F]
    exact radialParameterDerivative_smooth _ d (radialHorizontalSourceFamily q branch k)
  have h := baseAverage_hasDerivAt hF X
  have he (x : ℝ) :
      D4BMNativeCircle.average (fun theta => F (x, theta)) =
        deriv (fun r => angularMean q branch r x k) d := by
    rw [angularMean_radial_eq_average]
    rfl
  rw [show (fun x => deriv (fun r => angularMean q branch r x k) d) =
      fun x => D4BMNativeCircle.average (fun theta => F (x, theta)) by
        funext x; exact (he x).symm]
  simpa only [F, circleSource, radialParameterDerivative, angularMeanRadialHorizontal,
    baseParameterDerivative] using h

/-- Literal radial--log-height mixed jet of the full circular response. -/
theorem angularMean_radial_height_hasDerivAt (q : XiZeroCopy) (branch : Bool)
    (d X k : ℝ) :
    HasDerivAt (fun u => deriv (fun r => angularMean q branch r X u) d)
      (angularMeanRadialHeight q branch d X k) k := by
  let F : ℝ × ℝ → ℂ := radialParameterDerivative
    (fun p : ℝ × (ℝ × ℝ) => circleSource q branch p.1 p.2.2 X p.2.1) d
  have hF : ContDiff ℝ ∞ F := by
    dsimp only [F]
    exact radialParameterDerivative_smooth _ d (radialHeightSourceFamily q branch X)
  have h := baseAverage_hasDerivAt hF k
  have he (u : ℝ) :
      D4BMNativeCircle.average (fun theta => F (u, theta)) =
        deriv (fun r => angularMean q branch r X u) d := by
    rw [angularMean_radial_eq_average]
    rfl
  rw [show (fun u => deriv (fun r => angularMean q branch r X u) d) =
      fun u => D4BMNativeCircle.average (fun theta => F (u, theta)) by
        funext u; exact (he u).symm]
  simpa only [F, circleSource, radialParameterDerivative, angularMeanRadialHeight,
    baseParameterDerivative] using h

end
end RHTower.D4BMFullAngularCircleMixedJets
