import GaloisForLFunctions.RHTower.PaperThetaBoundedResolvent
import GaloisForLFunctions.HTGeometry.BoundedContinuousUniformTailCompactness
import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative

/-! # Compactness of the actual theta Green operator

The source ratio supplies uniform two-ended tails; the literal differential
equation supplies local equicontinuity. Together they give compactness in the
original global supremum norm on all bounded continuous forcing.
-/

noncomputable section
open Set Filter Topology Complex
open scoped BoundedContinuousFunction

namespace RHTower.PaperThetaEndpoint

def boundedNativeResidual (z : ThetaRegularParameter) :
    NativeContinuousSpace →L[ℂ] NativeContinuousSpace :=
  boundedNativeResolvent z-nativeConstantCLM.comp (boundedResolventTrace z)

@[simp] theorem boundedNativeResidual_apply (z : ThetaRegularParameter)
    (g : NativeContinuousSpace) (x : ℝ) :
    boundedNativeResidual z g x = I*boundedThetaTail z (boundedResolventAdjusted z g) x := by
  change (boundedResolventTrace z g+I*boundedThetaTail z (boundedResolventAdjusted z g) x)-
    boundedResolventTrace z g = _
  ring

theorem hasDerivAt_boundedNativeResidual (z : ThetaRegularParameter)
    (g : NativeContinuousSpace) (x : ℝ) :
    HasDerivAt (boundedNativeResidual z g)
      (-(sourceLogDerivative x+I*z.val)*boundedNativeResidual z g x-
        I*boundedResolventAdjusted z g x) x := by
  have h := (hasDerivAt_boundedThetaTail z (boundedResolventAdjusted z g) x).const_mul I
  rw [show (boundedNativeResidual z g : ℝ → ℂ) =
    (fun y => I*boundedThetaTail z (boundedResolventAdjusted z g) y) from
    funext (boundedNativeResidual_apply z g)]
  exact h.congr_deriv (by ring)

theorem norm_clm_apply_unit (T : NativeContinuousSpace →L[ℂ] NativeContinuousSpace)
    {g : NativeContinuousSpace} (hg : ‖g‖ ≤ 1) (x : ℝ) : ‖T g x‖ ≤ ‖T‖ :=
  ((T g).norm_coe_le_norm x).trans ((T.le_opNorm g).trans
    (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hg (norm_nonneg T)))

theorem boundedNativeResidual_equicontinuous (z : ThetaRegularParameter) :
    Equicontinuous (fun g : Metric.closedBall (0 : NativeContinuousSpace) 1 =>
      (boundedNativeResidual z g.val : ℝ → ℂ)) := by
  intro a
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (a-1) (a+1)) continuous_sourceLogDerivative.continuousOn
  let L := (max B 0+‖z.val‖)*‖boundedNativeResidual z‖+‖boundedResolventAdjusted z‖
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hderiv (g : Metric.closedBall (0 : NativeContinuousSpace) 1)
      (x : ℝ) (hx : x ∈ Icc (a-1) (a+1)) :
      ‖deriv (boundedNativeResidual z g.val) x‖ ≤ L := by
    have hg : ‖g.val‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using g.property
    rw [(hasDerivAt_boundedNativeResidual z g.val x).deriv]
    calc
      _ ≤ ‖sourceLogDerivative x+I*z.val‖*‖boundedNativeResidual z g.val x‖+
          ‖boundedResolventAdjusted z g.val x‖ := by
        simpa only [norm_mul, norm_neg, norm_I, one_mul] using
          norm_sub_le (-(sourceLogDerivative x+I*z.val)*boundedNativeResidual z g.val x)
            (I*boundedResolventAdjusted z g.val x)
      _ ≤ (max B 0+‖z.val‖)*‖boundedNativeResidual z‖+‖boundedResolventAdjusted z‖ := by
        apply add_le_add _ (norm_clm_apply_unit _ hg x)
        apply mul_le_mul _ (norm_clm_apply_unit _ hg x) (norm_nonneg _) (by positivity)
        exact (norm_add_le _ _).trans (add_le_add ((hB x hx).trans (le_max_left _ _))
          (by simp only [norm_mul, norm_I, one_mul, le_refl]))
  rw [Metric.equicontinuousAt_iff]
  intro ε hε
  refine ⟨min 1 (ε/(L+1)), lt_min zero_lt_one (div_pos hε (by linarith)), ?_⟩
  intro x hx g
  have hx1 : |x-a| < 1 := by
    exact lt_of_lt_of_le (by simpa only [Real.dist_eq] using hx) (min_le_left _ _)
  have hxI : x ∈ Icc (a-1) (a+1) := by
    constructor <;> linarith [(abs_lt.mp hx1).1, (abs_lt.mp hx1).2]
  have hd := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun y (_ : y ∈ Icc (a-1) (a+1)) =>
      (hasDerivAt_boundedNativeResidual z g.val y).differentiableAt)
    (hderiv g) (convex_Icc (a-1) (a+1))
    (show a ∈ Icc (a-1) (a+1) from ⟨by linarith, by linarith⟩) hxI
  have hxε : ‖x-a‖ < ε/(L+1) := by
    simpa only [Real.dist_eq, Real.norm_eq_abs] using hx.trans_le (min_le_right _ _)
  have hsmall : L*‖x-a‖ < ε := by
    have h := (lt_div_iff₀ (by linarith : 0 < L+1)).mp hxε
    nlinarith [norm_nonneg (x-a)]
  rw [dist_comm, dist_eq_norm]
  exact hd.trans_lt hsmall

theorem boundedNativeResidual_uniform_tails (z : ThetaRegularParameter) :
    ∀ ε > (0 : ℝ), ∃ R : ℝ, ∀ g : NativeContinuousSpace, ‖g‖ ≤ 1 →
      ∀ x, R ≤ |x| → ‖boundedNativeResidual z g x‖ ≤ ε := by
  intro ε hε
  have hp : Tendsto (fun x => ‖boundedResolventAdjusted z‖*forcedTailMass z x) atTop (𝓝 0) := by
    simpa using (tendsto_forcedTailMass z).const_mul ‖boundedResolventAdjusted z‖
  have hn : Tendsto (fun x => ‖boundedResolventAdjusted z‖*forcedTailMass (-z.val) x)
      atTop (𝓝 0) := by
    simpa using (tendsto_forcedTailMass (-z.val)).const_mul ‖boundedResolventAdjusted z‖
  obtain ⟨p, hp⟩ := eventually_atTop.1 (hp.eventually (gt_mem_nhds hε))
  obtain ⟨n, hn⟩ := eventually_atTop.1 (hn.eventually (gt_mem_nhds hε))
  refine ⟨max p n, ?_⟩
  intro g hg x hx
  have hadj : ‖boundedResolventAdjusted z g‖ ≤ ‖boundedResolventAdjusted z‖ :=
    ((boundedResolventAdjusted z).le_opNorm g).trans
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hg (norm_nonneg _))
  rw [boundedNativeResidual_apply, norm_mul, norm_I, one_mul]
  by_cases hx0 : 0 ≤ x
  · have hpx : p ≤ x := (le_max_left p n).trans (by simpa only [abs_of_nonneg hx0] using hx)
    exact (norm_boundedThetaTail_le z _ x).trans ((mul_le_mul_of_nonneg_right hadj
      (forcedTailMass_nonneg _ _)).trans (hp x hpx).le)
  · have hnx : n ≤ -x := (le_max_right p n).trans
      (by simpa only [abs_of_nonpos (le_of_not_ge hx0)] using hx)
    exact (norm_boundedThetaTail_left_le (boundedResolventAdjusted_moment z g) x).trans
      ((mul_le_mul_of_nonneg_right hadj (forcedTailMass_nonneg _ _)).trans (hn (-x) hnx).le)

theorem isCompactOperator_boundedNativeResidual (z : ThetaRegularParameter) :
    IsCompactOperator (boundedNativeResidual z) := by
  apply (isCompactOperator_iff_isCompact_closure_image_closedBall
    (boundedNativeResidual z).toLinearMap zero_lt_one).mpr
  apply HTGeometry.isCompact_closure_bcf_of_uniform_tails
    ((boundedNativeResidual z) '' Metric.closedBall (0 : NativeContinuousSpace) 1)
    (M := ‖boundedNativeResidual z‖)
  · rintro f ⟨g, hg, rfl⟩ x
    exact norm_clm_apply_unit _ (by simpa only [Metric.mem_closedBall, dist_zero_right] using hg) x
  · intro x
    rw [Metric.equicontinuousAt_iff_right] at ⊢
    intro ε hε
    have h := (Metric.equicontinuousAt_iff_right.mp (boundedNativeResidual_equicontinuous z x)) ε hε
    filter_upwards [h] with y hy f
    obtain ⟨g, hg, hgf⟩ := f.property
    simpa only [hgf] using hy ⟨g, hg⟩
  · intro ε hε
    obtain ⟨R, hR⟩ := boundedNativeResidual_uniform_tails z ε hε
    refine ⟨R, ?_⟩
    rintro f ⟨g, hg, rfl⟩ x hx
    exact hR g (by simpa only [Metric.mem_closedBall, dist_zero_right] using hg) x hx

/-- Actual compact Green operator on the entire native uniform space. -/
theorem isCompactOperator_boundedNativeResolvent (z : ThetaRegularParameter) :
    IsCompactOperator (boundedNativeResolvent z) := by
  have hc := (isCompactOperator_of_locallyCompactSpace_dom (boundedResolventTrace z)).clm_comp
    nativeConstantCLM
  have h := (isCompactOperator_boundedNativeResidual z).add hc
  have he : (boundedNativeResolvent z : NativeContinuousSpace → NativeContinuousSpace) =
      (boundedNativeResidual z : NativeContinuousSpace → NativeContinuousSpace)+
        (nativeConstantCLM ∘ boundedResolventTrace z) := by
    funext g
    ext x
    change boundedNativeResolvent z g x =
      (boundedNativeResolvent z g x-boundedResolventTrace z g)+boundedResolventTrace z g
    ring
  rw [he]
  exact h

def nativeCompactParameter : ThetaRegularParameter := thetaImaginaryRegularParameter (1 : ℝˣ)

@[simp] theorem nativeCompactParameter_val : nativeCompactParameter.val = I := by
  simp [nativeCompactParameter, thetaImaginaryRegularParameter]

def nativeCompactResolvent : NativeContinuousSpace →L[ℂ] NativeContinuousSpace :=
  boundedNativeResolvent nativeCompactParameter

/-- Unconditional compactness at the canonical imaginary base point. -/
theorem nativeCompactResolvent_compact : IsCompactOperator nativeCompactResolvent :=
  isCompactOperator_boundedNativeResolvent nativeCompactParameter

end RHTower.PaperThetaEndpoint
