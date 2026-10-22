import GaloisForLFunctions.HTGeometry.ComplexPowerC2Boundary
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMLaplaceSpatialODE

/-! A fixed regularity condition selects the actual original horizon branch throughout the continuation strip. -/
namespace RHTower.D4BMLaplaceRadial
open Complex Set Filter Topology GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

/-- Remove the literal original horizon phase and demand a genuine C² extension at the horizon. -/
def OriginalHorizonC2 (w : ℂ) (U : ℝ → ℂ) : Prop :=
  RightC2Extension (fun b => power (-w/2) b*U b)

/-- The actual Gauss multiplier extends smoothly across the horizon, including terminating parameters. -/
theorem gaussFactor_right_contDiffAt (w chi : ℂ) :
    ContDiffAt ℝ 2 (fun b : ℝ => gaussFactor w chi false b) 0 := by
  let p := horizonSeries w chi
  have hr : 0 < p.radius := lt_of_lt_of_le (by norm_num : (0:ENNReal) < 1) (hypergeometric_radius_one_le _ _ _)
  have ha : AnalyticAt ℂ (gaussFactor w chi false) 0 := p.analyticOnNhd 0 (by simpa using hr)
  have hj : ContDiffAt ℝ 2 (fun b : ℝ => (b:ℂ)) 0 := Complex.ofRealCLM.contDiff.contDiffAt
  exact (ha.contDiffAt.restrict_scalars ℝ).comp (f := fun b : ℝ => (b:ℂ)) 0 hj

/-- Exact phase cancellation for the original and opposite horizon branches. -/
theorem originalHorizon_strip_modes (w chi A B : ℂ) (b : ℝ) (hb : 0 < b) :
    power (-w/2) b*(A*horizon w chi b+B*horizon (-w) chi b) =
      A*gaussFactor w chi false b+B*((b:ℂ)^(-w)*gaussFactor (-w) chi false b) := by
  have hb0 : (b:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hb)
  have hp : power (-w/2) b*power (w/2) b = 1 := by
    rw [power,power,← Complex.cpow_add _ _ hb0,show -w/2+w/2=0 by ring,Complex.cpow_zero]
  have hm : power (-w/2) b*power (-w/2) b = (b:ℂ)^(-w) := by
    rw [power,← Complex.cpow_add _ _ hb0,show -w/2+-w/2= -w by ring]
  dsimp only [horizon,dress]
  have he : (-w)/2 = -w/2 := rfl
  linear_combination A*gaussFactor w chi false b*hp+B*gaussFactor (-w) chi false b*hm

/-- Exact two-branch classification: in the nonreal strip reaching fundamental QNMs,
the fixed C² horizon domain admits precisely the original branch. -/
theorem originalHorizonC2_modes_iff (w chi A B : ℂ) (hw : w.im ≠ 0) (hwr : -2 < w.re) :
    OriginalHorizonC2 w (fun b => A*horizon w chi b+B*horizon (-w) chi b) ↔ B = 0 := by
  have hplus := gaussFactor_right_contDiffAt w chi
  have hminus := gaussFactor_right_contDiffAt (-w) chi
  have ha : (-w).re < 2 := by simp only [Complex.neg_re]; linarith
  have ha0 : -w ≠ 0 := by intro he; apply hw; have := congrArg Complex.im he; simpa using this
  have ha1 : -w ≠ 1 := by intro he; apply hw; have := congrArg Complex.im he; simpa using this
  constructor
  · rintro ⟨g,hg,he⟩
    by_contra hB
    apply not_rightC2Extension_cpow_mul (-w) ha ha0 ha1 (fun b => gaussFactor (-w) chi false b) hminus
      (by simp)
    refine ⟨fun b => (g b-A*gaussFactor w chi false b)/B,
      (hg.sub (contDiffAt_const.mul hplus)).div_const B,?_⟩
    filter_upwards [he,self_mem_nhdsWithin] with b hb hpos
    change g b = power (-w/2) b*(A*horizon w chi b+B*horizon (-w) chi b) at hb
    rw [hb,originalHorizon_strip_modes w chi A B b hpos]
    field_simp [hB]
    ring
  · rintro rfl
    refine ⟨fun b => A*gaussFactor w chi false b,contDiffAt_const.mul hplus,?_⟩
    filter_upwards [self_mem_nhdsWithin] with b hpos
    simpa only [zero_mul,add_zero] using (originalHorizon_strip_modes w chi A 0 b hpos).symm

/-- The actual original horizon solution satisfies the same regularity domain across the strip. -/
theorem horizon_originalHorizonC2 (w chi : ℂ) (hw : w.im ≠ 0) (hwr : -2 < w.re) :
    OriginalHorizonC2 w (horizon w chi) := by
  simpa only [one_mul,zero_mul,add_zero] using (originalHorizonC2_modes_iff w chi 1 0 hw hwr).mpr rfl

/-- The opposite homogeneous branch fails the actual fixed regularity domain. -/
theorem oppositeHorizon_not_originalHorizonC2 (w chi : ℂ) (hw : w.im ≠ 0) (hwr : -2 < w.re) :
    ¬OriginalHorizonC2 w (horizon (-w) chi) := by
  simpa only [zero_mul,one_mul,zero_add] using
    (not_congr (originalHorizonC2_modes_iff w chi 0 1 hw hwr)).mpr one_ne_zero

end
end RHTower.D4BMLaplaceRadial
