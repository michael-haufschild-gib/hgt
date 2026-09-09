import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativeCutoffPowerMoments
import GaloisForLFunctions.HTGeometry.TruncatedMellinEntire
import Mathlib.Analysis.Meromorphic.Complex

/-! The unchanged finite transition is entire and the original cutoff moment is meromorphic. -/
open Complex MeasureTheory Set
open GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMJointSource
open D4BMGlobalAngularResponse
noncomputable section

/-- The entire transition interval gives an entire function of its original Mellin exponent. -/
theorem nativeCutoffTransitionMoment_differentiable : Differentiable ℂ nativeCutoffTransitionMoment := by
  have hi : IntegrableOn (fun y : ℝ => cutoff ![0,y]) (Ioo (2:ℝ) 3) :=
    nativeCutoff_height_continuous.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hd := differentiable_truncatedMellin (by norm_num : (0:ℝ)<2) (by norm_num : (2:ℝ)≤3) hi
  have hc := hd.comp ((differentiable_const (1:ℂ)).sub differentiable_id)
  change Differentiable ℂ (fun w => ∫ y in Ioc (2:ℝ) 3, cutoff ![0,y]*(y:ℂ)^(w-1))
  simpa only [Function.comp_def,Pi.sub_apply,id_eq,neg_sub,integral_Ioc_eq_integral_Ioo] using hc

/-- The derived original cutoff moment is meromorphic throughout the complex plane. -/
theorem nativeCutoffMellinContinuation_meromorphic (w : ℂ) :
    MeromorphicAt nativeCutoffMellinContinuation w := by
  have hd : Differentiable ℂ (fun z : ℂ => (3:ℂ)^z) :=
    differentiable_id.const_cpow (Or.inl (by norm_num : (3:ℂ)≠0))
  exact (((hd.analyticAt w).meromorphicAt.div analyticAt_id.meromorphicAt).sub
    ((nativeCutoffTransitionMoment_differentiable.analyticAt w).meromorphicAt))

/-- Away from the sole possible power-tail pole, the original cutoff continuation is analytic. -/
theorem nativeCutoffMellinContinuation_analytic {w : ℂ} (hw : w ≠ 0) :
    AnalyticAt ℂ nativeCutoffMellinContinuation w := by
  have hd : Differentiable ℂ (fun z : ℂ => (3:ℂ)^z) :=
    differentiable_id.const_cpow (Or.inl (by norm_num : (3:ℂ)≠0))
  exact ((hd.analyticAt w).div analyticAt_id hw).sub
    (nativeCutoffTransitionMoment_differentiable.analyticAt w)

end
end RHTower.D4BMJointSource
