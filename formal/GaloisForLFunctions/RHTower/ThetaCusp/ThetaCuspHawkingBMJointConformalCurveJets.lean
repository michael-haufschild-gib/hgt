import GaloisForLFunctions.HTGeometry.ComplexCoordinateDerivativeRules
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! Actual second derivatives of weighted pullbacks along real coordinate curves. -/
open Filter Topology
namespace RHTower.D4BMJointConformal
noncomputable section
attribute [-instance] NormedSpace.complexToReal

theorem weightedCurve_second {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → ℂ) (m : ℝ → ℂ) (g : ℝ → E) (t : ℝ)
    (hF : ContDiffAt ℝ 2 F (g t)) (hm : ContDiffAt ℝ 2 m t) (hg : ContDiffAt ℝ 2 g t) :
    deriv (deriv (fun x => m x*F (g x))) t =
      deriv (deriv m) t*F (g t)+2*deriv m t*(fderiv ℝ F (g t) (deriv g t))+
      m t*((fderiv ℝ (fderiv ℝ F) (g t)) (deriv g t) (deriv g t)+
        fderiv ℝ F (g t) (deriv (deriv g) t)) := by
  have hdg := (hg.differentiableAt (by norm_num)).hasDerivAt
  have hdm := (hm.differentiableAt (by norm_num)).hasDerivAt
  have hdF := (hF.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t hdg
  have hm1 : HasDerivAt (deriv m) (deriv (deriv m) t) t :=
    (((hm.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt (by norm_num)).hasDerivAt
  have hg1 : HasDerivAt (deriv g) (deriv (deriv g) t) t :=
    (((hg.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt (by norm_num)).hasDerivAt
  have hF1 := ((hF.fderiv_right (m := 1) (by norm_num)).differentiableAt
    (by norm_num)).hasFDerivAt.comp_hasDerivAt t hdg
  have he : deriv (fun x => m x*F (g x)) =ᶠ[𝓝 t]
      (fun x => deriv m x*F (g x)+m x*(fderiv ℝ F (g x) (deriv g x))) := by
    filter_upwards [hm.eventually (by norm_num),hg.eventually (by norm_num),
      hg.continuousAt.preimage_mem_nhds (hF.eventually (by norm_num))] with x hmx hgx hFx
    change ContDiffAt ℝ 2 F (g x) at hFx
    exact (((hmx.differentiableAt (by norm_num)).hasDerivAt).mul
      ((hFx.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt x
        (hgx.differentiableAt (by norm_num)).hasDerivAt)).deriv
  rw [he.deriv_eq]
  convert! ((hm1.mul hdF).add (hdm.mul (hF1.clm_apply hg1))).deriv using 1
  dsimp only [Function.comp_apply]
  ring

end
end RHTower.D4BMJointConformal
