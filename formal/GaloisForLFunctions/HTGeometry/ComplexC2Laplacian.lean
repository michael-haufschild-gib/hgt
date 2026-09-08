import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The real C² Laplacian under holomorphic coordinate changes

The second chain rule contains the Hessian of the outer field and second
derivatives of the holomorphic chart. The latter cancel between the two real
directions; the real bilinear Hessian trace scales by the squared complex
Jacobian norm. Only the two stated C² germs are used.
-/

open Complex Set Filter Topology
open scoped ContDiff
namespace GaloisForLFunctions.HTGeometry.ComplexC2Laplacian
noncomputable section

/-- The two real second directional derivatives in the original complex coordinate. -/
def laplacian (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  fderiv ℝ (fun w => fderiv ℝ f w 1) z 1 +
    fderiv ℝ (fun w => fderiv ℝ f w Complex.I) z Complex.I

private theorem real_linear_expand {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : ℂ →L[ℝ] E) (w : ℂ) : A w = w.re • A 1+w.im • A Complex.I := by
  have he : w = w.re • (1:ℂ)+w.im • Complex.I := by
    simpa only [Complex.real_smul,mul_one] using w.re_add_im.symm
  calc
    A w = A (w.re • (1:ℂ)+w.im • Complex.I) := congrArg A he
    _ = _ := by rw [A.map_add,A.map_smul,A.map_smul]

private theorem real_bilinear_trace (B : ℂ →L[ℝ] ℂ →L[ℝ] ℂ) (a : ℂ) :
    B a a+B (a*Complex.I) (a*Complex.I) =
      (Complex.normSq a : ℂ)*(B 1 1+B Complex.I Complex.I) := by
  rw [real_linear_expand B a,real_linear_expand B (a*Complex.I)]
  simp only [add_apply,smul_apply]
  rw [real_linear_expand (B 1) a,real_linear_expand (B Complex.I) a,
    real_linear_expand (B 1) (a*Complex.I),real_linear_expand (B Complex.I) (a*Complex.I)]
  simp only [Complex.mul_I_re,Complex.mul_I_im,Complex.real_smul,
    Complex.normSq_apply,Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_neg]
  ring

private theorem holomorphic_first_comp {f g : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℝ f (g z)) (hg : DifferentiableAt ℂ g z) (v : ℂ) :
    fderiv ℝ (f ∘ g) z v = fderiv ℝ f (g z) (deriv g z*v) := by
  rw [fderiv_comp z hf (hg.restrictScalars ℝ),hg.fderiv_restrictScalars ℝ]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.coe_restrictScalars',
    fderiv_eq_deriv_mul]

private theorem second_as_bilinear {f : ℂ → ℂ} {z : ℂ}
    (hf : ContDiffAt ℝ 2 f z) (v : ℂ) :
    fderiv ℝ (fun w => fderiv ℝ f w v) z v = fderiv ℝ (fderiv ℝ f) z v v := by
  have hh := ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hd := hh.clm_apply (hasFDerivAt_const v z)
  simpa using congrArg (fun L => L v) hd.fderiv

private theorem holomorphic_second_comp {f g : ℂ → ℂ} {z : ℂ}
    (hf : ContDiffAt ℝ 2 f (g z)) (hg : ContDiffAt ℂ 2 g z) (v : ℂ) :
    fderiv ℝ (fun w => fderiv ℝ (f ∘ g) w v) z v =
      fderiv ℝ (fderiv ℝ f) (g z) (deriv g z*v) (deriv g z*v) +
        fderiv ℝ f (g z) (deriv (deriv g) z*v*v) := by
  have hp := hg.continuousAt.eventually (hf.eventually (by norm_num))
  have hq := hg.eventually (by norm_num)
  have he : (fun w => fderiv ℝ (f ∘ g) w v) =ᶠ[𝓝 z]
      (fun w => fderiv ℝ f (g w) (deriv g w*v)) := by
    filter_upwards [hp,hq] with w hw hwg
    exact holomorphic_first_comp (hw.differentiableAt (by norm_num))
      (hwg.differentiableAt (by norm_num)) v
  have hG := ((hg.differentiableAt (by norm_num)).hasDerivAt.hasFDerivAt).restrictScalars ℝ
  have hJ := (((hg.derivWithin (m := 1) (by norm_num)).differentiableAt
    (by norm_num)).hasDerivAt.mul_const v).hasFDerivAt.restrictScalars ℝ
  have hF := (((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt
    (by norm_num)).hasFDerivAt).comp z hG
  have hcomp := hF.clm_apply hJ
  rw [he.fderiv_eq]
  have hc := hcomp.fderiv
  simp only [Function.comp_apply] at hc
  rw [hc]
  simp only [add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.coe_restrictScalars',ContinuousLinearMap.toSpanSingleton_apply,
    smul_eq_mul]
  simp only [mul_comm,add_comm]

/-- The full real Laplacian transforms by the squared complex derivative under a holomorphic chart. -/
theorem laplacian_holomorphic_comp {f g : ℂ → ℂ} {z : ℂ}
    (hf : ContDiffAt ℝ 2 f (g z)) (hg : ContDiffAt ℂ 2 g z) :
    laplacian (f ∘ g) z = (Complex.normSq (deriv g z) : ℂ)*laplacian f (g z) := by
  simp only [laplacian]
  rw [holomorphic_second_comp hf hg,holomorphic_second_comp hf hg]
  simp only [mul_one,mul_assoc,Complex.I_mul_I,mul_neg_one,map_neg]
  have ht := real_bilinear_trace (fderiv ℝ (fderiv ℝ f) (g z)) (deriv g z)
  rw [second_as_bilinear hf,second_as_bilinear hf]
  linear_combination ht


end
end GaloisForLFunctions.HTGeometry.ComplexC2Laplacian
