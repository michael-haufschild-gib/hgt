import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.ComplexPerturbation
import GaloisForLFunctions.HTGeometry.HermitianSubmoduleTraceOrthonormal
import GaloisForLFunctions.RHTower.InverseSquareChainCubicProjectiveFirstReturnLaw

/-! # Entire continuation of a local Heisenberg correlation -/
open NormedSpace Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
private abbrev Op (ι : Type*) := Matrix ι ι ℂ

private def prop (H P : Op ι) (t : ℝ) (z : ℂ) :=
  exp (t • ((-Complex.I) • (H+z • P)))

/-- At complex fields use backward evolution on the left. On the real axis
it is the adjoint, so this continues the physical trace correlation. -/
def fieldTrace (H P Y B : Op ι) (t : ℝ) (z : ℂ) : ℂ :=
  (Fintype.card ι : ℂ)⁻¹ * (prop H P (-t) z * Y * prop H P t z * B).trace

private theorem prop_analytic (H P : Op ι) (t : ℝ) (z : ℂ) : AnalyticAt ℂ (prop H P t) z := by
  unfold prop
  simp only [←Complex.coe_smul t]
  exact (exp_analytic (𝕂 := ℂ) _).comp
    ((analyticAt_const.add (analyticAt_id.smul analyticAt_const)).const_smul (-Complex.I) |>.const_smul (t:ℂ))

theorem fieldTrace_differentiable (H P Y B : Op ι) (t : ℝ) : Differentiable ℂ (fieldTrace H P Y B t) := by
  intro z
  let L := (Matrix.traceLinearMap ι ℂ ℂ).toContinuousLinearMap
  have h := (((prop_analytic H P (-t) z).mul analyticAt_const).mul (prop_analytic H P t z)).mul
    (analyticAt_const (v := B))
  exact (analyticAt_const.mul ((L.analyticAt _).comp h)).differentiableAt

private theorem prop_star (H P : Op ι) (hH : IsSelfAdjoint H) (hP : IsSelfAdjoint P)
    (t u : ℝ) : star (prop H P t u)=prop H P (-t) u := by
  simp only [prop,star_exp,star_smul,star_add,hH.star_eq,hP.star_eq,
    Complex.star_def,Complex.conj_ofReal,map_neg,Complex.conj_I,neg_neg,star_trivial,neg_smul]
  simp only [←neg_smul,neg_neg]

/-- A Hermitian observable paired with a Hermitian input gives a real
response at every real value of the varied coupling. -/
theorem fieldTrace_real (H P Y B : Op ι) (hH : IsSelfAdjoint H) (hP : IsSelfAdjoint P)
    (hY : Y.IsHermitian) (hB : B.IsHermitian) (t u : ℝ) : (fieldTrace H P Y B t u).im=0 := by
  let U := prop H P t u
  have hU : prop H P (-t) u=Uᴴ := (prop_star H P hH hP t u).symm
  have hconj := Matrix.isHermitian_conjTranspose_mul_mul U hY
  have hre := trace_mul_eq_ofReal_re hconj hB
  have him := congrArg Complex.im hre
  simp only [Complex.ofReal_im] at him
  unfold fieldTrace
  rw [hU]
  change (((Fintype.card ι : ℂ)⁻¹) * (Uᴴ * Y * U * B).trace).im=0
  simp [Complex.mul_im,him]

/-- Unit-norm observables and interactions have a common exponential
envelope, independent of the number and strengths of background terms. -/
theorem norm_fieldTrace (H P Y B : Op ι) (hH : IsSelfAdjoint H) (hP : IsSelfAdjoint P)
    (hY : ‖Y‖≤1) (hB : ‖B‖≤1) (hP' : ‖P‖≤1) (t : ℝ) (z : ℂ) :
    ‖fieldTrace H P Y B t z‖ ≤ Real.exp (2*|t|*‖z‖) := by
  letI : CStarAlgebra (Op ι) := {}
  have bound (s : ℝ) : ‖prop H P s z‖≤Real.exp (|s|*‖z‖) := by
    apply (norm_complex_field_evolution H P hH hP z s).trans
    apply Real.exp_le_exp.mpr
    calc |s|*|z.im|*‖P‖ ≤ |s|*‖z‖*1 := by gcongr; exact Complex.abs_im_le_norm z
         _ = _ := mul_one _
  have hm := RHTower.norm_normalizedTrace_sub_le_l2OpNorm
    (prop H P (-t) z * Y * prop H P t z * B) 0
  simp only [Matrix.trace_zero,mul_zero,sub_zero] at hm
  have hb := bound (-t)
  rw [abs_neg] at hb
  refine hm.trans ((norm_mul_le _ _).trans ?_)
  calc ‖prop H P (-t) z * Y * prop H P t z‖ * ‖B‖
      ≤ ((Real.exp (|t|*‖z‖)*1)*Real.exp (|t|*‖z‖))*1 :=
        mul_le_mul ((norm_mul_le _ _).trans (mul_le_mul
          ((norm_mul_le _ _).trans (mul_le_mul hb hY (norm_nonneg _) (Real.exp_pos _).le))
          (bound t) (norm_nonneg _) (by positivity))) hB (norm_nonneg _) (by positivity)
    _ = _ := by rw [mul_one,mul_one,←Real.exp_add]; congr 1; ring

end
end GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
