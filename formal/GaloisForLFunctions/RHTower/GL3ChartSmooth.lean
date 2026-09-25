import GaloisForLFunctions.RHTower.GL3Laplacian
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt


/-!
# Smooth functions on `h³` have smooth exponential charts

A function on `h³` is smooth when it is smooth in the Iwasawa coordinates on `ℝ³ × (0,∞)²`
(`IsSmooth`). The chart point `mat z · exp(v + vᵀ) · 1` is `ofPD` of the positive definite matrix
`mat z · exp(v + vᵀ) · mat zᵀ` (`chartPoint_eq`). Its entries are smooth in `v` because the matrix
exponential is analytic (`contDiff_symExp_apply`), and the Iwasawa coordinates of `ofPD` are ratios
and square roots with positive denominators (`contDiff_coords_ofPD`). Hence the exponential chart of
a smooth function is smooth (`contDiff_chart`), which is what makes the invariant Laplacian a
genuine second-order operator on smooth functions.
-/

open Matrix Laplacian InnerProductSpace

namespace GaloisForLFunctions.RHTower.GL3
namespace H3

/-! ### Smoothness of the exponential chart -/

section LocalNorm

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- `v ↦ v + vᵀ` as a continuous linear map into matrices (with the operator norm). -/
noncomputable def symLin : Dir →L[ℝ] Matrix (Fin 3) (Fin 3) ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => toMat v + (toMat v)ᵀ
      map_add' := fun v w => by
        rw [toMat_add, Matrix.transpose_add]; abel
      map_smul' := fun r v => by
        rw [toMat_smul, Matrix.transpose_smul, smul_add]; rfl }

/-- The entry `(i, j)` of a matrix, as a continuous linear functional. -/
noncomputable def entryCLM (i j : Fin 3) : Matrix (Fin 3) (Fin 3) ℝ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => M i j
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

/-- **The entries of `exp(v + vᵀ)` are smooth functions of `v`.** -/
theorem contDiff_symExp_apply (i j : Fin 3) : ContDiff ℝ ⊤ fun v : Dir => symExp v i j := by
  have hexp : ContDiff ℝ ⊤ (NormedSpace.exp : Matrix (Fin 3) (Fin 3) ℝ → _) :=
    contDiff_iff_contDiffAt.2 fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt
  have h := (entryCLM i j).contDiff.comp (hexp.comp symLin.contDiff)
  exact h

end LocalNorm

/-- **The Iwasawa coordinates depend smoothly on a smooth family of positive definite matrices.** -/
theorem contDiff_coords_ofPD {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : E → Matrix (Fin 3) (Fin 3) ℝ} (hS : ∀ i j, ContDiff ℝ ⊤ fun v => S v i j)
    (hpd : ∀ v, (S v).PosDef) : ContDiff ℝ ⊤ fun v => coords (ofPD (S v) (hpd v)) := by
  have hnt : ∀ i j, ContDiff ℝ ⊤ fun v => nt (S v) i j := fun i j =>
    (hS i j).div (hS 2 2) fun v => (s22_pos (hpd v)).ne'
  have hqa : ContDiff ℝ ⊤ fun v => qa (S v) := (hnt 1 1).sub ((hnt 1 2).pow 2)
  have hqa0 : ∀ v, qa (S v) ≠ 0 := fun v => (qa_pos (hpd v)).ne'
  have hqb : ContDiff ℝ ⊤ fun v => qb (S v) := (hnt 0 1).sub ((hnt 1 2).mul (hnt 0 2))
  have hqe : ContDiff ℝ ⊤ fun v => qe (S v) :=
    ((hnt 0 0).sub ((hnt 0 2).pow 2)).sub ((hqb.pow 2).div hqa hqa0)
  have hqe0 : ∀ v, qe (S v) ≠ 0 := fun v => (qe_pos (hpd v)).ne'
  have hsa : ContDiff ℝ ⊤ fun v => √(qa (S v)) := hqa.sqrt hqa0
  have hse : ContDiff ℝ ⊤ fun v => √(qe (S v)) := hqe.sqrt hqe0
  refine contDiff_pi.2 fun k => ?_
  fin_cases k
  · exact hnt 1 2
  · exact hqb.div hqa hqa0
  · exact hnt 0 2
  · exact hsa
  · exact hse.div hsa fun v => (Real.sqrt_pos.2 (qa_pos (hpd v))).ne'

/-- `g • ofMat E = ofMat (g E gᵀ)` for positive definite `E`. -/
theorem smul_ofMat (g : GL (Fin 3) ℝ) {E : Matrix (Fin 3) (Fin 3) ℝ} (hE : E.PosDef) :
    g • ofMat E = ofMat ((g : Matrix (Fin 3) (Fin 3) ℝ) * E * (g : Matrix (Fin 3) (Fin 3) ℝ)ᵀ) := by
  have hP : ((g : Matrix (Fin 3) (Fin 3) ℝ) * E * (g : Matrix (Fin 3) (Fin 3) ℝ)ᵀ).PosDef := by
    have := (IsUnit.posDef_star_right_conjugate_iff (x := E) (Units.isUnit g)).2 hE
    simpa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using this
  rw [smul_def, gram_ofMat_of_posDef hE, Matrix.mul_smul, Matrix.smul_mul,
    ofMat_smul hP (inv_pos.2 hE.diag_pos)]

/-- The positive definite matrix `mat z · exp(v + vᵀ) · mat zᵀ` of the chart point. -/
noncomputable def chartMat (z : H3) (v : Dir) : Matrix (Fin 3) (Fin 3) ℝ :=
  z.mat * symExp v * z.matᵀ

theorem posDef_chartMat (z : H3) (v : Dir) : (chartMat z v).PosDef := by
  have := (IsUnit.posDef_star_right_conjugate_iff (x := symExp v) z.isUnit_mat).2 (posDef_symExp v)
  simpa [chartMat, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using this

theorem chartPoint_eq (z : H3) (v : Dir) :
    toGL z • ofMat (symExp v) = ofPD (chartMat z v) (posDef_chartMat z v) := by
  rw [smul_ofMat _ (posDef_symExp v), coe_toGL]
  exact ofMat_eq (posDef_chartMat z v)

theorem contDiff_chartMat_apply (z : H3) (i j : Fin 3) :
    ContDiff ℝ ⊤ fun v => chartMat z v i j := by
  simp only [chartMat, Matrix.mul_apply, Matrix.transpose_apply]
  refine ContDiff.sum fun k _ => ?_
  refine ContDiff.mul ?_ contDiff_const
  refine ContDiff.sum fun l _ => ?_
  exact contDiff_const.mul (contDiff_symExp_apply l k)

/-- A function on `h³` is smooth when it is smooth in the Iwasawa coordinates. -/
def IsSmooth (F : H3 → ℂ) : Prop := ContDiffOn ℝ ⊤ (fun p => F (ofCoords p)) dom

/-- **The exponential chart of a smooth function is smooth.** -/
theorem contDiff_chart {F : H3 → ℂ} (hF : IsSmooth F) (z : H3) : ContDiff ℝ ⊤ (chart F z) := by
  have hc : ContDiff ℝ ⊤ fun v => coords (ofPD (chartMat z v) (posDef_chartMat z v)) :=
    contDiff_coords_ofPD (contDiff_chartMat_apply z) (posDef_chartMat z)
  have e : chart F z = (fun p => F (ofCoords p)) ∘
      fun v => coords (ofPD (chartMat z v) (posDef_chartMat z v)) := by
    funext v
    simp only [chart, Function.comp_apply, ofCoords_coords, chartPoint_eq]
  rw [e]
  exact hF.comp_contDiff hc fun v => ⟨(ofPD _ _).y1_pos, (ofPD _ _).y2_pos⟩

end H3
end GaloisForLFunctions.RHTower.GL3
