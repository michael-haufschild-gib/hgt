import GaloisForLFunctions.HTGeometry.GomesUnipotentInvariantForms
import GaloisForLFunctions.RHTower.WeldGermOrientationNoGo
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Basis.Fin

/-!
# Exact weld-shear invariant geometry

Apply Gomes' representation-menu distinction (arXiv:2607.24901) to the actual upper and
lower weld shears. Their common invariant bilinear forms are precisely the areas supplied
by unique weld classes. Nonzero area reconstructs determinant-one observers; positivity
cannot be preserved even by the upper shear alone. The observer transport formula is the
associated-action covariance mechanism discussed in arXiv:2404.10461.

https://arxiv.org/abs/2607.24901
https://arxiv.org/abs/2404.10461
-/

open scoped Matrix
open Module
noncomputable section
namespace GaloisForLFunctions.RHTower
open GaloisForLFunctions.HTGeometry

/-- Matrix of an observer on the corpus's real weld-generator plane. -/
def weldObserverMatrix (P : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)) : Matrix (Fin 2) (Fin 2) ℝ :=
  LinearMap.toMatrix (Basis.finTwoProd ℝ) (Basis.finTwoProd ℝ) P

/-- Matrix of a bilinear form in the existing weld-generator coordinates. -/
def weldBilinMatrix (B : LinearMap.BilinForm ℝ (ℝ × ℝ)) : Matrix (Fin 2) (Fin 2) ℝ :=
  LinearMap.BilinForm.toMatrix (Basis.finTwoProd ℝ) B

/-- The existing upper weld shear is the unit polynomial unipotent. -/
theorem weldObserverMatrix_upper :
    weldObserverMatrix weldUpperShear.toLinearMap = unipotentUpper (1 : ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [weldObserverMatrix,LinearMap.toMatrix_apply,Basis.finTwoProd,weldUpperShear,
      LinearEquiv.finTwoArrow,unipotentUpper]

/-- The lower weld shear is the transpose unit unipotent. -/
theorem weldObserverMatrix_lower :
    weldObserverMatrix weldLowerShear.toLinearMap = (unipotentUpper (1 : ℝ))ᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [weldObserverMatrix,LinearMap.toMatrix_apply,Basis.finTwoProd,weldLowerShear,
      LinearEquiv.finTwoArrow,unipotentUpper]

/-- Exact matrix of the actual class-selected weld area form. -/
theorem weldBilinMatrix_area (θ : ℝ) :
    weldBilinMatrix (weldAreaForm θ) = θ • gomesShearAreaMatrix ℝ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [weldBilinMatrix,LinearMap.BilinForm.toMatrix_apply,weldAreaForm,gomesShearAreaMatrix]

/-- The corpus's bilinear-preservation predicate agrees with matrix transport in this basis. -/
theorem weld_preservesBilin_iff_matrix (B : LinearMap.BilinForm ℝ (ℝ × ℝ))
    (P : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)) :
    PreservesBilin B P ↔
      (weldObserverMatrix P)ᵀ * weldBilinMatrix B * weldObserverMatrix P = weldBilinMatrix B := by
  have hcomp : weldBilinMatrix (B.comp P P) =
      (weldObserverMatrix P)ᵀ * weldBilinMatrix B * weldObserverMatrix P := by
    exact LinearMap.BilinForm.toMatrix_comp (Basis.finTwoProd ℝ) (Basis.finTwoProd ℝ) B P P
  rw [← hcomp]
  constructor
  · intro h
    have he : B.comp P P = B := by
      apply LinearMap.ext
      intro x
      apply LinearMap.ext
      intro y
      exact h x y
    exact congrArg weldBilinMatrix he
  · intro h
    have he := (LinearMap.BilinForm.toMatrix (Basis.finTwoProd ℝ)).injective h
    intro x y
    exact congrArg (fun C : LinearMap.BilinForm ℝ (ℝ × ℝ) => C x y) he

/-- The full positive survivor of the weld-shear obstruction: all invariant bilinear forms are
exactly the existing one-dimensional family of weld areas. -/
theorem weld_two_shears_invariant_forms (B : LinearMap.BilinForm ℝ (ℝ × ℝ)) :
    (PreservesBilin B weldUpperShear.toLinearMap ∧
      PreservesBilin B weldLowerShear.toLinearMap) ↔
        B = weldAreaForm (B (1,0) (0,1)) := by
  constructor
  · rintro ⟨hu,hl⟩
    rw [weld_preservesBilin_iff_matrix,weldObserverMatrix_upper] at hu
    rw [weld_preservesBilin_iff_matrix,weldObserverMatrix_lower,Matrix.transpose_transpose] at hl
    have hf := (two_unipotent_shears_bilinear_invariants (weldBilinMatrix B)).mp ⟨hu,hl⟩
    apply (LinearMap.BilinForm.toMatrix (Basis.finTwoProd ℝ)).injective
    change weldBilinMatrix B = weldBilinMatrix (weldAreaForm (B (1,0) (0,1)))
    calc
      weldBilinMatrix B = !![0,weldBilinMatrix B 0 1; -weldBilinMatrix B 0 1,0] := hf
      _ = weldBilinMatrix (weldAreaForm (B (1,0) (0,1))) := by
        rw [weldBilinMatrix_area]
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [weldBilinMatrix,LinearMap.BilinForm.toMatrix_apply,gomesShearAreaMatrix]
  · intro h
    rw [h]
    exact ⟨weldUpperShear_preserves_area _,weldLowerShear_preserves_area _⟩

/-- Even the upper shear alone excludes every positive-definite invariant metric. -/
theorem weldUpperShear_no_positive_metric :
    ¬ ∃ B : LinearMap.BilinForm ℝ (ℝ × ℝ),
      (∀ x : ℝ × ℝ, x ≠ 0 → 0 < B x x) ∧ PreservesBilin B weldUpperShear.toLinearMap := by
  rintro ⟨B,hpos,hinv⟩
  rw [weld_preservesBilin_iff_matrix,weldObserverMatrix_upper] at hinv
  have hf := (unipotentUpper_unit_bilinear_invariants (weldBilinMatrix B)).mp hinv
  have hz : B (1,0) (1,0) = 0 := by
    have he := congrFun (congrFun hf 0) 0
    simpa [weldBilinMatrix,LinearMap.BilinForm.toMatrix_apply] using he
  have hp := hpos (1,0) (by simp)
  rw [hz] at hp
  exact (lt_irrefl 0) hp

/-- Any observer transports the actual weld area by its determinant. -/
theorem weldAreaForm_observer_transport (θ : ℝ) (P : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)) :
    (weldAreaForm θ).comp P P = weldAreaForm (θ * (weldObserverMatrix P).det) := by
  apply (LinearMap.BilinForm.toMatrix (Basis.finTwoProd ℝ)).injective
  change weldBilinMatrix ((weldAreaForm θ).comp P P) =
    weldBilinMatrix (weldAreaForm (θ * (weldObserverMatrix P).det))
  have hcomp := LinearMap.BilinForm.toMatrix_comp
    (Basis.finTwoProd ℝ) (Basis.finTwoProd ℝ) (weldAreaForm θ) P P
  change weldBilinMatrix ((weldAreaForm θ).comp P P) =
    (weldObserverMatrix P)ᵀ * weldBilinMatrix (weldAreaForm θ) * weldObserverMatrix P at hcomp
  rw [hcomp,weldBilinMatrix_area,weldBilinMatrix_area,Matrix.mul_smul,Matrix.smul_mul,
    gomesShearArea_transport,smul_smul]

/-- The zero area has unrestricted observer symmetry; every nonzero area reconstructs
precisely determinant-one observers. -/
theorem weldAreaForm_observer_preservation_iff (θ : ℝ)
    (P : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)) :
    PreservesBilin (weldAreaForm θ) P ↔ θ = 0 ∨ (weldObserverMatrix P).det = 1 := by
  have he : PreservesBilin (weldAreaForm θ) P ↔
      (weldAreaForm θ).comp P P = weldAreaForm θ := by
    constructor
    · intro h
      apply LinearMap.ext
      intro x
      apply LinearMap.ext
      intro y
      exact h x y
    · intro h x y
      exact congrArg (fun B : LinearMap.BilinForm ℝ (ℝ × ℝ) => B x y) h
  rw [he,weldAreaForm_observer_transport]
  constructor
  · intro h
    have hx := congrArg (fun B : LinearMap.BilinForm ℝ (ℝ × ℝ) => B (1,0) (0,1)) h
    have hx' : θ * (weldObserverMatrix P).det = θ := by simpa [weldAreaForm] using hx
    have hc : θ * ((weldObserverMatrix P).det - 1) = 0 := by
      rw [mul_sub,mul_one]
      exact sub_eq_zero.mpr hx'
    exact (mul_eq_zero.mp hc).imp_right sub_eq_zero.mp
  · rintro (h | h) <;> simp [h]

/-- The actual positive weld-plane family is shear-invariant exactly at zero conversion rate. -/
theorem weldPlaneQ_upperShear_preservation_iff (θ : ℝ) :
    PreservesBilin (weldPlaneQ θ) weldUpperShear.toLinearMap ↔ θ = 0 := by
  constructor
  · intro h
    have he := h (1,0) (0,1)
    simp [weldUpperShear,weldPlaneQ_apply] at he
    exact he
  · rintro rfl
    intro x y
    simp [weldPlaneQ_apply]

/-- Every bilinear form invariant under the two weld shears comes from a unique actual weld class. -/
theorem weldClassLine_classifies_shear_invariant_forms (B : LinearMap.BilinForm ℝ (ℝ × ℝ)) :
    (PreservesBilin B weldUpperShear.toLinearMap ∧ PreservesBilin B weldLowerShear.toLinearMap) ↔
      ∃! c : WeldClassLine, weldClassLineToArea c = B := by
  constructor
  · intro h
    have hf := (weld_two_shears_invariant_forms B).mp h
    refine ⟨weldClassHom.rangeRestrict (B (1,0) (0,1)),?_,?_⟩
    · exact (weldClassLineToArea_apply _).trans hf.symm
    · intro c hc
      apply weldClassLineToArea_injective
      rw [hc,weldClassLineToArea_apply]
      exact hf
  · rintro ⟨c,hc,_⟩
    let θ := weldClassLineEquiv.symm c
    have he : c = weldClassHom.rangeRestrict θ := by
      change c = weldClassLineEquiv (weldClassLineEquiv.symm c)
      exact (weldClassLineEquiv.apply_symm_apply c).symm
    rw [he,weldClassLineToArea_apply] at hc
    rw [← hc]
    exact ⟨weldUpperShear_preserves_area _,weldLowerShear_preserves_area _⟩

end GaloisForLFunctions.RHTower
