import GaloisForLFunctions.HTGeometry.ComplexAffineLinePolynomialAvoidance
import GaloisForLFunctions.HTGeometry.MvPolynomialMatrixRankDefect
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # Generic injectivity of an operator pencil with real parameters -/
open MeasureTheory Matrix Module Set
namespace GaloisForLFunctions.HTGeometry.UntouchedSites
noncomputable section

/-- Real specialization of a complex linear pencil. -/
def pencil {p : ℕ} {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    (L : Fin p → E →ₗ[ℂ] F) (x : Fin p → ℝ) : E →ₗ[ℂ] F := ∑ i, (x i:ℂ) • L i

/-- One injective member of a finite-dimensional pencil makes almost every
real parameter injective. A left inverse at the witness gives a square
determinant equal to one there. -/
theorem pencil_ae_injective {p : ℕ} {E F : Type*} [AddCommGroup E] [Module ℂ E]
    [AddCommGroup F] [Module ℂ F] [FiniteDimensional ℂ E]
    (L : Fin p → E →ₗ[ℂ] F) (w : Fin p → ℝ) (hw : Function.Injective (pencil L w)) :
    ∀ᵐ x : Fin p → ℝ ∂volume, Function.Injective (pencil L x) := by
  classical
  obtain ⟨A,hwid⟩ := (pencil L w).exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hw)
  let b := Module.finBasis ℂ E
  let N := Module.finrank ℂ E
  let M : Matrix (Fin N) (Fin N) (MvPolynomial (Fin p) ℂ) := fun i j =>
    ∑ k, MvPolynomial.X k * MvPolynomial.C ((LinearMap.toMatrix b b (A.comp (L k))) i j)
  let B (x : Fin p → ℝ) := LinearMap.toMatrix b b (A.comp (pencil L x))
  have hM (x : Fin p → ℝ) : mvPolynomialMatrixEval M (fun i => (x i:ℂ)) = B x := by
    ext i j
    change MvPolynomial.eval (fun i => (x i:ℂ)) (∑ k, MvPolynomial.X k*MvPolynomial.C ((LinearMap.toMatrix b b (A.comp (L k))) i j)) = _
    simp only [map_sum,map_mul,MvPolynomial.eval_X,MvPolynomial.eval_C,B,LinearMap.toMatrix_apply,
      LinearMap.comp_apply,pencil,LinearMap.sum_apply,LinearMap.smul_apply,map_smul,
      Finsupp.finsetSum_apply,Finsupp.smul_apply,smul_eq_mul]
  have hdet (x : Fin p → ℝ) : MvPolynomial.eval (fun i => (x i:ℂ)) M.det = (B x).det := by
    have he := eval_mvPolynomialMatrixColumnMinor M id (fun i => (x i:ℂ))
    simpa only [mvPolynomialMatrixColumnMinor,Matrix.submatrix_id_id,hM] using he
  have hne : M.det ≠ 0 := by
    intro hz
    have he := hdet w
    rw [hz,map_zero,show B w=1 by dsimp [B]; rw [hwid,LinearMap.toMatrix_id],Matrix.det_one] at he
    exact zero_ne_one he
  have hnull := mvPolynomial_zero_set_volume_real_fin p (mvPolynomialRealShadow M.det)
    (mvPolynomialRealShadow_ne_zero hne)
  have hg : ∀ᵐ x : Fin p → ℝ ∂volume, MvPolynomial.eval x (mvPolynomialRealShadow M.det) ≠ 0 :=
    ae_iff.mpr (by simpa only [not_not] using hnull)
  filter_upwards [hg] with x hx
  have hd : (B x).det ≠ 0 := (hdet x) ▸ (eval₂_ne_zero_of_eval_mvPolynomialRealShadow_ne_zero hx)
  have hb := Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det (B x)).mpr (isUnit_iff_ne_zero.mpr hd))
  intro y z hyz
  apply b.repr.injective
  ext i
  have hy : B x *ᵥ (b.repr y : Fin N → ℂ) = B x *ᵥ (b.repr z : Fin N → ℂ) := by
    dsimp only [B]
    rw [LinearMap.toMatrix_mulVec_repr,LinearMap.toMatrix_mulVec_repr,LinearMap.comp_apply,
      LinearMap.comp_apply,hyz]
  exact congrFun (hb hy) i

#print axioms pencil_ae_injective
end
end GaloisForLFunctions.HTGeometry.UntouchedSites
