import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalWeilDeligne.WeilDeligneUnramifiedTwist
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalWeilDeligne.WeilDeligneSpecial
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalWeilDeligne.WeilDeligneTensor
import Mathlib.LinearAlgebra.TensorProduct.Matrix

/-! Normalized special twists turn a cuspidal parameter into a
segment parameter. Its Weil polynomial is the product of the
polynomials of its successive unramified twists. -/

noncomputable section

open Matrix Module NumberField IsDedekindDomain Polynomial TensorProduct
open scoped Kronecker
open WindowedLandauTheory.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.WeilDeligne

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

private theorem charpoly_blockDiagonal {m o R : Type*} [Fintype m] [DecidableEq m] [Fintype o]
    [DecidableEq o] [CommRing R] (B : o → Matrix m m R) :
    (Matrix.blockDiagonal B).charpoly = ∏ k, (B k).charpoly := by
  have he : Matrix.charmatrix (Matrix.blockDiagonal B) =
      Matrix.blockDiagonal (fun k => Matrix.charmatrix (B k)) := by
    ext ⟨i, k⟩ ⟨j, k'⟩
    simp only [Matrix.charmatrix_apply, Matrix.blockDiagonal_apply, Matrix.diagonal_apply,
      Prod.mk.injEq]
    split_ifs <;> simp_all
  rw [Matrix.charpoly, he, Matrix.det_blockDiagonal]
  rfl

private theorem charpoly_tensor_sp_ρ {n m : ℕ} (f : End ℂ (Fin n → ℂ)) (σ : Weil h) :
    (TensorProduct.map f ((WDRep.sp h m).ρ σ)).charpoly =
      ∏ i : Fin m, (((specialEigenvalue w m i : ℂ) ^ deg σ) • f).charpoly := by
  let b := Pi.basisFun ℂ (Fin n)
  let c := Pi.basisFun ℂ (Fin m)
  let eigen (i : Fin m) : ℂ := (specialEigenvalue w m i : ℂ) ^ deg σ
  have he : LinearMap.toMatrix c c ((WDRep.sp h m).ρ σ) = Matrix.diagonal eigen := by
    ext i j
    simp [c, eigen, LinearMap.toMatrix_apply, Matrix.diagonal_apply, Pi.single_apply, eq_comm]
  rw [← LinearMap.charpoly_toMatrix _ (b.tensorProduct c), TensorProduct.toMatrix_map, he]
  have hd : (LinearMap.toMatrix b b f) ⊗ₖ (Matrix.diagonal eigen) =
      Matrix.blockDiagonal fun i => LinearMap.toMatrix b b (eigen i • f) := by
    ext ⟨i, k⟩ ⟨j, k'⟩
    simp only [Matrix.kroneckerMap_apply, Matrix.blockDiagonal_apply, Matrix.diagonal_apply,
      map_smul, Matrix.smul_apply, smul_eq_mul]
    split_ifs <;> simp [mul_comm]
  rw [hd, charpoly_blockDiagonal]
  exact Finset.prod_congr rfl fun i _ => LinearMap.charpoly_toMatrix _ _

theorem WD.lpTensor_sp_one (x : WD h) : x.lpTensor (lpSp 1) = x := by
  refine WD.ind (fun n a => ?_) x
  rw [lpSp, lpTensor_mk]
  have hρ (σ : Weil h) : (WDRep.sp h 1).ρ σ = 1 := by
    apply LinearMap.ext
    intro v
    funext i
    simp [specialEigenvalue]
  have hN : (WDRep.sp h 1).N = 0 := by
    apply LinearMap.ext
    intro v
    funext i
    rw [WDRep.sp_N, specialShift_apply, dif_neg (by omega)]
    rfl
  apply WD.sound
  apply WDRep.Iso.symm
  refine ⟨(TensorProduct.rid ℂ (Fin n → ℂ)).symm ≪≫ₗ
    TensorProduct.congr (LinearEquiv.refl ℂ _) (LinearEquiv.funUnique (Fin 1) ℂ ℂ).symm,
    fun σ v => ?_, fun v => ?_⟩
  · rw [WDRep.tensor_ρ, hρ σ]
    simp
  · rw [WDRep.tensor_N, hN]
    simp


namespace WD

/-- Attach a segment of the given length to its first parameter. -/
def lpSegment (x : WD h) (n : ℕ) : WD h :=
  (x.lpTw (((n : ℝ) - 1) / 2)).lpTensor (lpSp n)

theorem lpDim_segment (x : WD h) (n : ℕ) : (x.lpSegment n).lpDim = x.lpDim * n := by
  rw [lpSegment, lpDim_tensor, lpTw, lpDim_twist, lpDim_sp]

@[simp] theorem lpSegment_one (x : WD h) : x.lpSegment 1 = x := by
  simp [lpSegment, lpTensor_sp_one]

theorem charpoly_segment (x : WD h) (n : ℕ) (σ : Weil h) :
    (x.lpSegment n).charpoly σ = ∏ i : Fin n, (x.lpTw (i.val : ℝ)).charpoly σ := by
  refine WD.ind (fun m a => ?_) x
  rw [lpSegment, lpTw, lpTwist_mk, lpSp, lpTensor_mk, charpoly_mk, WDRep.tensor_ρ,
    charpoly_tensor_sp_ρ]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [lpTw, lpTwist_mk, charpoly_mk]
  have ht (s : ℝ) : (a.twist (unrChar h (qPow w s)) (isSmooth_unrChar h _)).ρ σ =
      (((qPow w s : ℂˣ) : ℂ) ^ deg σ) • a.ρ σ := by
    change (unrChar h (qPow w s) σ : ℂ) • a.ρ σ = _
    rw [unrChar_apply, Units.val_zpow_eq_zpow_val]
  have hq : specialEigenvalue w n i * qPow w (((n : ℝ) - 1) / 2) = qPow w (i.val : ℝ) := by
    rw [specialEigenvalue, ← qPow_add, sub_add_cancel]
  rw [ht, ht, smul_smul, ← mul_zpow, ← Units.val_mul, hq]

theorem charpoly_segment_inertia (x : WD h) (n : ℕ) (t : Ine (F := E) A) :
    (x.lpSegment n).charpoly (ineIncl h t) = (x.charpoly (ineIncl h t)) ^ n := by
  rw [charpoly_segment]
  simp only [lpTw, charpoly_unramified_twist_on_inertia, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

end WD

end GlobalTheory.WeilDeligne

#print axioms GlobalTheory.WeilDeligne.WD.lpTensor_sp_one
#print axioms GlobalTheory.WeilDeligne.WD.lpSegment_one
#print axioms GlobalTheory.WeilDeligne.WD.charpoly_segment
#print axioms GlobalTheory.WeilDeligne.WD.charpoly_segment_inertia
