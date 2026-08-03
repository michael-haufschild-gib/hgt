import GaloisForLFunctions.RHTower.CyclicBarCyclicTupleRelations
import GaloisForLFunctions.RHTower.KRealCyclicModule

/-!
# Connes cyclic identities on bar tensor powers

The tuple-level cyclic identities lift to linear maps by the universal property of indexed tensor
products.  The final theorem proves categorical order directly on pure tensors and then invokes
their spanning property.
-/

noncomputable section

open CategoryTheory

namespace GaloisForLFunctions
namespace RHTower

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

theorem cyclicBarRotate_comp_face_zero {n : ℕ} :
    (cyclicBarFace (R := R) (A := A) (0 : Fin (n + 2))).comp
        (cyclicBarRotate (R := R) (A := A) (n + 1)).toLinearMap =
      cyclicBarFace (R := R) (A := A) (Fin.last (n + 1)) := by
  apply PiTensorProduct.ext
  ext x
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.coe_comp,
    Function.comp_apply, cyclicBarFace_tprod]
  change cyclicBarFace (R := R) (A := A) 0
      (cyclicBarRotate (R := R) (A := A) (n + 1) (PiTensorProduct.tprod R x)) = _
  rw [cyclicBarRotate_tprod, cyclicBarFace_tprod]
  rw [cyclicBarFaceTuple_rotate_zero]

theorem cyclicBarRotate_comp_face_succ {n : ℕ} (i : Fin (n + 1)) :
    (cyclicBarFace (R := R) (A := A) i.succ).comp
        (cyclicBarRotate (R := R) (A := A) (n + 1)).toLinearMap =
      (cyclicBarRotate (R := R) (A := A) n).toLinearMap.comp
        (cyclicBarFace (R := R) (A := A) i.castSucc) := by
  apply PiTensorProduct.ext
  ext x
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.coe_comp,
    Function.comp_apply, cyclicBarFace_tprod]
  change cyclicBarFace (R := R) (A := A) i.succ
      (cyclicBarRotate (R := R) (A := A) (n + 1) (PiTensorProduct.tprod R x)) =
    cyclicBarRotate (R := R) (A := A) n
      (PiTensorProduct.tprod R (cyclicBarFaceTuple i.castSucc x))
  rw [cyclicBarRotate_tprod, cyclicBarFace_tprod, cyclicBarRotate_tprod]
  rw [cyclicBarFaceTuple_rotate_succ]

theorem cyclicBarRotate_comp_degeneracy_zero {n : ℕ} :
    (cyclicBarDegeneracy (R := R) (A := A) (0 : Fin (n + 1))).comp
        (cyclicBarRotate (R := R) (A := A) n).toLinearMap =
      (cyclicBarRotate (R := R) (A := A) (n + 1)).toLinearMap.comp
        ((cyclicBarRotate (R := R) (A := A) (n + 1)).toLinearMap.comp
          (cyclicBarDegeneracy (R := R) (A := A) (Fin.last n))) := by
  apply PiTensorProduct.ext
  ext x
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.coe_comp,
    Function.comp_apply, cyclicBarDegeneracy_tprod]
  change cyclicBarDegeneracy (R := R) (A := A) 0
      (cyclicBarRotate (R := R) (A := A) n (PiTensorProduct.tprod R x)) =
    cyclicBarRotate (R := R) (A := A) (n + 1)
      (cyclicBarRotate (R := R) (A := A) (n + 1)
        (PiTensorProduct.tprod R (cyclicBarDegeneracyTuple (Fin.last n) x)))
  rw [cyclicBarRotate_tprod, cyclicBarDegeneracy_tprod,
    cyclicBarRotate_tprod, cyclicBarRotate_tprod]
  rw [cyclicBarDegeneracyTuple_rotate_zero]

theorem cyclicBarRotate_comp_degeneracy_succ {n : ℕ} (i : Fin n) :
    (cyclicBarDegeneracy (R := R) (A := A) i.succ).comp
        (cyclicBarRotate (R := R) (A := A) n).toLinearMap =
      (cyclicBarRotate (R := R) (A := A) (n + 1)).toLinearMap.comp
        (cyclicBarDegeneracy (R := R) (A := A) i.castSucc) := by
  apply PiTensorProduct.ext
  ext x
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.coe_comp,
    Function.comp_apply, cyclicBarDegeneracy_tprod]
  change cyclicBarDegeneracy (R := R) (A := A) i.succ
      (cyclicBarRotate (R := R) (A := A) n (PiTensorProduct.tprod R x)) =
    cyclicBarRotate (R := R) (A := A) (n + 1)
      (PiTensorProduct.tprod R (cyclicBarDegeneracyTuple i.castSucc x))
  rw [cyclicBarRotate_tprod, cyclicBarDegeneracy_tprod, cyclicBarRotate_tprod]
  rw [cyclicBarDegeneracyTuple_rotate_succ]

/-- Categorical iterates of tensor rotation act on pure tensors by iterated tuple rotation. -/
theorem cyclicBar_categoricalRotateIterate_tprod (n m : ℕ)
    (x : Fin (n + 1) → A) :
    categoricalEndIterate
        (ModuleCat.ofHom (cyclicBarRotate (R := R) (A := A) n).toLinearMap) m
        (PiTensorProduct.tprod R x) =
      PiTensorProduct.tprod R
        (((cyclicBarRotateTuple : (Fin (n + 1) → A) → (Fin (n + 1) → A))^[m]) x) := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [categoricalEndIterate_succ, ModuleCat.comp_apply, ih,
        ModuleCat.ofHom_apply]
      change cyclicBarRotate (R := R) (A := A) n
          (PiTensorProduct.tprod R
            (((cyclicBarRotateTuple : (Fin (n + 1) → A) → (Fin (n + 1) → A))^[m]) x)) = _
      rw [cyclicBarRotate_tprod]
      rw [Function.iterate_succ_apply']

/-- Tensor rotation has categorical order `n+1`. -/
theorem cyclicBar_categoricalRotate_order (n : ℕ) :
    categoricalEndIterate
        (ModuleCat.ofHom (cyclicBarRotate (R := R) (A := A) n).toLinearMap) (n + 1) =
      𝟙 (ModuleCat.of R (CyclicBarTensor R A n)) := by
  apply ModuleCat.hom_ext
  apply PiTensorProduct.ext
  ext x
  change categoricalEndIterate
      (ModuleCat.ofHom (cyclicBarRotate (R := R) (A := A) n).toLinearMap) (n + 1)
      (PiTensorProduct.tprod R x) = PiTensorProduct.tprod R x
  rw [cyclicBar_categoricalRotateIterate_tprod, cyclicBarRotateTuple_order]

end RHTower
end GaloisForLFunctions
