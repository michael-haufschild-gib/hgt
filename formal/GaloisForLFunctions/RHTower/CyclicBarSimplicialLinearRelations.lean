import GaloisForLFunctions.RHTower.CyclicBarSimplicialTupleRelations

/-!
# Simplicial identities for cyclic-bar tensor operators

Tuple identities lift through the universal property of `PiTensorProduct`.  The resulting six
linear-map equalities are exactly the relations used to quotient the free simplex quiver.
-/

noncomputable section

namespace GaloisForLFunctions
namespace RHTower

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- Linear face--face identity. -/
theorem cyclicBarFace_comp_face {n : ℕ} (i j : Fin (n + 2)) (hij : i ≤ j) :
    (cyclicBarFace (R := R) (A := A) i).comp
        (cyclicBarFace (R := R) (A := A) j.succ) =
      (cyclicBarFace (R := R) (A := A) j).comp
        (cyclicBarFace (R := R) (A := A) i.castSucc) := by
  apply PiTensorProduct.ext
  ext x
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.coe_comp,
    Function.comp_apply, cyclicBarFace_tprod]
  rw [cyclicBarFaceTuple_faceTuple i j hij x]

/-- Linear face--degeneracy identity before the inserted unit. -/
theorem cyclicBarFace_comp_degeneracy_of_le {n : ℕ} (i : Fin (n + 2))
    (j : Fin (n + 1)) (hij : i ≤ j.castSucc) :
    (cyclicBarFace (R := R) (A := A) i.castSucc).comp
        (cyclicBarDegeneracy (R := R) (A := A) j.succ) =
      (cyclicBarDegeneracy (R := R) (A := A) j).comp
        (cyclicBarFace (R := R) (A := A) i) := by
  apply PiTensorProduct.ext
  ext x
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.coe_comp,
    Function.comp_apply, cyclicBarDegeneracy_tprod, cyclicBarFace_tprod]
  rw [cyclicBarFaceTuple_degeneracyTuple_of_le i j hij x]

/-- First linear face cancellation identity. -/
theorem cyclicBarFace_comp_degeneracy_self {n : ℕ} (i : Fin (n + 1)) :
    (cyclicBarFace (R := R) (A := A) i.castSucc).comp
        (cyclicBarDegeneracy (R := R) (A := A) i) =
      LinearMap.id := by
  apply PiTensorProduct.ext
  ext x
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.coe_comp,
    Function.comp_apply, cyclicBarDegeneracy_tprod, cyclicBarFace_tprod,
    LinearMap.id_compMultilinearMap]
  rw [cyclicBarFaceTuple_degeneracyTuple_self]

/-- Second linear face cancellation identity. -/
theorem cyclicBarFace_comp_degeneracy_succ {n : ℕ} (i : Fin (n + 1)) :
    (cyclicBarFace (R := R) (A := A) i.succ).comp
        (cyclicBarDegeneracy (R := R) (A := A) i) =
      LinearMap.id := by
  apply PiTensorProduct.ext
  ext x
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.coe_comp,
    Function.comp_apply, cyclicBarDegeneracy_tprod, cyclicBarFace_tprod,
    LinearMap.id_compMultilinearMap]
  rw [cyclicBarFaceTuple_degeneracyTuple_succ]

/-- Linear face--degeneracy identity after the inserted unit, including the wrap face. -/
theorem cyclicBarFace_comp_degeneracy_of_gt {n : ℕ} (i : Fin (n + 2))
    (j : Fin (n + 1)) (hji : j.castSucc < i) :
    (cyclicBarFace (R := R) (A := A) i.succ).comp
        (cyclicBarDegeneracy (R := R) (A := A) j.castSucc) =
      (cyclicBarDegeneracy (R := R) (A := A) j).comp
        (cyclicBarFace (R := R) (A := A) i) := by
  apply PiTensorProduct.ext
  ext x
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.coe_comp,
    Function.comp_apply, cyclicBarDegeneracy_tprod, cyclicBarFace_tprod]
  rw [cyclicBarFaceTuple_degeneracyTuple_of_gt i j hji x]

/-- Linear degeneracy--degeneracy identity. -/
theorem cyclicBarDegeneracy_comp_degeneracy {n : ℕ} (i j : Fin (n + 1))
    (hij : i ≤ j) :
    (cyclicBarDegeneracy (R := R) (A := A) i.castSucc).comp
        (cyclicBarDegeneracy (R := R) (A := A) j) =
      (cyclicBarDegeneracy (R := R) (A := A) j.succ).comp
        (cyclicBarDegeneracy (R := R) (A := A) i) := by
  apply PiTensorProduct.ext
  ext x
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.coe_comp,
    Function.comp_apply, cyclicBarDegeneracy_tprod]
  rw [cyclicBarDegeneracyTuple_degeneracyTuple i j hij x]

end RHTower
end GaloisForLFunctions
