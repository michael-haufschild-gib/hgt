import GaloisForLFunctions.RHTower.KRealPiTensorProduct
import GaloisForLFunctions.RHTower.KRealCyclicWord
import GaloisForLFunctions.RHTower.CyclicBarCyclicModule

/-!
# Real structure on the genuine cyclic bar construction

This file lifts a `KRealAlgebraStructure` componentwise to the actual indexed tensor powers of
the cyclic bar construction.  It proves compatibility with every face, degeneracy, and cyclic
rotation map.  No free-word or degree-zero replacement is used.
-/

noncomputable section

open scoped TensorProduct

namespace GaloisForLFunctions.RHTower

variable {A : Type*} [Ring A] [Algebra ℂ A]

theorem kRealAlgebra_sigma_cyclicBarFaceTuple
    (K : KRealAlgebraStructure A) {n : ℕ} (i : Fin (n + 2))
    (x : Fin (n + 2) → A) :
    (fun j => K.sigma (cyclicBarFaceTuple i x j)) =
      cyclicBarFaceTuple i (fun j => K.sigma (x j)) := by
  induction i using Fin.lastCases with
  | last =>
      funext j
      by_cases hj : j = 0
      · subst j
        simp [cyclicBarFaceTuple, cyclicBarFaceWrapTuple, K.map_mul]
      · simp only [cyclicBarFaceTuple, Fin.lastCases_last,
          cyclicBarFaceWrapTuple, Function.update_of_ne hj,
          Fin.removeNth_last]
        rfl
  | cast i =>
      funext j
      by_cases hji : j = i
      · subst j
        simp [cyclicBarFaceTuple, cyclicBarFaceNonwrapTuple,
          K.map_mul]
      · simp [cyclicBarFaceTuple, cyclicBarFaceNonwrapTuple,
          Fin.removeNth, Function.update_of_ne hji]

theorem kRealAlgebra_sigma_cyclicBarDegeneracyTuple
    (K : KRealAlgebraStructure A) {n : ℕ} (i : Fin (n + 1))
    (x : Fin (n + 1) → A) :
    (fun j => K.sigma (cyclicBarDegeneracyTuple i x j)) =
      cyclicBarDegeneracyTuple i (fun j => K.sigma (x j)) := by
  funext j
  by_cases hj : j = i.succ
  · subst j
    simp [cyclicBarDegeneracyTuple, Fin.insertNth, Fin.succAboveCases,
      K.map_one]
  · by_cases hjlt : j < i.succ
    · simp [cyclicBarDegeneracyTuple, Fin.insertNth, Fin.succAboveCases,
        hj, hjlt]
    · simp [cyclicBarDegeneracyTuple, Fin.insertNth, Fin.succAboveCases,
        hj, hjlt]

theorem kRealAlgebra_sigma_cyclicBarRotateTuple
    (K : KRealAlgebraStructure A) {n : ℕ}
    (x : Fin (n + 1) → A) :
    (fun j => K.sigma (cyclicBarRotateTuple x j)) =
      cyclicBarRotateTuple (fun j => K.sigma (x j)) := by
  rfl

/-- Componentwise even Real structure on degree `n` of the genuine cyclic bar construction. -/
def cyclicBarDegreeKReal (K : KRealAlgebraStructure A) (n : ℕ) :
    KRealStructure false (CyclicBarTensor ℂ A n) :=
  kRealEvenPiTensorProduct (fun _ : Fin (n + 1) => K.toKRealStructure)

theorem cyclicBarDegreeKReal_face
    (K : KRealAlgebraStructure A) {n : ℕ} (i : Fin (n + 2))
    (x : CyclicBarTensor ℂ A (n + 1)) :
    (cyclicBarDegreeKReal K n).sigma (cyclicBarFace i x) =
      cyclicBarFace i ((cyclicBarDegreeKReal K (n + 1)).sigma x) := by
  induction x using PiTensorProduct.induction_on' with
  | tprodCoeff r f =>
      change kRealEvenPiTensorSigma (fun _ : Fin (n + 1) => K.toKRealStructure)
          (cyclicBarFace i (PiTensorProduct.tprodCoeff ℂ r f)) =
        cyclicBarFace i
          (kRealEvenPiTensorSigma
            (fun _ : Fin (n + 2) => K.toKRealStructure)
            (PiTensorProduct.tprodCoeff ℂ r f))
      rw [PiTensorProduct.tprodCoeff_eq_smul_tprod, map_smul,
        cyclicBarFace_tprod, map_smulₛₗ, kRealEvenPiTensorSigma_tprod,
        map_smulₛₗ, map_smul (cyclicBarFace i),
        kRealEvenPiTensorSigma_tprod, cyclicBarFace_tprod]
      rw [kRealAlgebra_sigma_cyclicBarFaceTuple K i f]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem cyclicBarDegreeKReal_degeneracy
    (K : KRealAlgebraStructure A) {n : ℕ} (i : Fin (n + 1))
    (x : CyclicBarTensor ℂ A n) :
    (cyclicBarDegreeKReal K (n + 1)).sigma (cyclicBarDegeneracy i x) =
      cyclicBarDegeneracy i ((cyclicBarDegreeKReal K n).sigma x) := by
  induction x using PiTensorProduct.induction_on' with
  | tprodCoeff r f =>
      change kRealEvenPiTensorSigma (fun _ : Fin (n + 2) => K.toKRealStructure)
          (cyclicBarDegeneracy i (PiTensorProduct.tprodCoeff ℂ r f)) =
        cyclicBarDegeneracy i
          (kRealEvenPiTensorSigma
            (fun _ : Fin (n + 1) => K.toKRealStructure)
            (PiTensorProduct.tprodCoeff ℂ r f))
      rw [PiTensorProduct.tprodCoeff_eq_smul_tprod, map_smul,
        cyclicBarDegeneracy_tprod, map_smulₛₗ, kRealEvenPiTensorSigma_tprod,
        map_smulₛₗ, map_smul (cyclicBarDegeneracy i),
        kRealEvenPiTensorSigma_tprod, cyclicBarDegeneracy_tprod]
      rw [kRealAlgebra_sigma_cyclicBarDegeneracyTuple K i f]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem cyclicBarDegreeKReal_rotate
    (K : KRealAlgebraStructure A) (n : ℕ)
    (x : CyclicBarTensor ℂ A n) :
    (cyclicBarDegreeKReal K n).sigma (cyclicBarRotate n x) =
      cyclicBarRotate n ((cyclicBarDegreeKReal K n).sigma x) := by
  induction x using PiTensorProduct.induction_on' with
  | tprodCoeff r f =>
      change kRealEvenPiTensorSigma (fun _ : Fin (n + 1) => K.toKRealStructure)
          (cyclicBarRotate n (PiTensorProduct.tprodCoeff ℂ r f)) =
        cyclicBarRotate n
          (kRealEvenPiTensorSigma
            (fun _ : Fin (n + 1) => K.toKRealStructure)
            (PiTensorProduct.tprodCoeff ℂ r f))
      rw [PiTensorProduct.tprodCoeff_eq_smul_tprod, map_smul,
        cyclicBarRotate_tprod, map_smulₛₗ, kRealEvenPiTensorSigma_tprod,
        map_smulₛₗ, map_smul (cyclicBarRotate n),
        kRealEvenPiTensorSigma_tprod, cyclicBarRotate_tprod]
      rw [kRealAlgebra_sigma_cyclicBarRotateTuple K f]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Even Real structure on the genuine cyclic bar cyclic module of a Real algebra. -/
def cyclicBarKReal (K : KRealAlgebraStructure A) :
    CyclicModule.KReal false (cyclicBarCyclicModule (R := ℂ) (A := A)) where
  real := cyclicBarDegreeKReal K
  face_naturality _n i x := cyclicBarDegreeKReal_face K i x
  degeneracy_naturality _n i x := cyclicBarDegreeKReal_degeneracy K i x
  cyclic_naturality n x := cyclicBarDegreeKReal_rotate K n x

end GaloisForLFunctions.RHTower
