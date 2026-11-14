import GaloisForLFunctions.HTGeometry.NomologicalHomotopyGeometry.StructuredMorita
import GaloisForLFunctions.HTGeometry.LinearAlgebra.SymmetricBorder
import Mathlib.Algebra.CharP.Two
import Mathlib.FieldTheory.Finite.Basic

/-!
# Symmetrizing the binary Selmer matrix

The rank-one shear `T=I+1yᵀ` identifies the kernels of the two block
matrices `[[A,Dy],[Dz,A+Dy]]` and `[[A+Aᵀ,Aᵀ],[A,Dz]]`.
The change of coordinates and its inverse are explicit. The proof uses
the row-sum and quadratic-reciprocity identities, then applies the
general kernel transport theorem for a commuting equivalence square.
-/

namespace GaloisForLFunctions.HTGeometry.LinearAlgebra

open Matrix
open _root_.HTGeometry.NomologicalHomotopyGeometry.StructuredMorita

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
private theorem binaryMatrix_add_self (B : Matrix ι ι (ZMod 2)) : B + B = 0 := by
  ext i j
  exact CharTwo.add_self_eq_zero _

/-- The rank-one shear used to symmetrize the two-descent equations. -/
def binarySelmerShear (y : ι → ZMod 2) : Matrix ι ι (ZMod 2) :=
  1 + vecMulVec 1 y

theorem binarySelmerShear_sq (y : ι → ZMod 2) (hy : y ⬝ᵥ 1 = 0) :
    binarySelmerShear y * binarySelmerShear y = 1 := by
  have hN : vecMulVec (1 : ι → ZMod 2) y * vecMulVec 1 y = 0 := by
    rw [vecMulVec_mul_vecMulVec, hy, zero_smul]
    ext i j
    simp [vecMulVec]
  unfold binarySelmerShear
  calc
    (1 + vecMulVec 1 y) * (1 + vecMulVec 1 y) =
        (1 + vecMulVec 1 y) + (vecMulVec 1 y + vecMulVec 1 y * vecMulVec 1 y) := by
      simp only [add_mul, mul_add, one_mul, mul_one]
    _ = 1 + (vecMulVec 1 y + vecMulVec 1 y) := by rw [hN, add_zero]; abel
    _ = 1 := by rw [binaryMatrix_add_self, add_zero]

theorem binarySelmer_mul_shear (A : Matrix ι ι (ZMod 2)) (y : ι → ZMod 2)
    (hA : A *ᵥ 1 = 0) : A * binarySelmerShear y = A := by
  rw [binarySelmerShear, mul_add, mul_one, mul_vecMulVec, hA]
  ext i j
  simp [vecMulVec]

/-- Row sums and reciprocity determine the column sums. -/
theorem binarySelmer_transpose_one (A : Matrix ι ι (ZMod 2)) (y : ι → ZMod 2)
    (hA : A *ᵥ 1 = 0) (hrec : A + Aᵀ = vecMulVec y y + diagonal y)
    (hy : y ⬝ᵥ 1 = 0) : Aᵀ *ᵥ 1 = y := by
  have h : (A + Aᵀ) *ᵥ 1 = y := by
    rw [hrec, add_mulVec]
    simp [vecMulVec_mulVec, hy]
    funext i
    simp only [mulVec_diagonal, Pi.one_apply, mul_one]
  simpa only [add_mulVec, hA, zero_add] using h

theorem binarySelmer_symmetric_mul_shear (A : Matrix ι ι (ZMod 2)) (y : ι → ZMod 2)
    (hA : A *ᵥ 1 = 0) (hrec : A + Aᵀ = vecMulVec y y + diagonal y)
    (hy : y ⬝ᵥ 1 = 0) : (A + Aᵀ) * binarySelmerShear y = diagonal y := by
  have hcol : (A + Aᵀ) *ᵥ 1 = y := by
    rw [add_mulVec, hA, binarySelmer_transpose_one A y hA hrec hy, zero_add]
  rw [binarySelmerShear, mul_add, mul_one, mul_vecMulVec, hcol, hrec]
  calc
    (vecMulVec y y + diagonal y) + vecMulVec y y =
        diagonal y + (vecMulVec y y + vecMulVec y y) := by abel
    _ = diagonal y := by rw [binaryMatrix_add_self, add_zero]

/-- The nonsymmetric matrix encoding the two local descent equations. -/
def binarySelmerSource (A : Matrix ι ι (ZMod 2)) (y z : ι → ZMod 2) :
    Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2) :=
  fromBlocks A (diagonal y) (diagonal z) (A + diagonal y)

/-- The symmetric matrix associated with the same descent equations. -/
def binarySelmerSymmetric (A : Matrix ι ι (ZMod 2)) (z : ι → ZMod 2) :
    Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2) :=
  fromBlocks (A + Aᵀ) Aᵀ A (diagonal z)

/-- Forward change of variables `(u,v) ↦ (u+Tv,u)`. -/
def binarySelmerChange (y : ι → ZMod 2) :
    Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2) :=
  fromBlocks 1 (binarySelmerShear y) 1 0

/-- Inverse change of variables `(u,v) ↦ (v,T(u+v))`. -/
def binarySelmerChangeInv (y : ι → ZMod 2) :
    Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2) :=
  fromBlocks 0 1 (binarySelmerShear y) (binarySelmerShear y)

/-- Adding the first block row to the second is an involution. -/
def binarySelmerRowChange : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2) :=
  fromBlocks 1 0 1 1

theorem binarySelmerChange_mul_inv (y : ι → ZMod 2) (hy : y ⬝ᵥ 1 = 0) :
    binarySelmerChange y * binarySelmerChangeInv y = 1 := by
  simp only [binarySelmerChange, binarySelmerChangeInv, fromBlocks_multiply,
    mul_zero, zero_mul, mul_one, add_zero, zero_add, binarySelmerShear_sq y hy]
  rw [binaryMatrix_add_self, fromBlocks_one]

theorem binarySelmerChange_inv_mul (y : ι → ZMod 2) (hy : y ⬝ᵥ 1 = 0) :
    binarySelmerChangeInv y * binarySelmerChange y = 1 := by
  simp only [binarySelmerChange, binarySelmerChangeInv, fromBlocks_multiply,
    mul_zero, zero_mul, mul_one, add_zero, zero_add, binarySelmerShear_sq y hy]
  rw [binaryMatrix_add_self, fromBlocks_one]

theorem binarySelmerRowChange_sq :
    (binarySelmerRowChange (ι := ι)) * binarySelmerRowChange = 1 := by
  simp only [binarySelmerRowChange, fromBlocks_multiply, mul_zero,
    mul_one, add_zero, zero_add]
  rw [binaryMatrix_add_self, fromBlocks_one]

/-- The explicit equivalence square relating the two block matrices. -/
theorem binarySelmer_intertwining (A : Matrix ι ι (ZMod 2)) (y z : ι → ZMod 2)
    (hA : A *ᵥ 1 = 0) (hrec : A + Aᵀ = vecMulVec y y + diagonal y)
    (hy : y ⬝ᵥ 1 = 0) :
    binarySelmerSymmetric A z * binarySelmerChange y =
      binarySelmerRowChange * binarySelmerSource A y z := by
  simp only [binarySelmerSymmetric, binarySelmerChange, binarySelmerRowChange,
    binarySelmerSource, fromBlocks_multiply, mul_zero, zero_mul, one_mul, mul_one,
    add_zero, binarySelmer_mul_shear A y hA,
    binarySelmer_symmetric_mul_shear A y hA hrec hy]
  have htop : A + Aᵀ + Aᵀ = A := by
    rw [add_assoc, binaryMatrix_add_self, add_zero]
  have hbottom : diagonal y + (A + diagonal y) = A := by
    calc
      diagonal y + (A + diagonal y) = A + (diagonal y + diagonal y) := by abel
      _ = A := by rw [binaryMatrix_add_self, add_zero]
  rw [htop, hbottom]

/-- The change of variables is an equivalence on the entire ambient space. -/
def binarySelmerChangeEquiv (y : ι → ZMod 2) (hy : y ⬝ᵥ 1 = 0) :
    (ι ⊕ ι → ZMod 2) ≃ₗ[ZMod 2] (ι ⊕ ι → ZMod 2) :=
  LinearEquiv.ofLinear (binarySelmerChange y).mulVecLin
    (binarySelmerChangeInv y).mulVecLin
    (by ext v; simp only [LinearMap.comp_apply, mulVecLin_apply, mulVec_mulVec,
      binarySelmerChange_mul_inv y hy, one_mulVec, LinearMap.id_apply])
    (by ext v; simp only [LinearMap.comp_apply, mulVecLin_apply, mulVec_mulVec,
      binarySelmerChange_inv_mul y hy, one_mulVec, LinearMap.id_apply])

/-- The row operation is a linear involution on the equation space. -/
def binarySelmerRowEquiv :
    (ι ⊕ ι → ZMod 2) ≃ₗ[ZMod 2] (ι ⊕ ι → ZMod 2) :=
  LinearEquiv.ofLinear binarySelmerRowChange.mulVecLin binarySelmerRowChange.mulVecLin
    (by ext v; simp only [LinearMap.comp_apply, mulVecLin_apply, mulVec_mulVec,
      binarySelmerRowChange_sq, one_mulVec, LinearMap.id_apply])
    (by ext v; simp only [LinearMap.comp_apply, mulVecLin_apply, mulVec_mulVec,
      binarySelmerRowChange_sq, one_mulVec, LinearMap.id_apply])

/-- Explicit isomorphism between the nonsymmetric and symmetric kernels. -/
def binarySelmerKernelEquiv (A : Matrix ι ι (ZMod 2)) (y z : ι → ZMod 2)
    (hA : A *ᵥ 1 = 0) (hrec : A + Aᵀ = vecMulVec y y + diagonal y)
    (hy : y ⬝ᵥ 1 = 0) :
    LinearMap.ker (binarySelmerSource A y z).mulVecLin ≃ₗ[ZMod 2]
      LinearMap.ker (binarySelmerSymmetric A z).mulVecLin :=
  mapKernelEquiv (binarySelmerChangeEquiv y hy) binarySelmerRowEquiv
    (binarySelmerSource A y z).mulVecLin (binarySelmerSymmetric A z).mulVecLin (by
      apply LinearMap.ext
      intro v
      change binarySelmerRowChange *ᵥ (binarySelmerSource A y z *ᵥ v) =
        binarySelmerSymmetric A z *ᵥ (binarySelmerChange y *ᵥ v)
      rw [mulVec_mulVec, mulVec_mulVec, binarySelmer_intertwining A y z hA hrec hy])

theorem binarySelmer_kernel_finrank (A : Matrix ι ι (ZMod 2)) (y z : ι → ZMod 2)
    (hA : A *ᵥ 1 = 0) (hrec : A + Aᵀ = vecMulVec y y + diagonal y)
    (hy : y ⬝ᵥ 1 = 0) :
    Module.finrank (ZMod 2) (LinearMap.ker (binarySelmerSource A y z).mulVecLin) =
      Module.finrank (ZMod 2) (LinearMap.ker (binarySelmerSymmetric A z).mulVecLin) :=
  (binarySelmerKernelEquiv A y z hA hrec hy).finrank_eq

#print axioms binarySelmerKernelEquiv
#print axioms binarySelmer_kernel_finrank

end GaloisForLFunctions.HTGeometry.LinearAlgebra
