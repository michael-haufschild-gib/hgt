import GaloisForLFunctions.HTGeometry.NumberFieldArchimedeanCone
import GaloisForLFunctions.HTGeometry.RealSchurPosDef
import GaloisForLFunctions.HTGeometry.ComplexSchurPosDef

/-!
# Placewise Schur descent on the number-field archimedean cone

The first coordinate and its tail are reindexed as an exact block matrix.  Positive definiteness
of the full form makes the head invertible, while real and complex Schur-complement theorems give
strict positivity of the tail.  Applying this at every infinite place constructs an unconditional
rank-lowering map on the corrected real/Hermitian archimedean cone.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix NumberField
open scoped Classical ComplexOrder NumberField

noncomputable section

variable {n : ℕ}

/-- Reindex one distinguished head coordinate followed by the remaining coordinates. -/
def matrixFirstTailIndex : Fin 1 ⊕ Fin n → Fin (n + 1)
  | Sum.inl _ => 0
  | Sum.inr i => i.succ

theorem matrixFirstTailIndex_injective :
    Function.Injective (matrixFirstTailIndex (n := n)) := by
  intro x y hxy
  cases x with
  | inl x =>
      cases y with
      | inl y => exact congrArg Sum.inl (Subsingleton.elim x y)
      | inr y =>
          exfalso
          have h := congrArg Fin.val hxy
          simp [matrixFirstTailIndex] at h
  | inr x =>
      cases y with
      | inl y =>
          exfalso
          have h := congrArg Fin.val hxy
          simp [matrixFirstTailIndex] at h
      | inr y =>
          exact congrArg Sum.inr (Fin.succ_injective n hxy)

def matrixFirstHead {R : Type*} [Zero R]
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) : Matrix (Fin 1) (Fin 1) R :=
  A.submatrix (fun _ => 0) (fun _ => 0)

def matrixFirstCross {R : Type*} [Zero R]
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) : Matrix (Fin 1) (Fin n) R :=
  A.submatrix (fun _ => 0) Fin.succ

def matrixFirstTail {R : Type*} [Zero R]
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) : Matrix (Fin n) (Fin n) R :=
  A.submatrix Fin.succ Fin.succ

def matrixFirstTailReindex {R : Type*} [Zero R]
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin n) R :=
  A.submatrix matrixFirstTailIndex matrixFirstTailIndex

theorem matrixFirstTailReindex_eq_fromBlocks
    {R : Type*} [Ring R] [StarRing R]
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) R} (hA : A.IsHermitian) :
    matrixFirstTailReindex A =
      fromBlocks (matrixFirstHead A) (matrixFirstCross A)
        (matrixFirstCross A)ᴴ (matrixFirstTail A) := by
  ext x y
  cases x with
  | inl x =>
      cases y with
      | inl y => rfl
      | inr y => rfl
  | inr x =>
      cases y with
      | inl y =>
          have h := congrFun (congrFun hA.eq x.succ) (0 : Fin (n + 1))
          simpa [matrixFirstTailReindex, matrixFirstTailIndex, matrixFirstCross,
            Matrix.conjTranspose_apply] using h.symm
      | inr y => rfl

theorem matrixFirstTailReindex_posDef
    {R : Type*} [Ring R] [PartialOrder R] [StarRing R]
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) R} (hA : A.PosDef) :
    (matrixFirstTailReindex A).PosDef :=
  hA.submatrix matrixFirstTailIndex_injective

theorem matrixFirstHead_posDef
    {R : Type*} [Ring R] [PartialOrder R] [StarRing R]
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) R} (hA : A.PosDef) :
    (matrixFirstHead A).PosDef := by
  exact hA.submatrix fun _ _ _ => Subsingleton.elim _ _

def matrixFirstSchur {R : Type*} [Field R] [StarRing R]
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) : Matrix (Fin n) (Fin n) R :=
  matrixFirstTail A -
    (matrixFirstCross A)ᴴ * (matrixFirstHead A)⁻¹ * matrixFirstCross A

theorem matrixFirstSchur_posDef_real
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (hA : A.PosDef) :
    (matrixFirstSchur A).PosDef := by
  have hhead := matrixFirstHead_posDef hA
  have hfull := matrixFirstTailReindex_posDef hA
  rw [matrixFirstTailReindex_eq_fromBlocks hA.isHermitian] at hfull
  have hsymm : (matrixFirstHead A)ᵀ = matrixFirstHead A := by
    have h := hhead.isHermitian.eq
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  simpa [matrixFirstSchur, Matrix.conjTranspose_eq_transpose_of_trivial] using
    schurComplement_posDef_real hhead.isUnit hsymm
      (matrixFirstCross A) (matrixFirstTail A) hfull

theorem matrixFirstSchur_posDef_complex
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hA : A.PosDef) :
    (matrixFirstSchur A).PosDef := by
  have hhead := matrixFirstHead_posDef hA
  have hfull := matrixFirstTailReindex_posDef hA
  rw [matrixFirstTailReindex_eq_fromBlocks hA.isHermitian] at hfull
  simpa [matrixFirstSchur] using
    schurComplement_posDef_complex hhead.isUnit hhead.isHermitian
      (matrixFirstCross A) (matrixFirstTail A) hfull

variable {K : Type*} [Field K] [NumberField K]

/-- Placewise real/Hermitian Schur descent lowers the rank of every archimedean cone point. -/
def numberFieldArchimedeanSchur
    (A : numberFieldArchimedeanPositiveForms K (n + 1)) :
    numberFieldArchimedeanPositiveForms K n := by
  let realS := fun w : {w : InfinitePlace K // w.IsReal} =>
    matrixFirstSchur (A.1.1 w : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
  let complexS := fun w : {w : InfinitePlace K // w.IsComplex} =>
    matrixFirstSchur (A.1.2 w : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
  have hreal : ∀ w, (realS w).PosDef := fun w => matrixFirstSchur_posDef_real (A.2.1 w)
  have hcomplex : ∀ w, (complexS w).PosDef :=
    fun w => matrixFirstSchur_posDef_complex (A.2.2 w)
  refine ⟨(fun w => ⟨realS w, (hreal w).isHermitian⟩,
    fun w => ⟨complexS w, (hcomplex w).isHermitian⟩), ?_⟩
  exact ⟨hreal, hcomplex⟩

end

end GaloisForLFunctions.HTGeometry
