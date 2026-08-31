import GaloisForLFunctions.HTGeometry.NumberFieldArchimedeanSchur
import GaloisForLFunctions.HTGeometry.SmithNormalFormDVR

/-!
# Tail actions and Schur descent

An action on the first Schur tail lifts block-diagonally while fixing the head coordinate.  The
lift preserves determinant and Schur descent turns its full congruence action into the original
tail congruence.  This is the recursive-action bridge required by the number-field greedy flag.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix NumberField

variable {n : ℕ}

/-- Block-diagonal lift fixing the first coordinate and acting by `B` on its tail. -/
def matrixFirstTailLift {R : Type*} [Zero R] [One R]
    (B : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  Fin.cases (Fin.cases 1 (fun _ => 0))
    (fun i => Fin.cases 0 (fun j => B i j))

@[simp]
theorem matrixFirstTailLift_zero_zero {R : Type*} [Zero R] [One R]
    (B : Matrix (Fin n) (Fin n) R) : matrixFirstTailLift B 0 0 = 1 := rfl

@[simp]
theorem matrixFirstTailLift_zero_succ {R : Type*} [Zero R] [One R]
    (B : Matrix (Fin n) (Fin n) R) (j : Fin n) :
    matrixFirstTailLift B 0 j.succ = 0 := rfl

@[simp]
theorem matrixFirstTailLift_succ_zero {R : Type*} [Zero R] [One R]
    (B : Matrix (Fin n) (Fin n) R) (i : Fin n) :
    matrixFirstTailLift B i.succ 0 = 0 := rfl

@[simp]
theorem matrixFirstTailLift_succ_succ {R : Type*} [Zero R] [One R]
    (B : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    matrixFirstTailLift B i.succ j.succ = B i j := rfl

@[simp]
theorem matrixFirstTail_matrixFirstTailLift {R : Type*} [Zero R] [One R]
    (B : Matrix (Fin n) (Fin n) R) :
    matrixFirstTail (matrixFirstTailLift B) = B := by
  ext i j
  rfl

/-- The determinant of the head-fixed lift is the tail determinant. -/
theorem det_matrixFirstTailLift {R : Type*} [CommRing R]
    (B : Matrix (Fin n) (Fin n) R) :
    (matrixFirstTailLift B).det = B.det := by
  rw [det_of_firstRow (matrixFirstTailLift B) (fun j => rfl)]
  rw [show (matrixFirstTailLift B).submatrix Fin.succ Fin.succ = B by
    ext i j
    rfl]
  simp

@[simp]
theorem map_matrixFirstTailLift {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (B : Matrix (Fin n) (Fin n) R) :
    (matrixFirstTailLift B).map f = matrixFirstTailLift (B.map f) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;> simp

@[simp]
theorem conjTranspose_matrixFirstTailLift {R : Type*}
    [CommRing R] [StarRing R]
    (B : Matrix (Fin n) (Fin n) R) :
    (matrixFirstTailLift B)ᴴ = matrixFirstTailLift Bᴴ := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [Matrix.conjTranspose_apply]

/-- Head-fixed lifts respect multiplication. -/
theorem matrixFirstTailLift_mul {R : Type*} [CommRing R]
    (B C : Matrix (Fin n) (Fin n) R) :
    matrixFirstTailLift B * matrixFirstTailLift C = matrixFirstTailLift (B * C) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ]

/-- The lifted congruence leaves the first head block unchanged. -/
theorem matrixFirstHead_lift_congr {R : Type*} [CommRing R] [StarRing R]
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (B : Matrix (Fin n) (Fin n) R) :
    matrixFirstHead (matrixFirstTailLift B * A * (matrixFirstTailLift B)ᴴ) =
      matrixFirstHead A := by
  ext i j
  fin_cases i
  fin_cases j
  simp [matrixFirstHead, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The lifted congruence sends the first cross block to `cross · Bᴴ`. -/
theorem matrixFirstCross_lift_congr {R : Type*} [CommRing R] [StarRing R]
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (B : Matrix (Fin n) (Fin n) R) :
    matrixFirstCross (matrixFirstTailLift B * A * (matrixFirstTailLift B)ᴴ) =
      matrixFirstCross A * Bᴴ := by
  ext i j
  fin_cases i
  simp [matrixFirstCross, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The lifted congruence acts on the first tail block by congruence with `B`. -/
theorem matrixFirstTail_lift_congr {R : Type*} [CommRing R] [StarRing R]
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (B : Matrix (Fin n) (Fin n) R) :
    matrixFirstTail (matrixFirstTailLift B * A * (matrixFirstTailLift B)ᴴ) =
      B * matrixFirstTail A * Bᴴ := by
  ext i j
  simp [matrixFirstTail, Matrix.mul_apply, Fin.sum_univ_succ]

/-- Schur descent intertwines a head-fixed congruence with the tail congruence. -/
theorem matrixFirstSchur_lift_congr {R : Type*} [Field R] [StarRing R]
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (B : Matrix (Fin n) (Fin n) R) :
    matrixFirstSchur (matrixFirstTailLift B * A * (matrixFirstTailLift B)ᴴ) =
      B * matrixFirstSchur A * Bᴴ := by
  rw [matrixFirstSchur, matrixFirstTail_lift_congr,
    matrixFirstCross_lift_congr, matrixFirstHead_lift_congr,
    matrixFirstSchur, Matrix.conjTranspose_mul]
  rw [Matrix.conjTranspose_conjTranspose]
  simp only [sub_mul, mul_sub, mul_assoc]
  congr 1
  calc
    B * (matrixFirstCross A)ᴴ * (matrixFirstHead A)⁻¹ *
          (matrixFirstCross A * Bᴴ) =
        (B * (matrixFirstCross A)ᴴ * (matrixFirstHead A)⁻¹ *
          matrixFirstCross A) * Bᴴ :=
      (Matrix.mul_assoc
        (B * (matrixFirstCross A)ᴴ * (matrixFirstHead A)⁻¹)
        (matrixFirstCross A) Bᴴ).symm
    _ = (B * (((matrixFirstCross A)ᴴ * (matrixFirstHead A)⁻¹) *
          matrixFirstCross A)) * Bᴴ := by
      rw [Matrix.mul_assoc B (matrixFirstCross A)ᴴ (matrixFirstHead A)⁻¹,
        Matrix.mul_assoc B ((matrixFirstCross A)ᴴ * (matrixFirstHead A)⁻¹)
          (matrixFirstCross A)]
    _ = B * ((matrixFirstCross A)ᴴ * (matrixFirstHead A)⁻¹ *
          matrixFirstCross A * Bᴴ) :=
      Matrix.mul_assoc B
        ((matrixFirstCross A)ᴴ * (matrixFirstHead A)⁻¹ * matrixFirstCross A) Bᴴ

variable {K : Type*} [Field K] [NumberField K]

/-- Determinant-one tail actions lift while fixing the first coordinate. -/
def specialLinearFirstTailLift
    (g : Matrix.SpecialLinearGroup (Fin n) (𝓞 K)) :
    Matrix.SpecialLinearGroup (Fin (n + 1)) (𝓞 K) :=
  ⟨matrixFirstTailLift (g : Matrix (Fin n) (Fin n) (𝓞 K)), by
    rw [det_matrixFirstTailLift, Matrix.SpecialLinearGroup.det_coe]⟩

omit [NumberField K] in
@[simp]
theorem numberFieldRealOrderMatrixAt_firstTailLift
    (w : {w : InfinitePlace K // w.IsReal})
    (B : Matrix (Fin n) (Fin n) (𝓞 K)) :
    numberFieldRealOrderMatrixAt w (matrixFirstTailLift B) =
      matrixFirstTailLift (numberFieldRealOrderMatrixAt w B) := by
  exact map_matrixFirstTailLift _ B

omit [NumberField K] in
@[simp]
theorem numberFieldComplexOrderMatrixAt_firstTailLift
    (w : {w : InfinitePlace K // w.IsComplex})
    (B : Matrix (Fin n) (Fin n) (𝓞 K)) :
    numberFieldComplexOrderMatrixAt w (matrixFirstTailLift B) =
      matrixFirstTailLift (numberFieldComplexOrderMatrixAt w B) := by
  exact map_matrixFirstTailLift _ B

/-- Explicit positive-cone congruence, with membership proved from determinant one. -/
noncomputable def numberFieldArchimedeanPositiveConj
    (g : Matrix.SpecialLinearGroup (Fin n) (𝓞 K))
    (A : numberFieldArchimedeanPositiveForms K n) :
    numberFieldArchimedeanPositiveForms K n :=
  ⟨numberFieldArchimedeanConj g A.1, numberFieldArchimedeanConj_mem g A.2⟩

omit [NumberField K] in
/-- Schur descent is equivariant for every integral determinant-one tail congruence. -/
theorem numberFieldArchimedeanSchur_specialLinearFirstTailLift
    (g : Matrix.SpecialLinearGroup (Fin n) (𝓞 K))
    (A : numberFieldArchimedeanPositiveForms K (n + 1)) :
    numberFieldArchimedeanSchur
        (numberFieldArchimedeanPositiveConj (specialLinearFirstTailLift g) A) =
      numberFieldArchimedeanPositiveConj g (numberFieldArchimedeanSchur A) := by
  apply Subtype.ext
  apply Prod.ext
  · funext w
    apply Subtype.ext
    change matrixFirstSchur
        (numberFieldRealOrderMatrixAt w
            (matrixFirstTailLift (g : Matrix (Fin n) (Fin n) (𝓞 K))) *
          (A.1.1 w : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) *
          (numberFieldRealOrderMatrixAt w
            (matrixFirstTailLift (g : Matrix (Fin n) (Fin n) (𝓞 K))))ᴴ) =
      numberFieldRealOrderMatrixAt w (g : Matrix (Fin n) (Fin n) (𝓞 K)) *
        matrixFirstSchur (A.1.1 w : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) *
        (numberFieldRealOrderMatrixAt w
          (g : Matrix (Fin n) (Fin n) (𝓞 K)))ᴴ
    rw [numberFieldRealOrderMatrixAt_firstTailLift]
    exact matrixFirstSchur_lift_congr _ _
  · funext w
    apply Subtype.ext
    change matrixFirstSchur
        (numberFieldComplexOrderMatrixAt w
            (matrixFirstTailLift (g : Matrix (Fin n) (Fin n) (𝓞 K))) *
          (A.1.2 w : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) *
          (numberFieldComplexOrderMatrixAt w
            (matrixFirstTailLift (g : Matrix (Fin n) (Fin n) (𝓞 K))))ᴴ) =
      numberFieldComplexOrderMatrixAt w (g : Matrix (Fin n) (Fin n) (𝓞 K)) *
        matrixFirstSchur (A.1.2 w : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) *
        (numberFieldComplexOrderMatrixAt w
          (g : Matrix (Fin n) (Fin n) (𝓞 K)))ᴴ
    rw [numberFieldComplexOrderMatrixAt_firstTailLift]
    exact matrixFirstSchur_lift_congr _ _

end GaloisForLFunctions.HTGeometry
