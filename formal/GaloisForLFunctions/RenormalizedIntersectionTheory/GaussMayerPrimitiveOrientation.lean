import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerPrimitiveWordCoding

/-!
# Inversion of primitive Gauss classes

The determinant-one quarter turn conjugates an inverse to its transpose.
For actual even Gauss words, transpose reverses the digits. Consequently,
inverse conjugacy is exactly cyclic rotation of the reversed digit pairs.
-/

open Matrix
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerCoding
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerHyperbolic
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerIntegralWords
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerGaussCoding
set_option autoImplicit false
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerOrientation

/-- Reverse the Gauss digits, retaining their grouping into consecutive pairs. -/
def reversedPairs (ps : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  ps.reverse.map (fun p => (p.2,p.1))

/-- The literal adjugate, which is the inverse on determinant-one integral matrices. -/
def integralInverse (A : IntMatrix) : IntMatrix := !![A 1 1,-A 0 1;-A 1 0,A 0 0]

theorem integralInverse_spec (A : IntMatrix) (hA : A.det = 1) :
    (integralInverse A).det = 1 ∧ integralInverse A*A = 1 ∧ A*integralInverse A = 1 := by
  have hd : A 0 0*A 1 1-A 0 1*A 1 0 = 1 := by simpa only [Matrix.det_fin_two] using hA
  refine ⟨?_,?_,?_⟩
  · rw [Matrix.det_fin_two]
    change A 1 1*A 0 0-(-A 0 1)*(-A 1 0) = 1
    nlinarith only [hd]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [integralInverse,Matrix.mul_apply,Fin.sum_univ_two] <;>
      nlinarith only [hd]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [integralInverse,Matrix.mul_apply,Fin.sum_univ_two] <;>
      nlinarith only [hd]

private def quarterTurn : IntMatrix := !![0,-1;1,0]
private def quarterTurnInverse : IntMatrix := !![0,1;-1,0]

private theorem quarterTurn_det : quarterTurn.det = 1 := by
  norm_num [quarterTurn,Matrix.det_fin_two]

private theorem quarterTurnInverse_det : quarterTurnInverse.det = 1 := by
  norm_num [quarterTurnInverse,Matrix.det_fin_two]

private theorem quarterTurn_intertwines (A : IntMatrix) :
    quarterTurn*integralInverse A = A.transpose*quarterTurn := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quarterTurn,integralInverse,Matrix.mul_apply,Fin.sum_univ_two]

private theorem quarterTurnInverse_intertwines (A : IntMatrix) :
    quarterTurnInverse*A.transpose = integralInverse A*quarterTurnInverse := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quarterTurnInverse,integralInverse,Matrix.mul_apply,Fin.sum_univ_two]

/-- Adjugate intertwiners are transpose intertwiners via the determinant-one quarter turn. -/
theorem adjugate_intertwiner_iff_transpose (A B : IntMatrix) :
    (∃ C : IntMatrix, C.det = 1 ∧ C*integralInverse A = B*C) ↔
      ∃ C : IntMatrix, C.det = 1 ∧ C*A.transpose = B*C := by
  constructor
  · rintro ⟨C,hC,he⟩
    refine ⟨C*quarterTurnInverse,?_,?_⟩
    · rw [Matrix.det_mul,hC,quarterTurnInverse_det,mul_one]
    · rw [Matrix.mul_assoc,quarterTurnInverse_intertwines,← Matrix.mul_assoc,he,Matrix.mul_assoc]
  · rintro ⟨C,hC,he⟩
    refine ⟨C*quarterTurn,?_,?_⟩
    · rw [Matrix.det_mul,hC,quarterTurn_det,mul_one]
    · rw [Matrix.mul_assoc,quarterTurn_intertwines,← Matrix.mul_assoc,he,Matrix.mul_assoc]

theorem actualPairedMatrix_append (ps qs : List (ℕ × ℕ)) :
    actualPairedMatrix (ps++qs) = actualPairedMatrix ps*actualPairedMatrix qs := by
  simp only [actualPairedMatrix_eq,pairedRunWord_append,matrixWord_append,intMatrix_mul]

private theorem actualPairedMatrix_singleton_transpose (a b : ℕ) :
    (actualPairedMatrix [(a,b)]).transpose = actualPairedMatrix [(b,a)] := by
  simp only [actualPairedMatrix_eq,pairedRunWord,List.append_nil,matrixWord_append,
    matrixWord_replicate,generator_false_pow,generator_true_pow]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [intMatrix,Matrix.mul_apply,Fin.sum_univ_two]
  ring

/-- Digit reversal gives exactly the transpose of the actual even Gauss matrix. -/
theorem actualPairedMatrix_reversedPairs (ps : List (ℕ × ℕ)) :
    actualPairedMatrix (reversedPairs ps) = (actualPairedMatrix ps).transpose := by
  induction ps with
  | nil => simp [reversedPairs,actualPairedMatrix_eq,pairedRunWord,matrixWord,intMatrix_one]
  | cons p ps ih =>
    rcases p with ⟨a,b⟩
    have hc : (a,b)::ps = [(a,b)]++ps := rfl
    rw [hc]
    simp only [reversedPairs,List.reverse_append,List.reverse_cons,List.reverse_nil,
      List.nil_append,List.map_append,List.map_cons,List.map_nil]
    change actualPairedMatrix (reversedPairs ps++[(b,a)]) =
      (actualPairedMatrix ([(a,b)]++ps)).transpose
    rw [actualPairedMatrix_append,actualPairedMatrix_append,Matrix.transpose_mul,ih,
      actualPairedMatrix_singleton_transpose]

private theorem reversedPairs_ne_nil (ps : List (ℕ × ℕ)) (hps : ps ≠ []) : reversedPairs ps ≠ [] := by
  simpa [reversedPairs] using hps

/-- The explicit adjugate is the actual determinant-one inverse of every even Gauss matrix. -/
theorem actualPairedMatrix_inverse_spec (ps : List (ℕ × ℕ)) :
    (integralInverse (actualPairedMatrix ps)).det = 1 ∧
      integralInverse (actualPairedMatrix ps)*actualPairedMatrix ps = 1 ∧
      actualPairedMatrix ps*integralInverse (actualPairedMatrix ps) = 1 := by
  apply integralInverse_spec
  rw [actualPairedMatrix_eq]
  exact (unimodular_iff_det _).mp (matrixWord_unimodular _)

/-- Matrix inversion acts on actual even Gauss classes by digit reversal, with no unoriented quotient imposed. -/
theorem actualPairedMatrix_inverse_conjugacy_iff (ps qs : List (ℕ × ℕ))
    (hps : ps ≠ []) (hqs : qs ≠ []) :
    (∃ C : IntMatrix, C.det = 1 ∧ C*integralInverse (actualPairedMatrix ps) = actualPairedMatrix qs*C) ↔
      ∃ a b : List (ℕ × ℕ), reversedPairs ps = a++b ∧ qs = b++a := by
  rw [adjugate_intertwiner_iff_transpose,← actualPairedMatrix_reversedPairs]
  exact actualPairedMatrix_conjugacy_iff (reversedPairs ps) qs (reversedPairs_ne_nil ps hps) hqs

#print axioms integralInverse_spec
#print axioms adjugate_intertwiner_iff_transpose
#print axioms actualPairedMatrix_reversedPairs
#print axioms actualPairedMatrix_inverse_spec
#print axioms actualPairedMatrix_inverse_conjugacy_iff

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerOrientation
