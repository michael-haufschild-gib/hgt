import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# A negative rank-one Gram with independent vectors

The trace pairing on upper triangular traceless matrices has a nilpotent
radical. Its affine family with diagonal `(1,-1)` has constant negative
Gram, while two members are independent exactly when their upper entries
differ. The precise survivor of the rank-one obstruction in Du, Lemma 7.14,
is the classification of the radical as the strictly upper triangular line.
-/

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Matrix

def upperTrace (a b : ℚ) : Matrix (Fin 2) (Fin 2) ℚ := !![a, b; 0, -a]

def splitTracePairing (A B : Matrix (Fin 2) (Fin 2) ℚ) : ℚ :=
  -(Matrix.trace (A * B)) / 2

/-- On the triangular plane the pairing sees only the diagonal coordinate. -/
theorem upperTrace_pairing (a b c d : ℚ) :
    splitTracePairing (upperTrace a b) (upperTrace c d) = -(a * c) := by
  simp [splitTracePairing, upperTrace, Matrix.trace, Fin.sum_univ_two]

/-- The exact radical is the strictly upper triangular, nilpotent line. -/
theorem upperTrace_radical_iff (a b : ℚ) :
    (∀ c d : ℚ, splitTracePairing (upperTrace a b) (upperTrace c d) = 0) ↔ a = 0 := by
  simp only [upperTrace_pairing]
  constructor
  · intro h
    simpa only [mul_one, neg_eq_zero] using h 1 0
  · rintro rfl
    intro c d
    rw [zero_mul, neg_zero]

/-- Isotropic vectors in this plane are precisely its radical. -/
theorem upperTrace_isotropic_iff (a b : ℚ) :
    splitTracePairing (upperTrace a b) (upperTrace a b) = 0 ↔ a = 0 := by
  rw [upperTrace_pairing, neg_eq_zero, mul_self_eq_zero]

/-- Distinct members of the same negative-norm affine fibre remain independent. -/
theorem upperTrace_fibre_independent_iff (b c : ℚ) :
    LinearIndependent ℚ ![upperTrace 1 b, upperTrace 1 c] ↔ b ≠ c := by
  rw [LinearIndependent.pair_iff]
  constructor
  · intro h hbc
    subst c
    have hz : (1 : ℚ) • upperTrace 1 b + (-1 : ℚ) • upperTrace 1 b = 0 := by
      rw [one_smul, neg_one_smul, add_neg_cancel]
    exact one_ne_zero (h 1 (-1) hz).1
  · intro hbc r s hrs
    have hdiag : r + s = 0 := by
      simpa [upperTrace] using congrArg (fun A : Matrix (Fin 2) (Fin 2) ℚ => A 0 0) hrs
    have hoff : r * b + s * c = 0 := by
      simpa [upperTrace] using congrArg (fun A : Matrix (Fin 2) (Fin 2) ℚ => A 0 1) hrs
    have hs : s * (c - b) = 0 := by
      calc
        s * (c - b) = r * b + s * c - b * (r + s) := by ring
        _ = 0 := by rw [hoff, hdiag, mul_zero, sub_zero]
    have hs0 : s = 0 := (mul_eq_zero.mp hs).resolve_right (sub_ne_zero.mpr hbc.symm)
    exact ⟨by simpa only [hs0, add_zero] using hdiag, hs0⟩

/-- Every fibre Gram has the same entries, independently of vector independence. -/
theorem upperTrace_fibre_gram (b : Fin 2 → ℚ) :
    (fun i j => splitTracePairing (upperTrace 1 (b i)) (upperTrace 1 (b j))) =
      (fun _ _ : Fin 2 => (-1 : ℚ)) := by
  funext i j
  rw [upperTrace_pairing, one_mul]

/-- The Gram rank stays one even when the two matrices are independent. -/
theorem upperTrace_fibre_gram_rank (b : Fin 2 → ℚ) :
    Matrix.rank (fun i j : Fin 2 =>
      splitTracePairing (upperTrace 1 (b i)) (upperTrace 1 (b j))) = 1 := by
  rw [upperTrace_fibre_gram, Matrix.rank_eq_finrank_span_cols]
  change Module.finrank ℚ (Submodule.span ℚ
    (Set.range (fun _ : Fin 2 => fun _ : Fin 2 => (-1 : ℚ)))) = 1
  rw [Set.range_const]
  apply finrank_span_singleton
  intro hz
  exact (neg_ne_zero.mpr one_ne_zero) (congrFun hz 0)

/-- Every element of the invisible line is square-zero in the ambient matrix algebra. -/
theorem upperTrace_radical_square_zero (b : ℚ) : upperTrace 0 b * upperTrace 0 b = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upperTrace, Matrix.mul_apply, Fin.sum_univ_two]

#print axioms upperTrace_pairing
#print axioms upperTrace_radical_iff
#print axioms upperTrace_isotropic_iff
#print axioms upperTrace_fibre_independent_iff
#print axioms upperTrace_fibre_gram
#print axioms upperTrace_fibre_gram_rank
#print axioms upperTrace_radical_square_zero

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
