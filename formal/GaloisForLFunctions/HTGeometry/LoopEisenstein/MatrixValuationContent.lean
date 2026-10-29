import GaloisForLFunctions.HTGeometry.LoopEisenstein.LaurentRotation

/-!
# Valuation content of a two-by-two matrix

The maximum valuation of the four entries is submultiplicative. Multiplying
by an integral matrix with integral inverse preserves it exactly. Applied
to the two lattices in an Iwahori flag, this supplies double-coset invariants.
-/

namespace GaloisForLFunctions.HTGeometry.LoopEisenstein

noncomputable section

variable {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]

/-- Maximum of the entry valuations, or equivalently the inverse minimum order. -/
def matrixValuationContent (v : Valuation K Γ) (M : Matrix (Fin 2) (Fin 2) K) : Γ :=
  max (max (v (M 0 0)) (v (M 0 1))) (max (v (M 1 0)) (v (M 1 1)))

theorem matrixValuationContent_entry_le (v : Valuation K Γ)
    (M : Matrix (Fin 2) (Fin 2) K) (i j : Fin 2) :
    v (M i j) ≤ matrixValuationContent v M := by
  fin_cases i <;> fin_cases j
  · exact (le_max_left _ _).trans (le_max_left _ _)
  · exact (le_max_right _ _).trans (le_max_left _ _)
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (le_max_right _ _).trans (le_max_right _ _)

theorem matrixValuationContent_le_iff (v : Valuation K Γ)
    (M : Matrix (Fin 2) (Fin 2) K) (r : Γ) :
    matrixValuationContent v M ≤ r ↔ ∀ i j, v (M i j) ≤ r := by
  constructor
  · intro h i j
    exact (matrixValuationContent_entry_le v M i j).trans h
  · intro h
    exact max_le (max_le (h 0 0) (h 0 1)) (max_le (h 1 0) (h 1 1))

/-- The ultrametric inequality removes any dimension factor from matrix multiplication. -/
theorem matrixValuationContent_mul_le (v : Valuation K Γ)
    (M N : Matrix (Fin 2) (Fin 2) K) :
    matrixValuationContent v (M * N) ≤ matrixValuationContent v M * matrixValuationContent v N := by
  apply (matrixValuationContent_le_iff v _ _).2
  intro i j
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  refine (v.map_add _ _).trans (max_le ?_ ?_)
  · rw [map_mul]
    exact mul_le_mul' (matrixValuationContent_entry_le v M i 0)
      (matrixValuationContent_entry_le v N 0 j)
  · rw [map_mul]
    exact mul_le_mul' (matrixValuationContent_entry_le v M i 1)
      (matrixValuationContent_entry_le v N 1 j)

theorem matrixValuationContent_mul_left_le (v : Valuation K Γ)
    (A M : Matrix (Fin 2) (Fin 2) K) (hA : matrixValuationContent v A ≤ 1) :
    matrixValuationContent v (A * M) ≤ matrixValuationContent v M :=
  (matrixValuationContent_mul_le v A M).trans
    (by simpa only [one_mul] using mul_le_mul' hA (le_refl (matrixValuationContent v M)))

theorem matrixValuationContent_mul_right_le (v : Valuation K Γ)
    (M A : Matrix (Fin 2) (Fin 2) K) (hA : matrixValuationContent v A ≤ 1) :
    matrixValuationContent v (M * A) ≤ matrixValuationContent v M :=
  (matrixValuationContent_mul_le v M A).trans
    (by simpa only [mul_one] using mul_le_mul' (le_refl (matrixValuationContent v M)) hA)

/-- An integral left inverse makes the integral multiplication bound an equality. -/
theorem matrixValuationContent_mul_left_eq (v : Valuation K Γ)
    (A B M : Matrix (Fin 2) (Fin 2) K)
    (hA : matrixValuationContent v A ≤ 1) (hB : matrixValuationContent v B ≤ 1)
    (hBA : B * A = 1) : matrixValuationContent v (A * M) = matrixValuationContent v M := by
  apply le_antisymm (matrixValuationContent_mul_left_le v A M hA)
  calc
    matrixValuationContent v M = matrixValuationContent v (B * (A * M)) := by
      rw [← mul_assoc, hBA, one_mul]
    _ ≤ matrixValuationContent v (A * M) := matrixValuationContent_mul_left_le v B _ hB

/-- An integral right inverse makes the integral multiplication bound an equality. -/
theorem matrixValuationContent_mul_right_eq (v : Valuation K Γ)
    (M A B : Matrix (Fin 2) (Fin 2) K)
    (hA : matrixValuationContent v A ≤ 1) (hB : matrixValuationContent v B ≤ 1)
    (hAB : A * B = 1) : matrixValuationContent v (M * A) = matrixValuationContent v M := by
  apply le_antisymm (matrixValuationContent_mul_right_le v M A hA)
  calc
    matrixValuationContent v M = matrixValuationContent v ((M * A) * B) := by
      rw [mul_assoc, hAB, mul_one]
    _ ≤ matrixValuationContent v (M * A) := matrixValuationContent_mul_right_le v _ B hB

@[simp] theorem matrixValuationContent_diagonal (v : Valuation K Γ) (a d : K) :
    matrixValuationContent v !![a, 0; 0, d] = max (v a) (v d) := by
  simp [matrixValuationContent]

@[simp] theorem matrixValuationContent_antidiagonal (v : Valuation K Γ) (b c : K) :
    matrixValuationContent v !![0, b; c, 0] = max (v b) (v c) := by
  simp [matrixValuationContent]

end

end GaloisForLFunctions.HTGeometry.LoopEisenstein
