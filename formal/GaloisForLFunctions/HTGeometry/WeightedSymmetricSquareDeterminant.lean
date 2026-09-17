import GaloisForLFunctions.HTGeometry.SymmetricSquareDeterminantFull
import Mathlib.RingTheory.Valuation.Basic

/-!
# Weighted symmetric-square determinants

Column weights multiply the symmetric-square determinant by their total product. Under a
valuation, this becomes the exact additive/multiplicative bookkeeping used by the k-server
paper's terminal potential bound. The unordered-pair sum theorem identifies diagonal-zero pair
weights with the usual strict clique sum.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped BigOperators

section CliqueWeight

variable {α ι : Type*} [LinearOrder ι] [AddCommMonoid α]

/-- Symmetric pair weight on unordered pairs. -/
def symmetricPairWeight (d : ι → ι → α) (hsymm : ∀ i j, d i j = d j i) : Sym2 ι → α :=
  Sym2.lift ⟨d, hsymm⟩

omit [LinearOrder ι] [AddCommMonoid α] in
@[simp] theorem symmetricPairWeight_mk
    (d : ι → ι → α) (hsymm : ∀ i j, d i j = d j i) (i j : ι) :
    symmetricPairWeight d hsymm s(i, j) = d i j := rfl

/-- Diagonal-zero unordered-pair weights sum to the strict clique sum. -/
theorem sum_sym2_symmetricPairWeight_eq_offDiag
    (s : Finset ι) (d : ι → ι → α) (hsymm : ∀ i j, d i j = d j i)
    (hdiag : ∀ i, d i i = 0) :
    ∑ p ∈ s.sym2, symmetricPairWeight d hsymm p =
      ∑ ij ∈ s.offDiag with ij.1 < ij.2, d ij.1 ij.2 := by
  calc
    ∑ p ∈ s.sym2, symmetricPairWeight d hsymm p =
        ∑ p ∈ s.sym2 with ¬p.IsDiag, symmetricPairWeight d hsymm p := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro p hp hnot
      simp only [Finset.mem_filter, hp, true_and, not_not] at hnot
      induction p with
      | _ i j =>
          have hij : i = j := Sym2.mk_isDiag_iff.mp hnot
          subst j
          exact symmetricPairWeight_mk d hsymm i i |>.trans (hdiag i)
    _ = _ := by
      simpa using Finset.sum_sym2_filter_not_isDiag s (symmetricPairWeight d hsymm)

end CliqueWeight

noncomputable section

variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]

/-- Determinant of a symmetric-square matrix after independently weighting its columns. -/
theorem det_weightedSymmetricSquare
    (A : Matrix ι ι K) (hA : A.det ≠ 0) (w : Sym2 ι → K) :
    (symmetricSquareMatrixGeneral A * Matrix.diagonal w).det =
      A.det ^ (Fintype.card ι + 1) * ∏ p, w p := by
  rw [Matrix.det_mul, det_symmetricSquareMatrixGeneral A hA, Matrix.det_diagonal]

/-- Valuation of the unweighted symmetric-square determinant. -/
theorem valuation_det_symmetricSquareMatrixGeneral
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (val : Valuation K Γ) (A : Matrix ι ι K) (hA : A.det ≠ 0) :
    val (symmetricSquareMatrixGeneral A).det =
      val A.det ^ (Fintype.card ι + 1) := by
  rw [det_symmetricSquareMatrixGeneral A hA, map_pow]

/-- Valuation of a column-weighted symmetric-square determinant. -/
theorem valuation_det_weightedSymmetricSquare
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (val : Valuation K Γ) (A : Matrix ι ι K) (hA : A.det ≠ 0)
    (w : Sym2 ι → K) :
    val (symmetricSquareMatrixGeneral A * Matrix.diagonal w).det =
      val A.det ^ (Fintype.card ι + 1) * ∏ p, val (w p) := by
  rw [det_weightedSymmetricSquare A hA, Valuation.map_mul, map_pow, map_prod]

end

end GaloisForLFunctions.HTGeometry
