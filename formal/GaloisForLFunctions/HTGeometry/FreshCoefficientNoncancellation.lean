import GaloisForLFunctions.HTGeometry.DeterminantDegreeOne
import GaloisForLFunctions.HTGeometry.RowReplacementRecurrence

/-!
# Fresh coefficient variables prevent cancellation

Distinct polynomial variables act as algebraically independent tags. If every coefficient is
independent of all tags, differentiating with respect to one tag recovers exactly its coefficient.
Hence a tagged finite sum cannot vanish when one coefficient is nonzero. This is the polynomial
noncancellation core of the k-server paper's fresh-coefficient lemma.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped BigOperators
open MvPolynomial

variable {ι σ R : Type*} [Fintype ι] [DecidableEq ι]
  [DecidableEq σ] [CommRing R]

/-- Partial differentiation with respect to a fresh tag extracts its unique coefficient. -/
theorem pderiv_sum_fresh_X_mul (eta : ι → σ) (heta : Function.Injective eta)
    (f : ι → MvPolynomial σ R)
    (hfresh : ∀ i j, degreeOf (eta i) (f j) = 0) (i : ι) :
    pderiv (eta i) (∑ j, X (eta j) * f j) = f i := by
  rw [map_sum]
  have hderiv (j : ι) : pderiv (eta i) (f j) = 0 :=
    pderiv_eq_zero_of_degreeOf_eq_zero (f j) (eta i) (hfresh i j)
  calc
    (∑ j, pderiv (eta i) (X (eta j) * f j)) =
        ∑ j, if i = j then f j else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      rw [pderiv_mul, hderiv, mul_zero, add_zero, pderiv_X]
      by_cases hij : i = j
      · subst j
        simp
      · have hne : eta j ≠ eta i := fun h => hij (heta h.symm)
        simp [hij, hne]
    _ = f i := by simp

/-- **Fresh-tag noncancellation.** One nonzero fresh-tagged coefficient forces the whole finite
sum to be nonzero. -/
theorem sum_fresh_X_mul_ne_zero (eta : ι → σ) (heta : Function.Injective eta)
    (f : ι → MvPolynomial σ R)
    (hfresh : ∀ i j, degreeOf (eta i) (f j) = 0)
    {i : ι} (hi : f i ≠ 0) :
    ∑ j, X (eta j) * f j ≠ 0 := by
  intro hzero
  have hderiv := congrArg (pderiv (eta i)) hzero
  rw [pderiv_sum_fresh_X_mul eta heta f hfresh i, map_zero] at hderiv
  exact hi hderiv

/-- **Fresh row-replacement noncancellation.** If every old entry is independent of all fresh
tags and one coordinate-column replacement has nonzero determinant, then replacing the chosen row
by the fresh tags produces a nonzero determinant. -/
theorem det_updateRow_fresh_ne_zero
    (A : Matrix ι ι (MvPolynomial σ R)) (row : ι)
    (eta : ι → σ) (heta : Function.Injective eta)
    (hA : ∀ k i j, degreeOf (eta k) (A i j) = 0)
    {column : ι}
    (hminor : (A.updateCol column (Pi.single row 1)).det ≠ 0) :
    (A.updateRow row fun j => X (eta j)).det ≠ 0 := by
  rw [det_updateRow_eq_sum_columnReplacementDet]
  apply sum_fresh_X_mul_ne_zero eta heta
  · intro k j
    apply degreeOf_det_eq_zero
    intro i column'
    by_cases hcolumn : column' = j
    · subst column'
      rw [Matrix.updateCol_self]
      by_cases hi : i = row
      · subst i
        rw [Pi.single_eq_same, degreeOf_one]
      · rw [Pi.single_eq_of_ne hi, degreeOf_zero]
    · rw [Matrix.updateCol_ne hcolumn]
      exact hA k i column'
  · exact hminor

end GaloisForLFunctions.HTGeometry
