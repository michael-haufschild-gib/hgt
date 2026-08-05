import GaloisForLFunctions.HTGeometry.GammaPoleSymbolicTriGrading

/-!
# Weighted-homogeneous jet polynomials exist in every degree

The source-derivative grading gives the `j`-th jet variable weight `j`.  The graded pieces are all
occupied: the zero polynomial and the constants sit in degree zero, each jet variable sits in its
own degree, and products add degrees, so a power of the first-order variable realizes every degree.
-/

open MvPolynomial

namespace GaloisForLFunctions.HTGeometry

/-- Constants are weighted homogeneous of degree zero for the jet grading. -/
theorem isWeightedHomogeneous_C_gammaPoleSourceDerivativeWeight {n : ℕ} (c : ℂ) :
    IsWeightedHomogeneous (gammaPoleSourceDerivativeWeight (n := n))
      (C c : MvPolynomial (Fin (n + 1)) ℂ) 0 :=
  isWeightedHomogeneous_C _ c

/-- **The `j`-th jet variable is weighted homogeneous of degree `j`.** -/
theorem isWeightedHomogeneous_X_gammaPoleSourceDerivativeWeight {n : ℕ} (j : Fin (n + 1)) :
    IsWeightedHomogeneous (gammaPoleSourceDerivativeWeight (n := n))
      (X j : MvPolynomial (Fin (n + 1)) ℂ) (j : ℕ) := by
  simpa [gammaPoleSourceDerivativeWeight] using
    isWeightedHomogeneous_X (R := ℂ) (gammaPoleSourceDerivativeWeight (n := n)) j

/-- **Every degree is occupied**: a power of the first-order jet variable has exactly that
weighted degree. -/
theorem isWeightedHomogeneous_X_one_pow {n : ℕ} (hn : 0 < n) (d : ℕ) :
    IsWeightedHomogeneous (gammaPoleSourceDerivativeWeight (n := n))
      ((X ⟨1, by omega⟩ : MvPolynomial (Fin (n + 1)) ℂ) ^ d) d := by
  have hX := isWeightedHomogeneous_X_gammaPoleSourceDerivativeWeight (n := n) ⟨1, by omega⟩
  have hpow := hX.pow d
  simpa [gammaPoleSourceDerivativeWeight] using hpow

/-- The zero polynomial is weighted homogeneous of every degree. -/
theorem isWeightedHomogeneous_zero_gammaPoleSourceDerivativeWeight {n : ℕ} (d : ℕ) :
    IsWeightedHomogeneous (gammaPoleSourceDerivativeWeight (n := n))
      (0 : MvPolynomial (Fin (n + 1)) ℂ) d :=
  isWeightedHomogeneous_zero _ _ _

end GaloisForLFunctions.HTGeometry
