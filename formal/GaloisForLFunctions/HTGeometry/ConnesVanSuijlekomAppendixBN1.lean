import Mathlib

/-!
# Connes--van Suijlekom, Appendix B.1: the `N = 1` source family

The finite `N = 1` matrices in Proposition B.1 have the exact
divided-difference form supplied by Proposition 4.2: an even diagonal and a
constant off-diagonal determined by the odd source parameter.  This module
builds that source family and the affine reduction used in Appendix B.1.
-/

open Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The `N = 1` even-diagonal, odd-divided-difference matrix family from
Proposition 4.2, indexed in source order `(-1, 0, 1)`. -/
def connesVanSuijlekomB1Matrix (a₀ a₁ b₁ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![a₁, b₁, b₁;
     b₁, a₀, b₁;
     b₁, b₁, a₁]

/-- The normalized matrix `M(c)` displayed in Appendix B.1, equation (30). -/
def connesVanSuijlekomB1NormalizedMatrix (c : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, -1, -1;
     -1, c, -1;
     -1, -1, 0]

/-- The reversal symmetry on the source coordinates `(-1, 0, 1)`. -/
def connesVanSuijlekomB1Reflection : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, 0, 1;
     0, 1, 0;
     1, 0, 0]

/-- The odd eigenvector of `M(c)`. -/
def connesVanSuijlekomB1OddVector : Fin 3 → ℝ := ![-1, 0, 1]

/-- The even vectors used for the two remaining eigendirections of `M(c)`. -/
def connesVanSuijlekomB1EvenVector (x : ℝ) : Fin 3 → ℝ := ![1, x, 1]

theorem connesVanSuijlekomB1_normalized_odd_eigenvector (c : ℝ) :
    connesVanSuijlekomB1NormalizedMatrix c *ᵥ connesVanSuijlekomB1OddVector =
      1 • connesVanSuijlekomB1OddVector := by
  ext i
  fin_cases i <;> simp [connesVanSuijlekomB1NormalizedMatrix,
    connesVanSuijlekomB1OddVector, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem connesVanSuijlekomB1_normalized_even_eigenvector
    {c x : ℝ} (hx : x ^ 2 + (c + 1) * x - 2 = 0) :
    connesVanSuijlekomB1NormalizedMatrix c *ᵥ connesVanSuijlekomB1EvenVector x =
      (-x - 1) • connesVanSuijlekomB1EvenVector x := by
  ext i
  fin_cases i <;> simp [connesVanSuijlekomB1NormalizedMatrix,
    connesVanSuijlekomB1EvenVector, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  nlinarith

/-- Appendix B.1's reduction of a nonzero off-diagonal source matrix to `M(c)`,
up to a nonzero scalar and a scalar identity shift. -/
theorem connesVanSuijlekomB1_affine_reduction (a₀ a₁ b₁ : ℝ) (hb : b₁ ≠ 0) :
    connesVanSuijlekomB1Matrix a₀ a₁ b₁ =
      (-b₁) • connesVanSuijlekomB1NormalizedMatrix ((a₀ - a₁) / (-b₁)) +
        a₁ • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [connesVanSuijlekomB1Matrix, connesVanSuijlekomB1NormalizedMatrix]
  all_goals (field_simp; ring)

/-- The normalized source family commutes with reflection, as required by the
even/odd eigenspace split in Appendix B.1. -/
theorem connesVanSuijlekomB1_normalized_commutes_reflection (c : ℝ) :
    connesVanSuijlekomB1NormalizedMatrix c * connesVanSuijlekomB1Reflection =
      connesVanSuijlekomB1Reflection * connesVanSuijlekomB1NormalizedMatrix c := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [connesVanSuijlekomB1NormalizedMatrix, connesVanSuijlekomB1Reflection,
      Matrix.mul_apply, Fin.sum_univ_three]

/-- The polynomial numerator in Equation (21), specialized to `N = 1` and
source coordinate order `(-1, 0, 1)`. -/
def connesVanSuijlekomB1FourierNumerator (v : Fin 3 → ℝ) (s : ℂ) : ℂ :=
  (v 0 : ℂ) * (0 - s) * (1 - s) +
    (v 1 : ℂ) * (-1 - s) * (1 - s) +
      (v 2 : ℂ) * (-1 - s) * (0 - s)

theorem connesVanSuijlekomB1FourierNumerator_expand (v : Fin 3 → ℝ) (s : ℂ) :
    connesVanSuijlekomB1FourierNumerator v s =
      ((v 0 + v 1 + v 2 : ℝ) : ℂ) * s ^ 2 + ((v 2 - v 0 : ℝ) : ℂ) * s - v 1 := by
  simp [connesVanSuijlekomB1FourierNumerator]
  ring

end

end GaloisForLFunctions.HTGeometry
