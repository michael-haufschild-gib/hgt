import GaloisForLFunctions.HilbertMetric.QuantumInformation.CauchyDephasing
import GaloisForLFunctions.HTGeometry.CauchyMatrixDeterminant
import Mathlib.Analysis.Matrix.Order

/-!
# The strict positivity boundary of the Cauchy dephasing symbol

Diagonal congruence reduces the normalized symbol to a Cauchy matrix.
The determinant formula detects exactly collisions of logarithmic rates;
positive semidefiniteness then turns nonsingularity into strict positivity.
-/

noncomputable section
open Matrix
open scoped ComplexOrder BigOperators
namespace GaloisForLFunctions.HilbertMetric.CauchyDephasing
open CauchyJordan

/-- The normalized symbol is a diagonal congruence of the Cauchy matrix. -/
theorem symbol_diagonal_factorization {n : ℕ} (r : Fin n → ℝ) :
    symbol r = (2 : ℂ) • (rateDiagonal r * cauchySymbol r * rateDiagonal r) := by
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [rateDiagonal, Matrix.mul_diagonal, Matrix.diagonal_mul]
  change ((2 * Real.exp (r i / 2) * Real.exp (r j / 2) /
      (Real.exp (r i) + Real.exp (r j)) : ℝ) : ℂ) =
    2 * ((Real.exp (r i / 2) : ℂ) *
      ((1 / (Real.exp (r i) + Real.exp (r j)) : ℝ) : ℂ) * (Real.exp (r j / 2) : ℂ))
  simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_add,
    Complex.ofReal_ofNat, Complex.ofReal_one]
  ring

private theorem cauchySymbol_det_ne_of_injective {n : ℕ} (r : Fin n → ℝ)
    (hinj : Function.Injective r) : (cauchySymbol r).det ≠ 0 := by
  have he : cauchySymbol r = HTGeometry.cauchyMatrix
      (fun i => (rate r i : ℂ)) (fun i => (rate r i : ℂ)) := by
    ext i j
    change ((1 / (rate r i + rate r j) : ℝ) : ℂ) =
      ((rate r i : ℂ) + (rate r j : ℂ))⁻¹
    simp only [Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_one, one_div]
  have hsum (i j : Fin n) : (rate r i : ℂ) + (rate r j : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_add]
    exact Complex.ofReal_ne_zero.mpr (add_pos (rate_pos r i) (rate_pos r j)).ne'
  have hd := HTGeometry.det_cauchyMatrix
    (fun i => (rate r i : ℂ)) (fun i => (rate r i : ℂ)) hsum
  have hp : (∏ i : Fin n, ∏ j ∈ Finset.Ioi i,
      (((rate r i : ℂ) - (rate r j : ℂ)) * ((rate r i : ℂ) - (rate r j : ℂ)))) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    have hij : i ≠ j := (ne_of_lt (Finset.mem_Ioi.mp hj))
    have hr : (rate r i : ℂ) - (rate r j : ℂ) ≠ 0 := by
      intro h
      have heq : rate r i = rate r j := Complex.ofReal_injective (sub_eq_zero.mp h)
      exact hij (hinj (Real.exp_injective heq))
    exact mul_ne_zero hr hr
  rw [he]
  intro hz
  rw [hz, zero_mul] at hd
  exact hp hd.symm

/-- Distinct rates make the normalized symbol nonsingular. -/
private theorem symbol_det_ne_of_injective {n : ℕ} (r : Fin n → ℝ)
    (hinj : Function.Injective r) : (symbol r).det ≠ 0 := by
  have hD : (rateDiagonal r).det ≠ 0 := by
    rw [rateDiagonal, Matrix.det_diagonal]
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
  rw [symbol_diagonal_factorization, Matrix.det_smul, Matrix.det_mul, Matrix.det_mul]
  exact mul_ne_zero (pow_ne_zero _ (by norm_num))
    (mul_ne_zero (mul_ne_zero hD (cauchySymbol_det_ne_of_injective r hinj)) hD)

/-- Collision of logarithmic rates is exactly singularity of the normalized channel symbol. -/
theorem symbol_det_ne_zero_iff {n : ℕ} (r : Fin n → ℝ) :
    (symbol r).det ≠ 0 ↔ Function.Injective r := by
  constructor
  · intro hd i j hrij
    by_contra hij
    have hrow : symbol r i = symbol r j := by
      funext k
      simp only [symbol, hrij]
    exact hd (Matrix.det_zero_of_row_eq hij hrow)
  · exact symbol_det_ne_of_injective r

/-- The Cauchy channel symbol is positive definite exactly at distinct logarithmic rates. -/
theorem symbol_posDef_iff {n : ℕ} (r : Fin n → ℝ) :
    (symbol r).PosDef ↔ Function.Injective r := by
  rw [(symbol_posSemidef r).posDef_iff_det_ne_zero, symbol_det_ne_zero_iff]

#print axioms symbol_diagonal_factorization
#print axioms symbol_det_ne_zero_iff
#print axioms symbol_posDef_iff
end GaloisForLFunctions.HilbertMetric.CauchyDephasing
