import GaloisForLFunctions.HTGeometry.GomesFiniteFockTruncatedArcEquiv
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Spectrum, determinant and invertibility of every finite Fock symmetry

The geometric augmentation is the sole diagonal value of a clock symmetry.
Its determinant and characteristic polynomial are exact powers, so invertibility
is detected by one scalar. The symmetry algebra has exactly the jet dimension.
-/

noncomputable section
open Matrix Polynomial
namespace GaloisForLFunctions.HTGeometry.GammaFactorialFock

/-- Every symbol matrix is upper triangular. -/
theorem gomesFiniteFockPolynomialHom_upperTriangular (N : ℕ) (p : ℂ[X]) :
    (gomesFiniteFockPolynomialHom N p).BlockTriangular id := by
  intro i j hji
  rw [gomesFiniteFockPolynomialHom_apply, if_neg]
  exact Nat.not_le_of_lt hji

/-- All diagonal values equal the symbol's constant coefficient. -/
theorem gomesFiniteFockPolynomialHom_diagonal (N : ℕ) (p : ℂ[X]) (i : Fin N) :
    gomesFiniteFockPolynomialHom N p i i = p.coeff 0 := by
  simp [gomesFiniteFockPolynomialHom_apply]

/-- Existing Toeplitz determinant geometry gives the determinant of every actual clock symmetry. -/
theorem gomesFiniteFockPolynomialHom_det (N : ℕ) (p : ℂ[X]) :
    (gomesFiniteFockPolynomialHom N p).det = p.coeff 0 ^ N := by
  change (toeplitz N p).transpose.det = _
  rw [Matrix.det_transpose, det_toeplitz]

/-- The characteristic polynomial of every symmetry has one scalar root, with full multiplicity. -/
theorem gomesFiniteFockPolynomialHom_charpoly (N : ℕ) (p : ℂ[X]) :
    (gomesFiniteFockPolynomialHom N p).charpoly = (X - C (p.coeff 0)) ^ N := by
  rw [Matrix.charpoly_of_upperTriangular _ (gomesFiniteFockPolynomialHom_upperTriangular N p)]
  simp only [gomesFiniteFockPolynomialHom_diagonal]
  simp

/-- For positive jet dimension, invertibility is exactly nonvanishing of the constant coefficient. -/
theorem gomesFiniteFockPolynomialHom_isUnit_iff (n : ℕ) (p : ℂ[X]) :
    IsUnit (gomesFiniteFockPolynomialHom (n + 1) p) ↔ p.coeff 0 ≠ 0 := by
  rw [Matrix.isUnit_iff_isUnit_det, gomesFiniteFockPolynomialHom_det]
  simp

/-- The invertibility classification also includes the trivial zero-dimensional matrix algebra. -/
theorem gomesFiniteFockPolynomialHom_isUnit_iff_all (N : ℕ) (p : ℂ[X]) :
    IsUnit (gomesFiniteFockPolynomialHom N p) ↔ N = 0 ∨ p.coeff 0 ≠ 0 := by
  cases N with
  | zero => rw [Matrix.isUnit_iff_isUnit_det, gomesFiniteFockPolynomialHom_det]; simp
  | succ n => simpa using gomesFiniteFockPolynomialHom_isUnit_iff n p

/-- The actual geometric augmentation determines the determinant under the algebra equivalence. -/
theorem gomesFiniteFockArcEquiv_det (n : ℕ) (a : TruncatedArcAlgebra ℂ n) :
    (gomesFiniteFockArcEquiv n a).val.det = truncatedArcAugmentation ℂ n a ^ (n + 1) := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [truncatedArcAugmentation_mk, ← Polynomial.coeff_zero_eq_eval_zero]
  exact gomesFiniteFockPolynomialHom_det (n + 1) p

/-- Every actual automorphism corresponds to an arc with nonzero geometric augmentation. -/
theorem gomesFiniteFockArcEquiv_isUnit_iff (n : ℕ) (a : TruncatedArcAlgebra ℂ n) :
    IsUnit (gomesFiniteFockArcEquiv n a).val ↔ truncatedArcAugmentation ℂ n a ≠ 0 := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [truncatedArcAugmentation_mk, ← Polynomial.coeff_zero_eq_eval_zero]
  exact gomesFiniteFockPolynomialHom_isUnit_iff n p

/-- The complete matrix symmetry algebra has exactly as many independent coefficients as the finite jet. -/
theorem gomesFiniteFockCommutant_finrank (n : ℕ) :
    Module.finrank ℂ (gomesFiniteFockCommutant (n + 1)) = n + 1 := by
  let e := (gomesFiniteFockArcEquiv n).symm.toLinearEquiv.trans (truncatedArcLinearEquiv ℂ n)
  rw [e.finrank_eq, Module.finrank_fin_fun]

end GaloisForLFunctions.HTGeometry.GammaFactorialFock
