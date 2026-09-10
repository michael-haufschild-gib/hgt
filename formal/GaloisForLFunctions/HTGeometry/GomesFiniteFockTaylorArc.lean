import GaloisForLFunctions.HTGeometry.GomesFiniteFockSymmetrySpectrum

/-!
# The existing Fock Taylor gauge as an exponential truncated arc

The already formalized finite exponential is transported through the exact
symmetry-algebra equivalence. No additional convergence or analytic hypotheses
are introduced, and the zero-dimensional matrix statement is retained.
-/

noncomputable section
open Matrix Polynomial
open scoped BigOperators
namespace GaloisForLFunctions.HTGeometry.GammaFactorialFock

/-- A finite coefficient list acts by the corresponding polynomial in the actual clock. -/
theorem gomesFiniteFockPolynomialHom_coefficients (N : ℕ) (c : Fin N → ℂ) :
    gomesFiniteFockPolynomialHom N (gomesFiniteFockCoefficientPolynomial N c) =
      ∑ k : Fin N, c k • (fockShiftMatrix N) ^ k.val := by
  rw [gomesFiniteFockCoefficientPolynomial, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [gomesFiniteFockPolynomialHom_eq_aeval, Polynomial.aeval_monomial,
    ← Algebra.smul_def]

/-- Full clock commutation is equivalent to a unique finite polynomial in the clock itself. -/
theorem gomesFiniteFock_commute_iff_unique_clock_polynomial (N : ℕ) (M : Matrix (Fin N) (Fin N) ℂ) :
    Commute M (fockShiftMatrix N) ↔
      ∃! c : Fin N → ℂ, ∑ k : Fin N, c k • (fockShiftMatrix N) ^ k.val = M := by
  simpa only [gomesFiniteFockPolynomialHom_coefficients] using
    gomesFiniteFock_commute_iff_unique_symbol N M

/-- Finite exponential coefficients, viewed as a polynomial symbol. -/
def gomesFiniteFockTaylorSymbol (N : ℕ) (z : ℂ) : ℂ[X] :=
  gomesFiniteFockCoefficientPolynomial N (fun k => z ^ k.val / (Nat.factorial k.val : ℂ))

/-- The literal existing Taylor matrix is the finite exponential polynomial under the clock map. -/
theorem gomesFiniteFockTaylorSymbol_matrix (N : ℕ) (z : ℂ) :
    gomesFiniteFockPolynomialHom N (gomesFiniteFockTaylorSymbol N z) = fockTaylorMatrix N z := by
  rw [gomesFiniteFockTaylorSymbol, gomesFiniteFockPolynomialHom_coefficients,
    fockTaylorMatrix_finite_exp]
  exact Fin.sum_univ_eq_sum_range (fun k =>
    (z ^ k / (Nat.factorial k : ℂ)) • fockShiftMatrix N ^ k) N

/-- The actual Taylor gauge is a point of the already existing truncated arc algebra. -/
def gomesFiniteFockTaylorArc (n : ℕ) (z : ℂ) : TruncatedArcAlgebra ℂ n :=
  Ideal.Quotient.mk (truncatedArcIdeal ℂ n) (gomesFiniteFockTaylorSymbol (n + 1) z)

/-- The geometric-to-symmetry equivalence maps the exponential arc to the literal Taylor gauge. -/
theorem gomesFiniteFockTaylorArc_matrix (n : ℕ) (z : ℂ) :
    (gomesFiniteFockArcEquiv n (gomesFiniteFockTaylorArc n z)).val = fockTaylorMatrix (n + 1) z :=
  gomesFiniteFockTaylorSymbol_matrix (n + 1) z

/-- Every coefficient is exactly the corresponding existing truncated exponential coefficient. -/
theorem gomesFiniteFockTaylorArc_coefficient (n : ℕ) (z : ℂ) (j : Fin (n + 1)) :
    truncatedArcLinearEquiv ℂ n (gomesFiniteFockTaylorArc n z) j =
      z ^ j.val / (Nat.factorial j.val : ℂ) := by
  rw [gomesFiniteFockTaylorArc, truncatedArcLinearEquiv_mk_apply,
    gomesFiniteFockTaylorSymbol, gomesFiniteFockCoefficientPolynomial_coeff]

/-- The geometric exponential arc is based at one for every translation parameter. -/
theorem gomesFiniteFockTaylorArc_augmentation (n : ℕ) (z : ℂ) :
    truncatedArcAugmentation ℂ n (gomesFiniteFockTaylorArc n z) = 1 := by
  rw [← truncatedArcLinearEquiv_apply_zero, gomesFiniteFockTaylorArc_coefficient]
  simp

/-- The group law of actual Taylor matrices is exactly multiplication of existing geometric arcs. -/
theorem gomesFiniteFockTaylorArc_add (n : ℕ) (z w : ℂ) :
    gomesFiniteFockTaylorArc n (z + w) = gomesFiniteFockTaylorArc n z * gomesFiniteFockTaylorArc n w := by
  apply (gomesFiniteFockArcEquiv n).injective
  apply Subtype.ext
  rw [map_mul]
  change (gomesFiniteFockArcEquiv n _).val =
    (gomesFiniteFockArcEquiv n _).val * (gomesFiniteFockArcEquiv n _).val
  rw [gomesFiniteFockTaylorArc_matrix, gomesFiniteFockTaylorArc_matrix,
    gomesFiniteFockTaylorArc_matrix, fockTaylorMatrix_add]

end GaloisForLFunctions.HTGeometry.GammaFactorialFock
