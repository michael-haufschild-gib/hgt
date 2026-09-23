import GaloisForLFunctions.RHTower.Sieve.OffDiagonalBound

/-!
# The mean value theorem for Dirichlet polynomials

`|∫_0^T |F(t)|² dt - T ∑_{n < N} |a_n|²| ≤ 4N(1 + log N) ∑_{n < N} |a_n|²`

for `F(t) = ∑_{n < N} a_n n^{it}`.

The diagonal of the expanded mean square contributes `T ∑_n |a_n|²` exactly, and
`OffDiagonalBound.lean` bounds the rest.  The error `O(N log N)` is what the elementary comparison
between logarithmic and integer separations yields; the sharp `O(N)` of Montgomery and Vaughan needs
a Hilbert inequality at the frequencies `log n`, which the corpus does not own.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

/-- **The mean value theorem, in complex form.** -/
theorem dirichlet_meanValue_complex (N : ℕ) (a : Fin N → ℂ) (T : ℝ) :
    ‖(∫ t in (0 : ℝ)..T, ((‖dirPoly N a t‖ ^ (2 : ℕ) : ℝ) : ℂ))
        - (T : ℂ) * ∑ m : Fin N, ((‖a m‖ ^ (2 : ℕ) : ℝ) : ℂ)‖
      ≤ 4 * (N : ℝ) * (1 + Real.log N) * ∑ m : Fin N, ‖a m‖ ^ (2 : ℕ) :=
  le_trans (norm_integral_normSq_dirPoly_sub_diag_le N a T) (offDiagonal_le N a)

/-- **The mean value theorem for Dirichlet polynomials.** -/
theorem dirichlet_meanValue_theorem (N : ℕ) (a : Fin N → ℂ) (T : ℝ) :
    |(∫ t in (0 : ℝ)..T, ‖dirPoly N a t‖ ^ (2 : ℕ)) - T * ∑ m : Fin N, ‖a m‖ ^ (2 : ℕ)|
      ≤ 4 * (N : ℝ) * (1 + Real.log N) * ∑ m : Fin N, ‖a m‖ ^ (2 : ℕ) := by
  have hbase := dirichlet_meanValue_complex N a T
  have hcast : (∫ t in (0 : ℝ)..T, ((‖dirPoly N a t‖ ^ (2 : ℕ) : ℝ) : ℂ))
      - (T : ℂ) * ∑ m : Fin N, ((‖a m‖ ^ (2 : ℕ) : ℝ) : ℂ)
      = ((((∫ t in (0 : ℝ)..T, ‖dirPoly N a t‖ ^ (2 : ℕ)) - T * ∑ m : Fin N, ‖a m‖ ^ (2 : ℕ) : ℝ)) : ℂ) := by
    rw [intervalIntegral.integral_ofReal, ← Complex.ofReal_sum, ← Complex.ofReal_mul,
      ← Complex.ofReal_sub]
  rw [hcast, Complex.norm_real, Real.norm_eq_abs] at hbase
  exact hbase

end RHTower.Sieve
