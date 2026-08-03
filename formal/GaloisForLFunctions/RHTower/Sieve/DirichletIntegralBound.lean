import GaloisForLFunctions.RHTower.Sieve.DirichletDerivEnergy

/-!
# The two integrals of Gallagher's reduction

The mean value theorem bounds the mean square of a Dirichlet polynomial,

`∫_0^T |F|² ≤ (T + 4N(1 + log N)) ∑_n |a_n|²`,

and applying it to `F'` — itself a Dirichlet polynomial, with coefficients of energy at most
`(log N)²` times that of `F` — bounds the second integral of `DirichletGallagher.lean` as well.

Both integrals in Gallagher's reduction for Dirichlet polynomials are therefore controlled by `T`,
`N` and the coefficient energy alone.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

/-- **The mean square of a Dirichlet polynomial.** -/
theorem integral_normSq_dirPoly_le (N : ℕ) (a : Fin N → ℂ) (T : ℝ) :
    (∫ t in (0 : ℝ)..T, ‖dirPoly N a t‖ ^ 2)
      ≤ (T + 4 * (N : ℝ) * (1 + Real.log N)) * ∑ m : Fin N, ‖a m‖ ^ 2 := by
  have hmvt := dirichlet_meanValue_theorem N a T
  have hle := (abs_le.mp hmvt).2
  nlinarith [hle]

/-- The window factor is nonnegative. -/
theorem window_factor_nonneg (N : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    (0 : ℝ) ≤ T + 4 * (N : ℝ) * (1 + Real.log N) := by
  have hlogN : 0 ≤ Real.log (N : ℝ) := by
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp
    · exact Real.log_nonneg (by exact_mod_cast hN)
  have hNR : (0 : ℝ) ≤ (N : ℝ) := by positivity
  nlinarith [hlogN, hNR, hT]

/-- **The mean square of the derivative.** -/
theorem integral_normSq_dirPoly_deriv_le (N : ℕ) (a : Fin N → ℂ) {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, ‖dirPoly N (dirDerivCoeff N a) t‖ ^ 2)
      ≤ (T + 4 * (N : ℝ) * (1 + Real.log N))
          * ((Real.log N) ^ 2 * ∑ m : Fin N, ‖a m‖ ^ 2) := by
  have hbase := integral_normSq_dirPoly_le N (dirDerivCoeff N a) T
  have henergy := sum_normSq_dirDerivCoeff_le N a
  have hfac := window_factor_nonneg N hT
  have hstep := mul_le_mul_of_nonneg_left henergy hfac
  linarith [hbase, hstep]

end RHTower.Sieve
