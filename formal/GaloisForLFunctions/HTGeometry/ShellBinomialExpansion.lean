import GaloisForLFunctions.HTGeometry.DiscExpansionExponential

/-!
# The mass-shell binomial power as a truncated expansion

The shell factor `(1 + x²w²)^α`, where `w` is the reciprocal spectral parameter, is a truncated
expansion in `w` of order twice the binomial order, with coefficients the binomial coefficients times
the corresponding power of the frequency.  The disc condition is exactly that the frequency times the
radius stays below the binomial radius.
-/

open Polynomial

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

noncomputable section

section ShellBinomial

/-- The truncated shell polynomial. -/
def shellBinomPoly (α : ℝ) (m : ℕ) (x : ℝ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range m,
    Polynomial.C (((cbinomCoeff α k : ℝ) : ℂ) * ((x : ℂ)) ^ (2 * k)) * Polynomial.X ^ (2 * k)

theorem eval_shellBinomPoly (α : ℝ) (m : ℕ) (x : ℝ) (w : ℂ) :
    (shellBinomPoly α m x).eval w
      = ∑ k ∈ Finset.range m, ((cbinomCoeff α k : ℝ) : ℂ) * ((x : ℂ) ^ 2 * w ^ 2) ^ k := by
  rw [shellBinomPoly, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
    mul_pow, ← pow_mul, ← pow_mul]
  ring

theorem norm_shell_arg {x r : ℝ} (hxr : x ^ 2 * r ^ 2 ≤ 1 / 2) {w : ℂ} (hw : ‖w‖ ≤ r) :
    ‖(x : ℂ) ^ 2 * w ^ 2‖ ≤ 1 / 2 := by
  have hr0 : 0 ≤ r := le_trans (norm_nonneg w) hw
  rw [norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hle : ‖w‖ ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (norm_nonneg w) hw 2
  nlinarith [sq_nonneg x, norm_nonneg w]

/-- **The shell binomial power as a truncated expansion**, at every nonpositive exponent. -/
theorem hasPolyExpansion_shellBinom {α : ℝ} (hα : α ≤ 0) (m : ℕ) (x : ℝ) {r : ℝ}
    (hxr : x ^ 2 * r ^ 2 ≤ 1 / 2) :
    HasPolyExpansion r (2 * m) (cbinomAbsCoeff α m * |x| ^ (2 * m))
      (fun w => (1 + ((x : ℂ)) ^ 2 * w ^ 2) ^ (α : ℂ)) (shellBinomPoly α m x) := by
  intro w hw
  have hu := norm_shell_arg hxr hw
  have hrem : (1 + ((x : ℂ)) ^ 2 * w ^ 2) ^ (α : ℂ) - (shellBinomPoly α m x).eval w
      = cbinomRem α m ((x : ℂ) ^ 2 * w ^ 2) := by
    rw [eval_shellBinomPoly, cbinomRem]
  rw [hrem]
  refine le_trans (norm_cbinomRem_le hα m hu) (le_of_eq ?_)
  have hnorm : ‖(x : ℂ) ^ 2 * w ^ 2‖ = x ^ 2 * ‖w‖ ^ 2 := by
    rw [norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have habs2 : |x| ^ (2 * m) = (x ^ 2) ^ m := by rw [pow_mul, sq_abs]
  have hw2 : ‖w‖ ^ (2 * m) = (‖w‖ ^ 2) ^ m := by rw [pow_mul]
  rw [hnorm, habs2, hw2, mul_pow]
  ring

/-- The same at every positive order, for exponents at most one -- in particular the square root. -/
theorem hasPolyExpansion_shellBinom_succ {α : ℝ} (hα : α ≤ 1) (m : ℕ) (x : ℝ) {r : ℝ}
    (hxr : x ^ 2 * r ^ 2 ≤ 1 / 2) :
    HasPolyExpansion r (2 * (m + 1)) (cbinomAbsCoeff α (m + 1) * |x| ^ (2 * (m + 1)))
      (fun w => (1 + ((x : ℂ)) ^ 2 * w ^ 2) ^ (α : ℂ)) (shellBinomPoly α (m + 1) x) := by
  intro w hw
  have hu := norm_shell_arg hxr hw
  have hrem : (1 + ((x : ℂ)) ^ 2 * w ^ 2) ^ (α : ℂ) - (shellBinomPoly α (m + 1) x).eval w
      = cbinomRem α (m + 1) ((x : ℂ) ^ 2 * w ^ 2) := by
    rw [eval_shellBinomPoly, cbinomRem]
  rw [hrem]
  refine le_trans (norm_cbinomRem_succ_le hα m hu) (le_of_eq ?_)
  have hnorm : ‖(x : ℂ) ^ 2 * w ^ 2‖ = x ^ 2 * ‖w‖ ^ 2 := by
    rw [norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have habs2 : |x| ^ (2 * (m + 1)) = (x ^ 2) ^ (m + 1) := by rw [pow_mul, sq_abs]
  have hw2 : ‖w‖ ^ (2 * (m + 1)) = (‖w‖ ^ 2) ^ (m + 1) := by rw [pow_mul]
  rw [hnorm, habs2, hw2, mul_pow]
  ring

end ShellBinomial

end

end GaloisForLFunctions.HTGeometry
