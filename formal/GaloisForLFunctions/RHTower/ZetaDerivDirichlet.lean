import Mathlib

/-!
# The Dirichlet series of `ζ'`

For `Re s > 1`, `ζ'(s) = -∑_{n} log n / n^s`, obtained by differentiating the absolutely convergent
`LSeries` of the constant function `1` (whose sum is `ζ`) term by term.
-/

namespace GaloisForLFunctions

open Complex Filter

/-- `ζ'(s) = -∑ log n / n^s` for `Re s > 1`. -/
theorem zeta_deriv_eq_neg_tsum {s : ℂ} (hs : 1 < s.re) :
    deriv riemannZeta s = -∑' n : ℕ, (Real.log n : ℂ) / (n : ℂ) ^ s := by
  have hopen : {z : ℂ | 1 < z.re} ∈ nhds s :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs
  have heq : riemannZeta =ᶠ[nhds s] LSeries 1 := by
    filter_upwards [hopen] with z hz
    exact (LSeries_one_eq_riemannZeta hz).symm
  rw [heq.deriv_eq]
  have habs : LSeries.abscissaOfAbsConv (1 : ℕ → ℂ) < (s.re : EReal) := by
    rw [LSeries.abscissaOfAbsConv_one]; exact_mod_cast hs
  rw [LSeries_deriv habs, neg_inj]
  unfold LSeries
  apply tsum_congr
  intro n
  rw [LSeries.term_def]
  by_cases hn : n = 0
  · simp [hn]
  · simp only [hn, if_false, LSeries.logMul, Pi.one_apply, mul_one]
    rw [Complex.ofReal_log (Nat.cast_nonneg n), Complex.ofReal_natCast]

end GaloisForLFunctions
