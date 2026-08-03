import GaloisForLFunctions.RHTower.Sieve.DirichletTrivial

/-!
# Gram entries are Lipschitz in the frequency

The chord of an arc never exceeds the arc, so the phase exponential is `1`-Lipschitz:

`‖e^{ia} - e^{ib}‖ ≤ |a - b|`.

Applied coordinatewise to a Dirichlet row this says the Gram entry stays near its diagonal value `N`
while the frequencies stay close:

`‖⟪dirRow N t, dirRow N u⟫ - N‖ ≤ |u - t| ∑_{n ≤ N} log n`.

This is the *near-diagonal* half of the mean value problem: no cancellation is available when the
frequencies are within `1/log N` of each other, so any useful separation hypothesis must exceed that
scale.  It is complementary to — and independent of — the estimate showing cancellation for well
separated frequencies.
-/

namespace RHTower.Sieve

open Finset
open scoped InnerProductSpace

/-- **The phase exponential is 1-Lipschitz.**  The chord never exceeds the arc. -/
theorem norm_exp_phase_sub_le (a b : ℝ) :
    ‖Complex.exp (((a : ℝ) : ℂ) * Complex.I) - Complex.exp (((b : ℝ) : ℂ) * Complex.I)‖
      ≤ |a - b| := by
  have hfactor : Complex.exp (((a : ℝ) : ℂ) * Complex.I) - Complex.exp (((b : ℝ) : ℂ) * Complex.I)
      = Complex.exp (((b : ℝ) : ℂ) * Complex.I)
        * (Complex.exp (((a - b : ℝ) : ℂ) * Complex.I) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [hfactor, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, norm_exp_I_sub_one]
  have hsin : |Real.sin ((a - b) / 2)| ≤ |(a - b) / 2| := Real.abs_sin_le_abs
  have habs : |(a - b) / 2| = |a - b| / 2 := by
    rw [abs_div]
    norm_num
  rw [habs] at hsin
  linarith

/-- **Gram entries are Lipschitz in the frequency.** -/
theorem norm_inner_dirRow_sub_card_le (N : ℕ) (t u : ℝ) :
    ‖⟪dirRow N t, dirRow N u⟫_ℂ - (N : ℂ)‖
      ≤ |u - t| * ∑ n : Fin N, Real.log ((n : ℕ) + 1) := by
  rw [inner_dirRow]
  have hcard : (N : ℂ) = ∑ _n : Fin N, (1 : ℂ) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  rw [hcard, ← Finset.sum_sub_distrib]
  refine le_trans (norm_sum_le _ _) ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun n _ => ?_
  have hone : (1 : ℂ) = Complex.exp (((0 : ℝ) : ℂ) * Complex.I) := by simp
  rw [hone]
  refine le_trans (norm_exp_phase_sub_le _ 0) ?_
  have hlog : 0 ≤ Real.log ((n : ℕ) + 1) := by
    refine Real.log_nonneg ?_
    have : (0 : ℝ) ≤ ((n : ℕ) : ℝ) := by positivity
    linarith
  rw [sub_zero, abs_mul, abs_of_nonneg hlog]

end RHTower.Sieve
