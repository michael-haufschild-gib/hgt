import GaloisForLFunctions.RHTower.Sieve.DirichletRow

/-!
# The trivial benchmark for Dirichlet mean values

The Gram entries of `DirichletRow.lean` are sums of `N` unimodular terms, so each is at most `N` in
modulus, with equality on the diagonal.  Feeding that into the Halász–Montgomery frame gives the
trivial mean value theorem

`∑_{r} |F(t_r)|² ≤ R N ∑_n |a_n|²`,

and Cauchy–Schwarz gives the pointwise `|F(t)|² ≤ N ∑_n |a_n|²`.

These are the benchmarks any analytic estimate must beat: the content of a genuine mean value
theorem is that the *off-diagonal* Gram entries `∑_{n ≤ N} n^{i(u-t)}` are much smaller than `N`
when the frequencies are separated, so the row is dominated by its diagonal term.  Nothing here
assumes that; these bounds are unconditional and deliberately crude.
-/

namespace RHTower.Sieve

open Finset
open scoped InnerProductSpace

/-- The diagonal Gram entry is exactly the length. -/
theorem inner_dirRow_self (N : ℕ) (t : ℝ) : ⟪dirRow N t, dirRow N t⟫_ℂ = (N : ℂ) := by
  rw [inner_dirRow]
  have hone : ∀ n : Fin N,
      Complex.exp ((((t - t) * Real.log ((n : ℕ) + 1) : ℝ) : ℂ) * Complex.I) = 1 := by
    intro n
    simp
  rw [Finset.sum_congr rfl (fun n _ => hone n), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]

/-- Every Gram entry is at most the length in modulus. -/
theorem norm_inner_dirRow_le (N : ℕ) (t u : ℝ) :
    ‖⟪dirRow N t, dirRow N u⟫_ℂ‖ ≤ (N : ℝ) := by
  rw [inner_dirRow]
  refine le_trans (norm_sum_le _ _) ?_
  have hone : ∀ n : Fin N,
      ‖Complex.exp ((((u - t) * Real.log ((n : ℕ) + 1) : ℝ) : ℂ) * Complex.I)‖ = 1 :=
    fun n => Complex.norm_exp_ofReal_mul_I _
  rw [Finset.sum_congr rfl (fun n _ => hone n), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]

/-- **The pointwise trivial bound for a Dirichlet polynomial.** -/
theorem dirichlet_pointwise (N : ℕ) (t : ℝ) (a : EuclideanSpace ℂ (Fin N)) :
    ‖⟪dirRow N t, a⟫_ℂ‖ ^ 2 ≤ (N : ℝ) * ‖a‖ ^ 2 := by
  have hcs := norm_inner_le_norm (𝕜 := ℂ) (dirRow N t) a
  have h1 : ‖⟪dirRow N t, a⟫_ℂ‖ ^ 2 ≤ (‖dirRow N t‖ * ‖a‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hcs 2
  rw [mul_pow, norm_dirRow_sq] at h1
  exact h1

/-- **The trivial mean value theorem for Dirichlet polynomials.** -/
theorem dirichlet_bessel_trivial {ι : Type*} (N : ℕ) (s : Finset ι) (τ : ι → ℝ)
    (a : EuclideanSpace ℂ (Fin N)) :
    ∑ r ∈ s, ‖⟪dirRow N (τ r), a⟫_ℂ‖ ^ 2 ≤ ((s.card : ℝ) * (N : ℝ)) * ‖a‖ ^ 2 := by
  refine dirichlet_bessel N s τ (by positivity) (fun r _ => ?_) a
  calc ∑ t ∈ s, ‖⟪dirRow N (τ r), dirRow N (τ t)⟫_ℂ‖
      ≤ ∑ _t ∈ s, (N : ℝ) :=
        Finset.sum_le_sum (fun t _ => norm_inner_dirRow_le N (τ r) (τ t))
    _ = (s.card : ℝ) * (N : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]

end RHTower.Sieve
