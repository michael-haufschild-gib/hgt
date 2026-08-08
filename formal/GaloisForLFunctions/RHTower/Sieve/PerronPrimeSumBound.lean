import GaloisForLFunctions.RHTower.Sieve.PerronVerticalPrimeBound
import GaloisForLFunctions.RHTower.Sieve.PerronTruncationError
import GaloisForLFunctions.RHTower.Sieve.LSeriesBlockDecomposition

/-!
# A partial sum of a prime-supported sequence, bounded through the sharp Perron formula

Closing the chain: the truncated Perron formula turns the partial sum into a vertical integral with a
polylogarithmic error, the modulus of the integrand factors into the Dirichlet series and the kernel,
and the dyadic height split against the prime-sieve mean square bounds the integral.  The result is an
unconditional bound

`‖∑_{n ≤ M} a_n‖ ≤ (truncation error) + (1/2π)·perronVerticalPrimeBound`

for any sequence supported on primes in `[1, M]`, with the sieve level and modulus free.

Everything in the bound is arithmetic-free except the two sieve constants: the `n`-weighted mass of the
coefficients over `log Y`, and the sieve's own error and level against their plain mass.  The height of
the truncation appears in the truncation error as `1/T` and in the analytic term only through the number
of dyadic blocks, so raising the height is almost free.
-/

noncomputable section
namespace RHTower.Sieve
open Complex MeasureTheory Set

/-- The analytic bound of the vertical Perron integral over a symmetric dyadic range. -/
def perronVerticalPrimeBound (a : ℕ → ℂ) (s : Finset ℕ) (σ x t₀ : ℝ) (z Y : ℕ) (M : ℕ) : ℝ :=
  2 * ((x ^ σ * Real.sqrt (sieveMeanSquareConst a s σ Y) * Real.sqrt 2 / Real.sqrt t₀)
          * (1 - Real.sqrt 2 / 2)⁻¹
        + 2 * x ^ σ * Real.sqrt (sieveMeanSquareRate a s σ z Y) * M)
    + (x ^ σ / σ) * (Real.sqrt (2 * t₀)
        * Real.sqrt (sieveMeanSquareConst a s σ Y + sieveMeanSquareRate a s σ z Y * t₀))

/-- A finitely supported Dirichlet series is the finite sum `∑ a_n n^{−w}`. -/
theorem sum_mul_cpow_neg_eq_LSeries {a : ℕ → ℂ} {s : Finset ℕ} (hs0 : 0 ∉ s)
    (hsupp : ∀ n : ℕ, a n ≠ 0 → n ∈ s) (w : ℂ) :
    (∑ n ∈ s, a n * (n : ℂ) ^ (-w)) = LSeries a w := by
  rw [LSeries_eq_sum_term_of_support hsupp w]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn0 : n ≠ 0 := fun h => hs0 (h ▸ hn)
  rw [LSeries.term_def, if_neg hn0, Complex.cpow_neg, div_eq_mul_inv]

/-- **A partial sum of a prime-supported sequence.**  The truncated Perron formula at the half-integer
cutoff `N + 1/2`, with the vertical integral bounded by the dyadic split against the prime-sieve mean
square. -/
theorem norm_sum_Icc_prime_le {a : ℕ → ℂ} {M N : ℕ} (hN : 1 ≤ N)
    (hsupp : ∀ n : ℕ, a n ≠ 0 → n ∈ Finset.Icc 1 M)
    (hprime : ∀ n ∈ Finset.Icc 1 M, a n ≠ 0 → n.Prime) {B : ℝ} (hB : ∀ n, ‖a n‖ ≤ B)
    {σ t₀ : ℝ} (hσ : 1 ≤ σ) (ht₀ : 1 ≤ t₀)
    (z Y : ℕ) (hY : 1 ≤ Y) (hYz : Y ≤ z) (hz : 2 ≤ z) (hlog : 0 < Real.log Y) (K : ℕ) :
    ‖∑ n ∈ Finset.Icc 1 (min M N), a n‖
      ≤ 2 * ((N : ℝ) + 1) * B * (((N : ℝ) + 1 / 2)) ^ σ * (1 + Real.log M)
            / (Real.pi * (t₀ * 2 ^ K))
          + (1 / (2 * Real.pi))
              * perronVerticalPrimeBound a (Finset.Icc 1 M) σ ((N : ℝ) + 1 / 2) t₀ z Y K := by
  have hσ0 : (0 : ℝ) < σ := by linarith
  have ht₀0 : (0 : ℝ) < t₀ := by linarith
  have hone : (1 : ℝ) ≤ 2 ^ K := one_le_pow₀ (by norm_num)
  have hT : (0 : ℝ) < t₀ * 2 ^ K := by positivity
  have hTle : -(t₀ * 2 ^ K) ≤ t₀ * 2 ^ K := by linarith
  have hs0 : (0 : ℕ) ∉ Finset.Icc 1 M := by simp
  have hN0 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hx : (0 : ℝ) < (N : ℝ) + 1 / 2 := by linarith
  set x : ℝ := (N : ℝ) + 1 / 2 with hxdef
  set T : ℝ := t₀ * 2 ^ K with hTdef
  -- the Perron formula, with the polynomial recognised as the Dirichlet series
  have hP := norm_sum_Icc_sub_perron_integral_le (c := a) (M := M) hN hB (σ := σ) (T := T) hσ hT
  have hbridge : ∀ t : ℝ,
      (∑ n ∈ Finset.Icc 1 M, a n * (n : ℂ) ^ (-((σ : ℂ) + (t : ℝ) * I)))
          * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I))
        = LSeries a ((σ : ℂ) + (t : ℝ) * I)
            * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I)) := by
    intro t
    rw [sum_mul_cpow_neg_eq_LSeries hs0 hsupp]
  rw [intervalIntegral.integral_congr (g := fun t : ℝ =>
      LSeries a ((σ : ℂ) + (t : ℝ) * I)
        * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I)))
    (fun t _ => hbridge t)] at hP
  -- the vertical integral
  have hanalytic := integral_symm_norm_perron_integrand_le hs0 hsupp hprime hσ0 hx ht₀
    z Y hY hYz hz hlog K
  have hnormint : ‖∫ t in (-T)..T, LSeries a ((σ : ℂ) + (t : ℝ) * I)
        * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I))‖
      ≤ ∫ t in (-T)..T, ‖LSeries a ((σ : ℂ) + (t : ℝ) * I)
          * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I))‖ :=
    intervalIntegral.norm_integral_le_integral_norm hTle
  have hscale : ‖((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t in (-T)..T,
        LSeries a ((σ : ℂ) + (t : ℝ) * I)
          * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I))‖
      ≤ (1 / (2 * Real.pi)) * perronVerticalPrimeBound a (Finset.Icc 1 M) σ x t₀ z Y K := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (2 * Real.pi))]
    refine mul_le_mul_of_nonneg_left (le_trans hnormint ?_) (by positivity)
    rw [perronVerticalPrimeBound]
    exact hanalytic
  -- assemble
  have htri : ‖∑ n ∈ Finset.Icc 1 (min M N), a n‖
      ≤ ‖(∑ n ∈ Finset.Icc 1 (min M N), a n) - ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t in (-T)..T,
            LSeries a ((σ : ℂ) + (t : ℝ) * I)
              * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I))‖
          + ‖((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t in (-T)..T,
            LSeries a ((σ : ℂ) + (t : ℝ) * I)
              * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I))‖ := by
    have := norm_add_le ((∑ n ∈ Finset.Icc 1 (min M N), a n) - ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t in (-T)..T, LSeries a ((σ : ℂ) + (t : ℝ) * I)
          * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I)))
      (((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t in (-T)..T, LSeries a ((σ : ℂ) + (t : ℝ) * I)
          * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I)))
    simpa using this
  linarith [hP, hscale, htri]

end RHTower.Sieve
end
