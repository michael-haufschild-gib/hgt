import GaloisForLFunctions.RHTower.RieszLogPartialSum

/-!
# The Tauberian step for Riesz means

Two Riesz means differ by exactly the tail of the logarithmic average,

```text
R(M) - R(N) = ∑_{N ≤ m < M} ( log(m+1) - log m ) · A(m) ,
```

with total weight `log M - log N`.  Splitting `A(m) = A(N) + (A(m) - A(N))` isolates the partial sum
being estimated:

```text
( log M - log N ) · A(N) = R(M) - R(N) - ∑_{N ≤ m < M} w_m ( A(m) - A(N) ) ,
```

so a bound `B` on the Riesz means and a bound `ε` on the increments over the block give

```text
‖A(N)‖ ≤ 2B / ( log M - log N ) + ε .
```

This is the Tauberian direction: bounded Riesz means alone say nothing about a single partial sum,
but together with control of the increments over a block of logarithmic length `h` they give
`2B/h + ε`.  Taking `h` large trades the first term against the second, which is what converts a
uniform bound on Riesz means into a logarithmic bound on partial sums.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.RHTower

/-- The logarithmic increments over a block sum to the logarithm of the ratio. -/
theorem sum_log_increment_Ico {N M : ℕ} (hNM : N ≤ M) :
    ∑ m ∈ Finset.Ico N M, (Real.log ((m : ℝ) + 1) - Real.log (m : ℝ))
      = Real.log (M : ℝ) - Real.log (N : ℝ) := by
  rw [Finset.sum_Ico_eq_sub _ hNM, sum_log_increment, sum_log_increment]

/-- The block form of the difference of two Riesz means. -/
theorem rieszLogSum_sub (a : ℕ → ℂ) {N M : ℕ} (hNM : N ≤ M) :
    (∑ n ∈ Finset.range M, a n
        * ((Real.log (M : ℝ) : ℂ) - (Real.log ((n : ℝ) + 1) : ℂ)))
      - (∑ n ∈ Finset.range N, a n
        * ((Real.log (N : ℝ) : ℂ) - (Real.log ((n : ℝ) + 1) : ℂ)))
      = ∑ m ∈ Finset.Ico N M,
          ((Real.log ((m : ℝ) + 1) : ℂ) - (Real.log (m : ℝ) : ℂ))
            * (∑ n ∈ Finset.range m, a n) := by
  rw [rieszLogSum_eq_sum_partialSum, rieszLogSum_eq_sum_partialSum,
    Finset.sum_Ico_eq_sub _ hNM]

/-- **The Tauberian bound for a partial sum from bounded Riesz means.** -/
theorem norm_partialSum_le_of_rieszLogSum_bound {a : ℕ → ℂ} {B ε : ℝ} {N M : ℕ}
    (hNM : N ≤ M)
    (hh : 0 < Real.log (M : ℝ) - Real.log (N : ℝ))
    (hRM : ‖∑ n ∈ Finset.range M, a n
        * ((Real.log (M : ℝ) : ℂ) - (Real.log ((n : ℝ) + 1) : ℂ))‖ ≤ B)
    (hRN : ‖∑ n ∈ Finset.range N, a n
        * ((Real.log (N : ℝ) : ℂ) - (Real.log ((n : ℝ) + 1) : ℂ))‖ ≤ B)
    (hinc : ∀ m ∈ Finset.Ico N M,
      ‖(∑ n ∈ Finset.range m, a n) - ∑ n ∈ Finset.range N, a n‖ ≤ ε) :
    ‖∑ n ∈ Finset.range N, a n‖
      ≤ 2 * B / (Real.log (M : ℝ) - Real.log (N : ℝ)) + ε := by
  set h : ℝ := Real.log (M : ℝ) - Real.log (N : ℝ) with hdef
  set AN : ℂ := ∑ n ∈ Finset.range N, a n with hAN
  have hwsum : ∑ m ∈ Finset.Ico N M,
      ((Real.log ((m : ℝ) + 1) : ℂ) - (Real.log (m : ℝ) : ℂ)) = (h : ℂ) := by
    rw [hdef, ← sum_log_increment_Ico hNM]
    push_cast
    ring
  have hsplit : ∑ m ∈ Finset.Ico N M,
        ((Real.log ((m : ℝ) + 1) : ℂ) - (Real.log (m : ℝ) : ℂ))
          * (∑ n ∈ Finset.range m, a n)
      = (h : ℂ) * AN
        + ∑ m ∈ Finset.Ico N M,
            ((Real.log ((m : ℝ) + 1) : ℂ) - (Real.log (m : ℝ) : ℂ))
              * ((∑ n ∈ Finset.range m, a n) - AN) := by
    have hterm : ∀ m ∈ Finset.Ico N M,
        ((Real.log ((m : ℝ) + 1) : ℂ) - (Real.log (m : ℝ) : ℂ))
            * (∑ n ∈ Finset.range m, a n)
          = ((Real.log ((m : ℝ) + 1) : ℂ) - (Real.log (m : ℝ) : ℂ)) * AN
            + ((Real.log ((m : ℝ) + 1) : ℂ) - (Real.log (m : ℝ) : ℂ))
              * ((∑ n ∈ Finset.range m, a n) - AN) := by
      intro m _
      ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.sum_mul, hwsum]
  have hkey : (h : ℂ) * AN
      = ((∑ n ∈ Finset.range M, a n
            * ((Real.log (M : ℝ) : ℂ) - (Real.log ((n : ℝ) + 1) : ℂ)))
          - (∑ n ∈ Finset.range N, a n
            * ((Real.log (N : ℝ) : ℂ) - (Real.log ((n : ℝ) + 1) : ℂ))))
        - ∑ m ∈ Finset.Ico N M,
            ((Real.log ((m : ℝ) + 1) : ℂ) - (Real.log (m : ℝ) : ℂ))
              * ((∑ n ∈ Finset.range m, a n) - AN) := by
    rw [rieszLogSum_sub a hNM, hsplit]
    ring
  have htail : ‖∑ m ∈ Finset.Ico N M,
      ((Real.log ((m : ℝ) + 1) : ℂ) - (Real.log (m : ℝ) : ℂ))
        * ((∑ n ∈ Finset.range m, a n) - AN)‖ ≤ ε * h := by
    refine le_trans (norm_sum_le _ _) ?_
    have hterm : ∀ m ∈ Finset.Ico N M,
        ‖((Real.log ((m : ℝ) + 1) : ℂ) - (Real.log (m : ℝ) : ℂ))
          * ((∑ n ∈ Finset.range m, a n) - AN)‖
          ≤ ε * (Real.log ((m : ℝ) + 1) - Real.log (m : ℝ)) := by
      intro m hm
      have hw : ((Real.log ((m : ℝ) + 1) : ℂ) - (Real.log (m : ℝ) : ℂ))
          = ((Real.log ((m : ℝ) + 1) - Real.log (m : ℝ) : ℝ) : ℂ) := by
        push_cast
        ring
      rw [hw, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (log_increment_nonneg m)]
      calc (Real.log ((m : ℝ) + 1) - Real.log (m : ℝ))
            * ‖(∑ n ∈ Finset.range m, a n) - AN‖
          ≤ (Real.log ((m : ℝ) + 1) - Real.log (m : ℝ)) * ε :=
            mul_le_mul_of_nonneg_left (hinc m hm) (log_increment_nonneg m)
        _ = ε * (Real.log ((m : ℝ) + 1) - Real.log (m : ℝ)) := by ring
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.mul_sum, sum_log_increment_Ico hNM]
  have hnorm : h * ‖AN‖ ≤ 2 * B + ε * h := by
    have hle : ‖(h : ℂ) * AN‖ ≤ 2 * B + ε * h := by
      rw [hkey]
      refine le_trans (norm_sub_le _ _) ?_
      have h1 : ‖(∑ n ∈ Finset.range M, a n
            * ((Real.log (M : ℝ) : ℂ) - (Real.log ((n : ℝ) + 1) : ℂ)))
          - (∑ n ∈ Finset.range N, a n
            * ((Real.log (N : ℝ) : ℂ) - (Real.log ((n : ℝ) + 1) : ℂ)))‖ ≤ 2 * B := by
        refine le_trans (norm_sub_le _ _) ?_
        linarith
      linarith [htail]
    have hval : ‖(h : ℂ) * AN‖ = h * ‖AN‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hh.le]
    rwa [hval] at hle
  rw [div_add' _ _ _ (ne_of_gt hh), le_div_iff₀ hh]
  linarith

end GaloisForLFunctions.RHTower

end
