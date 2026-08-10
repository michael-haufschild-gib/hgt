import GaloisForLFunctions.RHTower.Sieve.GhsArithmeticBlocks
import GaloisForLFunctions.RHTower.Sieve.TripleConvolutionPerronSum

/-!
# The Perron step for one block

The corpus's parametrised triple-convolution Perron bound, instantiated at the block's weights.
Both of its inputs are already available: the truncation error `E` is the corpus's own, and the
vertical integral is `ghs_block_bound_uniform`.

```text
‖∑_{n ≤ …} (block k ⍟ (ghsInner f (N/A_k) ⍟ f_{≤L}))(n)‖
  ≤ E + (1/2π)·V·((N + ½)^σ)·ghsBlockConst σ .
```

The only work is the change of variable between the interval integral the Perron bound states and
the set integral over `Icc` in which the cell decomposition was proved — they agree because the
endpoints are ordered and a point is null.
-/

noncomputable section

namespace RHTower.Sieve

open Complex MeasureTheory Set Finset

/-- The block's outer weight is supported below its right endpoint. -/
theorem ghsOuterBlock_mem_Icc {f : ℕ → ℂ} {N A B q : ℕ} (h : ghsOuterBlock f N A B q ≠ 0) :
    q ∈ Finset.Icc 1 B := by
  have hmem := ghsOuterBlock_supp h
  have hp : q.Prime := prime_of_mem_block hmem
  rw [Finset.mem_sdiff, Nat.mem_primesLE] at hmem
  exact Finset.mem_Icc.2 ⟨hp.one_lt.le.trans' (by norm_num), hmem.1.1⟩

/-- The interval integral of the block's Perron integrand is the set integral over `Icc`. -/
theorem interval_eq_Icc_block_integrand {A' B' g : ℕ → ℂ} {σ x : ℝ} {n : ℕ} :
    (∫ t in (-((n : ℝ) * 2 ^ (0 : ℕ)))..((n : ℝ) * 2 ^ (0 : ℕ)),
        ‖LSeries A' ((σ : ℂ) + (t : ℝ) * I) * LSeries B' ((σ : ℂ) + (t : ℝ) * I)
          * LSeries g ((σ : ℂ) + (t : ℝ) * I)
          * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I))‖)
      = ∫ y in Set.Icc (-(n : ℝ)) ((n : ℝ)),
          ‖LSeries A' ((σ : ℂ) + (y : ℝ) * I) * LSeries B' ((σ : ℂ) + (y : ℝ) * I)
            * LSeries g ((σ : ℂ) + (y : ℝ) * I)
            * ((x : ℂ) ^ ((σ : ℂ) + (y : ℝ) * I) / ((σ : ℂ) + (y : ℝ) * I))‖ := by
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hpow : ((n : ℝ) * 2 ^ (0 : ℕ)) = (n : ℝ) := by norm_num
  rw [hpow, intervalIntegral.integral_of_le (by linarith),
    MeasureTheory.integral_Icc_eq_integral_Ioc]

/-- **The Perron step for one block.** -/
theorem ghs_block_sum_perron_le
    {f g : ℕ → ℂ} {A' B' L N n : ℕ} {σ E : ℝ} {V C : ℝ}
    (hAsupp : ∀ i : ℕ, ghsOuterBlock f N A' B' i ≠ 0 → i ∈ Finset.Icc 1 B')
    (hBsupp : ∀ i : ℕ, ghsInner f L i ≠ 0 → i ∈ Finset.Icc 1 L)
    (hgsupp : ∀ i : ℕ, g i ≠ 0 → i ∈ Finset.Icc 1 N)
    (hE : ‖(∑ i ∈ Finset.Icc 1 (min (B' * (L * N)) N),
              (LSeries.convolution (ghsOuterBlock f N A' B')
                (LSeries.convolution (ghsInner f L) g)) i)
            - ((1 / (2 * Real.pi) : ℝ) : ℂ)
              * ∫ t in (-((n : ℝ) * 2 ^ (0 : ℕ)))..((n : ℝ) * 2 ^ (0 : ℕ)),
                  (∑ i ∈ Finset.Icc 1 (B' * (L * N)),
                      (LSeries.convolution (ghsOuterBlock f N A' B')
                        (LSeries.convolution (ghsInner f L) g)) i
                        * ((i : ℂ) ^ (-((σ : ℂ) + (t : ℝ) * I))))
                    * (((((N : ℝ) + 1 / 2) : ℝ) : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I)
                        / ((σ : ℂ) + (t : ℝ) * I))‖ ≤ E)
    (hP : (∫ y in Set.Icc (-(n : ℝ)) ((n : ℝ)),
        ‖LSeries (ghsOuterBlock f N A' B') ((σ : ℂ) + (y : ℝ) * I)
          * LSeries (ghsInner f L) ((σ : ℂ) + (y : ℝ) * I)
          * LSeries g ((σ : ℂ) + (y : ℝ) * I)
          * (((((N : ℝ) + 1 / 2) : ℝ) : ℂ) ^ ((σ : ℂ) + (y : ℝ) * I)
              / ((σ : ℂ) + (y : ℝ) * I))‖) ≤ V * ((N : ℝ) + 1 / 2) ^ σ * C) :
    ‖∑ i ∈ Finset.Icc 1 (min (B' * (L * N)) N),
        (LSeries.convolution (ghsOuterBlock f N A' B')
          (LSeries.convolution (ghsInner f L) g)) i‖
      ≤ E + (1 / (2 * Real.pi)) * (V * ((N : ℝ) + 1 / 2) ^ σ * C) := by
  refine norm_sum_Icc_triple_of_error_and_analytic_le hAsupp hBsupp hgsupp
    (Nat.cast_nonneg n) 0 hE ?_
  rw [interval_eq_Icc_block_integrand]
  exact hP

end RHTower.Sieve

end
