import GaloisForLFunctions.RHTower.Sieve.GhsCellMass
import GaloisForLFunctions.RHTower.Sieve.MertensFirstBlock

/-!
# The outer prime range, one block at a time

The outer weight's cell mass is `∑_p log p/(p·log²(N/p))`.  Summed over all primes below `N` this is
`≍ 1`, but that is not how the argument uses it: it is used on a block `A < p ≤ B`, where the
complementary scale `N/p` is essentially constant, and the block's contribution is the block's
Mertens mass divided by that scale.

Two steps, both unconditional:

```text
mertensFirst_general_block :  ∑_{A < p ≤ B} log p/p ≤ log B − log A + C
sum_block_outer_le         :  ∑_{A < p ≤ B} log p/(p·log²(N/p)) ≤ (log B − log A + C)/log²(N/B)
```

with `C = log 4 + 1 + 2·logSqTailConst` absolute.  The second uses only that natural division is
antitone in its denominator, so `N/B ≤ N/p` for every `p ≤ B`.

At the argument's ranges `A = x^{1−e^{1−k}}`, `B = x^{1−e^{−k}}` this gives
`log B − log A = e^{−k}(e−1)log x` and `log(N/B) ≥ e^{−k}log x`, hence `≍ e^k/log x` — the shape
that cancels the inner factor's `e^{−k}log x`.
-/

noncomputable section

namespace RHTower.Sieve

open Finset

/-- The absolute constant of the general Mertens block bound. -/
noncomputable def mertensBlockGapConst : ℝ := Real.log 4 + 1 + 2 * logSqTailConst

theorem mertensBlockGapConst_nonneg : 0 ≤ mertensBlockGapConst := by
  rw [mertensBlockGapConst]
  have h4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hL := logSqTailConst_nonneg
  linarith

/-- **Mertens' first theorem on an arbitrary block.**  Differencing the two-sided theorem at the two
endpoints; the main terms subtract and only the increment survives. -/
theorem mertensFirst_general_block {A B : ℕ} (hA : 1 ≤ A) (hAB : A ≤ B) :
    ∑ p ∈ Nat.primesLE B \ Nat.primesLE A, Real.log (p : ℝ) / (p : ℝ)
      ≤ Real.log B - Real.log A + mertensBlockGapConst := by
  classical
  have hB : 1 ≤ B := le_trans hA hAB
  have hsub : Nat.primesLE A ⊆ Nat.primesLE B := by
    intro p hp
    rw [Nat.mem_primesLE] at hp ⊢
    exact ⟨le_trans hp.1 hAB, hp.2⟩
  have hup := mertensFirst_upper hB
  have hlow := mertensFirst_lower hA
  rw [Finset.sum_sdiff_eq_sub hsub, mertensBlockGapConst]
  linarith

/-- **The outer weight's mass on a block.**  The complementary scale is bounded below by its value
at the right endpoint, because natural division is antitone in its denominator. -/
theorem sum_block_outer_le {A B N : ℕ} (hA : 1 ≤ A) (hAB : A ≤ B) (hBN : 2 ≤ N / B) :
    ∑ p ∈ Nat.primesLE B \ Nat.primesLE A,
        Real.log (p : ℝ) / ((p : ℝ) * (Real.log ((N / p : ℕ) : ℝ)) ^ (2 : ℕ))
      ≤ (Real.log B - Real.log A + mertensBlockGapConst)
          / (Real.log ((N / B : ℕ) : ℝ)) ^ (2 : ℕ) := by
  classical
  have hBN2 : (2 : ℝ) ≤ ((N / B : ℕ) : ℝ) := by exact_mod_cast hBN
  have hlogB : (0 : ℝ) < Real.log ((N / B : ℕ) : ℝ) := Real.log_pos (by linarith)
  have hsqB : (0 : ℝ) < (Real.log ((N / B : ℕ) : ℝ)) ^ (2 : ℕ) := by positivity
  -- termwise: the scale at `p` is at least the scale at `B`
  have hterm : ∀ p ∈ Nat.primesLE B \ Nat.primesLE A,
      Real.log (p : ℝ) / ((p : ℝ) * (Real.log ((N / p : ℕ) : ℝ)) ^ (2 : ℕ))
        ≤ (Real.log (p : ℝ) / (p : ℝ)) / (Real.log ((N / B : ℕ) : ℝ)) ^ (2 : ℕ) := by
    intro p hp
    rw [Finset.mem_sdiff, Nat.mem_primesLE] at hp
    obtain ⟨⟨hpB, hpp⟩, -⟩ := hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    have hlogp : (0 : ℝ) ≤ Real.log (p : ℝ) := Real.log_nonneg (by linarith)
    have hdiv : N / B ≤ N / p := Nat.div_le_div_left hpB hpp.pos
    have hdivR : ((N / B : ℕ) : ℝ) ≤ ((N / p : ℕ) : ℝ) := by exact_mod_cast hdiv
    have hlogle : Real.log ((N / B : ℕ) : ℝ) ≤ Real.log ((N / p : ℕ) : ℝ) :=
      Real.log_le_log (by linarith) hdivR
    have hsqle : (Real.log ((N / B : ℕ) : ℝ)) ^ (2 : ℕ) ≤ (Real.log ((N / p : ℕ) : ℝ)) ^ (2 : ℕ) := by
      nlinarith [hlogB.le, hlogle]
    have hden : (0 : ℝ) < (p : ℝ) * (Real.log ((N / B : ℕ) : ℝ)) ^ (2 : ℕ) := by positivity
    have hden' : (p : ℝ) * (Real.log ((N / B : ℕ) : ℝ)) ^ (2 : ℕ)
        ≤ (p : ℝ) * (Real.log ((N / p : ℕ) : ℝ)) ^ (2 : ℕ) :=
      mul_le_mul_of_nonneg_left hsqle hp0.le
    have hgoal : Real.log (p : ℝ) / ((p : ℝ) * (Real.log ((N / p : ℕ) : ℝ)) ^ (2 : ℕ))
        ≤ Real.log (p : ℝ) / ((p : ℝ) * (Real.log ((N / B : ℕ) : ℝ)) ^ (2 : ℕ)) :=
      div_le_div_of_nonneg_left hlogp hden hden'
    refine le_trans hgoal (le_of_eq ?_)
    field_simp
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.sum_div]
  exact div_le_div_of_nonneg_right (mertensFirst_general_block hA hAB) hsqB.le

end RHTower.Sieve

end
