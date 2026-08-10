import GaloisForLFunctions.RHTower.Sieve.PrimeLineSharpAffine

/-!
# The outer polynomial of one block, and the balance that makes the blocks cancel

The outer weight restricted to a block of the prime range is a prime-supported Dirichlet
polynomial, and its mean square on the Perron line is the block's `I₁`:

```text
∫_{|y| ≤ T} ‖L(ghsOuterBlock, σ+iy)‖² dy
  ≤ 2π·[ (5·700/4)·2·(log B − log A + C)/log²(N/B)  +  (5T/4)·(plain mass) ] .
```

The second factor of the Cauchy–Schwarz split is the inner polynomial's cell mass,
`≍ log(N/A) + log 4`.  Writing `S = log(N/B)` for the block's scale, the product of the two is

```text
((log B − log A + C)/S²) · (log(N/A) + log 4)  ≤  (κ + C)(κ' + log 4)
```

whenever the block is *balanced*, `log B − log A ≤ κS` and `log(N/A) ≤ κ'S`.  **The scale cancels**:
one factor of `S` from the numerator against one of the two in the denominator.  That cancellation
is the entire purpose of partitioning the outer range — it makes every block contribute the same
bounded amount, so the number of blocks is the only thing that multiplies.
-/

noncomputable section

namespace RHTower.Sieve

open Complex MeasureTheory Set Finset

/-- The outer weight restricted to a block of the prime range. -/
def ghsOuterBlock (f : ℕ → ℂ) (N A B : ℕ) (p : ℕ) : ℂ :=
  if p ∈ Nat.primesLE B \ Nat.primesLE A then ghsOuter f N p else 0

theorem ghsOuterBlock_supp {f : ℕ → ℂ} {N A B p : ℕ} (h : ghsOuterBlock f N A B p ≠ 0) :
    p ∈ Nat.primesLE B \ Nat.primesLE A := by
  by_contra hc
  rw [ghsOuterBlock, if_neg hc] at h
  exact h rfl

theorem ghsOuterBlock_eq {f : ℕ → ℂ} {N A B p : ℕ} (h : p ∈ Nat.primesLE B \ Nat.primesLE A) :
    ghsOuterBlock f N A B p = ghsOuter f N p := by
  rw [ghsOuterBlock, if_pos h]

theorem prime_of_mem_block {A B q : ℕ} (h : q ∈ Nat.primesLE B \ Nat.primesLE A) : q.Prime := by
  rw [Finset.mem_sdiff] at h
  exact Nat.prime_of_mem_primesLE h.1

theorem zero_notMem_block (A B : ℕ) : (0 : ℕ) ∉ Nat.primesLE B \ Nat.primesLE A := by
  intro h
  exact Nat.not_prime_zero (prime_of_mem_block h)

/-- **The block's `I₁`.** -/
theorem integral_Icc_normSq_LSeries_ghsOuterBlock_le
    {f : ℕ → ℂ} (hbdd : ∀ n : ℕ, ‖f n‖ ≤ 1) {σ : ℝ} (hσ : 1 ≤ σ) {T : ℝ} (hT : 1 ≤ T)
    {A B N : ℕ} (hA : 1 ≤ A) (hAB : A ≤ B) (hBN : 2 ≤ N / B)
    (hsq : ∀ q ∈ Nat.primesLE B \ Nat.primesLE A, T * T ≤ (q : ℝ))
    (hbig : ∀ q ∈ Nat.primesLE B \ Nat.primesLE A, 4 ≤ Real.log ((q : ℝ) * (1 / T)))
    {κplain : ℝ}
    (hplain : ∑ q ∈ Nat.primesLE B \ Nat.primesLE A,
        ‖ghsOuterBlock f N A B q * ((((q : ℝ) ^ (-σ) : ℝ)) : ℂ)‖ ^ 2 ≤ κplain) :
    (∫ y in Set.Icc (-T) T, ‖LSeries (ghsOuterBlock f N A B) ((σ : ℂ) + (y : ℝ) * I)‖ ^ 2)
      ≤ 2 * Real.pi
          * ((5 * 700 / 4)
                * (2 * ((Real.log B - Real.log A + mertensBlockGapConst)
                    / (Real.log ((N / B : ℕ) : ℝ)) ^ 2))
              + (5 * T / 4) * κplain) := by
  have hprime : ∀ q ∈ Nat.primesLE B \ Nat.primesLE A, q.Prime := fun q hq => prime_of_mem_block hq
  have hzero := zero_notMem_block A B
  have hsupp : ∀ n : ℕ, ghsOuterBlock f N A B n ≠ 0 → n ∈ Nat.primesLE B \ Nat.primesLE A :=
    fun n h => ghsOuterBlock_supp h
  refine le_trans (integral_Icc_normSq_LSeries_le_prime_sharp_delta hprime hzero hsupp σ hT hbig) ?_
  have hπ : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  refine mul_le_mul_of_nonneg_left ?_ hπ
  -- the sharp mass on the block, after identifying the restricted weight with the full one
  have hmass : ∑ q ∈ Nat.primesLE B \ Nat.primesLE A,
        ((q : ℝ) / Real.log ((q : ℝ) * (1 / T)))
          * ‖ghsOuterBlock f N A B q * ((((q : ℝ) ^ (-σ) : ℝ)) : ℂ)‖ ^ 2
      = ∑ q ∈ Nat.primesLE B \ Nat.primesLE A,
        ((q : ℝ) / Real.log ((q : ℝ) * (1 / T)))
          * ‖ghsOuter f N q * ((((q : ℝ) ^ (-σ) : ℝ)) : ℂ)‖ ^ 2 :=
    Finset.sum_congr rfl fun q hq => by rw [ghsOuterBlock_eq hq]
  rw [hmass]
  have hsharp := sum_sharp_mass_ghsOuter_block_le (f := f) hbdd hσ hT hA hAB hBN hsq
  have hTpos : (0 : ℝ) ≤ 5 * T / 4 := by linarith
  have h1 : (5 * 700 / 4 : ℝ)
        * ∑ q ∈ Nat.primesLE B \ Nat.primesLE A,
          ((q : ℝ) / Real.log ((q : ℝ) * (1 / T)))
            * ‖ghsOuter f N q * ((((q : ℝ) ^ (-σ) : ℝ)) : ℂ)‖ ^ 2
      ≤ (5 * 700 / 4 : ℝ) * (2 * ((Real.log B - Real.log A + mertensBlockGapConst)
          / (Real.log ((N / B : ℕ) : ℝ)) ^ 2)) :=
    mul_le_mul_of_nonneg_left hsharp (by norm_num)
  have h2 : (5 * T / 4 : ℝ)
        * ∑ q ∈ Nat.primesLE B \ Nat.primesLE A,
          ‖ghsOuterBlock f N A B q * ((((q : ℝ) ^ (-σ) : ℝ)) : ℂ)‖ ^ 2
      ≤ (5 * T / 4 : ℝ) * κplain :=
    mul_le_mul_of_nonneg_left hplain hTpos
  linarith [h1, h2]

/-- **The block balance.**  With the block's width and the inner range both proportional to the
block's scale, one factor of the scale cancels and the product is bounded independently of it. -/
theorem block_balance_le {S C κ κ' W U : ℝ} (hS : 1 ≤ S) (hC : 0 ≤ C) (hκ : 0 ≤ κ) (hκ' : 0 ≤ κ')
    (hW : 0 ≤ W) (hU : 0 ≤ U) (h1 : W ≤ κ * S) (h2 : U ≤ κ' * S) :
    ((W + C) / S ^ 2) * (U + Real.log 4) ≤ (κ + C) * (κ' + Real.log 4) := by
  have hS0 : (0 : ℝ) < S := by linarith
  have hlog4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hfirst : (W + C) / S ^ 2 ≤ (κ + C) / S := by
    rw [div_le_div_iff₀ (by positivity) hS0]
    nlinarith [mul_le_mul_of_nonneg_right h1 hS0.le,
      mul_nonneg (mul_nonneg hC hS0.le) (by linarith : (0 : ℝ) ≤ S - 1)]
  have hsecond : U + Real.log 4 ≤ (κ' + Real.log 4) * S := by
    nlinarith [h2, hlog4, hS]
  have hfirst0 : (0 : ℝ) ≤ (W + C) / S ^ 2 := by positivity
  have hsnd0 : (0 : ℝ) ≤ U + Real.log 4 := by linarith
  have hκC : (0 : ℝ) ≤ (κ + C) / S := by positivity
  calc ((W + C) / S ^ 2) * (U + Real.log 4)
      ≤ ((κ + C) / S) * (U + Real.log 4) := mul_le_mul_of_nonneg_right hfirst hsnd0
    _ ≤ ((κ + C) / S) * ((κ' + Real.log 4) * S) := mul_le_mul_of_nonneg_left hsecond hκC
    _ = (κ + C) * (κ' + Real.log 4) := by field_simp

end RHTower.Sieve

end
