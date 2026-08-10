import GaloisForLFunctions.RHTower.Sieve.GhsAssembly

/-!
# The top of the outer prime range

The geometric partition cannot reach `N/2`.  Its threshold `2^{k+1}·4·log 2 ≤ log N` caps the index
at `2^K ≤ (log N)/(8 log 2)`, hence `ghsScale N K ≥ 256` and `ghsBlockLeft N K ≤ N/256`, while the
coverage condition of the capstone needs the endpoints to reach `N/2` — the value beyond which
`ghsOuter` vanishes.  The two demands are incompatible: no admissible `K` does both.

The interval left over, `(ghsBlockLeft N K, N]`, needs no mean-square estimate.  On it
`log⌊N/p⌋ ≤ log 256`, so the outer coefficients are only `O(log p)`, but Mertens' first theorem on
a block bounds their `1/p`-mass by `(log B − log A + C)/log 2`, which for this block is an absolute
constant — and the inner range `N/A` is bounded too.  The trivial bound is therefore `O(N)`, and
after division by `log N` the top of the range costs `O(N/log N)`.

This is the general form of `norm_sum_Icc_ghs_small_block_le`: there the denominator `log⌊N/P⌋` was
large and worth keeping, here it is bounded and `log 2` is the right denominator.  Neither bound
dominates the other, and the argument uses both.
-/

noncomputable section

namespace RHTower.Sieve

open Complex Finset

/-- The `1/p`-mass of a block's outer weight, by Mertens' first theorem on the block. -/
theorem sum_Icc_norm_ghsOuterBlock_div_le_gap {f : ℕ → ℂ} (hf : ∀ i : ℕ, ‖f i‖ ≤ 1)
    {N A B : ℕ} (hA : 1 ≤ A) (hAB : A ≤ B) (hBN : B ≤ N) :
    ∑ p ∈ Finset.Icc 1 N, ‖ghsOuterBlock f N A B p‖ / p
      ≤ (1 / Real.log 2) * (Real.log B - Real.log A + mertensBlockGapConst) := by
  classical
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hsub : Nat.primesLE B \ Nat.primesLE A ⊆ Finset.Icc 1 N := by
    intro p hp
    have hpp : p.Prime := prime_of_mem_block hp
    rw [Finset.mem_sdiff, Nat.mem_primesLE] at hp
    rw [Finset.mem_Icc]
    exact ⟨hpp.one_lt.le, le_trans hp.1.1 hBN⟩
  have hzero : ∀ p ∈ Finset.Icc 1 N, p ∉ Nat.primesLE B \ Nat.primesLE A →
      ‖ghsOuterBlock f N A B p‖ / p = 0 := by
    intro p _ hp
    have : ghsOuterBlock f N A B p = 0 := by rw [ghsOuterBlock, if_neg hp]
    rw [this]
    simp
  rw [← Finset.sum_subset hsub hzero]
  have hterm : ∀ p ∈ Nat.primesLE B \ Nat.primesLE A,
      ‖ghsOuterBlock f N A B p‖ / p ≤ (1 / Real.log 2) * (Real.log p / p) := by
    intro p hp
    have hpp : p.Prime := prime_of_mem_block hp
    have hp0 : (0 : ℝ) < (p : ℝ) := by
      have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
      linarith
    calc ‖ghsOuterBlock f N A B p‖ / p
        ≤ ((1 / Real.log 2) * Real.log p) / p :=
          div_le_div_of_nonneg_right (norm_ghsOuterBlock_le hf N A B p) hp0.le
      _ = (1 / Real.log 2) * (Real.log p / p) := by ring
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (mertensFirst_general_block hA hAB) (by positivity)

/-- **The trivial bound for an arbitrary block.** -/
theorem norm_sum_Icc_ghs_block_trivial_le {f : ℕ → ℂ} (hf : ∀ i : ℕ, ‖f i‖ ≤ 1)
    {N A B M : ℕ} (hA : 1 ≤ A) (hAB : A ≤ B) (hBN : B ≤ N) (hM : 1 ≤ M) (hMN : M ≤ N) :
    ‖∑ i ∈ Finset.Icc 1 N,
        (LSeries.convolution (ghsOuterBlock f N A B)
          (LSeries.convolution (ghsInner f M) f)) i‖
      ≤ (N : ℝ) * (((1 / Real.log 2)
            * (Real.log B - Real.log A + mertensBlockGapConst))
          * (Real.log M + Real.log 4)) := by
  refine le_trans (norm_sum_Icc_convolution_triple_trivial_le hf N) ?_
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  refine mul_le_mul_of_nonneg_left ?_ hN0
  have hA' := sum_Icc_norm_ghsOuterBlock_div_le_gap hf hA hAB hBN
  have hB' := sum_Icc_norm_ghsInner_div_le hf hM hMN
  have hA0 : (0 : ℝ) ≤ ∑ p ∈ Finset.Icc 1 N, ‖ghsOuterBlock f N A B p‖ / p :=
    Finset.sum_nonneg fun p _ => by positivity
  have hB0 : (0 : ℝ) ≤ ∑ q ∈ Finset.Icc 1 N, ‖ghsInner f M q‖ / q :=
    Finset.sum_nonneg fun q _ => by positivity
  exact mul_le_mul hA' hB' hB0 (le_trans hA0 hA')

end RHTower.Sieve

end
