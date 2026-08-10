import GaloisForLFunctions.RHTower.Sieve.GhsBlockDDamped
import GaloisForLFunctions.RHTower.Sieve.ConvolutionSummatorySwap
import GaloisForLFunctions.RHTower.Sieve.MertensFirst

/-!
# The block of small primes

The mean-square estimate for a block needs its primes to exceed the height, `q ≥ n²`; the block
containing the smallest primes cannot satisfy that.  It does not have to: for that block the
triple convolution is bounded trivially, and the trivial bound is already of the size the argument
tolerates.

Writing the summatory function of `a ⍟ (b ⍟ c)` as an iterated sum and using `‖c‖ ≤ 1` to replace
the innermost partial sum by its length gives

```text
‖∑_{i ≤ N} (a ⍟ (b ⍟ c))(i)‖ ≤ N·(∑_{p ≤ N} ‖a p‖/p)·(∑_{q ≤ N} ‖b q‖/q) ,
```

and for `a` the outer block over `(1, P]` and `b` the inner weight truncated at `M` the two masses
are Mertens sums:

```text
‖∑_{i ≤ N} (blk ⍟ (ghsInner f M ⍟ f))(i)‖
  ≤ N·((log P + log 4)/log⌊N/P⌋)·(log M + log 4) .
```

With `P = n²` a power of `log N` and `M = N` this is `≍ N·log n`, so after division by `log N` the
small-prime block contributes `N·log log N/log N` — the size of the recursion error itself, and
paid once rather than once per block.
-/

noncomputable section

namespace RHTower.Sieve

open Complex Finset

/-- **The trivial bound for a triple convolution's summatory function.**  The innermost factor is
replaced by the length of its range, leaving the two `1/n`-weighted masses of the outer factors. -/
theorem norm_sum_Icc_convolution_triple_trivial_le
    {a b c : ℕ → ℂ} (hc : ∀ i : ℕ, ‖c i‖ ≤ 1) (N : ℕ) :
    ‖∑ i ∈ Finset.Icc 1 N, LSeries.convolution a (LSeries.convolution b c) i‖
      ≤ (N : ℝ) * ((∑ p ∈ Finset.Icc 1 N, ‖a p‖ / p)
          * (∑ q ∈ Finset.Icc 1 N, ‖b q‖ / q)) := by
  classical
  have hSb0 : (0 : ℝ) ≤ ∑ q ∈ Finset.Icc 1 N, ‖b q‖ / q :=
    Finset.sum_nonneg fun q _ => by positivity
  rw [sum_Icc_convolution_triple_apply]
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ p ∈ Finset.Icc 1 N,
      ‖a p * ∑ q ∈ Finset.Icc 1 (N / p), b q * ∑ k ∈ Finset.Icc 1 (N / p / q), c k‖
        ≤ ((N : ℝ) * (‖a p‖ / p)) * ∑ q ∈ Finset.Icc 1 N, ‖b q‖ / q := by
    intro p hp
    rw [Finset.mem_Icc] at hp
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.1
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    have hinner : ∀ q ∈ Finset.Icc 1 (N / p),
        ‖b q * ∑ k ∈ Finset.Icc 1 (N / p / q), c k‖
          ≤ (N : ℝ) * (‖b q‖ / q) / p := by
      intro q hq
      rw [Finset.mem_Icc] at hq
      have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq.1
      have hq0 : (0 : ℝ) < (q : ℝ) := by linarith
      have hlen : ‖∑ k ∈ Finset.Icc 1 (N / p / q), c k‖ ≤ ((N / p / q : ℕ) : ℝ) := by
        refine le_trans (norm_sum_le _ _) ?_
        refine le_trans (Finset.sum_le_card_nsmul _ _ 1 fun k _ => hc k) ?_
        rw [Nat.card_Icc, nsmul_eq_mul, mul_one]
        simp
      have hdiv : ((N / p / q : ℕ) : ℝ) ≤ (N : ℝ) / ((p : ℝ) * (q : ℝ)) := by
        rw [Nat.div_div_eq_div_mul]
        refine le_trans (Nat.cast_div_le) ?_
        rw [Nat.cast_mul]
      rw [norm_mul]
      calc ‖b q‖ * ‖∑ k ∈ Finset.Icc 1 (N / p / q), c k‖
          ≤ ‖b q‖ * ((N : ℝ) / ((p : ℝ) * (q : ℝ))) :=
            mul_le_mul_of_nonneg_left (le_trans hlen hdiv) (norm_nonneg _)
        _ = (N : ℝ) * (‖b q‖ / q) / p := by field_simp
    have hstep : ‖a p * ∑ q ∈ Finset.Icc 1 (N / p), b q * ∑ k ∈ Finset.Icc 1 (N / p / q), c k‖
        ≤ ‖a p‖ * ∑ q ∈ Finset.Icc 1 (N / p), (N : ℝ) * (‖b q‖ / q) / p := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left
        (le_trans (norm_sum_le _ _) (Finset.sum_le_sum hinner)) (norm_nonneg _)
    refine le_trans hstep ?_
    have hsplit : ∑ q ∈ Finset.Icc 1 (N / p), (N : ℝ) * (‖b q‖ / q) / p
        = ((N : ℝ) / p) * ∑ q ∈ Finset.Icc 1 (N / p), ‖b q‖ / q := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun q _ => by ring
    rw [hsplit]
    have hsub : ∑ q ∈ Finset.Icc 1 (N / p), ‖b q‖ / q
        ≤ ∑ q ∈ Finset.Icc 1 N, ‖b q‖ / q := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun q _ _ => by positivity
      exact Finset.Icc_subset_Icc_right (Nat.div_le_self N p)
    calc ‖a p‖ * (((N : ℝ) / p) * ∑ q ∈ Finset.Icc 1 (N / p), ‖b q‖ / q)
        ≤ ‖a p‖ * (((N : ℝ) / p) * ∑ q ∈ Finset.Icc 1 N, ‖b q‖ / q) := by
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          exact mul_le_mul_of_nonneg_left hsub (by positivity)
      _ = ((N : ℝ) * (‖a p‖ / p)) * ∑ q ∈ Finset.Icc 1 N, ‖b q‖ / q := by field_simp
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  refine le_of_eq ?_
  ring

/-- The `1/p`-weighted mass of the outer block over `(1, P]`. -/
theorem sum_Icc_norm_ghsOuterBlock_div_le {f : ℕ → ℂ} (hf : ∀ i : ℕ, ‖f i‖ ≤ 1)
    {N P : ℕ} (hP : 1 ≤ P) (hPN : P ≤ N) (hNP : 2 ≤ N / P) :
    ∑ p ∈ Finset.Icc 1 N, ‖ghsOuterBlock f N 1 P p‖ / p
      ≤ (Real.log P + Real.log 4) / Real.log ((N / P : ℕ) : ℝ) := by
  classical
  have hsub : Nat.primesLE P ⊆ Finset.Icc 1 N := by
    intro p hp
    rw [Nat.mem_primesLE] at hp
    rw [Finset.mem_Icc]
    exact ⟨hp.2.one_lt.le, le_trans hp.1 hPN⟩
  have hzero : ∀ p ∈ Finset.Icc 1 N, p ∉ Nat.primesLE P →
      ‖ghsOuterBlock f N 1 P p‖ / p = 0 := by
    intro p _ hp
    have : ghsOuterBlock f N 1 P p = 0 := by
      rw [ghsOuterBlock, if_neg]
      intro hc
      exact hp (Finset.mem_sdiff.1 hc).1
    rw [this]
    simp
  rw [← Finset.sum_subset hsub hzero]
  have hNPR : (2 : ℝ) ≤ ((N / P : ℕ) : ℝ) := by exact_mod_cast hNP
  have hlog0 : (0 : ℝ) < Real.log ((N / P : ℕ) : ℝ) := Real.log_pos (by linarith)
  have hterm : ∀ p ∈ Nat.primesLE P,
      ‖ghsOuterBlock f N 1 P p‖ / p
        ≤ (Real.log p / p) / Real.log ((N / P : ℕ) : ℝ) := by
    intro p hp
    rw [Nat.mem_primesLE] at hp
    have hp0 : (0 : ℝ) < (p : ℝ) := by
      have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.2.two_le
      linarith
    have hlogp : (0 : ℝ) ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.2.one_le)
    have hval : ‖ghsOuterBlock f N 1 P p‖
        ≤ Real.log p / Real.log ((N / P : ℕ) : ℝ) := by
      rw [ghsOuterBlock]
      split_ifs with hc
      · rw [ghsOuter]
        split_ifs with hd
        · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          have hmono : Real.log ((N / P : ℕ) : ℝ) ≤ Real.log ((N / p : ℕ) : ℝ) := by
            refine Real.log_le_log (by linarith) ?_
            exact_mod_cast Nat.div_le_div_left hp.1 hp.2.pos
          have hpos : (0 : ℝ) < Real.log ((N / p : ℕ) : ℝ) := lt_of_lt_of_le hlog0 hmono
          rw [abs_of_nonneg (by positivity)]
          calc ‖f p‖ * (Real.log p / Real.log ((N / p : ℕ) : ℝ))
              ≤ 1 * (Real.log p / Real.log ((N / p : ℕ) : ℝ)) :=
                mul_le_mul_of_nonneg_right (hf p) (by positivity)
            _ = Real.log p / Real.log ((N / p : ℕ) : ℝ) := one_mul _
            _ ≤ Real.log p / Real.log ((N / P : ℕ) : ℝ) :=
                div_le_div_of_nonneg_left hlogp hlog0 hmono
        · rw [norm_zero]
          exact div_nonneg hlogp hlog0.le
      · rw [norm_zero]
        exact div_nonneg hlogp hlog0.le
    calc ‖ghsOuterBlock f N 1 P p‖ / p
        ≤ (Real.log p / Real.log ((N / P : ℕ) : ℝ)) / p :=
          div_le_div_of_nonneg_right hval hp0.le
      _ = (Real.log p / p) / Real.log ((N / P : ℕ) : ℝ) := by ring
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.sum_div]
  exact div_le_div_of_nonneg_right (mertensFirst_upper hP) hlog0.le

/-- The `1/q`-weighted mass of the inner weight truncated at `M`. -/
theorem sum_Icc_norm_ghsInner_div_le {f : ℕ → ℂ} (hf : ∀ i : ℕ, ‖f i‖ ≤ 1)
    {N M : ℕ} (hM : 1 ≤ M) (hMN : M ≤ N) :
    ∑ q ∈ Finset.Icc 1 N, ‖ghsInner f M q‖ / q ≤ Real.log M + Real.log 4 := by
  classical
  have hsub : Nat.primesLE M ⊆ Finset.Icc 1 N := by
    intro q hq
    rw [Nat.mem_primesLE] at hq
    rw [Finset.mem_Icc]
    exact ⟨hq.2.one_lt.le, le_trans hq.1 hMN⟩
  have hzero : ∀ q ∈ Finset.Icc 1 N, q ∉ Nat.primesLE M → ‖ghsInner f M q‖ / q = 0 := by
    intro q _ hq
    have : ghsInner f M q = 0 := by
      rw [ghsInner, if_neg]
      intro hc
      exact hq (Nat.mem_primesLE.2 ⟨hc.2, hc.1⟩)
    rw [this]; simp
  rw [← Finset.sum_subset hsub hzero]
  refine le_trans (Finset.sum_le_sum ?_) (mertensFirst_upper hM)
  intro q hq
  rw [Nat.mem_primesLE] at hq
  have hq0 : (0 : ℝ) < (q : ℝ) := by
    have : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq.2.two_le
    linarith
  have hval : ‖ghsInner f M q‖ ≤ Real.log q := by
    rw [ghsInner, if_pos ⟨hq.2, hq.1⟩, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg (by exact_mod_cast hq.2.one_le))]
    calc ‖f q‖ * Real.log q ≤ 1 * Real.log q :=
          mul_le_mul_of_nonneg_right (hf q) (Real.log_nonneg (by exact_mod_cast hq.2.one_le))
      _ = Real.log q := one_mul _
  exact div_le_div_of_nonneg_right hval hq0.le

/-- **The small-prime block.**  Its contribution is `N·log P·(log M)/log⌊N/P⌋`, paid once. -/
theorem norm_sum_Icc_ghs_small_block_le {f : ℕ → ℂ} (hf : ∀ i : ℕ, ‖f i‖ ≤ 1)
    {N P M : ℕ} (hP : 1 ≤ P) (hPN : P ≤ N) (hNP : 2 ≤ N / P) (hM : 1 ≤ M) (hMN : M ≤ N) :
    ‖∑ i ∈ Finset.Icc 1 N,
        (LSeries.convolution (ghsOuterBlock f N 1 P)
          (LSeries.convolution (ghsInner f M) f)) i‖
      ≤ (N : ℝ) * (((Real.log P + Real.log 4) / Real.log ((N / P : ℕ) : ℝ))
          * (Real.log M + Real.log 4)) := by
  refine le_trans (norm_sum_Icc_convolution_triple_trivial_le hf N) ?_
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  refine mul_le_mul_of_nonneg_left ?_ hN0
  have hA := sum_Icc_norm_ghsOuterBlock_div_le hf hP hPN hNP
  have hB := sum_Icc_norm_ghsInner_div_le hf hM hMN
  have hA0 : (0 : ℝ) ≤ ∑ p ∈ Finset.Icc 1 N, ‖ghsOuterBlock f N 1 P p‖ / p :=
    Finset.sum_nonneg fun p _ => by positivity
  have hB0 : (0 : ℝ) ≤ ∑ q ∈ Finset.Icc 1 N, ‖ghsInner f M q‖ / q :=
    Finset.sum_nonneg fun q _ => by positivity
  have hBr : (0 : ℝ) ≤ Real.log M + Real.log 4 := le_trans hB0 hB
  exact mul_le_mul hA hB hB0 (le_trans hA0 hA)

end RHTower.Sieve

end
