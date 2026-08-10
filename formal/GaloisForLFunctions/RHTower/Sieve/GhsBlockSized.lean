import GaloisForLFunctions.RHTower.Sieve.GhsPartition

/-!
# A block above the height needs only its shape

Three of the six hypotheses of `ghs_block_D_le_general` are consequences of a single condition on
the block's left endpoint, `n² ≤ A`, together with `e⁴ ≤ n`:

* every prime of the block satisfies `n² ≤ q`, because `q > A`;
* every prime of the block satisfies `e⁴ ≤ q/n`, because `q/n > n`;
* the plain mass is `(log B/log⌊N/B⌋)²/A` by `sum_plain_mass_ghsOuterBlock_le`, and `1/A ≤ 1/n²`
  turns the domination hypothesis into
  `(5/4n)·(log B/log⌊N/B⌋)²·(log M + log 4) ≤ 1750·Γ`, in which the height appears only in the
  denominator.

That last inequality is the one the choice of `n` has to meet.  For the geometric blocks
`log B_k/log⌊N/B_k⌋ ≤ 2^{k+1}` and `log M + log 4 ≤ log N + log 4`, so with `K ≍ log log N` blocks
it asks for `n ≫ (log N)³` — a height polynomial in `log N`, which is what the rest of the argument
wants anyway.
-/

noncomputable section

namespace RHTower.Sieve

open Complex MeasureTheory Set Finset

/-- A prime of the block `(A, B]` exceeds `A`. -/
theorem lt_of_mem_block {A B q : ℕ} (hq : q ∈ Nat.primesLE B \ Nat.primesLE A) : A < q := by
  have hqp : q.Prime := prime_of_mem_block hq
  rw [Finset.mem_sdiff] at hq
  by_contra hle
  exact hq.2 (Nat.mem_primesLE.2 ⟨by omega, hqp⟩)

/-- Above the height every prime of the block exceeds the height's square. -/
theorem ghs_block_hsq {A B n : ℕ} (hA : n ^ 2 ≤ A) :
    ∀ q ∈ Nat.primesLE B \ Nat.primesLE A, (n : ℝ) * (n : ℝ) ≤ (q : ℝ) := by
  intro q hq
  have h : n ^ 2 < q := lt_of_le_of_lt hA (lt_of_mem_block hq)
  have : (n : ℝ) ^ 2 ≤ (q : ℝ) := by exact_mod_cast h.le
  nlinarith [this]

/-- Above the height every prime of the block satisfies `e⁴ ≤ q/n`. -/
theorem ghs_block_hbig {A B n : ℕ} (hn : 1 ≤ n) (hA : n ^ 2 ≤ A)
    (hne : Real.exp 4 ≤ (n : ℝ)) :
    ∀ q ∈ Nat.primesLE B \ Nat.primesLE A, 4 ≤ Real.log ((q : ℝ) * (1 / (n : ℝ))) := by
  intro q hq
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h : n ^ 2 < q := lt_of_le_of_lt hA (lt_of_mem_block hq)
  have hqR : (n : ℝ) ^ 2 ≤ (q : ℝ) := by exact_mod_cast h.le
  have hkey : (n : ℝ) ≤ (q : ℝ) * (1 / (n : ℝ)) := by
    rw [mul_one_div, le_div_iff₀ hn0]
    nlinarith [hqR]
  rw [Real.le_log_iff_exp_le (by nlinarith [hne, Real.exp_pos (4 : ℝ)])]
  linarith [hne, hkey]

/-- **A block above the height.**  Its shape is the only thing left to supply. -/
theorem ghs_block_D_le_sized
    {f : ℕ → ℂ} {Ab Bb M N n z : ℕ} (hf1 : f 1 = 1)
    (hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n)
    (hf : ∀ i : ℕ, ‖f i‖ ≤ 1)
    {σ δ : ℝ} (hσ : 1 < σ) (hz : 1 ≤ z) (hδ : 0 ≤ δ)
    (hunif : ∀ y : ℝ, |y| ≤ (n : ℝ) →
      δ ≤ Real.sqrt (mulDistSqPair f (charFn y) (Nat.primesLE z)))
    (hn : 1 ≤ n) (hne : Real.exp 4 ≤ (n : ℝ)) (hN : 1 ≤ N)
    (hA : 1 ≤ Ab) (hAB : Ab ≤ Bb) (hBN : 2 ≤ N / Bb) (hM : 1 ≤ M)
    (hA2 : n ^ 2 ≤ Ab)
    {Γ : ℝ}
    (hshape : ((Real.log Bb - Real.log Ab + mertensBlockGapConst)
          / (Real.log ((N / Bb : ℕ) : ℝ)) ^ 2) * (Real.log M + Real.log 4) ≤ Γ)
    (hdom : (5 / (4 * (n : ℝ)))
        * ((Real.log Bb / Real.log ((N / Bb : ℕ) : ℝ)) ^ 2 * (Real.log M + Real.log 4))
      ≤ 1750 * Γ)
    {E : ℝ}
    (hE : ‖(∑ i ∈ Finset.Icc 1 (min (Bb * (M * N)) N),
              (LSeries.convolution (ghsOuterBlock f N Ab Bb)
                (LSeries.convolution (ghsInner f M) (truncSeq f N))) i)
            - ((1 / (2 * Real.pi) : ℝ) : ℂ)
              * ∫ t in (-((n : ℝ) * 2 ^ (0 : ℕ)))..((n : ℝ) * 2 ^ (0 : ℕ)),
                  (∑ i ∈ Finset.Icc 1 (Bb * (M * N)),
                      (LSeries.convolution (ghsOuterBlock f N Ab Bb)
                        (LSeries.convolution (ghsInner f M) (truncSeq f N))) i
                        * ((i : ℂ) ^ (-((σ : ℂ) + (t : ℝ) * I))))
                    * (((((N : ℝ) + 1 / 2) : ℝ) : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I)
                        / ((σ : ℂ) + (t : ℝ) * I))‖ ≤ E) :
    ‖∑ i ∈ Finset.Icc 1 N,
        (LSeries.convolution (ghsOuterBlock f N Ab Bb)
          (LSeries.convolution (ghsInner f M) f)) i‖
      ≤ E + (1 / (2 * Real.pi))
          * (dampedSize σ δ z N * ((N : ℝ) + 1 / 2) ^ σ * ghsBlockConstOf σ Γ) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hBN2 : (2 : ℝ) ≤ ((N / Bb : ℕ) : ℝ) := by exact_mod_cast hBN
  have hlogNB : (0 : ℝ) < Real.log ((N / Bb : ℕ) : ℝ) := Real.log_pos (by linarith)
  have hB1 : 1 ≤ Bb := le_trans hA hAB
  have hlogB : (0 : ℝ) ≤ Real.log Bb := Real.log_nonneg (by exact_mod_cast hB1)
  have hlogM : (0 : ℝ) ≤ Real.log M + Real.log 4 := by
    have h1 : (0 : ℝ) ≤ Real.log M := Real.log_nonneg (by exact_mod_cast hM)
    have h2 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    linarith
  set R : ℝ := (Real.log Bb / Real.log ((N / Bb : ℕ) : ℝ)) ^ 2 with hRdef
  have hR0 : (0 : ℝ) ≤ R := by rw [hRdef]; positivity
  have hκ0 : (0 : ℝ) ≤ R * (1 / (Ab : ℝ)) := by
    have : (0 : ℝ) ≤ 1 / (Ab : ℝ) := by positivity
    exact mul_nonneg hR0 this
  have hplain := sum_plain_mass_ghsOuterBlock_le hf hσ.le hA hAB hBN
  -- the domination, with `1/A ≤ 1/n²`
  have hAn : (n : ℝ) ^ 2 ≤ (Ab : ℝ) := by exact_mod_cast hA2
  have hinv : (1 : ℝ) / (Ab : ℝ) ≤ 1 / (n : ℝ) ^ 2 :=
    one_div_le_one_div_of_le (by positivity) hAn
  have hdom' : (5 * (n : ℝ) / 4) * (R * (1 / (Ab : ℝ))) * (Real.log M + Real.log 4)
      ≤ 1750 * Γ := by
    have hstep : (5 * (n : ℝ) / 4) * (R * (1 / (Ab : ℝ))) * (Real.log M + Real.log 4)
        ≤ (5 * (n : ℝ) / 4) * (R * (1 / (n : ℝ) ^ 2)) * (Real.log M + Real.log 4) := by
      have h1 : R * (1 / (Ab : ℝ)) ≤ R * (1 / (n : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hinv hR0
      have h2 : (0 : ℝ) ≤ 5 * (n : ℝ) / 4 := by positivity
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 h2) hlogM
    have heq : (5 * (n : ℝ) / 4) * (R * (1 / (n : ℝ) ^ 2)) * (Real.log M + Real.log 4)
        = (5 / (4 * (n : ℝ))) * (R * (Real.log M + Real.log 4)) := by
      field_simp
    rw [heq] at hstep
    linarith [hstep, hdom]
  exact ghs_block_D_le_general hf1 hmul hf hσ hz hδ hunif hn hN hA hAB hBN hM
    (ghs_block_hsq hA2) (ghs_block_hbig hn hA2 hne) hκ0 hplain hshape hdom' hE

end RHTower.Sieve

end
