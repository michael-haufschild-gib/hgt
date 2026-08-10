import GaloisForLFunctions.RHTower.Sieve.GhsBlockPlainMass

/-!
# The Granville–Harper–Soundararajan bound for one block

Every estimate the argument needs is now a corpus theorem, so they compose.  For one block
`(A, B]` of the outer prime range, at the symmetric height `n`:

```text
∫_{|y| ≤ n} ‖L(A_blk)·L(B_inner)·L(g)·x^s/s‖ dy
  ≤ √( 2π·[ (5·700/4)·2·(log B − log A + C)/log²(N/B) + (5n/4)·κ_plain ] )
    · √( V²·x^{2σ}·(7/σ² + 1) · 2π·(5/4)·701·(log M + log 4) ) .
```

The first factor is `I₁`: the outer polynomial's mean square, with the sharp near-diagonal weight
and the height entering only through the negligible plain mass.  The second is `I₂`: the long
factor's aggregate — bounded by `V²x^{2σ}` times an absolute constant, *not* by `V²x^{2σ}·log n` —
times the inner polynomial's Mertens mass.

Nothing here is asymptotic.  The two square roots are closed formulas in `A`, `B`, `M`, `N`, `n`,
`σ`, `x`, `V`.
-/

noncomputable section

namespace RHTower.Sieve

open Complex MeasureTheory Set Finset

/-- **The block's Perron bound.** -/
theorem ghs_block_perron_bound
    {f g : ℕ → ℂ} {n : ℕ} (hf : ∀ i : ℕ, ‖f i‖ ≤ 1)
    {σ x V : ℝ} (hσ : 1 ≤ σ) (hx : 0 < x) (hV : 0 ≤ V)
    (hgc : Continuous fun t : ℝ => LSeries g ((σ : ℂ) + (t : ℝ) * I))
    (hgb : ∀ y : ℝ, |y| ≤ (n : ℝ) → ‖LSeries g ((σ : ℂ) + (y : ℝ) * I)‖ ≤ V)
    {Ab Bb N M : ℕ} (hn : 1 ≤ n) (hA : 1 ≤ Ab) (hAB : Ab ≤ Bb) (hBN : 2 ≤ N / Bb)
    (hsq : ∀ q ∈ Nat.primesLE Bb \ Nat.primesLE Ab, (n : ℝ) * (n : ℝ) ≤ (q : ℝ))
    (hbig : ∀ q ∈ Nat.primesLE Bb \ Nat.primesLE Ab,
      4 ≤ Real.log ((q : ℝ) * (1 / (n : ℝ))))
    (hM : 1 ≤ M) {κplain : ℝ}
    (hplain : ∑ q ∈ Nat.primesLE Bb \ Nat.primesLE Ab,
        ‖ghsOuterBlock f N Ab Bb q * ((((q : ℝ) ^ (-σ) : ℝ)) : ℂ)‖ ^ 2 ≤ κplain) :
    (∫ y in Set.Icc (-(n : ℝ)) ((n : ℝ)),
        ‖LSeries (ghsOuterBlock f N Ab Bb) ((σ : ℂ) + (y : ℝ) * I)
          * LSeries (ghsInner f M) ((σ : ℂ) + (y : ℝ) * I)
          * LSeries g ((σ : ℂ) + (y : ℝ) * I)
          * ((x : ℂ) ^ ((σ : ℂ) + (y : ℝ) * I) / ((σ : ℂ) + (y : ℝ) * I))‖)
      ≤ Real.sqrt (2 * Real.pi
            * ((5 * 700 / 4) * (2 * ((Real.log Bb - Real.log Ab + mertensBlockGapConst)
                  / (Real.log ((N / Bb : ℕ) : ℝ)) ^ 2))
              + (5 * (n : ℝ) / 4) * κplain))
        * Real.sqrt (V ^ 2 * (x ^ σ) ^ 2 * (7 / σ ^ 2 + 1)
            * (2 * Real.pi * ((5 / 4) * 701 * (Real.log M + Real.log 4)))) := by
  classical
  have hσ0 : (0 : ℝ) < σ := by linarith
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  -- the supports
  have hA0 : (0 : ℕ) ∉ Nat.primesLE Bb \ Nat.primesLE Ab := zero_notMem_block Ab Bb
  have hAsupp : ∀ i : ℕ, ghsOuterBlock f N Ab Bb i ≠ 0 →
      i ∈ Nat.primesLE Bb \ Nat.primesLE Ab := fun i h => ghsOuterBlock_supp h
  have hsBp : ∀ i ∈ Nat.primesLE M, i.Prime := fun i hi => Nat.prime_of_mem_primesLE hi
  have hB0 : (0 : ℕ) ∉ Nat.primesLE M := fun h => Nat.not_prime_zero (hsBp 0 h)
  have hBsupp : ∀ i : ℕ, ghsInner f M i ≠ 0 → i ∈ Nat.primesLE M := by
    intro i h
    rw [ghsInner] at h
    by_cases hc : Nat.Prime i ∧ i ≤ M
    · exact Nat.mem_primesLE.2 ⟨hc.2, hc.1⟩
    · rw [if_neg hc] at h; exact absurd rfl h
  -- the cell bound at the symmetric range
  obtain ⟨v, hvmem, hvle⟩ := exists_cell_bound_integral_norm_perron_triple
    (A := ghsOuterBlock f N Ab Bb) (B := ghsInner f M) (f := g)
    hA0 hAsupp hsBp hB0 hBsupp (σ := σ) (x := x) (b := -(n : ℝ)) hσ0 hx hgc (2 * n)
  have hrange : -(n : ℝ) + ((2 * n : ℕ) : ℝ) * 1 = (n : ℝ) := by push_cast; ring
  rw [hrange] at hvle
  refine le_trans hvle ?_
  -- the first factor
  have hI₁ : (∫ y in Set.Icc (-(n : ℝ)) ((n : ℝ)),
      ‖LSeries (ghsOuterBlock f N Ab Bb) ((σ : ℂ) + (y : ℝ) * I)‖ ^ 2)
      ≤ 2 * Real.pi
          * ((5 * 700 / 4) * (2 * ((Real.log Bb - Real.log Ab + mertensBlockGapConst)
                / (Real.log ((N / Bb : ℕ) : ℝ)) ^ 2))
            + (5 * (n : ℝ) / 4) * κplain) :=
    integral_Icc_normSq_LSeries_ghsOuterBlock_le hf hσ hnR hA hAB hBN hsq hbig hplain
  -- the second factor
  have hvmem' : ∀ k, k < 2 * n →
      v k ∈ Set.Icc (-(n : ℝ) + (k : ℝ) * 1) (-(n : ℝ) + ((k : ℝ) + 1) * 1) := hvmem
  have hagg := sum_cells_aggregate_le_of_bound (σ := σ) (x := x) (V := V) hσ0 hx hV
    (le_rfl : 2 * n ≤ 2 * n) hgb hvmem'
  have hinner := primeCellMass_ghsInner_le (f := f) hf hσ M hM
  have hinner0 : (0 : ℝ) ≤ primeCellMass
      (fun i => ghsInner f M i * ((((i : ℝ) ^ (-σ) : ℝ)) : ℂ)) (Nat.primesLE M) :=
    primeCellMass_nonneg _ hsBp
  have hagg0 : (0 : ℝ) ≤ ∑ k ∈ Finset.range (2 * n),
      (‖LSeries g ((σ : ℂ) + (v k : ℝ) * I)‖ * (x ^ σ / ‖(σ : ℂ) + (v k : ℝ) * I‖)) ^ 2 :=
    Finset.sum_nonneg fun k _ => by positivity
  have hπ0 : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hI₂ : (∑ k ∈ Finset.range (2 * n),
        (‖LSeries g ((σ : ℂ) + (v k : ℝ) * I)‖ * (x ^ σ / ‖(σ : ℂ) + (v k : ℝ) * I‖)) ^ 2)
        * (2 * Real.pi * primeCellMass
            (fun i => ghsInner f M i * ((((i : ℝ) ^ (-σ) : ℝ)) : ℂ)) (Nat.primesLE M))
      ≤ V ^ 2 * (x ^ σ) ^ 2 * (7 / σ ^ 2 + 1)
          * (2 * Real.pi * ((5 / 4) * 701 * (Real.log M + Real.log 4))) := by
    have hV2 : (0 : ℝ) ≤ V ^ 2 * (x ^ σ) ^ 2 * (7 / σ ^ 2 + 1) := by
      have : (0 : ℝ) ≤ (x ^ σ) ^ 2 := by positivity
      have h7 : (0 : ℝ) ≤ 7 / σ ^ 2 + 1 := by positivity
      positivity
    have hstep1 : (∑ k ∈ Finset.range (2 * n),
          (‖LSeries g ((σ : ℂ) + (v k : ℝ) * I)‖ * (x ^ σ / ‖(σ : ℂ) + (v k : ℝ) * I‖)) ^ 2)
          * (2 * Real.pi * primeCellMass
              (fun i => ghsInner f M i * ((((i : ℝ) ^ (-σ) : ℝ)) : ℂ)) (Nat.primesLE M))
        ≤ (V ^ 2 * (x ^ σ) ^ 2 * (7 / σ ^ 2 + 1))
          * (2 * Real.pi * primeCellMass
              (fun i => ghsInner f M i * ((((i : ℝ) ^ (-σ) : ℝ)) : ℂ)) (Nat.primesLE M)) :=
      mul_le_mul_of_nonneg_right hagg (by positivity)
    have hstep2 : (V ^ 2 * (x ^ σ) ^ 2 * (7 / σ ^ 2 + 1))
          * (2 * Real.pi * primeCellMass
              (fun i => ghsInner f M i * ((((i : ℝ) ^ (-σ) : ℝ)) : ℂ)) (Nat.primesLE M))
        ≤ (V ^ 2 * (x ^ σ) ^ 2 * (7 / σ ^ 2 + 1))
          * (2 * Real.pi * ((5 / 4) * 701 * (Real.log M + Real.log 4))) := by
      refine mul_le_mul_of_nonneg_left ?_ hV2
      exact mul_le_mul_of_nonneg_left hinner hπ0
    linarith [hstep1, hstep2]
  exact mul_le_mul (Real.sqrt_le_sqrt hI₁) (Real.sqrt_le_sqrt hI₂) (Real.sqrt_nonneg _)
    (Real.sqrt_nonneg _)

end RHTower.Sieve

end
