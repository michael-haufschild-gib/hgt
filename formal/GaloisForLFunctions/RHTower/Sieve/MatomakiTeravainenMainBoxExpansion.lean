import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenBlockChainFactor

/-!
# Complete finite main-term box expansion

Every repaired finite-iteration main term is exactly a finite sum over layer, active chain,
truncated Möbius block, and terminal cofactor block.  This is the finite family classified into
Proposition 2.2's three alternatives.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

noncomputable section

/-- Exact four-index box expansion of a repaired finite main term on a finite source window. -/
theorem coefficient_mul_finiteIterationMain_apply_eq_sum_adicBoxes
    {t : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (data : MTFiniteIterationSourceData t) (α : ℕ → ℂ)
    (depth : ℕ) (j : Fin (t + 1))
    {n N : ℕ} (hn : 0 < n) (hnN : n ≤ N) :
    (mtCoefficientAF α *
        mtFiniteIterationMain data.truncation data.block data.cutoff depth j) n =
      (∑ layer ∈ Finset.range (depth + 1),
        ∑ chain ∈ mtActiveBlockChains data.block layer j,
          ∑ i ∈ Finset.range (mtUpperAdicIndex δ data.D + 1),
            ∑ k ∈ Finset.range (mtUpperAdicIndex δ N + 1),
              mtSignedBlockChainAdicBoxAF α data.block chain
                data.z₀ data.D δ i k) n := by
  rw [mtFiniteIterationMain_eq_sum_signedLayers, Finset.mul_sum,
    arithmeticFunction_finset_sum_apply, arithmeticFunction_finset_sum_apply]
  apply Finset.sum_congr rfl
  intro layer hlayer
  rw [mtSignedMainLayerAF_eq_sum_activeChains, Finset.mul_sum,
    arithmeticFunction_finset_sum_apply, arithmeticFunction_finset_sum_apply]
  apply Finset.sum_congr rfl
  intro chain hchain
  simpa only [MTFiniteIterationSourceData.truncation] using
    coefficient_mul_signedBlockChain_apply_eq_sum_adicBoxes hδ α data.block chain
      (activeBlockChain_nodup hchain) data.z₀ data.D hn hnN

end

end RHTower.Sieve
