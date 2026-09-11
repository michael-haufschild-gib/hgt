import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicSpacedToMeasure
import GaloisForLFunctions.RHTower.Sieve.PrimeBlockLevelSetCount

/-!
# Huxley's large-values count, as a measure

`Sieve/PrimeBlockLevelSetCount.card_le_of_mem_primeBlockLevelSet` bounds the cardinality of a
one-spaced family inside a prime-block level set.  `MenonHarmonicSpacedToMeasure` converts any such
bound into a measure.  Composing them gives Huxley's estimate in the form the receivers of this
chain consume: a bound on the **measure** of a prime-block level set.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- **Huxley's two-term density estimate, as a measure bound.** -/
theorem volume_real_primeBlockLevelSet_le_huxley
    {N : ℕ} (hN : 1 ≤ N) {B : Finset ℕ} (hB : B ⊆ Finset.Ico N (2 * N))
    {G E sigma : ℝ} (hG : 0 ≤ G) (hE : 0 ≤ E)
    (hmass : (B.card : ℝ) ≤ E / (N : ℝ))
    (hthr : 2400 * E ≤ (N : ℝ) ^ ((1 : ℝ) / 2 - 2 * sigma)) :
    volume.real (primeBlockLevelSet B G ((N : ℝ) ^ (-sigma)))
      ≤ 2 * ((6594624 * (2 * Real.pi * G) * E ^ 3 * (N : ℝ) ^ (6 * sigma - 2)
              + 2 * E * (N : ℝ) ^ (2 * sigma))
            * (1 + 12 * Real.pi * (1 + Real.log (2 * (2 * Real.pi * G) + 1)))) * 1 := by
  refine measureReal_le_of_spaced_card_le hG one_pos
    (primeBlockLevelSet_subset B G ((N : ℝ) ^ (-sigma))) ?_
  intro P hPsep hPmem
  exact card_le_of_mem_primeBlockLevelSet hN hB hG hE hmass hthr P hPsep hPmem

end

end RHTower.Sieve
