import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicHuxleyMeasure
import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicNarrowBlockComparison
import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicFrequencyPartition

/-!
# Huxley's estimate as a per-block large-value measure

The narrow-block comparison
(`norm_harmonicPrimeBlockPoly_le_narrow`: `‖harmonic‖ ≤ ‖ordinary‖/Q + #B·eta/Q`) turns a lower
bound on the harmonic prime polynomial into one on the ordinary polynomial, so a harmonic
block-large set sits inside an ordinary prime-block level set.  Huxley's count, in the measure form
of `MenonHarmonicHuxleyMeasure`, then bounds it.

The output is exactly the family `M j` that
`integral_Icc_normSq_harmonicRamareBilinear_le_partition_blockMeasures` consumes.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- A harmonic block-large set sits inside an ordinary prime-block level set. -/
theorem menonHarmonicBlockLarge_subset_primeBlockLevelSet
    (P : Finset ℕ) {Q eta : ℝ} (hQ : 0 < Q) (heta : 0 ≤ eta) (V : ℕ → ℝ) (W : ℝ) (j : ℕ) :
    menonHarmonicBlockLarge P Q eta V W j
      ⊆ primeBlockLevelSet (geomBlock P Q (1 + eta) j) W
          ((Q * (1 + eta) ^ j) * V j
            - ((geomBlock P Q (1 + eta) j).card : ℝ) * eta) := by
  intro w hw
  obtain ⟨hmem, hge⟩ := hw
  refine ⟨hmem, ?_⟩
  have hQj : 0 < Q * (1 + eta) ^ j := by positivity
  have hrange : ∀ p ∈ geomBlock P Q (1 + eta) j,
      Q * (1 + eta) ^ j < (p : ℝ) ∧ (p : ℝ) ≤ (Q * (1 + eta) ^ j) * (1 + eta) := by
    intro p hp
    rw [geomBlock, Finset.mem_filter] at hp
    refine ⟨hp.2.1, ?_⟩
    calc (p : ℝ) ≤ Q * (1 + eta) ^ (j + 1) := hp.2.2
      _ = (Q * (1 + eta) ^ j) * (1 + eta) := by rw [pow_succ]; ring
  have hnarrow := norm_harmonicPrimeBlockPoly_le_narrow
    (B := geomBlock P Q (1 + eta) j) (Q := Q * (1 + eta) ^ j) (eta := eta)
    hQj heta hrange w
  have h1 : V j ≤ ‖primeBlockPoly (geomBlock P Q (1 + eta) j) w‖ / (Q * (1 + eta) ^ j)
      + ((geomBlock P Q (1 + eta) j).card : ℝ) * eta / (Q * (1 + eta) ^ j) :=
    le_trans hge hnarrow
  have h2 : V j * (Q * (1 + eta) ^ j)
      ≤ ‖primeBlockPoly (geomBlock P Q (1 + eta) j) w‖
        + ((geomBlock P Q (1 + eta) j).card : ℝ) * eta := by
    have hmul := mul_le_mul_of_nonneg_right h1 hQj.le
    rwa [add_mul, div_mul_cancel₀ _ (ne_of_gt hQj),
      div_mul_cancel₀ _ (ne_of_gt hQj)] at hmul
  simp only [Set.mem_setOf_eq]
  linarith

/-- **Huxley's estimate as a per-block large-value measure.** -/
theorem volume_real_menonHarmonicBlockLarge_le_huxley
    (P : Finset ℕ) {Q eta W : ℝ} (hQ : 0 < Q) (heta : 0 ≤ eta) (V : ℕ → ℝ) (j : ℕ)
    {N : ℕ} (hN : 1 ≤ N) (hBsub : geomBlock P Q (1 + eta) j ⊆ Finset.Ico N (2 * N))
    {Ec sigma : ℝ} (hW : 0 ≤ W) (hEc : 0 ≤ Ec)
    (hmass : ((geomBlock P Q (1 + eta) j).card : ℝ) ≤ Ec / (N : ℝ))
    (hthr : 2400 * Ec ≤ (N : ℝ) ^ ((1 : ℝ) / 2 - 2 * sigma))
    (hlevel : (Q * (1 + eta) ^ j) * V j
        - ((geomBlock P Q (1 + eta) j).card : ℝ) * eta = (N : ℝ) ^ (-sigma)) :
    volume.real (menonHarmonicBlockLarge P Q eta V W j)
      ≤ 2 * ((6594624 * (2 * Real.pi * W) * Ec ^ 3 * (N : ℝ) ^ (6 * sigma - 2)
              + 2 * Ec * (N : ℝ) ^ (2 * sigma))
            * (1 + 12 * Real.pi * (1 + Real.log (2 * (2 * Real.pi * W) + 1)))) * 1 := by
  have hsub := menonHarmonicBlockLarge_subset_primeBlockLevelSet P hQ heta V W j
  rw [hlevel] at hsub
  have hfin : volume (primeBlockLevelSet (geomBlock P Q (1 + eta) j) W
      ((N : ℝ) ^ (-sigma))) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_
      (measure_mono (primeBlockLevelSet_subset (geomBlock P Q (1 + eta) j) W _))
    simp [Real.volume_Icc]
  refine le_trans (measureReal_mono hsub hfin) ?_
  exact volume_real_primeBlockLevelSet_le_huxley hN hBsub hW hEc hmass hthr

end

end RHTower.Sieve
