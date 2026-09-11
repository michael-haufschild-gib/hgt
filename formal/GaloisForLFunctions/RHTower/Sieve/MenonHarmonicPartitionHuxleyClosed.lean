import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicBlockHuxley
import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicSomeLargeUnionBudget

/-!
# The window estimate closed by Huxley's large-values theorem

`MenonHarmonicBlockHuxley` produces the per-block large-value measure family that
`integral_Icc_normSq_harmonicRamareBilinear_le_partition_blockMeasures` consumes.  Substituting it
closes the window estimate with **Huxley's two-term density estimate** as the large-values input —
strictly stronger than the moment method of `MenonHarmonicPartitionMomentClosed`, which is vacuous
on narrow blocks.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- Huxley's measure bound for one block, as a named scalar. -/
def huxleyBlockMeasureBound (Nb : ℕ) (Ec sigma W : ℝ) : ℝ :=
  2 * ((6594624 * (2 * Real.pi * W) * Ec ^ 3 * (Nb : ℝ) ^ (6 * sigma - 2)
        + 2 * Ec * (Nb : ℝ) ^ (2 * sigma))
      * (1 + 12 * Real.pi * (1 + Real.log (2 * (2 * Real.pi * W) + 1)))) * 1

/-- **The window estimate, closed by Huxley's large-values theorem.** -/
theorem integral_Icc_normSq_harmonicRamareBilinear_le_partition_huxley
    {P : Finset ℕ} {A₀ B₀ L : ℕ} {Q eta W : ℝ} (k : ℕ) (hk : 1 ≤ k)
    (hA₀ : 1 ≤ A₀) (hQ : 0 < Q) (heta : 0 ≤ eta) (hW : 1 ≤ W) (hL : 1 ≤ L)
    (hPprime : ∀ p ∈ P, p.Prime)
    (hPrange : ∀ p ∈ P, Q < (p : ℝ) ∧ (p : ℝ) ≤ Q * (1 + eta) ^ L)
    (hleft : ∀ j ∈ Finset.range L,
      1 ≤ ⌈(A₀ : ℝ) / ((Q * (1 + eta) ^ j) * (1 + eta))⌉₊)
    (hright : ∀ j ∈ Finset.range L,
      1 ≤ ⌊(B₀ : ℝ) / (Q * (1 + eta) ^ j)⌋₊)
    (htop : ∀ j ∈ Finset.range L, 1 ≤ ⌊Q * (1 + eta) ^ (j + 1)⌋₊)
    (V V₀ : ℕ → ℝ) (hV₀ : ∀ j ∈ Finset.range L, 0 < V₀ j)
    (J : ℕ → ℕ)
    (hJ : ∀ j ∈ Finset.range L,
      harmonicPrimeMass (geomBlock P Q (1 + eta) j) ≤ 2 ^ (J j) * V₀ j)
    (Nb : ℕ → ℕ) (Ec sigma : ℕ → ℝ)
    (hNb : ∀ j ∈ Finset.range L, 1 ≤ Nb j)
    (hBsub : ∀ j ∈ Finset.range L,
      geomBlock P Q (1 + eta) j ⊆ Finset.Ico (Nb j) (2 * Nb j))
    (hEc : ∀ j ∈ Finset.range L, 0 ≤ Ec j)
    (hmass : ∀ j ∈ Finset.range L,
      ((geomBlock P Q (1 + eta) j).card : ℝ) ≤ Ec j / ((Nb j : ℕ) : ℝ))
    (hthr : ∀ j ∈ Finset.range L,
      2400 * Ec j ≤ ((Nb j : ℕ) : ℝ) ^ ((1 : ℝ) / 2 - 2 * sigma j))
    (hlevel : ∀ j ∈ Finset.range L,
      (Q * (1 + eta) ^ j) * V j - ((geomBlock P Q (1 + eta) j).card : ℝ) * eta
        = ((Nb j : ℕ) : ℝ) ^ (-(sigma j))) :
    (∫ w in Set.Icc (-W) W, ‖harmonicRamareBilinear P (Finset.Icc A₀ B₀) w‖ ^ 2)
      ≤ harmonicPrimeMass P * ∑ j ∈ menonHarmonicActiveBlocks P Q eta L,
            min (menonHarmonicAllSmallBlockCost P A₀ B₀ Q eta W (V j)
                  (menonHarmonicAllBlocksSmall P Q eta L V W) j)
              (menonHarmonicSwappedBlockCost P A₀ B₀ Q eta W
                (menonHarmonicAllBlocksSmall P Q eta L V W) j)
              / harmonicPrimeMass (geomBlock P Q (1 + eta) j)
        + harmonicPrimeMass P * ∑ j ∈ menonHarmonicActiveBlocks P Q eta L,
            menonHarmonicLevelTrivialBlockCost P A₀ B₀ Q eta W
                (∑ i ∈ Finset.range L, huxleyBlockMeasureBound (Nb i) (Ec i) (sigma i) W)
                k j (J j) (V₀ j)
              / harmonicPrimeMass (geomBlock P Q (1 + eta) j) :=
  integral_Icc_normSq_harmonicRamareBilinear_le_partition_blockMeasures k hk hA₀ hQ heta hW hL
    hPprime hPrange hleft hright htop V V₀ hV₀ J hJ
    (fun i => huxleyBlockMeasureBound (Nb i) (Ec i) (sigma i) W)
    (fun j hj => volume_real_menonHarmonicBlockLarge_le_huxley P hQ heta V j
      (hNb j hj) (hBsub j hj) (by linarith) (hEc j hj) (hmass j hj) (hthr j hj)
      (hlevel j hj))

end

end RHTower.Sieve
