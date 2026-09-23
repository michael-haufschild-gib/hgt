import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicSomeLargeUnionBudget

/-!
# The partition estimate closed by the moment method

`MenonHarmonicSomeLargeUnionBudget` reduced the window estimate to a family of per-block
large-value measures.  The corpus already owns one such family unconditionally — the moment method
at the block's own upper endpoint,
`Sieve/MenonHarmonicFrequencyMoment.volume_menonHarmonicBlockLarge_pow_le_local`.

Substituting it closes the chain: the resulting window estimate has **no free measure and no
external input**, only the schedule's thresholds and moment order.  It is not sharp enough for the
`(log x)^{-2}` rate the cards need — the moment method is weak on narrow blocks — but it is the
complete assembly, and any stronger per-block input drops into the same slot.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- **The moment method as a per-block measure bound.** -/
theorem volume_real_menonHarmonicBlockLarge_le_moment
    (k : ℕ) (hk : 1 ≤ k) {P : Finset ℕ} {Q eta W : ℝ} (V : ℕ → ℝ) (j : ℕ)
    (hPprime : ∀ p ∈ P, p.Prime) (hQ : 0 < Q) (heta : 0 ≤ eta) (hW : 0 ≤ W)
    (hV : 0 < V j) :
    volume.real (menonHarmonicBlockLarge P Q eta V W j)
      ≤ menonHarmonicLocalBlockMomentCost k Q eta W j / (V j) ^ (2 * k) := by
  have hbase := volume_menonHarmonicBlockLarge_pow_le_local k hk (P := P) (Q := Q)
    (eta := eta) (V := V j) (W := W) j hPprime hQ heta hW hV.le
  have hset : menonHarmonicBlockLarge P Q eta (fun _ => V j) W j
      = menonHarmonicBlockLarge P Q eta V W j := rfl
  rw [hset] at hbase
  have hVpow : (0 : ℝ) < (V j) ^ (2 * k) := by positivity
  rw [le_div_iff₀ hVpow]
  calc volume.real (menonHarmonicBlockLarge P Q eta V W j) * (V j) ^ (2 * k)
      = (V j) ^ (2 * k) * volume.real (menonHarmonicBlockLarge P Q eta V W j) := by ring
    _ ≤ menonHarmonicLocalBlockMomentCost k Q eta W j := hbase

/-- **The complete window estimate, closed by the moment method.**  No free measure and no external
analytic input remains: only the schedule's thresholds `V j`, base levels `V₀ j`, level counts
`J j` and moment order `k`. -/
theorem integral_Icc_normSq_harmonicRamareBilinear_le_partition_moment_closed
    {P : Finset ℕ} {A₀ B₀ L : ℕ} {Q eta W : ℝ} (k : ℕ) (hk : 1 ≤ k)
    (hA₀ : 1 ≤ A₀) (hQ : 0 < Q) (heta : 0 ≤ eta) (hW : 1 ≤ W) (hL : 1 ≤ L)
    (hPprime : ∀ p ∈ P, p.Prime)
    (hPrange : ∀ p ∈ P, Q < (p : ℝ) ∧ (p : ℝ) ≤ Q * (1 + eta) ^ L)
    (hleft : ∀ j ∈ Finset.range L,
      1 ≤ ⌈(A₀ : ℝ) / ((Q * (1 + eta) ^ j) * (1 + eta))⌉₊)
    (hright : ∀ j ∈ Finset.range L,
      1 ≤ ⌊(B₀ : ℝ) / (Q * (1 + eta) ^ j)⌋₊)
    (htop : ∀ j ∈ Finset.range L, 1 ≤ ⌊Q * (1 + eta) ^ (j + 1)⌋₊)
    (V : ℕ → ℝ) (hV : ∀ j ∈ Finset.range L, 0 < V j)
    (V₀ : ℕ → ℝ) (hV₀ : ∀ j ∈ Finset.range L, 0 < V₀ j)
    (J : ℕ → ℕ)
    (hJ : ∀ j ∈ Finset.range L,
      harmonicPrimeMass (geomBlock P Q (1 + eta) j) ≤ 2 ^ (J j) * V₀ j) :
    (∫ w in Set.Icc (-W) W, ‖harmonicRamareBilinear P (Finset.Icc A₀ B₀) w‖ ^ (2 : ℕ))
      ≤ harmonicPrimeMass P * ∑ j ∈ menonHarmonicActiveBlocks P Q eta L,
            min (menonHarmonicAllSmallBlockCost P A₀ B₀ Q eta W (V j)
                  (menonHarmonicAllBlocksSmall P Q eta L V W) j)
              (menonHarmonicSwappedBlockCost P A₀ B₀ Q eta W
                (menonHarmonicAllBlocksSmall P Q eta L V W) j)
              / harmonicPrimeMass (geomBlock P Q (1 + eta) j)
        + harmonicPrimeMass P * ∑ j ∈ menonHarmonicActiveBlocks P Q eta L,
            menonHarmonicLevelTrivialBlockCost P A₀ B₀ Q eta W
                (∑ i ∈ Finset.range L,
                  menonHarmonicLocalBlockMomentCost k Q eta W i / (V i) ^ (2 * k))
                k j (J j) (V₀ j)
              / harmonicPrimeMass (geomBlock P Q (1 + eta) j) :=
  integral_Icc_normSq_harmonicRamareBilinear_le_partition_blockMeasures k hk hA₀ hQ heta hW hL
    hPprime hPrange hleft hright htop V V₀ hV₀ J hJ
    (fun i => menonHarmonicLocalBlockMomentCost k Q eta W i / (V i) ^ (2 * k))
    (fun j hj => volume_real_menonHarmonicBlockLarge_le_moment k hk V j hPprime hQ heta
      (by linarith) (hV j hj))

end

end RHTower.Sieve
