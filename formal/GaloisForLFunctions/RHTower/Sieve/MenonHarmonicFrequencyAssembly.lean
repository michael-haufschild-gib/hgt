import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicSomeLargeBound
import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicRoughMeanSquare

/-!
# Menon's harmonic full-frequency assembly

The all-small and some-large estimates are assembled across their exact measurable partition.
The resulting bilinear bound is then inserted into the literal harmonic Ramaré identity, retaining
the complete rough remainder rather than suppressing it.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- Exact full-frequency assembly of the harmonic all-small and some-large Ramaré bounds. -/
theorem integral_Icc_normSq_harmonicRamareBilinear_le_frequencyPartition
    {P : Finset ℕ} {A₀ B₀ L : ℕ} {Q eta W : ℝ}
    (hA₀ : 1 ≤ A₀) (hQ : 0 < Q) (heta : 0 ≤ eta) (hW : 1 ≤ W) (hL : 1 ≤ L)
    (hPprime : ∀ p ∈ P, p.Prime)
    (hPrange : ∀ p ∈ P, Q < (p : ℝ) ∧ (p : ℝ) ≤ Q * (1 + eta) ^ L)
    (V : ℕ → ℝ)
    (hleft : ∀ j ∈ Finset.range L,
      1 ≤ ⌈(A₀ : ℝ) / ((Q * (1 + eta) ^ j) * (1 + eta))⌉₊)
    (hright : ∀ j ∈ Finset.range L,
      1 ≤ ⌊(B₀ : ℝ) / (Q * (1 + eta) ^ j)⌋₊) :
    (∫ w in Set.Icc (-W) W,
      ‖harmonicRamareBilinear P (Finset.Icc A₀ B₀) w‖ ^ 2)
      ≤ (L : ℝ) * ∑ j ∈ Finset.range L,
          menonHarmonicAllSmallBlockCost P A₀ B₀ Q eta W (V j)
            (menonHarmonicAllBlocksSmall P Q eta L V W) j
        + (L : ℝ) * ∑ j ∈ Finset.range L,
          menonHarmonicAllSmallBlockCost P A₀ B₀ Q eta W
            (harmonicPrimeMass (geomBlock P Q (1 + eta) j))
            (menonHarmonicSomeBlockLarge P Q eta L V W) j := by
  let f : ℝ → ℝ := fun w =>
    ‖harmonicRamareBilinear P (Finset.Icc A₀ B₀) w‖ ^ 2
  have hfcont : Continuous f := by
    dsimp only [f]
    refine (continuous_finsetSum P fun p _ => ?_).norm.pow 2
    exact ((continuous_moebiusPhase p).div_const _).mul (continuous_logPoly _ _)
  have hsplit := setIntegral_menonHarmonic_frequencyPartition
    P Q eta L V W f hfcont.integrableOn_Icc
  have hsmall := setIntegral_normSq_harmonicRamareBilinear_le_allSmall
    hA₀ hQ heta hW hL hPprime hPrange V hleft hright
  have hlarge := setIntegral_normSq_harmonicRamareBilinear_le_someLarge
    hA₀ hQ heta hW hL hPprime hPrange V hleft hright
  calc
    (∫ w in Set.Icc (-W) W,
        ‖harmonicRamareBilinear P (Finset.Icc A₀ B₀) w‖ ^ 2) =
        (∫ w in menonHarmonicAllBlocksSmall P Q eta L V W,
          ‖harmonicRamareBilinear P (Finset.Icc A₀ B₀) w‖ ^ 2) +
        ∫ w in menonHarmonicSomeBlockLarge P Q eta L V W,
          ‖harmonicRamareBilinear P (Finset.Icc A₀ B₀) w‖ ^ 2 := by
            simpa only [f] using hsplit
    _ ≤ _ := add_le_add hsmall hlarge

/-- The literal Menon harmonic shell is bounded by the assembled Ramaré frequency partition plus
the exact rough energy. -/
theorem integral_Icc_normSq_menonFinalRangeShell_le_frequencyPartition
    {x Q eta : ℝ} {L : ℕ} (hx : 1 ≤ x) (hQ : 0 < Q) (heta : 0 ≤ eta) (hL : 1 ≤ L)
    (hPrange : ∀ p ∈ menonFinalRangePrimes x,
      Q < (p : ℝ) ∧ (p : ℝ) ≤ Q * (1 + eta) ^ L)
    (V : ℕ → ℝ)
    (hleft : ∀ j ∈ Finset.range L,
      1 ≤ ⌈x / ((Q * (1 + eta) ^ j) * (1 + eta))⌉₊)
    (hright : ∀ j ∈ Finset.range L,
      1 ≤ ⌊(menonFinalRangeTopNat x : ℝ) / (Q * (1 + eta) ^ j)⌋₊) :
    (∫ w in Set.Icc (-x) x,
      ‖logPoly harmonicMoebiusC (menonFinalRangeShell x) w‖ ^ 2)
      ≤ 2 * ((L : ℝ) * ∑ j ∈ Finset.range L,
          menonHarmonicAllSmallBlockCost (menonFinalRangePrimes x) ⌈x⌉₊
            (menonFinalRangeTopNat x) Q eta x (V j)
            (menonHarmonicAllBlocksSmall (menonFinalRangePrimes x) Q eta L V x) j
        + (L : ℝ) * ∑ j ∈ Finset.range L,
          menonHarmonicAllSmallBlockCost (menonFinalRangePrimes x) ⌈x⌉₊
            (menonFinalRangeTopNat x) Q eta x
            (harmonicPrimeMass
              (geomBlock (menonFinalRangePrimes x) Q (1 + eta) j))
            (menonHarmonicSomeBlockLarge (menonFinalRangePrimes x) Q eta L V x) j)
        + 2 * menonFinalRangeHarmonicRoughEnergy x := by
  have hA₀ : 1 ≤ ⌈x⌉₊ := by
    exact_mod_cast hx.trans (Nat.le_ceil x)
  have hbil := integral_Icc_normSq_harmonicRamareBilinear_le_frequencyPartition
    (P := menonFinalRangePrimes x) (A₀ := ⌈x⌉₊) (B₀ := menonFinalRangeTopNat x)
    (L := L) (Q := Q) (eta := eta) (W := x)
    hA₀ hQ heta hx hL (fun p hp => menonFinalRangePrimes_prime x hp)
    hPrange V hleft hright
  have hsplit := setIntegral_normSq_add_le
    (F := fun w => harmonicRamareBilinear (menonFinalRangePrimes x)
      (menonFinalRangeShell x) w)
    (G := fun w => logPoly harmonicMoebiusC (menonFinalRangeHarmonicRoughSet x) w)
    (by
      refine continuous_finsetSum (menonFinalRangePrimes x) fun p _ => ?_
      exact ((continuous_moebiusPhase p).div_const _).mul (continuous_logPoly _ _))
    (continuous_logPoly _ _) measurableSet_Icc (fun _ hw => hw)
  have hshell : menonFinalRangeShell x =
      Finset.Icc ⌈x⌉₊ (menonFinalRangeTopNat x) := rfl
  rw [menonFinalRangeHarmonicRoughEnergy]
  calc
    (∫ w in Set.Icc (-x) x,
        ‖logPoly harmonicMoebiusC (menonFinalRangeShell x) w‖ ^ 2)
        ≤ 2 * (∫ w in Set.Icc (-x) x,
            ‖harmonicRamareBilinear (menonFinalRangePrimes x)
              (menonFinalRangeShell x) w‖ ^ 2)
          + 2 * ∫ w in Set.Icc (-x) x,
            ‖logPoly harmonicMoebiusC (menonFinalRangeHarmonicRoughSet x) w‖ ^ 2 := by
              simpa only [logPoly_harmonicMoebius_eq_menonFinalRange_ramare_add_rough,
                menonFinalRangeHarmonicRoughSet] using hsplit
    _ ≤ 2 * ((L : ℝ) * ∑ j ∈ Finset.range L,
          menonHarmonicAllSmallBlockCost (menonFinalRangePrimes x) ⌈x⌉₊
            (menonFinalRangeTopNat x) Q eta x (V j)
            (menonHarmonicAllBlocksSmall (menonFinalRangePrimes x) Q eta L V x) j
        + (L : ℝ) * ∑ j ∈ Finset.range L,
          menonHarmonicAllSmallBlockCost (menonFinalRangePrimes x) ⌈x⌉₊
            (menonFinalRangeTopNat x) Q eta x
            (harmonicPrimeMass
              (geomBlock (menonFinalRangePrimes x) Q (1 + eta) j))
            (menonHarmonicSomeBlockLarge (menonFinalRangePrimes x) Q eta L V x) j)
          + 2 * ∫ w in Set.Icc (-x) x,
            ‖logPoly harmonicMoebiusC (menonFinalRangeHarmonicRoughSet x) w‖ ^ 2 := by
              rw [hshell]
              exact add_le_add_right (mul_le_mul_of_nonneg_left hbil (by norm_num)) _

end

end RHTower.Sieve
