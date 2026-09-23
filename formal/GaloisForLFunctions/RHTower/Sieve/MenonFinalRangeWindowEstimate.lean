import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicWindowChebyshev

/-!
# The complete window estimate for Menon's literal final-range harmonic shell

The exact Ramare factorisation of the shell is bilinear plus rough.  The bilinear half now has the
`L²`--`L^∞` window estimate of `MenonHarmonicWindowChebyshev`; the rough half is the corpus's own
friable energy, already known to be `o((log x)^{-8})`.  This file joins them, so that the whole
shell's frequency integral is bounded with only the schedule's scalars and the rough energy left
free.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- **Menon's literal shell on a frequency window: threshold, ladder, and rough energy.** -/
theorem integral_Icc_normSq_menonFinalRangeShell_le_threshold_chebyshev
    {x Q eta W V I : ℝ} {L : ℕ} (k : ℕ) (hk : 1 ≤ k)
    (hx : 1 ≤ ⌈x⌉₊) (hQ : 0 < Q) (heta : 0 ≤ eta) (hW : 1 ≤ W) (hL : 1 ≤ L) (hV : 0 < V)
    (hPrange : ∀ p ∈ menonFinalRangePrimes x,
      Q < (p : ℝ) ∧ (p : ℝ) ≤ Q * (1 + eta) ^ L)
    (hmass : ∀ j ∈ Finset.range L,
      0 < harmonicPrimeMass (geomBlock (menonFinalRangePrimes x) Q (1 + eta) j))
    (hleft : ∀ j ∈ Finset.range L,
      1 ≤ ⌈(⌈x⌉₊ : ℝ) / ((Q * (1 + eta) ^ j) * (1 + eta))⌉₊)
    (V₀ : ℕ → ℝ) (hV₀ : ∀ j ∈ Finset.range L, 0 < V₀ j)
    (J : ℕ → ℕ)
    (hJ : ∀ j ∈ Finset.range L,
      harmonicPrimeMass (geomBlock (menonFinalRangePrimes x) Q (1 + eta) j)
        ≤ 2 ^ (J j) * V₀ j)
    (hI : (∫ w in Set.Icc (-W) W,
      ‖harmonicRamareBilinear (menonFinalRangePrimes x) (menonFinalRangeShell x) w‖ ^ (2 : ℕ)) ≤ I) :
    (∫ w in Set.Icc (-W) W,
      ‖logPoly harmonicMoebiusC (menonFinalRangeShell x) w‖ ^ (2 : ℕ))
      ≤ 2 * (V ^ (2 : ℕ) * (2 * W)
          + harmonicPrimeMass (menonFinalRangePrimes x) * ∑ j ∈ Finset.range L,
              menonHarmonicLevelTrivialBlockCost (menonFinalRangePrimes x) ⌈x⌉₊
                  (menonFinalRangeTopNat x) Q eta W (I / V ^ (2 : ℕ)) k j (J j) (V₀ j)
                / harmonicPrimeMass (geomBlock (menonFinalRangePrimes x) Q (1 + eta) j))
        + 2 * ∫ w in Set.Icc (-W) W,
            ‖logPoly harmonicMoebiusC (menonFinalRangeHarmonicRoughSet x) w‖ ^ (2 : ℕ) := by
  classical
  have hbil := integral_Icc_normSq_harmonicRamareBilinear_le_threshold_chebyshev
    (P := menonFinalRangePrimes x) (A₀ := ⌈x⌉₊) (B₀ := menonFinalRangeTopNat x) (L := L)
    (Q := Q) (eta := eta) (W := W) (V := V) (I := I) k hk hx hQ heta hW hL hV
    (fun p hp => menonFinalRangePrimes_prime x hp) hPrange hmass hleft V₀ hV₀ J hJ hI
  have hsplit := setIntegral_normSq_add_le
    (F := fun w => harmonicRamareBilinear (menonFinalRangePrimes x)
      (menonFinalRangeShell x) w)
    (G := fun w => logPoly harmonicMoebiusC (menonFinalRangeHarmonicRoughSet x) w)
    (E := Set.Icc (-W) W) (W := W)
    (continuous_harmonicRamareBilinear _ _)
    (continuous_logPoly _ _) measurableSet_Icc (le_refl _)
  have hsum : (∫ w in Set.Icc (-W) W,
      ‖logPoly harmonicMoebiusC (menonFinalRangeShell x) w‖ ^ (2 : ℕ))
      ≤ 2 * (∫ w in Set.Icc (-W) W,
          ‖harmonicRamareBilinear (menonFinalRangePrimes x)
            (menonFinalRangeShell x) w‖ ^ (2 : ℕ))
        + 2 * ∫ w in Set.Icc (-W) W,
            ‖logPoly harmonicMoebiusC (menonFinalRangeHarmonicRoughSet x) w‖ ^ (2 : ℕ) := by
    simpa only [logPoly_harmonicMoebius_eq_menonFinalRange_ramare_add_rough,
      menonFinalRangeHarmonicRoughSet] using hsplit
  have htwice := mul_le_mul_of_nonneg_left hbil (show (0 : ℝ) ≤ 2 by norm_num)
  exact hsum.trans (add_le_add htwice le_rfl)

end

end RHTower.Sieve
