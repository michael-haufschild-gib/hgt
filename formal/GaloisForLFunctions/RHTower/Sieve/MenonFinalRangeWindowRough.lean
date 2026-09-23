import GaloisForLFunctions.RHTower.Sieve.MenonFinalRangeWindowEstimate

/-!
# The rough half of the shell's window estimate, discharged

`MenonFinalRangeWindowEstimate` leaves the rough term as a frequency integral over the receiver's
own window `[-W,W]`.  The corpus's friable estimate is stated on the full interval `[-x,x]`, and
the integrand is nonnegative, so the receiver's window inherits it whenever `W ≤ x`.  With that the
rough half of the shell's window estimate is `o((log x)^{-8})` unconditionally, and the only free
inputs left are the schedule's scalars.
-/

namespace RHTower.Sieve

open Filter Finset MeasureTheory

noncomputable section

/-- The rough energy on a sub-window is at most the corpus's full-interval rough energy. -/
theorem integral_Icc_normSq_menonFinalRangeHarmonicRough_le_energy
    {x W : ℝ} (_hW : 0 ≤ W) (hWx : W ≤ x) :
    (∫ w in Set.Icc (-W) W,
      ‖logPoly harmonicMoebiusC (menonFinalRangeHarmonicRoughSet x) w‖ ^ (2 : ℕ))
      ≤ menonFinalRangeHarmonicRoughEnergy x := by
  classical
  have hcont : Continuous fun w : ℝ =>
      ‖logPoly harmonicMoebiusC (menonFinalRangeHarmonicRoughSet x) w‖ ^ (2 : ℕ) :=
    ((continuous_logPoly _ _).norm).pow 2
  have hsub : Set.Icc (-W) W ⊆ Set.Icc (-x) x := by
    intro w hw
    exact ⟨le_trans (by linarith) hw.1, le_trans hw.2 hWx⟩
  rw [menonFinalRangeHarmonicRoughEnergy]
  exact setIntegral_mono_set hcont.integrableOn_Icc
    (Filter.Eventually.of_forall fun w => by positivity) (LE.le.eventuallyLE hsub)

/-- **Menon's shell on a frequency window, with the rough half discharged.** -/
theorem integral_Icc_normSq_menonFinalRangeShell_le_threshold_rough
    {x Q eta W V I : ℝ} {L : ℕ} (k : ℕ) (hk : 1 ≤ k)
    (hx : 1 ≤ ⌈x⌉₊) (hQ : 0 < Q) (heta : 0 ≤ eta) (hW : 1 ≤ W) (hWx : W ≤ x)
    (hL : 1 ≤ L) (hV : 0 < V)
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
        + 2 * menonFinalRangeHarmonicRoughEnergy x := by
  have hbase := integral_Icc_normSq_menonFinalRangeShell_le_threshold_chebyshev
    (x := x) (Q := Q) (eta := eta) (W := W) (V := V) (I := I) (L := L)
    k hk hx hQ heta hW hL hV hPrange hmass hleft V₀ hV₀ J hJ hI
  have hrough := integral_Icc_normSq_menonFinalRangeHarmonicRough_le_energy
    (x := x) (W := W) (by linarith) hWx
  have htwice := mul_le_mul_of_nonneg_left hrough (show (0 : ℝ) ≤ 2 by norm_num)
  exact hbase.trans (add_le_add le_rfl htwice)

end

end RHTower.Sieve
