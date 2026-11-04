import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.ReceivingCharges.UpwardProfileOffsets
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheUpwardPrimeRowsRealizeTheCompletedShellCorrection

/-!
# Square-root normalization of literal upward profile rows

The finite offset identity becomes a reciprocal Mangoldt sum with the exact
logarithmic autocorrelation kernel. Both horizon cutoffs remain explicit,
and the integer strip has width linear in overlap.
-/

noncomputable section
open MeasureTheory Finset

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open RenormalizedArithmeticPotentialTheory SpacingScaleHarmonicAnalysis ArithmeticElectrostatics
  BezoutValuationIncidence RenormalizedArithmeticPotentialTheory.CompletedShell

/-- The square-root normalization is linear in the sampled arithmetic value. -/
theorem sqrt_mul_upward_profile_offset_factor {φ : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    {N k n j : ℕ} (hN : 1 ≤ N) (hk : 1 ≤ k) (hn : 1 ≤ n) (hj : 1 ≤ j) (x : ℝ) :
    Real.sqrt n * (_root_.RHTower.vonMangoldtAtom k *
      (x / Real.sqrt j * bumpCorr (atomDilate φ (c / N))
        (Real.log (k * n : ℕ) - Real.log j)) / (∫ u, atomDilate φ (c / N) u ^ 2)) =
      1 / (∫ u, φ u ^ 2) * ((ArithmeticFunction.vonMangoldt k : ℝ) / k *
        x * logarithmicUpwardKernel φ c N (k * n) j) := by
  have h := sqrt_mul_upward_offset_factor (φ := φ) hc hN hk hn hj 1
  have hone : ramanujanLagCoefficient 1 j = 1 := by
    simp [ramanujanLagCoefficient, moebiusReal]
  rw [hone] at h
  calc
    _ = x * (Real.sqrt n * (_root_.RHTower.vonMangoldtAtom k *
        (1 / Real.sqrt j * bumpCorr (atomDilate φ (c / N))
          (Real.log (k * n : ℕ) - Real.log j)) / (∫ u, atomDilate φ (c / N) u ^ 2))) := by ring
    _ = _ := by rw [h]; ring

/-- Both logarithmic offsets of one prime power, with their actual cutoffs. -/
def logarithmicUpwardProfileOffset (φ : ℝ → ℝ) (c : ℝ) (N : ℕ) (F : ℕ → ℝ) (n k h : ℕ) : ℝ :=
  (if k * n + h ≤ N then F (k * n + h) *
    logarithmicUpwardKernel φ c N (k * n) (k * n + h) else 0) +
  (if h < k * n ∧ k * n - h ≤ N then F (k * n - h) *
    logarithmicUpwardKernel φ c N (k * n) (k * n - h) else 0)

/-- The finite logarithmic source after square-root normalization of the arithmetic profile. -/
def logarithmicUpwardProfileCoefficient (φ : ℝ → ℝ) (c : ℝ) (B N : ℕ) (F : ℕ → ℝ) (n : ℕ) : ℝ :=
  1 / (∫ u, φ u ^ 2) * ∑ k ∈ Icc 1 (N + B), (ArithmeticFunction.vonMangoldt k : ℝ) / k *
    ∑ h ∈ Icc 1 B, logarithmicUpwardProfileOffset φ c N F n k h

/-- Exact finite-source normalization of the literal upward arithmetic row. -/
theorem sqrt_mul_upwardProfileRow_eq_logarithmicCoefficient {φ : ℝ → ℝ}
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) {c : ℝ} (hc : 0 < c)
    {N n : ℕ} (hn : n ∈ Icc 1 N) (hwidth : c / N ≤ 1) (F : ℕ → ℝ) :
    Real.sqrt n * (upwardPrimeRow (atomDilate φ (c / N)) N
      (fun j => F j / Real.sqrt j) n /
        (∫ u, atomDilate φ (c / N) u ^ 2)) =
      logarithmicUpwardProfileCoefficient φ c (linearPrimeStrip c) N F n := by
  have hN : 1 ≤ N := (mem_Icc.mp hn).1.trans (mem_Icc.mp hn).2
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hg : ∀ u, u ∉ Set.Icc 0 (c / N) → atomDilate φ (c / N) u = 0 := by
    intro u hu
    change φ (u / (c / N)) = 0
    apply hsupp
    intro hv
    apply hu
    refine ⟨?_, ?_⟩
    · simpa only [zero_mul] using (le_div_iff₀ (div_pos hc hN0)).mp hv.1
    · simpa only [one_mul] using (div_le_iff₀ (div_pos hc hN0)).mp hv.2
  have hterm (k : ℕ) (hk : k ∈ Icc 1 (N + linearPrimeStrip c)) (h : ℕ)
      (hh : h ∈ Icc 1 (linearPrimeStrip c)) :
      Real.sqrt n * (_root_.RHTower.vonMangoldtAtom k *
        (positiveUpwardProfileOffset (atomDilate φ (c / N)) N F n k h +
          negativeUpwardProfileOffset (atomDilate φ (c / N)) N F n k h) /
          (∫ u, atomDilate φ (c / N) u ^ 2)) =
      1 / (∫ u, φ u ^ 2) * ((ArithmeticFunction.vonMangoldt k : ℝ) / k *
        logarithmicUpwardProfileOffset φ c N F n k h) := by
    have hk1 := (mem_Icc.mp hk).1
    have hn1 := (mem_Icc.mp hn).1
    have hh1 := (mem_Icc.mp hh).1
    have hp : Real.sqrt n * (_root_.RHTower.vonMangoldtAtom k *
        positiveUpwardProfileOffset (atomDilate φ (c / N)) N F n k h /
          (∫ u, atomDilate φ (c / N) u ^ 2)) =
        1 / (∫ u, φ u ^ 2) * ((ArithmeticFunction.vonMangoldt k : ℝ) / k *
          (if k * n + h ≤ N then F (k * n + h) *
            logarithmicUpwardKernel φ c N (k * n) (k * n + h) else 0)) := by
      dsimp only [positiveUpwardProfileOffset]
      split_ifs
      · simpa only [mul_assoc] using sqrt_mul_upward_profile_offset_factor hc hN hk1 hn1
          (show 1 ≤ k * n + h by omega) (F (k * n + h))
      · simp only [mul_zero, zero_div]
    have hm : Real.sqrt n * (_root_.RHTower.vonMangoldtAtom k *
        negativeUpwardProfileOffset (atomDilate φ (c / N)) N F n k h /
          (∫ u, atomDilate φ (c / N) u ^ 2)) =
        1 / (∫ u, φ u ^ 2) * ((ArithmeticFunction.vonMangoldt k : ℝ) / k *
          (if h < k * n ∧ k * n - h ≤ N then F (k * n - h) *
            logarithmicUpwardKernel φ c N (k * n) (k * n - h) else 0)) := by
      dsimp only [negativeUpwardProfileOffset]
      split_ifs with hhT
      · simpa only [mul_assoc] using sqrt_mul_upward_profile_offset_factor hc hN hk1 hn1
          (show 1 ≤ k * n - h by omega) (F (k * n - h))
      · simp only [mul_zero, zero_div]
    dsimp only [logarithmicUpwardProfileOffset]
    linear_combination hp + hm
  rw [upwardProfileRow_eq_offsets_small_width hc hn hg hwidth F, logarithmicUpwardProfileCoefficient]
  simp only [sum_div, mul_sum]
  exact sum_congr rfl fun k hk => sum_congr rfl fun h hh => hterm k hk h hh


#print axioms sqrt_mul_upwardProfileRow_eq_logarithmicCoefficient

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
