import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicWindowSymmetry
import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicWindowPartitionMassFilter

/-!
# The window estimate from a positive-ordinate exceptional count

Every Heath--Brown/Montgomery large-values receiver in `Sieve/MenonHeathBrown*` is stated for
positive ordinates.  By the reflection symmetry of the harmonic Ramare bilinear form its
exceptional set is symmetric, so a bound on the nonnegative half doubles to the whole window.

This file is the resulting interface: the complete window estimate, with the exceptional measure
supplied **only on `[0, W]`**.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- **The window estimate from a nonnegative-half exceptional bound.** -/
theorem integral_Icc_normSq_harmonicRamareBilinear_le_threshold_halfMeasure
    {P : Finset ℕ} {A₀ B₀ L : ℕ} {Q eta W V vol : ℝ} (k : ℕ) (hk : 1 ≤ k)
    (hA₀ : 1 ≤ A₀) (hQ : 0 < Q) (heta : 0 ≤ eta) (hW : 1 ≤ W) (hL : 1 ≤ L)
    (hPprime : ∀ p ∈ P, p.Prime)
    (hPrange : ∀ p ∈ P, Q < (p : ℝ) ∧ (p : ℝ) ≤ Q * (1 + eta) ^ L)
    (hleft : ∀ j ∈ Finset.range L,
      1 ≤ ⌈(A₀ : ℝ) / ((Q * (1 + eta) ^ j) * (1 + eta))⌉₊)
    (V₀ : ℕ → ℝ) (hV₀ : ∀ j ∈ Finset.range L, 0 < V₀ j)
    (J : ℕ → ℕ)
    (hJ : ∀ j ∈ Finset.range L,
      harmonicPrimeMass (geomBlock P Q (1 + eta) j) ≤ 2 ^ (J j) * V₀ j)
    (hhalf : volume.real
      (windowSuperLevel (harmonicRamareBilinear P (Finset.Icc A₀ B₀)) W V ∩ Set.Ici 0) ≤ vol) :
    (∫ w in Set.Icc (-W) W, ‖harmonicRamareBilinear P (Finset.Icc A₀ B₀) w‖ ^ (2 : ℕ))
      ≤ V ^ (2 : ℕ) * (2 * W)
        + harmonicPrimeMass P * ∑ j ∈ menonHarmonicActiveBlocks P Q eta L,
            menonHarmonicLevelTrivialBlockCost P A₀ B₀ Q eta W (2 * vol) k j (J j) (V₀ j)
              / harmonicPrimeMass (geomBlock P Q (1 + eta) j) := by
  classical
  have hcont : Continuous fun w : ℝ => harmonicRamareBilinear P (Finset.Icc A₀ B₀) w := by
    refine continuous_finsetSum _ fun p _ => ?_
    exact ((continuous_moebiusPhase p).div_const _).mul (continuous_logPoly _ _)
  have hsplit := integral_Icc_normSq_le_threshold_add_superLevel (F :=
    fun w => harmonicRamareBilinear P (Finset.Icc A₀ B₀) w) hcont (V := V)
    (by linarith : (0 : ℝ) ≤ W)
  have hsym := volume_windowSuperLevel_le_two_mul_nonneg hcont
    (fun w => norm_harmonicRamareBilinear_neg P (Finset.Icc A₀ B₀) w) W V
  have hbudget : volume.real
      (windowSuperLevel (harmonicRamareBilinear P (Finset.Icc A₀ B₀)) W V) ≤ 2 * vol :=
    hsym.trans (by linarith)
  have hlad := setIntegral_normSq_harmonicRamareBilinear_le_levelTrivial_mass_filter
    (B₀ := B₀) (vol := 2 * vol) k hk hA₀ hQ heta hW hL hPprime hPrange hleft V₀ hV₀ J hJ
    (measurableSet_windowSuperLevel hcont W V) (windowSuperLevel_subset _ W V) hbudget
  exact hsplit.trans (add_le_add le_rfl hlad)

end

end RHTower.Sieve
