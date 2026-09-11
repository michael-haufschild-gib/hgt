import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicWindowThresholdSplit

/-!
# Menon's window estimate: threshold outside, ladder on the exceptional set

The two halves of the `L²`--`L^∞` argument, joined.  Below the threshold the window contributes
`V²` times its length; above it, the exceptional set carries the harmonic Ramare ladder, split at
the blocks' own masses and with every dyadic level measured by the moment method.

The only quantities a schedule still has to supply are the threshold `V`, the base levels `V₀ j`,
the level counts `J j`, the moment order `k`, and a bound for the measure of the exceptional set.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

theorem continuous_harmonicRamareBilinear (P s : Finset ℕ) :
    Continuous fun w : ℝ => harmonicRamareBilinear P s w := by
  refine continuous_finsetSum P fun p _ => ?_
  exact ((continuous_moebiusPhase p).div_const _).mul (continuous_logPoly _ _)

/-- **The complete window estimate for the harmonic Ramare bilinear form.** -/
theorem integral_Icc_normSq_harmonicRamareBilinear_le_threshold_levelTrivial
    {P : Finset ℕ} {A₀ B₀ L : ℕ} {Q eta W V : ℝ} (k : ℕ) (hk : 1 ≤ k)
    (hA₀ : 1 ≤ A₀) (hQ : 0 < Q) (heta : 0 ≤ eta) (hW : 1 ≤ W) (hL : 1 ≤ L)
    (hPprime : ∀ p ∈ P, p.Prime)
    (hPrange : ∀ p ∈ P, Q < (p : ℝ) ∧ (p : ℝ) ≤ Q * (1 + eta) ^ L)
    (hmass : ∀ j ∈ Finset.range L,
      0 < harmonicPrimeMass (geomBlock P Q (1 + eta) j))
    (hleft : ∀ j ∈ Finset.range L,
      1 ≤ ⌈(A₀ : ℝ) / ((Q * (1 + eta) ^ j) * (1 + eta))⌉₊)
    (V₀ : ℕ → ℝ) (hV₀ : ∀ j ∈ Finset.range L, 0 < V₀ j)
    (J : ℕ → ℕ)
    (hJ : ∀ j ∈ Finset.range L,
      harmonicPrimeMass (geomBlock P Q (1 + eta) j) ≤ 2 ^ (J j) * V₀ j) :
    (∫ w in Set.Icc (-W) W, ‖harmonicRamareBilinear P (Finset.Icc A₀ B₀) w‖ ^ 2)
      ≤ V ^ 2 * (2 * W)
        + harmonicPrimeMass P * ∑ j ∈ Finset.range L,
            menonHarmonicLevelTrivialBlockCost P A₀ B₀ Q eta W
                (volume.real
                  (windowSuperLevel (harmonicRamareBilinear P (Finset.Icc A₀ B₀)) W V))
                k j (J j) (V₀ j)
              / harmonicPrimeMass (geomBlock P Q (1 + eta) j) := by
  classical
  have hcont := continuous_harmonicRamareBilinear P (Finset.Icc A₀ B₀)
  have hsplit := integral_Icc_normSq_le_threshold_add_superLevel (F :=
    fun w => harmonicRamareBilinear P (Finset.Icc A₀ B₀) w) hcont (V := V)
    (by linarith : (0 : ℝ) ≤ W)
  refine hsplit.trans (add_le_add le_rfl ?_)
  exact setIntegral_normSq_harmonicRamareBilinear_le_levelTrivial_mass k hk hA₀ hQ heta hW hL
    hPprime hPrange hmass hleft V₀ hV₀ J hJ
    (measurableSet_windowSuperLevel hcont W V) (windowSuperLevel_subset _ W V)

end

end RHTower.Sieve
