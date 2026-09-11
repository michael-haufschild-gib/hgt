import GaloisForLFunctions.RHTower.Sieve.MeanSquareLevelSplit
import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicSomeLargeBound
import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicRamareLadderMass

/-!
# The harmonic block product split by the level sets of its prime factor

`Sieve/BlockProductLevelSplit` performs the `L²`--`L^∞` dyadic level split for the *unweighted*
prime block polynomial, whose sup bound is the block's cardinality.  Menon's argument runs in the
harmonic normalisation, where the sup bound is the block's harmonic mass `∑_{p ∈ B} 1/p`, and the
level split is the interface the large-values estimates plug into: the ambient half is paid by the
base level `V₀`, and every dyadic level above it is paid by the *measure* of the set where the
prime factor is that large.

This file supplies the harmonic form, on an arbitrary measurable part of the frequency window, and
inserts it into the exact harmonic Ramare block.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

theorem measurable_norm_harmonicPrimeBlockPoly (B : Finset ℕ) :
    Measurable fun w : ℝ => ‖harmonicPrimeBlockPoly B w‖ :=
  (continuous_harmonicPrimeBlockPoly B).norm.measurable

/-- **One harmonic block product, split by the level sets of its prime factor.** -/
theorem setIntegral_normSq_harmonicBlockProduct_levelSplit
    (a : ℕ → ℂ) {B : Finset ℕ} (D : Finset ℕ) (hBprime : ∀ p ∈ B, p.Prime) {W : ℝ}
    {E : Set ℝ} (hEm : MeasurableSet E) (hEs : E ⊆ Set.Icc (-W) W)
    {V₀ : ℝ} (hV₀ : 0 < V₀) {J : ℕ} (hJ : harmonicPrimeMass B ≤ 2 ^ J * V₀) :
    (∫ w in E, ‖harmonicPrimeBlockPoly B w * logPoly a D w‖ ^ 2)
      ≤ V₀ ^ 2 * (∫ w in E, ‖logPoly a D w‖ ^ 2)
        + ∑ j ∈ Finset.range J,
            (2 ^ (j + 1) * V₀) ^ 2
              * ∫ w in E ∩ {w | 2 ^ j * V₀ ≤ ‖harmonicPrimeBlockPoly B w‖},
                  ‖logPoly a D w‖ ^ 2 := by
  classical
  have hcontP : Continuous fun w : ℝ => ‖harmonicPrimeBlockPoly B w‖ :=
    (continuous_harmonicPrimeBlockPoly B).norm
  have hcontC : Continuous fun w : ℝ => ‖logPoly a D w‖ ^ 2 :=
    ((continuous_logPoly a D).norm).pow 2
  have hrw : (∫ w in E, ‖harmonicPrimeBlockPoly B w * logPoly a D w‖ ^ 2)
      = ∫ w in E, ‖harmonicPrimeBlockPoly B w‖ ^ 2 * ‖logPoly a D w‖ ^ 2 := by
    refine MeasureTheory.setIntegral_congr_fun hEm fun w _ => ?_
    rw [norm_mul, mul_pow]
  rw [hrw]
  refine integral_sq_mul_le_levelSplit hEm hcontP.measurable
    ((((hcontP.pow 2).mul hcontC).integrableOn_Icc (a := -W) (b := W)).mono_set hEs)
    ((hcontC.integrableOn_Icc (a := -W) (b := W)).mono_set hEs)
    (fun w => norm_nonneg _) (fun w => by positivity) hV₀
    (fun w => norm_harmonicPrimeBlockPoly_le_mass hBprime w) hJ

/-- **The complete harmonic Ramare block on a level split.**  The prime factor is never bounded by
a supremum on the whole window; every dyadic level above the base is charged to the measure of its
own level set. -/
theorem setIntegral_normSq_harmonicRamareBlock_le_levelSplit
    {P s B : Finset ℕ} (C : Finset ℕ) (hBprime : ∀ p ∈ B, p.Prime) {W : ℝ}
    {E : Set ℝ} (hEm : MeasurableSet E) (hEs : E ⊆ Set.Icc (-W) W)
    {V₀ : ℝ} (hV₀ : 0 < V₀) {J : ℕ} (hJ : harmonicPrimeMass B ≤ 2 ^ J * V₀) :
    (∫ w in E, ‖harmonicRamareBlock P s B w‖ ^ 2)
      ≤ 2 * (V₀ ^ 2 *
            (∫ w in E, ‖logPoly (harmonicRamareCofactorCoeff P) C w‖ ^ 2)
          + ∑ j ∈ Finset.range J,
              (2 ^ (j + 1) * V₀) ^ 2
                * ∫ w in E ∩ {w | 2 ^ j * V₀ ≤ ‖harmonicPrimeBlockPoly B w‖},
                    ‖logPoly (harmonicRamareCofactorCoeff P) C w‖ ^ 2)
        + 2 * harmonicPrimeMass B * ∑ p ∈ B, (1 / (p : ℝ)) *
            (∫ w in E, ‖harmonicRamareCofactorPoly P s p w
              - logPoly (harmonicRamareCofactorCoeff P) C w‖ ^ 2) := by
  have hbase := setIntegral_normSq_harmonicRamareBlock_le_product
    (P := P) (s := s) (B := B) hBprime C hEm hEs
  have hsplit := setIntegral_normSq_harmonicBlockProduct_levelSplit
    (harmonicRamareCofactorCoeff P) C hBprime hEm hEs hV₀ hJ
  linarith

end

end RHTower.Sieve
