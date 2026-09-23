import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicRamareLadderLevelSplit

/-!
# Every level of the harmonic level split, received by reciprocal Halasz--Montgomery

`MenonHarmonicBlockLevelSplit` reduces one harmonic block product to a base term plus one term per
dyadic level, each carrying the cofactor's mean square over that level's own set.  This file pays
each of those cofactor mean squares by the corpus's reciprocal Halasz--Montgomery receiver, so the
only thing left undetermined on every level is the **measure of its level set** — which is exactly
what a large-values estimate supplies.

No hypothesis is added: the level sets are measurable because the harmonic prime block polynomial
is continuous, and they sit inside the ambient window because the ambient set does.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- The level sets of a harmonic prime block, inside a measurable ambient set. -/
def harmonicBlockLevelSet (B : Finset ℕ) (E : Set ℝ) (V : ℝ) : Set ℝ :=
  E ∩ {w | V ≤ ‖harmonicPrimeBlockPoly B w‖}

theorem measurableSet_harmonicBlockLevelSet {B : Finset ℕ} {E : Set ℝ}
    (hEm : MeasurableSet E) (V : ℝ) :
    MeasurableSet (harmonicBlockLevelSet B E V) :=
  hEm.inter (measurableSet_le measurable_const (measurable_norm_harmonicPrimeBlockPoly B))

theorem harmonicBlockLevelSet_subset {B : Finset ℕ} {E : Set ℝ} {W V : ℝ}
    (hEs : E ⊆ Set.Icc (-W) W) :
    harmonicBlockLevelSet B E V ⊆ Set.Icc (-W) W :=
  (Set.inter_subset_left).trans hEs

/-- **One harmonic block product, level split, with every level received by reciprocal
Halasz--Montgomery.**  The only free scalar on each level is the measure of that level set. -/
theorem setIntegral_normSq_harmonicBlockProduct_levelSplit_HM
    (P : Finset ℕ) {B D : Finset ℕ} {L' N : ℕ} (hBprime : ∀ p ∈ B, p.Prime)
    (hL' : 1 ≤ L') (hN : 1 ≤ N) (hD : D ⊆ Finset.Icc L' N)
    {W : ℝ} (hW : 1 ≤ W) {E : Set ℝ} (hEm : MeasurableSet E) (hEs : E ⊆ Set.Icc (-W) W)
    {V₀ : ℝ} (hV₀ : 0 < V₀) {J : ℕ} (hJ : harmonicPrimeMass B ≤ 2 ^ J * V₀) :
    (∫ w in E,
      ‖harmonicPrimeBlockPoly B w * logPoly (harmonicRamareCofactorCoeff P) D w‖ ^ (2 : ℕ))
      ≤ V₀ ^ (2 : ℕ) * ((2 * Real.pi)⁻¹ *
            (hmMassRecip N (2 * Real.pi * W) (2 * Real.pi * volume.real E)
              * ((1 / (L' : ℝ)) ^ (2 : ℕ) * (D.card : ℝ))))
        + ∑ i ∈ Finset.range J,
            (2 ^ (i + 1) * V₀) ^ (2 : ℕ) * ((2 * Real.pi)⁻¹ *
              (hmMassRecip N (2 * Real.pi * W)
                  (2 * Real.pi *
                    volume.real (harmonicBlockLevelSet B E (2 ^ i * V₀)))
                * ((1 / (L' : ℝ)) ^ (2 : ℕ) * (D.card : ℝ)))) := by
  classical
  have hbase := setIntegral_normSq_harmonicBlockProduct_levelSplit
    (harmonicRamareCofactorCoeff P) D hBprime hEm hEs hV₀ hJ
  have hHM0 := setIntegral_normSq_harmonicRamareCofactor_le_HM_recip
    P D hL' hN hD hEm hW hEs
  have hHMi : ∀ i ∈ Finset.range J,
      (∫ w in harmonicBlockLevelSet B E (2 ^ i * V₀),
        ‖logPoly (harmonicRamareCofactorCoeff P) D w‖ ^ (2 : ℕ))
        ≤ (2 * Real.pi)⁻¹ *
            (hmMassRecip N (2 * Real.pi * W)
                (2 * Real.pi * volume.real (harmonicBlockLevelSet B E (2 ^ i * V₀)))
              * ((1 / (L' : ℝ)) ^ (2 : ℕ) * (D.card : ℝ))) := by
    intro i _
    exact setIntegral_normSq_harmonicRamareCofactor_le_HM_recip
      P D hL' hN hD (measurableSet_harmonicBlockLevelSet hEm _) hW
      (harmonicBlockLevelSet_subset hEs)
  refine hbase.trans (add_le_add ?_ ?_)
  · exact mul_le_mul_of_nonneg_left hHM0 (by positivity)
  · refine Finset.sum_le_sum fun i hi => ?_
    exact mul_le_mul_of_nonneg_left (hHMi i hi) (by positivity)

end

end RHTower.Sieve
