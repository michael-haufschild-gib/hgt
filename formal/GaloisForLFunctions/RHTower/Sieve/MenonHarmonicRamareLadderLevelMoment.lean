import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicBlockLevelMoment

/-!
# Menon's ladder receiver with no free measure

The complete assembly of this session's corrections to the harmonic Ramare ladder:

* outside, the ladder is split at the blocks' own harmonic masses, so the split costs
  `∑_{p ∈ P} 1/p` rather than the number of blocks;
* inside each block the prime factor is split into dyadic levels rather than replaced by a
  supremum;
* every level's set is measured by the moment method at the block's own upper endpoint;
* every level's cofactor mean square is received by reciprocal Halasz--Montgomery;
* the moving-support discrepancy is the corpus's exact `harmonicCofactorSupportError`.

The result has no free measure and no analytic premise: the only parameters are the schedule's own
base levels `V₀ j`, level counts `J j` and moment order `k`.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- The per-block cost of the level-split/moment receiver. -/
def menonHarmonicLevelMomentBlockCost
    (P : Finset ℕ) (A₀ B₀ : ℕ) (Q eta W volE : ℝ) (k j J : ℕ) (V₀ : ℝ) : ℝ :=
  2 * (V₀ ^ 2 * ((2 * Real.pi)⁻¹ *
          (hmMassRecip ⌊(B₀ : ℝ) / (Q * (1 + eta) ^ j)⌋₊ (2 * Real.pi * W)
              (2 * Real.pi * volE)
            * ((1 / (⌈(A₀ : ℝ) / ((Q * (1 + eta) ^ j) * (1 + eta))⌉₊ : ℝ)) ^ 2
              * ((harmonicGeomCofactorBlock A₀ B₀ Q eta j).card : ℝ))))
        + ∑ i ∈ Finset.range J,
            (2 ^ (i + 1) * V₀) ^ 2 * ((2 * Real.pi)⁻¹ *
              (hmMassRecip ⌊(B₀ : ℝ) / (Q * (1 + eta) ^ j)⌋₊ (2 * Real.pi * W)
                  (2 * Real.pi * (menonHarmonicLocalBlockMomentCost k Q eta W j
                    / (2 ^ i * V₀) ^ (2 * k)))
                * ((1 / (⌈(A₀ : ℝ) / ((Q * (1 + eta) ^ j) * (1 + eta))⌉₊ : ℝ)) ^ 2
                  * ((harmonicGeomCofactorBlock A₀ B₀ Q eta j).card : ℝ)))))
    + 2 * harmonicPrimeMass (geomBlock P Q (1 + eta) j) ^ 2 *
        harmonicCofactorSupportError A₀ B₀ Q eta W j

/-- **One geometric block against the level-split/moment cost.** -/
theorem setIntegral_normSq_harmonicRamareBlock_geom_le_levelMoment
    {P : Finset ℕ} {A₀ B₀ : ℕ} {Q eta W : ℝ} (j k : ℕ) (hk : 1 ≤ k)
    (hA₀ : 1 ≤ A₀) (hQ : 0 < Q) (heta : 0 ≤ eta) (hW : 1 ≤ W)
    (hPprime : ∀ p ∈ P, p.Prime)
    (hleft : 1 ≤ ⌈(A₀ : ℝ) / ((Q * (1 + eta) ^ j) * (1 + eta))⌉₊)
    (hright : 1 ≤ ⌊(B₀ : ℝ) / (Q * (1 + eta) ^ j)⌋₊)
    {E : Set ℝ} (hEm : MeasurableSet E) (hEs : E ⊆ Set.Icc (-W) W)
    {V₀ : ℝ} (hV₀ : 0 < V₀) {J : ℕ}
    (hJ : harmonicPrimeMass (geomBlock P Q (1 + eta) j) ≤ 2 ^ J * V₀) :
    (∫ w in E,
      ‖harmonicRamareBlock P (Finset.Icc A₀ B₀)
        (geomBlock P Q (1 + eta) j) w‖ ^ 2)
      ≤ menonHarmonicLevelMomentBlockCost P A₀ B₀ Q eta W (volume.real E) k j J V₀ := by
  classical
  have hD : harmonicGeomCofactorBlock A₀ B₀ Q eta j ⊆
      Finset.Icc ⌈(A₀ : ℝ) / ((Q * (1 + eta) ^ j) * (1 + eta))⌉₊
        ⌊(B₀ : ℝ) / (Q * (1 + eta) ^ j)⌋₊ := by
    intro n hn
    simpa [harmonicGeomCofactorBlock] using hn
  have hprod := setIntegral_normSq_harmonicBlockProduct_levelSplit_moment
    P (D := harmonicGeomCofactorBlock A₀ B₀ Q eta j)
    (L' := ⌈(A₀ : ℝ) / ((Q * (1 + eta) ^ j) * (1 + eta))⌉₊)
    (N := ⌊(B₀ : ℝ) / (Q * (1 + eta) ^ j)⌋₊)
    j k hk hPprime hQ heta hleft hright hD hW hEm hEs hV₀ hJ
  have hblock := setIntegral_normSq_harmonicRamareBlock_geom_le
    (P := P) (A₀ := A₀) (B₀ := B₀) (Q := Q) (eta := eta) (W := W)
    hA₀ hQ heta hW j hPprime hleft hEm hEs
  rw [menonHarmonicLevelMomentBlockCost]
  linarith

/-- **The complete ladder: mass split outside, level split and moment measure inside.** -/
theorem setIntegral_normSq_harmonicRamareBilinear_le_levelMoment_mass
    {P : Finset ℕ} {A₀ B₀ L : ℕ} {Q eta W : ℝ} (k : ℕ) (hk : 1 ≤ k)
    (hA₀ : 1 ≤ A₀) (hQ : 0 < Q) (heta : 0 ≤ eta) (hW : 1 ≤ W) (hL : 1 ≤ L)
    (hPprime : ∀ p ∈ P, p.Prime)
    (hPrange : ∀ p ∈ P, Q < (p : ℝ) ∧ (p : ℝ) ≤ Q * (1 + eta) ^ L)
    (hmass : ∀ j ∈ Finset.range L,
      0 < harmonicPrimeMass (geomBlock P Q (1 + eta) j))
    (hleft : ∀ j ∈ Finset.range L,
      1 ≤ ⌈(A₀ : ℝ) / ((Q * (1 + eta) ^ j) * (1 + eta))⌉₊)
    (hright : ∀ j ∈ Finset.range L,
      1 ≤ ⌊(B₀ : ℝ) / (Q * (1 + eta) ^ j)⌋₊)
    (V₀ : ℕ → ℝ) (hV₀ : ∀ j ∈ Finset.range L, 0 < V₀ j)
    (J : ℕ → ℕ)
    (hJ : ∀ j ∈ Finset.range L,
      harmonicPrimeMass (geomBlock P Q (1 + eta) j) ≤ 2 ^ (J j) * V₀ j)
    {E : Set ℝ} (hEm : MeasurableSet E) (hEs : E ⊆ Set.Icc (-W) W) :
    (∫ w in E, ‖harmonicRamareBilinear P (Finset.Icc A₀ B₀) w‖ ^ 2)
      ≤ harmonicPrimeMass P * ∑ j ∈ Finset.range L,
          menonHarmonicLevelMomentBlockCost P A₀ B₀ Q eta W (volume.real E) k j (J j) (V₀ j)
            / harmonicPrimeMass (geomBlock P Q (1 + eta) j) := by
  classical
  have hr : 1 ≤ 1 + eta := by linarith
  have hsplit := setIntegral_normSq_harmonicRamareBilinear_le_blocks_mass
    (P := P) (s := Finset.Icc A₀ B₀) (W := W) hEm hEs
    (Finset.range L) (geomBlock P Q (1 + eta))
    (geomBlock_pairwiseDisjoint P hQ hr L)
    (geomBlock_biUnion_eq P Q (1 + eta) hL hPrange) hmass
  have hPmass : (0 : ℝ) ≤ harmonicPrimeMass P :=
    Finset.sum_nonneg fun p _ => by positivity
  refine hsplit.trans (mul_le_mul_of_nonneg_left ?_ hPmass)
  refine Finset.sum_le_sum fun j hj => ?_
  refine div_le_div_of_nonneg_right ?_ (hmass j hj).le
  exact setIntegral_normSq_harmonicRamareBlock_geom_le_levelMoment j k hk hA₀ hQ heta hW
    hPprime (hleft j hj) (hright j hj) hEm hEs (hV₀ j hj) (hJ j hj)

end

end RHTower.Sieve
