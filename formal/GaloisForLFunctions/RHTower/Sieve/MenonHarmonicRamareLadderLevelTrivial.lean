import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicBlockLevelTrivial
import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicRamareLadderLevelMoment

/-!
# The ladder receiver on a small frequency set

`MenonHarmonicRamareLadderLevelMoment` runs the ladder with the reciprocal Halasz--Montgomery
receiver on every level.  That receiver's `hmMassRecip` carries the term `48 pi N log(2+2T)`, which
does not shrink with the frequency set, so on the *exceptional* set of Menon's `L²`--`L^∞` split —
which is where the ladder is actually applied, and whose measure is tiny — it is the wrong tool.

This file runs the same ladder with the trivial measure-times-supremum receiver instead, so every
term is proportional to a measure.  The resulting per-block cost is
`≍ harmonicPrimeMass (B_j)² · |E|`, and under the mass split the whole ladder is
`≍ harmonicPrimeMass P² · |E|` — the total harmonic mass squared times the measure of the set, with
no logarithm of the height anywhere.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- The per-block cost of the level-split receiver on a small frequency set. -/
def menonHarmonicLevelTrivialBlockCost
    (P : Finset ℕ) (A₀ B₀ : ℕ) (Q eta W volE : ℝ) (k j J : ℕ) (V₀ : ℝ) : ℝ :=
  2 * (V₀ ^ 2 *
          (volE * harmonicPrimeMass (harmonicGeomCofactorBlock A₀ B₀ Q eta j) ^ 2)
        + ∑ i ∈ Finset.range J,
            (2 ^ (i + 1) * V₀) ^ 2 *
              ((menonHarmonicLocalBlockMomentCost k Q eta W j / (2 ^ i * V₀) ^ (2 * k)) *
                harmonicPrimeMass (harmonicGeomCofactorBlock A₀ B₀ Q eta j) ^ 2))
    + 2 * harmonicPrimeMass (geomBlock P Q (1 + eta) j) ^ 2 *
        harmonicCofactorSupportError A₀ B₀ Q eta W j

/-- **One geometric block on a small frequency set.** -/
theorem setIntegral_normSq_harmonicRamareBlock_geom_le_levelTrivial
    {P : Finset ℕ} {A₀ B₀ : ℕ} {Q eta W : ℝ} (j k : ℕ) (hk : 1 ≤ k)
    (hA₀ : 1 ≤ A₀) (hQ : 0 < Q) (heta : 0 ≤ eta) (hW : 1 ≤ W)
    (hPprime : ∀ p ∈ P, p.Prime)
    (hleft : 1 ≤ ⌈(A₀ : ℝ) / ((Q * (1 + eta) ^ j) * (1 + eta))⌉₊)
    {E : Set ℝ} (hEm : MeasurableSet E) (hEs : E ⊆ Set.Icc (-W) W)
    {V₀ : ℝ} (hV₀ : 0 < V₀) {J : ℕ}
    (hJ : harmonicPrimeMass (geomBlock P Q (1 + eta) j) ≤ 2 ^ J * V₀) :
    (∫ w in E,
      ‖harmonicRamareBlock P (Finset.Icc A₀ B₀)
        (geomBlock P Q (1 + eta) j) w‖ ^ 2)
      ≤ menonHarmonicLevelTrivialBlockCost P A₀ B₀ Q eta W (volume.real E) k j J V₀ := by
  classical
  have hprod := setIntegral_normSq_harmonicBlockProduct_levelSplit_trivial_moment
    P (harmonicGeomCofactorBlock A₀ B₀ Q eta j) j k hk hPprime hQ heta hW hEm hEs hV₀ hJ
  have hblock := setIntegral_normSq_harmonicRamareBlock_geom_le
    (P := P) (A₀ := A₀) (B₀ := B₀) (Q := Q) (eta := eta) (W := W)
    hA₀ hQ heta hW j hPprime hleft hEm hEs
  rw [menonHarmonicLevelTrivialBlockCost]
  linarith

/-- **The complete ladder on a small frequency set: mass split outside, measured levels inside.** -/
theorem setIntegral_normSq_harmonicRamareBilinear_le_levelTrivial_mass
    {P : Finset ℕ} {A₀ B₀ L : ℕ} {Q eta W : ℝ} (k : ℕ) (hk : 1 ≤ k)
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
      harmonicPrimeMass (geomBlock P Q (1 + eta) j) ≤ 2 ^ (J j) * V₀ j)
    {E : Set ℝ} (hEm : MeasurableSet E) (hEs : E ⊆ Set.Icc (-W) W) :
    (∫ w in E, ‖harmonicRamareBilinear P (Finset.Icc A₀ B₀) w‖ ^ 2)
      ≤ harmonicPrimeMass P * ∑ j ∈ Finset.range L,
          menonHarmonicLevelTrivialBlockCost P A₀ B₀ Q eta W (volume.real E) k j (J j) (V₀ j)
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
  exact setIntegral_normSq_harmonicRamareBlock_geom_le_levelTrivial j k hk hA₀ hQ heta hW
    hPprime (hleft j hj) hEm hEs (hV₀ j hj) (hJ j hj)

end

end RHTower.Sieve
