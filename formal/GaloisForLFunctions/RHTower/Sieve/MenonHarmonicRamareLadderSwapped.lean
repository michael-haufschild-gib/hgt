import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicRamareBlockSwapped
import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicAllSmallBound

/-!
# The swapped and hybrid harmonic Ramare ladders

`MenonHarmonicAllSmallBound` runs the whole geometric ladder with one ordering: every prime block
is paid pointwise and every cofactor by reciprocal Halasz--Montgomery.  That ordering is wasteful
on the blocks whose prime scale is comparable with the source scale, because there the cofactor
polynomial is short and the pointwise prime bound throws away the mean-square saving carried by
the prime polynomial itself.

This file adds the reversed ladder and, more usefully, the **hybrid** ladder, in which every block
independently takes whichever of the two receivers is smaller.  The hybrid bound is therefore
never worse than the existing all-small ladder, and it is the receiver the high blocks need.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- The swapped cost of one harmonic geometric block: the cofactor's own harmonic supremum times
the reciprocal Halasz--Montgomery mean square of the prime block, plus the exact moving-support
error. -/
def menonHarmonicSwappedBlockCost
    (P : Finset ℕ) (A₀ B₀ : ℕ) (Q eta W : ℝ) (E : Set ℝ) (j : ℕ) : ℝ :=
  2 * harmonicPrimeMass (harmonicGeomCofactorBlock A₀ B₀ Q eta j) ^ 2 *
      ((2 * Real.pi)⁻¹ *
        (hmMassRecip ⌊Q * (1 + eta) ^ (j + 1)⌋₊
          (2 * Real.pi * W) (2 * Real.pi * volume.real E) *
            ((1 / ((⌊Q * (1 + eta) ^ j⌋₊ + 1 : ℕ) : ℝ)) ^ 2 *
              ((geomBlock P Q (1 + eta) j).card : ℝ))))
    + 2 * harmonicPrimeMass (geomBlock P Q (1 + eta) j) ^ 2 *
        harmonicCofactorSupportError A₀ B₀ Q eta W j

/-- One geometric block, against the swapped cost. -/
theorem setIntegral_normSq_harmonicRamareBlock_geom_le_swappedCost
    {P : Finset ℕ} {A₀ B₀ : ℕ} {Q eta W : ℝ}
    (hA₀ : 1 ≤ A₀) (hQ : 0 < Q) (heta : 0 ≤ eta) (hW : 1 ≤ W) (j : ℕ)
    (hPprime : ∀ p ∈ P, p.Prime)
    (hleft : 1 ≤ ⌈(A₀ : ℝ) / ((Q * (1 + eta) ^ j) * (1 + eta))⌉₊)
    (htop : 1 ≤ ⌊Q * (1 + eta) ^ (j + 1)⌋₊)
    {E : Set ℝ} (hEm : MeasurableSet E) (hEs : E ⊆ Set.Icc (-W) W) :
    (∫ w in E,
      ‖harmonicRamareBlock P (Finset.Icc A₀ B₀)
        (geomBlock P Q (1 + eta) j) w‖ ^ 2)
      ≤ menonHarmonicSwappedBlockCost P A₀ B₀ Q eta W E j :=
  setIntegral_normSq_harmonicRamareBlock_geom_le_HM_swapped
    hA₀ hQ heta hW j hPprime hleft htop hEm hEs

/-- **One geometric block against the better of the two receivers.** -/
theorem setIntegral_normSq_harmonicRamareBlock_geom_le_min
    {P : Finset ℕ} {A₀ B₀ : ℕ} {Q eta W V : ℝ}
    (hA₀ : 1 ≤ A₀) (hQ : 0 < Q) (heta : 0 ≤ eta) (hW : 1 ≤ W) (j : ℕ)
    (hPprime : ∀ p ∈ P, p.Prime)
    (hleft : 1 ≤ ⌈(A₀ : ℝ) / ((Q * (1 + eta) ^ j) * (1 + eta))⌉₊)
    (hright : 1 ≤ ⌊(B₀ : ℝ) / (Q * (1 + eta) ^ j)⌋₊)
    (htop : 1 ≤ ⌊Q * (1 + eta) ^ (j + 1)⌋₊)
    {E : Set ℝ} (hEm : MeasurableSet E) (hEs : E ⊆ Set.Icc (-W) W)
    (hprime : ∀ w ∈ E,
      ‖harmonicPrimeBlockPoly (geomBlock P Q (1 + eta) j) w‖ ≤ V) :
    (∫ w in E,
      ‖harmonicRamareBlock P (Finset.Icc A₀ B₀)
        (geomBlock P Q (1 + eta) j) w‖ ^ 2)
      ≤ min (menonHarmonicAllSmallBlockCost P A₀ B₀ Q eta W V E j)
          (menonHarmonicSwappedBlockCost P A₀ B₀ Q eta W E j) := by
  refine le_min ?_ ?_
  · have h := setIntegral_normSq_harmonicRamareBlock_geom_le_HM
      hA₀ hQ heta hW j hPprime hleft hright hEm hEs hprime
    simpa only [menonHarmonicAllSmallBlockCost] using h
  · exact setIntegral_normSq_harmonicRamareBlock_geom_le_swappedCost
      hA₀ hQ heta hW j hPprime hleft htop hEm hEs

/-- **The complete swapped geometric ladder.** -/
theorem setIntegral_normSq_harmonicRamareBilinear_le_swapped
    {P : Finset ℕ} {A₀ B₀ L : ℕ} {Q eta W : ℝ}
    (hA₀ : 1 ≤ A₀) (hQ : 0 < Q) (heta : 0 ≤ eta) (hW : 1 ≤ W) (hL : 1 ≤ L)
    (hPprime : ∀ p ∈ P, p.Prime)
    (hPrange : ∀ p ∈ P, Q < (p : ℝ) ∧ (p : ℝ) ≤ Q * (1 + eta) ^ L)
    (hleft : ∀ j ∈ Finset.range L,
      1 ≤ ⌈(A₀ : ℝ) / ((Q * (1 + eta) ^ j) * (1 + eta))⌉₊)
    (htop : ∀ j ∈ Finset.range L, 1 ≤ ⌊Q * (1 + eta) ^ (j + 1)⌋₊)
    {E : Set ℝ} (hEm : MeasurableSet E) (hEs : E ⊆ Set.Icc (-W) W) :
    (∫ w in E, ‖harmonicRamareBilinear P (Finset.Icc A₀ B₀) w‖ ^ 2)
      ≤ (L : ℝ) * ∑ j ∈ Finset.range L,
          menonHarmonicSwappedBlockCost P A₀ B₀ Q eta W E j := by
  classical
  have hr : 1 ≤ 1 + eta := by linarith
  have hsplit := setIntegral_normSq_harmonicRamareBilinear_le_blocks
    (P := P) (s := Finset.Icc A₀ B₀) (W := W) hEm hEs
    (Finset.range L) (geomBlock P Q (1 + eta))
    (geomBlock_pairwiseDisjoint P hQ hr L)
    (geomBlock_biUnion_eq P Q (1 + eta) hL hPrange)
  rw [Finset.card_range] at hsplit
  refine hsplit.trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg L))
  refine Finset.sum_le_sum fun j hj => ?_
  exact setIntegral_normSq_harmonicRamareBlock_geom_le_swappedCost
    hA₀ hQ heta hW j hPprime (hleft j hj) (htop j hj) hEm hEs

/-- **The hybrid geometric ladder: every block takes the better of the two receivers.**  This is
never worse than `setIntegral_normSq_harmonicRamareBilinear_le_allSmall`, and it is the estimate
the blocks at the source scale require. -/
theorem setIntegral_normSq_harmonicRamareBilinear_le_min
    {P : Finset ℕ} {A₀ B₀ L : ℕ} {Q eta W : ℝ}
    (hA₀ : 1 ≤ A₀) (hQ : 0 < Q) (heta : 0 ≤ eta) (hW : 1 ≤ W) (hL : 1 ≤ L)
    (hPprime : ∀ p ∈ P, p.Prime)
    (hPrange : ∀ p ∈ P, Q < (p : ℝ) ∧ (p : ℝ) ≤ Q * (1 + eta) ^ L)
    (V : ℕ → ℝ)
    (hleft : ∀ j ∈ Finset.range L,
      1 ≤ ⌈(A₀ : ℝ) / ((Q * (1 + eta) ^ j) * (1 + eta))⌉₊)
    (hright : ∀ j ∈ Finset.range L,
      1 ≤ ⌊(B₀ : ℝ) / (Q * (1 + eta) ^ j)⌋₊)
    (htop : ∀ j ∈ Finset.range L, 1 ≤ ⌊Q * (1 + eta) ^ (j + 1)⌋₊)
    {E : Set ℝ} (hEm : MeasurableSet E) (hEs : E ⊆ Set.Icc (-W) W)
    (hprime : ∀ j ∈ Finset.range L, ∀ w ∈ E,
      ‖harmonicPrimeBlockPoly (geomBlock P Q (1 + eta) j) w‖ ≤ V j) :
    (∫ w in E, ‖harmonicRamareBilinear P (Finset.Icc A₀ B₀) w‖ ^ 2)
      ≤ (L : ℝ) * ∑ j ∈ Finset.range L,
          min (menonHarmonicAllSmallBlockCost P A₀ B₀ Q eta W (V j) E j)
            (menonHarmonicSwappedBlockCost P A₀ B₀ Q eta W E j) := by
  classical
  have hr : 1 ≤ 1 + eta := by linarith
  have hsplit := setIntegral_normSq_harmonicRamareBilinear_le_blocks
    (P := P) (s := Finset.Icc A₀ B₀) (W := W) hEm hEs
    (Finset.range L) (geomBlock P Q (1 + eta))
    (geomBlock_pairwiseDisjoint P hQ hr L)
    (geomBlock_biUnion_eq P Q (1 + eta) hL hPrange)
  rw [Finset.card_range] at hsplit
  refine hsplit.trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg L))
  refine Finset.sum_le_sum fun j hj => ?_
  exact setIntegral_normSq_harmonicRamareBlock_geom_le_min
    hA₀ hQ heta hW j hPprime (hleft j hj) (hright j hj) (htop j hj) hEm hEs
    (hprime j hj)

end

end RHTower.Sieve
