import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicFrequencyPartition
import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicRamareLadderOnHM

/-!
# Menon's harmonic all-small Ramaré bound

On the frequency set where every harmonic prime block is small, the exact harmonic Ramaré
bilinear form is split over the geometric ladder.  Each block is then bounded by its assigned
prime threshold and the reciprocal Halász--Montgomery mean square for the common cofactor block.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- Exact reciprocal-HM cost of one harmonic geometric Ramaré block. -/
def menonHarmonicAllSmallBlockCost
    (P : Finset ℕ) (A₀ B₀ : ℕ) (Q eta W V : ℝ) (E : Set ℝ) (j : ℕ) : ℝ :=
  2 * V ^ (2 : ℕ) * ((2 * Real.pi)⁻¹ *
      (hmMassRecip ⌊(B₀ : ℝ) / (Q * (1 + eta) ^ j)⌋₊
        (2 * Real.pi * W) (2 * Real.pi * volume.real E) *
          ((1 / (⌈(A₀ : ℝ) /
            ((Q * (1 + eta) ^ j) * (1 + eta))⌉₊ : ℝ)) ^ (2 : ℕ) *
            ((harmonicGeomCofactorBlock A₀ B₀ Q eta j).card : ℝ))))
    + 2 * harmonicPrimeMass (geomBlock P Q (1 + eta) j) ^ (2 : ℕ) *
        harmonicCofactorSupportError A₀ B₀ Q eta W j

/-- Menon's complete Case-I estimate on the harmonic all-small frequency set.  This is the exact
finite geometric-ladder sum, including reciprocal-HM cofactor mass and moving-support error. -/
theorem setIntegral_normSq_harmonicRamareBilinear_le_allSmall
    {P : Finset ℕ} {A₀ B₀ L : ℕ} {Q eta W : ℝ}
    (hA₀ : 1 ≤ A₀) (hQ : 0 < Q) (heta : 0 ≤ eta) (hW : 1 ≤ W) (hL : 1 ≤ L)
    (hPprime : ∀ p ∈ P, p.Prime)
    (hPrange : ∀ p ∈ P, Q < (p : ℝ) ∧ (p : ℝ) ≤ Q * (1 + eta) ^ L)
    (V : ℕ → ℝ)
    (hleft : ∀ j ∈ Finset.range L,
      1 ≤ ⌈(A₀ : ℝ) / ((Q * (1 + eta) ^ j) * (1 + eta))⌉₊)
    (hright : ∀ j ∈ Finset.range L,
      1 ≤ ⌊(B₀ : ℝ) / (Q * (1 + eta) ^ j)⌋₊) :
    (∫ w in menonHarmonicAllBlocksSmall P Q eta L V W,
      ‖harmonicRamareBilinear P (Finset.Icc A₀ B₀) w‖ ^ (2 : ℕ))
      ≤ (L : ℝ) * ∑ j ∈ Finset.range L,
          menonHarmonicAllSmallBlockCost P A₀ B₀ Q eta W (V j)
            (menonHarmonicAllBlocksSmall P Q eta L V W) j := by
  classical
  let E : Set ℝ := menonHarmonicAllBlocksSmall P Q eta L V W
  have hEm : MeasurableSet E :=
    measurableSet_menonHarmonicAllBlocksSmall P Q eta L V W
  have hEs : E ⊆ Set.Icc (-W) W :=
    menonHarmonicAllBlocksSmall_subset P Q eta L V W
  have hr : 1 ≤ 1 + eta := by linarith
  have hsplit := setIntegral_normSq_harmonicRamareBilinear_le_blocks
    (P := P) (s := Finset.Icc A₀ B₀) (W := W) hEm hEs
    (Finset.range L) (geomBlock P Q (1 + eta))
    (geomBlock_pairwiseDisjoint P hQ hr L)
    (geomBlock_biUnion_eq P Q (1 + eta) hL hPrange)
  rw [Finset.card_range] at hsplit
  refine hsplit.trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg L))
  refine Finset.sum_le_sum fun j hj => ?_
  have hblock := setIntegral_normSq_harmonicRamareBlock_geom_le_HM
    (P := P) (A₀ := A₀) (B₀ := B₀) (Q := Q) (eta := eta) (W := W) (V := V j)
    hA₀ hQ heta hW j hPprime (hleft j hj) (hright j hj) hEm hEs
    (fun w hw => norm_harmonicPrimeBlockPoly_le_of_mem_allBlocksSmall hj hw)
  simpa [E, menonHarmonicAllSmallBlockCost] using hblock

end

end RHTower.Sieve
