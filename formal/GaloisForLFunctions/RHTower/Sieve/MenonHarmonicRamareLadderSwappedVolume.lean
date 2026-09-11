import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicRamareLadderSwapped
import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicFrequencyMomentAssembly

/-!
# The swapped ladder with its frequency measure exposed, and the cofactor supremum evaluated

Two things the swapped receiver needs before it can be summed over a schedule.

* The Gallagher-set measure is exposed as a scalar, exactly as
  `menonHarmonicBlockCostVolume` does for the pointwise ordering, together with its monotonicity
  in that scalar.  This is what lets an exceptional-set budget replace the literal measure.
* The cofactor supremum that the swapped receiver pays is the harmonic mass of a literal integer
  interval, and on a geometric block that interval has ratio `O(1)`.  The elementary bound
  `∑_{a ≤ m ≤ b} 1/m ≤ (b+1-a)/a` therefore turns the supremum into an explicit `O(1)` scalar.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- The swapped block cost with the Gallagher-set measure exposed as a scalar. -/
def menonHarmonicSwappedBlockCostVolume
    (P : Finset ℕ) (A₀ B₀ : ℕ) (Q eta W volE : ℝ) (j : ℕ) : ℝ :=
  2 * harmonicPrimeMass (harmonicGeomCofactorBlock A₀ B₀ Q eta j) ^ 2 *
      ((2 * Real.pi)⁻¹ *
        (hmMassRecip ⌊Q * (1 + eta) ^ (j + 1)⌋₊
          (2 * Real.pi * W) (2 * Real.pi * volE) *
            ((1 / ((⌊Q * (1 + eta) ^ j⌋₊ + 1 : ℕ) : ℝ)) ^ 2 *
              ((geomBlock P Q (1 + eta) j).card : ℝ))))
    + 2 * harmonicPrimeMass (geomBlock P Q (1 + eta) j) ^ 2 *
        harmonicCofactorSupportError A₀ B₀ Q eta W j

theorem menonHarmonicSwappedBlockCost_eq_volume
    (P : Finset ℕ) (A₀ B₀ : ℕ) (Q eta W : ℝ) (E : Set ℝ) (j : ℕ) :
    menonHarmonicSwappedBlockCost P A₀ B₀ Q eta W E j =
      menonHarmonicSwappedBlockCostVolume P A₀ B₀ Q eta W (volume.real E) j := rfl

/-- The swapped block cost is monotone in the exposed set-measure budget. -/
theorem menonHarmonicSwappedBlockCostVolume_mono
    (P : Finset ℕ) (A₀ B₀ : ℕ) (Q eta W : ℝ) {u v : ℝ} (j : ℕ)
    (hW : 1 ≤ W) (huv : u ≤ v) :
    menonHarmonicSwappedBlockCostVolume P A₀ B₀ Q eta W u j ≤
      menonHarmonicSwappedBlockCostVolume P A₀ B₀ Q eta W v j := by
  have hT : 1 ≤ 2 * Real.pi * W := by
    nlinarith [Real.pi_gt_three]
  have hvol : 2 * Real.pi * u ≤ 2 * Real.pi * v :=
    mul_le_mul_of_nonneg_left huv (by positivity)
  unfold menonHarmonicSwappedBlockCostVolume
  gcongr
  exact hmMassRecip_mono_volume _ hT hvol

/-- The harmonic mass of an integer interval is at most its length over its left endpoint. -/
theorem harmonicPrimeMass_Icc_le {a b : ℕ} (ha : 1 ≤ a) :
    harmonicPrimeMass (Finset.Icc a b) ≤ ((b + 1 - a : ℕ) : ℝ) / (a : ℝ) := by
  classical
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt ha
  have hterm : ∀ m ∈ Finset.Icc a b, (1 : ℝ) / (m : ℝ) ≤ 1 / (a : ℝ) := by
    intro m hm
    have ham : (a : ℝ) ≤ (m : ℝ) := by exact_mod_cast (Finset.mem_Icc.1 hm).1
    exact one_div_le_one_div_of_le haR ham
  have hsum : harmonicPrimeMass (Finset.Icc a b)
      ≤ ((Finset.Icc a b).card : ℝ) * (1 / (a : ℝ)) := by
    rw [harmonicPrimeMass]
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [Finset.sum_const, nsmul_eq_mul]
  rw [Nat.card_Icc] at hsum
  calc
    harmonicPrimeMass (Finset.Icc a b) ≤ ((b + 1 - a : ℕ) : ℝ) * (1 / (a : ℝ)) := hsum
    _ = ((b + 1 - a : ℕ) : ℝ) / (a : ℝ) := by ring

/-- **The cofactor supremum paid by the swapped receiver is explicit.**  On a geometric block it
is the harmonic mass of the literal cofactor interval, hence at most its length over its left
endpoint. -/
theorem harmonicPrimeMass_harmonicGeomCofactorBlock_le
    (A₀ B₀ : ℕ) (Q eta : ℝ) (j : ℕ)
    (hleft : 1 ≤ ⌈(A₀ : ℝ) / ((Q * (1 + eta) ^ j) * (1 + eta))⌉₊) :
    harmonicPrimeMass (harmonicGeomCofactorBlock A₀ B₀ Q eta j)
      ≤ ((⌊(B₀ : ℝ) / (Q * (1 + eta) ^ j)⌋₊ + 1 -
            ⌈(A₀ : ℝ) / ((Q * (1 + eta) ^ j) * (1 + eta))⌉₊ : ℕ) : ℝ) /
          ((⌈(A₀ : ℝ) / ((Q * (1 + eta) ^ j) * (1 + eta))⌉₊ : ℕ) : ℝ) := by
  rw [harmonicGeomCofactorBlock]
  exact harmonicPrimeMass_Icc_le hleft

end

end RHTower.Sieve
