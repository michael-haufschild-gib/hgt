import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicNarrowBlockComparison
import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicGlobalFrequencyAssembly

/-!
# Harmonic Ramaré energy on an ordinary all-small frequency set

An ordinary geometric prime ladder controls the corresponding reciprocal-weighted harmonic
ladder block by block.  This file inserts that narrow-block comparison into the exact harmonic
Ramaré product assembly, retaining the reciprocal Halász--Montgomery cost and paying the moving
support defect once globally.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- The complete harmonic Ramaré bound on an ordinary all-small frequency set. -/
theorem setIntegral_normSq_harmonicRamareBilinear_le_ordinary_allSmall
    {P : Finset ℕ} {A₀ B₀ L : ℕ} {Q eta theta W : ℝ}
    (hA : 0 < A₀) (hQ : 1 < Q) (heta : 0 ≤ eta) (hW : 1 ≤ W) (hL : 1 ≤ L)
    (hPprime : ∀ p ∈ P, p.Prime)
    (hPrange : ∀ p ∈ P, Q < (p : ℝ) ∧ (p : ℝ) ≤ Q * (1 + eta) ^ L)
    (hleft : ∀ j ∈ Finset.range L,
      1 ≤ ⌈(A₀ : ℝ) / ((Q * (1 + eta) ^ j) * (1 + eta))⌉₊)
    (hright : ∀ j ∈ Finset.range L,
      1 ≤ ⌊(B₀ : ℝ) / (Q * (1 + eta) ^ j)⌋₊) :
    let E := allBlocksSmall P Q eta L
      (fun j => ((geomBlock P Q (1 + eta) j).card : ℝ) * theta) W
    (∫ w in E,
      ‖harmonicRamareBilinear P (Finset.Icc A₀ B₀) w‖ ^ 2) ≤
      2 * (L : ℝ) * ∑ j ∈ Finset.range L,
        menonHarmonicProductCostVolume P A₀ B₀ Q eta W
          (((geomBlock P Q (1 + eta) j).card : ℝ) * (theta + eta) /
            (Q * (1 + eta) ^ j)) (volume.real E) j +
        2 * menonHarmonicLadderErrorBudget A₀ B₀ Q eta W L := by
  classical
  let E := allBlocksSmall P Q eta L
    (fun j => ((geomBlock P Q (1 + eta) j).card : ℝ) * theta) W
  have hEm : MeasurableSet E := by
    simpa only [E] using measurableSet_allBlocksSmall P Q eta L
      (fun j => ((geomBlock P Q (1 + eta) j).card : ℝ) * theta) W
  have hEs : E ⊆ Set.Icc (-W) W := by
    simpa only [E] using allBlocksSmall_subset P Q eta L
      (fun j => ((geomBlock P Q (1 + eta) j).card : ℝ) * theta) W
  have hbase := setIntegral_normSq_harmonicRamareBilinear_le_ladder_closed
    (P := P) (A₀ := A₀) (B₀ := B₀) (Q := Q) (eta := eta) (W := W) (L := L)
    hA hQ heta hW hL hPprime hPrange hEm hEs
  refine hbase.trans (add_le_add ?_ le_rfl)
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j hj => ?_)
    (mul_nonneg (by norm_num) (Nat.cast_nonneg L))
  exact setIntegral_normSq_harmonicProduct_geom_le_HM
    (P := P) (A₀ := A₀) (B₀ := B₀) (Q := Q) (eta := eta) (W := W)
    (V := ((geomBlock P Q (1 + eta) j).card : ℝ) * (theta + eta) /
      (Q * (1 + eta) ^ j)) hW j (hleft j hj) (hright j hj) hEm hEs
      (fun w hw =>
        norm_harmonicPrimeBlockPoly_le_of_mem_ordinary_allBlocksSmall
          (lt_trans zero_lt_one hQ) heta hj (by simpa only [E] using hw))

end

end RHTower.Sieve
