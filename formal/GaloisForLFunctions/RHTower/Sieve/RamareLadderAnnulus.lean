import GaloisForLFunctions.RHTower.Sieve.BlockProductAnnulus
import GaloisForLFunctions.RHTower.Sieve.LadderErrorBudget
import GaloisForLFunctions.RHTower.Sieve.LadderBlockMeanSquare
import GaloisForLFunctions.RHTower.Sieve.LadderAffineMajorant

/-!
# The Ramaré bilinear mean square over a cut window

`Sieve/RamareBlockSplit` writes the bilinear form as the ladder of products plus one global
discrepancy, and `Sieve/LadderErrorBudget` pays the discrepancy once, in closed form.  Cutting the
window at a frequency `w₀` and applying `Sieve/BlockProductAnnulus` to each product bounds the
ladder: on the annulus by the prime polynomial's cancellation, on the disc by the cofactor
polynomial's.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- The closed form of the ladder discrepancy budget. -/
theorem integral_normSq_ramareLadderError_le_defectSum {P : Finset ℕ} (M : ℕ) {Q η W : ℝ}
    (hQ : 1 < Q) (hη : 0 ≤ η) (hW : 1 ≤ W) {L : ℕ}
    (hPprime : ∀ q ∈ P, q.Prime) (hPge : ∀ p ∈ P, Q ≤ (p : ℝ)) :
    (∫ w in Set.Icc (-W) W, ‖ramareLadderError P M Q η L w‖ ^ (2 : ℕ))
      ≤ (5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * ((⌊(M : ℝ) * (1 + η)⌋₊ : ℕ) : ℝ))
          * ladderDefectSum L M Q η := by
  refine (integral_normSq_ramareLadderError_le_closed M hQ hη hW hPprime hPge).trans
    (le_of_eq ?_)
  rw [ladderDefectSum]
  push_cast
  ring

/-- **The Ramaré bilinear mean square over a cut window.** -/
theorem integral_normSq_ramareBilinear_annulus_le {P : Finset ℕ} (M : ℕ) {Q η w₀ W : ℝ}
    (hQ : 1 < Q) (hη : 0 ≤ η) (hW : 1 ≤ W) (hw₀ : 0 ≤ w₀) (hwW : w₀ ≤ W) {L : ℕ} (hL : 1 ≤ L)
    (hPprime : ∀ q ∈ P, q.Prime) (hPge : ∀ p ∈ P, Q ≤ (p : ℝ))
    (hP : ∀ p ∈ P, Q < (p : ℝ) ∧ (p : ℝ) ≤ Q * (1 + η) ^ L)
    (V U Vlow : ℕ → ℝ) (hV : ∀ j, 0 ≤ V j) (hU : ∀ j, 0 ≤ U j) (hVlow : ∀ j, 0 ≤ Vlow j)
    (hann : ∀ j ∈ Finset.range L, ∀ w ∈ Set.Icc (-W) W \ Set.Icc (-w₀) w₀,
      ‖primeBlockPoly (geomBlock P Q (1 + η) j) w‖ ≤ V j)
    (hlowP : ∀ j ∈ Finset.range L, ∀ w ∈ Set.Icc (-w₀) w₀,
      ‖primeBlockPoly (geomBlock P Q (1 + η) j) w‖ ≤ Vlow j)
    (hlowC : ∀ j ∈ Finset.range L, ∀ w ∈ Set.Icc (-w₀) w₀,
      ‖logPoly (ramareCofactorCoeff P) (geomCofactorBlock M Q η j) w‖ ≤ U j) :
    (∫ w in Set.Icc (-W) W, ‖ramareBilinear P M w‖ ^ (2 : ℕ))
      ≤ 2 * (L : ℝ) * ∑ j ∈ Finset.range L,
            (V j ^ (2 : ℕ) * ((5 * Real.pi / 2 * W
                  + 5 * Real.exp 1 / 2 * ((⌊(M : ℝ) / (Q * (1 + η) ^ j)⌋₊ : ℕ) : ℝ))
                * ((geomCofactorBlock M Q η j).card : ℝ))
              + Vlow j ^ (2 : ℕ) * U j ^ (2 : ℕ) * (2 * w₀))
        + 2 * ((5 * Real.pi / 2 * W
              + 5 * Real.exp 1 / 2 * ((⌊(M : ℝ) * (1 + η)⌋₊ : ℕ) : ℝ))
            * ladderDefectSum L M Q η) := by
  classical
  have hQ0 : (0 : ℝ) < Q := lt_trans zero_lt_one hQ
  have hbase := integral_normSq_ramareBilinear_le_ladder_error (P := P) M hQ0 hη hL hP (W := W)
  have hsteps : ∑ j ∈ Finset.range L,
      (∫ w in Set.Icc (-W) W,
        ‖primeBlockPoly (geomBlock P Q (1 + η) j) w
          * logPoly (ramareCofactorCoeff P) (geomCofactorBlock M Q η j) w‖ ^ (2 : ℕ))
      ≤ ∑ j ∈ Finset.range L,
          (V j ^ (2 : ℕ) * ((5 * Real.pi / 2 * W
                + 5 * Real.exp 1 / 2 * ((⌊(M : ℝ) / (Q * (1 + η) ^ j)⌋₊ : ℕ) : ℝ))
              * ((geomCofactorBlock M Q η j).card : ℝ))
            + Vlow j ^ (2 : ℕ) * U j ^ (2 : ℕ) * (2 * w₀)) := by
    refine Finset.sum_le_sum fun j hj => ?_
    have hbounds := geomCofactorBlockAt_bounds (A₀ := 1) (B₀ := M) (by norm_num) hQ0 hη j
    exact integral_normSq_blockProduct_annulus_le (ramareCofactorCoeff P)
      (norm_ramareCofactorCoeff_le_one P) (geomBlock P Q (1 + η) j) (geomCofactorBlock M Q η j)
      hbounds.1 hbounds.2 hW hw₀ hwW (hV j) (hVlow j) (hU j) (hann j hj) (hlowP j hj) (hlowC j hj)
  have herr := integral_normSq_ramareLadderError_le_defectSum (P := P) (L := L) M hQ hη hW
    hPprime hPge
  have hLnn : (0 : ℝ) ≤ 2 * (L : ℝ) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hsteps hLnn
  linarith [hbase, hmul, herr]

end

end RHTower.Sieve
