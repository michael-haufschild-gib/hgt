import GaloisForLFunctions.RHTower.Sieve.Section4DiscCofactor
import GaloisForLFunctions.RHTower.Sieve.OmegaQEnergy

/-!
# One short block of exposé §4, complete

The disc and the annulus, each with its own data, combined into the single per-step bound that the
assembly of `Sieve/Section4Assembly` consumes.  Everything is a parameter: the Route-T saving `Vk`
on the annulus, the two cofactor mean squares `Idisc`, `Iann`, the long ladder's defect `Dfct`, and
the non-exceptional mean square `Enonexc`.  Each of the five is supplied by a corpus theorem or by
one of this session's bricks.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- **One short block of §4, disc and annulus together.** -/
theorem section4_block_master {B Q : Finset ℕ} {B₁ : ℕ} {RQ ηQ W w₀ VP : ℝ} {LQ : ℕ}
    (hRQ : 0 < RQ) (hηQ : 0 ≤ ηQ) (hLQ : 1 ≤ LQ)
    (hQprime : ∀ q ∈ Q, q.Prime)
    (hQrange : ∀ q ∈ Q, RQ < (q : ℝ) ∧ (q : ℝ) ≤ RQ * (1 + ηQ) ^ LQ)
    (hwW : w₀ ≤ W)
    (v : ℕ → ℝ) (hv : ∀ k ∈ Finset.range LQ, 0 < v k)
    (Vk Idisc Iann : ℕ → ℝ) (Dfct Enonexc : ℝ)
    (hVk : ∀ k ∈ Finset.range LQ, ∀ w ∈ shortExceptionalOn (windowAnnulus w₀ W) B VP,
      ‖primeBlockPoly (geomBlock Q RQ (1 + ηQ) k) w‖ ≤ Vk k)
    (hIdisc : ∀ k ∈ Finset.range LQ,
      (∫ w in Set.Icc (-w₀) w₀,
          ‖logPoly moebiusCoeff (geomCofactorBlockAt 1 B₁ RQ ηQ k) w‖ ^ 2) ≤ Idisc k)
    (hIann : ∀ k ∈ Finset.range LQ,
      (∫ w in shortExceptionalOn (windowAnnulus w₀ W) B VP,
          ‖logPoly moebiusCoeff (geomCofactorBlockAt 1 B₁ RQ ηQ k) w‖ ^ 2) ≤ Iann k)
    (hDdisc : (∫ w in Set.Icc (-w₀) w₀,
        ‖ladderProductDefect Q 1 B₁ RQ ηQ LQ w‖ ^ 2) ≤ Dfct)
    (hDann : (∫ w in shortExceptionalOn (windowAnnulus w₀ W) B VP,
        ‖ladderProductDefect Q 1 B₁ RQ ηQ LQ w‖ ^ 2) ≤ Dfct)
    (hnonexc : (∫ w in windowAnnulus w₀ W,
        ‖omegaWeightedMoebiusPoly Q (Finset.Icc 1 B₁) w‖ ^ 2) ≤ Enonexc) :
    (∫ w in Set.Icc (-W) W,
        ‖primeBlockPoly B w‖ ^ 2 * ‖omegaWeightedMoebiusPoly Q (Finset.Icc 1 B₁) w‖ ^ 2)
      ≤ (B.card : ℝ) ^ 2
          * (2 * ((∑ k ∈ Finset.range LQ, 1 / v k)
                * ∑ k ∈ Finset.range LQ, v k
                    * (((geomBlock Q RQ (1 + ηQ) k).card : ℝ) ^ 2 * Idisc k))
            + 2 * Dfct)
        + (VP ^ 2 * Enonexc
          + (B.card : ℝ) ^ 2
              * (2 * ((∑ k ∈ Finset.range LQ, 1 / v k)
                    * ∑ k ∈ Finset.range LQ, v k * (Vk k ^ 2 * Iann k))
                + 2 * Dfct)) := by
  classical
  -- the disc
  have hdisc := section4_block_disc (B := B) (Q := Q) (A₁ := 1) (B₁ := B₁) (W := W)
    hRQ hηQ hLQ hwW hQprime hQrange v hv Idisc hIdisc
  have hdisc' : (∫ w in Set.Icc (-w₀) w₀,
      ‖primeBlockPoly B w‖ ^ 2 * ‖omegaWeightedMoebiusPoly Q (Finset.Icc 1 B₁) w‖ ^ 2)
      ≤ (B.card : ℝ) ^ 2
          * (2 * ((∑ k ∈ Finset.range LQ, 1 / v k)
                * ∑ k ∈ Finset.range LQ, v k
                    * (((geomBlock Q RQ (1 + ηQ) k).card : ℝ) ^ 2 * Idisc k))
            + 2 * Dfct) := by
    refine hdisc.trans ?_
    have hB2 : (0 : ℝ) ≤ (B.card : ℝ) ^ 2 := sq_nonneg _
    have := mul_le_mul_of_nonneg_left hDdisc (by norm_num : (0 : ℝ) ≤ 2)
    exact mul_le_mul_of_nonneg_left (by linarith) hB2
  -- the annulus
  have hann := section4_block_full_on (B := B) (Q := Q) (A₁ := 1) (B₁ := B₁) (W := W)
    (VP := VP) hRQ hηQ hLQ hQprime hQrange v hv Vk Iann
    (measurableSet_windowAnnulus w₀ W) (windowAnnulus_subset w₀ W) hVk hIann
  have hann' : (∫ w in windowAnnulus w₀ W,
      ‖primeBlockPoly B w‖ ^ 2 * ‖omegaWeightedMoebiusPoly Q (Finset.Icc 1 B₁) w‖ ^ 2)
      ≤ VP ^ 2 * Enonexc
        + (B.card : ℝ) ^ 2
            * (2 * ((∑ k ∈ Finset.range LQ, 1 / v k)
                  * ∑ k ∈ Finset.range LQ, v k * (Vk k ^ 2 * Iann k))
              + 2 * Dfct) := by
    refine hann.trans ?_
    have hB2 : (0 : ℝ) ≤ (B.card : ℝ) ^ 2 := sq_nonneg _
    have h1 : VP ^ 2 * (∫ w in windowAnnulus w₀ W,
        ‖omegaWeightedMoebiusPoly Q (Finset.Icc 1 B₁) w‖ ^ 2) ≤ VP ^ 2 * Enonexc :=
      mul_le_mul_of_nonneg_left hnonexc (sq_nonneg _)
    have h2 := mul_le_mul_of_nonneg_left
      (by linarith [mul_le_mul_of_nonneg_left hDann (by norm_num : (0 : ℝ) ≤ 2)] :
        2 * ((∑ k ∈ Finset.range LQ, 1 / v k)
              * ∑ k ∈ Finset.range LQ, v k * (Vk k ^ 2 * Iann k))
            + 2 * ∫ w in shortExceptionalOn (windowAnnulus w₀ W) B VP,
                ‖ladderProductDefect Q 1 B₁ RQ ηQ LQ w‖ ^ 2
          ≤ 2 * ((∑ k ∈ Finset.range LQ, 1 / v k)
                * ∑ k ∈ Finset.range LQ, v k * (Vk k ^ 2 * Iann k))
              + 2 * Dfct) hB2
    linarith [h1, h2]
  exact section4_block_disc_ann hwW hdisc' hann'

end

end RHTower.Sieve
