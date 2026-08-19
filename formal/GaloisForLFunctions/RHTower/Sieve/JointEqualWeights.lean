import GaloisForLFunctions.RHTower.Sieve.Section4Master
import GaloisForLFunctions.RHTower.Sieve.StepMassCard
import GaloisForLFunctions.RHTower.Sieve.Section4BlockMaster

/-!
# The ladder splits at equal weights

The harmonic Cauchy–Schwarz of `Sieve/LadderHarmonicSplit` and `Sieve/SetIntegralBlockSplit` needs
strictly positive weights, and the natural choice `v_j = 1/stepMass_j` is unavailable: a thin ladder
step need not contain a prime, and proving otherwise would need prime counting in short intervals.

Equal weights `v_j = 1` are available, and they are affordable.  The split then costs the *number of
steps* rather than the harmonic mass, and the number of steps is a polylogarithm; the compensating
fact is `Sieve/StepMassCard.stepMass_le`, which makes each step's mass `O(η)`, so that
`∑_j stepMass_j² ≤ 2η·W` and `L·η` is again a polylogarithm.

This module records the three equal-weight corollaries the assembly uses.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

theorem sum_one_div_one (L : ℕ) : (∑ _j ∈ Finset.range L, (1 : ℝ) / 1) = (L : ℝ) := by
  simp

/-- **The long ladder over a measurable set, at equal weights.** -/
theorem setIntegral_normSq_omegaWeighted_le_blocks_one {Q : Finset ℕ} {A₁ B₁ : ℕ}
    {R η W : ℝ} (hR : 0 < R) (hη : 0 ≤ η) {L : ℕ} (hL : 1 ≤ L)
    (hQprime : ∀ q ∈ Q, q.Prime)
    (hQrange : ∀ q ∈ Q, R < (q : ℝ) ∧ (q : ℝ) ≤ R * (1 + η) ^ L)
    (Vk Ik : ℕ → ℝ)
    {E : Set ℝ} (hEm : MeasurableSet E) (hEs : E ⊆ Set.Icc (-W) W)
    (hVk : ∀ k ∈ Finset.range L, ∀ w ∈ E,
      ‖primeBlockPoly (geomBlock Q R (1 + η) k) w‖ ≤ Vk k)
    (hIk : ∀ k ∈ Finset.range L,
      (∫ w in E, ‖logPoly moebiusCoeff (geomCofactorBlockAt A₁ B₁ R η k) w‖ ^ 2) ≤ Ik k) :
    (∫ w in E, ‖omegaWeightedMoebiusPoly Q (Finset.Icc A₁ B₁) w‖ ^ 2)
      ≤ 2 * ((L : ℝ) * ∑ k ∈ Finset.range L, Vk k ^ 2 * Ik k)
        + 2 * ∫ w in E, ‖ladderProductDefect Q A₁ B₁ R η L w‖ ^ 2 := by
  have hbase := setIntegral_normSq_omegaWeighted_le_blocks (Q := Q) (A₁ := A₁) (B₁ := B₁)
    (W := W) hR hη hL hQprime hQrange (fun _ => (1 : ℝ)) (fun _ _ => zero_lt_one) Vk Ik
    hEm hEs hVk hIk
  have h2 : (∑ k ∈ Finset.range L, (1 : ℝ) * (Vk k ^ 2 * Ik k))
      = ∑ k ∈ Finset.range L, Vk k ^ 2 * Ik k :=
    Finset.sum_congr rfl fun k _ => one_mul _
  refine hbase.trans (le_of_eq ?_)
  rw [sum_one_div_one, h2]

/-- **The joint polynomial over the short ladder, at equal weights.** -/
theorem integral_normSq_jointOmegaPoly_le_one {P Q : Finset ℕ} {B₀ : ℕ} {RP ηP W : ℝ}
    (hRP : 0 < RP) (hηP : 0 ≤ ηP) {LP : ℕ} (hLP : 1 ≤ LP)
    (hPprime : ∀ p ∈ P, p.Prime) (hQprime : ∀ q ∈ Q, q.Prime) (hPQ : Disjoint P Q)
    (hPrange : ∀ p ∈ P, RP < (p : ℝ) ∧ (p : ℝ) ≤ RP * (1 + ηP) ^ LP)
    (J : ℕ → ℝ) (Dshort : ℝ)
    (hJ : ∀ j ∈ Finset.range LP,
      (∫ w in Set.Icc (-W) W,
          ‖primeBlockPoly (geomBlock P RP (1 + ηP) j) w‖ ^ 2
            * ‖omegaWeightedMoebiusPoly Q (geomCofactorBlockAt 1 B₀ RP ηP j) w‖ ^ 2) ≤ J j)
    (hDshort : (∫ w in Set.Icc (-W) W,
        ‖jointLadderProductDefect P Q 1 B₀ RP ηP LP w‖ ^ 2) ≤ Dshort) :
    (∫ w in Set.Icc (-W) W, ‖jointOmegaPoly P Q (Finset.Icc 1 B₀) w‖ ^ 2)
      ≤ 2 * ((LP : ℝ) * ∑ j ∈ Finset.range LP, J j) + 2 * Dshort := by
  have hbase := integral_normSq_jointOmegaPoly_le_master (P := P) (Q := Q) (B₀ := B₀)
    (W := W) hRP hηP hLP hPprime hQprime hPQ hPrange (fun _ => (1 : ℝ))
    (fun _ _ => zero_lt_one) J Dshort hJ hDshort
  have h2 : (∑ j ∈ Finset.range LP, (1 : ℝ) * J j) = ∑ j ∈ Finset.range LP, J j :=
    Finset.sum_congr rfl fun j _ => one_mul _
  refine hbase.trans (le_of_eq ?_)
  rw [sum_one_div_one, h2]

/-- **One short block of §4, at equal weights.** -/
theorem section4_block_master_one {B Q : Finset ℕ} {B₁ : ℕ} {RQ ηQ W w₀ VP : ℝ} {LQ : ℕ}
    (hRQ : 0 < RQ) (hηQ : 0 ≤ ηQ) (hLQ : 1 ≤ LQ)
    (hQprime : ∀ q ∈ Q, q.Prime)
    (hQrange : ∀ q ∈ Q, RQ < (q : ℝ) ∧ (q : ℝ) ≤ RQ * (1 + ηQ) ^ LQ)
    (hwW : w₀ ≤ W)
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
          * (2 * ((LQ : ℝ)
                * ∑ k ∈ Finset.range LQ,
                    ((geomBlock Q RQ (1 + ηQ) k).card : ℝ) ^ 2 * Idisc k)
            + 2 * Dfct)
        + (VP ^ 2 * Enonexc
          + (B.card : ℝ) ^ 2
              * (2 * ((LQ : ℝ) * ∑ k ∈ Finset.range LQ, Vk k ^ 2 * Iann k) + 2 * Dfct)) := by
  have hbase := section4_block_master (B := B) (Q := Q) (B₁ := B₁) (W := W) (w₀ := w₀) (VP := VP)
    hRQ hηQ hLQ hQprime hQrange hwW (fun _ => (1 : ℝ)) (fun _ _ => zero_lt_one)
    Vk Idisc Iann Dfct Enonexc hVk hIdisc hIann hDdisc hDann hnonexc
  have h1 : (∑ k ∈ Finset.range LQ,
      (1 : ℝ) * (((geomBlock Q RQ (1 + ηQ) k).card : ℝ) ^ 2 * Idisc k))
      = ∑ k ∈ Finset.range LQ, ((geomBlock Q RQ (1 + ηQ) k).card : ℝ) ^ 2 * Idisc k :=
    Finset.sum_congr rfl fun k _ => one_mul _
  have h2 : (∑ k ∈ Finset.range LQ, (1 : ℝ) * (Vk k ^ 2 * Iann k))
      = ∑ k ∈ Finset.range LQ, Vk k ^ 2 * Iann k :=
    Finset.sum_congr rfl fun k _ => one_mul _
  refine hbase.trans (le_of_eq ?_)
  rw [sum_one_div_one, h1, h2]

end

end RHTower.Sieve
