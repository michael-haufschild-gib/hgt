import GaloisForLFunctions.RHTower.Sieve.Section4BlockFull
import GaloisForLFunctions.RHTower.Sieve.LadderAnnulus

/-!
# One short block, split into disc and annulus

Lemma 2.3 — the Route-T twisted prime-sum bound that the exceptional case of §4 applies to the long
prime blocks — is only available for frequencies bounded away from the origin.  The window is
therefore cut into a disc `|w| ≤ w₀` and an annulus, and the two are estimated differently:

* on the **annulus** the §4 machinery runs as written (`Sieve/Section4BlockFull.section4_block_full_on`);
* on the **disc** the short prime polynomial is bounded trivially and the long ladder's blocks are
  bounded trivially too, the saving coming instead from the *cofactor*, which is a Möbius polynomial
  of near-maximal length and therefore has more than a power-of-log cancellation at low frequency.

Both halves consume the same long-ladder lemma
`Sieve/Section4QSide.setIntegral_normSq_omegaWeighted_le_blocks`; only the data `Vk`, `Ik` differ.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- The annulus of a window. -/
def windowAnnulus (w₀ W : ℝ) : Set ℝ := Set.Icc (-W) W \ Set.Icc (-w₀) w₀

theorem measurableSet_windowAnnulus (w₀ W : ℝ) : MeasurableSet (windowAnnulus w₀ W) :=
  measurableSet_Icc.diff measurableSet_Icc

theorem windowAnnulus_subset (w₀ W : ℝ) : windowAnnulus w₀ W ⊆ Set.Icc (-W) W :=
  Set.sdiff_subset

/-- Every frequency of the annulus is bounded away from the origin. -/
theorem abs_ge_of_mem_windowAnnulus {w₀ W w : ℝ} (hw : w ∈ windowAnnulus w₀ W) :
    w₀ ≤ |w| := by
  by_contra hcon
  have hlt : |w| < w₀ := not_le.1 hcon
  refine hw.2 (Set.mem_Icc.2 ⟨?_, ?_⟩)
  · cases abs_cases w with
    | inl h => linarith [h.1, h.2]
    | inr h => linarith [h.1, h.2]
  · cases abs_cases w with
    | inl h => linarith [h.1, h.2]
    | inr h => linarith [h.1, h.2]

/-- **The disc half of a short block.**  Both prime factors are bounded trivially; the saving is in
the cofactor, whose mean square over the disc is the parameter `Ik`. -/
theorem section4_block_disc {B Q : Finset ℕ} {A₁ B₁ : ℕ}
    {R η W w₀ : ℝ} (hR : 0 < R) (hη : 0 ≤ η) {L : ℕ} (hL : 1 ≤ L) (hwW : w₀ ≤ W)
    (hQprime : ∀ q ∈ Q, q.Prime)
    (hQrange : ∀ q ∈ Q, R < (q : ℝ) ∧ (q : ℝ) ≤ R * (1 + η) ^ L)
    (v : ℕ → ℝ) (hv : ∀ k ∈ Finset.range L, 0 < v k) (Ik : ℕ → ℝ)
    (hIk : ∀ k ∈ Finset.range L,
      (∫ w in Set.Icc (-w₀) w₀,
          ‖logPoly moebiusCoeff (geomCofactorBlockAt A₁ B₁ R η k) w‖ ^ 2) ≤ Ik k) :
    (∫ w in Set.Icc (-w₀) w₀,
        ‖primeBlockPoly B w‖ ^ 2 * ‖omegaWeightedMoebiusPoly Q (Finset.Icc A₁ B₁) w‖ ^ 2)
      ≤ (B.card : ℝ) ^ 2
        * (2 * ((∑ k ∈ Finset.range L, 1 / v k)
              * ∑ k ∈ Finset.range L, v k
                  * (((geomBlock Q R (1 + η) k).card : ℝ) ^ 2 * Ik k))
          + 2 * ∫ w in Set.Icc (-w₀) w₀,
              ‖ladderProductDefect Q A₁ B₁ R η L w‖ ^ 2) := by
  classical
  have hsub : Set.Icc (-w₀) w₀ ⊆ Set.Icc (-W) W := Set.Icc_subset_Icc (by linarith) hwW
  have hBf : ∀ w ∈ Set.Icc (-w₀) w₀, ‖primeBlockPoly B w‖ ≤ (B.card : ℝ) := by
    intro w _
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun p _ => norm_moebiusPhase_le_one w p).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  have hstep1 := setIntegral_normSq_mul_le_of_bound
    (F := fun w => primeBlockPoly B w)
    (G := fun w => omegaWeightedMoebiusPoly Q (Finset.Icc A₁ B₁) w)
    (continuous_primeBlockPoly B) (continuous_omegaWeightedMoebiusPoly Q _)
    measurableSet_Icc hsub hBf
  have hVk : ∀ k ∈ Finset.range L, ∀ w ∈ Set.Icc (-w₀) w₀,
      ‖primeBlockPoly (geomBlock Q R (1 + η) k) w‖ ≤ ((geomBlock Q R (1 + η) k).card : ℝ) := by
    intro k _ w _
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun p _ => norm_moebiusPhase_le_one w p).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  have hchain := setIntegral_normSq_omegaWeighted_le_blocks (Q := Q) (A₁ := A₁) (B₁ := B₁)
    (W := W) hR hη hL hQprime hQrange v hv
    (fun k => ((geomBlock Q R (1 + η) k).card : ℝ)) Ik measurableSet_Icc hsub hVk hIk
  exact hstep1.trans (mul_le_mul_of_nonneg_left hchain (sq_nonneg _))

/-- **One short block, disc plus annulus.** -/
theorem section4_block_disc_ann {B Q : Finset ℕ} {A₁ B₁ : ℕ} {W w₀ : ℝ} (hwW : w₀ ≤ W)
    {Ddisc Dann : ℝ}
    (hdisc : (∫ w in Set.Icc (-w₀) w₀,
        ‖primeBlockPoly B w‖ ^ 2 * ‖omegaWeightedMoebiusPoly Q (Finset.Icc A₁ B₁) w‖ ^ 2) ≤ Ddisc)
    (hann : (∫ w in windowAnnulus w₀ W,
        ‖primeBlockPoly B w‖ ^ 2 * ‖omegaWeightedMoebiusPoly Q (Finset.Icc A₁ B₁) w‖ ^ 2)
      ≤ Dann) :
    (∫ w in Set.Icc (-W) W,
        ‖primeBlockPoly B w‖ ^ 2 * ‖omegaWeightedMoebiusPoly Q (Finset.Icc A₁ B₁) w‖ ^ 2)
      ≤ Ddisc + Dann := by
  have hcont : Continuous fun w : ℝ =>
      ‖primeBlockPoly B w‖ ^ 2 * ‖omegaWeightedMoebiusPoly Q (Finset.Icc A₁ B₁) w‖ ^ 2 :=
    (((continuous_primeBlockPoly B).norm).pow 2).mul
      (((continuous_omegaWeightedMoebiusPoly Q _).norm).pow 2)
  rw [setIntegral_Icc_split hcont hwW]
  exact add_le_add hdisc hann

end

end RHTower.Sieve
