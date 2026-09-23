import GaloisForLFunctions.RHTower.Sieve.SetIntegralBlockSplit
import GaloisForLFunctions.RHTower.Sieve.LogPolySetScaling
import GaloisForLFunctions.RHTower.Sieve.LadderHarmonicSplit
import GaloisForLFunctions.RHTower.Sieve.OmegaWeightedLadderBound

/-!
# The long-prime side of the exceptional case

On the exceptional set of exposé §4 the short prime polynomial is bounded trivially, and the saving
has to come from the *long* designated primes: the range `Q` is chosen so high that Lemma 2.3
applies to each of its blocks.  This module carries the long ladder over a measurable set:

```text
   ∫_E ‖∑_{m} μ(m)ω_Q(m) m^{iw}‖² dw
     ≤ 2(∑_k 1/v_k)·∑_k v_k·V_k²·∫_E‖cofactor_k‖²  +  2·(ladder defect) ,
```

with `V_k` any pointwise bound for the `k`-th long prime block on `E`.  The defect is the corpus's
`Sieve/LadderProductDefect`, bounded over the whole window since `E` sits inside it.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

theorem continuous_ladderProductDefect' (P : Finset ℕ) (A₀ B₀ : ℕ) (R η : ℝ) (L : ℕ) :
    Continuous (ladderProductDefect P A₀ B₀ R η L) := by
  refine continuous_finsetSum _ fun x _ => ?_
  exact (continuous_moebiusPhase _).mul (continuous_logPoly _ _)

/-- **The long ladder over a measurable set.** -/
theorem setIntegral_normSq_omegaWeighted_le_ladder {Q : Finset ℕ} {A₁ B₁ : ℕ}
    {R η W : ℝ} (hR : 0 < R) (hη : 0 ≤ η) {L : ℕ} (hL : 1 ≤ L)
    (hQprime : ∀ q ∈ Q, q.Prime)
    (hQrange : ∀ q ∈ Q, R < (q : ℝ) ∧ (q : ℝ) ≤ R * (1 + η) ^ L)
    (v : ℕ → ℝ) (hv : ∀ k ∈ Finset.range L, 0 < v k)
    {E : Set ℝ} (hEm : MeasurableSet E) (hEs : E ⊆ Set.Icc (-W) W) :
    (∫ w in E, ‖omegaWeightedMoebiusPoly Q (Finset.Icc A₁ B₁) w‖ ^ (2 : ℕ))
      ≤ 2 * ((∑ k ∈ Finset.range L, 1 / v k)
          * ∑ k ∈ Finset.range L, v k
              * ∫ w in E, ‖primeBlockPoly (geomBlock Q R (1 + η) k) w‖ ^ (2 : ℕ)
                  * ‖logPoly moebiusCoeff (geomCofactorBlockAt A₁ B₁ R η k) w‖ ^ (2 : ℕ))
        + 2 * ∫ w in E, ‖ladderProductDefect Q A₁ B₁ R η L w‖ ^ (2 : ℕ) := by
  classical
  have hdec : ∀ w : ℝ, omegaWeightedMoebiusPoly Q (Finset.Icc A₁ B₁) w
      = ladderProductPoly Q A₁ B₁ R η L w + (-(ladderProductDefect Q A₁ B₁ R η L w)) := by
    intro w
    have h := ladderProductPoly_sub_omegaWeighted_eq A₁ B₁ hR hη hL hQprime hQrange w
    linear_combination -h
  rw [MeasureTheory.setIntegral_congr_fun hEm fun w _ => by rw [hdec w]]
  have hsplit := setIntegral_normSq_add_le (F := ladderProductPoly Q A₁ B₁ R η L)
    (G := fun w => -(ladderProductDefect Q A₁ B₁ R η L w))
    (continuous_ladderProductPoly Q A₁ B₁ R η L)
    ((continuous_ladderProductDefect' Q A₁ B₁ R η L).neg) hEm hEs
  have hneg : (∫ w in E, ‖-(ladderProductDefect Q A₁ B₁ R η L w)‖ ^ (2 : ℕ))
      = ∫ w in E, ‖ladderProductDefect Q A₁ B₁ R η L w‖ ^ (2 : ℕ) := by
    refine MeasureTheory.setIntegral_congr_fun hEm fun w _ => ?_
    rw [norm_neg]
  rw [hneg] at hsplit
  have hharm := setIntegral_normSq_sum_mul_le_weighted (Finset.range L) v hv
    (fun k w => primeBlockPoly (geomBlock Q R (1 + η) k) w)
    (fun k w => logPoly moebiusCoeff (geomCofactorBlockAt A₁ B₁ R η k) w)
    (fun k => continuous_primeBlockPoly _) (fun k => continuous_logPoly _ _) hEm hEs
  have hlad : (∫ w in E, ‖ladderProductPoly Q A₁ B₁ R η L w‖ ^ (2 : ℕ))
      ≤ (∑ k ∈ Finset.range L, 1 / v k)
        * ∑ k ∈ Finset.range L, v k
            * ∫ w in E, ‖primeBlockPoly (geomBlock Q R (1 + η) k) w‖ ^ (2 : ℕ)
                * ‖logPoly moebiusCoeff (geomCofactorBlockAt A₁ B₁ R η k) w‖ ^ (2 : ℕ) := by
    refine le_trans (le_of_eq ?_) hharm
    refine MeasureTheory.setIntegral_congr_fun hEm fun w _ => ?_
    rw [ladderProductPoly]
  linarith [hsplit, hlad]

/-- **The long ladder over a measurable set, with the Lemma 2.3 saving applied.**  This is the
factor that replaces the trivial cofactor bound in the exceptional case of §4. -/
theorem setIntegral_normSq_omegaWeighted_le_blocks {Q : Finset ℕ} {A₁ B₁ : ℕ}
    {R η W : ℝ} (hR : 0 < R) (hη : 0 ≤ η) {L : ℕ} (hL : 1 ≤ L)
    (hQprime : ∀ q ∈ Q, q.Prime)
    (hQrange : ∀ q ∈ Q, R < (q : ℝ) ∧ (q : ℝ) ≤ R * (1 + η) ^ L)
    (v : ℕ → ℝ) (hv : ∀ k ∈ Finset.range L, 0 < v k) (Vk Ik : ℕ → ℝ)
    {E : Set ℝ} (hEm : MeasurableSet E) (hEs : E ⊆ Set.Icc (-W) W)
    (hVk : ∀ k ∈ Finset.range L, ∀ w ∈ E,
      ‖primeBlockPoly (geomBlock Q R (1 + η) k) w‖ ≤ Vk k)
    (hIk : ∀ k ∈ Finset.range L,
      (∫ w in E, ‖logPoly moebiusCoeff (geomCofactorBlockAt A₁ B₁ R η k) w‖ ^ (2 : ℕ)) ≤ Ik k) :
    (∫ w in E, ‖omegaWeightedMoebiusPoly Q (Finset.Icc A₁ B₁) w‖ ^ (2 : ℕ))
      ≤ 2 * ((∑ k ∈ Finset.range L, 1 / v k)
            * ∑ k ∈ Finset.range L, v k * (Vk k ^ (2 : ℕ) * Ik k))
        + 2 * ∫ w in E, ‖ladderProductDefect Q A₁ B₁ R η L w‖ ^ (2 : ℕ) := by
  classical
  have hstep2 := setIntegral_normSq_omegaWeighted_le_ladder (Q := Q) (A₁ := A₁) (B₁ := B₁)
    hR hη hL hQprime hQrange v hv hEm hEs
  have hblock : ∀ k ∈ Finset.range L,
      v k * (∫ w in E, ‖primeBlockPoly (geomBlock Q R (1 + η) k) w‖ ^ (2 : ℕ)
              * ‖logPoly moebiusCoeff (geomCofactorBlockAt A₁ B₁ R η k) w‖ ^ (2 : ℕ))
        ≤ v k * (Vk k ^ (2 : ℕ) * Ik k) := by
    intro k hk
    refine mul_le_mul_of_nonneg_left ?_ (hv k hk).le
    have hb := setIntegral_normSq_mul_le_of_bound
      (F := fun w => primeBlockPoly (geomBlock Q R (1 + η) k) w)
      (G := fun w => logPoly moebiusCoeff (geomCofactorBlockAt A₁ B₁ R η k) w)
      (continuous_primeBlockPoly _) (continuous_logPoly _ _) hEm hEs (hVk k hk)
    exact hb.trans (mul_le_mul_of_nonneg_left (hIk k hk) (sq_nonneg _))
  have hsum := Finset.sum_le_sum hblock
  have hmass : (0 : ℝ) ≤ ∑ k ∈ Finset.range L, 1 / v k :=
    Finset.sum_nonneg fun k hk => div_nonneg zero_le_one (hv k hk).le
  refine hstep2.trans ?_
  have := mul_le_mul_of_nonneg_left hsum hmass
  linarith [this]


/-- **The exceptional case of §4, three factors.**  The short prime polynomial is bounded by its
trivial size, the long ladder carries the Lemma 2.3 saving `V k`, and what is left is the mean
square of the innermost cofactor over the exceptional set. -/
theorem setIntegral_normSq_short_long_le {B Q : Finset ℕ} {A₁ B₁ : ℕ}
    {R η W : ℝ} (hR : 0 < R) (hη : 0 ≤ η) {L : ℕ} (hL : 1 ≤ L)
    (hQprime : ∀ q ∈ Q, q.Prime)
    (hQrange : ∀ q ∈ Q, R < (q : ℝ) ∧ (q : ℝ) ≤ R * (1 + η) ^ L)
    (v : ℕ → ℝ) (hv : ∀ k ∈ Finset.range L, 0 < v k)
    (Vk Ik : ℕ → ℝ)
    {E : Set ℝ} (hEm : MeasurableSet E) (hEs : E ⊆ Set.Icc (-W) W)
    (hVk : ∀ k ∈ Finset.range L, ∀ w ∈ E,
      ‖primeBlockPoly (geomBlock Q R (1 + η) k) w‖ ≤ Vk k)
    (hIk : ∀ k ∈ Finset.range L,
      (∫ w in E, ‖logPoly moebiusCoeff (geomCofactorBlockAt A₁ B₁ R η k) w‖ ^ (2 : ℕ)) ≤ Ik k) :
    (∫ w in E,
        ‖primeBlockPoly B w‖ ^ (2 : ℕ) * ‖omegaWeightedMoebiusPoly Q (Finset.Icc A₁ B₁) w‖ ^ (2 : ℕ))
      ≤ (B.card : ℝ) ^ (2 : ℕ)
        * (2 * ((∑ k ∈ Finset.range L, 1 / v k)
              * ∑ k ∈ Finset.range L, v k * (Vk k ^ (2 : ℕ) * Ik k))
          + 2 * ∫ w in E, ‖ladderProductDefect Q A₁ B₁ R η L w‖ ^ (2 : ℕ)) := by
  classical
  have hBf : ∀ w ∈ E, ‖primeBlockPoly B w‖ ≤ (B.card : ℝ) := by
    intro w _
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun p _ => norm_moebiusPhase_le_one w p).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  have hstep1 := setIntegral_normSq_mul_le_of_bound
    (F := fun w => primeBlockPoly B w)
    (G := fun w => omegaWeightedMoebiusPoly Q (Finset.Icc A₁ B₁) w)
    (continuous_primeBlockPoly B) (continuous_omegaWeightedMoebiusPoly Q _) hEm hEs hBf
  have hchain := setIntegral_normSq_omegaWeighted_le_blocks (Q := Q) (A₁ := A₁) (B₁ := B₁)
    hR hη hL hQprime hQrange v hv Vk Ik hEm hEs hVk hIk
  have hB2 : (0 : ℝ) ≤ (B.card : ℝ) ^ (2 : ℕ) := sq_nonneg _
  exact hstep1.trans (mul_le_mul_of_nonneg_left hchain hB2)

end

end RHTower.Sieve
