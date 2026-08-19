import GaloisForLFunctions.RHTower.Sieve.Section4QSide

/-!
# One block of exposé §4 with both designated variables

Combining the exceptional-set split (`Sieve/ExceptionalSplitGen`) with the long-prime ladder over
the exceptional set (`Sieve/Section4QSide`) gives the estimate §4 actually uses:

```text
   ∫_{|w|≤W} ‖∑_{p∈B}μ(p)p^{iw}‖²·‖∑_m μ(m)ω_Q(m)m^{iw}‖² dw
     ≤ V_P²·∫_{|w|≤W}‖∑_m μ(m)ω_Q(m)m^{iw}‖²                              (Lemma 2.4)
       + (#B)²·[ 2(∑_k 1/v_k)·∑_k v_k·V_k²·I_k  +  2·(ladder defect) ]     (Lemmas 2.3, 2.5, 2.6)
```

`V_P` is the cancellation threshold of `(35)`, `V_k` the Lemma 2.3 saving on the `k`-th long prime
block, and `I_k` the mean square of the innermost cofactor over the exceptional set — the quantity
Halász–Montgomery bounds in terms of the measure of that set.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- The exceptional set of a short prime block, in the Gallagher variable. -/
def shortExceptional (B : Finset ℕ) (W VP : ℝ) : Set ℝ :=
  Set.Icc (-W) W ∩ {w : ℝ | VP ≤ ‖primeBlockPoly B w‖}

theorem measurableSet_shortExceptional (B : Finset ℕ) (W VP : ℝ) :
    MeasurableSet (shortExceptional B W VP) :=
  measurableSet_Icc.inter
    (measurableSet_le measurable_const ((continuous_primeBlockPoly B).norm).measurable)

theorem shortExceptional_subset (B : Finset ℕ) (W VP : ℝ) :
    shortExceptional B W VP ⊆ Set.Icc (-W) W := fun _ hw => hw.1

/-- **One block of §4, both designated variables.** -/
theorem section4_block_full {B Q : Finset ℕ} {A₁ B₁ : ℕ}
    {R η W VP : ℝ} (hR : 0 < R) (hη : 0 ≤ η) {L : ℕ} (hL : 1 ≤ L)
    (hQprime : ∀ q ∈ Q, q.Prime)
    (hQrange : ∀ q ∈ Q, R < (q : ℝ) ∧ (q : ℝ) ≤ R * (1 + η) ^ L)
    (v : ℕ → ℝ) (hv : ∀ k ∈ Finset.range L, 0 < v k) (Vk Ik : ℕ → ℝ)
    (hVk : ∀ k ∈ Finset.range L, ∀ w ∈ shortExceptional B W VP,
      ‖primeBlockPoly (geomBlock Q R (1 + η) k) w‖ ≤ Vk k)
    (hIk : ∀ k ∈ Finset.range L,
      (∫ w in shortExceptional B W VP,
          ‖logPoly moebiusCoeff (geomCofactorBlockAt A₁ B₁ R η k) w‖ ^ 2) ≤ Ik k) :
    (∫ w in Set.Icc (-W) W,
        ‖primeBlockPoly B w‖ ^ 2 * ‖omegaWeightedMoebiusPoly Q (Finset.Icc A₁ B₁) w‖ ^ 2)
      ≤ VP ^ 2 * (∫ w in Set.Icc (-W) W, ‖omegaWeightedMoebiusPoly Q (Finset.Icc A₁ B₁) w‖ ^ 2)
        + (B.card : ℝ) ^ 2
          * (2 * ((∑ k ∈ Finset.range L, 1 / v k)
                * ∑ k ∈ Finset.range L, v k * (Vk k ^ 2 * Ik k))
            + 2 * ∫ w in shortExceptional B W VP,
                ‖ladderProductDefect Q A₁ B₁ R η L w‖ ^ 2) := by
  classical
  have hBf : ∀ w : ℝ, ‖primeBlockPoly B w‖ ≤ (B.card : ℝ) := by
    intro w
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun p _ => norm_moebiusPhase_le_one w p).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  have hsplit := integral_normSq_mul_split_exceptional_gen
    (F := fun w => primeBlockPoly B w)
    (G := fun w => omegaWeightedMoebiusPoly Q (Finset.Icc A₁ B₁) w)
    (continuous_primeBlockPoly B) (continuous_omegaWeightedMoebiusPoly Q _)
    (W := W) (V := VP) (Bf := (B.card : ℝ)) hBf
  rw [show Set.Icc (-W) W ∩ {w : ℝ | VP ≤ ‖primeBlockPoly B w‖} = shortExceptional B W VP from
    rfl] at hsplit
  have hchain := setIntegral_normSq_omegaWeighted_le_blocks (Q := Q) (A₁ := A₁) (B₁ := B₁)
    (W := W) hR hη hL hQprime hQrange v hv Vk Ik
    (measurableSet_shortExceptional B W VP) (shortExceptional_subset B W VP) hVk hIk
  have hB2 : (0 : ℝ) ≤ (B.card : ℝ) ^ 2 := sq_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hchain hB2
  exact hsplit.trans (by linarith [hmul])

/-! ## The same estimate over an arbitrary part of the window -/

/-- The exceptional set of a short prime block, relative to a part of the window. -/
def shortExceptionalOn (S : Set ℝ) (B : Finset ℕ) (VP : ℝ) : Set ℝ :=
  S ∩ {w : ℝ | VP ≤ ‖primeBlockPoly B w‖}

theorem measurableSet_shortExceptionalOn {S : Set ℝ} (hSm : MeasurableSet S) (B : Finset ℕ)
    (VP : ℝ) : MeasurableSet (shortExceptionalOn S B VP) :=
  hSm.inter (measurableSet_le measurable_const ((continuous_primeBlockPoly B).norm).measurable)

theorem shortExceptionalOn_subset {S : Set ℝ} {W : ℝ} (hSs : S ⊆ Set.Icc (-W) W) (B : Finset ℕ)
    (VP : ℝ) : shortExceptionalOn S B VP ⊆ Set.Icc (-W) W := fun _ hw => hSs hw.1

/-- **One block of §4, over an arbitrary measurable part of the window.**  The annulus form: the
Route-T bound for the long prime blocks is only available away from the origin, so §4 is run on
`{w₀ ≤ |w| ≤ W}` and the disc is handled separately. -/
theorem section4_block_full_on {B Q : Finset ℕ} {A₁ B₁ : ℕ}
    {R η W VP : ℝ} (hR : 0 < R) (hη : 0 ≤ η) {L : ℕ} (hL : 1 ≤ L)
    (hQprime : ∀ q ∈ Q, q.Prime)
    (hQrange : ∀ q ∈ Q, R < (q : ℝ) ∧ (q : ℝ) ≤ R * (1 + η) ^ L)
    (v : ℕ → ℝ) (hv : ∀ k ∈ Finset.range L, 0 < v k) (Vk Ik : ℕ → ℝ)
    {S : Set ℝ} (hSm : MeasurableSet S) (hSs : S ⊆ Set.Icc (-W) W)
    (hVk : ∀ k ∈ Finset.range L, ∀ w ∈ shortExceptionalOn S B VP,
      ‖primeBlockPoly (geomBlock Q R (1 + η) k) w‖ ≤ Vk k)
    (hIk : ∀ k ∈ Finset.range L,
      (∫ w in shortExceptionalOn S B VP,
          ‖logPoly moebiusCoeff (geomCofactorBlockAt A₁ B₁ R η k) w‖ ^ 2) ≤ Ik k) :
    (∫ w in S,
        ‖primeBlockPoly B w‖ ^ 2 * ‖omegaWeightedMoebiusPoly Q (Finset.Icc A₁ B₁) w‖ ^ 2)
      ≤ VP ^ 2 * (∫ w in S, ‖omegaWeightedMoebiusPoly Q (Finset.Icc A₁ B₁) w‖ ^ 2)
        + (B.card : ℝ) ^ 2
          * (2 * ((∑ k ∈ Finset.range L, 1 / v k)
                * ∑ k ∈ Finset.range L, v k * (Vk k ^ 2 * Ik k))
            + 2 * ∫ w in shortExceptionalOn S B VP,
                ‖ladderProductDefect Q A₁ B₁ R η L w‖ ^ 2) := by
  classical
  have hBf : ∀ w : ℝ, ‖primeBlockPoly B w‖ ≤ (B.card : ℝ) := by
    intro w
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun p _ => norm_moebiusPhase_le_one w p).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  have hsplit := setIntegral_normSq_mul_split_exceptional_set
    (F := fun w => primeBlockPoly B w)
    (G := fun w => omegaWeightedMoebiusPoly Q (Finset.Icc A₁ B₁) w)
    (continuous_primeBlockPoly B) (continuous_omegaWeightedMoebiusPoly Q _)
    hSm (W := W) (V := VP) (Bf := (B.card : ℝ)) hSs hBf
  rw [show S ∩ {w : ℝ | VP ≤ ‖primeBlockPoly B w‖} = shortExceptionalOn S B VP from
    rfl] at hsplit
  have hchain := setIntegral_normSq_omegaWeighted_le_blocks (Q := Q) (A₁ := A₁) (B₁ := B₁)
    (W := W) hR hη hL hQprime hQrange v hv Vk Ik
    (measurableSet_shortExceptionalOn hSm B VP) (shortExceptionalOn_subset hSs B VP) hVk hIk
  have hB2 : (0 : ℝ) ≤ (B.card : ℝ) ^ 2 := sq_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hchain hB2
  exact hsplit.trans (by linarith [hmul])

end

end RHTower.Sieve
