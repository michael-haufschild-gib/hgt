import GaloisForLFunctions.RHTower.Sieve.RamareBlockSplit

/-!
# The Ramaré block split over a measurable set

`Sieve/RamareBlockSplit.integral_normSq_ramareBilinear_le_blocks` splits the bilinear form's mean
square over a symmetric window.  Matomäki–Radziwiłł's frequency partition needs the same split over
an arbitrary measurable part of that window, because the pointwise bound for the prime blocks is
available on one part by definition and has to be replaced on the other.

Nothing changes in the argument: the Cauchy–Schwarz over blocks is pointwise, and the only
analytic input is that a continuous function is integrable on a subset of a compact interval.
-/

namespace RHTower.Sieve

open MeasureTheory Finset

noncomputable section

/-- **The Ramaré block split over a measurable set.** -/
theorem setIntegral_normSq_ramareBilinear_le_blocks {P : Finset ℕ} (M : ℕ) {W : ℝ}
    {E : Set ℝ} (hEm : MeasurableSet E) (hEs : E ⊆ Set.Icc (-W) W)
    {ι : Type*} [DecidableEq ι] (I : Finset ι) (B : ι → Finset ℕ)
    (hdisj : (I : Set ι).PairwiseDisjoint B) (hcover : I.biUnion B = P) :
    (∫ w in E, ‖ramareBilinear P M w‖ ^ 2)
      ≤ (I.card : ℝ) * ∑ i ∈ I, ∫ w in E, ‖ramareBlock P M (B i) w‖ ^ 2 := by
  classical
  have hpt : ∀ w : ℝ, ‖ramareBilinear P M w‖ ^ 2
      ≤ (I.card : ℝ) * ∑ i ∈ I, ‖ramareBlock P M (B i) w‖ ^ 2 := by
    intro w
    rw [ramareBilinear_eq_sum_blocks M w I B hdisj hcover]
    have h1 : ‖∑ i ∈ I, ramareBlock P M (B i) w‖ ≤ ∑ i ∈ I, ‖ramareBlock P M (B i) w‖ :=
      norm_sum_le _ _
    have h2 : (∑ i ∈ I, ‖ramareBlock P M (B i) w‖) ^ 2
        ≤ (I.card : ℝ) * ∑ i ∈ I, ‖ramareBlock P M (B i) w‖ ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    have h3 : ‖∑ i ∈ I, ramareBlock P M (B i) w‖ ^ 2
        ≤ (∑ i ∈ I, ‖ramareBlock P M (B i) w‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    linarith
  have hcont : Continuous fun w : ℝ => ‖ramareBilinear P M w‖ ^ 2 :=
    ((continuous_ramareBilinear P M).norm).pow 2
  have hcontB : ∀ i : ι, Continuous fun w : ℝ => ‖ramareBlock P M (B i) w‖ ^ 2 := fun i =>
    ((continuous_ramareBlock P M (B i)).norm).pow 2
  have hcontS : Continuous fun w : ℝ =>
      (I.card : ℝ) * ∑ i ∈ I, ‖ramareBlock P M (B i) w‖ ^ 2 :=
    (continuous_finsetSum I fun i _ => hcontB i).const_mul _
  have hint1 : IntegrableOn (fun w : ℝ => ‖ramareBilinear P M w‖ ^ 2) E volume :=
    (hcont.integrableOn_Icc (a := -W) (b := W)).mono_set hEs
  have hint2 : IntegrableOn (fun w : ℝ =>
      (I.card : ℝ) * ∑ i ∈ I, ‖ramareBlock P M (B i) w‖ ^ 2) E volume :=
    (hcontS.integrableOn_Icc (a := -W) (b := W)).mono_set hEs
  have hmono := setIntegral_mono_on hint1 hint2 hEm (fun w _ => hpt w)
  refine hmono.trans (le_of_eq ?_)
  rw [integral_const_mul]
  congr 1
  refine integral_finsetSum I fun i _ => ?_
  exact ((hcontB i).integrableOn_Icc (a := -W) (b := W)).mono_set hEs

/-- **The Ramaré block split over a measurable set, geometric ladder.** -/
theorem setIntegral_normSq_ramareBilinear_le_geomLadder {P : Finset ℕ} (M : ℕ) {W Q r : ℝ}
    (hQ : 0 < Q) (hr : 1 ≤ r) {L : ℕ} (hL : 1 ≤ L)
    (hcover : ∀ p ∈ P, Q < (p : ℝ) ∧ (p : ℝ) ≤ Q * r ^ L)
    {E : Set ℝ} (hEm : MeasurableSet E) (hEs : E ⊆ Set.Icc (-W) W) :
    (∫ w in E, ‖ramareBilinear P M w‖ ^ 2)
      ≤ (L : ℝ) * ∑ j ∈ Finset.range L,
          ∫ w in E, ‖ramareBlock P M (geomBlock P Q r j) w‖ ^ 2 := by
  classical
  have h := setIntegral_normSq_ramareBilinear_le_blocks (P := P) M hEm hEs
    (Finset.range L) (geomBlock P Q r)
    (geomBlock_pairwiseDisjoint P hQ hr L) (geomBlock_biUnion_eq P Q r hL hcover)
  rwa [Finset.card_range] at h

end

end RHTower.Sieve

namespace RHTower.Sieve

open MeasureTheory Finset

noncomputable section

/-- **One Ramaré block as a product, over a measurable set.** -/
theorem setIntegral_normSq_ramareBlock_le_product {P : Finset ℕ} (M : ℕ) {B : Finset ℕ}
    (hBprime : ∀ q ∈ B, q.Prime) (C : Finset ℕ) {W : ℝ}
    {E : Set ℝ} (hEm : MeasurableSet E) (hEs : E ⊆ Set.Icc (-W) W) :
    (∫ w in E, ‖ramareBlock P M B w‖ ^ 2)
      ≤ 2 * (∫ w in E, ‖primeBlockPoly B w * logPoly (ramareCofactorCoeff P) C w‖ ^ 2)
        + 2 * (B.card : ℝ) * ∑ p ∈ B, ∫ w in E,
            ‖ramareCofactorPoly P M p w - logPoly (ramareCofactorCoeff P) C w‖ ^ 2 := by
  classical
  set G : ℝ → ℂ := fun w => logPoly (ramareCofactorCoeff P) C w with hG
  have hdecomp : ∀ w : ℝ, ramareBlock P M B w
      = primeBlockPoly B w * G w
        + ∑ p ∈ B, moebiusPhase w p * (ramareCofactorPoly P M p w - G w) := by
    intro w
    rw [ramareBlock, primeBlockPoly, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    ring
  have hpt : ∀ w : ℝ, ‖ramareBlock P M B w‖ ^ 2
      ≤ 2 * ‖primeBlockPoly B w * G w‖ ^ 2
        + 2 * (B.card : ℝ) * ∑ p ∈ B, ‖ramareCofactorPoly P M p w - G w‖ ^ 2 := by
    intro w
    rw [hdecomp w]
    have hY : ‖∑ p ∈ B, moebiusPhase w p * (ramareCofactorPoly P M p w - G w)‖
        ≤ ∑ p ∈ B, ‖ramareCofactorPoly P M p w - G w‖ := by
      refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun p hp => ?_)
      rw [norm_mul, norm_moebiusPhase_prime (hBprime p hp), one_mul]
    have hY2 : ‖∑ p ∈ B, moebiusPhase w p * (ramareCofactorPoly P M p w - G w)‖ ^ 2
        ≤ (B.card : ℝ) * ∑ p ∈ B, ‖ramareCofactorPoly P M p w - G w‖ ^ 2 := by
      refine le_trans (pow_le_pow_left₀ (norm_nonneg _) hY 2) ?_
      exact sq_sum_le_card_mul_sum_sq
    have htri := norm_add_le (primeBlockPoly B w * G w)
      (∑ p ∈ B, moebiusPhase w p * (ramareCofactorPoly P M p w - G w))
    have hsq := pow_le_pow_left₀ (norm_nonneg _) htri 2
    nlinarith [hsq, hY2, sq_nonneg (‖primeBlockPoly B w * G w‖
      - ‖∑ p ∈ B, moebiusPhase w p * (ramareCofactorPoly P M p w - G w)‖), norm_nonneg
      (∑ p ∈ B, moebiusPhase w p * (ramareCofactorPoly P M p w - G w))]
  have hcontZ : Continuous fun w : ℝ => ‖ramareBlock P M B w‖ ^ 2 :=
    ((continuous_ramareBlock P M B).norm).pow 2
  have hcontX : Continuous fun w : ℝ => ‖primeBlockPoly B w * G w‖ ^ 2 :=
    (((continuous_primeBlockPoly B).mul (continuous_logPoly _ _)).norm).pow 2
  have hcontD : ∀ p : ℕ, Continuous fun w : ℝ =>
      ‖ramareCofactorPoly P M p w - G w‖ ^ 2 := fun p =>
    ((((continuous_ramareCofactorPoly P M p).sub (continuous_logPoly _ _))).norm).pow 2
  have hcontR : Continuous fun w : ℝ =>
      2 * ‖primeBlockPoly B w * G w‖ ^ 2
        + 2 * (B.card : ℝ) * ∑ p ∈ B, ‖ramareCofactorPoly P M p w - G w‖ ^ 2 :=
    (hcontX.const_mul 2).add ((continuous_finsetSum B fun p _ => hcontD p).const_mul _)
  have hint1 : IntegrableOn (fun w : ℝ => ‖ramareBlock P M B w‖ ^ 2) E volume :=
    (hcontZ.integrableOn_Icc (a := -W) (b := W)).mono_set hEs
  have hint2 : IntegrableOn (fun w : ℝ =>
      2 * ‖primeBlockPoly B w * G w‖ ^ 2
        + 2 * (B.card : ℝ) * ∑ p ∈ B, ‖ramareCofactorPoly P M p w - G w‖ ^ 2) E volume :=
    (hcontR.integrableOn_Icc (a := -W) (b := W)).mono_set hEs
  have hmono := setIntegral_mono_on hint1 hint2 hEm (fun w _ => hpt w)
  refine hmono.trans (le_of_eq ?_)
  have hiX : IntegrableOn (fun w : ℝ => 2 * ‖primeBlockPoly B w * G w‖ ^ 2) E volume :=
    ((hcontX.const_mul 2).integrableOn_Icc (a := -W) (b := W)).mono_set hEs
  have hiD : IntegrableOn (fun w : ℝ =>
      2 * (B.card : ℝ) * ∑ p ∈ B, ‖ramareCofactorPoly P M p w - G w‖ ^ 2) E volume :=
    (((continuous_finsetSum B fun p _ => hcontD p).const_mul _).integrableOn_Icc
      (a := -W) (b := W)).mono_set hEs
  rw [integral_add hiX hiD, integral_const_mul, integral_const_mul]
  congr 1
  congr 1
  exact integral_finsetSum B fun p _ =>
    ((hcontD p).integrableOn_Icc (a := -W) (b := W)).mono_set hEs

end

end RHTower.Sieve

namespace RHTower.Sieve

open MeasureTheory Finset

noncomputable section

/-- **One geometric Ramaré block over a measurable set.**  The cofactor discrepancy is bounded by
its value over the whole window, since the integrand is nonnegative. -/
theorem setIntegral_normSq_ramareBlock_geom_le {P : Finset ℕ} (M : ℕ) {Q η W : ℝ}
    (hQ : 1 ≤ Q) (hη : 0 ≤ η) (hW : 1 ≤ W) (j : ℕ) (hPprime : ∀ q ∈ P, q.Prime)
    {E : Set ℝ} (hEm : MeasurableSet E) (hEs : E ⊆ Set.Icc (-W) W) :
    (∫ w in E, ‖ramareBlock P M (geomBlock P Q (1 + η) j) w‖ ^ 2)
      ≤ 2 * (∫ w in E,
            ‖primeBlockPoly (geomBlock P Q (1 + η) j) w
              * logPoly (ramareCofactorCoeff P) (geomCofactorBlock M Q η j) w‖ ^ 2)
        + 2 * ((geomBlock P Q (1 + η) j).card : ℝ) ^ 2
            * (2 * (5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * (M : ℝ))
                * ((((1 : ℕ) : ℝ) + ((M : ℕ) : ℝ)) * η / (Q * (1 + η) ^ j) + 4
                  + (((M : ℕ) : ℝ) / (Q * (1 + η) ^ j) ^ 2 + 1))) := by
  classical
  set B : Finset ℕ := geomBlock P Q (1 + η) j with hB
  set Qj : ℝ := Q * (1 + η) ^ j with hQj
  have hr1 : (1 : ℝ) ≤ 1 + η := by linarith
  have hQj1 : (1 : ℝ) ≤ Qj := by
    rw [hQj]
    have hpow : (1 : ℝ) ≤ (1 + η) ^ j := one_le_pow₀ hr1
    nlinarith [hQ, hpow]
  have hBprime : ∀ q ∈ B, q.Prime := fun q hq =>
    hPprime q (geomBlock_subset P Q (1 + η) j hq)
  have hrange : ∀ p ∈ B, 0 < p ∧ Qj < (p : ℝ) ∧ (p : ℝ) ≤ Qj * (1 + η) := by
    intro p hp
    have hq := hBprime p hp
    rw [hB, geomBlock, Finset.mem_filter] at hp
    obtain ⟨-, hlo, hhi⟩ := hp
    refine ⟨hq.pos, hlo, ?_⟩
    have hpow : Q * (1 + η) ^ (j + 1) = Qj * (1 + η) := by
      rw [hQj, pow_succ]; ring
    rwa [hpow] at hhi
  have hprod := setIntegral_normSq_ramareBlock_le_product (P := P) M hBprime
    (geomCofactorBlock M Q η j) hEm hEs
  have hterm : ∀ p ∈ B, (∫ w in E,
      ‖ramareCofactorPoly P M p w
        - logPoly (ramareCofactorCoeff P) (geomCofactorBlock M Q η j) w‖ ^ 2)
      ≤ 2 * (5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * (M : ℝ))
          * ((((1 : ℕ) : ℝ) + ((M : ℕ) : ℝ)) * η / Qj + 4 + (((M : ℕ) : ℝ) / Qj ^ 2 + 1)) := by
    intro p hp
    obtain ⟨hp0, hplo, hphi⟩ := hrange p hp
    have hcont : Continuous fun w : ℝ =>
        ‖ramareCofactorPoly P M p w
          - logPoly (ramareCofactorCoeff P) (geomCofactorBlock M Q η j) w‖ ^ 2 :=
      ((((continuous_ramareCofactorPoly P M p).sub (continuous_logPoly _ _))).norm).pow 2
    have hmono : (∫ w in E, ‖ramareCofactorPoly P M p w
          - logPoly (ramareCofactorCoeff P) (geomCofactorBlock M Q η j) w‖ ^ 2)
        ≤ ∫ w in Set.Icc (-W) W, ‖ramareCofactorPoly P M p w
          - logPoly (ramareCofactorCoeff P) (geomCofactorBlock M Q η j) w‖ ^ 2 := by
      refine MeasureTheory.setIntegral_mono_set (hcont.integrableOn_Icc (a := -W) (b := W))
        (Filter.Eventually.of_forall fun w => by positivity)
        (Filter.Eventually.of_forall hEs)
    exact hmono.trans (integral_normSq_cofactor_sub_common_le (P := P) M hQj1 hη hW hp0 hplo hphi)
  have hsum : (∑ p ∈ B, ∫ w in E,
      ‖ramareCofactorPoly P M p w
        - logPoly (ramareCofactorCoeff P) (geomCofactorBlock M Q η j) w‖ ^ 2)
      ≤ (B.card : ℝ)
          * (2 * (5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * (M : ℝ))
              * ((((1 : ℕ) : ℝ) + ((M : ℕ) : ℝ)) * η / Qj + 4
                + (((M : ℕ) : ℝ) / Qj ^ 2 + 1))) := by
    have h := Finset.sum_le_sum hterm
    rw [Finset.sum_const, nsmul_eq_mul] at h
    exact h
  have hmul := mul_le_mul_of_nonneg_left hsum
    (by positivity : (0 : ℝ) ≤ 2 * (B.card : ℝ))
  refine hprod.trans ?_
  have hval : 2 * (B.card : ℝ)
      * ((B.card : ℝ)
          * (2 * (5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * (M : ℝ))
              * ((((1 : ℕ) : ℝ) + ((M : ℕ) : ℝ)) * η / Qj + 4 + (((M : ℕ) : ℝ) / Qj ^ 2 + 1))))
      = 2 * (B.card : ℝ) ^ 2
          * (2 * (5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * (M : ℝ))
              * ((((1 : ℕ) : ℝ) + ((M : ℕ) : ℝ)) * η / Qj + 4
                + (((M : ℕ) : ℝ) / Qj ^ 2 + 1))) := by ring
  rw [hval] at hmul
  linarith [hmul]

/-- **The whole bilinear mean square over a measurable set, along the ladder.** -/
theorem setIntegral_normSq_ramareBilinear_le_ladder_assembled {P : Finset ℕ} (M : ℕ) {Q η W : ℝ}
    (hQ : 1 ≤ Q) (hη : 0 ≤ η) (hW : 1 ≤ W) {L : ℕ} (hL : 1 ≤ L)
    (hPprime : ∀ q ∈ P, q.Prime)
    (hP : ∀ p ∈ P, Q < (p : ℝ) ∧ (p : ℝ) ≤ Q * (1 + η) ^ L)
    {E : Set ℝ} (hEm : MeasurableSet E) (hEs : E ⊆ Set.Icc (-W) W) :
    (∫ w in E, ‖ramareBilinear P M w‖ ^ 2)
      ≤ (L : ℝ) * ∑ j ∈ Finset.range L,
          (2 * (∫ w in E,
                ‖primeBlockPoly (geomBlock P Q (1 + η) j) w
                  * logPoly (ramareCofactorCoeff P) (geomCofactorBlock M Q η j) w‖ ^ 2)
            + 2 * ((geomBlock P Q (1 + η) j).card : ℝ) ^ 2
                * (2 * (5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * (M : ℝ))
                    * ((((1 : ℕ) : ℝ) + ((M : ℕ) : ℝ)) * η / (Q * (1 + η) ^ j) + 4
                      + (((M : ℕ) : ℝ) / (Q * (1 + η) ^ j) ^ 2 + 1)))) := by
  have hQ0 : (0 : ℝ) < Q := lt_of_lt_of_le zero_lt_one hQ
  have hr1 : (1 : ℝ) ≤ 1 + η := by linarith
  have hladder := setIntegral_normSq_ramareBilinear_le_geomLadder (P := P) M hQ0 hr1 hL hP hEm hEs
  refine hladder.trans ?_
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => ?_) (Nat.cast_nonneg L)
  exact setIntegral_normSq_ramareBlock_geom_le M hQ hη hW j hPprime hEm hEs

end

end RHTower.Sieve
