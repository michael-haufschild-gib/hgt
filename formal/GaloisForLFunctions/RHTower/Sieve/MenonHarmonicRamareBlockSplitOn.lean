import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicRamareBlockSplit

/-!
# Harmonic Ramaré blocks on measurable frequency sets

Menon's final-frequency argument partitions a compact frequency window into measurable pieces.
These are the measurable-set forms of the exact harmonic block split and its weighted
block-to-product replacement.
-/

namespace RHTower.Sieve

open MeasureTheory Finset

noncomputable section

/-- The harmonic Ramaré block split over a measurable part of a compact frequency window. -/
theorem setIntegral_normSq_harmonicRamareBilinear_le_blocks {P s : Finset ℕ} {W : ℝ}
    {E : Set ℝ} (hEm : MeasurableSet E) (hEs : E ⊆ Set.Icc (-W) W)
    {ι : Type*} [DecidableEq ι] (I : Finset ι) (B : ι → Finset ℕ)
    (hdisj : (I : Set ι).PairwiseDisjoint B) (hcover : I.biUnion B = P) :
    (∫ w in E, ‖harmonicRamareBilinear P s w‖ ^ (2 : ℕ))
      ≤ (I.card : ℝ) * ∑ i ∈ I,
          ∫ w in E, ‖harmonicRamareBlock P s (B i) w‖ ^ (2 : ℕ) := by
  classical
  have hpt : ∀ w : ℝ, ‖harmonicRamareBilinear P s w‖ ^ (2 : ℕ)
      ≤ (I.card : ℝ) * ∑ i ∈ I, ‖harmonicRamareBlock P s (B i) w‖ ^ (2 : ℕ) := by
    intro w
    rw [harmonicRamareBilinear_eq_sum_blocks w I B hdisj hcover]
    have h1 : ‖∑ i ∈ I, harmonicRamareBlock P s (B i) w‖
        ≤ ∑ i ∈ I, ‖harmonicRamareBlock P s (B i) w‖ := norm_sum_le _ _
    have h2 : (∑ i ∈ I, ‖harmonicRamareBlock P s (B i) w‖) ^ (2 : ℕ)
        ≤ (I.card : ℝ) * ∑ i ∈ I, ‖harmonicRamareBlock P s (B i) w‖ ^ (2 : ℕ) :=
      sq_sum_le_card_mul_sum_sq
    exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2
  have hcont : Continuous fun w : ℝ => ‖harmonicRamareBilinear P s w‖ ^ (2 : ℕ) := by
    refine (continuous_finsetSum P fun p _ => ?_).norm.pow 2
    exact ((continuous_moebiusPhase p).div_const _).mul (continuous_logPoly _ _)
  have hcontB : ∀ i : ι, Continuous fun w : ℝ =>
      ‖harmonicRamareBlock P s (B i) w‖ ^ (2 : ℕ) := fun i =>
    ((continuous_harmonicRamareBlock P s (B i)).norm).pow 2
  have hcontS : Continuous fun w : ℝ =>
      (I.card : ℝ) * ∑ i ∈ I, ‖harmonicRamareBlock P s (B i) w‖ ^ (2 : ℕ) :=
    (continuous_finsetSum I fun i _ => hcontB i).const_mul _
  have hint1 : IntegrableOn (fun w : ℝ => ‖harmonicRamareBilinear P s w‖ ^ (2 : ℕ)) E volume :=
    (hcont.integrableOn_Icc (a := -W) (b := W)).mono_set hEs
  have hint2 : IntegrableOn (fun w : ℝ =>
      (I.card : ℝ) * ∑ i ∈ I, ‖harmonicRamareBlock P s (B i) w‖ ^ (2 : ℕ)) E volume :=
    (hcontS.integrableOn_Icc (a := -W) (b := W)).mono_set hEs
  have hmono := setIntegral_mono_on hint1 hint2 hEm (fun w _ => hpt w)
  refine hmono.trans (le_of_eq ?_)
  rw [integral_const_mul]
  congr 1
  exact integral_finsetSum I fun i _ =>
    ((hcontB i).integrableOn_Icc (a := -W) (b := W)).mono_set hEs

/-- Weighted harmonic block-to-product replacement on a measurable part of a compact window. -/
theorem setIntegral_normSq_harmonicRamareBlock_le_product {P s B : Finset ℕ}
    (hBprime : ∀ p ∈ B, p.Prime) (C : Finset ℕ) {W : ℝ}
    {E : Set ℝ} (hEm : MeasurableSet E) (hEs : E ⊆ Set.Icc (-W) W) :
    (∫ w in E, ‖harmonicRamareBlock P s B w‖ ^ (2 : ℕ))
      ≤ 2 * (∫ w in E,
            ‖harmonicPrimeBlockPoly B w
              * logPoly (harmonicRamareCofactorCoeff P) C w‖ ^ (2 : ℕ))
        + 2 * harmonicPrimeMass B * ∑ p ∈ B, (1 / (p : ℝ)) *
            (∫ w in E, ‖harmonicRamareCofactorPoly P s p w
              - logPoly (harmonicRamareCofactorCoeff P) C w‖ ^ (2 : ℕ)) := by
  classical
  set G : ℝ → ℂ := fun w => logPoly (harmonicRamareCofactorCoeff P) C w
  have hpt : ∀ w : ℝ, ‖harmonicRamareBlock P s B w‖ ^ (2 : ℕ)
      ≤ 2 * ‖harmonicPrimeBlockPoly B w * G w‖ ^ (2 : ℕ)
        + 2 * harmonicPrimeMass B * ∑ p ∈ B, (1 / (p : ℝ)) *
            ‖harmonicRamareCofactorPoly P s p w - G w‖ ^ (2 : ℕ) := by
    intro w
    have hdisc := normSq_harmonicRamareBlock_sub_product_le
      (P := P) (s := s) (C := C) hBprime w
    have htri := norm_add_le (harmonicPrimeBlockPoly B w * G w)
      (harmonicRamareBlock P s B w - harmonicPrimeBlockPoly B w * G w)
    have heq : harmonicPrimeBlockPoly B w * G w +
        (harmonicRamareBlock P s B w - harmonicPrimeBlockPoly B w * G w) =
          harmonicRamareBlock P s B w := by ring
    rw [heq] at htri
    have hsq : ‖harmonicRamareBlock P s B w‖ ^ (2 : ℕ) ≤
        (‖harmonicPrimeBlockPoly B w * G w‖ +
          ‖harmonicRamareBlock P s B w - harmonicPrimeBlockPoly B w * G w‖) ^ (2 : ℕ) := by
      exact pow_le_pow_left₀ (norm_nonneg _) htri 2
    nlinarith [hsq, hdisc,
      sq_nonneg (‖harmonicPrimeBlockPoly B w * G w‖ -
        ‖harmonicRamareBlock P s B w - harmonicPrimeBlockPoly B w * G w‖)]
  have hcontZ : Continuous fun w : ℝ => ‖harmonicRamareBlock P s B w‖ ^ (2 : ℕ) :=
    ((continuous_harmonicRamareBlock P s B).norm).pow 2
  have hcontX : Continuous fun w : ℝ => ‖harmonicPrimeBlockPoly B w * G w‖ ^ (2 : ℕ) :=
    (((continuous_harmonicPrimeBlockPoly B).mul (continuous_logPoly _ _)).norm).pow 2
  have hcontD : ∀ p : ℕ, Continuous fun w : ℝ =>
      ‖harmonicRamareCofactorPoly P s p w - G w‖ ^ (2 : ℕ) := fun p =>
    (((continuous_harmonicRamareCofactorPoly P s p).sub
      (continuous_logPoly _ _)).norm).pow 2
  have hcontR : Continuous fun w : ℝ =>
      2 * ‖harmonicPrimeBlockPoly B w * G w‖ ^ (2 : ℕ)
        + 2 * harmonicPrimeMass B * ∑ p ∈ B, (1 / (p : ℝ)) *
            ‖harmonicRamareCofactorPoly P s p w - G w‖ ^ (2 : ℕ) :=
    (hcontX.const_mul 2).add
      ((continuous_finsetSum B fun p _ => (hcontD p).const_mul _).const_mul _)
  have hint1 : IntegrableOn (fun w : ℝ => ‖harmonicRamareBlock P s B w‖ ^ (2 : ℕ)) E volume :=
    (hcontZ.integrableOn_Icc (a := -W) (b := W)).mono_set hEs
  have hint2 : IntegrableOn (fun w : ℝ =>
      2 * ‖harmonicPrimeBlockPoly B w * G w‖ ^ (2 : ℕ)
        + 2 * harmonicPrimeMass B * ∑ p ∈ B, (1 / (p : ℝ)) *
            ‖harmonicRamareCofactorPoly P s p w - G w‖ ^ (2 : ℕ)) E volume :=
    (hcontR.integrableOn_Icc (a := -W) (b := W)).mono_set hEs
  have hmono := setIntegral_mono_on hint1 hint2 hEm (fun w _ => hpt w)
  refine hmono.trans (le_of_eq ?_)
  have hiX : IntegrableOn (fun w : ℝ => 2 * ‖harmonicPrimeBlockPoly B w * G w‖ ^ (2 : ℕ))
      E volume := ((hcontX.const_mul 2).integrableOn_Icc (a := -W) (b := W)).mono_set hEs
  have hiD : IntegrableOn (fun w : ℝ =>
      2 * harmonicPrimeMass B * ∑ p ∈ B, (1 / (p : ℝ)) *
        ‖harmonicRamareCofactorPoly P s p w - G w‖ ^ (2 : ℕ)) E volume :=
    (((continuous_finsetSum B fun p _ => (hcontD p).const_mul _).const_mul _).integrableOn_Icc
      (a := -W) (b := W)).mono_set hEs
  rw [integral_add hiX hiD, integral_const_mul]
  congr 1
  rw [integral_const_mul]
  congr 1
  rw [integral_finsetSum B fun p _ =>
    (((hcontD p).const_mul (1 / (p : ℝ))).integrableOn_Icc
      (a := -W) (b := W)).mono_set hEs]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [integral_const_mul]

end

end RHTower.Sieve
