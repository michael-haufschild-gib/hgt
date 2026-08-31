import GaloisForLFunctions.RHTower.HedenmalmCriticalFeatureCenteredStencilCharge

/-!
# Seven-center shallow HCF charge

The five-center receiver discards the next two nonnegative height channels.  On the Route-T
shallow band, centers at displacement three contribute an additional exact rational quantum.
This file retains them and propagates the resulting seven-center charge through a reusable finite
stencil theorem.
-/

open Complex

namespace RHTower

noncomputable section

/-- Integer offsets in the seven-center nearest-height stencil. -/
def criticalFeatureSevenCenterStencil : Finset ℤ := {-3, -2, -1, 0, 1, 2, 3}

/-- Direct shallow charge retained by seven height centers. -/
def criticalFeatureShallowDirectSevenCenterCharge : ℝ :=
  (23 / 25 : ℝ) * (23232 / 4225 + 32 / 221 + 32 / 725 : ℝ)

/-- Reflected-pair seven-center shallow charge. -/
def criticalFeatureShallowReflectedSevenCenterCharge : ℝ :=
  2 * criticalFeatureShallowDirectSevenCenterCharge

theorem criticalFeatureShallowDirectSevenCenterCharge_pos :
    0 < criticalFeatureShallowDirectSevenCenterCharge := by
  norm_num [criticalFeatureShallowDirectSevenCenterCharge]

theorem criticalFeatureShallowReflectedSevenCenterCharge_pos :
    0 < criticalFeatureShallowReflectedSevenCenterCharge := by
  norm_num [criticalFeatureShallowReflectedSevenCenterCharge,
    criticalFeatureShallowDirectSevenCenterCharge]

/-- Denominator bound for a center within distance `7/2` throughout the critical strip. -/
theorem criticalFeatureDenominatorNormSq_le_sevenHundredTwentyFiveFourths
    (t : ℝ) {z : ℂ} (hy : |z.im| ≤ 1 / 2)
    (ht : |z.re - t| ≤ 7 / 2) :
    criticalFeatureDenominatorNormSq t z ≤ 725 / 4 := by
  let u : ℝ := z.re - t
  let y : ℝ := z.im
  have hu2 : u ^ 2 ≤ 49 / 4 := by
    have h := (sq_le_sq₀ (abs_nonneg u) (by norm_num : (0 : ℝ) ≤ 7 / 2)).2
      (by simpa [u] using ht)
    rw [sq_abs] at h
    norm_num at h ⊢
    exact h
  have hy2 : y ^ 2 ≤ 1 / 4 := by
    have h := (sq_le_sq₀ (abs_nonneg y) (by norm_num : (0 : ℝ) ≤ 1 / 2)).2
      (by simpa [y] using hy)
    rw [sq_abs] at h
    norm_num at h ⊢
    exact h
  have hmonoU :
      0 ≤ (49 / 4 - u ^ 2) * (49 / 4 + u ^ 2 + 2 + 2 * y ^ 2) := by
    exact mul_nonneg (by linarith) (by nlinarith [sq_nonneg u, sq_nonneg y])
  have hmonoY :
      0 ≤ (1 / 4 - y ^ 2) * (1 / 4 + y ^ 2 + 45 / 2) := by
    exact mul_nonneg (by linarith) (by nlinarith [sq_nonneg y])
  rw [criticalFeatureDenominatorNormSq_eq]
  dsimp only [u, y] at hu2 hy2 hmonoU hmonoY ⊢
  ring_nf at hmonoU hmonoY ⊢
  nlinarith

/-- Every distance-three center contributes at least `16/725` Hermitian energy. -/
theorem sixteen_sevenHundredTwentyFive_le_normSq_criticalFeatureCauchyKernelTest
    {t : ℝ} {z : ℂ} (hz : |z.im| < 1 / 2)
    (ht : |z.re - t| ≤ 7 / 2) :
    (16 / 725 : ℝ) ≤ Complex.normSq (criticalFeatureCauchyKernelTest t z) := by
  have hpos := criticalFeatureDenominatorNormSq_pos t hz
  have hden := criticalFeatureDenominatorNormSq_le_sevenHundredTwentyFiveFourths
    t hz.le ht
  rw [normSq_criticalFeatureCauchyKernelTest_eq_four_div t hz]
  apply (le_div_iff₀ hpos).2
  nlinarith

/-- Direct seven-center local charge on the `|Im z| ≤ 1/5` band. -/
theorem shallowDirectSevenCenterCriticalFeatureHolomorphicCharge_lower
    {t : ℝ} {z : ℂ} (hy : |z.im| ≤ 1 / 5)
    (ht : |z.re - t| ≤ 1 / 2) :
    criticalFeatureShallowDirectSevenCenterCharge ≤
      ((criticalFeatureCauchyKernelTest (t - 3) z) ^ 2).re +
      ((criticalFeatureCauchyKernelTest (t - 2) z) ^ 2).re +
      ((criticalFeatureCauchyKernelTest (t - 1) z) ^ 2).re +
      ((criticalFeatureCauchyKernelTest t z) ^ 2).re +
      ((criticalFeatureCauchyKernelTest (t + 1) z) ^ 2).re +
      ((criticalFeatureCauchyKernelTest (t + 2) z) ^ 2).re +
      ((criticalFeatureCauchyKernelTest (t + 3) z) ^ 2).re := by
  have hz : |z.im| < 1 / 2 := by linarith
  have hfive := shallowDirectFiveCenterCriticalFeatureHolomorphicCharge_lower hy ht
  have hmDist : |z.re - (t - 3)| ≤ 7 / 2 := by
    rw [abs_le]
    rcases abs_le.mp ht with ⟨hl, hr⟩
    constructor <;> linarith
  have hpDist : |z.re - (t + 3)| ≤ 7 / 2 := by
    rw [abs_le]
    rcases abs_le.mp ht with ⟨hl, hr⟩
    constructor <;> linarith
  have hmNorm :=
    sixteen_sevenHundredTwentyFive_le_normSq_criticalFeatureCauchyKernelTest hz hmDist
  have hpNorm :=
    sixteen_sevenHundredTwentyFive_le_normSq_criticalFeatureCauchyKernelTest hz hpDist
  have hmSector :=
    twentyThree_twentyFive_mul_normSq_criticalFeatureCauchyKernelTest_le_re_sq
      (t - 3) hy
  have hpSector :=
    twentyThree_twentyFive_mul_normSq_criticalFeatureCauchyKernelTest_le_re_sq
      (t + 3) hy
  dsimp [criticalFeatureShallowDirectSevenCenterCharge]
  nlinarith

/-- Every shallow off-line packet deposits the direct seven-center charge. -/
theorem finite_shallowOffLine_card_mul_directSevenCenterCharge_le_offLineLatticeBudget
    (K : Finset ℤ) (S : Finset XiZeroCopy)
    (hoff : ∀ q ∈ S, (q.1 : ℂ).re ≠ 1 / 2)
    (hshallow : ∀ q ∈ S, |(xiSpectralPoint q).im| ≤ 1 / 5)
    (hcenters : ∀ q ∈ S, ∀ j ∈ criticalFeatureSevenCenterStencil,
      round (xiSpectralPoint q).re + j ∈ K) :
    (S.card : ℝ) * criticalFeatureShallowDirectSevenCenterCharge ≤
      criticalFeaturePrimeGammaOffLineLatticeBudget K := by
  apply finite_offLine_card_mul_centeredStencilLocalCharge_le_offLineLatticeBudget
    criticalFeatureSevenCenterStencil K S criticalFeatureShallowDirectSevenCenterCharge
    hoff hcenters
  intro q hq
  have hlocal := shallowDirectSevenCenterCriticalFeatureHolomorphicCharge_lower
    (t := ((round (xiSpectralPoint q).re : ℤ) : ℝ))
    (hshallow q hq) (abs_sub_round _)
  simpa [criticalFeatureSevenCenterStencil, Int.cast_add, Int.cast_sub,
    sub_eq_add_neg, add_assoc] using hlocal

private theorem I_mul_xiSpectralPoint_lineConj_re_sevenCenter
    (q : XiZeroCopy) :
    (I * xiSpectralPoint (xiZeroCopyLineConjEquiv q)).re =
      -(I * xiSpectralPoint q).re := by
  rw [xiSpectralPoint_lineConj]
  simp [Complex.mul_re]

private theorem xiZeroCopy_re_ne_half_of_transverse_re_ne_zero_sevenCenter
    (q : XiZeroCopy) (hq : (I * xiSpectralPoint q).re ≠ 0) :
    (q.1 : ℂ).re ≠ 1 / 2 := by
  intro hline
  apply hq
  rw [I_mul_xiSpectralPoint, Complex.sub_re, hline]
  norm_num

/-- A strict-right shallow packet and its line reflection deposit the reflected seven-center
charge in the corrected budget. -/
theorem finite_strictRight_shallow_card_mul_reflectedSevenCenterCharge_le_offLineLatticeBudget
    (K : Finset ℤ) (S : Finset XiZeroCopy)
    (hright : ∀ q ∈ S, 0 < (I * xiSpectralPoint q).re)
    (hshallow : ∀ q ∈ S, |(xiSpectralPoint q).im| ≤ 1 / 5)
    (hcenters : ∀ q ∈ S, ∀ j ∈ criticalFeatureSevenCenterStencil,
      round (xiSpectralPoint q).re + j ∈ K) :
    (S.card : ℝ) * criticalFeatureShallowReflectedSevenCenterCharge ≤
      criticalFeaturePrimeGammaOffLineLatticeBudget K := by
  let R : Finset XiZeroCopy := S.image xiZeroCopyLineConjEquiv
  let U : Finset XiZeroCopy := S ∪ R
  have hdisjoint : Disjoint S R := by
    rw [Finset.disjoint_left]
    intro q hqS hqR
    change q ∈ S.image xiZeroCopyLineConjEquiv at hqR
    rw [Finset.mem_image] at hqR
    obtain ⟨p, hpS, hpq⟩ := hqR
    subst q
    have hp := hright p hpS
    have hreflected := hright (xiZeroCopyLineConjEquiv p) hqS
    rw [I_mul_xiSpectralPoint_lineConj_re_sevenCenter] at hreflected
    linarith
  have hcardR : R.card = S.card := by
    exact Finset.card_image_of_injective S xiZeroCopyLineConjEquiv.injective
  have hcardU : U.card = 2 * S.card := by
    change (S ∪ R).card = 2 * S.card
    rw [Finset.card_union_of_disjoint hdisjoint, hcardR]
    omega
  have hoffU : ∀ q ∈ U, (q.1 : ℂ).re ≠ 1 / 2 := by
    intro q hqU
    change q ∈ S ∪ R at hqU
    rw [Finset.mem_union] at hqU
    rcases hqU with hqS | hqR
    · exact xiZeroCopy_re_ne_half_of_transverse_re_ne_zero_sevenCenter q
        (ne_of_gt (hright q hqS))
    · change q ∈ S.image xiZeroCopyLineConjEquiv at hqR
      rw [Finset.mem_image] at hqR
      obtain ⟨p, hpS, rfl⟩ := hqR
      apply xiZeroCopy_re_ne_half_of_transverse_re_ne_zero_sevenCenter
      rw [I_mul_xiSpectralPoint_lineConj_re_sevenCenter]
      exact neg_ne_zero.mpr (ne_of_gt (hright p hpS))
  have hshallowU : ∀ q ∈ U, |(xiSpectralPoint q).im| ≤ 1 / 5 := by
    intro q hqU
    change q ∈ S ∪ R at hqU
    rw [Finset.mem_union] at hqU
    rcases hqU with hqS | hqR
    · exact hshallow q hqS
    · change q ∈ S.image xiZeroCopyLineConjEquiv at hqR
      rw [Finset.mem_image] at hqR
      obtain ⟨p, hpS, rfl⟩ := hqR
      rw [xiSpectralPoint_lineConj]
      simpa using hshallow p hpS
  have hcentersU : ∀ q ∈ U, ∀ j ∈ criticalFeatureSevenCenterStencil,
      round (xiSpectralPoint q).re + j ∈ K := by
    intro q hqU j hj
    change q ∈ S ∪ R at hqU
    rw [Finset.mem_union] at hqU
    rcases hqU with hqS | hqR
    · exact hcenters q hqS j hj
    · change q ∈ S.image xiZeroCopyLineConjEquiv at hqR
      rw [Finset.mem_image] at hqR
      obtain ⟨p, hpS, rfl⟩ := hqR
      have hre : (xiSpectralPoint (xiZeroCopyLineConjEquiv p)).re =
          (xiSpectralPoint p).re := by
        rw [xiSpectralPoint_lineConj]
        simp
      rw [hre]
      exact hcenters p hpS j hj
  have hcharge :=
    finite_shallowOffLine_card_mul_directSevenCenterCharge_le_offLineLatticeBudget
      K U hoffU hshallowU hcentersU
  calc
    (S.card : ℝ) * criticalFeatureShallowReflectedSevenCenterCharge =
        (U.card : ℝ) * criticalFeatureShallowDirectSevenCenterCharge := by
      rw [hcardU]
      push_cast
      rw [criticalFeatureShallowReflectedSevenCenterCharge]
      ring
    _ ≤ criticalFeaturePrimeGammaOffLineLatticeBudget K := hcharge

end

end RHTower
