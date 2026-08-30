import GaloisForLFunctions.RHTower.HedenmalmCriticalFeatureReflectedPairDirectThreeCenterCharge

/-!
# Reflected-pair direct five-center HCF charge

The direct three-center HCF receiver discards every source channel outside the nearest cell and its
two neighbours.  The global holomorphic-sector inequality makes those discarded channels
nonnegative.  Keeping the next two centers gives a strict unconditional receiver improvement.

For a point in the nearest-center cell, each center at displacement two is at distance at most
`5/2`.  Its critical-feature denominator is at most `221/4`, hence its Hermitian energy is at
least `16/221` and its real holomorphic-square energy is at least `8/221`.  Reflection doubles the
two-center gain.  Consequently the sufficient 75% source ceiling rises from `15872/21125` to
`15872/21125 + 4/221`.

This is a receiver improvement only.  It does not assert the remaining source-side asymptotic
upper bound.
-/

open Complex

namespace RHTower

noncomputable section

/-- Denominator bound for the next unused lattice center.  The maximum `221/4` is attained on the
closed rectangle `|Re z - t| ≤ 5/2`, `|Im z| ≤ 1/2` at its four corners. -/
theorem criticalFeatureDenominatorNormSq_le_twoHundredTwentyOneFourths
    (t : ℝ) {z : ℂ} (hy : |z.im| ≤ 1 / 2)
    (ht : |z.re - t| ≤ 5 / 2) :
    criticalFeatureDenominatorNormSq t z ≤ 221 / 4 := by
  let u : ℝ := z.re - t
  let y : ℝ := z.im
  have hu2 : u ^ 2 ≤ 25 / 4 := by
    have h := (sq_le_sq₀ (abs_nonneg u) (by norm_num : (0 : ℝ) ≤ 5 / 2)).2
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
      0 ≤ (25 / 4 - u ^ 2) * (25 / 4 + u ^ 2 + 2 + 2 * y ^ 2) := by
    exact mul_nonneg (by linarith) (by nlinarith [sq_nonneg u, sq_nonneg y])
  have hmonoY :
      0 ≤ (1 / 4 - y ^ 2) * (1 / 4 + y ^ 2 + 21 / 2) := by
    exact mul_nonneg (by linarith) (by nlinarith [sq_nonneg y])
  rw [criticalFeatureDenominatorNormSq_eq]
  dsimp only [u, y] at hu2 hy2 hmonoU hmonoY ⊢
  ring_nf at hmonoU hmonoY ⊢
  nlinarith

/-- Every critical feature whose center is within distance `5/2` contributes at least `16/221`
Hermitian energy throughout the open critical strip. -/
theorem sixteen_twoHundredTwentyOne_le_normSq_criticalFeatureCauchyKernelTest
    {t : ℝ} {z : ℂ} (hz : |z.im| < 1 / 2)
    (ht : |z.re - t| ≤ 5 / 2) :
    (16 / 221 : ℝ) ≤
      Complex.normSq (criticalFeatureCauchyKernelTest t z) := by
  have hpos := criticalFeatureDenominatorNormSq_pos t hz
  have hden :=
    criticalFeatureDenominatorNormSq_le_twoHundredTwentyOneFourths t hz.le ht
  rw [normSq_criticalFeatureCauchyKernelTest_eq_four_div t hz]
  apply (le_div_iff₀ hpos).2
  nlinarith

/-- Direct five-center holomorphic charge.  The next two centers add `16/221` to the sharp direct
three-center charge. -/
theorem directFiveCenterCriticalFeatureHolomorphicCharge_lower
    {t : ℝ} {z : ℂ} (hz : |z.im| < 1 / 2)
    (ht : |z.re - t| ≤ 1 / 2) :
    (63488 / 21125 + 16 / 221 : ℝ) ≤
      ((criticalFeatureCauchyKernelTest (t - 2) z) ^ 2).re +
        ((criticalFeatureCauchyKernelTest (t - 1) z) ^ 2).re +
        ((criticalFeatureCauchyKernelTest t z) ^ 2).re +
        ((criticalFeatureCauchyKernelTest (t + 1) z) ^ 2).re +
        ((criticalFeatureCauchyKernelTest (t + 2) z) ^ 2).re := by
  have hthree := directThreeCenterCriticalFeatureHolomorphicCharge_lower hz ht
  have hmDist : |z.re - (t - 2)| ≤ 5 / 2 := by
    rw [abs_le]
    rcases abs_le.mp ht with ⟨hl, hr⟩
    constructor <;> linarith
  have hpDist : |z.re - (t + 2)| ≤ 5 / 2 := by
    rw [abs_le]
    rcases abs_le.mp ht with ⟨hl, hr⟩
    constructor <;> linarith
  have hmNorm :=
    sixteen_twoHundredTwentyOne_le_normSq_criticalFeatureCauchyKernelTest hz hmDist
  have hpNorm :=
    sixteen_twoHundredTwentyOne_le_normSq_criticalFeatureCauchyKernelTest hz hpDist
  have hmSector :=
    half_mul_normSq_criticalFeatureCauchyKernelTest_le_re_sq (t - 2) hz
  have hpSector :=
    half_mul_normSq_criticalFeatureCauchyKernelTest_le_re_sq (t + 2) hz
  nlinarith

/-- Every finite off-line packet deposits the direct five-center charge when its nearest five
integer centers lie in the source window. -/
theorem finite_offLine_card_mul_directFiveCenterCharge_le_offLineLatticeBudget
    (K : Finset ℤ) (S : Finset XiZeroCopy)
    (hoff : ∀ q ∈ S, (q.1 : ℂ).re ≠ 1 / 2)
    (hcenters : ∀ q ∈ S,
      round (xiSpectralPoint q).re - 2 ∈ K ∧
      round (xiSpectralPoint q).re - 1 ∈ K ∧
      round (xiSpectralPoint q).re ∈ K ∧
      round (xiSpectralPoint q).re + 1 ∈ K ∧
      round (xiSpectralPoint q).re + 2 ∈ K) :
    (S.card : ℝ) * (63488 / 21125 + 16 / 221 : ℝ) ≤
      criticalFeaturePrimeGammaOffLineLatticeBudget K := by
  calc
    (S.card : ℝ) * (63488 / 21125 + 16 / 221 : ℝ) =
        ∑ _q ∈ S, (63488 / 21125 + 16 / 221 : ℝ) := by
      simp
      ring
    _ ≤ ∑ q ∈ S, ∑ k ∈ K,
        offLineCriticalFeatureHolomorphicEnergy (k : ℝ) q := by
      gcongr with q hq
      let kq : ℤ := round (xiSpectralPoint q).re
      have hmem := hcenters q hq
      have hqoff := hoff q hq
      have hfive :=
        directFiveCenterCriticalFeatureHolomorphicCharge_lower
          (z := xiSpectralPoint q) (t := (kq : ℝ))
          (abs_xiSpectralPoint_im_lt_half q) (abs_sub_round _)
      have hoffeq (j : ℤ) :
          ((criticalFeatureCauchyKernelTest (j : ℝ)
            (xiSpectralPoint q)) ^ 2).re =
            offLineCriticalFeatureHolomorphicEnergy (j : ℝ) q := by
        rw [offLineCriticalFeatureHolomorphicEnergy, if_neg hqoff]
      have hcastm2 : (kq : ℝ) - 2 = ((kq - 2 : ℤ) : ℝ) := by
        exact_mod_cast (rfl : kq - 2 = kq - 2)
      have hcastm1 : (kq : ℝ) - 1 = ((kq - 1 : ℤ) : ℝ) := by
        exact_mod_cast (rfl : kq - 1 = kq - 1)
      have hcastp1 : (kq : ℝ) + 1 = ((kq + 1 : ℤ) : ℝ) := by
        exact_mod_cast (rfl : kq + 1 = kq + 1)
      have hcastp2 : (kq : ℝ) + 2 = ((kq + 2 : ℤ) : ℝ) := by
        exact_mod_cast (rfl : kq + 2 = kq + 2)
      rw [hcastm2, hcastm1, hcastp1, hcastp2,
        hoffeq, hoffeq, hoffeq, hoffeq, hoffeq] at hfive
      let Tq : Finset ℤ := {kq - 2, kq - 1, kq, kq + 1, kq + 2}
      have hTq : Tq ⊆ K := by
        intro j hj
        simp only [Tq, Finset.mem_insert, Finset.mem_singleton] at hj
        rcases hj with hj | hj | hj | hj | hj
        · simpa [hj] using hmem.1
        · simpa [hj] using hmem.2.1
        · simpa [hj] using hmem.2.2.1
        · simpa [hj] using hmem.2.2.2.1
        · simpa [hj] using hmem.2.2.2.2
      have hsumTq :
          (∑ j ∈ Tq, offLineCriticalFeatureHolomorphicEnergy (j : ℝ) q) =
            offLineCriticalFeatureHolomorphicEnergy ((kq - 2 : ℤ) : ℝ) q +
              offLineCriticalFeatureHolomorphicEnergy ((kq - 1 : ℤ) : ℝ) q +
              offLineCriticalFeatureHolomorphicEnergy (kq : ℝ) q +
              offLineCriticalFeatureHolomorphicEnergy ((kq + 1 : ℤ) : ℝ) q +
              offLineCriticalFeatureHolomorphicEnergy ((kq + 2 : ℤ) : ℝ) q := by
        have hab : kq - 2 ≠ kq - 1 := by omega
        have hac : kq - 2 ≠ kq := by omega
        have had : kq - 2 ≠ kq + 1 := by omega
        have hae : kq - 2 ≠ kq + 2 := by omega
        have hbc : kq - 1 ≠ kq := by omega
        have hbd : kq - 1 ≠ kq + 1 := by omega
        have hbe : kq - 1 ≠ kq + 2 := by omega
        have hcd : kq ≠ kq + 1 := by omega
        have hce : kq ≠ kq + 2 := by omega
        have hde : kq + 1 ≠ kq + 2 := by omega
        simp [Tq, hab, hac, had, hae, hbc, hbd, hbe, hcd, hce, hde]
        ring
      calc
        (63488 / 21125 + 16 / 221 : ℝ) ≤ ∑ j ∈ Tq,
            offLineCriticalFeatureHolomorphicEnergy (j : ℝ) q := by
          rw [hsumTq]
          simpa [Int.cast_sub, Int.cast_add] using hfive
        _ ≤ ∑ j ∈ K, offLineCriticalFeatureHolomorphicEnergy (j : ℝ) q := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hTq
          intro j hjK hjTq
          exact offLineCriticalFeatureHolomorphicEnergy_nonneg (j : ℝ) q
    _ = ∑ k ∈ K, ∑ q ∈ S,
        offLineCriticalFeatureHolomorphicEnergy (k : ℝ) q := by
      rw [Finset.sum_comm]
    _ ≤ ∑ k ∈ K, ∑' q : XiZeroCopy,
        offLineCriticalFeatureHolomorphicEnergy (k : ℝ) q := by
      gcongr with k hk
      exact (offLineCriticalFeatureHolomorphicEnergy_summable (k : ℝ)).sum_le_tsum S
        (fun q _ => offLineCriticalFeatureHolomorphicEnergy_nonneg (k : ℝ) q)
    _ = criticalFeaturePrimeGammaOffLineLatticeBudget K := by
      rw [criticalFeaturePrimeGammaOffLineLatticeBudget]
      apply Finset.sum_congr rfl
      intro k hk
      rw [criticalFeaturePrimeGammaOffLineExcess_eq_tsum_offLineHolomorphicEnergy]

private theorem I_mul_xiSpectralPoint_lineConj_re_fiveCenter
    (q : XiZeroCopy) :
    (I * xiSpectralPoint (xiZeroCopyLineConjEquiv q)).re =
      -(I * xiSpectralPoint q).re := by
  rw [xiSpectralPoint_lineConj]
  simp [Complex.mul_re]

private theorem xiZeroCopy_re_ne_half_of_transverse_re_ne_zero_fiveCenter
    (q : XiZeroCopy) (hq : (I * xiSpectralPoint q).re ≠ 0) :
    (q.1 : ℂ).re ≠ 1 / 2 := by
  intro hline
  apply hq
  rw [I_mul_xiSpectralPoint, Complex.sub_re, hline]
  norm_num

/-- A strict-right packet and its reflected packet deposit the reflected direct five-center charge
in the same all-copy corrected budget. -/
theorem finite_strictRight_card_mul_reflectedDirectFiveCenterCharge_le_offLineLatticeBudget
    (K : Finset ℤ) (S : Finset XiZeroCopy)
    (hright : ∀ q ∈ S, 0 < (I * xiSpectralPoint q).re)
    (hcenters : ∀ q ∈ S,
      round (xiSpectralPoint q).re - 2 ∈ K ∧
      round (xiSpectralPoint q).re - 1 ∈ K ∧
      round (xiSpectralPoint q).re ∈ K ∧
      round (xiSpectralPoint q).re + 1 ∈ K ∧
      round (xiSpectralPoint q).re + 2 ∈ K) :
    (S.card : ℝ) * (126976 / 21125 + 32 / 221 : ℝ) ≤
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
    rw [I_mul_xiSpectralPoint_lineConj_re_fiveCenter] at hreflected
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
    · exact xiZeroCopy_re_ne_half_of_transverse_re_ne_zero_fiveCenter q
        (ne_of_gt (hright q hqS))
    · change q ∈ S.image xiZeroCopyLineConjEquiv at hqR
      rw [Finset.mem_image] at hqR
      obtain ⟨p, hpS, rfl⟩ := hqR
      apply xiZeroCopy_re_ne_half_of_transverse_re_ne_zero_fiveCenter
      rw [I_mul_xiSpectralPoint_lineConj_re_fiveCenter]
      exact neg_ne_zero.mpr (ne_of_gt (hright p hpS))
  have hcentersU : ∀ q ∈ U,
      round (xiSpectralPoint q).re - 2 ∈ K ∧
      round (xiSpectralPoint q).re - 1 ∈ K ∧
      round (xiSpectralPoint q).re ∈ K ∧
      round (xiSpectralPoint q).re + 1 ∈ K ∧
      round (xiSpectralPoint q).re + 2 ∈ K := by
    intro q hqU
    change q ∈ S ∪ R at hqU
    rw [Finset.mem_union] at hqU
    rcases hqU with hqS | hqR
    · exact hcenters q hqS
    · change q ∈ S.image xiZeroCopyLineConjEquiv at hqR
      rw [Finset.mem_image] at hqR
      obtain ⟨p, hpS, rfl⟩ := hqR
      have hre : (xiSpectralPoint (xiZeroCopyLineConjEquiv p)).re =
          (xiSpectralPoint p).re := by
        rw [xiSpectralPoint_lineConj]
        simp
      rw [hre]
      exact hcenters p hpS
  have hcharge :=
    finite_offLine_card_mul_directFiveCenterCharge_le_offLineLatticeBudget
      K U hoffU hcentersU
  calc
    (S.card : ℝ) * (126976 / 21125 + 32 / 221 : ℝ) =
        (U.card : ℝ) * (63488 / 21125 + 16 / 221 : ℝ) := by
      rw [hcardU]
      push_cast
      ring
    _ ≤ criticalFeaturePrimeGammaOffLineLatticeBudget K := hcharge

/-- Reflected-pair direct five-center 75% receiver.  Its sufficient corrected-source ceiling is
`15872/21125 + 4/221`, strictly larger than the direct three-center ceiling. -/
theorem three_quarters_line_of_reflectedDirectFiveCenter_primeGammaOffLineLatticeBudget
    {N N₀ : ℝ} (K : Finset ℤ) (S : Finset XiZeroCopy)
    (hright : ∀ q ∈ S, 0 < (I * xiSpectralPoint q).re)
    (hcenters : ∀ q ∈ S,
      round (xiSpectralPoint q).re - 2 ∈ K ∧
      round (xiSpectralPoint q).re - 1 ∈ K ∧
      round (xiSpectralPoint q).re ∈ K ∧
      round (xiSpectralPoint q).re + 1 ∈ K ∧
      round (xiSpectralPoint q).re + 2 ∈ K)
    (hsplit : N = N₀ + 2 * S.card)
    (hbudget : criticalFeaturePrimeGammaOffLineLatticeBudget K ≤
      (15872 / 21125 + 4 / 221 : ℝ) * N) :
    3 * N / 4 ≤ N₀ := by
  have hcharge :=
    finite_strictRight_card_mul_reflectedDirectFiveCenterCharge_le_offLineLatticeBudget
      K S hright hcenters
  have hcount : (S.card : ℝ) ≤ N / 8 := by
    nlinarith
  nlinarith

end

end RHTower
