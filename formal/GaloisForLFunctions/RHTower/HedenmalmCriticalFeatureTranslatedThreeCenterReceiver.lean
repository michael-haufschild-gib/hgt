import GaloisForLFunctions.RHTower.HedenmalmCriticalFeatureReflectedPairDirectThreeCenterCharge
import GaloisForLFunctions.HTGeometry.RoundingVarianceFloor

/-!
# Translation-uniform direct three-center HCF receiver

The integer HCF lattice may be translated by an arbitrary real phase.  A zero copy of height `x`
then uses the center `round (x - θ) + θ`; nearest-integer rounding still places this center within
one half-unit.  Consequently the direct three-center charge and its critical-line-reflected
doubling are uniform in the translation phase.

This module is receiver geometry only.  It makes no source-budget estimate and does not average a
zero divisor.  Its role is to permit a separately constructed, zero-independent translated source
budget to choose the phase before the receiver is applied.
-/

open Complex

namespace RHTower

noncomputable section

/-- Corrected HCF budget on the finite lattice translated by the real phase `θ`. -/
def criticalFeaturePrimeGammaOffLineTranslatedLatticeBudget
    (θ : ℝ) (K : Finset ℤ) : ℝ :=
  ∑ k ∈ K, criticalFeaturePrimeGammaOffLineExcess ((k : ℝ) + θ)

theorem criticalFeaturePrimeGammaOffLineTranslatedLatticeBudget_nonneg
    (θ : ℝ) (K : Finset ℤ) :
    0 ≤ criticalFeaturePrimeGammaOffLineTranslatedLatticeBudget θ K := by
  rw [criticalFeaturePrimeGammaOffLineTranslatedLatticeBudget]
  exact Finset.sum_nonneg fun k hk =>
    criticalFeaturePrimeGammaOffLineExcess_nonneg ((k : ℝ) + θ)

/-- Arbitrary-real translation preserves the direct three-center charge for every finite off-line
packet. -/
theorem finite_offLine_card_mul_directThreeCenterCharge_le_translatedLatticeBudget
    (θ : ℝ) (K : Finset ℤ) (S : Finset XiZeroCopy)
    (hoff : ∀ q ∈ S, (q.1 : ℂ).re ≠ 1 / 2)
    (hcenters : ∀ q ∈ S,
      round ((xiSpectralPoint q).re - θ) - 1 ∈ K ∧
      round ((xiSpectralPoint q).re - θ) ∈ K ∧
      round ((xiSpectralPoint q).re - θ) + 1 ∈ K) :
    (S.card : ℝ) * (63488 / 21125 : ℝ) ≤
      criticalFeaturePrimeGammaOffLineTranslatedLatticeBudget θ K := by
  calc
    (S.card : ℝ) * (63488 / 21125 : ℝ) =
        ∑ _q ∈ S, (63488 / 21125 : ℝ) := by simp
    _ ≤ ∑ q ∈ S, ∑ k ∈ K,
        offLineCriticalFeatureHolomorphicEnergy ((k : ℝ) + θ) q := by
      gcongr with q hq
      let kq : ℤ := round ((xiSpectralPoint q).re - θ)
      have hmem := hcenters q hq
      have hnear :
          |(xiSpectralPoint q).re - ((kq : ℝ) + θ)| ≤ 1 / 2 := by
        rw [show (xiSpectralPoint q).re - ((kq : ℝ) + θ) =
            ((xiSpectralPoint q).re - θ) - (kq : ℝ) by ring]
        exact abs_sub_round ((xiSpectralPoint q).re - θ)
      have hthree :=
        directThreeCenterCriticalFeatureHolomorphicCharge_lower
          (z := xiSpectralPoint q) (t := (kq : ℝ) + θ)
          (abs_xiSpectralPoint_im_lt_half q) hnear
      have hoffeq (j : ℤ) :
          ((criticalFeatureCauchyKernelTest ((j : ℝ) + θ)
            (xiSpectralPoint q)) ^ 2).re =
            offLineCriticalFeatureHolomorphicEnergy ((j : ℝ) + θ) q := by
        rw [offLineCriticalFeatureHolomorphicEnergy, if_neg (hoff q hq)]
      have hcastm : (kq : ℝ) + θ - 1 = ((kq - 1 : ℤ) : ℝ) + θ := by
        push_cast
        ring
      have hcastp : (kq : ℝ) + θ + 1 = ((kq + 1 : ℤ) : ℝ) + θ := by
        push_cast
        ring
      rw [hcastm, hcastp, hoffeq, hoffeq, hoffeq] at hthree
      let Tq : Finset ℤ := {kq - 1, kq, kq + 1}
      have hTq : Tq ⊆ K := by
        intro j hj
        simp only [Tq, Finset.mem_insert, Finset.mem_singleton] at hj
        rcases hj with hj | hj | hj
        · simpa [hj] using hmem.1
        · simpa [hj] using hmem.2.1
        · simpa [hj] using hmem.2.2
      have hsumTq :
          (∑ j ∈ Tq,
              offLineCriticalFeatureHolomorphicEnergy ((j : ℝ) + θ) q) =
            offLineCriticalFeatureHolomorphicEnergy (((kq - 1 : ℤ) : ℝ) + θ) q +
              offLineCriticalFeatureHolomorphicEnergy ((kq : ℝ) + θ) q +
              offLineCriticalFeatureHolomorphicEnergy (((kq + 1 : ℤ) : ℝ) + θ) q := by
        have hm0 : kq - 1 ≠ kq := by omega
        have hmp : kq - 1 ≠ kq + 1 := by omega
        have h0p : kq ≠ kq + 1 := by omega
        simp [Tq, hm0, hmp, h0p]
        ring
      calc
        (63488 / 21125 : ℝ) ≤ ∑ j ∈ Tq,
            offLineCriticalFeatureHolomorphicEnergy ((j : ℝ) + θ) q := by
          rw [hsumTq]
          exact hthree
        _ ≤ ∑ j ∈ K,
            offLineCriticalFeatureHolomorphicEnergy ((j : ℝ) + θ) q := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hTq
          intro j hjK hjTq
          exact offLineCriticalFeatureHolomorphicEnergy_nonneg ((j : ℝ) + θ) q
    _ = ∑ k ∈ K, ∑ q ∈ S,
        offLineCriticalFeatureHolomorphicEnergy ((k : ℝ) + θ) q := by
      rw [Finset.sum_comm]
    _ ≤ ∑ k ∈ K, ∑' q : XiZeroCopy,
        offLineCriticalFeatureHolomorphicEnergy ((k : ℝ) + θ) q := by
      gcongr with k hk
      exact (offLineCriticalFeatureHolomorphicEnergy_summable ((k : ℝ) + θ)).sum_le_tsum S
        (fun q _ => offLineCriticalFeatureHolomorphicEnergy_nonneg ((k : ℝ) + θ) q)
    _ = criticalFeaturePrimeGammaOffLineTranslatedLatticeBudget θ K := by
      rw [criticalFeaturePrimeGammaOffLineTranslatedLatticeBudget]
      apply Finset.sum_congr rfl
      intro k hk
      rw [criticalFeaturePrimeGammaOffLineExcess_eq_tsum_offLineHolomorphicEnergy]

/-- Critical-line reflection reverses transverse orientation while preserving the translated
height cell. -/
private theorem I_mul_xiSpectralPoint_lineConj_re_translated
    (q : XiZeroCopy) :
    (I * xiSpectralPoint (xiZeroCopyLineConjEquiv q)).re =
      -(I * xiSpectralPoint q).re := by
  rw [xiSpectralPoint_lineConj]
  simp [Complex.mul_re]

private theorem xiZeroCopy_re_ne_half_of_transverse_re_ne_zero
    (q : XiZeroCopy) (hq : (I * xiSpectralPoint q).re ≠ 0) :
    (q.1 : ℂ).re ≠ 1 / 2 := by
  intro hline
  apply hq
  rw [I_mul_xiSpectralPoint, Complex.sub_re, hline]
  norm_num

/-- Reflection doubles the direct charge uniformly for every translated height lattice. -/
theorem finite_strictRight_card_mul_reflectedDirectThreeCenterCharge_le_translatedLatticeBudget
    (θ : ℝ) (K : Finset ℤ) (S : Finset XiZeroCopy)
    (hright : ∀ q ∈ S, 0 < (I * xiSpectralPoint q).re)
    (hcenters : ∀ q ∈ S,
      round ((xiSpectralPoint q).re - θ) - 1 ∈ K ∧
      round ((xiSpectralPoint q).re - θ) ∈ K ∧
      round ((xiSpectralPoint q).re - θ) + 1 ∈ K) :
    (S.card : ℝ) * (126976 / 21125 : ℝ) ≤
      criticalFeaturePrimeGammaOffLineTranslatedLatticeBudget θ K := by
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
    rw [I_mul_xiSpectralPoint_lineConj_re_translated] at hreflected
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
    · exact xiZeroCopy_re_ne_half_of_transverse_re_ne_zero q
        (ne_of_gt (hright q hqS))
    · change q ∈ S.image xiZeroCopyLineConjEquiv at hqR
      rw [Finset.mem_image] at hqR
      obtain ⟨p, hpS, rfl⟩ := hqR
      apply xiZeroCopy_re_ne_half_of_transverse_re_ne_zero
      rw [I_mul_xiSpectralPoint_lineConj_re_translated]
      exact neg_ne_zero.mpr (ne_of_gt (hright p hpS))
  have hcentersU : ∀ q ∈ U,
      round ((xiSpectralPoint q).re - θ) - 1 ∈ K ∧
      round ((xiSpectralPoint q).re - θ) ∈ K ∧
      round ((xiSpectralPoint q).re - θ) + 1 ∈ K := by
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
    finite_offLine_card_mul_directThreeCenterCharge_le_translatedLatticeBudget
      θ K U hoffU hcentersU
  calc
    (S.card : ℝ) * (126976 / 21125 : ℝ) =
        (U.card : ℝ) * (63488 / 21125 : ℝ) := by
      rw [hcardU]
      push_cast
      ring
    _ ≤ criticalFeaturePrimeGammaOffLineTranslatedLatticeBudget θ K := hcharge

/-- Translation-uniform reflected-pair 75% receiver. -/
theorem three_quarters_line_of_reflectedDirectThreeCenter_translatedLatticeBudget
    {N N₀ : ℝ} (θ : ℝ) (K : Finset ℤ) (S : Finset XiZeroCopy)
    (hright : ∀ q ∈ S, 0 < (I * xiSpectralPoint q).re)
    (hcenters : ∀ q ∈ S,
      round ((xiSpectralPoint q).re - θ) - 1 ∈ K ∧
      round ((xiSpectralPoint q).re - θ) ∈ K ∧
      round ((xiSpectralPoint q).re - θ) + 1 ∈ K)
    (hsplit : N = N₀ + 2 * S.card)
    (hbudget : criticalFeaturePrimeGammaOffLineTranslatedLatticeBudget θ K ≤
      (15872 / 21125 : ℝ) * N) :
    3 * N / 4 ≤ N₀ := by
  have hcharge :=
    finite_strictRight_card_mul_reflectedDirectThreeCenterCharge_le_translatedLatticeBudget
      θ K S hright hcenters
  have hcount : (S.card : ℝ) ≤ N / 8 := by
    nlinarith
  nlinarith

end

end RHTower
