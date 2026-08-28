/-
# Direct three-center holomorphic charge for HCF

Critical-line subtraction turns the prime--Gamma source diagonal into the exact off-line trace of
real holomorphic squares.  Using that trace directly retains the nearest-cell sector improvement
and raises the three-center source charge from `11616/4225` to `63488/21125` per strict-right copy.
-/
import GaloisForLFunctions.RHTower.HedenmalmCriticalFeatureThreeCenterSharpQuantum
import GaloisForLFunctions.RHTower.HedenmalmCriticalFeatureThreeCenterHolomorphicSector

open Complex

namespace RHTower

noncomputable section

/-- Off-line part of the real holomorphic critical-feature square. -/
def offLineCriticalFeatureHolomorphicEnergy (t : ℝ) (q : XiZeroCopy) : ℝ :=
  if (q.1 : ℂ).re = 1 / 2 then 0
  else ((criticalFeatureCauchyKernelTest t (xiSpectralPoint q)) ^ 2).re

private theorem criticalFeatureHolomorphicSquare_re_nonneg
    (t : ℝ) (q : XiZeroCopy) :
    0 ≤ ((criticalFeatureCauchyKernelTest t (xiSpectralPoint q)) ^ 2).re := by
  have hsector := half_mul_normSq_criticalFeatureCauchyKernelTest_le_re_sq
    t (abs_xiSpectralPoint_im_lt_half q)
  nlinarith [Complex.normSq_nonneg
    (criticalFeatureCauchyKernelTest t (xiSpectralPoint q))]

theorem offLineCriticalFeatureHolomorphicEnergy_nonneg
    (t : ℝ) (q : XiZeroCopy) :
    0 ≤ offLineCriticalFeatureHolomorphicEnergy t q := by
  rw [offLineCriticalFeatureHolomorphicEnergy]
  split_ifs
  · exact le_rfl
  · exact criticalFeatureHolomorphicSquare_re_nonneg t q

private theorem criticalFeatureHolomorphicSquare_re_summable (t : ℝ) :
    Summable (fun q : XiZeroCopy =>
      ((criticalFeatureCauchyKernelTest t (xiSpectralPoint q)) ^ 2).re) := by
  let F : ℂ → ℂ := criticalFeatureCauchyKernelTest t
  have hF := criticalFeatureCauchyKernelTest_squareSummable t
  rw [XiWeilSquareSummable] at hF
  have hsquareNorm : Summable (fun q : XiZeroCopy =>
      ‖(F (xiSpectralPoint q)) ^ 2‖) := by
    simpa only [norm_pow] using hF
  have hsquare : Summable (fun q : XiZeroCopy =>
      (F (xiSpectralPoint q)) ^ 2) :=
    summable_norm_iff.mp hsquareNorm
  exact (hsquare.map Complex.reCLM Complex.reCLM.continuous).congr
    (fun q => rfl)

theorem offLineCriticalFeatureHolomorphicEnergy_summable (t : ℝ) :
    Summable (offLineCriticalFeatureHolomorphicEnergy t) := by
  exact Summable.of_nonneg_of_le
    (offLineCriticalFeatureHolomorphicEnergy_nonneg t)
    (fun q => by
      rw [offLineCriticalFeatureHolomorphicEnergy]
      split_ifs
      · exact criticalFeatureHolomorphicSquare_re_nonneg t q
      · exact le_rfl)
    (criticalFeatureHolomorphicSquare_re_summable t)

private theorem criticalFeaturePrimeGammaSourceDiagonal_re_eq_tsum_holomorphicSquare
    (t : ℝ) :
    (criticalFeaturePrimeGammaSourceDiagonal t).re =
      ∑' q : XiZeroCopy,
        ((criticalFeatureCauchyKernelTest t (xiSpectralPoint q)) ^ 2).re := by
  let F : ℂ → ℂ := criticalFeatureCauchyKernelTest t
  have hF := criticalFeatureCauchyKernelTest_squareSummable t
  rw [XiWeilSquareSummable] at hF
  have hsquareNorm : Summable (fun q : XiZeroCopy =>
      ‖(F (xiSpectralPoint q)) ^ 2‖) := by
    simpa only [norm_pow] using hF
  have hsquare : Summable (fun q : XiZeroCopy =>
      (F (xiSpectralPoint q)) ^ 2) :=
    summable_norm_iff.mp hsquareNorm
  calc
    (criticalFeaturePrimeGammaSourceDiagonal t).re =
        (xiWeilPolarization F F).re := by
      rw [xiWeilPolarization_criticalFeatureCauchyKernelTest_eq_sourceDiagonal]
    _ = (∑' q : XiZeroCopy, (F (xiSpectralPoint q)) ^ 2).re := by
      unfold xiWeilPolarization
      rw [show xiWeilSharp F = F by
        simpa only [F] using xiWeilSharp_criticalFeatureCauchyKernelTest t]
      congr 2
      apply tsum_congr
      intro q
      ring
    _ = ∑' q : XiZeroCopy, ((F (xiSpectralPoint q)) ^ 2).re := by
      rw [Complex.re_tsum hsquare]

private theorem criticalLineEnergy_add_offLineHolomorphicEnergy_eq
    (t : ℝ) (q : XiZeroCopy) :
    criticalLineCriticalFeatureEnergy t q +
        offLineCriticalFeatureHolomorphicEnergy t q =
      ((criticalFeatureCauchyKernelTest t (xiSpectralPoint q)) ^ 2).re := by
  by_cases hq : (q.1 : ℂ).re = 1 / 2
  · rw [criticalLineCriticalFeatureEnergy, if_pos hq,
      offLineCriticalFeatureHolomorphicEnergy, if_pos hq, add_zero]
    have hspim : (xiSpectralPoint q).im = 0 := by
      rw [xiSpectralPoint_im_eq, hq]
      ring
    have heq :
        HedenmalmThetaSource.criticalEvaluation
            (xiSpectralPoint q) (abs_xiSpectralPoint_im_lt_half q)
            (HedenmalmThetaSource.criticalFeature (t : ℂ) (by norm_num)) =
          criticalFeatureCauchyKernelTest t (xiSpectralPoint q) := by
      rw [criticalEvaluation_realCriticalFeature_eq_hardyCauchySum]
      rfl
    have hFim :
        (criticalFeatureCauchyKernelTest t (xiSpectralPoint q)).im = 0 := by
      rw [← heq]
      exact criticalEvaluation_realCriticalFeature_im_eq_zero_of_im_eq_zero
        t (abs_xiSpectralPoint_im_lt_half q) hspim
    rw [Complex.normSq_apply]
    simp [pow_two, Complex.mul_re, hFim]
  · rw [criticalLineCriticalFeatureEnergy, if_neg hq,
      offLineCriticalFeatureHolomorphicEnergy, if_neg hq, zero_add]

/-- Exact trace identity: critical-line subtraction leaves precisely the off-line real
holomorphic-square trace. -/
theorem criticalFeaturePrimeGammaOffLineExcess_eq_tsum_offLineHolomorphicEnergy
    (t : ℝ) :
    criticalFeaturePrimeGammaOffLineExcess t =
      ∑' q : XiZeroCopy, offLineCriticalFeatureHolomorphicEnergy t q := by
  have hline := criticalLineCriticalFeatureEnergy_summable t
  have hoff := offLineCriticalFeatureHolomorphicEnergy_summable t
  have hsplit :
      (criticalFeaturePrimeGammaSourceDiagonal t).re =
        criticalLineCriticalFeatureEnergyTrace t +
          ∑' q : XiZeroCopy, offLineCriticalFeatureHolomorphicEnergy t q := by
    calc
      (criticalFeaturePrimeGammaSourceDiagonal t).re =
          ∑' q : XiZeroCopy,
            ((criticalFeatureCauchyKernelTest t (xiSpectralPoint q)) ^ 2).re :=
        criticalFeaturePrimeGammaSourceDiagonal_re_eq_tsum_holomorphicSquare t
      _ = ∑' q : XiZeroCopy,
          (criticalLineCriticalFeatureEnergy t q +
            offLineCriticalFeatureHolomorphicEnergy t q) := by
        apply tsum_congr
        intro q
        exact (criticalLineEnergy_add_offLineHolomorphicEnergy_eq t q).symm
      _ = criticalLineCriticalFeatureEnergyTrace t +
          ∑' q : XiZeroCopy, offLineCriticalFeatureHolomorphicEnergy t q := by
        rw [hline.tsum_add hoff]
        rfl
  rw [criticalFeaturePrimeGammaOffLineExcess]
  linarith

/-- Direct three-center holomorphic charge.  The nearest-cell sector surplus is retained after
the sharp Hermitian three-center optimization. -/
theorem directThreeCenterCriticalFeatureHolomorphicCharge_lower
    {t : ℝ} {z : ℂ} (hz : |z.im| < 1 / 2)
    (ht : |z.re - t| ≤ 1 / 2) :
    (63488 / 21125 : ℝ) ≤
      ((criticalFeatureCauchyKernelTest (t - 1) z) ^ 2).re +
        ((criticalFeatureCauchyKernelTest t z) ^ 2).re +
        ((criticalFeatureCauchyKernelTest (t + 1) z) ^ 2).re := by
  have hthree := sharp_threeCenterCriticalFeatureEnergy_lower hz ht
  rw [threeCenterCriticalFeatureEnergy] at hthree
  have hcenter : (64 / 25 : ℝ) ≤
      Complex.normSq (criticalFeatureCauchyKernelTest t z) := by
    have heval := normSq_criticalEvaluation_realCriticalFeature_ge_of_abs_sub_le_half
      (t := t) (z := z) hz ht
    rw [criticalEvaluation_realCriticalFeature_eq_hardyCauchySum] at heval
    exact heval
  have hcenterSector :=
    three_fifths_mul_normSq_criticalFeatureCauchyKernelTest_le_re_sq t hz ht
  have hminusSector :=
    half_mul_normSq_criticalFeatureCauchyKernelTest_le_re_sq (t - 1) hz
  have hplusSector :=
    half_mul_normSq_criticalFeatureCauchyKernelTest_le_re_sq (t + 1) hz
  nlinarith

/-- Every finite strict-right packet deposits the direct holomorphic charge in the corrected
prime--Gamma lattice budget. -/
theorem finite_strictRight_card_mul_directThreeCenterCharge_le_offLineLatticeBudget
    (K : Finset ℤ) (S : Finset XiZeroCopy)
    (hright : ∀ q ∈ S, 0 < (I * xiSpectralPoint q).re)
    (hcenters : ∀ q ∈ S,
      round (xiSpectralPoint q).re - 1 ∈ K ∧
      round (xiSpectralPoint q).re ∈ K ∧
      round (xiSpectralPoint q).re + 1 ∈ K) :
    (S.card : ℝ) * (63488 / 21125 : ℝ) ≤
      criticalFeaturePrimeGammaOffLineLatticeBudget K := by
  calc
    (S.card : ℝ) * (63488 / 21125 : ℝ) =
        ∑ _q ∈ S, (63488 / 21125 : ℝ) := by simp
    _ ≤ ∑ q ∈ S, ∑ k ∈ K,
        offLineCriticalFeatureHolomorphicEnergy (k : ℝ) q := by
      gcongr with q hq
      let kq : ℤ := round (xiSpectralPoint q).re
      have hmem := hcenters q hq
      have hqoff : (q.1 : ℂ).re ≠ 1 / 2 := by
        intro hline
        have hp := hright q hq
        rw [I_mul_xiSpectralPoint, Complex.sub_re, hline] at hp
        norm_num at hp
      have hthree :=
        directThreeCenterCriticalFeatureHolomorphicCharge_lower
          (z := xiSpectralPoint q) (t := (kq : ℝ))
          (abs_xiSpectralPoint_im_lt_half q) (abs_sub_round _)
      have hoffeq (j : ℤ) :
          ((criticalFeatureCauchyKernelTest (j : ℝ)
            (xiSpectralPoint q)) ^ 2).re =
            offLineCriticalFeatureHolomorphicEnergy (j : ℝ) q := by
        rw [offLineCriticalFeatureHolomorphicEnergy, if_neg hqoff]
      have hcastm : (kq : ℝ) - 1 = ((kq - 1 : ℤ) : ℝ) := by
        exact_mod_cast (rfl : kq - 1 = kq - 1)
      have hcastp : (kq : ℝ) + 1 = ((kq + 1 : ℤ) : ℝ) := by
        exact_mod_cast (rfl : kq + 1 = kq + 1)
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
          (∑ j ∈ Tq, offLineCriticalFeatureHolomorphicEnergy (j : ℝ) q) =
            offLineCriticalFeatureHolomorphicEnergy ((kq - 1 : ℤ) : ℝ) q +
              offLineCriticalFeatureHolomorphicEnergy (kq : ℝ) q +
              offLineCriticalFeatureHolomorphicEnergy ((kq + 1 : ℤ) : ℝ) q := by
        have hm0 : kq - 1 ≠ kq := by omega
        have hmp : kq - 1 ≠ kq + 1 := by omega
        have h0p : kq ≠ kq + 1 := by omega
        simp [Tq, hm0, hmp, h0p]
        ring
      calc
        (63488 / 21125 : ℝ) ≤ ∑ j ∈ Tq,
            offLineCriticalFeatureHolomorphicEnergy (j : ℝ) q := by
          rw [hsumTq]
          simpa [Int.cast_sub, Int.cast_add] using hthree
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

/-- Improved exact three-center 75% receiver.  Direct holomorphic charge relaxes the sufficient
corrected-source ceiling from `1452/4225` to `7936/21125`. -/
theorem three_quarters_line_of_directThreeCenter_primeGammaOffLineLatticeBudget
    {N N₀ : ℝ} (K : Finset ℤ) (S : Finset XiZeroCopy)
    (hright : ∀ q ∈ S, 0 < (I * xiSpectralPoint q).re)
    (hcenters : ∀ q ∈ S,
      round (xiSpectralPoint q).re - 1 ∈ K ∧
      round (xiSpectralPoint q).re ∈ K ∧
      round (xiSpectralPoint q).re + 1 ∈ K)
    (hsplit : N = N₀ + 2 * S.card)
    (hbudget : criticalFeaturePrimeGammaOffLineLatticeBudget K ≤
      (7936 / 21125 : ℝ) * N) :
    3 * N / 4 ≤ N₀ := by
  have hcharge :=
    finite_strictRight_card_mul_directThreeCenterCharge_le_offLineLatticeBudget
      K S hright hcenters
  have hcount : (S.card : ℝ) ≤ N / 8 := by
    nlinarith
  nlinarith

end

end RHTower
