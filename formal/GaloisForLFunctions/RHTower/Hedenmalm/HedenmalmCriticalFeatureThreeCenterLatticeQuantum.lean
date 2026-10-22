import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmOrientedAdjacentTransverseDeterminantQuantum
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmCriticalFeatureLatticePrimeGammaBudget

/-!
# Three-center lattice quantum for the corrected critical-feature budget

The original lattice receiver charges each off-line Xi copy only through its nearest integer
feature.  A height window is naturally padded by one lattice site at each end, so both adjacent
features are already available.  The nearest feature contributes `64/25`; one adjacent feature is
within distance one and contributes at least `4/5`.  Keeping both predeclared adjacent features
avoids a divisor-dependent orientation choice and gives the elementary Hermitian quantum `84/25`.

After the global holomorphic-sector factor two, corrected source charge is `42/25`; consequently a
`21/100 * N` source ceiling implies the 75% receiver.  This already subsumes the stronger proposed
`4/25 * N` source ceiling.  No numerical polynomial certificate is needed.
-/

open Complex

namespace RHTower

noncomputable section

/-- Hermitian energy in the nearest feature and its two fixed neighbours. -/
def threeCenterCriticalFeatureEnergy (t : ℝ) (z : ℂ) : ℝ :=
  Complex.normSq (criticalFeatureCauchyKernelTest (t - 1) z) +
    Complex.normSq (criticalFeatureCauchyKernelTest t z) +
    Complex.normSq (criticalFeatureCauchyKernelTest (t + 1) z)

/-- Every critical feature whose center is within distance one contributes at least `4/5`. -/
theorem four_fifths_le_normSq_criticalFeatureCauchyKernelTest
    {t : ℝ} {z : ℂ} (hz : |z.im| < 1 / 2)
    (ht : |z.re - t| ≤ 1) :
    (4 / 5 : ℝ) ≤
      Complex.normSq (criticalFeatureCauchyKernelTest t z) := by
  have hpos := criticalFeatureDenominatorNormSq_pos t hz
  have hden := criticalFeatureDenominatorNormSq_le_five t hz.le ht
  rw [criticalFeatureCauchyKernelTest_eq t hz, Complex.normSq_div]
  norm_num
  change (4 / 5 : ℝ) ≤ 4 / criticalFeatureDenominatorNormSq t z
  apply (le_div_iff₀ hpos).2
  nlinarith

/-- **Three-center local quantum.**  Nearest feature plus two fixed neighbours carry at least
`84/25` Hermitian mass throughout the open critical strip. -/
theorem eightyFour_twentyFive_le_threeCenterCriticalFeatureEnergy
    {t : ℝ} {z : ℂ} (hz : |z.im| < 1 / 2)
    (ht : |z.re - t| ≤ 1 / 2) :
    (84 / 25 : ℝ) ≤ threeCenterCriticalFeatureEnergy t z := by
  have hcenter : (64 / 25 : ℝ) ≤
      Complex.normSq (criticalFeatureCauchyKernelTest t z) := by
    have heval := normSq_criticalEvaluation_realCriticalFeature_ge_of_abs_sub_le_half
      (t := t) (z := z) hz ht
    rw [criticalEvaluation_realCriticalFeature_eq_hardyCauchySum] at heval
    exact heval
  by_cases hu : 0 ≤ z.re - t
  · have hadjdist : |z.re - (t + 1)| ≤ 1 := by
      rw [abs_le]
      rcases abs_le.mp ht with ⟨htl, htr⟩
      constructor <;> linarith
    have hadj := four_fifths_le_normSq_criticalFeatureCauchyKernelTest
      hz hadjdist
    rw [threeCenterCriticalFeatureEnergy]
    nlinarith [Complex.normSq_nonneg
      (criticalFeatureCauchyKernelTest (t - 1) z)]
  · have hu' : z.re - t ≤ 0 := le_of_not_ge hu
    have hadjdist : |z.re - (t - 1)| ≤ 1 := by
      rw [abs_le]
      rcases abs_le.mp ht with ⟨htl, htr⟩
      constructor <;> linarith
    have hadj := four_fifths_le_normSq_criticalFeatureCauchyKernelTest
      hz hadjdist
    rw [threeCenterCriticalFeatureEnergy]
    nlinarith [Complex.normSq_nonneg
      (criticalFeatureCauchyKernelTest (t + 1) z)]

/-- Every finite strict-right packet deposits the elementary `84/25` quantum when its nearest
centers and their two neighbours belong to the lattice window. -/
theorem finite_strictRight_card_mul_eightyFour_twentyFive_le_offLineLatticeEnergy
    (K : Finset ℤ) (S : Finset XiZeroCopy)
    (hright : ∀ q ∈ S, 0 < (I * xiSpectralPoint q).re)
    (hcenters : ∀ q ∈ S,
      round (xiSpectralPoint q).re - 1 ∈ K ∧
      round (xiSpectralPoint q).re ∈ K ∧
      round (xiSpectralPoint q).re + 1 ∈ K) :
    (S.card : ℝ) * (84 / 25 : ℝ) ≤
      ∑ k ∈ K, offLineCriticalFeatureEnergyTrace (k : ℝ) := by
  calc
    (S.card : ℝ) * (84 / 25 : ℝ) =
        ∑ _q ∈ S, (84 / 25 : ℝ) := by simp
    _ ≤ ∑ q ∈ S, ∑ k ∈ K, offLineCriticalFeatureEnergy (k : ℝ) q := by
      gcongr with q hq
      let kq : ℤ := round (xiSpectralPoint q).re
      have hmem := hcenters q hq
      have hqoff : (q.1 : ℂ).re ≠ 1 / 2 := by
        intro hline
        have hp := hright q hq
        rw [I_mul_xiSpectralPoint, Complex.sub_re, hline] at hp
        norm_num at hp
      have hthree := eightyFour_twentyFive_le_threeCenterCriticalFeatureEnergy
        (z := xiSpectralPoint q) (t := (kq : ℝ))
        (abs_xiSpectralPoint_im_lt_half q) (abs_sub_round _)
      have hoffeq (j : ℤ) :
          Complex.normSq
              (criticalFeatureCauchyKernelTest (j : ℝ) (xiSpectralPoint q)) =
            offLineCriticalFeatureEnergy (j : ℝ) q := by
        rw [offLineCriticalFeatureEnergy, if_neg hqoff]
      have hcastm : (kq : ℝ) - 1 = ((kq - 1 : ℤ) : ℝ) := by
        exact_mod_cast (rfl : kq - 1 = kq - 1)
      have hcastp : (kq : ℝ) + 1 = ((kq + 1 : ℤ) : ℝ) := by
        exact_mod_cast (rfl : kq + 1 = kq + 1)
      rw [threeCenterCriticalFeatureEnergy, hcastm, hcastp,
        hoffeq, hoffeq, hoffeq] at hthree
      let Tq : Finset ℤ := {kq - 1, kq, kq + 1}
      have hTq : Tq ⊆ K := by
        intro j hj
        simp only [Tq, Finset.mem_insert, Finset.mem_singleton] at hj
        rcases hj with hj | hj | hj
        · simpa [hj] using hmem.1
        · simpa [hj] using hmem.2.1
        · simpa [hj] using hmem.2.2
      have hsumTq :
          (∑ j ∈ Tq, offLineCriticalFeatureEnergy (j : ℝ) q) =
            offLineCriticalFeatureEnergy ((kq - 1 : ℤ) : ℝ) q +
              offLineCriticalFeatureEnergy (kq : ℝ) q +
              offLineCriticalFeatureEnergy ((kq + 1 : ℤ) : ℝ) q := by
        have hm0 : kq - 1 ≠ kq := by omega
        have hmp : kq - 1 ≠ kq + 1 := by omega
        have h0p : kq ≠ kq + 1 := by omega
        simp [Tq, hm0, hmp, h0p]
        ring
      calc
        (84 / 25 : ℝ) ≤ ∑ j ∈ Tq,
            offLineCriticalFeatureEnergy (j : ℝ) q := by
          rw [hsumTq]
          simpa [Int.cast_sub, Int.cast_add] using hthree
        _ ≤ ∑ j ∈ K, offLineCriticalFeatureEnergy (j : ℝ) q := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hTq
          intro j hjK hjTq
          exact offLineCriticalFeatureEnergy_nonneg (j : ℝ) q
    _ = ∑ k ∈ K, ∑ q ∈ S, offLineCriticalFeatureEnergy (k : ℝ) q := by
      rw [Finset.sum_comm]
    _ ≤ ∑ k ∈ K, offLineCriticalFeatureEnergyTrace (k : ℝ) := by
      gcongr with k hk
      exact (offLineCriticalFeatureEnergy_summable (k : ℝ)).sum_le_tsum S
        (fun q _ => offLineCriticalFeatureEnergy_nonneg (k : ℝ) q)

/-- Corrected source charge after the sharp holomorphic-sector factor two. -/
theorem finite_strictRight_card_mul_fortyTwo_twentyFive_le_offLineLatticeBudget
    (K : Finset ℤ) (S : Finset XiZeroCopy)
    (hright : ∀ q ∈ S, 0 < (I * xiSpectralPoint q).re)
    (hcenters : ∀ q ∈ S,
      round (xiSpectralPoint q).re - 1 ∈ K ∧
      round (xiSpectralPoint q).re ∈ K ∧
      round (xiSpectralPoint q).re + 1 ∈ K) :
    (S.card : ℝ) * (42 / 25 : ℝ) ≤
      criticalFeaturePrimeGammaOffLineLatticeBudget K := by
  have hframe :=
    finite_strictRight_card_mul_eightyFour_twentyFive_le_offLineLatticeEnergy
      K S hright hcenters
  have hsource :
      (∑ k ∈ K, offLineCriticalFeatureEnergyTrace (k : ℝ)) ≤
        2 * criticalFeaturePrimeGammaOffLineLatticeBudget K := by
    rw [criticalFeaturePrimeGammaOffLineLatticeBudget, Finset.mul_sum]
    gcongr with k hk
    exact offLineCriticalFeatureEnergyTrace_le_two_primeGammaOffLineExcess (k : ℝ)
  nlinarith

/-- **Strengthened 75% receiver.**  Three-center geometry relaxes the sufficient corrected-source
ceiling from `4/25 * N` to `21/100 * N`. -/
theorem three_quarters_line_of_threeCenter_primeGammaOffLineLatticeBudget
    {N N₀ : ℝ} (K : Finset ℤ) (S : Finset XiZeroCopy)
    (hright : ∀ q ∈ S, 0 < (I * xiSpectralPoint q).re)
    (hcenters : ∀ q ∈ S,
      round (xiSpectralPoint q).re - 1 ∈ K ∧
      round (xiSpectralPoint q).re ∈ K ∧
      round (xiSpectralPoint q).re + 1 ∈ K)
    (hsplit : N = N₀ + 2 * S.card)
    (hbudget : criticalFeaturePrimeGammaOffLineLatticeBudget K ≤
      (21 / 100 : ℝ) * N) :
    3 * N / 4 ≤ N₀ := by
  have hcharge :=
    finite_strictRight_card_mul_fortyTwo_twentyFive_le_offLineLatticeBudget
      K S hright hcenters
  have hcount : (S.card : ℝ) ≤ N / 8 := by
    nlinarith
  nlinarith

end

end RHTower
