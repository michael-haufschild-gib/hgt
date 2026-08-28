import GaloisForLFunctions.RHTower.HedenmalmCriticalFeatureThreeCenterLatticeQuantum

/-!
# Sharp three-center lattice quantum for the corrected critical-feature budget

The three-center receiver already requires the nearest feature and both fixed neighbours in its
height window.  The earlier `84/25` estimate retained the nearest contribution and only the closer
neighbour.  The other neighbour is still at distance at most `3/2`, hence contributes at least
`16/45`.  Keeping this forced third term raises the Hermitian quantum to `836/225`.

After the global holomorphic-sector factor two, every strict-right copy costs `418/225` of corrected
source budget.  Thus `209/900 * N` is sufficient for the 75% receiver.  This is a receiver
improvement only; it does not establish the source-side asymptotic budget ceiling.
-/

open Complex

namespace RHTower

noncomputable section

/-- If a feature center is at most `3/2` from the spectral ordinate, its kernel denominator has
squared norm at most `45/4`.  The proof keeps the joint `u²y²` term instead of bounding the two
squares separately. -/
theorem criticalFeatureDenominatorNormSq_le_fortyFiveFourths
    (t : ℝ) {z : ℂ} (hy : |z.im| ≤ 1 / 2)
    (ht : |z.re - t| ≤ 3 / 2) :
    criticalFeatureDenominatorNormSq t z ≤ 45 / 4 := by
  let u : ℝ := z.re - t
  let y : ℝ := z.im
  have hu2 : u ^ 2 ≤ 9 / 4 := by
    have h := (sq_le_sq₀ (abs_nonneg u) (by norm_num : (0 : ℝ) ≤ 3 / 2)).2
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
      0 ≤ (9 / 4 - u ^ 2) * (u ^ 2 + 17 / 4 + 2 * y ^ 2) := by
    exact mul_nonneg (by linarith) (by nlinarith [sq_nonneg u, sq_nonneg y])
  have hmonoY :
      0 ≤ (1 / 4 - y ^ 2) * (y ^ 2 + 11 / 4) := by
    exact mul_nonneg (by linarith) (by nlinarith [sq_nonneg y])
  rw [criticalFeatureDenominatorNormSq_eq]
  dsimp only [u, y] at hu2 hy2 hmonoU hmonoY ⊢
  ring_nf at hmonoU hmonoY ⊢
  nlinarith

/-- Every critical feature whose center is within distance `3/2` contributes at least `16/45`. -/
theorem sixteen_fortyFive_le_normSq_criticalFeatureCauchyKernelTest
    {t : ℝ} {z : ℂ} (hz : |z.im| < 1 / 2)
    (ht : |z.re - t| ≤ 3 / 2) :
    (16 / 45 : ℝ) ≤
      Complex.normSq (criticalFeatureCauchyKernelTest t z) := by
  have hpos := criticalFeatureDenominatorNormSq_pos t hz
  have hden := criticalFeatureDenominatorNormSq_le_fortyFiveFourths t hz.le ht
  rw [criticalFeatureCauchyKernelTest_eq t hz, Complex.normSq_div]
  norm_num
  change (16 / 45 : ℝ) ≤ 4 / criticalFeatureDenominatorNormSq t z
  apply (le_div_iff₀ hpos).2
  nlinarith

/-- **Sharp three-center local quantum.**  The nearest feature, closer neighbour, and farther
neighbour carry at least `64/25 + 4/5 + 16/45 = 836/225` Hermitian mass. -/
theorem eightHundredThirtySix_twoHundredTwentyFive_le_threeCenterCriticalFeatureEnergy
    {t : ℝ} {z : ℂ} (hz : |z.im| < 1 / 2)
    (ht : |z.re - t| ≤ 1 / 2) :
    (836 / 225 : ℝ) ≤ threeCenterCriticalFeatureEnergy t z := by
  have hcenter : (64 / 25 : ℝ) ≤
      Complex.normSq (criticalFeatureCauchyKernelTest t z) := by
    have heval := normSq_criticalEvaluation_realCriticalFeature_ge_of_abs_sub_le_half
      (t := t) (z := z) hz ht
    rw [criticalEvaluation_realCriticalFeature_eq_hardyCauchySum] at heval
    exact heval
  by_cases hu : 0 ≤ z.re - t
  · have hnearDist : |z.re - (t + 1)| ≤ 1 := by
      rw [abs_le]
      rcases abs_le.mp ht with ⟨htl, htr⟩
      constructor <;> linarith
    have hfarDist : |z.re - (t - 1)| ≤ 3 / 2 := by
      rw [abs_le]
      rcases abs_le.mp ht with ⟨htl, htr⟩
      constructor <;> linarith
    have hnear := four_fifths_le_normSq_criticalFeatureCauchyKernelTest hz hnearDist
    have hfar := sixteen_fortyFive_le_normSq_criticalFeatureCauchyKernelTest hz hfarDist
    rw [threeCenterCriticalFeatureEnergy]
    nlinarith
  · have hu' : z.re - t ≤ 0 := le_of_not_ge hu
    have hnearDist : |z.re - (t - 1)| ≤ 1 := by
      rw [abs_le]
      rcases abs_le.mp ht with ⟨htl, htr⟩
      constructor <;> linarith
    have hfarDist : |z.re - (t + 1)| ≤ 3 / 2 := by
      rw [abs_le]
      rcases abs_le.mp ht with ⟨htl, htr⟩
      constructor <;> linarith
    have hnear := four_fifths_le_normSq_criticalFeatureCauchyKernelTest hz hnearDist
    have hfar := sixteen_fortyFive_le_normSq_criticalFeatureCauchyKernelTest hz hfarDist
    rw [threeCenterCriticalFeatureEnergy]
    nlinarith

/-- Every finite strict-right packet deposits the sharp `836/225` quantum when its nearest centers
and their two fixed neighbours belong to the lattice window. -/
theorem finite_strictRight_card_mul_eightHundredThirtySix_twoHundredTwentyFive_le_offLineLatticeEnergy
    (K : Finset ℤ) (S : Finset XiZeroCopy)
    (hright : ∀ q ∈ S, 0 < (I * xiSpectralPoint q).re)
    (hcenters : ∀ q ∈ S,
      round (xiSpectralPoint q).re - 1 ∈ K ∧
      round (xiSpectralPoint q).re ∈ K ∧
      round (xiSpectralPoint q).re + 1 ∈ K) :
    (S.card : ℝ) * (836 / 225 : ℝ) ≤
      ∑ k ∈ K, offLineCriticalFeatureEnergyTrace (k : ℝ) := by
  calc
    (S.card : ℝ) * (836 / 225 : ℝ) =
        ∑ _q ∈ S, (836 / 225 : ℝ) := by simp
    _ ≤ ∑ q ∈ S, ∑ k ∈ K, offLineCriticalFeatureEnergy (k : ℝ) q := by
      gcongr with q hq
      let kq : ℤ := round (xiSpectralPoint q).re
      have hmem := hcenters q hq
      have hqoff : (q.1 : ℂ).re ≠ 1 / 2 := by
        intro hline
        have hp := hright q hq
        rw [I_mul_xiSpectralPoint, Complex.sub_re, hline] at hp
        norm_num at hp
      have hthree :=
        eightHundredThirtySix_twoHundredTwentyFive_le_threeCenterCriticalFeatureEnergy
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
        (836 / 225 : ℝ) ≤ ∑ j ∈ Tq,
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

/-- Corrected source charge after the global holomorphic-sector factor two. -/
theorem finite_strictRight_card_mul_fourHundredEighteen_twoHundredTwentyFive_le_offLineLatticeBudget
    (K : Finset ℤ) (S : Finset XiZeroCopy)
    (hright : ∀ q ∈ S, 0 < (I * xiSpectralPoint q).re)
    (hcenters : ∀ q ∈ S,
      round (xiSpectralPoint q).re - 1 ∈ K ∧
      round (xiSpectralPoint q).re ∈ K ∧
      round (xiSpectralPoint q).re + 1 ∈ K) :
    (S.card : ℝ) * (418 / 225 : ℝ) ≤
      criticalFeaturePrimeGammaOffLineLatticeBudget K := by
  have hframe :=
    finite_strictRight_card_mul_eightHundredThirtySix_twoHundredTwentyFive_le_offLineLatticeEnergy
      K S hright hcenters
  have hsource :
      (∑ k ∈ K, offLineCriticalFeatureEnergyTrace (k : ℝ)) ≤
        2 * criticalFeaturePrimeGammaOffLineLatticeBudget K := by
    rw [criticalFeaturePrimeGammaOffLineLatticeBudget, Finset.mul_sum]
    gcongr with k hk
    exact offLineCriticalFeatureEnergyTrace_le_two_primeGammaOffLineExcess (k : ℝ)
  nlinarith

/-- **Sharp 75% receiver.**  The forced far-neighbour contribution relaxes the sufficient corrected
source ceiling from `21/100 * N` to `209/900 * N`. -/
theorem three_quarters_line_of_sharpThreeCenter_primeGammaOffLineLatticeBudget
    {N N₀ : ℝ} (K : Finset ℤ) (S : Finset XiZeroCopy)
    (hright : ∀ q ∈ S, 0 < (I * xiSpectralPoint q).re)
    (hcenters : ∀ q ∈ S,
      round (xiSpectralPoint q).re - 1 ∈ K ∧
      round (xiSpectralPoint q).re ∈ K ∧
      round (xiSpectralPoint q).re + 1 ∈ K)
    (hsplit : N = N₀ + 2 * S.card)
    (hbudget : criticalFeaturePrimeGammaOffLineLatticeBudget K ≤
      (209 / 900 : ℝ) * N) :
    3 * N / 4 ≤ N₀ := by
  have hcharge :=
    finite_strictRight_card_mul_fourHundredEighteen_twoHundredTwentyFive_le_offLineLatticeBudget
      K S hright hcenters
  have hcount : (S.card : ℝ) ≤ N / 8 := by
    nlinarith
  nlinarith

end

end RHTower
