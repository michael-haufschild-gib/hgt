import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmCriticalFeatureThreeCenterLatticeQuantum

/-!
# Sharp three-center lattice quantum for the corrected critical-feature budget

The three-center receiver already requires the nearest feature and both fixed neighbours in its
height window.  The earlier `84/25` estimate retained the nearest contribution and only the closer
neighbour.  A first termwise repair keeps the other neighbour and raises the Hermitian quantum to
`836/225`.  Joint optimization of all three denominators then gives the exact minimum
`23232/4225`, attained at half-cell points on the critical axis.

After the global holomorphic-sector factor two, every strict-right copy costs `11616/4225` of
corrected source budget.  Thus `1452/4225 * N` is sufficient for the 75% receiver.  This is a
receiver improvement only; it does not establish the source-side asymptotic budget ceiling.
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
  have hu2 : u ^ (2 : ℕ) ≤ 9 / 4 := by
    have h := (sq_le_sq₀ (abs_nonneg u) (by norm_num : (0 : ℝ) ≤ 3 / 2)).2
      (by simpa [u] using ht)
    rw [sq_abs] at h
    norm_num at h ⊢
    exact h
  have hy2 : y ^ (2 : ℕ) ≤ 1 / 4 := by
    have h := (sq_le_sq₀ (abs_nonneg y) (by norm_num : (0 : ℝ) ≤ 1 / 2)).2
      (by simpa [y] using hy)
    rw [sq_abs] at h
    norm_num at h ⊢
    exact h
  have hmonoU :
      0 ≤ (9 / 4 - u ^ (2 : ℕ)) * (u ^ (2 : ℕ) + 17 / 4 + 2 * y ^ (2 : ℕ)) := by
    exact mul_nonneg (by linarith) (by nlinarith [sq_nonneg u, sq_nonneg y])
  have hmonoY :
      0 ≤ (1 / 4 - y ^ (2 : ℕ)) * (y ^ (2 : ℕ) + 11 / 4) := by
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

/-! ## Exact three-center quantum -/
namespace RHTower

noncomputable section

/-- Cleared-denominator form of the exact three-center lower bound.  With
`x = 4u²` and `p = 1 - 4y²`, its numerator has a nonnegative degree-six tensor Bernstein
certificate on `[0,1]²`. -/
theorem threeCenterCriticalFeatureDenominatorCleared_nonneg
    {u y : ℝ} (hu : |u| ≤ 1 / 2) (hy : |y| ≤ 1 / 2) :
    let dm := (1 + (u + 1) ^ (2 : ℕ) - y ^ (2 : ℕ)) ^ (2 : ℕ) + (2 * (u + 1) * y) ^ (2 : ℕ)
    let d0 := (1 + u ^ (2 : ℕ) - y ^ (2 : ℕ)) ^ (2 : ℕ) + (2 * u * y) ^ (2 : ℕ)
    let dp := (1 + (u - 1) ^ (2 : ℕ) - y ^ (2 : ℕ)) ^ (2 : ℕ) + (2 * (u - 1) * y) ^ (2 : ℕ)
    0 ≤ 16900 * (dm * d0 + dm * dp + d0 * dp) - 23232 * dm * d0 * dp := by
  let dm := (1 + (u + 1) ^ (2 : ℕ) - y ^ (2 : ℕ)) ^ (2 : ℕ) + (2 * (u + 1) * y) ^ (2 : ℕ)
  let d0 := (1 + u ^ (2 : ℕ) - y ^ (2 : ℕ)) ^ (2 : ℕ) + (2 * u * y) ^ (2 : ℕ)
  let dp := (1 + (u - 1) ^ (2 : ℕ) - y ^ (2 : ℕ)) ^ (2 : ℕ) + (2 * (u - 1) * y) ^ (2 : ℕ)
  let x : ℝ := 4 * u ^ (2 : ℕ)
  let p : ℝ := 1 - 4 * y ^ (2 : ℕ)
  have hu2 : u ^ (2 : ℕ) ≤ 1 / 4 := by
    have h := (sq_le_sq₀ (abs_nonneg u) (by norm_num : (0 : ℝ) ≤ 1 / 2)).2 hu
    rw [sq_abs] at h
    norm_num at h ⊢
    exact h
  have hy2 : y ^ (2 : ℕ) ≤ 1 / 4 := by
    have h := (sq_le_sq₀ (abs_nonneg y) (by norm_num : (0 : ℝ) ≤ 1 / 2)).2 hy
    rw [sq_abs] at h
    norm_num at h ⊢
    exact h
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hx1 : 0 ≤ 1 - x := by dsimp [x]; nlinarith
  have hp0 : 0 ≤ p := by dsimp [p]; nlinarith
  have hp1 : 0 ≤ 1 - p := by dsimp [p]; nlinarith [sq_nonneg y]
  have hcert :
      16900 * (dm * d0 + dm * dp + d0 * dp) - 23232 * dm * d0 * dp =
      (1 - x) ^ (6 : ℕ) * (
        (561925/4 : ℝ) * (1 - p) ^ (6 : ℕ) +
        (23818535/192 : ℝ) * 6 * p * (1 - p) ^ (5 : ℕ) +
        (103008227/960 : ℝ) * 15 * p ^ (2 : ℕ) * (1 - p) ^ (4 : ℕ) +
        (7206919/80 : ℝ) * 20 * p ^ (3 : ℕ) * (1 - p) ^ (3 : ℕ) +
        (2167529/30 : ℝ) * 15 * p ^ (4 : ℕ) * (1 - p) ^ (2 : ℕ) +
        (160792/3 : ℝ) * 6 * p ^ (5 : ℕ) * (1 - p) +
        (33888 : ℝ) * p ^ (6 : ℕ)) +
      6 * x * (1 - x) ^ (5 : ℕ) * (
        (22977169/192 : ℝ) * (1 - p) ^ (6 : ℕ) +
        (40763873/384 : ℝ) * 6 * p * (1 - p) ^ (5 : ℕ) +
        (88330277/960 : ℝ) * 15 * p ^ (2 : ℕ) * (1 - p) ^ (4 : ℕ) +
        (147987403/1920 : ℝ) * 20 * p ^ (3 : ℕ) * (1 - p) ^ (3 : ℕ) +
        (7339393/120 : ℝ) * 15 * p ^ (4 : ℕ) * (1 - p) ^ (2 : ℕ) +
        (528475/12 : ℝ) * 6 * p ^ (5 : ℕ) * (1 - p) +
        (76336/3 : ℝ) * p ^ (6 : ℕ)) +
      15 * x ^ (2 : ℕ) * (1 - x) ^ (4 : ℕ) * (
        (33258669/320 : ℝ) * (1 - p) ^ (6 : ℕ) +
        (17778011/192 : ℝ) * 6 * p * (1 - p) ^ (5 : ℕ) +
        (2008996/25 : ℝ) * 15 * p ^ (2 : ℕ) * (1 - p) ^ (4 : ℕ) +
        (107267923/1600 : ℝ) * 20 * p ^ (3 : ℕ) * (1 - p) ^ (3 : ℕ) +
        (125807347/2400 : ℝ) * 15 * p ^ (4 : ℕ) * (1 - p) ^ (2 : ℕ) +
        (1449473/40 : ℝ) * 6 * p ^ (5 : ℕ) * (1 - p) +
        (182003/10 : ℝ) * p ^ (6 : ℕ)) +
      20 * x ^ (3 : ℕ) * (1 - x) ^ (3 : ℕ) * (
        (14942899/160 : ℝ) * (1 - p) ^ (6 : ℕ) +
        (160272419/1920 : ℝ) * 6 * p * (1 - p) ^ (5 : ℕ) +
        (347661409/4800 : ℝ) * 15 * p ^ (2 : ℕ) * (1 - p) ^ (4 : ℕ) +
        (384251693/6400 : ℝ) * 20 * p ^ (3 : ℕ) * (1 - p) ^ (3 : ℕ) +
        (44212069/960 : ℝ) * 15 * p ^ (4 : ℕ) * (1 - p) ^ (2 : ℕ) +
        (11593151/384 : ℝ) * 6 * p ^ (5 : ℕ) * (1 - p) +
        (194025/16 : ℝ) * p ^ (6 : ℕ)) +
      15 * x ^ (4 : ℕ) * (1 - x) ^ (2 : ℕ) * (
        (2115029/24 : ℝ) * (1 - p) ^ (6 : ℕ) +
        (18925019/240 : ℝ) * 6 * p * (1 - p) ^ (5 : ℕ) +
        (163804367/2400 : ℝ) * 15 * p ^ (2 : ℕ) * (1 - p) ^ (4 : ℕ) +
        (53833229/960 : ℝ) * 20 * p ^ (3 : ℕ) * (1 - p) ^ (3 : ℕ) +
        (12614821/300 : ℝ) * 15 * p ^ (4 : ℕ) * (1 - p) ^ (2 : ℕ) +
        (24824909/960 : ℝ) * 6 * p ^ (5 : ℕ) * (1 - p) +
        (1374055/192 : ℝ) * p ^ (6 : ℕ)) +
      6 * x ^ (5 : ℕ) * (1 - x) * (
        (176275/2 : ℝ) * (1 - p) ^ (6 : ℕ) +
        (3778565/48 : ℝ) * 6 * p * (1 - p) ^ (5 : ℕ) +
        (5423861/80 : ℝ) * 15 * p ^ (2 : ℕ) * (1 - p) ^ (4 : ℕ) +
        (35267121/640 : ℝ) * 20 * p ^ (3 : ℕ) * (1 - p) ^ (3 : ℕ) +
        (38721967/960 : ℝ) * 15 * p ^ (4 : ℕ) * (1 - p) ^ (2 : ℕ) +
        (2963275/128 : ℝ) * 6 * p ^ (5 : ℕ) * (1 - p) +
        (203125/64 : ℝ) * p ^ (6 : ℕ)) +
      x ^ (6 : ℕ) * (
        (373375/4 : ℝ) * (1 - p) ^ (6 : ℕ) +
        (497875/6 : ℝ) * 6 * p * (1 - p) ^ (5 : ℕ) +
        (1703093/24 : ℝ) * 15 * p ^ (2 : ℕ) * (1 - p) ^ (4 : ℕ) +
        (9120527/160 : ℝ) * 20 * p ^ (3 : ℕ) * (1 - p) ^ (3 : ℕ) +
        (39142183/960 : ℝ) * 15 * p ^ (4 : ℕ) * (1 - p) ^ (2 : ℕ) +
        (4206025/192 : ℝ) * 6 * p ^ (5 : ℕ) * (1 - p)) := by
    dsimp [dm, d0, dp, x, p]
    ring
  dsimp only
  rw [hcert]
  positivity

end

end RHTower

namespace RHTower

noncomputable section

/-- Squared critical-feature amplitude as four divided by its positive denominator norm. -/
theorem normSq_criticalFeatureCauchyKernelTest_eq_four_div
    (t : ℝ) {z : ℂ} (hz : |z.im| < 1 / 2) :
    Complex.normSq (criticalFeatureCauchyKernelTest t z) =
      4 / criticalFeatureDenominatorNormSq t z := by
  rw [criticalFeatureCauchyKernelTest_eq t hz, Complex.normSq_div]
  norm_num [criticalFeatureDenominatorNormSq]

/-- **Exact three-center local quantum.**  Joint denominator optimization gives
`23232/4225`; the separate termwise bounds lose more than thirty percent. -/
theorem sharp_threeCenterCriticalFeatureEnergy_lower
    {t : ℝ} {z : ℂ} (hz : |z.im| < 1 / 2)
    (ht : |z.re - t| ≤ 1 / 2) :
    (23232 / 4225 : ℝ) ≤ threeCenterCriticalFeatureEnergy t z := by
  let dm := criticalFeatureDenominatorNormSq (t - 1) z
  let d0 := criticalFeatureDenominatorNormSq t z
  let dp := criticalFeatureDenominatorNormSq (t + 1) z
  have hmpos : 0 < dm := criticalFeatureDenominatorNormSq_pos (t - 1) hz
  have h0pos : 0 < d0 := criticalFeatureDenominatorNormSq_pos t hz
  have hppos : 0 < dp := criticalFeatureDenominatorNormSq_pos (t + 1) hz
  have hclear0 := threeCenterCriticalFeatureDenominatorCleared_nonneg
    (u := z.re - t) (y := z.im) ht hz.le
  have hclear :
      0 ≤ 16900 * (dm * d0 + dm * dp + d0 * dp) -
        23232 * dm * d0 * dp := by
    dsimp only at hclear0
    dsimp [dm, d0, dp]
    rw [criticalFeatureDenominatorNormSq_eq,
      criticalFeatureDenominatorNormSq_eq,
      criticalFeatureDenominatorNormSq_eq]
    convert hclear0 using 1
    all_goals ring
  have hprod : 0 < dm * d0 * dp := mul_pos (mul_pos hmpos h0pos) hppos
  have hfrac :
      4 / dm + 4 / d0 + 4 / dp =
        4 * (dm * d0 + dm * dp + d0 * dp) / (dm * d0 * dp) := by
    field_simp
    ring
  rw [threeCenterCriticalFeatureEnergy,
    normSq_criticalFeatureCauchyKernelTest_eq_four_div (t - 1) hz,
    normSq_criticalFeatureCauchyKernelTest_eq_four_div t hz,
    normSq_criticalFeatureCauchyKernelTest_eq_four_div (t + 1) hz]
  change (23232 / 4225 : ℝ) ≤ 4 / dm + 4 / d0 + 4 / dp
  rw [hfrac]
  apply (le_div_iff₀ hprod).2
  nlinarith

end


end RHTower

namespace RHTower

noncomputable section

/-- Exact local minimum propagated through a finite strict-right Xi packet. -/
theorem finite_strictRight_card_mul_sharpThreeCenterQuantum_le_offLineLatticeEnergy
    (K : Finset ℤ) (S : Finset XiZeroCopy)
    (hright : ∀ q ∈ S, 0 < (I * xiSpectralPoint q).re)
    (hcenters : ∀ q ∈ S,
      round (xiSpectralPoint q).re - 1 ∈ K ∧
      round (xiSpectralPoint q).re ∈ K ∧
      round (xiSpectralPoint q).re + 1 ∈ K) :
    (S.card : ℝ) * (23232 / 4225 : ℝ) ≤
      ∑ k ∈ K, offLineCriticalFeatureEnergyTrace (k : ℝ) := by
  calc
    (S.card : ℝ) * (23232 / 4225 : ℝ) =
        ∑ _q ∈ S, (23232 / 4225 : ℝ) := by simp
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
        sharp_threeCenterCriticalFeatureEnergy_lower
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
        (23232 / 4225 : ℝ) ≤ ∑ j ∈ Tq,
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

/-- Exact three-center source charge after the global holomorphic-sector factor two. -/
theorem finite_strictRight_card_mul_sharpThreeCenterSourceCharge_le_offLineLatticeBudget
    (K : Finset ℤ) (S : Finset XiZeroCopy)
    (hright : ∀ q ∈ S, 0 < (I * xiSpectralPoint q).re)
    (hcenters : ∀ q ∈ S,
      round (xiSpectralPoint q).re - 1 ∈ K ∧
      round (xiSpectralPoint q).re ∈ K ∧
      round (xiSpectralPoint q).re + 1 ∈ K) :
    (S.card : ℝ) * (11616 / 4225 : ℝ) ≤
      criticalFeaturePrimeGammaOffLineLatticeBudget K := by
  have hframe :=
    finite_strictRight_card_mul_sharpThreeCenterQuantum_le_offLineLatticeEnergy
      K S hright hcenters
  have hsource :
      (∑ k ∈ K, offLineCriticalFeatureEnergyTrace (k : ℝ)) ≤
        2 * criticalFeaturePrimeGammaOffLineLatticeBudget K := by
    rw [criticalFeaturePrimeGammaOffLineLatticeBudget, Finset.mul_sum]
    gcongr with k hk
    exact offLineCriticalFeatureEnergyTrace_le_two_primeGammaOffLineExcess (k : ℝ)
  nlinarith

/-- **Exact three-center 75% receiver.**  The sharp local optimization raises the sufficient
corrected-source ceiling from `21/100 * N` to `1452/4225 * N`. -/
theorem three_quarters_line_of_exactThreeCenter_primeGammaOffLineLatticeBudget
    {N N₀ : ℝ} (K : Finset ℤ) (S : Finset XiZeroCopy)
    (hright : ∀ q ∈ S, 0 < (I * xiSpectralPoint q).re)
    (hcenters : ∀ q ∈ S,
      round (xiSpectralPoint q).re - 1 ∈ K ∧
      round (xiSpectralPoint q).re ∈ K ∧
      round (xiSpectralPoint q).re + 1 ∈ K)
    (hsplit : N = N₀ + 2 * S.card)
    (hbudget : criticalFeaturePrimeGammaOffLineLatticeBudget K ≤
      (1452 / 4225 : ℝ) * N) :
    3 * N / 4 ≤ N₀ := by
  have hcharge :=
    finite_strictRight_card_mul_sharpThreeCenterSourceCharge_le_offLineLatticeBudget
      K S hright hcenters
  have hcount : (S.card : ℝ) ≤ N / 8 := by
    nlinarith
  nlinarith

end

end RHTower

namespace RHTower

noncomputable section

/-- Half-cell points on the critical axis attain the exact three-center lower bound. -/
theorem sharp_threeCenterCriticalFeatureEnergy_eq_at_halfCell (t : ℝ) :
    threeCenterCriticalFeatureEnergy t (((t + 1 / 2 : ℝ) : ℂ)) =
      (23232 / 4225 : ℝ) := by
  rw [threeCenterCriticalFeatureEnergy,
    normSq_criticalFeatureCauchyKernelTest_eq_four_div (t - 1) (by simp),
    normSq_criticalFeatureCauchyKernelTest_eq_four_div t (by simp),
    normSq_criticalFeatureCauchyKernelTest_eq_four_div (t + 1) (by simp)]
  norm_num [criticalFeatureDenominatorNormSq, Complex.normSq_apply]

end

end RHTower
