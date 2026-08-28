import GaloisForLFunctions.RHTower.HedenmalmOrientedAdjacentTransverseDeterminantQuantum
import GaloisForLFunctions.RHTower.HedenmalmCriticalFeatureLatticePrimeGammaBudget

/-!
# Three-center lattice quantum for the corrected critical-feature budget

The original lattice receiver charges each off-line Xi copy only through its nearest integer
feature.  A height window is naturally padded by one lattice site at each end, so both adjacent
features are already available.  The nearest feature contributes `64/25`; one adjacent feature is
within distance one and contributes at least `4/5`.  Keeping both predeclared adjacent features
avoids a divisor-dependent orientation choice.

An elementary argument gives Hermitian quantum `84/25`.  An exact positive Bernstein certificate
sharpens it to five.  After the global holomorphic-sector factor two, corrected source charge is
`5/2`; consequently a `5/16 * N` source ceiling implies the 75% receiver.  The older single-center
proof required the much smaller `4/25 * N` ceiling.
-/

open Complex

namespace RHTower

noncomputable section

private def bernsteinSix (i : ℕ) (x : ℝ) : ℝ :=
  match i with
  | 0 => (1 - x) ^ 6
  | 1 => 6 * x * (1 - x) ^ 5
  | 2 => 15 * x ^ 2 * (1 - x) ^ 4
  | 3 => 20 * x ^ 3 * (1 - x) ^ 3
  | 4 => 15 * x ^ 4 * (1 - x) ^ 2
  | 5 => 6 * x ^ 5 * (1 - x)
  | 6 => x ^ 6
  | _ => 0

private noncomputable def threeCenterBernsteinCoeff (i j : ℕ) : ℝ :=
  match i, j with
  | 0, 0 => 16
  | 0, 1 => 20
  | 0, 2 => 119 / 5
  | 0, 3 => 549 / 20
  | 0, 4 => 39669 / 1280
  | 0, 5 => 105857 / 3072
  | 0, 6 => 155155 / 4096
  | 1, 0 => 44 / 3
  | 1, 1 => 331 / 18
  | 1, 2 => 982 / 45
  | 1, 3 => 38435 / 1536
  | 1, 4 => 1292011 / 46080
  | 1, 5 => 2278945 / 73728
  | 1, 6 => 68961 / 2048
  | 2, 0 => 41 / 3
  | 2, 1 => 517 / 30
  | 2, 2 => 196127 / 9600
  | 2, 3 => 1790873 / 76800
  | 2, 4 => 7973039 / 307200
  | 2, 5 => 290643 / 10240
  | 2, 6 => 470737 / 15360
  | 3, 0 => 13
  | 3, 1 => 42341 / 2560
  | 3, 2 => 502661 / 25600
  | 3, 3 => 9156903 / 409600
  | 3, 4 => 1267797 / 51200
  | 3, 5 => 826577 / 30720
  | 3, 6 => 14765 / 512
  | 4, 0 => 48607 / 3840
  | 4, 1 => 751309 / 46080
  | 4, 2 => 17916797 / 921600
  | 4, 3 => 3401051 / 153600
  | 4, 4 => 2819539 / 115200
  | 4, 5 => 61055 / 2304
  | 4, 6 => 36183 / 1280
  | 5, 0 => 12925 / 1024
  | 5, 1 => 135289 / 8192
  | 5, 2 => 121889 / 6144
  | 5, 3 => 232187 / 10240
  | 5, 4 => 19273 / 768
  | 5, 5 => 13909 / 512
  | 5, 6 => 3705 / 128
  | 6, 0 => 52675 / 4096
  | 6, 1 => 35109 / 2048
  | 6, 2 => 106523 / 5120
  | 6, 3 => 61269 / 2560
  | 6, 4 => 6811 / 256
  | 6, 5 => 11095 / 384
  | 6, 6 => 1975 / 64
  | _, _ => 0

private noncomputable def threeCenterBernsteinCertificate (x y : ℝ) : ℝ :=
  ∑ i ∈ Finset.range 7, ∑ j ∈ Finset.range 7,
    threeCenterBernsteinCoeff i j * bernsteinSix i x * bernsteinSix j y

private theorem bernsteinSix_nonneg {i : ℕ} (hi : i < 7)
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ bernsteinSix i x := by
  interval_cases i <;> simp [bernsteinSix] <;> positivity

private theorem threeCenterBernsteinCoeff_nonneg
    {i j : ℕ} (hi : i < 7) (hj : j < 7) :
    0 ≤ threeCenterBernsteinCoeff i j := by
  interval_cases i <;> interval_cases j <;>
    norm_num [threeCenterBernsteinCoeff]

private theorem threeCenterBernsteinCertificate_nonneg
    {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    0 ≤ threeCenterBernsteinCertificate x y := by
  rw [threeCenterBernsteinCertificate]
  apply Finset.sum_nonneg
  intro i hi
  apply Finset.sum_nonneg
  intro j hj
  have hi7 : i < 7 := Finset.mem_range.mp hi
  have hj7 : j < 7 := Finset.mem_range.mp hj
  exact mul_nonneg
    (mul_nonneg (threeCenterBernsteinCoeff_nonneg hi7 hj7)
      (bernsteinSix_nonneg hi7 hx0 hx1))
    (bernsteinSix_nonneg hj7 hy0 hy1)

private def threeCenterDenominator (u y : ℝ) : ℝ :=
  (1 + u ^ 2 - y ^ 2) ^ 2 + (2 * u * y) ^ 2

set_option maxHeartbeats 2000000 in
private theorem threeCenterDenominator_bernstein_identity (u y : ℝ) :
    4 * (threeCenterDenominator u y * threeCenterDenominator (u - 1) y +
      threeCenterDenominator (u + 1) y * threeCenterDenominator (u - 1) y +
      threeCenterDenominator (u + 1) y * threeCenterDenominator u y) -
        5 * threeCenterDenominator (u + 1) y * threeCenterDenominator u y *
          threeCenterDenominator (u - 1) y =
      threeCenterBernsteinCertificate (4 * u ^ 2) (4 * y ^ 2) := by
  norm_num [threeCenterDenominator, threeCenterBernsteinCertificate,
    threeCenterBernsteinCoeff, bernsteinSix, Finset.sum_range_succ]
  ring

private theorem threeCenterDenominator_certificate_nonneg
    {u y : ℝ} (hu : |u| ≤ 1 / 2) (hy : |y| ≤ 1 / 2) :
    0 ≤ 4 * (threeCenterDenominator u y * threeCenterDenominator (u - 1) y +
      threeCenterDenominator (u + 1) y * threeCenterDenominator (u - 1) y +
      threeCenterDenominator (u + 1) y * threeCenterDenominator u y) -
        5 * threeCenterDenominator (u + 1) y * threeCenterDenominator u y *
          threeCenterDenominator (u - 1) y := by
  have hu2 : u ^ 2 ≤ 1 / 4 := by
    have h := (sq_le_sq₀ (abs_nonneg u)
      (by norm_num : (0 : ℝ) ≤ 1 / 2)).2 hu
    rw [sq_abs] at h
    norm_num at h ⊢
    exact h
  have hy2 : y ^ 2 ≤ 1 / 4 := by
    have h := (sq_le_sq₀ (abs_nonneg y)
      (by norm_num : (0 : ℝ) ≤ 1 / 2)).2 hy
    rw [sq_abs] at h
    norm_num at h ⊢
    exact h
  rw [threeCenterDenominator_bernstein_identity]
  exact threeCenterBernsteinCertificate_nonneg
    (by positivity) (by nlinarith) (by positivity) (by nlinarith)

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

theorem normSq_criticalFeatureCauchyKernelTest_eq_four_div_denominator
    (t : ℝ) {z : ℂ} (hz : |z.im| < 1 / 2) :
    Complex.normSq (criticalFeatureCauchyKernelTest t z) =
      4 / criticalFeatureDenominatorNormSq t z := by
  rw [criticalFeatureCauchyKernelTest_eq t hz, Complex.normSq_div]
  norm_num
  rfl

/-- **Sharp rational three-center quantum.**  A positive Bernstein certificate on
`4 (Re z-t)^2, 4 (Im z)^2 ∈ [0,1]` proves a uniform floor of five. -/
theorem five_le_threeCenterCriticalFeatureEnergy
    {t : ℝ} {z : ℂ} (hz : |z.im| < 1 / 2)
    (ht : |z.re - t| ≤ 1 / 2) :
    (5 : ℝ) ≤ threeCenterCriticalFeatureEnergy t z := by
  let u : ℝ := z.re - t
  let y : ℝ := z.im
  let Dm : ℝ := threeCenterDenominator (u + 1) y
  let D0 : ℝ := threeCenterDenominator u y
  let Dp : ℝ := threeCenterDenominator (u - 1) y
  have hDm : criticalFeatureDenominatorNormSq (t - 1) z = Dm := by
    rw [criticalFeatureDenominatorNormSq_eq]
    simp only [Dm, threeCenterDenominator, u, y]
    congr 1 <;> ring
  have hD0 : criticalFeatureDenominatorNormSq t z = D0 := by
    rw [criticalFeatureDenominatorNormSq_eq]
    rfl
  have hDp : criticalFeatureDenominatorNormSq (t + 1) z = Dp := by
    rw [criticalFeatureDenominatorNormSq_eq]
    simp only [Dp, threeCenterDenominator, u, y]
    congr 1 <;> ring
  have hDmpos : 0 < Dm := by
    rw [← hDm]
    exact criticalFeatureDenominatorNormSq_pos (t - 1) hz
  have hD0pos : 0 < D0 := by
    rw [← hD0]
    exact criticalFeatureDenominatorNormSq_pos t hz
  have hDppos : 0 < Dp := by
    rw [← hDp]
    exact criticalFeatureDenominatorNormSq_pos (t + 1) hz
  have hQ := threeCenterDenominator_certificate_nonneg
    (u := u) (y := y) (by simpa [u] using ht) hz.le
  have hsum : 4 / Dm + 4 / D0 + 4 / Dp =
      4 * (D0 * Dp + Dm * Dp + Dm * D0) / (Dm * D0 * Dp) := by
    field_simp [ne_of_gt hDmpos, ne_of_gt hD0pos, ne_of_gt hDppos]
  rw [threeCenterCriticalFeatureEnergy,
    normSq_criticalFeatureCauchyKernelTest_eq_four_div_denominator (t - 1) hz,
    normSq_criticalFeatureCauchyKernelTest_eq_four_div_denominator t hz,
    normSq_criticalFeatureCauchyKernelTest_eq_four_div_denominator (t + 1) hz,
    hDm, hD0, hDp, hsum]
  apply (le_div_iff₀ (mul_pos (mul_pos hDmpos hD0pos) hDppos)).2
  dsimp only [Dm, D0, Dp] at hQ ⊢
  nlinarith

/-- Every finite strict-right packet deposits five units when its nearest centers
and their two neighbours belong to the lattice window. -/
theorem finite_strictRight_card_mul_five_le_offLineLatticeEnergy
    (K : Finset ℤ) (S : Finset XiZeroCopy)
    (hright : ∀ q ∈ S, 0 < (I * xiSpectralPoint q).re)
    (hcenters : ∀ q ∈ S,
      round (xiSpectralPoint q).re - 1 ∈ K ∧
      round (xiSpectralPoint q).re ∈ K ∧
      round (xiSpectralPoint q).re + 1 ∈ K) :
    (S.card : ℝ) * 5 ≤
      ∑ k ∈ K, offLineCriticalFeatureEnergyTrace (k : ℝ) := by
  calc
    (S.card : ℝ) * 5 = ∑ _q ∈ S, (5 : ℝ) := by simp
    _ ≤ ∑ q ∈ S, ∑ k ∈ K, offLineCriticalFeatureEnergy (k : ℝ) q := by
      gcongr with q hq
      let kq : ℤ := round (xiSpectralPoint q).re
      have hmem := hcenters q hq
      have hqoff : (q.1 : ℂ).re ≠ 1 / 2 := by
        intro hline
        have hp := hright q hq
        rw [I_mul_xiSpectralPoint, Complex.sub_re, hline] at hp
        norm_num at hp
      have hthree := five_le_threeCenterCriticalFeatureEnergy
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
        (5 : ℝ) ≤ ∑ j ∈ Tq,
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

/-- The earlier elementary `84/25` quantum follows from the sharp five-unit theorem. -/
theorem finite_strictRight_card_mul_eightyFour_twentyFive_le_offLineLatticeEnergy
    (K : Finset ℤ) (S : Finset XiZeroCopy)
    (hright : ∀ q ∈ S, 0 < (I * xiSpectralPoint q).re)
    (hcenters : ∀ q ∈ S,
      round (xiSpectralPoint q).re - 1 ∈ K ∧
      round (xiSpectralPoint q).re ∈ K ∧
      round (xiSpectralPoint q).re + 1 ∈ K) :
    (S.card : ℝ) * (84 / 25 : ℝ) ≤
      ∑ k ∈ K, offLineCriticalFeatureEnergyTrace (k : ℝ) := by
  have hsharp := finite_strictRight_card_mul_five_le_offLineLatticeEnergy
    K S hright hcenters
  have hcard : (0 : ℝ) ≤ S.card := by positivity
  nlinarith

/-- Sharp corrected source charge after the holomorphic-sector factor two. -/
theorem finite_strictRight_card_mul_five_halves_le_offLineLatticeBudget
    (K : Finset ℤ) (S : Finset XiZeroCopy)
    (hright : ∀ q ∈ S, 0 < (I * xiSpectralPoint q).re)
    (hcenters : ∀ q ∈ S,
      round (xiSpectralPoint q).re - 1 ∈ K ∧
      round (xiSpectralPoint q).re ∈ K ∧
      round (xiSpectralPoint q).re + 1 ∈ K) :
    (S.card : ℝ) * (5 / 2 : ℝ) ≤
      criticalFeaturePrimeGammaOffLineLatticeBudget K := by
  have hframe := finite_strictRight_card_mul_five_le_offLineLatticeEnergy
    K S hright hcenters
  have hsource :
      (∑ k ∈ K, offLineCriticalFeatureEnergyTrace (k : ℝ)) ≤
        2 * criticalFeaturePrimeGammaOffLineLatticeBudget K := by
    rw [criticalFeaturePrimeGammaOffLineLatticeBudget, Finset.mul_sum]
    gcongr with k hk
    exact offLineCriticalFeatureEnergyTrace_le_two_primeGammaOffLineExcess (k : ℝ)
  nlinarith

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

/-- **Sharp three-center 75% receiver.**  A `5/16 * N` corrected-source ceiling suffices. -/
theorem three_quarters_line_of_five_sixteenths_primeGammaOffLineLatticeBudget
    {N N₀ : ℝ} (K : Finset ℤ) (S : Finset XiZeroCopy)
    (hright : ∀ q ∈ S, 0 < (I * xiSpectralPoint q).re)
    (hcenters : ∀ q ∈ S,
      round (xiSpectralPoint q).re - 1 ∈ K ∧
      round (xiSpectralPoint q).re ∈ K ∧
      round (xiSpectralPoint q).re + 1 ∈ K)
    (hsplit : N = N₀ + 2 * S.card)
    (hbudget : criticalFeaturePrimeGammaOffLineLatticeBudget K ≤
      (5 / 16 : ℝ) * N) :
    3 * N / 4 ≤ N₀ := by
  have hcharge :=
    finite_strictRight_card_mul_five_halves_le_offLineLatticeBudget
      K S hright hcenters
  have hcount : (S.card : ℝ) ≤ N / 8 := by
    nlinarith
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
