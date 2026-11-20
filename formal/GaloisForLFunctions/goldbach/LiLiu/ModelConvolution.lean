import GaloisForLFunctions.goldbach.LiLiu.TestWeight
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Cancellation and integer samples of the signed continuous model

Write J for the additive self-convolution of the test weight. By reflection
the difference convolution at y is J(1−y), and J(2−y) = J(y). Thus the
signed profile has zero integral on the positive half-line, while its only
nonzero positive integer sample is minus the squared mass, at one.
-/

namespace GaloisForLFunctions.Goldbach.LiLiu
open MeasureTheory Set
open scoped ContDiff
noncomputable section

def sumProfile (φ : TestWeight) (y : ℝ) : ℝ := ∫ u, φ u * φ (y - u)

def signedProfile (φ : TestWeight) (y : ℝ) : ℝ := 2 * sumProfile φ (1 - y) - sumProfile φ y

theorem differenceProfile_eq (φ : TestWeight) (y : ℝ) :
    (∫ u, φ u * φ (u + y)) = sumProfile φ (1 - y) := by
  apply integral_congr_ae
  filter_upwards with u
  rw [show 1 - y - u = 1 - (u + y) by ring, φ.symmetric]

theorem sumProfile_smooth (φ : TestWeight) : ContDiff ℝ ∞ (sumProfile φ) := by
  have hc : HasCompactSupport φ.toFun := HasCompactSupport.intro isCompact_Icc
    fun _ hx => Function.notMem_support.mp fun hu => hx (φ.supported hu)
  exact hc.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
    φ.smooth.continuous.locallyIntegrable φ.smooth

theorem sumProfile_reflect (φ : TestWeight) (y : ℝ) : sumProfile φ (2 - y) = sumProfile φ y := by
  unfold sumProfile
  rw [← integral_sub_left_eq_self (fun u : ℝ => φ u * φ (2 - y - u)) volume 1]
  apply integral_congr_ae
  filter_upwards with u
  rw [φ.symmetric, show 2 - y - (1 - u) = 1 - (y - u) by ring, φ.symmetric]

theorem sumProfile_zero (φ : TestWeight) {y : ℝ} (hy : y ∉ Icc (2 / 3 : ℝ) (4 / 3)) :
    sumProfile φ y = 0 := by
  unfold sumProfile
  apply integral_eq_zero_of_ae
  filter_upwards with u
  by_contra! h
  obtain ⟨hu, hv⟩ := mul_ne_zero_iff.mp h
  have a := φ.supported hu
  have b := φ.supported hv
  exact hy ⟨by linarith only [a.1, b.1], by linarith only [a.2, b.2]⟩

theorem sumProfile_one (φ : TestWeight) : sumProfile φ 1 = φ.mass := by
  simp only [sumProfile, TestWeight.mass, φ.symmetric, pow_two]

/-- The pole cancellation uses an integral, whereas this identity retains a discrete sample. -/
theorem signedProfile_nat (φ : TestWeight) {k : ℕ} (hk : 0 < k) :
    signedProfile φ k = if k = 1 then -φ.mass else 0 := by
  have h1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hzero : sumProfile φ (1 - k) = 0 := sumProfile_zero φ fun h => by linarith only [h.1, h1]
  rw [signedProfile, hzero, mul_zero, zero_sub]
  by_cases he : k = 1
  · simp [he, sumProfile_one]
  · have h2 : (2 : ℝ) ≤ k := by exact_mod_cast (by omega : 2 ≤ k)
    simp only [if_neg he, neg_eq_zero]
    exact sumProfile_zero φ fun h => by linarith only [h.2, h2]

/-- The Mellin transform at one vanishes. The two reflected halves of J have equal mass. -/
theorem integral_signedProfile_Ioi (φ : TestWeight) : (∫ y in Ioi 0, signedProfile φ y) = 0 := by
  let J := sumProfile φ
  have hJ : Continuous J := (sumProfile_smooth φ).continuous
  have hsym : (∫ y in (1 : ℝ)..2, J y) = ∫ y in (0 : ℝ)..1, J y := by
    calc
      _ = ∫ y in (1 : ℝ)..2, J (2 - y) :=
        intervalIntegral.integral_congr fun y _ => (sumProfile_reflect φ y).symm
      _ = _ := by rw [intervalIntegral.integral_comp_sub_left]; norm_num
  have hsupp : (∫ y in Ioi 0, signedProfile φ y) = ∫ y in (0 : ℝ)..2, signedProfile φ y := by
    rw [intervalIntegral.integral_of_le (by norm_num)]
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi fun y h => h.1
    intro y hy
    have h2 : 2 < y := lt_of_not_ge fun h => hy.2 ⟨hy.1, h⟩
    rw [signedProfile, sumProfile_zero φ (fun h => by linarith only [h.1, h2]),
      sumProfile_zero φ (fun h => by linarith only [h.2, h2]), mul_zero, sub_zero]
  have hleft : (∫ y in (-1 : ℝ)..0, J y) = 0 := by
    apply intervalIntegral.integral_zero_ae
    filter_upwards with y hy
    rw [uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 0)] at hy
    exact sumProfile_zero φ fun h => by linarith only [h.1, hy.2]
  have hneg := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (a := (-1 : ℝ)) (b := 0) (c := 1) (hJ.intervalIntegrable ..) (hJ.intervalIntegrable ..)
  have hpos := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (a := (0 : ℝ)) (b := 1) (c := 2) (hJ.intervalIntegrable ..) (hJ.intervalIntegrable ..)
  rw [hsupp]
  change (∫ y in (0 : ℝ)..2, 2 * J (1 - y) - J y) = 0
  have hc : Continuous (fun y : ℝ => 2 * J (1 - y)) :=
    continuous_const.mul (hJ.comp (continuous_const.sub continuous_id))
  rw [intervalIntegral.integral_sub (hc.intervalIntegrable ..) (hJ.intervalIntegrable ..),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_sub_left]
  norm_num only [show (1 : ℝ) - 2 = -1 by norm_num, sub_zero]
  linarith only [hleft, hneg, hpos, hsym]

#print axioms integral_signedProfile_Ioi
#print axioms signedProfile_nat
end
end GaloisForLFunctions.Goldbach.LiLiu
