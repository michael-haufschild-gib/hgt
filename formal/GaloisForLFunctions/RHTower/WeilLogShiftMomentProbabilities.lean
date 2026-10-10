import GaloisForLFunctions.RHTower.WeilLogShiftGramLeakageAlgebra
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Finset.Max

/-! A unit zero-sum dual splits into two disjoint probability profiles. -/

open scoped BigOperators
noncomputable section
namespace RHTower

def finiteWeilAbsMass {ι : Type} [Fintype ι] (c : ι → ℝ) : ℝ := ∑ i, |c i|

def finiteWeilPositiveProfile {ι : Type} [Fintype ι] (c : ι → ℝ) (i : ι) : ℝ :=
  (|c i| + c i) / finiteWeilAbsMass c

def finiteWeilNegativeProfile {ι : Type} [Fintype ι] (c : ι → ℝ) (i : ι) : ℝ :=
  (|c i| - c i) / finiteWeilAbsMass c

theorem finiteWeil_zero_sum_unit_mass {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (c : ι → ℝ) (hc : ‖c‖ = 1) (hzero : ∑ i, c i = 0) : 2 ≤ finiteWeilAbsMass c := by
  obtain ⟨i, _, hmax⟩ := Finset.exists_max_image Finset.univ (fun i => |c i|)
    Finset.univ_nonempty
  have htop : ‖c‖ ≤ |c i| := (pi_norm_le_iff_of_nonneg (abs_nonneg _)).mpr fun j => by
    simpa only [Real.norm_eq_abs] using hmax j (Finset.mem_univ j)
  have hi : |c i| = 1 := le_antisymm
    (by simpa only [Real.norm_eq_abs, hc] using norm_le_pi_norm c i)
    (by simpa only [hc] using htop)
  have hoff : 1 ≤ ∑ j ∈ Finset.univ.erase i, |c j| := by
    simpa only [one_mul, mul_one, hzero, abs_one, abs_zero, zero_add] using
      finiteWeil_coordinate_le_pairing_add_off i c (fun _ => 1) hi
  have hs := Finset.sum_erase_add Finset.univ (fun j => |c j|) (Finset.mem_univ i)
  rw [hi] at hs
  change 2 ≤ ∑ j, |c j|
  linarith only [hoff, hs]

theorem finiteWeil_profile_scale_bounds {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (c : ι → ℝ) (hc : ‖c‖ = 1) (hzero : ∑ i, c i = 0) :
    0 < 2 / finiteWeilAbsMass c ∧ 2 / finiteWeilAbsMass c ≤ 1 := by
  have hmass := finiteWeil_zero_sum_unit_mass c hc hzero
  have hpos : 0 < finiteWeilAbsMass c := by linarith only [hmass]
  exact ⟨div_pos (by norm_num) hpos, (div_le_one hpos).mpr hmass⟩

theorem finiteWeil_profile_difference {ι : Type} [Fintype ι] (c : ι → ℝ) (i : ι) :
    finiteWeilPositiveProfile c i - finiteWeilNegativeProfile c i =
      (2 / finiteWeilAbsMass c) * c i := by
  dsimp [finiteWeilPositiveProfile, finiteWeilNegativeProfile]
  ring

theorem finiteWeil_profile_pairing {ι : Type} [Fintype ι] (c y : ι → ℝ) :
    (∑ i, finiteWeilPositiveProfile c i * y i) -
      (∑ i, finiteWeilNegativeProfile c i * y i) =
      (2 / finiteWeilAbsMass c) * ∑ i, c i * y i := by
  calc
    _ = ∑ i, (finiteWeilPositiveProfile c i - finiteWeilNegativeProfile c i) * y i := by
      simp only [sub_mul, Finset.sum_sub_distrib]
    _ = _ := by
      simp only [finiteWeil_profile_difference, mul_assoc, ← Finset.mul_sum]

/-- The sign indicator reads the positive profile as one and the negative as zero after summing. -/
theorem finiteWeil_profile_positive_indicator {ι : Type} [Fintype ι] (c : ι → ℝ) (i : ι) :
    finiteWeilPositiveProfile c i * (if 0 < c i then 1 else 0) = finiteWeilPositiveProfile c i ∧
    finiteWeilNegativeProfile c i * (if 0 < c i then 1 else 0) = 0 := by
  by_cases hi : 0 < c i
  · simp only [if_pos hi, mul_one, finiteWeilNegativeProfile, abs_of_pos hi, sub_self,
      zero_div, and_self]
  · have hci : c i ≤ 0 := le_of_not_gt hi
    simp only [if_neg hi, mul_zero, finiteWeilPositiveProfile, abs_of_nonpos hci,
      neg_add_cancel, zero_div, and_self]

theorem finiteWeil_profiles_pairing_le {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (c : ι → ℝ) (hc : ‖c‖ = 1) (hzero : ∑ i, c i = 0) (y : ι → ℝ) :
    |(∑ i, finiteWeilPositiveProfile c i * y i) -
      (∑ i, finiteWeilNegativeProfile c i * y i)| ≤ |∑ i, c i * y i| := by
  have hs := finiteWeil_profile_scale_bounds c hc hzero
  rw [finiteWeil_profile_pairing, abs_mul, abs_of_pos hs.1]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hs.2 (abs_nonneg (∑ i, c i * y i))

/-- Positive and negative parts have unit mass, disjoint full combined support,
and maximal absolute difference. -/
theorem finiteWeil_profiles_spec {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (c : ι → ℝ) (hc : ‖c‖ = 1) (hzero : ∑ i, c i = 0) (hne : ∀ i, c i ≠ 0) :
    (∀ i, 0 ≤ finiteWeilPositiveProfile c i ∧ 0 ≤ finiteWeilNegativeProfile c i ∧
      finiteWeilPositiveProfile c i * finiteWeilNegativeProfile c i = 0 ∧
      0 < finiteWeilPositiveProfile c i + finiteWeilNegativeProfile c i) ∧
    (∑ i, finiteWeilPositiveProfile c i) = 1 ∧
    (∑ i, finiteWeilNegativeProfile c i) = 1 ∧
    (∑ i, |finiteWeilPositiveProfile c i - finiteWeilNegativeProfile c i|) = 2 := by
  have hmass := finiteWeil_zero_sum_unit_mass c hc hzero
  have hpos : 0 < finiteWeilAbsMass c := by linarith only [hmass]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    have hp : 0 ≤ |c i| + c i := by have := neg_abs_le (c i); linarith only [this]
    have hq : 0 ≤ |c i| - c i := sub_nonneg.mpr (le_abs_self (c i))
    refine ⟨div_nonneg hp hpos.le, div_nonneg hq hpos.le, ?_, ?_⟩
    · by_cases hi : 0 ≤ c i
      · simp only [finiteWeilPositiveProfile, finiteWeilNegativeProfile, abs_of_nonneg hi]
        ring
      · simp only [finiteWeilPositiveProfile, finiteWeilNegativeProfile,
          abs_of_neg (lt_of_not_ge hi)]
        ring
    · have heq : finiteWeilPositiveProfile c i + finiteWeilNegativeProfile c i =
          2 * |c i| / finiteWeilAbsMass c := by
        dsimp [finiteWeilPositiveProfile, finiteWeilNegativeProfile]
        ring
      rw [heq]
      exact div_pos (mul_pos (by norm_num) (abs_pos.mpr (hne i))) hpos
  · change (∑ i, (|c i| + c i) / finiteWeilAbsMass c) = 1
    rw [← Finset.sum_div, Finset.sum_add_distrib, hzero, add_zero]
    exact div_self hpos.ne'
  · change (∑ i, (|c i| - c i) / finiteWeilAbsMass c) = 1
    rw [← Finset.sum_div, Finset.sum_sub_distrib, hzero, sub_zero]
    exact div_self hpos.ne'
  · have ht : 0 < 2 / finiteWeilAbsMass c := div_pos (by norm_num) hpos
    simp only [finiteWeil_profile_difference, abs_mul, abs_of_pos ht, ← Finset.mul_sum]
    exact div_mul_cancel₀ 2 hpos.ne'

end RHTower
