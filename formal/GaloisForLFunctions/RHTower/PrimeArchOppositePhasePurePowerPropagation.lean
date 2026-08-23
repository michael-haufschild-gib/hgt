import GaloisForLFunctions.RHTower.PrimeArchScaledHausdorffDivisorValueRelation

/-!
# Opposite-phase propagation of positive pure powers

For the established prime-archimedean endpoint sectors, opposite imaginary
orientations prevent angular errors from adding.  Consequently any positive
pure power `z ^ p`, `p ≤ 38`, remains nonnegative after multiplication by
every endpoint-complement power `w ^ r`, `r ≤ 57`.  This converts a
two-index Hausdorff sign problem into one pure-power sign problem.
-/

open Complex Polynomial Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

theorem re_pow_mul_pow_nonneg_of_opposite_phase_of_pow_pos_bounded
    (z w : ℂ) (p r : ℕ)
    (hzre : 0 < z.re) (hwre : 0 < w.re)
    (hwim : w.im = -z.im)
    (hzsector : (121 / 10 : ℝ) * |z.im| ≤ z.re)
    (hwsector : (363 / 10 : ℝ) * |w.im| ≤ w.re)
    (hzpow : 0 < (z ^ p).re) (hp : p ≤ 38) (hr : r ≤ 57) :
    0 ≤ (z ^ p * w ^ r).re := by
  have hzarg : |z.arg| ≤ (10 / 121 : ℝ) :=
    abs_arg_le_of_re_pos_for_scaledHausdorff hzre (by nlinarith)
  have hwarg : |w.arg| ≤ (10 / 363 : ℝ) :=
    abs_arg_le_of_re_pos_for_scaledHausdorff hwre (by nlinarith)
  let x : ℝ := (p : ℝ) * z.arg
  let y : ℝ := (r : ℝ) * w.arg
  have hp0 : 0 ≤ (p : ℝ) := Nat.cast_nonneg p
  have hpR : (p : ℝ) ≤ 38 := by exact_mod_cast hp
  have hxcoarse : |x| ≤ (380 / 121 : ℝ) := by
    calc
      |x| = (p : ℝ) * |z.arg| := by
        simp only [x, abs_mul, abs_of_nonneg hp0]
      _ ≤ (p : ℝ) * (10 / 121 : ℝ) :=
        mul_le_mul_of_nonneg_left hzarg hp0
      _ ≤ 380 / 121 := by nlinarith
  have hxpi : |x| < Real.pi :=
    hxcoarse.trans_lt (by nlinarith [Real.pi_gt_d20])
  have hnorm : 0 < ‖z‖ ^ p := by
    apply pow_pos
    exact norm_pos_iff.mpr (fun hz => by simpa [hz] using hzre.ne')
  have hpolar : (z ^ p).re = ‖z‖ ^ p * Real.cos x := by
    simpa only [x, pow_one, pow_zero, mul_one, Nat.cast_one, Nat.cast_zero,
      zero_mul, add_zero] using pow_mul_pow_re_eq_norm_cos z 1 p 0
  have hcosx : 0 < Real.cos x := by
    rw [hpolar] at hzpow
    rcases (mul_pos_iff.mp hzpow) with h | h
    · exact h.2
    · exact False.elim (not_lt_of_ge hnorm.le h.1)
  have hx : |x| < Real.pi / 2 := by
    rw [abs_lt]
    constructor
    · by_contra h
      have hnonpos := Real.cos_nonpos_of_pi_div_two_le_of_le
        (show Real.pi / 2 ≤ -x by linarith)
        (show -x ≤ Real.pi + Real.pi / 2 by
          rw [abs_lt] at hxpi
          linarith [Real.pi_pos])
      rw [Real.cos_neg] at hnonpos
      linarith
    · by_contra h
      have hnonpos := Real.cos_nonpos_of_pi_div_two_le_of_le
        (show Real.pi / 2 ≤ x by linarith)
        (show x ≤ Real.pi + Real.pi / 2 by
          rw [abs_lt] at hxpi
          linarith [Real.pi_pos])
      linarith
  have hr0 : 0 ≤ (r : ℝ) := Nat.cast_nonneg r
  have hrR : (r : ℝ) ≤ 57 := by exact_mod_cast hr
  have hy : |y| < Real.pi / 2 := by
    have hyBound : |y| ≤ (190 / 121 : ℝ) := by
      calc
        |y| = (r : ℝ) * |w.arg| := by
          simp only [y, abs_mul, abs_of_nonneg hr0]
        _ ≤ (r : ℝ) * (10 / 363 : ℝ) :=
          mul_le_mul_of_nonneg_left hwarg hr0
        _ ≤ 190 / 121 := by nlinarith
    exact hyBound.trans_lt (by nlinarith [Real.pi_gt_d20])
  have hangle : x + y ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    rw [abs_lt] at hx hy
    by_cases hzim : 0 ≤ z.im
    · have hzarg0 : 0 ≤ z.arg := Complex.arg_nonneg_iff.mpr hzim
      have hwim0 : w.im ≤ 0 := by rw [hwim]; linarith
      have hwarg0 : w.arg ≤ 0 := by
        rw [arg_eq_arctan_of_re_pos hwre]
        exact Real.arctan_le_zero.mpr
          (div_nonpos_of_nonpos_of_nonneg hwim0 hwre.le)
      have hx0 : 0 ≤ x := mul_nonneg hp0 hzarg0
      have hy0 : y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hr0 hwarg0
      constructor
      · nlinarith [hy.1, hx0]
      · nlinarith [hx.2, hy0]
    · have hzim0 : z.im ≤ 0 := le_of_not_ge hzim
      have hzarg0 : z.arg ≤ 0 := by
        rw [arg_eq_arctan_of_re_pos hzre]
        exact Real.arctan_le_zero.mpr
          (div_nonpos_of_nonpos_of_nonneg hzim0 hzre.le)
      have hwim0 : 0 ≤ w.im := by rw [hwim]; linarith
      have hwarg0 : 0 ≤ w.arg := Complex.arg_nonneg_iff.mpr hwim0
      have hx0 : x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hp0 hzarg0
      have hy0 : 0 ≤ y := mul_nonneg hr0 hwarg0
      constructor
      · nlinarith [hx.1, hy0]
      · nlinarith [hy.2, hx0]
  rw [pow_mul_pow_re_eq_norm_cos]
  exact mul_nonneg
    (mul_nonneg (pow_nonneg (norm_nonneg z) p) (pow_nonneg (norm_nonneg w) r))
    (Real.cos_pos_of_mem_Ioo (by simpa only [x, y] using hangle)).le

end

end RHTower
