import GaloisForLFunctions.RHTower.PrimeArchOrderTwentyHausdorffSourceBand
import GaloisForLFunctions.HTGeometry.HausdorffCDDPhaseKernel

/-!
# Mixed Hausdorff claw at centered order twenty one

Pure twenty-first reciprocal powers retain one unresolved residual annulus.  The
endpoint-complement factor has the opposite phase.  On that annulus its phase is
uniformly bounded away from zero, so powers `22 ≤ r ≤ 57` rotate every bad
twenty-first power back into the right half-plane.  Off the annulus the pure
power is already positive.

This proves an unconditional mixed Hausdorff claw at `k = 20` despite the still
open sign of the pure source moment `normalizedPrimeArchMoment 20`.
-/

open Complex Polynomial Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- A residual order-twenty-one atom has a quantitatively nonzero transverse coordinate. -/
theorem one_over_threeThousand_lt_abs_im_xiZeroCopyReciprocalSquare_of_orderTwentyOneResidual
    (q : XiZeroCopy) (hq : XiCenteredOrderTwentyOneResidualAnnulus q) :
    (1 / 3000 : ℝ) < |(xiZeroCopyReciprocalSquare q).im| := by
  let u : ℝ := ((q.1 : ℂ).re - 1 / 2) ^ 2
  let v : ℝ := (q.1 : ℂ).im ^ 2
  let w : ℝ := u + v
  have hu0 : 0 < u := by dsimp only [u]; linarith [hq.2.1]
  have huL : 2365 / 11552 < u := by simpa only [u] using hq.2.1
  have huU : u < 1 / 4 := by simpa only [u] using hq.2.2.1
  have hv0 : 0 < v := by dsimp only [v]; linarith [hq.2.2.2.1]
  have hvL : 2365 / 16 ≤ v := by simpa only [v] using hq.2.2.2.1
  have hvU : v < 361 / 2 := by simpa only [v] using hq.2.2.2.2
  have hw0 : 0 < w := by dsimp only [w]; positivity
  have hwU : w < 723 / 4 := by dsimp only [w]; linarith
  have hw4 : w ^ 4 < (723 / 4 : ℝ) ^ 4 :=
    pow_lt_pow_left₀ hwU hw0.le (by norm_num)
  have huv : (2365 / 11552 : ℝ) * (2365 / 16) < u * v := by
    calc
      (2365 / 11552 : ℝ) * (2365 / 16) < u * (2365 / 16) := by
        exact mul_lt_mul_of_pos_right huL (by norm_num)
      _ ≤ u * v := mul_le_mul_of_nonneg_left hvL hu0.le
  have hrat :
      (1 / 9000000 : ℝ) * (723 / 4 : ℝ) ^ 4 <
        4 * ((2365 / 11552 : ℝ) * (2365 / 16 : ℝ)) := by
    norm_num
  have hbudget : (1 / 9000000 : ℝ) * w ^ 4 < 4 * u * v := by
    calc
      (1 / 9000000 : ℝ) * w ^ 4 <
          (1 / 9000000 : ℝ) * (723 / 4 : ℝ) ^ 4 := by gcongr
      _ < 4 * ((2365 / 11552 : ℝ) * (2365 / 16 : ℝ)) := hrat
      _ < 4 * u * v := by nlinarith
  apply (sq_lt_sq₀ (by norm_num : (0 : ℝ) ≤ 1 / 3000)
    (abs_nonneg _)).mp
  rw [sq_abs, xiZeroCopyReciprocalSquare_im_formula]
  have hden : 0 < w ^ 4 := pow_pos hw0 4
  have hsquare :
      (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im /
          (((q.1 : ℂ).re - 1 / 2) ^ 2 + (q.1 : ℂ).im ^ 2) ^ 2) ^ 2 =
        4 * u * v / w ^ 4 := by
    dsimp only [u, v, w]
    field_simp [hw0.ne']
    ring
  rw [hsquare, lt_div_iff₀ hden]
  norm_num at hbudget ⊢
  exact hbudget

/-- A residual order-twenty-one atom retains a definite longitudinal coordinate. -/
theorem one_over_oneHundredEightyTwo_lt_re_xiZeroCopyReciprocalSquare_of_orderTwentyOneResidual
    (q : XiZeroCopy) (hq : XiCenteredOrderTwentyOneResidualAnnulus q) :
    (1 / 182 : ℝ) < (xiZeroCopyReciprocalSquare q).re := by
  let u : ℝ := ((q.1 : ℂ).re - 1 / 2) ^ 2
  let v : ℝ := (q.1 : ℂ).im ^ 2
  let F : ℝ → ℝ → ℝ := fun a b => 182 * (b - a) - (a + b) ^ 2
  let U : ℝ := 1 / 4
  let V : ℝ := 361 / 2
  have hu0 : 0 < u := by dsimp only [u]; linarith [hq.2.1]
  have huU : u < U := by simpa only [u, U] using hq.2.2.1
  have hvL : 2365 / 16 ≤ v := by simpa only [v] using hq.2.2.2.1
  have hvV : v < V := by simpa only [v, V] using hq.2.2.2.2
  have hstepv : F u V < F u v := by
    have hcoef : 0 < 2 * u + v + V - 182 := by
      dsimp only [V]
      nlinarith
    have hp := mul_pos (sub_pos.mpr hvV) hcoef
    have hid : F u v - F u V = (V - v) * (2 * u + v + V - 182) := by
      dsimp only [F]
      ring
    nlinarith
  have hstepu : F U V < F u V := by
    have hcoef : 0 < 182 + U + u + 2 * V := by
      dsimp only [U, V]
      nlinarith
    have hp := mul_pos (sub_pos.mpr huU) hcoef
    have hid : F u V - F U V = (U - u) * (182 + U + u + 2 * V) := by
      dsimp only [F]
      ring
    nlinarith
  have hend : 0 < F U V := by
    norm_num [F, U, V]
  have hF : 0 < F u v := hend.trans (hstepu.trans hstepv)
  have hw0 : 0 < u + v := by
    have hv0 : 0 < v := by linarith
    positivity
  rw [xiZeroCopyReciprocalSquare_re_formula, lt_div_iff₀ (sq_pos_of_pos hw0)]
  dsimp only [u, v, F] at hF
  nlinarith

/-- On the residual annulus the endpoint-complement angle has tangent above `1/130`. -/
theorem one_over_oneHundredThirty_lt_endpointComplement_abs_im_div_re_of_orderTwentyOneResidual
    (q : XiZeroCopy) (hq : XiCenteredOrderTwentyOneResidualAnnulus q) :
    (1 / 130 : ℝ) <
      |((primeArchEndpointHausdorffRadius : ℂ) -
        xiZeroCopyReciprocalSquare q).im| /
      (((primeArchEndpointHausdorffRadius : ℂ) -
        xiZeroCopyReciprocalSquare q).re) := by
  let z := xiZeroCopyReciprocalSquare q
  let R := primeArchEndpointHausdorffRadius
  let w : ℂ := (R : ℂ) - z
  have hzre : 0 < z.re := by
    simpa only [z, xiThermalNode] using xiThermalNode_pos q
  have hzQuarter : z.re < (1 / 4 : ℝ) * R := by
    simpa only [z, R, xiThermalNode] using
      xiThermalNode_lt_one_fourth_endpointRadius_of_offLine q hq.1
  have hwre : 0 < w.re := by
    dsimp only [w]
    simp only [Complex.sub_re, Complex.ofReal_re]
    nlinarith [primeArchEndpointHausdorffRadius_pos]
  have hR : R < 2 / 41 := by
    dsimp only [R]
    exact primeArchEndpointHausdorffRadius_lt_two_over_fortyOne
  have hzreL : (1 / 182 : ℝ) < z.re := by
    simpa only [z] using
      one_over_oneHundredEightyTwo_lt_re_xiZeroCopyReciprocalSquare_of_orderTwentyOneResidual
        q hq
  have hwreU : w.re < 2 / 41 - 1 / 182 := by
    dsimp only [w]
    simp only [Complex.sub_re, Complex.ofReal_re]
    linarith
  have him : (1 / 3000 : ℝ) < |z.im| := by
    simpa only [z] using
      one_over_threeThousand_lt_abs_im_xiZeroCopyReciprocalSquare_of_orderTwentyOneResidual
        q hq
  have hwim : |w.im| = |z.im| := by
    dsimp only [w]
    simp
  change (1 / 130 : ℝ) < |w.im| / w.re
  rw [lt_div_iff₀ hwre]
  rw [hwim]
  nlinarith

private theorem arctan_one_over_oneHundredThirty_cubic_lower :
    (1 / 130 : ℝ) - (1 / 130 : ℝ) ^ 3 / 3 ≤ Real.arctan (1 / 130 : ℝ) := by
  have h :=
    GaloisForLFunctions.HTGeometry.sub_arctan_le_cube_div_three
      (t := (1 / 130 : ℝ)) (by norm_num)
  linarith

private theorem endpointComplement_abs_arg_lower_of_orderTwentyOneResidual
    (q : XiZeroCopy) (hq : XiCenteredOrderTwentyOneResidualAnnulus q) :
    (1 / 130 : ℝ) - (1 / 130 : ℝ) ^ 3 / 3 <
      |((primeArchEndpointHausdorffRadius : ℂ) -
        xiZeroCopyReciprocalSquare q).arg| := by
  let w : ℂ := (primeArchEndpointHausdorffRadius : ℂ) -
    xiZeroCopyReciprocalSquare q
  have hzQuarter :=
    xiThermalNode_lt_one_fourth_endpointRadius_of_offLine q hq.1
  have hwre : 0 < w.re := by
    dsimp only [w]
    simp only [Complex.sub_re, Complex.ofReal_re]
    rw [xiThermalNode] at hzQuarter
    nlinarith [primeArchEndpointHausdorffRadius_pos]
  have hratio : (1 / 130 : ℝ) < |w.im| / w.re := by
    simpa only [w] using
      one_over_oneHundredThirty_lt_endpointComplement_abs_im_div_re_of_orderTwentyOneResidual q hq
  have hatan : Real.arctan (1 / 130 : ℝ) < Real.arctan (|w.im| / w.re) :=
    Real.arctan_strictMono hratio
  have hargabs :
      |Real.arctan (w.im / w.re)| = Real.arctan (|w.im| / w.re) := by
    by_cases him : 0 ≤ w.im
    · have hdiv : 0 ≤ w.im / w.re := div_nonneg him hwre.le
      rw [abs_of_nonneg him, abs_of_nonneg (Real.arctan_nonneg.mpr hdiv)]
    · have him' : w.im ≤ 0 := le_of_not_ge him
      have hdiv : w.im / w.re ≤ 0 := div_nonpos_of_nonpos_of_nonneg him' hwre.le
      rw [abs_of_nonpos him', abs_of_nonpos (Real.arctan_le_zero.mpr hdiv),
        ← Real.arctan_neg]
      congr 1
      ring
  rw [arg_eq_arctan_of_re_pos hwre, hargabs]
  exact arctan_one_over_oneHundredThirty_cubic_lower.trans_lt hatan

private theorem re_twentyOne_pow_mul_pow_nonneg_of_opposite_phase_of_pow_pos
    (z w : ℂ) (r : ℕ)
    (hzre : 0 < z.re) (hwre : 0 < w.re)
    (hwim : w.im = -z.im)
    (hzsector : (121 / 10 : ℝ) * |z.im| ≤ z.re)
    (hwsector : (363 / 10 : ℝ) * |w.im| ≤ w.re)
    (hzpow : 0 < (z ^ 21).re) (hr : r ≤ 57) :
    0 ≤ (z ^ 21 * w ^ r).re := by
  have hzarg : |z.arg| ≤ (10 / 121 : ℝ) :=
    abs_arg_le_of_re_pos_for_scaledHausdorff hzre (by nlinarith)
  have hwarg : |w.arg| ≤ (10 / 363 : ℝ) :=
    abs_arg_le_of_re_pos_for_scaledHausdorff hwre (by nlinarith)
  let x : ℝ := 21 * z.arg
  let y : ℝ := (r : ℝ) * w.arg
  have hxcoarse : |x| ≤ (210 / 121 : ℝ) := by
    calc
      |x| = 21 * |z.arg| := by norm_num [x]
      _ ≤ 21 * (10 / 121 : ℝ) := mul_le_mul_of_nonneg_left hzarg (by norm_num)
      _ = 210 / 121 := by ring
  have hxpi : |x| < Real.pi :=
    hxcoarse.trans_lt (by nlinarith [Real.pi_gt_d20])
  have hnorm : 0 < ‖z‖ ^ 21 := by
    apply pow_pos
    exact norm_pos_iff.mpr (fun hz => by simpa [hz] using hzre.ne')
  have hpolar : (z ^ 21).re = ‖z‖ ^ 21 * Real.cos x := by
    have h := pow_mul_pow_re_eq_norm_cos z 1 21 0
    norm_num [x] at h ⊢
    exact h
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
      have hx0 : 0 ≤ x := mul_nonneg (by norm_num) hzarg0
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
      have hx0 : x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by norm_num) hzarg0
      have hy0 : 0 ≤ y := mul_nonneg hr0 hwarg0
      constructor
      · nlinarith [hx.1, hy0]
      · nlinarith [hy.2, hx0]
  rw [pow_mul_pow_re_eq_norm_cos]
  exact mul_nonneg
    (mul_nonneg (pow_nonneg (norm_nonneg z) 21) (pow_nonneg (norm_nonneg w) r))
    (Real.cos_pos_of_mem_Ioo (by simpa only [x, y, Nat.cast_ofNat] using hangle)).le

private theorem re_twentyOne_pow_mul_pow_pos_of_residual
    (q : XiZeroCopy) (r : ℕ)
    (hq : XiCenteredOrderTwentyOneResidualAnnulus q)
    (hrLower : 22 ≤ r) (hrUpper : r ≤ 57) :
    0 < (xiZeroCopyReciprocalSquare q ^ 21 *
      ((primeArchEndpointHausdorffRadius : ℂ) -
        xiZeroCopyReciprocalSquare q) ^ r).re := by
  let z := xiZeroCopyReciprocalSquare q
  let R := primeArchEndpointHausdorffRadius
  let w : ℂ := (R : ℂ) - z
  have hzre : 0 < z.re := by
    simpa only [z, xiThermalNode] using xiThermalNode_pos q
  have hzQuarter : z.re < (1 / 4 : ℝ) * R := by
    simpa only [z, R, xiThermalNode] using
      xiThermalNode_lt_one_fourth_endpointRadius_of_offLine q hq.1
  have hwre : 0 < w.re := by
    dsimp only [w]
    simp only [Complex.sub_re, Complex.ofReal_re]
    nlinarith [primeArchEndpointHausdorffRadius_pos]
  have hzarg : |z.arg| ≤ (10 / 121 : ℝ) :=
    abs_arg_le_of_re_pos_for_scaledHausdorff hzre (by
      have hsector := twelvePointOne_mul_abs_im_xiZeroCopyReciprocalSquare_le_re q
      change (121 / 10 : ℝ) * |z.im| ≤ z.re at hsector
      nlinarith [hsector])
  have hwarg : |w.arg| ≤ (10 / 363 : ℝ) :=
    abs_arg_le_of_re_pos_for_scaledHausdorff hwre (by
      have hsector : (363 / 10 : ℝ) * |w.im| ≤ w.re := by
        dsimp only [w]
        simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, abs_neg,
          Complex.sub_re, Complex.ofReal_re]
        have hzsector := twelvePointOne_mul_abs_im_xiZeroCopyReciprocalSquare_le_re q
        change (121 / 10 : ℝ) * |z.im| ≤ z.re at hzsector
        nlinarith [hzsector]
      nlinarith)
  have hwargLower :
      (1 / 130 : ℝ) - (1 / 130 : ℝ) ^ 3 / 3 < |w.arg| := by
    simpa only [w] using endpointComplement_abs_arg_lower_of_orderTwentyOneResidual q hq
  let x : ℝ := 21 * z.arg
  let y : ℝ := (r : ℝ) * w.arg
  have hxBound : |x| ≤ (210 / 121 : ℝ) := by
    calc
      |x| = 21 * |z.arg| := by norm_num [x]
      _ ≤ 21 * (10 / 121 : ℝ) := mul_le_mul_of_nonneg_left hzarg (by norm_num)
      _ = 210 / 121 := by ring
  have hr0 : 0 ≤ (r : ℝ) := Nat.cast_nonneg r
  have hrL : (22 : ℝ) ≤ r := by exact_mod_cast hrLower
  have hrU : (r : ℝ) ≤ 57 := by exact_mod_cast hrUpper
  have hyBound : |y| < Real.pi / 2 := by
    have h : |y| ≤ (190 / 121 : ℝ) := by
      calc
        |y| = (r : ℝ) * |w.arg| := by
          simp only [y, abs_mul, abs_of_nonneg hr0]
        _ ≤ (r : ℝ) * (10 / 363 : ℝ) := mul_le_mul_of_nonneg_left hwarg hr0
        _ ≤ 190 / 121 := by nlinarith
    exact h.trans_lt (by nlinarith [Real.pi_gt_d20])
  have hcancel :
      22 * ((1 / 130 : ℝ) - (1 / 130 : ℝ) ^ 3 / 3) <
        (r : ℝ) * |w.arg| := by
    calc
      22 * ((1 / 130 : ℝ) - (1 / 130 : ℝ) ^ 3 / 3) <
          22 * |w.arg| := mul_lt_mul_of_pos_left hwargLower (by norm_num)
      _ ≤ (r : ℝ) * |w.arg| := mul_le_mul_of_nonneg_right hrL (abs_nonneg _)
  have hangle : x + y ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    rw [abs_le] at hxBound
    rw [abs_lt] at hyBound
    by_cases hzim : 0 ≤ z.im
    · have hzarg0 : 0 ≤ z.arg := Complex.arg_nonneg_iff.mpr hzim
      have hwim0 : w.im ≤ 0 := by dsimp only [w]; simp; linarith
      have hwarg0 : w.arg ≤ 0 := by
        rw [arg_eq_arctan_of_re_pos hwre]
        exact Real.arctan_le_zero.mpr
          (div_nonpos_of_nonpos_of_nonneg hwim0 hwre.le)
      have hyabs : -y = (r : ℝ) * |w.arg| := by
        rw [abs_of_nonpos hwarg0]
        dsimp only [y]
        ring
      constructor
      · have hx0 : 0 ≤ x := mul_nonneg (by norm_num) hzarg0
        linarith
      · rw [← hyabs] at hcancel
        nlinarith [Real.pi_gt_d20]
    · have hzim0 : z.im ≤ 0 := le_of_not_ge hzim
      have hzarg0 : z.arg ≤ 0 := by
        rw [arg_eq_arctan_of_re_pos hzre]
        exact Real.arctan_le_zero.mpr
          (div_nonpos_of_nonpos_of_nonneg hzim0 hzre.le)
      have hwim0 : 0 ≤ w.im := by dsimp only [w]; simp; linarith
      have hwarg0 : 0 ≤ w.arg := Complex.arg_nonneg_iff.mpr hwim0
      have hyabs : y = (r : ℝ) * |w.arg| := by
        rw [abs_of_nonneg hwarg0]
      constructor
      · rw [← hyabs] at hcancel
        nlinarith [Real.pi_gt_d20]
      · have hx0 : x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by norm_num) hzarg0
        linarith
  rw [pow_mul_pow_re_eq_norm_cos]
  have hnormz : 0 < ‖z‖ ^ 21 := pow_pos (norm_pos_iff.mpr (by
    intro hz
    simpa [hz] using hzre.ne')) 21
  have hnormw : 0 < ‖w‖ ^ r := pow_pos (norm_pos_iff.mpr (by
    intro hw
    have := congrArg Complex.re hw
    simp only [Complex.zero_re] at this
    linarith)) r
  exact mul_pos (mul_pos hnormz hnormw)
    (Real.cos_pos_of_mem_Ioo (by simpa only [x, y, Nat.cast_ofNat] using hangle))

/-- Mixed endpoint compensation makes the order-twenty-one atom nonnegative for `22 ≤ r ≤ 57`. -/
theorem re_xiCentral_scaledBasis_orderTwentyOneClaw_nonneg
    (q : XiZeroCopy) (r : ℕ) (hrLower : 22 ≤ r) (hrUpper : r ≤ 57) :
    0 ≤ (xiZeroCopyReciprocalSquare q ^ 21 *
      ((primeArchEndpointHausdorffRadius : ℂ) -
        xiZeroCopyReciprocalSquare q) ^ r).re := by
  let z := xiZeroCopyReciprocalSquare q
  let R := primeArchEndpointHausdorffRadius
  let w : ℂ := (R : ℂ) - z
  by_cases hon : (q.1 : ℂ).re = 1 / 2
  · have him : z.im = 0 := by
      dsimp only [z]
      rw [xiZeroCopyReciprocalSquare_im_formula, hon]
      norm_num
    have hzReal : z = (z.re : ℂ) := by
      apply Complex.ext
      · simp
      · simpa using him
    have hwReal : w = ((R - z.re : ℝ) : ℂ) := by
      dsimp only [w]
      rw [hzReal]
      norm_num
    have hzre : 0 < z.re := by
      simpa only [z, xiThermalNode] using xiThermalNode_pos q
    have hzleR : z.re ≤ R := by
      simpa only [z, R, xiThermalNode] using
        xiThermalNode_le_primeArchEndpointHausdorffRadius q
    change 0 ≤ (z ^ 21 * w ^ r).re
    rw [hzReal, hwReal]
    norm_cast
    exact mul_nonneg (pow_nonneg hzre.le 21)
      (pow_nonneg (sub_nonneg.mpr hzleR) r)
  · have hzre : 0 < z.re := by
      simpa only [z, xiThermalNode] using xiThermalNode_pos q
    have hzQuarter : z.re < (1 / 4 : ℝ) * R := by
      simpa only [z, R, xiThermalNode] using
        xiThermalNode_lt_one_fourth_endpointRadius_of_offLine q hon
    have hwre : 0 < w.re := by
      dsimp only [w]
      simp only [Complex.sub_re, Complex.ofReal_re]
      nlinarith [primeArchEndpointHausdorffRadius_pos]
    have hzsector : (121 / 10 : ℝ) * |z.im| ≤ z.re := by
      simpa only [z] using twelvePointOne_mul_abs_im_xiZeroCopyReciprocalSquare_le_re q
    have hwsector : (363 / 10 : ℝ) * |w.im| ≤ w.re := by
      dsimp only [w]
      simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, abs_neg,
        Complex.sub_re, Complex.ofReal_re]
      nlinarith
    have hwim : w.im = -z.im := by dsimp only [w]; simp
    by_cases hq : XiCenteredOrderTwentyOneResidualAnnulus q
    · exact (by
        simpa only [z, R, w] using
          (re_twentyOne_pow_mul_pow_pos_of_residual q r hq hrLower hrUpper).le)
    · have hzpow : 0 < (z ^ 21).re := by
        simpa only [z] using
          xiZeroCopyReciprocalSquare_pow_twentyOne_re_pos_of_not_mem_residualAnnulus q hq
      exact re_twentyOne_pow_mul_pow_nonneg_of_opposite_phase_of_pow_pos
        z w r hzre hwre hwim hzsector hwsector hzpow hrUpper

/-- The completed source Hausdorff differences are nonnegative on the mixed claw. -/
theorem scaledPrimeArchEndpointHausdorffDifference_orderTwentyOneClaw_nonnegative
    (r : ℕ) (hrLower : 22 ≤ r) (hrUpper : r ≤ 57) :
    0 ≤ scaledHausdorffMomentDifference primeArchEndpointHausdorffRadius
      normalizedPrimeArchMoment 20 r := by
  rw [scaledHausdorffMomentDifference_eq_re_xiCentralSum,
    Complex.re_tsum (summable_xiCentralScaledHausdorffTerm
      primeArchEndpointHausdorffRadius 20 r)]
  apply tsum_nonneg
  intro q
  exact re_xiCentral_scaledBasis_orderTwentyOneClaw_nonneg
    q r hrLower hrUpper

/-- Remaining endpoint carrier after removing both the order-twenty rectangle and the mixed
order-twenty-one claw. -/
def PrimeArchEndpointOrderTwentyOneMixedClawTailNonnegative : Prop :=
  ∀ k r : ℕ, 20 < k ∨ 57 < r ∨ (k = 20 ∧ r < 22) →
    0 ≤ scaledHausdorffMomentDifference primeArchEndpointHausdorffRadius
      normalizedPrimeArchMoment k r

/-- The order-twenty RH tail is exactly its complement after deleting the unconditional mixed
claw. -/
theorem primeArchEndpointOrderTwentyHausdorffTailNonnegative_iff_mixedClawTailNonnegative :
    PrimeArchEndpointOrderTwentyHausdorffTailNonnegative ↔
      PrimeArchEndpointOrderTwentyOneMixedClawTailNonnegative := by
  constructor
  · intro hold k r htail
    exact hold k r (by omega)
  · intro hnew k r htail
    by_cases hr : r ≤ 57
    · by_cases hk : k ≤ 19
      · exact
          scaledPrimeArchEndpointHausdorffDifference_orderTwentyRectangle_nonnegative
            k r hk hr
      · by_cases hk20 : k = 20
        · subst k
          by_cases hr22 : 22 ≤ r
          · exact
              scaledPrimeArchEndpointHausdorffDifference_orderTwentyOneClaw_nonnegative
                r hr22 hr
          · exact hnew 20 r (Or.inr (Or.inr ⟨rfl, by omega⟩))
        · exact hnew k r (Or.inl (by omega))
    · exact hnew k r (Or.inr (Or.inl (by omega)))

/-- The claw-excised endpoint tail remains exactly equivalent to RH. -/
theorem primeArchEndpointOrderTwentyOneMixedClawTailNonnegative_iff_riemannHypothesis :
    PrimeArchEndpointOrderTwentyOneMixedClawTailNonnegative ↔ RiemannHypothesis :=
  primeArchEndpointOrderTwentyHausdorffTailNonnegative_iff_mixedClawTailNonnegative.symm.trans
    primeArchEndpointOrderTwentyHausdorffTailNonnegative_iff_riemannHypothesis

end

end RHTower
