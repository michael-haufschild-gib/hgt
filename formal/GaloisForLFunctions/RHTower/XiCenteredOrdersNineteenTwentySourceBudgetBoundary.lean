import GaloisForLFunctions.RHTower.XiFourthTraceExtendedCriticalLineBand
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Centered orders nineteen and twenty source-budget boundaries

The extended fourth reciprocal-trace source band and the universal off-line height floor
force positivity of the twentieth centered reciprocal power outside one explicit
finite annulus. Consequently, emptiness of precisely that annulus discharges
positivity of normalized prime-archimedean moment nineteen.
-/

open Complex

namespace RHTower

noncomputable section

theorem orderTwentyReciprocalPower_re_pos_of_sectorRatio
    {A B : ℝ} (hA : 0 < A) (hsector : 163 * B ^ 2 < A ^ 2) :
    0 < ((((A : ℂ) - B * I)⁻¹) ^ 20).re := by
  let mu : ℂ := ((A : ℂ) - B * I)⁻¹
  have hden : 0 < A ^ 2 + B ^ 2 := by nlinarith [sq_nonneg B]
  have hmure : mu.re = A / (A ^ 2 + B ^ 2) := by
    dsimp only [mu]
    rw [Complex.inv_re, Complex.normSq_apply]
    simp
    ring
  have hmuim : mu.im = B / (A ^ 2 + B ^ 2) := by
    dsimp only [mu]
    rw [Complex.inv_im, Complex.normSq_apply]
    simp
    ring
  have hmurepos : 0 < mu.re := by rw [hmure]; positivity
  have htan : Real.tan (Complex.arg mu) = B / A := by
    rw [Complex.tan_arg, hmuim, hmure]
    field_simp
  have hsq : (10000 * B) ^ 2 < (784 * A) ^ 2 := by
    nlinarith [sq_pos_of_pos hA]
  have habsScaled : |10000 * B| < 784 * A := by
    exact abs_lt_of_sq_lt_sq hsq (mul_nonneg (by norm_num) hA.le)
  have habsB : |B| < (784 / 10000 : ℝ) * A := by
    rw [abs_mul] at habsScaled
    norm_num at habsScaled
    nlinarith
  have habsRatio : |B / A| < 784 / 10000 := by
    rw [abs_div, abs_of_pos hA]
    rw [div_lt_iff₀ hA]
    exact habsB
  have hargRange : |Complex.arg mu| < Real.pi / 2 := by
    rw [Complex.abs_arg_lt_pi_div_two_iff]
    exact Or.inl hmurepos
  have htanabs : Real.tan |Complex.arg mu| = |B / A| := by
    by_cases harg : 0 ≤ Complex.arg mu
    · rw [abs_of_nonneg harg, htan, abs_of_nonneg]
      rw [← htan]
      exact Real.tan_nonneg_of_nonneg_of_le_pi_div_two harg
        ((le_abs_self _).trans hargRange.le)
    · have hargneg : Complex.arg mu < 0 := lt_of_not_ge harg
      rw [abs_of_neg hargneg, Real.tan_neg, htan, abs_of_neg]
      rw [← htan]
      exact Real.tan_neg_of_neg_of_pi_div_two_lt hargneg (by
        rw [abs_lt] at hargRange
        exact hargRange.1)
  have hargSmall : |Complex.arg mu| < 784 / 10000 := by
    by_cases hargzero : Complex.arg mu = 0
    · simp [hargzero]
    · have hargabspos : 0 < |Complex.arg mu| := abs_pos.mpr hargzero
      have hlt := Real.lt_tan hargabspos hargRange
      rw [htanabs] at hlt
      exact hlt.trans habsRatio
  have hangle : |20 * Complex.arg mu| < Real.pi / 2 := by
    rw [abs_mul]
    norm_num
    nlinarith [Real.pi_gt_d20]
  have hcos : 0 < Real.cos (20 * Complex.arg mu) := by
    exact Real.cos_pos_of_mem_Ioo (abs_lt.mp hangle)
  have hmu : mu ≠ 0 := by
    exact inv_ne_zero (by
      intro hz
      have hzre := congrArg Complex.re hz
      simp at hzre
      linarith)
  have hnorm : 0 < ‖mu‖ ^ 20 := pow_pos (norm_pos_iff.mpr hmu) _
  change 0 < (mu ^ 20).re
  rw [← Complex.norm_mul_exp_arg_mul_I mu, mul_pow, ← Complex.exp_nat_mul]
  have hexp :
      ((20 : ℕ) : ℂ) * ((Complex.arg mu : ℂ) * I) =
        ((20 * Complex.arg mu : ℝ) : ℂ) * I := by
    push_cast
    ring
  rw [hexp, mul_re, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im]
  rw [← Complex.ofReal_pow]
  simp only [ofReal_re, ofReal_im, zero_mul, sub_zero]
  exact mul_pos hnorm hcos

theorem xiCenteredOrderTwentySectorRatio_of_offLine_inner
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    (hinner : ((q.1 : ℂ).re - 1 / 2) ^ 2 ≤ (2365 / 10464 : ℝ)) :
    163 * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ 2 <
      ((q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2) ^ 2 := by
  let u : ℝ := ((q.1 : ℂ).re - 1 / 2) ^ 2
  let v : ℝ := (q.1 : ℂ).im ^ 2
  let B : ℝ := 2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im
  have hu : u ≤ 2365 / 10464 := by simpa only [u] using hinner
  have hu0 : 0 < u := by
    dsimp only [u]
    exact sq_pos_of_ne_zero (sub_ne_zero.mpr hoff)
  have hv : (2365 / 16 : ℝ) ≤ v := by
    apply le_of_not_gt
    intro hvlt
    exact hoff (xiZeroCopy_re_eq_half_of_im_sq_lt_2365_over_16 q (by
      simpa only [v] using hvlt))
  have hv0 : 0 < v := by nlinarith
  have h654 : 654 * u ≤ v := by nlinarith
  have hprod : 0 ≤ v * (v - 654 * u) :=
    mul_nonneg hv0.le (sub_nonneg.mpr h654)
  have hB : B ^ 2 = 4 * u * v := by dsimp only [B, u, v]; ring
  change 163 * B ^ 2 < (v - u) ^ 2
  rw [hB]
  nlinarith [sq_pos_of_pos hu0]

theorem xiCenteredOrderTwentySectorRatio_of_threeHundredTwentySevenHalves_le_im_sq
    (q : XiZeroCopy) (hhigh : 327 / 2 ≤ (q.1 : ℂ).im ^ 2) :
    163 * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ 2 <
      ((q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2) ^ 2 := by
  let u : ℝ := ((q.1 : ℂ).re - 1 / 2) ^ 2
  let v : ℝ := (q.1 : ℂ).im ^ 2
  let A : ℝ := v - u
  let B : ℝ := 2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  have hu : u < 1 / 4 := by
    dsimp only [u]
    nlinarith [mul_pos hstrip.1 (sub_pos.mpr hstrip.2)]
  have hv : 327 / 2 ≤ v := by simpa only [v] using hhigh
  have hB : B ^ 2 = 4 * u * v := by dsimp only [B, u, v]; ring
  have hBbound : 163 * B ^ 2 < 163 * v := by rw [hB]; nlinarith
  have hbase : 163 * v < (v - 1 / 4) ^ 2 := by
    have hprod : 0 ≤ (v - 327 / 2) * v :=
      mul_nonneg (sub_nonneg.mpr hv) (by positivity)
    nlinarith
  have hA0 : 0 < A := by dsimp only [A]; nlinarith
  have hleft : 0 < v - 1 / 4 := by nlinarith
  have hlt : v - 1 / 4 < A := by dsimp only [A]; nlinarith
  have hAsq : (v - 1 / 4) ^ 2 < A ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hlt) (add_pos hleft hA0)]
  change 163 * B ^ 2 < A ^ 2
  linarith

def XiCenteredOrderTwentyResidualAnnulus (q : XiZeroCopy) : Prop :=
  (q.1 : ℂ).re ≠ 1 / 2 ∧
    (2365 / 10464 : ℝ) < ((q.1 : ℂ).re - 1 / 2) ^ 2 ∧
      ((q.1 : ℂ).re - 1 / 2) ^ 2 < 1 / 4 ∧
        2365 / 16 ≤ (q.1 : ℂ).im ^ 2 ∧
          (q.1 : ℂ).im ^ 2 < 327 / 2

theorem xiCenteredOrderTwentySectorFailure_mem_residualAnnulus
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    (hfail :
      ((q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2) ^ 2 ≤
        163 * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ 2) :
    XiCenteredOrderTwentyResidualAnnulus q := by
  have hedge : (2365 / 10464 : ℝ) <
      ((q.1 : ℂ).re - 1 / 2) ^ 2 := by
    by_contra h
    linarith [xiCenteredOrderTwentySectorRatio_of_offLine_inner
      q hoff (le_of_not_gt h)]
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  have hu : ((q.1 : ℂ).re - 1 / 2) ^ 2 < (1 / 4 : ℝ) := by
    nlinarith [mul_pos hstrip.1 (sub_pos.mpr hstrip.2)]
  have hvlow : 2365 / 16 ≤ (q.1 : ℂ).im ^ 2 := by
    by_contra h
    exact hoff
      (xiZeroCopy_re_eq_half_of_im_sq_lt_2365_over_16 q
        (lt_of_not_ge h))
  have hvhigh : (q.1 : ℂ).im ^ 2 < 327 / 2 := by
    by_contra h
    linarith [
      xiCenteredOrderTwentySectorRatio_of_threeHundredTwentySevenHalves_le_im_sq
        q (le_of_not_gt h)]
  exact ⟨hoff, hedge, hu, hvlow, hvhigh⟩

theorem xiZeroCopyReciprocalSquare_pow_twenty_re_pos_of_not_mem_residualAnnulus
    (q : XiZeroCopy) (hnot : ¬ XiCenteredOrderTwentyResidualAnnulus q) :
    0 < (xiZeroCopyReciprocalSquare q ^ 20).re := by
  rw [xiZeroCopyReciprocalSquare_eq_centeredOrderCoordinate]
  let A : ℝ := (q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2
  let B : ℝ := 2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im
  change 0 < ((((A : ℂ) - B * I)⁻¹) ^ 20).re
  by_cases hoff : (q.1 : ℂ).re = 1 / 2
  · have hA : 0 < A := by
      dsimp only [A]
      rw [hoff]
      norm_num
      exact sq_pos_of_ne_zero (xi_divisor_support_im_ne_zero q.1)
    apply orderTwentyReciprocalPower_re_pos_of_sectorRatio hA
    dsimp only [A, B]
    rw [hoff]
    norm_num
    nlinarith [sq_pos_of_ne_zero (xi_divisor_support_im_ne_zero q.1)]
  · by_contra hpos
    have hstrip := xi_divisor_support_re_mem_open_unit q.1
    have hu : ((q.1 : ℂ).re - 1 / 2) ^ 2 < (1 / 4 : ℝ) := by
      nlinarith [mul_pos hstrip.1 (sub_pos.mpr hstrip.2)]
    have hv := xiZeroCopy_offLine_eightyFive_lt_im_sq q hoff
    have hA : 0 < A := by dsimp only [A]; nlinarith
    have hfail : A ^ 2 ≤ 163 * B ^ 2 := by
      by_contra h
      have hpositive :=
        orderTwentyReciprocalPower_re_pos_of_sectorRatio hA (lt_of_not_ge h)
      have hnonpos : ((((A : ℂ) - B * I)⁻¹) ^ 20).re ≤ 0 :=
        le_of_not_gt hpos
      linarith
    exact hnot
      (xiCenteredOrderTwentySectorFailure_mem_residualAnnulus q hoff
        (by simpa only [A, B] using hfail))

def XiCenteredOrderTwentyResidualAnnulusEmpty : Prop :=
  ¬ ∃ q : XiZeroCopy, XiCenteredOrderTwentyResidualAnnulus q

/-- RH excludes the order-twenty residual annulus because every Xi divisor point is centered. -/
theorem xiCenteredOrderTwentyResidualAnnulusEmpty_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    XiCenteredOrderTwentyResidualAnnulusEmpty := by
  rintro ⟨q, hq⟩
  exact hq.1 (xi_divisor_support_re_eq_half_of_rh hRH q.1)

theorem xiZeroCopyReciprocalSquare_pow_twenty_re_pos_of_residualAnnulusEmpty
    (h : XiCenteredOrderTwentyResidualAnnulusEmpty) (q : XiZeroCopy) :
    0 < (xiZeroCopyReciprocalSquare q ^ 20).re := by
  apply xiZeroCopyReciprocalSquare_pow_twenty_re_pos_of_not_mem_residualAnnulus
  intro hq
  exact h ⟨q, hq⟩

theorem normalizedPrimeArchMoment_nineteen_pos_of_centeredOrderTwentyResidualAnnulusEmpty
    (h : XiCenteredOrderTwentyResidualAnnulusEmpty) :
    0 < normalizedPrimeArchMoment 19 := by
  apply normalizedPrimeArchMoment_pos_of_atomwise_re_pos 19
  simpa using
    xiZeroCopyReciprocalSquare_pow_twenty_re_pos_of_residualAnnulusEmpty h

theorem orderTwentyOneReciprocalPower_re_pos_of_sectorRatio
    {A B : ℝ} (hA : 0 < A) (hsector : 180 * B ^ 2 < A ^ 2) :
    0 < ((((A : ℂ) - B * I)⁻¹) ^ 21).re := by
  let mu : ℂ := ((A : ℂ) - B * I)⁻¹
  have hden : 0 < A ^ 2 + B ^ 2 := by nlinarith [sq_nonneg B]
  have hmure : mu.re = A / (A ^ 2 + B ^ 2) := by
    dsimp only [mu]
    rw [Complex.inv_re, Complex.normSq_apply]
    simp
    ring
  have hmuim : mu.im = B / (A ^ 2 + B ^ 2) := by
    dsimp only [mu]
    rw [Complex.inv_im, Complex.normSq_apply]
    simp
    ring
  have hmurepos : 0 < mu.re := by rw [hmure]; positivity
  have htan : Real.tan (Complex.arg mu) = B / A := by
    rw [Complex.tan_arg, hmuim, hmure]
    field_simp
  have hsq : (10000 * B) ^ 2 < (747 * A) ^ 2 := by
    nlinarith [sq_pos_of_pos hA]
  have habsScaled : |10000 * B| < 747 * A := by
    exact abs_lt_of_sq_lt_sq hsq (mul_nonneg (by norm_num) hA.le)
  have habsB : |B| < (747 / 10000 : ℝ) * A := by
    rw [abs_mul] at habsScaled
    norm_num at habsScaled
    nlinarith
  have habsRatio : |B / A| < 747 / 10000 := by
    rw [abs_div, abs_of_pos hA]
    rw [div_lt_iff₀ hA]
    exact habsB
  have hargRange : |Complex.arg mu| < Real.pi / 2 := by
    rw [Complex.abs_arg_lt_pi_div_two_iff]
    exact Or.inl hmurepos
  have htanabs : Real.tan |Complex.arg mu| = |B / A| := by
    by_cases harg : 0 ≤ Complex.arg mu
    · rw [abs_of_nonneg harg, htan, abs_of_nonneg]
      rw [← htan]
      exact Real.tan_nonneg_of_nonneg_of_le_pi_div_two harg
        ((le_abs_self _).trans hargRange.le)
    · have hargneg : Complex.arg mu < 0 := lt_of_not_ge harg
      rw [abs_of_neg hargneg, Real.tan_neg, htan, abs_of_neg]
      rw [← htan]
      exact Real.tan_neg_of_neg_of_pi_div_two_lt hargneg (by
        rw [abs_lt] at hargRange
        exact hargRange.1)
  have hargSmall : |Complex.arg mu| < 747 / 10000 := by
    by_cases hargzero : Complex.arg mu = 0
    · simp [hargzero]
    · have hargabspos : 0 < |Complex.arg mu| := abs_pos.mpr hargzero
      have hlt := Real.lt_tan hargabspos hargRange
      rw [htanabs] at hlt
      exact hlt.trans habsRatio
  have hangle : |21 * Complex.arg mu| < Real.pi / 2 := by
    rw [abs_mul]
    norm_num
    nlinarith [Real.pi_gt_d20]
  have hcos : 0 < Real.cos (21 * Complex.arg mu) := by
    exact Real.cos_pos_of_mem_Ioo (abs_lt.mp hangle)
  have hmu : mu ≠ 0 := by
    exact inv_ne_zero (by
      intro hz
      have hzre := congrArg Complex.re hz
      simp at hzre
      linarith)
  have hnorm : 0 < ‖mu‖ ^ 21 := pow_pos (norm_pos_iff.mpr hmu) _
  change 0 < (mu ^ 21).re
  rw [← Complex.norm_mul_exp_arg_mul_I mu, mul_pow, ← Complex.exp_nat_mul]
  have hexp :
      ((21 : ℕ) : ℂ) * ((Complex.arg mu : ℂ) * I) =
        ((21 * Complex.arg mu : ℝ) : ℂ) * I := by
    push_cast
    ring
  rw [hexp, mul_re, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im]
  rw [← Complex.ofReal_pow]
  simp only [ofReal_re, ofReal_im, zero_mul, sub_zero]
  exact mul_pos hnorm hcos

theorem xiCenteredOrderTwentyOneSectorRatio_of_offLine_inner
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    (hinner : ((q.1 : ℂ).re - 1 / 2) ^ 2 ≤ (2365 / 11552 : ℝ)) :
    180 * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ 2 <
      ((q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2) ^ 2 := by
  let u : ℝ := ((q.1 : ℂ).re - 1 / 2) ^ 2
  let v : ℝ := (q.1 : ℂ).im ^ 2
  let B : ℝ := 2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im
  have hu : u ≤ 2365 / 11552 := by simpa only [u] using hinner
  have hu0 : 0 < u := by
    dsimp only [u]
    exact sq_pos_of_ne_zero (sub_ne_zero.mpr hoff)
  have hv : (2365 / 16 : ℝ) ≤ v := by
    apply le_of_not_gt
    intro hvlt
    exact hoff (xiZeroCopy_re_eq_half_of_im_sq_lt_2365_over_16 q (by
      simpa only [v] using hvlt))
  have hv0 : 0 < v := by nlinarith
  have h722 : 722 * u ≤ v := by nlinarith
  have hprod : 0 ≤ v * (v - 722 * u) :=
    mul_nonneg hv0.le (sub_nonneg.mpr h722)
  have hB : B ^ 2 = 4 * u * v := by dsimp only [B, u, v]; ring
  change 180 * B ^ 2 < (v - u) ^ 2
  rw [hB]
  nlinarith [sq_pos_of_pos hu0]

theorem xiCenteredOrderTwentyOneSectorRatio_of_threeHundredSixtyOneHalves_le_im_sq
    (q : XiZeroCopy) (hhigh : 361 / 2 ≤ (q.1 : ℂ).im ^ 2) :
    180 * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ 2 <
      ((q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2) ^ 2 := by
  let u : ℝ := ((q.1 : ℂ).re - 1 / 2) ^ 2
  let v : ℝ := (q.1 : ℂ).im ^ 2
  let A : ℝ := v - u
  let B : ℝ := 2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  have hu : u < 1 / 4 := by
    dsimp only [u]
    nlinarith [mul_pos hstrip.1 (sub_pos.mpr hstrip.2)]
  have hv : 361 / 2 ≤ v := by simpa only [v] using hhigh
  have hB : B ^ 2 = 4 * u * v := by dsimp only [B, u, v]; ring
  have hBbound : 180 * B ^ 2 < 180 * v := by rw [hB]; nlinarith
  have hbase : 180 * v < (v - 1 / 4) ^ 2 := by
    have hprod : 0 ≤ (v - 361 / 2) * v :=
      mul_nonneg (sub_nonneg.mpr hv) (by positivity)
    nlinarith
  have hA0 : 0 < A := by dsimp only [A]; nlinarith
  have hleft : 0 < v - 1 / 4 := by nlinarith
  have hlt : v - 1 / 4 < A := by dsimp only [A]; nlinarith
  have hAsq : (v - 1 / 4) ^ 2 < A ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hlt) (add_pos hleft hA0)]
  change 180 * B ^ 2 < A ^ 2
  linarith

def XiCenteredOrderTwentyOneResidualAnnulus (q : XiZeroCopy) : Prop :=
  (q.1 : ℂ).re ≠ 1 / 2 ∧
    (2365 / 11552 : ℝ) < ((q.1 : ℂ).re - 1 / 2) ^ 2 ∧
      ((q.1 : ℂ).re - 1 / 2) ^ 2 < 1 / 4 ∧
        2365 / 16 ≤ (q.1 : ℂ).im ^ 2 ∧
          (q.1 : ℂ).im ^ 2 < 361 / 2

theorem xiCenteredOrderTwentyOneSectorFailure_mem_residualAnnulus
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    (hfail :
      ((q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2) ^ 2 ≤
        180 * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ 2) :
    XiCenteredOrderTwentyOneResidualAnnulus q := by
  have hedge : (2365 / 11552 : ℝ) <
      ((q.1 : ℂ).re - 1 / 2) ^ 2 := by
    by_contra h
    linarith [xiCenteredOrderTwentyOneSectorRatio_of_offLine_inner
      q hoff (le_of_not_gt h)]
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  have hu : ((q.1 : ℂ).re - 1 / 2) ^ 2 < (1 / 4 : ℝ) := by
    nlinarith [mul_pos hstrip.1 (sub_pos.mpr hstrip.2)]
  have hvlow : 2365 / 16 ≤ (q.1 : ℂ).im ^ 2 := by
    by_contra h
    exact hoff
      (xiZeroCopy_re_eq_half_of_im_sq_lt_2365_over_16 q
        (lt_of_not_ge h))
  have hvhigh : (q.1 : ℂ).im ^ 2 < 361 / 2 := by
    by_contra h
    linarith [
      xiCenteredOrderTwentyOneSectorRatio_of_threeHundredSixtyOneHalves_le_im_sq
        q (le_of_not_gt h)]
  exact ⟨hoff, hedge, hu, hvlow, hvhigh⟩

theorem xiZeroCopyReciprocalSquare_pow_twentyOne_re_pos_of_not_mem_residualAnnulus
    (q : XiZeroCopy) (hnot : ¬ XiCenteredOrderTwentyOneResidualAnnulus q) :
    0 < (xiZeroCopyReciprocalSquare q ^ 21).re := by
  rw [xiZeroCopyReciprocalSquare_eq_centeredOrderCoordinate]
  let A : ℝ := (q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2
  let B : ℝ := 2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im
  change 0 < ((((A : ℂ) - B * I)⁻¹) ^ 21).re
  by_cases hoff : (q.1 : ℂ).re = 1 / 2
  · have hA : 0 < A := by
      dsimp only [A]
      rw [hoff]
      norm_num
      exact sq_pos_of_ne_zero (xi_divisor_support_im_ne_zero q.1)
    apply orderTwentyOneReciprocalPower_re_pos_of_sectorRatio hA
    dsimp only [A, B]
    rw [hoff]
    norm_num
    nlinarith [sq_pos_of_ne_zero (xi_divisor_support_im_ne_zero q.1)]
  · by_contra hpos
    have hstrip := xi_divisor_support_re_mem_open_unit q.1
    have hu : ((q.1 : ℂ).re - 1 / 2) ^ 2 < (1 / 4 : ℝ) := by
      nlinarith [mul_pos hstrip.1 (sub_pos.mpr hstrip.2)]
    have hv := xiZeroCopy_offLine_eightyFive_lt_im_sq q hoff
    have hA : 0 < A := by dsimp only [A]; nlinarith
    have hfail : A ^ 2 ≤ 180 * B ^ 2 := by
      by_contra h
      have hpositive :=
        orderTwentyOneReciprocalPower_re_pos_of_sectorRatio hA (lt_of_not_ge h)
      have hnonpos : ((((A : ℂ) - B * I)⁻¹) ^ 21).re ≤ 0 :=
        le_of_not_gt hpos
      linarith
    exact hnot
      (xiCenteredOrderTwentyOneSectorFailure_mem_residualAnnulus q hoff
        (by simpa only [A, B] using hfail))

def XiCenteredOrderTwentyOneResidualAnnulusEmpty : Prop :=
  ¬ ∃ q : XiZeroCopy, XiCenteredOrderTwentyOneResidualAnnulus q

/-- RH excludes the order-twenty-one residual annulus for the same centered-divisor reason. -/
theorem xiCenteredOrderTwentyOneResidualAnnulusEmpty_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    XiCenteredOrderTwentyOneResidualAnnulusEmpty := by
  rintro ⟨q, hq⟩
  exact hq.1 (xi_divisor_support_re_eq_half_of_rh hRH q.1)

theorem xiZeroCopyReciprocalSquare_pow_twentyOne_re_pos_of_residualAnnulusEmpty
    (h : XiCenteredOrderTwentyOneResidualAnnulusEmpty) (q : XiZeroCopy) :
    0 < (xiZeroCopyReciprocalSquare q ^ 21).re := by
  apply xiZeroCopyReciprocalSquare_pow_twentyOne_re_pos_of_not_mem_residualAnnulus
  intro hq
  exact h ⟨q, hq⟩

theorem normalizedPrimeArchMoment_twenty_pos_of_centeredOrderTwentyOneResidualAnnulusEmpty
    (h : XiCenteredOrderTwentyOneResidualAnnulusEmpty) :
    0 < normalizedPrimeArchMoment 20 := by
  apply normalizedPrimeArchMoment_pos_of_atomwise_re_pos 20
  simpa using
    xiZeroCopyReciprocalSquare_pow_twentyOne_re_pos_of_residualAnnulusEmpty h

def XiCenteredDegreeTenResidualAnnuliEmpty : Prop :=
  XiCenteredOrderTwentyResidualAnnulusEmpty ∧
    XiCenteredOrderTwentyOneResidualAnnulusEmpty

/-- RH simultaneously discharges both residual-annulus interfaces at degree ten. -/
theorem xiCenteredDegreeTenResidualAnnuliEmpty_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    XiCenteredDegreeTenResidualAnnuliEmpty :=
  ⟨xiCenteredOrderTwentyResidualAnnulusEmpty_of_riemannHypothesis hRH,
    xiCenteredOrderTwentyOneResidualAnnulusEmpty_of_riemannHypothesis hRH⟩

theorem normalizedPrimeArchMoment_nineteen_pos_of_degreeTenResidualAnnuliEmpty
    (h : XiCenteredDegreeTenResidualAnnuliEmpty) :
    0 < normalizedPrimeArchMoment 19 :=
  normalizedPrimeArchMoment_nineteen_pos_of_centeredOrderTwentyResidualAnnulusEmpty h.1

theorem normalizedPrimeArchMoment_twenty_pos_of_degreeTenResidualAnnuliEmpty
    (h : XiCenteredDegreeTenResidualAnnuliEmpty) :
    0 < normalizedPrimeArchMoment 20 :=
  normalizedPrimeArchMoment_twenty_pos_of_centeredOrderTwentyOneResidualAnnulusEmpty h.2

/-- Degree-nineteen source-moment positivity no longer needs a residual-annulus premise once RH
is in scope. -/
theorem normalizedPrimeArchMoment_nineteen_pos_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    0 < normalizedPrimeArchMoment 19 :=
  normalizedPrimeArchMoment_nineteen_pos_of_degreeTenResidualAnnuliEmpty
    (xiCenteredDegreeTenResidualAnnuliEmpty_of_riemannHypothesis hRH)

/-- Degree-twenty source-moment positivity no longer needs a residual-annulus premise once RH is
in scope. -/
theorem normalizedPrimeArchMoment_twenty_pos_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    0 < normalizedPrimeArchMoment 20 :=
  normalizedPrimeArchMoment_twenty_pos_of_degreeTenResidualAnnuliEmpty
    (xiCenteredDegreeTenResidualAnnuliEmpty_of_riemannHypothesis hRH)

end

end RHTower
