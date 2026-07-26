import GaloisForLFunctions.RHTower.XiCenteredOrdersSeventeenEighteenSourcePositivity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Centered order-nineteen source-budget boundary

The fourth reciprocal-trace source data and the universal off-line height floor
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
    (hinner : ((q.1 : ℂ).re - 1 / 2) ^ 2 ≤ (1299 / 10000 : ℝ)) :
    163 * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ 2 <
      ((q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2) ^ 2 := by
  let u : ℝ := ((q.1 : ℂ).re - 1 / 2) ^ 2
  let v : ℝ := (q.1 : ℂ).im ^ 2
  let A : ℝ := v - u
  let B : ℝ := 2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im
  have hu : u ≤ 1299 / 10000 := by simpa only [u] using hinner
  have hv : 7907 / 93 < v := by
    simpa only [v] using
      xiZeroCopy_offLine_sevenThousandNineHundredSeven_over_ninetyThree_lt_im_sq
        q hoff
  have hA : 8489 / 100 < A := by dsimp only [A]; nlinarith
  have hB : B ^ 2 = 4 * u * v := by dsimp only [B, u, v]; ring
  have hBbound : 163 * B ^ 2 ≤ (211737 / 2500 : ℝ) * v := by
    rw [hB]
    nlinarith
  have hvA : v ≤ A + 1299 / 10000 := by dsimp only [A]; nlinarith
  have hbase :
      (211737 / 2500 : ℝ) * (8489 / 100 + 1299 / 10000) <
        (8489 / 100 : ℝ) ^ 2 := by
    norm_num
  have hprod :
      0 < (A - 8489 / 100) *
        (A + 8489 / 100 - 211737 / 2500) := by
    apply mul_pos
    · nlinarith
    · nlinarith
  have hpoly :
      (211737 / 2500 : ℝ) * (A + 1299 / 10000) < A ^ 2 := by
    nlinarith
  change 163 * B ^ 2 < A ^ 2
  nlinarith

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
    (1299 / 10000 : ℝ) < ((q.1 : ℂ).re - 1 / 2) ^ 2 ∧
      ((q.1 : ℂ).re - 1 / 2) ^ 2 < 1 / 4 ∧
        295 / 2 ≤ (q.1 : ℂ).im ^ 2 ∧
          (q.1 : ℂ).im ^ 2 < 327 / 2

theorem xiCenteredOrderTwentySectorFailure_mem_residualAnnulus
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    (hfail :
      ((q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2) ^ 2 ≤
        163 * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ 2) :
    XiCenteredOrderTwentyResidualAnnulus q := by
  have hedge : (1299 / 10000 : ℝ) <
      ((q.1 : ℂ).re - 1 / 2) ^ 2 := by
    by_contra h
    linarith [xiCenteredOrderTwentySectorRatio_of_offLine_inner
      q hoff (le_of_not_gt h)]
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  have hu : ((q.1 : ℂ).re - 1 / 2) ^ 2 < (1 / 4 : ℝ) := by
    nlinarith [mul_pos hstrip.1 (sub_pos.mpr hstrip.2)]
  have hvlow : 295 / 2 ≤ (q.1 : ℂ).im ^ 2 := by
    by_contra h
    exact hoff
      (xiZeroCopy_re_eq_half_of_im_sq_lt_twoHundredNinetyFiveHalves q
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

end

end RHTower
