import GaloisForLFunctions.RHTower.XiOrderFourteenCornerSourceExclusion
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The compact edge corner for the order-sixteen squared-Xi source

For a Xi zero with centered coordinates `delta + gamma*I`, the order-sixteen radial atom is
controlled by the seventeenth reciprocal power of

`A - B*I`, where `A = gamma^2 - delta^2 + y` and `B = 2*delta*gamma`.

The rational sector coefficient `118` protects the central band `delta^2 <= 9/50` and every
zero above squared height `118`.  Thus, at every `y > 1/4`, failure of that certificate forces
an off-critical zero into the compact corner

`9/50 < delta^2 < 1/4`, `85 < gamma^2 < 118`.

The proof is unconditional and uses no zero table.
-/

open Complex

namespace RHTower

noncomputable section

/-- A positive real base whose squared transverse-to-longitudinal ratio is below `1/118` has a
strictly positive seventeenth reciprocal power. -/
theorem orderSeventeenReciprocalPower_re_pos_of_sectorRatio
    {A B : ℝ} (hA : 0 < A) (hsector : 118 * B ^ 2 < A ^ 2) :
    0 < ((((A : ℂ) - B * I)⁻¹) ^ 17).re := by
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
  have hsq : (10000 * B) ^ 2 < (923 * A) ^ 2 := by
    nlinarith [sq_pos_of_pos hA]
  have habsScaled : |10000 * B| < 923 * A := by
    exact abs_lt_of_sq_lt_sq hsq (mul_nonneg (by norm_num) hA.le)
  have habsB : |B| < (923 / 10000 : ℝ) * A := by
    rw [abs_mul] at habsScaled
    norm_num at habsScaled
    nlinarith
  have habsRatio : |B / A| < 923 / 10000 := by
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
  have hargSmall : |Complex.arg mu| < 923 / 10000 := by
    by_cases hargzero : Complex.arg mu = 0
    · simp [hargzero]
    · have hargabspos : 0 < |Complex.arg mu| := abs_pos.mpr hargzero
      have hlt := Real.lt_tan hargabspos hargRange
      rw [htanabs] at hlt
      exact hlt.trans habsRatio
  have hangle : |17 * Complex.arg mu| < Real.pi / 2 := by
    rw [abs_mul]
    norm_num
    nlinarith [Real.pi_gt_d20]
  have hcos : 0 < Real.cos (17 * Complex.arg mu) := by
    exact Real.cos_pos_of_mem_Ioo (abs_lt.mp hangle)
  have hmu : mu ≠ 0 := by
    exact inv_ne_zero (by
      intro hz
      have hzre := congrArg Complex.re hz
      simp at hzre
      linarith)
  have hnorm : 0 < ‖mu‖ ^ 17 := pow_pos (norm_pos_iff.mpr hmu) _
  change 0 < (mu ^ 17).re
  rw [← Complex.norm_mul_exp_arg_mul_I mu, mul_pow, ← Complex.exp_nat_mul]
  have hexp :
      ((17 : ℕ) : ℂ) * ((Complex.arg mu : ℂ) * I) =
        ((17 * Complex.arg mu : ℝ) : ℂ) * I := by
    push_cast
    ring
  rw [hexp, mul_re, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im]
  rw [← Complex.ofReal_pow]
  simp only [ofReal_re, ofReal_im, zero_mul, sub_zero]
  exact mul_pos hnorm hcos

/-- Off the critical line, the protected central band satisfies the rational order-seventeen
sector certificate at every absolute-Euler squared coordinate. -/
theorem xiOrderSeventeenSectorRatio_of_offLine_inner
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    (hinner : ((q.1 : ℂ).re - 1 / 2) ^ 2 ≤ (9 / 50 : ℝ))
    {y : ℝ} (hy : 1 / 4 < y) :
    118 * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ 2 <
      ((q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2 + y) ^ 2 := by
  let u : ℝ := ((q.1 : ℂ).re - 1 / 2) ^ 2
  let v : ℝ := (q.1 : ℂ).im ^ 2
  let A : ℝ := v - u + y
  let B : ℝ := 2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im
  have hu : u ≤ 9 / 50 := by simpa only [u] using hinner
  have hv : 85 < v := by
    simpa only [v] using xiZeroCopy_offLine_eightyFive_lt_im_sq q hoff
  have hv0 : 0 < v := by linarith
  have hA : v < A := by
    dsimp only [A]
    nlinarith
  have hB : B ^ 2 = 4 * u * v := by
    dsimp only [B, u, v]
    ring
  have hBbound : 118 * B ^ 2 ≤ (2124 / 25 : ℝ) * v := by
    rw [hB]
    nlinarith
  have hheight : (2124 / 25 : ℝ) * v < v ^ 2 := by
    nlinarith
  have hAsq : v ^ 2 < A ^ 2 := by nlinarith
  change 118 * B ^ 2 < A ^ 2
  linarith

/-- Every Xi zero above squared height `118` satisfies the rational order-seventeen sector
certificate at every absolute-Euler squared coordinate. -/
theorem xiOrderSeventeenSectorRatio_of_oneHundredEighteen_le_im_sq
    (q : XiZeroCopy) (hhigh : 118 ≤ (q.1 : ℂ).im ^ 2)
    {y : ℝ} (hy : 1 / 4 < y) :
    118 * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ 2 <
      ((q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2 + y) ^ 2 := by
  let u : ℝ := ((q.1 : ℂ).re - 1 / 2) ^ 2
  let v : ℝ := (q.1 : ℂ).im ^ 2
  let A : ℝ := v - u + y
  let B : ℝ := 2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  have hu : u < 1 / 4 := by
    dsimp only [u]
    nlinarith [mul_pos hstrip.1 (sub_pos.mpr hstrip.2)]
  have hv : 118 ≤ v := by simpa only [v] using hhigh
  have hv0 : 0 < v := by linarith
  have hA : v < A := by
    dsimp only [A]
    nlinarith
  have hB : B ^ 2 = 4 * u * v := by
    dsimp only [B, u, v]
    ring
  have hBbound : 118 * B ^ 2 < 118 * v := by
    rw [hB]
    nlinarith
  have hheight : 118 * v ≤ v ^ 2 := by nlinarith
  have hAsq : v ^ 2 < A ^ 2 := by nlinarith
  change 118 * B ^ 2 < A ^ 2
  linarith

/-- Failure of the order-seventeen sector certificate at `y > 1/4` forces an off-critical Xi
zero into `9/50 < delta^2 < 1/4`, `85 < gamma^2 < 118`. -/
theorem xiOrderSeventeenSectorFailure_mem_edgeCorner
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    {y : ℝ} (hy : 1 / 4 < y)
    (hfail :
      ((q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2 + y) ^ 2 ≤
        118 * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ 2) :
    (9 / 50 : ℝ) < ((q.1 : ℂ).re - 1 / 2) ^ 2 ∧
      ((q.1 : ℂ).re - 1 / 2) ^ 2 < 1 / 4 ∧
      85 < (q.1 : ℂ).im ^ 2 ∧
      (q.1 : ℂ).im ^ 2 < 118 := by
  have hedge : (9 / 50 : ℝ) < ((q.1 : ℂ).re - 1 / 2) ^ 2 := by
    by_contra h
    have hsector := xiOrderSeventeenSectorRatio_of_offLine_inner q hoff
      (le_of_not_gt h) hy
    linarith
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  have hu : ((q.1 : ℂ).re - 1 / 2) ^ 2 < (1 / 4 : ℝ) := by
    nlinarith [mul_pos hstrip.1 (sub_pos.mpr hstrip.2)]
  have hvlow : 85 < (q.1 : ℂ).im ^ 2 :=
    xiZeroCopy_offLine_eightyFive_lt_im_sq q hoff
  have hvhigh : (q.1 : ℂ).im ^ 2 < 118 := by
    by_contra h
    have hsector := xiOrderSeventeenSectorRatio_of_oneHundredEighteen_le_im_sq q
      (le_of_not_gt h) hy
    linarith
  exact ⟨hedge, hu, hvlow, hvhigh⟩

/-- A nonpositive seventeenth reciprocal-power atom at `y > 1/4` must lie in the compact edge
corner. -/
theorem xiOrderSeventeenReciprocalPower_nonpos_mem_edgeCorner
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    {y : ℝ} (hy : 1 / 4 < y)
    (hnonpos :
      let A : ℝ := (q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2 + y
      let B : ℝ := 2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im
      ((((A : ℂ) - B * I)⁻¹) ^ 17).re ≤ 0) :
    (9 / 50 : ℝ) < ((q.1 : ℂ).re - 1 / 2) ^ 2 ∧
      ((q.1 : ℂ).re - 1 / 2) ^ 2 < 1 / 4 ∧
      85 < (q.1 : ℂ).im ^ 2 ∧
      (q.1 : ℂ).im ^ 2 < 118 := by
  let u : ℝ := ((q.1 : ℂ).re - 1 / 2) ^ 2
  let v : ℝ := (q.1 : ℂ).im ^ 2
  let A : ℝ := v - u + y
  let B : ℝ := 2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  have hu : u < 1 / 4 := by
    dsimp only [u]
    nlinarith [mul_pos hstrip.1 (sub_pos.mpr hstrip.2)]
  have hv0 : 0 ≤ v := by dsimp only [v]; positivity
  have hA : 0 < A := by
    dsimp only [A]
    nlinarith
  have hfail : A ^ 2 ≤ 118 * B ^ 2 := by
    by_contra h
    have hsector : 118 * B ^ 2 < A ^ 2 := lt_of_not_ge h
    have hpos := orderSeventeenReciprocalPower_re_pos_of_sectorRatio hA hsector
    change ((((A : ℂ) - B * I)⁻¹) ^ 17).re ≤ 0 at hnonpos
    linarith
  apply xiOrderSeventeenSectorFailure_mem_edgeCorner q hoff hy
  simpa only [A, B, u, v] using hfail

end

end RHTower
