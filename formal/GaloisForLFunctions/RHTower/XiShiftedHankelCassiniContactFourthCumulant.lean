import GaloisForLFunctions.RHTower.XiShiftedHankelCassiniThetaCumulantContact

/-!
# Route-U degree-one contact reduction to one fourth-cumulant wall

For the theta Esscher mean `A`, variance `V`, and higher cumulants `K₃,K₄`, put

`ε(t) = t V(t) / A(t)`.

On the degree-one flat face `N(t)=0`, the contact equation eliminates `K₃` exactly and the
outgoing flow factors as

`N'(t) = 3 A(t)^(2 : ℕ) / t * (1 - ε(t)) * (1 - 2 ε(t)^(2 : ℕ)) - t^(2 : ℕ) A(t) K₄(t)`.

Thus the first Route-U crossing obstruction is a fourth-cumulant inequality only on its
self-selected contact locus.  The unconditional first-zero height gap also forces
`ε(t) > 77/85` throughout `0 < t < 1`; hence the geometric factor
`(1 - ε)(1 - 2 ε^(2 : ℕ))` lies in its negative chamber at every possible contact.
-/

open Complex

namespace RHTower

noncomputable section

/-- Radial elasticity of the inward theta Esscher mean. -/
def thetaCuspCassiniContactElasticity (t : ℝ) : ℝ :=
  t * thetaCuspCassiniEsscherVariance t /
    thetaCuspCassiniEsscherMean t

/-- Exact shifted-moment coordinate of the contact elasticity. -/
theorem thetaCuspCassiniContactElasticity_eq_one_sub_momentRatio
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    thetaCuspCassiniContactElasticity t =
      1 - 2 * t ^ (2 : ℕ) * (xiShiftedReciprocalMoment (t ^ (2 : ℕ)) 1).re /
        xiShiftedCassiniResponse (t ^ (2 : ℕ)) := by
  have hresponse : xiShiftedCassiniResponse (t ^ (2 : ℕ)) ≠ 0 :=
    (xiShiftedCassiniResponse_pos (sq_pos_of_pos ht0)).ne'
  rw [thetaCuspCassiniContactElasticity,
    thetaCuspCassiniEsscherMean_eq ht0 ht1,
    thetaCuspCassiniEsscherVariance]
  field_simp [ht0.ne', hresponse]

/-- The endpoint-height gap controls the first two shifted moments uniformly over the open theta
strip.  This is the radial form of the `85`-to-`4` atomwise resolvent inequality. -/
theorem eightyFive_mul_y_mul_re_xiShiftedReciprocalMoment_one_lt_four_mul_zero
    {y : ℝ} (hy0 : 0 < y) (hy1 : y < 1) :
    85 * y * (xiShiftedReciprocalMoment y 1).re <
      4 * (xiShiftedReciprocalMoment y 0).re := by
  have hatom : ∀ q : XiZeroCopy,
      85 * y * (xiShiftedReciprocalSquare y q ^ (2 : ℕ)).re <
        4 * (xiShiftedReciprocalSquare y q).re := by
    intro q
    let A : ℝ := y + (xiSquaredNode q).re
    let B : ℝ := (xiSquaredNode q).im
    have hnode : 81 / 4 < (xiSquaredNode q).re := by
      rw [xiSquaredNode_re]
      have hv := xiZeroCopy_fortyOne_div_two_lt_im_sq q
      have hu := xi_divisor_support_centered_re_sq_lt_quarter q.1
      linarith
    have hA : 85 * y / 4 < A := by
      dsimp only [A]
      nlinarith
    have hA0 : 0 < A := by linarith
    have hden : 0 < A ^ (2 : ℕ) + B ^ (2 : ℕ) := by
      nlinarith [sq_pos_of_pos hA0, sq_nonneg B]
    have hcoord : (y : ℂ) + xiSquaredNode q =
        (A : ℂ) + (B : ℂ) * I := by
      apply Complex.ext <;> simp [A, B]
    rw [xiShiftedReciprocalSquare_eq_inv hy0.le]
    change 85 * y * ((((y : ℂ) + xiSquaredNode q)⁻¹ ^ (2 : ℕ)).re) <
      4 * (((y : ℂ) + xiSquaredNode q)⁻¹).re
    rw [hcoord, pow_two, Complex.mul_re, Complex.inv_re, Complex.inv_im,
      Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, mul_zero, sub_zero, mul_one, add_zero, zero_add]
    have hgap : 85 * y * A < 4 * (A ^ (2 : ℕ) + B ^ (2 : ℕ)) := by
      nlinarith [sq_nonneg B]
    field_simp
    nlinarith [hden, sq_nonneg (A ^ (2 : ℕ) + B ^ (2 : ℕ))]
  have hsum1C : Summable (fun q : XiZeroCopy =>
      xiShiftedReciprocalSquare y q ^ (0 + 1)) :=
    summable_xiShiftedReciprocalSquare_pow hy0.le 0
  have hsum2C : Summable (fun q : XiZeroCopy =>
      xiShiftedReciprocalSquare y q ^ (1 + 1)) :=
    summable_xiShiftedReciprocalSquare_pow hy0.le 1
  have hsum1 : Summable (fun q : XiZeroCopy =>
      4 * (xiShiftedReciprocalSquare y q).re) := by
    simpa using (Complex.reCLM.summable hsum1C).mul_left 4
  have hsum2 : Summable (fun q : XiZeroCopy =>
      85 * y * (xiShiftedReciprocalSquare y q ^ (2 : ℕ)).re) := by
    simpa [mul_assoc] using
      (Complex.reCLM.summable hsum2C).mul_left (85 * y)
  obtain ⟨q0⟩ := nonempty_xiZeroCopy
  have hlt := hsum2.tsum_lt_tsum (i := q0)
    (fun q => (hatom q).le) (hatom q0) hsum1
  change 85 * y * (∑' q : XiZeroCopy,
      xiShiftedReciprocalSquare y q ^ (1 + 1)).re <
    4 * (∑' q : XiZeroCopy,
      xiShiftedReciprocalSquare y q ^ (0 + 1)).re
  rw [Complex.re_tsum hsum2C, Complex.re_tsum hsum1C]
  simpa only [tsum_mul_left, zero_add, pow_one, mul_assoc] using hlt

/-- Variable-shift form of the adjacent second-to-third resolvent contraction. -/
theorem eightyFive_mul_y_mul_re_xiShiftedReciprocalSquare_cube_lt_four_mul_square
    {y : ℝ} (hy0 : 0 < y) (hy1 : y < 1) (q : XiZeroCopy) :
    85 * y * (xiShiftedReciprocalSquare y q ^ (3 : ℕ)).re <
      4 * (xiShiftedReciprocalSquare y q ^ (2 : ℕ)).re := by
  let A : ℝ := y + (xiSquaredNode q).re
  let B : ℝ := (xiSquaredNode q).im
  have hnode : 81 / 4 < (xiSquaredNode q).re := by
    rw [xiSquaredNode_re]
    have hv := xiZeroCopy_fortyOne_div_two_lt_im_sq q
    have hu := xi_divisor_support_centered_re_sq_lt_quarter q.1
    linarith
  have hA : 85 * y / 4 < A := by
    dsimp only [A]
    nlinarith
  have hA0 : 0 < A := by linarith
  have hden : 0 < A ^ (2 : ℕ) + B ^ (2 : ℕ) := by
    nlinarith [sq_pos_of_pos hA0, sq_nonneg B]
  have hcoord : (y : ℂ) + xiSquaredNode q =
      (A : ℂ) + (B : ℂ) * I := by
    apply Complex.ext <;> simp [A, B]
  have hre2pos : 0 < (xiShiftedReciprocalSquare y q ^ (2 : ℕ)).re :=
    re_xiShiftedReciprocalSquare_pow_pos_of_le_nineteen hy0 q (by norm_num)
  rw [xiShiftedReciprocalSquare_eq_inv hy0.le, hcoord] at hre2pos ⊢
  have hnormSq :
      Complex.normSq ((A : ℂ) + (B : ℂ) * I) = A ^ (2 : ℕ) + B ^ (2 : ℕ) := by
    norm_num [Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im]
    ring
  have hsqRe (z : ℂ) :
      (z ^ (2 : ℕ)).re = z.re ^ (2 : ℕ) - z.im ^ (2 : ℕ) := by
    rw [pow_two, Complex.mul_re]
    ring
  have hcubeRe (z : ℂ) :
      (z ^ (3 : ℕ)).re = z.re ^ (3 : ℕ) - 3 * z.re * z.im ^ (2 : ℕ) := by
    rw [show z ^ (3 : ℕ) = z * z * z by ring, Complex.mul_re,
      Complex.mul_re, Complex.mul_im]
    ring
  have hre2 :
      (((A : ℂ) + (B : ℂ) * I)⁻¹ ^ (2 : ℕ)).re =
        (A ^ (2 : ℕ) - B ^ (2 : ℕ)) / (A ^ (2 : ℕ) + B ^ (2 : ℕ)) ^ (2 : ℕ) := by
    rw [hsqRe, Complex.inv_re, Complex.inv_im, hnormSq]
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, mul_zero, sub_zero, mul_one, add_zero, zero_add]
    field_simp [hden.ne']
  have hre3 :
      (((A : ℂ) + (B : ℂ) * I)⁻¹ ^ (3 : ℕ)).re =
        A * (A ^ (2 : ℕ) - 3 * B ^ (2 : ℕ)) / (A ^ (2 : ℕ) + B ^ (2 : ℕ)) ^ (3 : ℕ) := by
    rw [hcubeRe, Complex.inv_re, Complex.inv_im, hnormSq]
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, mul_zero, sub_zero, mul_one, add_zero, zero_add]
    field_simp [hden.ne']
  rw [hre2] at hre2pos
  rw [hre3, hre2]
  have hnum2 : 0 < A ^ (2 : ℕ) - B ^ (2 : ℕ) := by
    rcases div_pos_iff.mp hre2pos with hpos | hneg
    · exact hpos.1
    · nlinarith [sq_nonneg (A ^ (2 : ℕ) + B ^ (2 : ℕ))]
  have hratio :
      A ^ (2 : ℕ) * (A ^ (2 : ℕ) - 3 * B ^ (2 : ℕ)) ≤
        (A ^ (2 : ℕ) - B ^ (2 : ℕ)) * (A ^ (2 : ℕ) + B ^ (2 : ℕ)) := by
    have hfactor : 0 ≤ 3 * A ^ (2 : ℕ) - B ^ (2 : ℕ) := by nlinarith
    have hprod : 0 ≤ B ^ (2 : ℕ) * (3 * A ^ (2 : ℕ) - B ^ (2 : ℕ)) :=
      mul_nonneg (sq_nonneg B) hfactor
    nlinarith
  have hscale : 85 * y < 4 * A := by linarith
  have hstep :
      85 * y * A * (A ^ (2 : ℕ) - 3 * B ^ (2 : ℕ)) <
        4 * (A ^ (2 : ℕ) - B ^ (2 : ℕ)) * (A ^ (2 : ℕ) + B ^ (2 : ℕ)) := by
    by_cases hnum3 : 0 ≤ A ^ (2 : ℕ) - 3 * B ^ (2 : ℕ)
    · rcases hnum3.eq_or_lt with hzero | hpos
      · rw [← hzero]
        have hright :
            0 < 4 * (A ^ (2 : ℕ) - B ^ (2 : ℕ)) * (A ^ (2 : ℕ) + B ^ (2 : ℕ)) := by
          positivity
        linarith
      · have hleft :=
          mul_lt_mul_of_pos_right hscale (mul_pos hA0 hpos)
        have hright :=
          mul_le_mul_of_nonneg_left hratio (by norm_num : (0 : ℝ) ≤ 4)
        nlinarith
    · have hneg : A ^ (2 : ℕ) - 3 * B ^ (2 : ℕ) < 0 := lt_of_not_ge hnum3
      have hright :
          0 < 4 * (A ^ (2 : ℕ) - B ^ (2 : ℕ)) * (A ^ (2 : ℕ) + B ^ (2 : ℕ)) := by
        positivity
      have hyNonneg : 0 ≤ 85 * y * A := by positivity
      nlinarith
  field_simp
  nlinarith [hstep, sq_pos_of_pos hden]

/-- Summed variable-shift contraction between the next adjacent reciprocal moments. -/
theorem eightyFive_mul_y_mul_re_xiShiftedReciprocalMoment_two_lt_four_mul_one
    {y : ℝ} (hy0 : 0 < y) (hy1 : y < 1) :
    85 * y * (xiShiftedReciprocalMoment y 2).re <
      4 * (xiShiftedReciprocalMoment y 1).re := by
  have hsum2C : Summable (fun q : XiZeroCopy =>
      xiShiftedReciprocalSquare y q ^ (1 + 1)) :=
    summable_xiShiftedReciprocalSquare_pow hy0.le 1
  have hsum3C : Summable (fun q : XiZeroCopy =>
      xiShiftedReciprocalSquare y q ^ (2 + 1)) :=
    summable_xiShiftedReciprocalSquare_pow hy0.le 2
  have hsum2 : Summable (fun q : XiZeroCopy =>
      4 * (xiShiftedReciprocalSquare y q ^ (2 : ℕ)).re) := by
    simpa using (Complex.reCLM.summable hsum2C).mul_left 4
  have hsum3 : Summable (fun q : XiZeroCopy =>
      85 * y * (xiShiftedReciprocalSquare y q ^ (3 : ℕ)).re) := by
    simpa [mul_assoc] using
      (Complex.reCLM.summable hsum3C).mul_left (85 * y)
  obtain ⟨q0⟩ := nonempty_xiZeroCopy
  have hlt := hsum3.tsum_lt_tsum (i := q0)
    (fun q =>
      (eightyFive_mul_y_mul_re_xiShiftedReciprocalSquare_cube_lt_four_mul_square
        hy0 hy1 q).le)
    (eightyFive_mul_y_mul_re_xiShiftedReciprocalSquare_cube_lt_four_mul_square
      hy0 hy1 q0) hsum2
  change 85 * y * (∑' q : XiZeroCopy,
      xiShiftedReciprocalSquare y q ^ (2 + 1)).re <
    4 * (∑' q : XiZeroCopy,
      xiShiftedReciprocalSquare y q ^ (1 + 1)).re
  rw [Complex.re_tsum hsum3C, Complex.re_tsum hsum2C]
  simpa only [tsum_mul_left, mul_assoc] using hlt

/-- Third theta Esscher cumulant is strictly negative throughout the open strip. -/
theorem thetaCuspCassiniEsscherThirdCumulant_neg
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    thetaCuspCassiniEsscherThirdCumulant t < 0 := by
  have hy0 : 0 < t ^ (2 : ℕ) := sq_pos_of_pos ht0
  have hy1 : t ^ (2 : ℕ) < 1 := by nlinarith
  have hm1 : 0 < (xiShiftedReciprocalMoment (t ^ (2 : ℕ)) 1).re :=
    re_xiShiftedReciprocalMoment_pos hy0 (by norm_num)
  have hcontract :=
    eightyFive_mul_y_mul_re_xiShiftedReciprocalMoment_two_lt_four_mul_one
      hy0 hy1
  have hcore :
      -6 * (xiShiftedReciprocalMoment (t ^ (2 : ℕ)) 1).re +
        8 * t ^ (2 : ℕ) * (xiShiftedReciprocalMoment (t ^ (2 : ℕ)) 2).re < 0 := by
    nlinarith
  rw [thetaCuspCassiniEsscherThirdCumulant]
  calc
    -6 * t * (xiShiftedReciprocalMoment (t ^ (2 : ℕ)) 1).re +
          8 * t ^ (3 : ℕ) * (xiShiftedReciprocalMoment (t ^ (2 : ℕ)) 2).re =
        t * (-6 * (xiShiftedReciprocalMoment (t ^ (2 : ℕ)) 1).re +
          8 * t ^ (2 : ℕ) * (xiShiftedReciprocalMoment (t ^ (2 : ℕ)) 2).re) := by ring
    _ < 0 := mul_neg_of_pos_of_neg ht0 hcore

/-- Fourth theta Esscher cumulant is also strictly negative throughout the open strip. -/
theorem thetaCuspCassiniEsscherFourthCumulant_neg
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    thetaCuspCassiniEsscherFourthCumulant t < 0 := by
  have hy0 : 0 < t ^ (2 : ℕ) := sq_pos_of_pos ht0
  have hy1 : t ^ (2 : ℕ) < 1 := by nlinarith
  have hm1 : 0 < (xiShiftedReciprocalMoment (t ^ (2 : ℕ)) 1).re :=
    re_xiShiftedReciprocalMoment_pos hy0 (by norm_num)
  have hm3 : 0 < (xiShiftedReciprocalMoment (t ^ (2 : ℕ)) 3).re :=
    re_xiShiftedReciprocalMoment_pos hy0 (by norm_num)
  have hcontract :=
    eightyFive_mul_y_mul_re_xiShiftedReciprocalMoment_two_lt_four_mul_one
      hy0 hy1
  have hcore :
      -6 * (xiShiftedReciprocalMoment (t ^ (2 : ℕ)) 1).re +
        48 * t ^ (2 : ℕ) * (xiShiftedReciprocalMoment (t ^ (2 : ℕ)) 2).re < 0 := by
    nlinarith
  rw [thetaCuspCassiniEsscherFourthCumulant]
  nlinarith [sq_nonneg (t ^ (2 : ℕ))]

/-- Every possible degree-one contact in the theta strip lies in the narrow elasticity chamber
`77/85 < ε < 1`. -/
theorem thetaCuspCassiniContactElasticity_mem_chamber
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    77 / 85 < thetaCuspCassiniContactElasticity t ∧
      thetaCuspCassiniContactElasticity t < 1 := by
  have hy0 : 0 < t ^ (2 : ℕ) := sq_pos_of_pos ht0
  have hy1 : t ^ (2 : ℕ) < 1 := by nlinarith
  have hresponse : 0 < xiShiftedCassiniResponse (t ^ (2 : ℕ)) :=
    xiShiftedCassiniResponse_pos hy0
  have hmoment : 0 < (xiShiftedReciprocalMoment (t ^ (2 : ℕ)) 1).re :=
    re_xiShiftedReciprocalMoment_pos hy0 (by norm_num)
  have hheight :=
    eightyFive_mul_y_mul_re_xiShiftedReciprocalMoment_one_lt_four_mul_zero
      hy0 hy1
  change 85 * t ^ (2 : ℕ) * (xiShiftedReciprocalMoment (t ^ (2 : ℕ)) 1).re <
    4 * xiShiftedCassiniResponse (t ^ (2 : ℕ)) at hheight
  rw [thetaCuspCassiniContactElasticity_eq_one_sub_momentRatio ht0 ht1]
  constructor
  · have hratio :
        2 * t ^ (2 : ℕ) * (xiShiftedReciprocalMoment (t ^ (2 : ℕ)) 1).re /
            xiShiftedCassiniResponse (t ^ (2 : ℕ)) < 8 / 85 := by
      rw [div_lt_iff₀ hresponse]
      nlinarith
    nlinarith
  · exact sub_lt_self _ (div_pos (mul_pos (mul_pos (by norm_num) hy0) hmoment)
      hresponse)

/-- Contact eliminates the third cumulant in favor of mean, variance elasticity, and radius. -/
theorem thetaCuspCassiniEsscherThirdCumulant_eq_of_contact
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hcontact : thetaCuspCassiniEulerContactNumerator t = 0) :
    thetaCuspCassiniEsscherThirdCumulant t =
      -(thetaCuspCassiniEsscherMean t / t ^ (2 : ℕ)) *
        (1 + thetaCuspCassiniContactElasticity t -
          2 * thetaCuspCassiniContactElasticity t ^ (2 : ℕ)) := by
  have hmean : thetaCuspCassiniEsscherMean t ≠ 0 := by
    rw [thetaCuspCassiniEsscherMean_eq ht0 ht1]
    exact mul_ne_zero ht0.ne'
      (xiShiftedCassiniResponse_pos (sq_pos_of_pos ht0)).ne'
  rw [thetaCuspCassiniEulerContactNumerator] at hcontact
  rw [thetaCuspCassiniContactElasticity]
  field_simp [ht0.ne', hmean]
  nlinarith

/-- Exact fourth-cumulant factorization of the contact flow. -/
theorem thetaCuspCassiniEulerContactFlow_eq_fourthCumulantWall_of_contact
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hcontact : thetaCuspCassiniEulerContactNumerator t = 0) :
    thetaCuspCassiniEulerContactFlow t =
      3 * thetaCuspCassiniEsscherMean t ^ (2 : ℕ) / t *
          (1 - thetaCuspCassiniContactElasticity t) *
          (1 - 2 * thetaCuspCassiniContactElasticity t ^ (2 : ℕ)) -
        t ^ (2 : ℕ) * thetaCuspCassiniEsscherMean t *
          thetaCuspCassiniEsscherFourthCumulant t := by
  have hmean : thetaCuspCassiniEsscherMean t ≠ 0 := by
    rw [thetaCuspCassiniEsscherMean_eq ht0 ht1]
    exact mul_ne_zero ht0.ne'
      (xiShiftedCassiniResponse_pos (sq_pos_of_pos ht0)).ne'
  have hthird :=
    thetaCuspCassiniEsscherThirdCumulant_eq_of_contact ht0 ht1 hcontact
  rw [thetaCuspCassiniEulerContactFlow, hthird,
    thetaCuspCassiniContactElasticity]
  field_simp [ht0.ne', hmean]
  ring

/-- A single fourth-cumulant cap on the contact locus excludes downward degree-one flow. -/
theorem thetaCuspCassiniEulerContactFlow_nonneg_of_fourthCumulantCap
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hcontact : thetaCuspCassiniEulerContactNumerator t = 0)
    (hcap :
      t ^ (3 : ℕ) * thetaCuspCassiniEsscherFourthCumulant t ≤
        3 * thetaCuspCassiniEsscherMean t *
          (1 - thetaCuspCassiniContactElasticity t) *
          (1 - 2 * thetaCuspCassiniContactElasticity t ^ (2 : ℕ))) :
    0 ≤ thetaCuspCassiniEulerContactFlow t := by
  have hmean : 0 < thetaCuspCassiniEsscherMean t := by
    rw [thetaCuspCassiniEsscherMean_eq ht0 ht1]
    exact mul_pos ht0 (xiShiftedCassiniResponse_pos (sq_pos_of_pos ht0))
  rw [thetaCuspCassiniEulerContactFlow_eq_fourthCumulantWall_of_contact
    ht0 ht1 hcontact]
  have hscaled := mul_le_mul_of_nonneg_left hcap (div_pos hmean ht0).le
  have heq :
      thetaCuspCassiniEsscherMean t / t *
          (t ^ (3 : ℕ) * thetaCuspCassiniEsscherFourthCumulant t) =
        t ^ (2 : ℕ) * thetaCuspCassiniEsscherMean t *
      thetaCuspCassiniEsscherFourthCumulant t := by
    field_simp [ht0.ne']
  have heq' :
      thetaCuspCassiniEsscherMean t / t *
          (3 * thetaCuspCassiniEsscherMean t *
            (1 - thetaCuspCassiniContactElasticity t) *
            (1 - 2 * thetaCuspCassiniContactElasticity t ^ (2 : ℕ))) =
        3 * thetaCuspCassiniEsscherMean t ^ (2 : ℕ) / t *
          (1 - thetaCuspCassiniContactElasticity t) *
          (1 - 2 * thetaCuspCassiniContactElasticity t ^ (2 : ℕ)) := by
    ring
  rw [heq, heq'] at hscaled
  exact sub_nonneg.mpr hscaled

/-- The geometric part of the fourth-cumulant wall is strictly negative throughout the theta
strip.  Any successful exclusion must therefore use a genuinely negative fourth cumulant, not
mere nonpositivity. -/
theorem thetaCuspCassiniContact_geometricFactor_neg
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    (1 - thetaCuspCassiniContactElasticity t) *
        (1 - 2 * thetaCuspCassiniContactElasticity t ^ (2 : ℕ)) < 0 := by
  have hchamber := thetaCuspCassiniContactElasticity_mem_chamber ht0 ht1
  have hupper : 0 < 1 - thetaCuspCassiniContactElasticity t := by
    linarith
  have hsecond : 1 - 2 * thetaCuspCassiniContactElasticity t ^ (2 : ℕ) < 0 := by
    have hproduct :
        0 < (thetaCuspCassiniContactElasticity t - 77 / 85) *
          (thetaCuspCassiniContactElasticity t + 77 / 85) := by
      exact mul_pos (sub_pos.mpr hchamber.1) (by nlinarith)
    nlinarith
  exact mul_neg_of_pos_of_neg hupper hsecond

end

end RHTower
