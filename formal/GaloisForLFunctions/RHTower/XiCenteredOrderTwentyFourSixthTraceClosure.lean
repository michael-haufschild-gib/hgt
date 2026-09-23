import GaloisForLFunctions.RHTower.XiCenteredOrderTwentyFourCriticalLineCompetition
import GaloisForLFunctions.RHTower.PrimeArchThetaSixthTraceFiniteReduction

/-!
# Sixth-trace closure of centered order 24

The sharper sector parameter `N = 233` confines every possible order-24 obstruction to
`v < 467 / 2`.  On that annulus the existing positive sixth reciprocal trace has a four-copy
floor strictly above `3 / 10^(7 : ℕ)`.  Hence the source cap reduced to five first-atom rational
enclosures empties the annulus and forces positivity of centered source moment 23.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

private def orderTwentyFourSectorPolynomial (X Y : ℝ) : ℝ :=
  X ^ (12 : ℕ) - 276 * X ^ (11 : ℕ) * Y + 10626 * X ^ (10 : ℕ) * Y ^ (2 : ℕ) -
    134596 * X ^ (9 : ℕ) * Y ^ (3 : ℕ) + 735471 * X ^ (8 : ℕ) * Y ^ (4 : ℕ) -
    1961256 * X ^ (7 : ℕ) * Y ^ (5 : ℕ) + 2704156 * X ^ (6 : ℕ) * Y ^ (6 : ℕ) -
    1961256 * X ^ (5 : ℕ) * Y ^ (7 : ℕ) + 735471 * X ^ (4 : ℕ) * Y ^ (8 : ℕ) -
    134596 * X ^ (3 : ℕ) * Y ^ (9 : ℕ) + 10626 * X ^ (2 : ℕ) * Y ^ (10 : ℕ) -
    276 * X * Y ^ (11 : ℕ) + Y ^ (12 : ℕ)

/-- Exact Bernstein-at-the-sector-wall certificate.  Translating by `Z = X - 233Y`
turns the real-part polynomial into a polynomial with thirteen strictly positive coefficients. -/
private theorem orderTwentyFourSectorPolynomial_pos
    {X Y : ℝ} (hX : 0 < X) (hsector : 233 * Y < X) :
    0 < orderTwentyFourSectorPolynomial X Y := by
  let Z := X - 233 * Y
  have hZ : 0 < Z := by dsimp only [Z]; linarith
  have hid : (233 : ℝ) ^ (12 : ℕ) * orderTwentyFourSectorPolynomial X Y =
      20149829413061413960749056 * X ^ (12 : ℕ) +
      21096589149884652771069468672 * Z * X ^ (11 : ℕ) +
      4231407486389219840499886080 * Z ^ (2 : ℕ) * X ^ (10 : ℕ) +
      247585526518824259252422656 * Z ^ (3 : ℕ) * X ^ (9 : ℕ) +
      6029558284499559048294144 * Z ^ (4 : ℕ) * X ^ (8 : ℕ) +
      70550320207379249046528 * Z ^ (5 : ℕ) * X ^ (7 : ℕ) +
      423313162703301235456 * Z ^ (6 : ℕ) * X ^ (6 : ℕ) +
      1329553458199000320 * Z ^ (7 : ℕ) * X ^ (5 : ℕ) +
      2152353381420528 * Z ^ (8 : ℕ) * X ^ (4 : ℕ) +
      1696784950432 * Z ^ (9 : ℕ) * X ^ (3 : ℕ) +
      576167592 * Z ^ (10 : ℕ) * X ^ (2 : ℕ) + 64296 * Z ^ (11 : ℕ) * X + Z ^ (12 : ℕ) := by
    dsimp only [orderTwentyFourSectorPolynomial, Z]
    ring
  have hrhs : 0 <
      20149829413061413960749056 * X ^ (12 : ℕ) +
      21096589149884652771069468672 * Z * X ^ (11 : ℕ) +
      4231407486389219840499886080 * Z ^ (2 : ℕ) * X ^ (10 : ℕ) +
      247585526518824259252422656 * Z ^ (3 : ℕ) * X ^ (9 : ℕ) +
      6029558284499559048294144 * Z ^ (4 : ℕ) * X ^ (8 : ℕ) +
      70550320207379249046528 * Z ^ (5 : ℕ) * X ^ (7 : ℕ) +
      423313162703301235456 * Z ^ (6 : ℕ) * X ^ (6 : ℕ) +
      1329553458199000320 * Z ^ (7 : ℕ) * X ^ (5 : ℕ) +
      2152353381420528 * Z ^ (8 : ℕ) * X ^ (4 : ℕ) +
      1696784950432 * Z ^ (9 : ℕ) * X ^ (3 : ℕ) +
      576167592 * Z ^ (10 : ℕ) * X ^ (2 : ℕ) + 64296 * Z ^ (11 : ℕ) * X + Z ^ (12 : ℕ) := by
    positivity
  nlinarith [hid, pow_pos (by norm_num : (0 : ℝ) < 233) 12]

private theorem re_add_mul_I_pow_twentyFour (A B : ℝ) :
    (((A : ℂ) + B * I) ^ (24 : ℕ)).re =
      orderTwentyFourSectorPolynomial (A ^ (2 : ℕ)) (B ^ (2 : ℕ)) := by
  let z : ℂ := (A : ℂ) + B * I
  have hzre : z.re = A := by simp [z]
  have hzim : z.im = B := by simp [z]
  have h2re : (z ^ (2 : ℕ)).re = A ^ (2 : ℕ) - B ^ (2 : ℕ) := by
    rw [pow_two, Complex.mul_re, hzre, hzim]
    ring
  have h2im : (z ^ (2 : ℕ)).im = 2 * A * B := by
    rw [pow_two, Complex.mul_im, hzre, hzim]
    ring
  have h4re : (z ^ (4 : ℕ)).re = (A ^ (2 : ℕ) - B ^ (2 : ℕ)) ^ (2 : ℕ) - (2 * A * B) ^ (2 : ℕ) := by
    rw [show (4 : ℕ) = 2 + 2 by norm_num, pow_add, Complex.mul_re, h2re, h2im]
    ring
  have h4im : (z ^ (4 : ℕ)).im = 2 * (A ^ (2 : ℕ) - B ^ (2 : ℕ)) * (2 * A * B) := by
    rw [show (4 : ℕ) = 2 + 2 by norm_num, pow_add, Complex.mul_im, h2re, h2im]
    ring
  have h8re : (z ^ (8 : ℕ)).re =
      ((A ^ (2 : ℕ) - B ^ (2 : ℕ)) ^ (2 : ℕ) - (2 * A * B) ^ (2 : ℕ)) ^ (2 : ℕ) -
        (2 * (A ^ (2 : ℕ) - B ^ (2 : ℕ)) * (2 * A * B)) ^ (2 : ℕ) := by
    rw [show (8 : ℕ) = 4 + 4 by norm_num, pow_add, Complex.mul_re, h4re, h4im]
    ring
  have h8im : (z ^ (8 : ℕ)).im =
      2 * ((A ^ (2 : ℕ) - B ^ (2 : ℕ)) ^ (2 : ℕ) - (2 * A * B) ^ (2 : ℕ)) *
        (2 * (A ^ (2 : ℕ) - B ^ (2 : ℕ)) * (2 * A * B)) := by
    rw [show (8 : ℕ) = 4 + 4 by norm_num, pow_add, Complex.mul_im, h4re, h4im]
    ring
  have h16re : (z ^ (16 : ℕ)).re = (z ^ (8 : ℕ)).re ^ (2 : ℕ) - (z ^ (8 : ℕ)).im ^ (2 : ℕ) := by
    rw [show (16 : ℕ) = 8 + 8 by norm_num, pow_add, Complex.mul_re]
    ring
  have h16im : (z ^ (16 : ℕ)).im = 2 * (z ^ (8 : ℕ)).re * (z ^ (8 : ℕ)).im := by
    rw [show (16 : ℕ) = 8 + 8 by norm_num, pow_add, Complex.mul_im]
    ring
  change (z ^ (24 : ℕ)).re = _
  rw [show (24 : ℕ) = 16 + 8 by norm_num, pow_add, Complex.mul_re,
    h16re, h16im, h8re, h8im]
  dsimp only [orderTwentyFourSectorPolynomial]
  ring

theorem orderTwentyFourReciprocalPower_re_pos_of_sectorRatio_twoHundredThirtyThree
    {A B : ℝ} (hA : 0 < A) (hsector : 233 * B ^ (2 : ℕ) < A ^ (2 : ℕ)) :
    0 < ((((A : ℂ) - B * I)⁻¹) ^ (24 : ℕ)).re := by
  have hp : 0 < orderTwentyFourSectorPolynomial (A ^ (2 : ℕ)) (B ^ (2 : ℕ)) :=
    orderTwentyFourSectorPolynomial_pos (sq_pos_of_pos hA) hsector
  have hden : 0 < A ^ (2 : ℕ) + B ^ (2 : ℕ) := by positivity
  let zm : ℂ := (A : ℂ) - B * I
  let zp : ℂ := (A : ℂ) + B * I
  let D : ℝ := A ^ (2 : ℕ) + B ^ (2 : ℕ)
  have hne : zm ≠ 0 := by
    intro hz
    have hre := congrArg Complex.re hz
    simp [zm] at hre
    linarith
  have hprod : zm * (zp / (D : ℂ)) = 1 := by
    rw [div_eq_mul_inv, ← mul_assoc]
    have hm : zm * zp = (D : ℂ) := by
      calc
        zm * zp = (A : ℂ) ^ (2 : ℕ) - (B * I) ^ (2 : ℕ) := by
          dsimp only [zm, zp]
          ring
        _ = (D : ℂ) := by
          apply Complex.ext
          · norm_num [D, Complex.mul_re, Complex.mul_im, pow_two]
          · norm_num [D, Complex.mul_re, Complex.mul_im, pow_two]
    rw [hm, mul_inv_cancel₀]
    exact_mod_cast hden.ne'
  have hinv : (((A : ℂ) - B * I)⁻¹) =
      ((A : ℂ) + B * I) / ((A ^ (2 : ℕ) + B ^ (2 : ℕ) : ℝ) : ℂ) := by
    change zm⁻¹ = zp / (D : ℂ)
    apply mul_left_cancel₀ hne
    rw [mul_inv_cancel₀ hne]
    exact hprod.symm
  rw [hinv, div_pow]
  rw [show (((A ^ (2 : ℕ) + B ^ (2 : ℕ) : ℝ) : ℂ) ^ (24 : ℕ)) =
      (((A ^ (2 : ℕ) + B ^ (2 : ℕ)) ^ (24 : ℕ) : ℝ) : ℂ) by norm_num]
  have hrediv (z : ℂ) :
      (z / (((A ^ (2 : ℕ) + B ^ (2 : ℕ)) ^ (24 : ℕ) : ℝ) : ℂ)).re =
        z.re / (A ^ (2 : ℕ) + B ^ (2 : ℕ)) ^ (24 : ℕ) := by
    rw [Complex.div_re]
    simp only [ofReal_re, ofReal_im, mul_zero, add_zero, Complex.normSq_apply,
      add_zero]
    field_simp [ne_of_gt (pow_pos hden 24)]
    ring
  rw [hrediv, re_add_mul_I_pow_twentyFour]
  exact div_pos hp (by positivity)

theorem xiCenteredOrderTwentyFourSectorRatio233_of_offLine_inner
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    (hinner : ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) ≤ (2365 / 14944 : ℝ)) :
    233 * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ (2 : ℕ) <
      ((q.1 : ℂ).im ^ (2 : ℕ) - ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ)) ^ (2 : ℕ) := by
  have hv : (2365 / 16 : ℝ) ≤ (q.1 : ℂ).im ^ (2 : ℕ) :=
    le_of_not_gt fun hvlt => hoff (xiZeroCopy_re_eq_half_of_im_sq_lt_2365_over_16 q hvlt)
  simpa only [add_zero] using
    GaloisForLFunctions.HTGeometry.sector_ratio_of_corner (N := 233)
      (u₀ := 2365 / 14944) (v₀ := 2365 / 16) (y₀ := 0) (y := 0)
      (by norm_num) le_rfl hinner hv (by norm_num) (by norm_num)

theorem xiCenteredOrderTwentyFourSectorRatio233_of_fourHundredSixtySevenHalves_le_im_sq
    (q : XiZeroCopy) (hhigh : 467 / 2 ≤ (q.1 : ℂ).im ^ (2 : ℕ)) :
    233 * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ (2 : ℕ) <
      ((q.1 : ℂ).im ^ (2 : ℕ) - ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ)) ^ (2 : ℕ) := by
  simpa only [add_zero] using
    GaloisForLFunctions.HTGeometry.sector_ratio_of_corner (N := 233)
      (u₀ := 1 / 4) (v₀ := 467 / 2) (y₀ := 0) (y := 0)
      (by norm_num) le_rfl
      (xi_divisor_support_centered_re_sq_lt_quarter q.1).le hhigh
      (by norm_num) (by norm_num)

def XiCenteredOrderTwentyFourResidualAnnulus233 (q : XiZeroCopy) : Prop :=
  (q.1 : ℂ).re ≠ 1 / 2 ∧
    (2365 / 14944 : ℝ) < ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) ∧
      ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) < 1 / 4 ∧
        2365 / 16 ≤ (q.1 : ℂ).im ^ (2 : ℕ) ∧
          (q.1 : ℂ).im ^ (2 : ℕ) < 467 / 2

theorem xiCenteredOrderTwentyFourSectorFailure233_mem_residualAnnulus
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    (hfail :
      ((q.1 : ℂ).im ^ (2 : ℕ) - ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ)) ^ (2 : ℕ) ≤
        233 * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ (2 : ℕ)) :
    XiCenteredOrderTwentyFourResidualAnnulus233 q := by
  refine ⟨hoff, ?_, xi_divisor_support_centered_re_sq_lt_quarter q.1, ?_, ?_⟩
  · by_contra h
    exact absurd
      (xiCenteredOrderTwentyFourSectorRatio233_of_offLine_inner q hoff (not_lt.mp h))
      (not_lt.mpr hfail)
  · by_contra h
    exact hoff (xiZeroCopy_re_eq_half_of_im_sq_lt_2365_over_16 q (not_le.mp h))
  · by_contra h
    exact absurd
      (xiCenteredOrderTwentyFourSectorRatio233_of_fourHundredSixtySevenHalves_le_im_sq
        q (not_lt.mp h))
      (not_lt.mpr hfail)

theorem xiZeroCopyReciprocalSquare_pow_twentyFour_re_pos_of_not_mem_residualAnnulus233
    (q : XiZeroCopy) (hnot : ¬ XiCenteredOrderTwentyFourResidualAnnulus233 q) :
    0 < (xiZeroCopyReciprocalSquare q ^ (24 : ℕ)).re :=
  xiZeroCopyReciprocalSquare_pow_re_pos_of_window_empty q
    (fun _ _ hA h =>
      orderTwentyFourReciprocalPower_re_pos_of_sectorRatio_twoHundredThirtyThree hA h)
    (fun hoff hfail =>
      xiCenteredOrderTwentyFourSectorFailure233_mem_residualAnnulus q hoff hfail)
    hnot

/-- Every atom in the `N = 233` residual annulus costs more than `3 / 40,000,000` in
the sixth reciprocal trace. -/
theorem three_over_fortyMillion_lt_xiSixthReciprocalTraceAtom_orderTwentyFour
    (q : XiZeroCopy)
    (huLower : (0 : ℝ) < ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ))
    (huUpper : ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) < 1 / 4)
    (hvLower : 2365 / 16 ≤ (q.1 : ℂ).im ^ (2 : ℕ))
    (hvUpper : (q.1 : ℂ).im ^ (2 : ℕ) < 467 / 2) :
    (3 / 40000000 : ℝ) < (xiZeroCopyReciprocalSquare q ^ (3 : ℕ)).re := by
  let u : ℝ := ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ)
  let v : ℝ := (q.1 : ℂ).im ^ (2 : ℕ)
  let w : ℝ := u + v
  have hu0 : 0 < u := by simpa only [u] using huLower
  have huU : u < 1 / 4 := by simpa only [u] using huUpper
  have hv0 : 0 < v := by dsimp only [v]; linarith
  have hvL : 2365 / 16 ≤ v := by simpa only [v] using hvLower
  have hvU : v < 467 / 2 := by simpa only [v] using hvUpper
  have hw0 : 0 < w := by dsimp only [w]; positivity
  have hvw : v < w := by dsimp only [w]; linarith
  have hwU : w < 935 / 4 := by dsimp only [w]; linarith
  have hur : 591 * u < w := by dsimp only [w]; linarith
  have huv : 591 * (u * v) < w ^ (2 : ℕ) := by
    have hleft : 591 * u * v < w * v := mul_lt_mul_of_pos_right hur hv0
    have hright : w * v < w * w := mul_lt_mul_of_pos_left hvw hw0
    nlinarith
  have hfirst : (589 / 591 : ℝ) < (v - u) / w := by
    rw [lt_div_iff₀ hw0]
    dsimp only [w]
    nlinarith
  have hsecond : (575 / 591 : ℝ) <
      (v ^ (2 : ℕ) - 14 * u * v + u ^ (2 : ℕ)) / w ^ (2 : ℕ) := by
    rw [lt_div_iff₀ (sq_pos_of_pos hw0)]
    have hid : v ^ (2 : ℕ) - 14 * u * v + u ^ (2 : ℕ) = w ^ (2 : ℕ) - 16 * u * v := by
      dsimp only [w]
      ring
    rw [hid]
    nlinarith
  have hthird : (4 / 935 : ℝ) ^ (3 : ℕ) < 1 / w ^ (3 : ℕ) := by
    have hw3 : w ^ (3 : ℕ) < (935 / 4 : ℝ) ^ (3 : ℕ) :=
      pow_lt_pow_left₀ hwU hw0.le (by norm_num)
    rw [one_div]
    rw [show (4 / 935 : ℝ) ^ (3 : ℕ) = ((935 / 4 : ℝ) ^ (3 : ℕ))⁻¹ by norm_num]
    simpa only [one_div] using one_div_lt_one_div_of_lt (pow_pos hw0 3) hw3
  have hfirst0 : 0 < (v - u) / w :=
    (by norm_num : (0 : ℝ) < 589 / 591).trans hfirst
  have hsecond0 : 0 < (v ^ (2 : ℕ) - 14 * u * v + u ^ (2 : ℕ)) / w ^ (2 : ℕ) :=
    (by norm_num : (0 : ℝ) < 575 / 591).trans hsecond
  have hrat : (3 / 40000000 : ℝ) <
      (589 / 591 : ℝ) * (575 / 591 : ℝ) * (4 / 935 : ℝ) ^ (3 : ℕ) := by
    norm_num
  rw [xiZeroCopyReciprocalSquare_cube_re_formula]
  dsimp only [u, v, w] at *
  calc
    (3 / 40000000 : ℝ) <
        (589 / 591 : ℝ) * (575 / 591 : ℝ) * (4 / 935 : ℝ) ^ (3 : ℕ) := hrat
    _ < ((v - u) / w) * (575 / 591 : ℝ) * (4 / 935 : ℝ) ^ (3 : ℕ) := by
      gcongr
    _ < ((v - u) / w) *
        ((v ^ (2 : ℕ) - 14 * u * v + u ^ (2 : ℕ)) / w ^ (2 : ℕ)) * (4 / 935 : ℝ) ^ (3 : ℕ) := by
      gcongr
    _ < ((v - u) / w) *
        ((v ^ (2 : ℕ) - 14 * u * v + u ^ (2 : ℕ)) / w ^ (2 : ℕ)) * (1 / w ^ (3 : ℕ)) := by
      gcongr

theorem not_exists_orderTwentyFourResidualAnnulus233_of_sixthTrace_cap
    (hsource : normalizedPrimeArchMoment 2 < (3 / 10000000 : ℝ)) :
    ¬ ∃ q : XiZeroCopy, XiCenteredOrderTwentyFourResidualAnnulus233 q := by
  rintro ⟨q, hq⟩
  have hle := four_mul_xiSixthReciprocalTraceAtom_le_source_of_offLine q hq.1
  have hatom := three_over_fortyMillion_lt_xiSixthReciprocalTraceAtom_orderTwentyFour
    q (by linarith [hq.2.1]) hq.2.2.1 hq.2.2.2.1 hq.2.2.2.2
  nlinarith

theorem xiZeroCopyReciprocalSquare_pow_twentyFour_re_pos_of_sixthTrace_cap
    (hsource : normalizedPrimeArchMoment 2 < (3 / 10000000 : ℝ))
    (q : XiZeroCopy) :
    0 < (xiZeroCopyReciprocalSquare q ^ (24 : ℕ)).re :=
  xiZeroCopyReciprocalSquare_pow_twentyFour_re_pos_of_not_mem_residualAnnulus233 q
    (fun hq => not_exists_orderTwentyFourResidualAnnulus233_of_sixthTrace_cap hsource ⟨q, hq⟩)

theorem normalizedPrimeArchMoment_twentyThree_pos_of_sixthTrace_cap
    (hsource : normalizedPrimeArchMoment 2 < (3 / 10000000 : ℝ)) :
    0 < normalizedPrimeArchMoment 23 := by
  apply normalizedPrimeArchMoment_pos_of_atomwise_re_pos 23
  simpa using xiZeroCopyReciprocalSquare_pow_twentyFour_re_pos_of_sixthTrace_cap hsource

/-- Five finite first-atom enclosures close centered order 24. -/
theorem normalizedPrimeArchMoment_twentyThree_pos_of_firstAtom_bounds
    (ha0 : (0.4969488 : ℝ) < thetaCuspAtomRawEvenMoment 0 1)
    (ha1lower : (0.02297 : ℝ) < thetaCuspAtomRawEvenMoment 1 1)
    (ha1upper : thetaCuspAtomRawEvenMoment 1 1 < (0.0229718 : ℝ))
    (ha2 : (0.0029627 : ℝ) < thetaCuspAtomRawEvenMoment 2 1)
    (ha3 : thetaCuspAtomRawEvenMoment 3 1 < (0.00059935 : ℝ)) :
    0 < normalizedPrimeArchMoment 23 :=
  normalizedPrimeArchMoment_twentyThree_pos_of_sixthTrace_cap
    (normalizedPrimeArchMoment_two_lt_three_over_tenMillion_of_firstAtom_bounds
      ha0 ha1lower ha1upper ha2 ha3)

end

end RHTower
