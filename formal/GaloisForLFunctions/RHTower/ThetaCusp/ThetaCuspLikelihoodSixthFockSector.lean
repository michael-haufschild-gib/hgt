import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspLikelihoodHighCumulantCalibration

/-!
# Sixth theta likelihood score and graded Fock-sector completion

The literal sixth source score is positive on one-particle support. Its two-particle fusion is
controlled by a uniform binary comparison, while all higher negative-parity sectors form a
strictly subcritical geometric tail. Thus source orientation survives infinite logarithmic
completion at sixth order without Xi divisor or zero-location input.
-/

namespace RHTower

def thetaLikelihoodSixthScore (z : ℝ) : ℝ :=
  z ^ 6 - 15 * z ^ 5 + 65 * z ^ 4 - 90 * z ^ 3 + 31 * z ^ 2 - z

theorem one_thirtieth_mul_pow_six_le_thetaLikelihoodSixthScore
    {z : ℝ} (hz : (47 / 5 : ℝ) < z) :
    (1 / 30 : ℝ) * z ^ 6 ≤ thetaLikelihoodSixthScore z := by
  let y := z - 9
  have hy : (2 / 5 : ℝ) < y := by dsimp only [y]; linarith
  have hy0 : 0 ≤ y := by linarith
  have hy2 : (4 / 25 : ℝ) < y ^ 2 := by
    have hprod : 0 < (y - 2 / 5) * (y + 2 / 5) := by positivity
    nlinarith
  have hcore : 0 <
      (29951 / 2 : ℝ) * y ^ 2 + (93181 / 5 : ℝ) * y - 86517 / 10 := by
    nlinarith
  have hhigh : 0 ≤
      (29 / 30 : ℝ) * y ^ 6 + (186 / 5 : ℝ) * y ^ 5 +
        (1129 / 2 : ℝ) * y ^ 4 + 4194 * y ^ 3 := by positivity
  dsimp only [thetaLikelihoodSixthScore, y] at hcore hhigh ⊢
  nlinarith [show
    z ^ 6 - 15 * z ^ 5 + 65 * z ^ 4 - 90 * z ^ 3 + 31 * z ^ 2 - z -
          (1 / 30 : ℝ) * z ^ 6 =
      (29 / 30 : ℝ) * (z - 9) ^ 6 + (186 / 5 : ℝ) * (z - 9) ^ 5 +
        (1129 / 2 : ℝ) * (z - 9) ^ 4 + 4194 * (z - 9) ^ 3 +
        (29951 / 2 : ℝ) * (z - 9) ^ 2 +
        (93181 / 5 : ℝ) * (z - 9) - 86517 / 10 by ring]

theorem thetaLikelihoodSixthScore_le_pow_six
    {z : ℝ} (hz : (47 / 5 : ℝ) < z) :
    thetaLikelihoodSixthScore z ≤ z ^ 6 := by
  let y := z - 9
  have hy : 0 ≤ y := by dsimp only [y]; linarith
  have hpoly : 0 ≤
      15 * y ^ 4 + 475 * y ^ 3 + 5625 * y ^ 2 + 29534 * y + 58042 := by
    positivity
  dsimp only [thetaLikelihoodSixthScore, y] at hpoly ⊢
  nlinarith [show
    15 * z ^ 5 - 65 * z ^ 4 + 90 * z ^ 3 - 31 * z ^ 2 + z =
      z * (15 * (z - 9) ^ 4 + 475 * (z - 9) ^ 3 +
        5625 * (z - 9) ^ 2 + 29534 * (z - 9) + 58042) by ring]

theorem half_pow_six_le_thetaLikelihoodSixthScore
    {z : ℝ} (hz : 30 ≤ z) :
    (1 / 2 : ℝ) * z ^ 6 ≤ thetaLikelihoodSixthScore z := by
  have hz0 : 0 ≤ z := by linarith
  have hfirst : 0 ≤ z ^ 5 * (z / 2 - 15) :=
    mul_nonneg (pow_nonneg hz0 5) (by linarith)
  have htailCore : 0 ≤ 65 * z ^ 3 - 90 * z ^ 2 + 31 * z - 1 := by
    have h1 : 0 ≤ z ^ 2 * (65 * z - 90) :=
      mul_nonneg (sq_nonneg z) (by linarith)
    nlinarith [show z ^ 2 * (65 * z - 90) = 65 * z ^ 3 - 90 * z ^ 2 by ring]
  have htail : 0 ≤ z * (65 * z ^ 3 - 90 * z ^ 2 + 31 * z - 1) :=
    mul_nonneg hz0 htailCore
  dsimp only [thetaLikelihoodSixthScore]
  nlinarith [show
    z ^ 6 - 15 * z ^ 5 + 65 * z ^ 4 - 90 * z ^ 3 + 31 * z ^ 2 - z -
        (1 / 2 : ℝ) * z ^ 6 =
      z ^ 5 * (z / 2 - 15) +
        z * (65 * z ^ 3 - 90 * z ^ 2 + 31 * z - 1) by ring]

theorem thetaLikelihoodSixthScore_le_four_fifths_pow_six
    {z : ℝ} (hz : (94 / 5 : ℝ) < z) (hz60 : z ≤ 60) :
    thetaLikelihoodSixthScore z ≤ (4 / 5 : ℝ) * z ^ 6 := by
  have hz0 : 0 < z := by linarith
  by_cases hz22 : z ≤ 22
  · have hcoef : (53 / 5 : ℝ) ≤ 15 - z / 5 := by linarith
    have hfactor : 0 < (53 / 5 : ℝ) * z - 65 := by nlinarith
    have hmul : 0 < z * ((53 / 5 : ℝ) * z - 65) := mul_pos hz0 hfactor
    have hquad : 90 < (15 - z / 5) * z ^ 2 - 65 * z + 90 := by
      have hscale := mul_le_mul_of_nonneg_right hcoef (sq_nonneg z)
      nlinarith [show z * ((53 / 5 : ℝ) * z - 65) =
        (53 / 5 : ℝ) * z ^ 2 - 65 * z by ring]
    have htail : 0 < 90 * z ^ 2 - 31 * z + 1 := by nlinarith [sq_nonneg (z - 1)]
    have hmain : 0 <
        z ^ 2 * ((15 - z / 5) * z ^ 2 - 65 * z + 90) - 31 * z + 1 := by
      have hz2 : 1 < z ^ 2 := by nlinarith [sq_nonneg (z - 1)]
      nlinarith [mul_pos (sq_pos_of_pos hz0) (sub_pos.mpr hquad)]
    dsimp only [thetaLikelihoodSixthScore]
    nlinarith [show
      (4 / 5 : ℝ) * z ^ 6 -
          (z ^ 6 - 15 * z ^ 5 + 65 * z ^ 4 - 90 * z ^ 3 + 31 * z ^ 2 - z) =
        z * (z ^ 2 * ((15 - z / 5) * z ^ 2 - 65 * z + 90) -
          31 * z + 1) by ring]
  · have hz22' : 22 < z := lt_of_not_ge hz22
    have hcoef : 3 ≤ 15 - z / 5 := by linarith
    have hfirst : 0 < z ^ 4 * (3 * z - 65) :=
      mul_pos (pow_pos hz0 4) (by linarith)
    have htail : 0 < 90 * z ^ 2 - 31 * z + 1 := by nlinarith [sq_nonneg (z - 1)]
    have hmain : 0 <
        z ^ 4 * (15 - z / 5) - 65 * z ^ 3 + 90 * z ^ 2 - 31 * z + 1 := by
      have hscale := mul_le_mul_of_nonneg_right hcoef (pow_nonneg hz0.le 4)
      nlinarith [show z ^ 4 * (3 * z - 65) = 3 * z ^ 5 - 65 * z ^ 4 by ring]
    dsimp only [thetaLikelihoodSixthScore]
    nlinarith [show
      (4 / 5 : ℝ) * z ^ 6 -
          (z ^ 6 - 15 * z ^ 5 + 65 * z ^ 4 - 90 * z ^ 3 + 31 * z ^ 2 - z) =
        z * (z ^ 4 * (15 - z / 5) - 65 * z ^ 3 + 90 * z ^ 2 -
          31 * z + 1) by ring]

/-- Sharp binary fusion bound. The constant `384` is below the reciprocal source activity
threshold `399`; this strict gap is what lets the two-particle sector be absorbed. -/
theorem thetaLikelihoodSixthScore_add_le_384_mul
    {z w : ℝ} (hz : (47 / 5 : ℝ) < z) (hw : (47 / 5 : ℝ) < w) :
    thetaLikelihoodSixthScore (z + w) ≤
      384 * (thetaLikelihoodSixthScore z + thetaLikelihoodSixthScore w) := by
  let u := z - 47 / 5
  let v := w - 47 / 5
  have hu : 0 < u := by dsimp only [u]; linarith
  have hv : 0 < v := by dsimp only [v]; linarith
  have h2 := add_pow_le hu.le hv.le 2
  have h3 := add_pow_le hu.le hv.le 3
  have h4 := add_pow_le hu.le hv.le 4
  have h5 := add_pow_le hu.le hv.le 5
  have h6 := add_pow_le hu.le hv.le 6
  norm_num at h2 h3 h4 h5 h6
  have hp1 : 0 ≤ u + v := by positivity
  have hp2 : 0 ≤ u ^ 2 + v ^ 2 := by positivity
  have hp3 : 0 ≤ u ^ 3 + v ^ 3 := by positivity
  have hp4 : 0 ≤ u ^ 4 + v ^ 4 := by positivity
  have hp5 : 0 ≤ u ^ 5 + v ^ 5 := by positivity
  have hp6 : 0 ≤ u ^ 6 + v ^ 6 := by positivity
  rw [show z = u + 47 / 5 by dsimp only [u]; ring,
    show w = v + 47 / 5 by dsimp only [v]; ring]
  dsimp only [thetaLikelihoodSixthScore]
  rw [show
      (u + 47 / 5 + (v + 47 / 5)) ^ 6 -
            15 * (u + 47 / 5 + (v + 47 / 5)) ^ 5 +
            65 * (u + 47 / 5 + (v + 47 / 5)) ^ 4 -
            90 * (u + 47 / 5 + (v + 47 / 5)) ^ 3 +
            31 * (u + 47 / 5 + (v + 47 / 5)) ^ 2 -
            (u + 47 / 5 + (v + 47 / 5)) =
          (u + v) ^ 6 + 489 / 5 * (u + v) ^ 5 +
            19783 / 5 * (u + v) ^ 4 +
            2116886 / 25 * (u + v) ^ 3 +
            126236663 / 125 * (u + v) ^ 2 +
            19860375719 / 3125 * (u + v) +
            257140304006 / 15625 by ring,
    show
      384 *
        ((u + 47 / 5) ^ 6 - 15 * (u + 47 / 5) ^ 5 +
              65 * (u + 47 / 5) ^ 4 - 90 * (u + 47 / 5) ^ 3 +
              31 * (u + 47 / 5) ^ 2 - (u + 47 / 5) +
          ((v + 47 / 5) ^ 6 - 15 * (v + 47 / 5) ^ 5 +
              65 * (v + 47 / 5) ^ 4 - 90 * (v + 47 / 5) ^ 3 +
              31 * (v + 47 / 5) ^ 2 - (v + 47 / 5))) =
        384 * (u ^ 6 + v ^ 6) + 79488 / 5 * (u ^ 5 + v ^ 5) +
          1315968 / 5 * (u ^ 4 + v ^ 4) +
          54832128 / 25 * (u ^ 3 + v ^ 3) +
          1174950912 / 125 * (u ^ 2 + v ^ 2) +
          56948560128 / 3125 * (u + v) +
          293733257472 / 15625 by ring]
  linarith

/-- Coarser compatibility alias retained for downstream estimates. -/
theorem thetaLikelihoodSixthScore_add_le_768_mul
    {z w : ℝ} (hz : (47 / 5 : ℝ) < z) (hw : (47 / 5 : ℝ) < w) :
    thetaLikelihoodSixthScore (z + w) ≤
      768 * (thetaLikelihoodSixthScore z + thetaLikelihoodSixthScore w) := by
  have h := thetaLikelihoodSixthScore_add_le_384_mul hz hw
  have hz0 := one_thirtieth_mul_pow_six_le_thetaLikelihoodSixthScore hz
  have hw0 := one_thirtieth_mul_pow_six_le_thetaLikelihoodSixthScore hw
  have hnonneg : 0 ≤ thetaLikelihoodSixthScore z + thetaLikelihoodSixthScore w := by
    have hzpow : 0 ≤ (1 / 30 : ℝ) * z ^ 6 := by positivity
    have hwpow : 0 ≤ (1 / 30 : ℝ) * w ^ 6 := by positivity
    linarith
  nlinarith

/-- Sharp normalized tail calibration converted to unnormalized Fock activity. -/
theorem three_hundred_ninety_nine_mul_thetaCuspHigherLikelihoodSpectralResponse_lt_one
    {x : ℝ} (hx : 0 ≤ x) :
    399 * thetaCuspHigherLikelihoodSpectralResponse
      (thetaCuspLikelihoodCoordinate x) < 1 := by
  let B := thetaCuspLikelihoodCoordinate x
  let r := thetaCuspHigherLikelihoodSpectralResponse B
  let p := thetaCuspLikelihoodTailProbability B
  have hB : 0 < B := by simpa only [B] using thetaCuspLikelihoodCoordinate_pos hx
  have hr : 0 ≤ r := by
    dsimp only [r]
    rw [← thetaCuspHigherLikelihoodSpectralMoment_zero_eq_response hB]
    exact thetaCuspHigherLikelihoodSpectralMoment_nonneg 0
  have hp : 400 * p < 1 := by
    simpa only [B, p] using
      four_hundred_mul_thetaCuspLikelihoodTailProbability_coordinate_lt_one hx
  have hpEq : p = r / (1 + r) := by
    dsimp only [p, r]
    unfold thetaCuspLikelihoodTailProbability thetaCuspLikelihoodNormalizedMoment
      thetaCuspLikelihoodPartition
    rw [thetaCuspHigherLikelihoodSpectralMoment_zero_eq_response hB]
  have hden : 0 < 1 + r := by linarith
  rw [hpEq] at hp
  rw [show 400 * (r / (1 + r)) = (400 * r) / (1 + r) by ring] at hp
  have hraw := (div_lt_iff₀ hden).mp hp
  nlinarith

private theorem even_shift_pow_five_le_six_pow (m : ℕ) :
    (((2 * (m + 2) : ℕ) : ℝ) ^ 5) ≤
      (6 : ℝ) ^ (2 * (m + 2)) := by
  induction m with
  | zero => norm_num
  | succ m ih =>
      let k : ℕ := 2 * (m + 2)
      have hk : (4 : ℝ) ≤ k := by
        dsimp only [k]
        push_cast
        nlinarith [show (0 : ℝ) ≤ m by positivity]
      have hk0 : (0 : ℝ) ≤ k := by positivity
      have hstep : ((k : ℝ) + 2) ≤ (3 / 2 : ℝ) * k := by nlinarith
      have hpow := pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ k + 2) hstep 5
      have hcoeff : (3 / 2 : ℝ) ^ 5 < 36 := by norm_num
      have hnonneg : 0 ≤ (k : ℝ) ^ 5 := pow_nonneg hk0 5
      have hscaled : (((k : ℝ) + 2) ^ 5) ≤ 36 * (k : ℝ) ^ 5 := by
        calc
          ((k : ℝ) + 2) ^ 5 ≤ ((3 / 2 : ℝ) * k) ^ 5 := hpow
          _ = (3 / 2 : ℝ) ^ 5 * (k : ℝ) ^ 5 := by ring
          _ ≤ 36 * (k : ℝ) ^ 5 :=
            mul_le_mul_of_nonneg_right hcoeff.le hnonneg
      have hind : ((k : ℝ) ^ 5) ≤ (6 : ℝ) ^ k := by
        simpa only [k, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] using ih
      have hmul := mul_le_mul_of_nonneg_left hind (by norm_num : (0 : ℝ) ≤ 36)
      change ((((2 * (m + 1 + 2) : ℕ) : ℝ) ^ 5) ≤
        (6 : ℝ) ^ (2 * (m + 1 + 2)))
      rw [show 2 * (m + 1 + 2) = k + 2 by omega]
      push_cast
      calc
        ((k : ℝ) + 2) ^ 5 ≤ 36 * (k : ℝ) ^ 5 := hscaled
        _ ≤ 36 * (6 : ℝ) ^ k := hmul
        _ = (6 : ℝ) ^ (k + 2) := by rw [pow_add]; norm_num; ring

/-- Uniform bound for completed negative-parity sectors beyond two-particle level. -/
theorem summable_evenSixthSectorTail_and_tsum_le
    {r : ℝ} (hr0 : 0 ≤ r) (hr : 399 * r < 1) :
    Summable (fun m : ℕ =>
      (((2 * (m + 2) : ℕ) : ℝ) ^ 5) * r ^ (2 * (m + 2) - 1)) ∧
    (∑' m : ℕ, (((2 * (m + 2) : ℕ) : ℝ) ^ 5) *
        r ^ (2 * (m + 2) - 1)) ≤
      1296 * r ^ 3 * (1 - 36 * r ^ 2)⁻¹ := by
  have hr1 : r < 1 / 399 := by nlinarith
  have hq0 : 0 ≤ 36 * r ^ 2 := by positivity
  have hq1 : 36 * r ^ 2 < 1 := by
    have hrSq := pow_lt_pow_left₀ hr1 hr0 (by norm_num : 2 ≠ 0)
    nlinarith
  have hqNorm : ‖36 * r ^ 2‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hq0]
    exact hq1
  have hmajorSummable : Summable (fun m : ℕ =>
      1296 * r ^ 3 * (36 * r ^ 2) ^ m) :=
    (summable_geometric_of_norm_lt_one hqNorm).mul_left _
  have hmajor : ∀ m : ℕ,
      (((2 * (m + 2) : ℕ) : ℝ) ^ 5) * r ^ (2 * (m + 2) - 1) ≤
        1296 * r ^ 3 * (36 * r ^ 2) ^ m := by
    intro m
    have hpow := even_shift_pow_five_le_six_pow m
    have hrpow : 0 ≤ r ^ (2 * (m + 2) - 1) := pow_nonneg hr0 _
    calc
      (((2 * (m + 2) : ℕ) : ℝ) ^ 5) * r ^ (2 * (m + 2) - 1) ≤
          (6 : ℝ) ^ (2 * (m + 2)) * r ^ (2 * (m + 2) - 1) :=
        mul_le_mul_of_nonneg_right hpow hrpow
      _ = 1296 * r ^ 3 * (36 * r ^ 2) ^ m := by
        rw [show 2 * (m + 2) = 2 * m + 4 by omega,
          show 2 * m + 4 - 1 = 2 * m + 3 by omega]
        simp only [pow_add, pow_mul]
        ring
  have htermNonneg : ∀ m : ℕ, 0 ≤
      (((2 * (m + 2) : ℕ) : ℝ) ^ 5) * r ^ (2 * (m + 2) - 1) := by
    intro m
    positivity
  have hsummable := Summable.of_nonneg_of_le
    (fun m => htermNonneg m) hmajor hmajorSummable
  refine ⟨hsummable, ?_⟩
  calc
    (∑' m : ℕ, (((2 * (m + 2) : ℕ) : ℝ) ^ 5) *
        r ^ (2 * (m + 2) - 1)) ≤
        ∑' m : ℕ, 1296 * r ^ 3 * (36 * r ^ 2) ^ m :=
      Summable.tsum_le_tsum hmajor hsummable hmajorSummable
    _ = 1296 * r ^ 3 * (1 - 36 * r ^ 2)⁻¹ := by
      rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hqNorm]

/-- Two-particle loss plus every completed higher even sector remains strictly below the
one-particle sixth margin whenever source tail mass is below `1/399`. -/
theorem sixthEvenSectorCompletionBudget_lt_one
    {r : ℝ} (hr0 : 0 ≤ r) (hr : 399 * r < 1) :
    384 * r + 30 *
      (∑' m : ℕ, (((2 * (m + 2) : ℕ) : ℝ) ^ 5) *
        r ^ (2 * (m + 2) - 1)) < 1 := by
  rcases eq_or_lt_of_le hr0 with rfl | hrpos
  · have hzero : (fun m : ℕ =>
        (((2 * (m + 2) : ℕ) : ℝ) ^ 5) *
          (0 : ℝ) ^ (2 * (m + 2) - 1)) = (fun _ : ℕ => (0 : ℝ)) := by
      funext m
      rw [zero_pow (by omega), mul_zero]
    rw [hzero]
    simp
  have hr1 : r < 1 / 399 := by nlinarith
  have hrSq := pow_lt_pow_left₀ hr1 hr0 (by norm_num : 2 ≠ 0)
  have hq : 36 * r ^ 2 < 1 / 2 := by nlinarith
  have hden : 0 < 1 - 36 * r ^ 2 := by linarith
  have hinv : (1 - 36 * r ^ 2)⁻¹ < 2 := by
    rw [inv_eq_one_div]
    apply (one_div_lt hden (by norm_num)).2
    nlinarith
  have hrCube := pow_lt_pow_left₀ hr1 hr0 (by norm_num : 3 ≠ 0)
  have htail := (summable_evenSixthSectorTail_and_tsum_le hr0 hr).2
  have htail' :
      (∑' m : ℕ, (((2 * (m + 2) : ℕ) : ℝ) ^ 5) *
        r ^ (2 * (m + 2) - 1)) < 2592 * (1 / 399 : ℝ) ^ 3 := by
    have hpos : 0 ≤ 1296 * r ^ 3 := by positivity
    have hfirst := mul_lt_mul_of_pos_left hinv (by positivity : 0 < 1296 * r ^ 3)
    have hsecond := mul_lt_mul_of_pos_left hrCube (by norm_num : (0 : ℝ) < 2592)
    nlinarith
  nlinarith [show
    384 * (1 / 399 : ℝ) + 30 * (2592 * (1 / 399 : ℝ) ^ 3) < 1 by norm_num]

/-- Actual theta activity lies in strict sixth-order graded completion chamber. -/
theorem thetaCuspLikelihoodSixthEvenSectorCompletionBudget_lt_one
    {x : ℝ} (hx : 0 ≤ x) :
    384 * thetaCuspHigherLikelihoodSpectralResponse
        (thetaCuspLikelihoodCoordinate x) +
      30 * (∑' m : ℕ, (((2 * (m + 2) : ℕ) : ℝ) ^ 5) *
        thetaCuspHigherLikelihoodSpectralResponse
            (thetaCuspLikelihoodCoordinate x) ^ (2 * (m + 2) - 1)) < 1 := by
  let B := thetaCuspLikelihoodCoordinate x
  let r := thetaCuspHigherLikelihoodSpectralResponse B
  have hB : 0 < B := by simpa only [B] using thetaCuspLikelihoodCoordinate_pos hx
  have hr0 : 0 ≤ r := by
    dsimp only [r]
    rw [← thetaCuspHigherLikelihoodSpectralMoment_zero_eq_response hB]
    exact thetaCuspHigherLikelihoodSpectralMoment_nonneg 0
  have hr : 399 * r < 1 := by
    simpa only [B, r] using
      three_hundred_ninety_nine_mul_thetaCuspHigherLikelihoodSpectralResponse_lt_one hx
  simpa only [B, r] using sixthEvenSectorCompletionBudget_lt_one hr0 hr

/-- Source-defined odd supertrace weight: one-particle sixth margin after paying every completed
negative-parity sector. -/
noncomputable def thetaCuspLikelihoodSixthFockOddWeight (x : ℝ) : ℝ :=
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  let r := thetaCuspHigherLikelihoodSpectralResponse B
  let evenTail := ∑' m : ℕ, (((2 * (m + 2) : ℕ) : ℝ) ^ 5) *
    r ^ (2 * (m + 2) - 1)
  (1 / 30 : ℝ) * A ^ 6 * thetaCuspHigherLikelihoodSpectralMoment B 6 *
    (1 - (384 * r + 30 * evenTail))

/-- Graded sixth-order source weight survives infinite Fock completion with strict orientation. -/
theorem thetaCuspLikelihoodSixthFockOddWeight_pos
    {x : ℝ} (hx : 0 ≤ x) :
    0 < thetaCuspLikelihoodSixthFockOddWeight x := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  let r := thetaCuspHigherLikelihoodSpectralResponse B
  let evenTail := ∑' m : ℕ, (((2 * (m + 2) : ℕ) : ℝ) ^ 5) *
    r ^ (2 * (m + 2) - 1)
  have hB : 0 < B := by simpa only [B] using thetaCuspLikelihoodCoordinate_pos hx
  have hA : 0 < A := by
    dsimp only [A, thetaCuspSingleAtomReflectionScale]
    positivity
  have h1 : 0 < thetaCuspHigherLikelihoodSpectralMoment B 1 :=
    thetaCuspHigherLikelihoodSpectralMoment_one_pos hB
  have h12 := three_mul_thetaCuspHigherLikelihoodSpectralMoment_le_succ hB 1
  have h23 := three_mul_thetaCuspHigherLikelihoodSpectralMoment_le_succ hB 2
  have h34 := three_mul_thetaCuspHigherLikelihoodSpectralMoment_le_succ hB 3
  have h45 := three_mul_thetaCuspHigherLikelihoodSpectralMoment_le_succ hB 4
  have h56 := three_mul_thetaCuspHigherLikelihoodSpectralMoment_le_succ hB 5
  have h6 : 0 < thetaCuspHigherLikelihoodSpectralMoment B 6 := by nlinarith
  have hbudget : 384 * r + 30 * evenTail < 1 := by
    simpa only [B, r, evenTail] using
      thetaCuspLikelihoodSixthEvenSectorCompletionBudget_lt_one hx
  dsimp only [thetaCuspLikelihoodSixthFockOddWeight, A, B, r, evenTail]
  positivity

end RHTower
