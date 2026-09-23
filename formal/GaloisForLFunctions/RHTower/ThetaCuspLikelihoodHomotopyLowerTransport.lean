import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodHomotopyCurvatureEnergy
import GaloisForLFunctions.RHTower.ThetaCuspFixedActionC5LikelihoodHomotopyCurvatureReduction

/-!
# Theta likelihood homotopy lower-transport closure

The new invariant
`J = F₃² F₄ + 2 F₂ F₄² - 2 F₂ F₃ F₅`
forces strict drift of `F₄² / ((-F₃)² F₂)`. Combined with strict convexity of
`F₂⁻¹ᐟ²`, it orients the reflected endpoint determinant and, through two exact
monotone-l’Hospital descents, proves positivity of the literal C5 homotopy
`velocityCenterTwo`.

RH chain: positive lower transport -> lower Bose balance -> positive `M'''` ->
convex likelihood lift -> direct-J -> reflection-odd rank-four/Ptolemy ->
CLG/TTF or Weil positivity -> RH.
-/

open MeasureTheory Set

namespace RHTower

noncomputable section

theorem fiveHalves_mul_variance_lt_thirdCumulant
    {x : ℝ} (hx : 0 ≤ x) :
    (5 / 2 : ℝ) *
        thetaCuspLikelihoodVariance (thetaCuspLikelihoodCoordinate x) <
      thetaCuspLikelihoodThirdCumulant (thetaCuspLikelihoodCoordinate x) := by
  let B := thetaCuspLikelihoodCoordinate x
  let m := thetaCuspLikelihoodMean B
  let e2 := thetaCuspLikelihoodNormalizedMoment B 2
  let e3 := thetaCuspLikelihoodNormalizedMoment B 3
  have hB : 0 < B := by
    simpa only [B] using thetaCuspLikelihoodCoordinate_pos hx
  have hm : 0 < m := by
    simpa only [m] using thetaCuspLikelihoodMean_pos hB
  have hmSmall : 12 * m < 1 := by
    simpa only [m, B] using twelve_mul_thetaCuspLikelihoodMean_coordinate_lt_one hx
  have he2 : 0 < e2 := by
    simpa only [e2] using thetaCuspLikelihoodNormalizedMoment_two_pos hB
  have he23 : 3 * e2 ≤ e3 := by
    simpa only [e2, e3] using
      three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hB 2
  unfold thetaCuspLikelihoodVariance thetaCuspLikelihoodThirdCumulant
  change (5 / 2 : ℝ) * (e2 - m ^ (2 : ℕ)) <
    e3 - 3 * m * e2 + 2 * m ^ (3 : ℕ)
  nlinarith [mul_pos (by linarith : 0 < 1 / 2 - 3 * m) he2,
    sq_nonneg m, mul_nonneg (sq_nonneg m) hm.le]

theorem four_mul_scale_mul_jetTwo_lt_neg_jetThree
    {x : ℝ} (hx : 0 ≤ x)
    (hscale : 6 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    4 * thetaCuspSingleAtomReflectionScale 1 x *
        thetaCuspLikelihoodSourceLogPartitionJetTwo x <
      -thetaCuspLikelihoodSourceLogPartitionJetThree x := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  let m := thetaCuspLikelihoodMean B
  let v := thetaCuspLikelihoodVariance B
  let k := thetaCuspLikelihoodThirdCumulant B
  have hA : 0 < A := by dsimp only [A] at hscale ⊢; linarith
  have hm : 0 < m := by
    simpa only [m, B] using thetaCuspLikelihoodMean_pos
      (thetaCuspLikelihoodCoordinate_pos hx)
  have hv : 0 < v := by
    simpa only [v, B] using thetaCuspLikelihoodVariance_pos
      (thetaCuspLikelihoodCoordinate_pos hx)
  have hk : (5 / 2 : ℝ) * v < k := by
    simpa only [v, k, B] using
      fiveHalves_mul_variance_lt_thirdCumulant hx
  have htail : 0 ≤ 4 * A ^ (2 : ℕ) * (A - 6) * v := by positivity
  unfold thetaCuspLikelihoodSourceLogPartitionJetTwo
    thetaCuspLikelihoodSourceLogPartitionJetThree
  dsimp only [A, B, m, v, k] at hscale hA hm hv hk htail ⊢
  nlinarith [mul_lt_mul_of_pos_left hk (pow_pos hA 3)]

/-- Positive magnitude of the ordinary third source score. -/
def thetaLikelihoodThirdScore (z : ℝ) : ℝ :=
  z ^ (3 : ℕ) - 3 * z ^ (2 : ℕ) + z

theorem thetaLikelihoodThirdScore_pos
    {z : ℝ} (hz : 18 ≤ z) :
    0 < thetaLikelihoodThirdScore z := by
  dsimp [thetaLikelihoodThirdScore]
  have hz0 : 0 < z := by linarith
  have hquad : 0 < z ^ (2 : ℕ) - 3 * z + 1 := by nlinarith [sq_nonneg (z - 3)]
  nlinarith

theorem four_mul_z_mul_thirdScore_le_five_mul_fourthScore
    {z : ℝ} (hz : 18 ≤ z) :
    4 * z * thetaLikelihoodThirdScore z ≤
      5 * thetaLikelihoodFourthScore z := by
  let y := z - 18
  have hy : 0 ≤ y := by dsimp only [y]; linarith
  have hy2 : 0 ≤ y ^ (2 : ℕ) := sq_nonneg y
  have hy3 : 0 ≤ y ^ (3 : ℕ) := by positivity
  have hy4 : 0 ≤ y ^ (4 : ℕ) := by positivity
  rw [show z = 18 + y by dsimp only [y]; ring]
  dsimp [thetaLikelihoodThirdScore, thetaLikelihoodFourthScore]
  ring_nf
  nlinarith

/-- Normalized positive magnitude of the one-particle ordinary third source jet. -/
def thetaCuspLikelihoodSourceOrdinaryNegativeJetThree (x : ℝ) : ℝ :=
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  8 * (A ^ (3 : ℕ) * thetaCuspLikelihoodNormalizedMoment B 3 -
    3 * A ^ (2 : ℕ) * thetaCuspLikelihoodNormalizedMoment B 2 +
    A * thetaCuspLikelihoodMean B)

private theorem integrable_thirdScore_tilted
    (A : ℝ) {B : ℝ} (hB : 0 < B) :
    Integrable (fun t : ℝ => thetaLikelihoodThirdScore (A * t))
      (thetaCuspHigherLikelihoodTiltedMeasure B) := by
  have h3 := (integrable_pow_thetaCuspHigherLikelihoodTiltedMeasure 3 hB).const_mul (A ^ (3 : ℕ))
  have h2 := (integrable_pow_thetaCuspHigherLikelihoodTiltedMeasure 2 hB).const_mul (3 * A ^ (2 : ℕ))
  have h1 := (integrable_pow_thetaCuspHigherLikelihoodTiltedMeasure 1 hB).const_mul A
  rw [show (fun t : ℝ => thetaLikelihoodThirdScore (A * t)) =
      ((fun t : ℝ => A ^ (3 : ℕ) * t ^ (3 : ℕ)) -
        (fun t : ℝ => (3 * A ^ (2 : ℕ)) * t ^ (2 : ℕ))) +
        (fun t : ℝ => A * t ^ (1 : ℕ)) by
    funext t
    dsimp [thetaLikelihoodThirdScore]
    ring]
  exact (h3.sub h2).add h1

private theorem integral_thirdScore_tilted_eq
    (A : ℝ) {B : ℝ} (hB : 0 < B) :
    (∫ t : ℝ, thetaLikelihoodThirdScore (A * t)
      ∂thetaCuspHigherLikelihoodTiltedMeasure B) =
      A ^ (3 : ℕ) * thetaCuspHigherLikelihoodSpectralMoment B 3 -
        3 * A ^ (2 : ℕ) * thetaCuspHigherLikelihoodSpectralMoment B 2 +
        A * thetaCuspHigherLikelihoodSpectralMoment B 1 := by
  have h3 := (integrable_pow_thetaCuspHigherLikelihoodTiltedMeasure 3 hB).const_mul (A ^ (3 : ℕ))
  have h2 := (integrable_pow_thetaCuspHigherLikelihoodTiltedMeasure 2 hB).const_mul (3 * A ^ (2 : ℕ))
  have h1 := (integrable_pow_thetaCuspHigherLikelihoodTiltedMeasure 1 hB).const_mul A
  rw [show (fun t : ℝ => thetaLikelihoodThirdScore (A * t)) =
      ((fun t : ℝ => A ^ (3 : ℕ) * t ^ (3 : ℕ)) -
        (fun t : ℝ => (3 * A ^ (2 : ℕ)) * t ^ (2 : ℕ))) +
        (fun t : ℝ => A * t ^ (1 : ℕ)) by
    funext t
    dsimp [thetaLikelihoodThirdScore]
    ring]
  rw [integral_add' (h3.sub h2) h1, integral_sub' h3 h2]
  simp only [integral_const_mul]
  rfl

private theorem integrable_fourthScore_tilted
    (A : ℝ) {B : ℝ} (hB : 0 < B) :
    Integrable (fun t : ℝ => thetaLikelihoodFourthScore (A * t))
      (thetaCuspHigherLikelihoodTiltedMeasure B) := by
  have h4 := (integrable_pow_thetaCuspHigherLikelihoodTiltedMeasure 4 hB).const_mul (A ^ (4 : ℕ))
  have h3 := (integrable_pow_thetaCuspHigherLikelihoodTiltedMeasure 3 hB).const_mul (6 * A ^ (3 : ℕ))
  have h2 := (integrable_pow_thetaCuspHigherLikelihoodTiltedMeasure 2 hB).const_mul (7 * A ^ (2 : ℕ))
  have h1 := (integrable_pow_thetaCuspHigherLikelihoodTiltedMeasure 1 hB).const_mul A
  rw [show (fun t : ℝ => thetaLikelihoodFourthScore (A * t)) =
      (((fun t : ℝ => A ^ (4 : ℕ) * t ^ (4 : ℕ)) -
        (fun t : ℝ => (6 * A ^ (3 : ℕ)) * t ^ (3 : ℕ))) +
        (fun t : ℝ => (7 * A ^ (2 : ℕ)) * t ^ (2 : ℕ))) -
        (fun t : ℝ => A * t ^ (1 : ℕ)) by
    funext t
    dsimp [thetaLikelihoodFourthScore]
    ring]
  exact ((h4.sub h3).add h2).sub h1

private theorem integral_fourthScore_tilted_eq
    (A : ℝ) {B : ℝ} (hB : 0 < B) :
    (∫ t : ℝ, thetaLikelihoodFourthScore (A * t)
      ∂thetaCuspHigherLikelihoodTiltedMeasure B) =
      A ^ (4 : ℕ) * thetaCuspHigherLikelihoodSpectralMoment B 4 -
        6 * A ^ (3 : ℕ) * thetaCuspHigherLikelihoodSpectralMoment B 3 +
        7 * A ^ (2 : ℕ) * thetaCuspHigherLikelihoodSpectralMoment B 2 -
        A * thetaCuspHigherLikelihoodSpectralMoment B 1 := by
  have h4 := (integrable_pow_thetaCuspHigherLikelihoodTiltedMeasure 4 hB).const_mul (A ^ (4 : ℕ))
  have h3 := (integrable_pow_thetaCuspHigherLikelihoodTiltedMeasure 3 hB).const_mul (6 * A ^ (3 : ℕ))
  have h2 := (integrable_pow_thetaCuspHigherLikelihoodTiltedMeasure 2 hB).const_mul (7 * A ^ (2 : ℕ))
  have h1 := (integrable_pow_thetaCuspHigherLikelihoodTiltedMeasure 1 hB).const_mul A
  rw [show (fun t : ℝ => thetaLikelihoodFourthScore (A * t)) =
      (((fun t : ℝ => A ^ (4 : ℕ) * t ^ (4 : ℕ)) -
        (fun t : ℝ => (6 * A ^ (3 : ℕ)) * t ^ (3 : ℕ))) +
        (fun t : ℝ => (7 * A ^ (2 : ℕ)) * t ^ (2 : ℕ))) -
        (fun t : ℝ => A * t ^ (1 : ℕ)) by
    funext t
    dsimp [thetaLikelihoodFourthScore]
    ring]
  rw [integral_sub' ((h4.sub h3).add h2) h1,
    integral_add' (h4.sub h3) h2, integral_sub' h4 h3]
  simp only [integral_const_mul]
  rfl

theorem four_mul_scale_mul_ordinaryNegJetThree_le_fiveSixths_ordinaryJetFour
    {x : ℝ} (hx : 0 ≤ x)
    (hscale : 6 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    4 * thetaCuspSingleAtomReflectionScale 1 x *
        thetaCuspLikelihoodSourceOrdinaryNegativeJetThree x ≤
      (5 / 6 : ℝ) * thetaCuspLikelihoodSourceOrdinaryJetFour x := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  let P := thetaCuspLikelihoodPartition B
  have hB : 0 < B := by simpa only [B] using thetaCuspLikelihoodCoordinate_pos hx
  have hA : 0 < A := by dsimp only [A] at hscale ⊢; linarith
  have hI3 := integrable_thirdScore_tilted A hB
  have hI4 := integrable_fourthScore_tilted A hB
  have hpoint : ∀ᵐ t ∂thetaCuspHigherLikelihoodTiltedMeasure B,
      2 * A * thetaLikelihoodThirdScore (A * t) ≤
        (5 / 6 : ℝ) * thetaLikelihoodFourthScore (A * t) := by
    filter_upwards [ae_three_le_thetaCuspHigherLikelihoodTiltedMeasure B] with t ht
    have ht0 : 0 < t := by linarith
    have hz : 18 ≤ A * t := by nlinarith
    have hp3 : 0 < thetaLikelihoodThirdScore (A * t) :=
      thetaLikelihoodThirdScore_pos hz
    have hAz : 3 * A ≤ A * t := by nlinarith
    have hfirst : 2 * A * thetaLikelihoodThirdScore (A * t) ≤
        (2 / 3 : ℝ) * (A * t) * thetaLikelihoodThirdScore (A * t) := by
      nlinarith
    have hsecond := four_mul_z_mul_thirdScore_le_five_mul_fourthScore hz
    exact hfirst.trans (by nlinarith)
  have hscaledI4 : Integrable
      (fun t : ℝ => (5 / 6 : ℝ) * thetaLikelihoodFourthScore (A * t))
      (thetaCuspHigherLikelihoodTiltedMeasure B) := hI4.const_mul _
  have hscaledI3 : Integrable
      (fun t : ℝ => 2 * A * thetaLikelihoodThirdScore (A * t))
      (thetaCuspHigherLikelihoodTiltedMeasure B) := hI3.const_mul _
  have hint := integral_mono_ae hscaledI3 hscaledI4 hpoint
  simp only [integral_const_mul] at hint
  rw [integral_thirdScore_tilted_eq A hB,
    integral_fourthScore_tilted_eq A hB] at hint
  have hP : 0 < P := by simpa only [P] using thetaCuspLikelihoodPartition_pos hB
  have hcoeff : 0 ≤ 16 / P := div_nonneg (by norm_num) hP.le
  have hscaled := mul_le_mul_of_nonneg_left hint hcoeff
  calc
    4 * thetaCuspSingleAtomReflectionScale 1 x *
          thetaCuspLikelihoodSourceOrdinaryNegativeJetThree x =
        (16 / P) * (2 * A *
          (A ^ (3 : ℕ) * thetaCuspHigherLikelihoodSpectralMoment B 3 -
            3 * A ^ (2 : ℕ) * thetaCuspHigherLikelihoodSpectralMoment B 2 +
            A * thetaCuspHigherLikelihoodSpectralMoment B 1)) := by
      dsimp only [thetaCuspLikelihoodSourceOrdinaryNegativeJetThree, A, B]
      unfold thetaCuspLikelihoodNormalizedMoment thetaCuspLikelihoodMean
      dsimp only [P]
      field_simp [hP.ne']
      ring
    _ ≤ (16 / P) * ((5 / 6 : ℝ) *
          (A ^ (4 : ℕ) * thetaCuspHigherLikelihoodSpectralMoment B 4 -
            6 * A ^ (3 : ℕ) * thetaCuspHigherLikelihoodSpectralMoment B 3 +
            7 * A ^ (2 : ℕ) * thetaCuspHigherLikelihoodSpectralMoment B 2 -
            A * thetaCuspHigherLikelihoodSpectralMoment B 1)) := hscaled
    _ = (5 / 6 : ℝ) * thetaCuspLikelihoodSourceOrdinaryJetFour x := by
      dsimp only [thetaCuspLikelihoodSourceOrdinaryJetFour, A, B]
      unfold thetaCuspLikelihoodNormalizedMoment thetaCuspLikelihoodMean
      dsimp only [P]
      field_simp [hP.ne']
      ring

theorem neg_jetThree_lt_ordinaryNegativeJetThree
    {x : ℝ} (hx : 0 ≤ x) :
    -thetaCuspLikelihoodSourceLogPartitionJetThree x <
      thetaCuspLikelihoodSourceOrdinaryNegativeJetThree x := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  let m := thetaCuspLikelihoodMean B
  let e2 := thetaCuspLikelihoodNormalizedMoment B 2
  let e3 := thetaCuspLikelihoodNormalizedMoment B 3
  have hA : 0 < A := by
    have h := three_lt_thetaCuspSingleAtomReflectionScale (n := 1) (by norm_num) hx
    simpa only [A] using h.trans' (by norm_num)
  have hm : 0 < m := by
    simpa only [m, B] using thetaCuspLikelihoodMean_pos
      (thetaCuspLikelihoodCoordinate_pos hx)
  have hF2 := thetaCuspLikelihoodSourceLogPartitionJetTwo_pos hx
  have hgap : 0 < A * e2 - A * m ^ (2 : ℕ) - m := by
    unfold thetaCuspLikelihoodSourceLogPartitionJetTwo at hF2
    unfold thetaCuspLikelihoodVariance at hF2
    change 0 < 4 * A ^ (2 : ℕ) * (e2 - m ^ (2 : ℕ)) - 4 * A * m at hF2
    rw [show 4 * A ^ (2 : ℕ) * (e2 - m ^ (2 : ℕ)) - 4 * A * m =
      (4 * A) * (A * e2 - A * m ^ (2 : ℕ) - m) by ring] at hF2
    rcases (mul_pos_iff.mp hF2) with h | h
    · exact h.2
    · exact False.elim ((not_lt_of_ge (mul_nonneg (by norm_num) hA.le)) h.1)
  have hbracket : 0 < 3 * A * e2 - 2 * A * m ^ (2 : ℕ) - 3 * m := by
    nlinarith [mul_nonneg hA.le (sq_nonneg m)]
  unfold thetaCuspLikelihoodSourceLogPartitionJetThree
    thetaCuspLikelihoodThirdCumulant thetaCuspLikelihoodVariance
  dsimp only [thetaCuspLikelihoodSourceOrdinaryNegativeJetThree,
    A, B, m, e2, e3]
  change -(-8 * A ^ (3 : ℕ) * (e3 - 3 * m * e2 + 2 * m ^ (3 : ℕ)) +
      24 * A ^ (2 : ℕ) * (e2 - m ^ (2 : ℕ)) - 8 * A * m) <
    8 * (A ^ (3 : ℕ) * e3 - 3 * A ^ (2 : ℕ) * e2 + A * m)
  nlinarith [mul_pos (mul_pos (pow_pos hA 2) hm) hbracket]

theorem four_mul_scale_mul_neg_jetThree_lt_jetFour
    {x : ℝ} (hx : 0 ≤ x)
    (hscale : 6 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    4 * thetaCuspSingleAtomReflectionScale 1 x *
        (-thetaCuspLikelihoodSourceLogPartitionJetThree x) <
      thetaCuspLikelihoodSourceLogPartitionJetFour x := by
  have hA : 0 < thetaCuspSingleAtomReflectionScale 1 x := by linarith
  have hlogOrd := neg_jetThree_lt_ordinaryNegativeJetThree hx
  have hmul := mul_lt_mul_of_pos_left hlogOrd
    (show 0 < 4 * thetaCuspSingleAtomReflectionScale 1 x by positivity)
  have hord :=
    four_mul_scale_mul_ordinaryNegJetThree_le_fiveSixths_ordinaryJetFour
      hx hscale
  have halpha : 0 < -thetaCuspLikelihoodSourceLogPartitionJetThree x :=
    neg_pos.mpr (thetaCuspLikelihoodSourceLogPartitionJetThree_neg hx)
  have hord3Pos : 0 < thetaCuspLikelihoodSourceOrdinaryNegativeJetThree x :=
    halpha.trans hlogOrd
  have hleftPos : 0 < 4 * thetaCuspSingleAtomReflectionScale 1 x *
      thetaCuspLikelihoodSourceOrdinaryNegativeJetThree x := by positivity
  have hrightPos : 0 < (5 / 6 : ℝ) * thetaCuspLikelihoodSourceOrdinaryJetFour x :=
    hleftPos.trans_le hord
  have hordPos : 0 < thetaCuspLikelihoodSourceOrdinaryJetFour x := by nlinarith
  have hfiveNineteen :
      (5 / 6 : ℝ) * thetaCuspLikelihoodSourceOrdinaryJetFour x <
        (19 / 20 : ℝ) * thetaCuspLikelihoodSourceOrdinaryJetFour x := by
    nlinarith
  have hretain :=
    nineteenTwentieths_mul_ordinary_lt_thetaCuspLikelihoodSourceLogPartitionJetFour hx
  exact (hmul.trans_le hord).trans (hfiveNineteen.trans hretain)

/-- Next projective derivative selected by the reflected lower transport. -/
def thetaCuspLikelihoodProjectiveTransportInvariant (x : ℝ) : ℝ :=
  thetaCuspLikelihoodSourceLogPartitionJetThree x ^ (2 : ℕ) *
      thetaCuspLikelihoodSourceLogPartitionJetFour x +
    2 * thetaCuspLikelihoodSourceLogPartitionJetTwo x *
      thetaCuspLikelihoodSourceLogPartitionJetFour x ^ (2 : ℕ) -
    2 * thetaCuspLikelihoodSourceLogPartitionJetTwo x *
      thetaCuspLikelihoodSourceLogPartitionJetThree x *
      thetaCuspLikelihoodSourceLogPartitionJetFive x

theorem projectiveTransportInvariant_pos
    {x : ℝ} (hx : 0 ≤ x)
    (hscale : 6 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    0 < thetaCuspLikelihoodProjectiveTransportInvariant x := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let h := thetaCuspLikelihoodSourceLogPartitionJetTwo x
  let α := -thetaCuspLikelihoodSourceLogPartitionJetThree x
  let C := thetaCuspLikelihoodSourceLogPartitionJetFour x
  let γ := -thetaCuspLikelihoodSourceLogPartitionJetFive x
  have hA : 0 < A := by dsimp only [A] at hscale ⊢; linarith
  have hh : 0 < h := by
    simpa only [h] using thetaCuspLikelihoodSourceLogPartitionJetTwo_pos hx
  have hα : 0 < α := by
    simpa only [α] using neg_pos.mpr
      (thetaCuspLikelihoodSourceLogPartitionJetThree_neg hx)
  have hC : 0 < C := by
    simpa only [C] using thetaCuspLikelihoodSourceLogPartitionJetFour_pos hx
  have hγ : 0 < γ := by
    simpa only [γ] using neg_pos.mpr
      (thetaCuspLikelihoodSourceLogPartitionJetFive_neg hx)
  have hlowTwo : 4 * A * h < α := by
    simpa only [A, h, α] using
      four_mul_scale_mul_jetTwo_lt_neg_jetThree hx hscale
  have hlowFour : 4 * A * α < C := by
    simpa only [A, α, C] using
      four_mul_scale_mul_neg_jetThree_lt_jetFour hx hscale
  have huppFive : γ < 6 * A * C := by
    simpa only [A, C, γ] using
      neg_thetaCuspLikelihoodSourceLogPartitionJetFive_lt_six_mul_scale_mul_jetFour
        hx hscale
  have hmulLow : 8 * A * h * α * C < 2 * h * C ^ (2 : ℕ) := by
    nlinarith [mul_lt_mul_of_pos_left hlowFour
      (mul_pos (mul_pos (show 0 < (2 : ℝ) by norm_num) hh) hC)]
  have hmulUpp : 2 * h * α * γ < 12 * A * h * α * C := by
    nlinarith [mul_lt_mul_of_pos_left huppFive
      (mul_pos (mul_pos (show 0 < (2 : ℝ) by norm_num) hh) hα)]
  have hcore : 0 < α ^ (2 : ℕ) * C - 4 * A * h * α * C := by
    have hmul := mul_lt_mul_of_pos_right hlowTwo (mul_pos hα hC)
    nlinarith
  dsimp only [thetaCuspLikelihoodProjectiveTransportInvariant,
    A, h, α, C, γ] at *
  nlinarith

/-- Squared projective curvature ratio whose drift is the new invariant. -/
def thetaCuspLikelihoodFourthThirdRootRatio (x : ℝ) : ℝ :=
  thetaCuspLikelihoodSourceLogPartitionJetFour x ^ (2 : ℕ) /
    ((-thetaCuspLikelihoodSourceLogPartitionJetThree x) ^ (2 : ℕ) *
      thetaCuspLikelihoodSourceLogPartitionJetTwo x)

theorem hasDerivAt_fourthThirdRootRatio
    {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt thetaCuspLikelihoodFourthThirdRootRatio
      ((thetaCuspLikelihoodSourceLogPartitionJetFour x *
          (-thetaCuspLikelihoodSourceLogPartitionJetThree x) *
          thetaCuspLikelihoodProjectiveTransportInvariant x) /
        (((-thetaCuspLikelihoodSourceLogPartitionJetThree x) ^ (2 : ℕ) *
          thetaCuspLikelihoodSourceLogPartitionJetTwo x) ^ (2 : ℕ))) x := by
  let h := thetaCuspLikelihoodSourceLogPartitionJetTwo
  let α : ℝ → ℝ := fun y => -thetaCuspLikelihoodSourceLogPartitionJetThree y
  let C := thetaCuspLikelihoodSourceLogPartitionJetFour
  have hB : 0 < thetaCuspLikelihoodCoordinate x :=
    thetaCuspLikelihoodCoordinate_pos hx
  have hh : HasDerivAt h (-α x) x := by
    simpa only [h, α, neg_neg] using
      hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetTwo hB
  have hα : HasDerivAt α (-C x) x := by
    have hraw :=
      (hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetThree hB).neg
    exact hraw.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _ => rfl)
  have hC : HasDerivAt C
      (thetaCuspLikelihoodSourceLogPartitionJetFive x) x := by
    simpa only [C] using hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetFour hB
  have hhPos : 0 < h x := by
    simpa only [h] using thetaCuspLikelihoodSourceLogPartitionJetTwo_pos hx
  have hαPos : 0 < α x := by
    simpa only [α] using neg_pos.mpr
      (thetaCuspLikelihoodSourceLogPartitionJetThree_neg hx)
  have hden : α x ^ (2 : ℕ) * h x ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 hαPos.ne') hhPos.ne'
  have hquot := (hC.pow 2).div ((hα.pow 2).mul hh) hden
  change HasDerivAt (C ^ (2 : ℕ) / (α ^ (2 : ℕ) * h)) _ x
  refine hquot.congr_deriv ?_
  simp only [Pi.pow_apply, Pi.mul_apply]
  dsimp only [h, α, C, thetaCuspLikelihoodProjectiveTransportInvariant]
  rw [div_eq_div_iff (pow_ne_zero 2 hden) (pow_ne_zero 2 hden)]
  ring

private theorem scale_mono
    {x y : ℝ} (hxy : x ≤ y) :
    thetaCuspSingleAtomReflectionScale 1 x ≤
      thetaCuspSingleAtomReflectionScale 1 y := by
  unfold thetaCuspSingleAtomReflectionScale
  norm_num
  exact mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (by linarith)) Real.pi_pos.le

theorem deriv_fourthThirdRootRatio_pos
    {x : ℝ} (hx : 0 ≤ x)
    (hscale : 6 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    0 < deriv thetaCuspLikelihoodFourthThirdRootRatio x := by
  rw [(hasDerivAt_fourthThirdRootRatio hx).deriv]
  exact div_pos
    (mul_pos
      (mul_pos
        (thetaCuspLikelihoodSourceLogPartitionJetFour_pos hx)
        (neg_pos.mpr (thetaCuspLikelihoodSourceLogPartitionJetThree_neg hx)))
      (projectiveTransportInvariant_pos hx hscale))
    (pow_pos
      (mul_pos
        (pow_pos (neg_pos.mpr
          (thetaCuspLikelihoodSourceLogPartitionJetThree_neg hx)) 2)
        (thetaCuspLikelihoodSourceLogPartitionJetTwo_pos hx)) 2)

theorem strictMonoOn_fourthThirdRootRatio_of_scale
    {x₀ : ℝ} (hx₀ : 0 ≤ x₀)
    (hscale₀ : 6 ≤ thetaCuspSingleAtomReflectionScale 1 x₀) :
    StrictMonoOn thetaCuspLikelihoodFourthThirdRootRatio (Set.Ici x₀) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici x₀)
  · intro x hx
    exact (hasDerivAt_fourthThirdRootRatio
      (hx₀.trans hx)).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    have hx0 : 0 ≤ x := hx₀.trans hx.le
    exact deriv_fourthThirdRootRatio_pos hx0
      (hscale₀.trans (scale_mono hx.le))

/-- Reciprocal square root of likelihood curvature. -/
def thetaCuspLikelihoodInverseRoot (x : ℝ) : ℝ :=
  (Real.sqrt (thetaCuspLikelihoodSourceLogPartitionJetTwo x))⁻¹

/-- Its positive source slope. -/
def thetaCuspLikelihoodInverseRootSlope (x : ℝ) : ℝ :=
  (-thetaCuspLikelihoodSourceLogPartitionJetThree x) /
    (2 * thetaCuspLikelihoodSourceLogPartitionJetTwo x *
      Real.sqrt (thetaCuspLikelihoodSourceLogPartitionJetTwo x))

theorem hasDerivAt_inverseRoot
    {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt thetaCuspLikelihoodInverseRoot
      (thetaCuspLikelihoodInverseRootSlope x) x := by
  let h := thetaCuspLikelihoodSourceLogPartitionJetTwo
  have hB := thetaCuspLikelihoodCoordinate_pos hx
  have hh := hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetTwo hB
  have hhPos : 0 < h x := by
    simpa only [h] using thetaCuspLikelihoodSourceLogPartitionJetTwo_pos hx
  have hs := (Real.hasDerivAt_sqrt hhPos.ne').comp x hh
  have hsne : Real.sqrt (h x) ≠ 0 := (Real.sqrt_pos.mpr hhPos).ne'
  have hi := hs.inv hsne
  change HasDerivAt (fun y => (Real.sqrt (h y))⁻¹) _ x
  refine hi.congr_deriv ?_
  simp only [Function.comp_apply]
  change -(1 / (2 * Real.sqrt (h x)) *
      thetaCuspLikelihoodSourceLogPartitionJetThree x) /
        Real.sqrt (h x) ^ (2 : ℕ) =
    (-thetaCuspLikelihoodSourceLogPartitionJetThree x) /
      (2 * h x * Real.sqrt (h x))
  rw [Real.sq_sqrt hhPos.le]
  field_simp [hhPos.ne', hsne]

theorem hasDerivAt_inverseRootSlope
    {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt thetaCuspLikelihoodInverseRootSlope
      (thetaCuspLikelihoodHomotopyCurvatureEnergy x /
        (4 * thetaCuspLikelihoodSourceLogPartitionJetTwo x ^ (2 : ℕ) *
          Real.sqrt (thetaCuspLikelihoodSourceLogPartitionJetTwo x))) x := by
  let h := thetaCuspLikelihoodSourceLogPartitionJetTwo
  let α : ℝ → ℝ := fun y => -thetaCuspLikelihoodSourceLogPartitionJetThree y
  have hB := thetaCuspLikelihoodCoordinate_pos hx
  have hh : HasDerivAt h (-α x) x := by
    simpa only [h, α, neg_neg] using
      hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetTwo hB
  have hα : HasDerivAt α
      (-thetaCuspLikelihoodSourceLogPartitionJetFour x) x := by
    have hraw :=
      (hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetThree hB).neg
    exact hraw.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _ => rfl)
  have hhPos : 0 < h x := by
    simpa only [h] using thetaCuspLikelihoodSourceLogPartitionJetTwo_pos hx
  have hs : HasDerivAt ((fun z : ℝ => Real.sqrt z) ∘ h)
      ((-α x) / (2 * Real.sqrt (h x))) x := by
    simpa only [div_eq_mul_inv, mul_comm, one_mul] using
      (Real.hasDerivAt_sqrt hhPos.ne').comp x hh
  let d : ℝ → ℝ :=
    fun y => 2 * (h * ((fun z : ℝ => Real.sqrt z) ∘ h)) y
  have hd : HasDerivAt d (-3 * α x * Real.sqrt (h x)) x := by
    have hraw := (hh.mul hs).const_mul 2
    change HasDerivAt
      (fun y => 2 * (h * ((fun z : ℝ => Real.sqrt z) ∘ h)) y) _ x
    refine hraw.congr_deriv ?_
    simp only [Function.comp_apply]
    field_simp [(Real.sqrt_pos.mpr hhPos).ne']
    rw [Real.sq_sqrt hhPos.le]
    ring
  have hdne : d x ≠ 0 := by
    dsimp only [d, Function.comp_apply, Pi.mul_apply]
    exact mul_ne_zero (by norm_num)
      (mul_ne_zero hhPos.ne' (Real.sqrt_pos.mpr hhPos).ne')
  have hquot := hα.div hd hdne
  have hfun : thetaCuspLikelihoodInverseRootSlope = α / d := by
    funext y
    dsimp only [thetaCuspLikelihoodInverseRootSlope, α, d, h,
      Function.comp_apply, Pi.mul_apply, Pi.div_apply]
    ring
  rw [hfun]
  refine hquot.congr_deriv ?_
  have hrhsne :
      4 * h x ^ (2 : ℕ) * Real.sqrt (h x) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hhPos.ne'))
      (Real.sqrt_pos.mpr hhPos).ne'
  rw [div_eq_div_iff (pow_ne_zero 2 hdne) hrhsne]
  dsimp only [d, h, α, thetaCuspLikelihoodHomotopyCurvatureEnergy]
  simp only [Function.comp_apply, Pi.mul_apply]
  ring

theorem deriv_inverseRootSlope_pos
    {x : ℝ} (hx : 0 ≤ x)
    (hscale : 6 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    0 < deriv thetaCuspLikelihoodInverseRootSlope x := by
  rw [(hasDerivAt_inverseRootSlope hx).deriv]
  exact div_pos
    (thetaCuspLikelihoodHomotopyCurvatureEnergy_pos hx hscale)
    (mul_pos
      (mul_pos (by norm_num)
        (pow_pos (thetaCuspLikelihoodSourceLogPartitionJetTwo_pos hx) 2))
      (Real.sqrt_pos.mpr
        (thetaCuspLikelihoodSourceLogPartitionJetTwo_pos hx)))

theorem strictMonoOn_inverseRootSlope_of_scale
    {x₀ : ℝ} (hx₀ : 0 ≤ x₀)
    (hscale₀ : 6 ≤ thetaCuspSingleAtomReflectionScale 1 x₀) :
    StrictMonoOn thetaCuspLikelihoodInverseRootSlope (Set.Ici x₀) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici x₀)
  · intro x hx
    exact (hasDerivAt_inverseRootSlope
      (hx₀.trans hx)).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    have hx0 : 0 ≤ x := hx₀.trans hx.le
    exact deriv_inverseRootSlope_pos hx0
      (hscale₀.trans (scale_mono hx.le))

private theorem projective_endpoint_bridge
    {a b α β C D t r q z : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hα : 0 < α) (hβ : 0 < β)
    (hC : 0 < C) (hD : 0 < D) (hr : 0 < r)
    (hq : 0 < q)
    (hbrel : b = a * r ^ (2 : ℕ)) (hαrel : α = q * β)
    (htrel : t * β = z * b)
    (hshape : q * r ^ (3 : ℕ) < 1)
    (hsec : 1 - r < z)
    (hprojective : C * r < D * q) :
    C * (b - t * β) < D * (a + t * α) := by
  by_cases hz1 : z < 1
  · have hfac : 0 < a * r * (1 - z) := by positivity
    have hprojMul := mul_lt_mul_of_pos_right hprojective hfac
    have hsecMul := mul_lt_mul_of_pos_left hsec
      (mul_pos (mul_pos hq hr) (by positivity : 0 < 1 + r))
    have hsecNorm :
        q * r - q * r ^ (3 : ℕ) < q * z * r + q * z * r ^ (2 : ℕ) := by
      calc
        q * r - q * r ^ (3 : ℕ) = q * r * (1 + r) * (1 - r) := by ring
        _ < q * r * (1 + r) * z := hsecMul
        _ = q * z * r + q * z * r ^ (2 : ℕ) := by ring
    have hnormalized : q * r * (1 - z) < 1 + q * z * r ^ (2 : ℕ) := by
      linarith
    have hnormMul := mul_lt_mul_of_pos_left hnormalized (mul_pos hD ha)
    have hprojNorm :
        C * a * r ^ (2 : ℕ) * (1 - z) < D * q * a * r * (1 - z) := by
      calc
        C * a * r ^ (2 : ℕ) * (1 - z) =
            C * r * (a * r * (1 - z)) := by ring
        _ < D * q * (a * r * (1 - z)) := hprojMul
        _ = D * q * a * r * (1 - z) := by ring
    have hnormalizedMul :
        D * q * a * r * (1 - z) <
          D * a * (1 + q * z * r ^ (2 : ℕ)) := by
      calc
        D * q * a * r * (1 - z) =
            D * a * (q * r * (1 - z)) := by ring
        _ < D * a * (1 + q * z * r ^ (2 : ℕ)) := hnormMul
    calc
      C * (b - t * β) = C * a * r ^ (2 : ℕ) * (1 - z) := by
        rw [htrel, hbrel]
        ring
      _ < D * q * a * r * (1 - z) := hprojNorm
      _ < D * a * (1 + q * z * r ^ (2 : ℕ)) := hnormalizedMul
      _ = D * (a + t * α) := by
        rw [hαrel, show t * (q * β) = q * (t * β) by ring, htrel, hbrel]
        ring
  · have hz : 1 ≤ z := le_of_not_gt hz1
    have hleft : C * (b - t * β) ≤ 0 := by
      rw [htrel, hbrel]
      have hzMul : 1 * (a * r ^ (2 : ℕ)) ≤ z * (a * r ^ (2 : ℕ)) :=
        mul_le_mul_of_nonneg_right hz (by positivity)
      exact mul_nonpos_of_nonneg_of_nonpos hC.le (sub_nonpos.mpr (by
        simpa only [one_mul] using hzMul))
    have hright : 0 < D * (a + t * α) := by
      have hzPos : 0 < z := lt_of_lt_of_le zero_lt_one hz
      have htβPos : 0 < t * β := by rw [htrel]; positivity
      have htPos : 0 < t :=
        ((mul_pos_iff.mp htβPos).resolve_right (fun hneg =>
          (not_lt_of_ge hβ.le) hneg.2)).1
      have htα : 0 ≤ t * α := (mul_pos htPos hα).le
      positivity
    exact hleft.trans_lt hright

/-- Reflected endpoint determinant forced by inverse-root and projective curvature drift. -/
theorem thetaCuspLikelihood_projectiveEndpointTransport
    {u t : ℝ} (ht : 0 < t) (htu : t ≤ u)
    (hscale : 6 ≤ thetaCuspSingleAtomReflectionScale 1 (u - t)) :
    thetaCuspLikelihoodSourceLogPartitionJetFour (u - t) *
        (thetaCuspLikelihoodSourceLogPartitionJetTwo (u + t) -
          t * (-thetaCuspLikelihoodSourceLogPartitionJetThree (u + t))) <
      thetaCuspLikelihoodSourceLogPartitionJetFour (u + t) *
        (thetaCuspLikelihoodSourceLogPartitionJetTwo (u - t) +
          t * (-thetaCuspLikelihoodSourceLogPartitionJetThree (u - t))) := by
  let l := u - t
  let r₀ := u + t
  let h := thetaCuspLikelihoodSourceLogPartitionJetTwo
  let a := h l
  let b := h r₀
  let α := -thetaCuspLikelihoodSourceLogPartitionJetThree l
  let β := -thetaCuspLikelihoodSourceLogPartitionJetThree r₀
  let C := thetaCuspLikelihoodSourceLogPartitionJetFour l
  let D := thetaCuspLikelihoodSourceLogPartitionJetFour r₀
  let r := Real.sqrt b / Real.sqrt a
  let q := α / β
  let z := t * β / b
  have hl0 : 0 ≤ l := by dsimp only [l]; linarith
  have hr0 : 0 ≤ r₀ := by dsimp only [r₀]; linarith
  have hlr : l < r₀ := by dsimp only [l, r₀]; linarith
  have ha : 0 < a := by
    simpa only [a, h] using thetaCuspLikelihoodSourceLogPartitionJetTwo_pos hl0
  have hb : 0 < b := by
    simpa only [b, h] using thetaCuspLikelihoodSourceLogPartitionJetTwo_pos hr0
  have hα : 0 < α := by
    simpa only [α] using neg_pos.mpr
      (thetaCuspLikelihoodSourceLogPartitionJetThree_neg hl0)
  have hβ : 0 < β := by
    simpa only [β] using neg_pos.mpr
      (thetaCuspLikelihoodSourceLogPartitionJetThree_neg hr0)
  have hC : 0 < C := by
    simpa only [C] using thetaCuspLikelihoodSourceLogPartitionJetFour_pos hl0
  have hD : 0 < D := by
    simpa only [D] using thetaCuspLikelihoodSourceLogPartitionJetFour_pos hr0
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  have hr : 0 < r := by dsimp only [r]; positivity
  have hbrel : b = a * r ^ (2 : ℕ) := by
    dsimp only [r]
    field_simp [hsa.ne']
    rw [Real.sq_sqrt ha.le, Real.sq_sqrt hb.le]
    ring
  have hsqrtRel : Real.sqrt b = r * Real.sqrt a := by
    dsimp only [r]
    field_simp [hsa.ne']
  have hq : 0 < q := by dsimp only [q]; positivity
  have hαrel : α = q * β := by
    dsimp only [q]
    field_simp [hβ.ne']
  have htrel : t * β = z * b := by
    dsimp only [z]
    field_simp [hb.ne']
  have hslopeMono :=
    strictMonoOn_inverseRootSlope_of_scale hl0 hscale
  have hslope := hslopeMono
    (show l ∈ Set.Ici l by exact Set.mem_Ici.mpr le_rfl)
    (show r₀ ∈ Set.Ici l by exact hlr.le) hlr
  have hslopeRaw :
      α / (2 * a * Real.sqrt a) <
        β / (2 * b * Real.sqrt b) := by
    simpa only [thetaCuspLikelihoodInverseRootSlope,
      l, r₀, a, b, h, α, β] using hslope
  have hdenA : 0 < 2 * a * Real.sqrt a := by positivity
  have hdenB : 0 < 2 * b * Real.sqrt b := by positivity
  have hslopeCross :
      α * (2 * b * Real.sqrt b) <
        β * (2 * a * Real.sqrt a) :=
    (div_lt_div_iff₀ hdenA hdenB).mp hslopeRaw
  have hshape : q * r ^ (3 : ℕ) < 1 := by
    have hcommon : 0 < β * (2 * a * Real.sqrt a) := by positivity
    have hmul :
        β * (2 * a * Real.sqrt a) * (q * r ^ (3 : ℕ)) <
          β * (2 * a * Real.sqrt a) * 1 := by
      calc
        β * (2 * a * Real.sqrt a) * (q * r ^ (3 : ℕ)) =
            α * (2 * b * Real.sqrt b) := by
          rw [hαrel, hsqrtRel, hbrel]
          ring
        _ < β * (2 * a * Real.sqrt a) := hslopeCross
        _ = β * (2 * a * Real.sqrt a) * 1 := by ring
    exact lt_of_mul_lt_mul_left hmul hcommon.le
  have hratioMono :=
    strictMonoOn_fourthThirdRootRatio_of_scale hl0 hscale
  have hratio := hratioMono
    (show l ∈ Set.Ici l by exact Set.mem_Ici.mpr le_rfl)
    (show r₀ ∈ Set.Ici l by exact hlr.le) hlr
  have hratioRaw :
      C ^ (2 : ℕ) / (α ^ (2 : ℕ) * a) < D ^ (2 : ℕ) / (β ^ (2 : ℕ) * b) := by
    simpa only [thetaCuspLikelihoodFourthThirdRootRatio,
      l, r₀, a, b, h, α, β, C, D] using hratio
  have hratioDenA : 0 < α ^ (2 : ℕ) * a := mul_pos (sq_pos_of_pos hα) ha
  have hratioDenB : 0 < β ^ (2 : ℕ) * b := mul_pos (sq_pos_of_pos hβ) hb
  have hratioCross :
      C ^ (2 : ℕ) * (β ^ (2 : ℕ) * b) < D ^ (2 : ℕ) * (α ^ (2 : ℕ) * a) :=
    (div_lt_div_iff₀ hratioDenA hratioDenB).mp hratioRaw
  have hprojective : C * r < D * q := by
    have hcommon : 0 < β ^ (2 : ℕ) * a := mul_pos (sq_pos_of_pos hβ) ha
    have hsquares : (C * r) ^ (2 : ℕ) < (D * q) ^ (2 : ℕ) := by
      have hmul :
          β ^ (2 : ℕ) * a * (C * r) ^ (2 : ℕ) <
            β ^ (2 : ℕ) * a * (D * q) ^ (2 : ℕ) := by
        calc
          β ^ (2 : ℕ) * a * (C * r) ^ (2 : ℕ) = C ^ (2 : ℕ) * (β ^ (2 : ℕ) * b) := by
            rw [hbrel]
            ring
          _ < D ^ (2 : ℕ) * (α ^ (2 : ℕ) * a) := hratioCross
          _ = β ^ (2 : ℕ) * a * (D * q) ^ (2 : ℕ) := by
            rw [hαrel]
            ring
      exact lt_of_mul_lt_mul_left hmul hcommon.le
    exact (sq_lt_sq₀ (mul_nonneg hC.le hr.le)
      (mul_nonneg hD.le hq.le)).mp hsquares
  let p := thetaCuspLikelihoodInverseRoot
  let L := thetaCuspLikelihoodInverseRootSlope
  have hpcont : ContinuousOn p (Set.Icc l r₀) := by
    intro y hy
    exact (hasDerivAt_inverseRoot
      (hl0.trans hy.1)).continuousAt.continuousWithinAt
  have hpderiv : ∀ y ∈ Set.Ioo l r₀, HasDerivAt p (L y) y := by
    intro y hy
    exact hasDerivAt_inverseRoot (hl0.trans hy.1.le)
  obtain ⟨c, hc, hcslope⟩ :=
    exists_hasDerivAt_eq_slope p L hlr hpcont hpderiv
  have hcSlopeLt : L c < L r₀ :=
    hslopeMono (show c ∈ Set.Ici l by exact hc.1.le)
      (show r₀ ∈ Set.Ici l by exact hlr.le) hc.2
  have hchord : p r₀ - p l = (r₀ - l) * L c := by
    have hne : r₀ - l ≠ 0 := sub_ne_zero.mpr hlr.ne'
    have hcleared := (eq_div_iff hne).mp hcslope
    calc
      p r₀ - p l = L c * (r₀ - l) := hcleared.symm
      _ = (r₀ - l) * L c := by ring
  have hsecRaw : p r₀ - p l < 2 * t * L r₀ := by
    rw [hchord, show r₀ - l = 2 * t by dsimp only [r₀, l]; ring]
    exact mul_lt_mul_of_pos_left hcSlopeLt (by positivity)
  have hsecBase : b * (1 - r) < t * β := by
    have hP : 0 < b * Real.sqrt b * Real.sqrt a := by positivity
    have hmul := mul_lt_mul_of_pos_right hsecRaw hP
    have hcleared :
        b * (Real.sqrt a - Real.sqrt b) < t * β * Real.sqrt a := by
      calc
        b * (Real.sqrt a - Real.sqrt b) =
            (p r₀ - p l) * (b * Real.sqrt b * Real.sqrt a) := by
          change b * (Real.sqrt a - Real.sqrt b) =
            ((Real.sqrt b)⁻¹ - (Real.sqrt a)⁻¹) *
              (b * Real.sqrt b * Real.sqrt a)
          field_simp [hsa.ne', hsb.ne']
        _ < (2 * t * L r₀) * (b * Real.sqrt b * Real.sqrt a) := hmul
        _ = t * β * Real.sqrt a := by
          change (2 * t * (β / (2 * b * Real.sqrt b))) *
              (b * Real.sqrt b * Real.sqrt a) =
            t * β * Real.sqrt a
          field_simp [hb.ne', hsb.ne']
    have hscaled :
        b * (1 - r) * Real.sqrt a < t * β * Real.sqrt a := by
      calc
        b * (1 - r) * Real.sqrt a =
            b * (Real.sqrt a - Real.sqrt b) := by rw [hsqrtRel]; ring
        _ < t * β * Real.sqrt a := hcleared
    exact lt_of_mul_lt_mul_right hscaled hsa.le
  have hsec : 1 - r < z := by
    have hscaled : b * (1 - r) < b * z := by
      calc
        b * (1 - r) < t * β := hsecBase
        _ = b * z := by rw [htrel]; ring
    exact lt_of_mul_lt_mul_left hscaled hb.le
  have hbridge := projective_endpoint_bridge ha hb hα hβ hC hD
    hr hq hbrel hαrel htrel hshape hsec hprojective
  simpa only [a, b, h, α, β, C, D, l, r₀] using hbridge

/-- Derivative numerator of the second reflected transport ratio. -/
theorem thetaCuspLikelihood_secondTransportNumerator_neg
    {u t : ℝ} (ht : 0 < t) (htu : t ≤ u)
    (hscale : 6 ≤ thetaCuspSingleAtomReflectionScale 1 (u - t)) :
    let a := thetaCuspLikelihoodSourceLogPartitionJetTwo (u - t)
    let b := thetaCuspLikelihoodSourceLogPartitionJetTwo (u + t)
    let α := -thetaCuspLikelihoodSourceLogPartitionJetThree (u - t)
    let β := -thetaCuspLikelihoodSourceLogPartitionJetThree (u + t)
    let C := thetaCuspLikelihoodSourceLogPartitionJetFour (u - t)
    let D := thetaCuspLikelihoodSourceLogPartitionJetFour (u + t)
    (C - D) * (2 * (a + b) + t * (α - β)) -
      (α + β) * (3 * (α - β) + t * (C + D)) < 0 := by
  dsimp only
  let l := u - t
  let r := u + t
  let a := thetaCuspLikelihoodSourceLogPartitionJetTwo l
  let b := thetaCuspLikelihoodSourceLogPartitionJetTwo r
  let α := -thetaCuspLikelihoodSourceLogPartitionJetThree l
  let β := -thetaCuspLikelihoodSourceLogPartitionJetThree r
  let C := thetaCuspLikelihoodSourceLogPartitionJetFour l
  let D := thetaCuspLikelihoodSourceLogPartitionJetFour r
  have hl0 : 0 ≤ l := by dsimp only [l]; linarith
  have hr0 : 0 ≤ r := by dsimp only [r]; linarith
  have hlr : l < r := by dsimp only [l, r]; linarith
  have henergy :=
    strictAntiOn_thetaCuspLikelihoodHomotopyCurvatureEnergy_of_scale hl0 hscale
      (show l ∈ Set.Ici l by exact Set.mem_Ici.mpr le_rfl)
      (show r ∈ Set.Ici l by exact Set.mem_Ici.mpr hlr.le) hlr
  have henergyRaw : 2 * (a * C - b * D) < 3 * (α ^ (2 : ℕ) - β ^ (2 : ℕ)) := by
    have henergy' := henergy
    dsimp only [thetaCuspLikelihoodHomotopyCurvatureEnergy,
      a, b, α, β, C, D, l, r] at henergy' ⊢
    nlinarith
  have hbridge := thetaCuspLikelihood_projectiveEndpointTransport
    ht htu hscale
  have hbridgeRaw : b * C - a * D < t * (C * β + D * α) := by
    dsimp only [a, b, α, β, C, D, l, r]
    calc
      thetaCuspLikelihoodSourceLogPartitionJetTwo (u + t) *
            thetaCuspLikelihoodSourceLogPartitionJetFour (u - t) -
          thetaCuspLikelihoodSourceLogPartitionJetTwo (u - t) *
            thetaCuspLikelihoodSourceLogPartitionJetFour (u + t) <
        t * (thetaCuspLikelihoodSourceLogPartitionJetFour (u - t) *
              (-thetaCuspLikelihoodSourceLogPartitionJetThree (u + t)) +
            thetaCuspLikelihoodSourceLogPartitionJetFour (u + t) *
              (-thetaCuspLikelihoodSourceLogPartitionJetThree (u - t))) := by
          linarith
      _ = _ := by rfl
  change (C - D) * (2 * (a + b) + t * (α - β)) -
    (α + β) * (3 * (α - β) + t * (C + D)) < 0
  calc
    (C - D) * (2 * (a + b) + t * (α - β)) -
        (α + β) * (3 * (α - β) + t * (C + D)) =
      2 * (a + b) * (C - D) - 3 * (α ^ (2 : ℕ) - β ^ (2 : ℕ)) -
        2 * t * (C * β + D * α) := by ring
    _ < 2 * (a + b) * (C - D) - 2 * (a * C - b * D) -
        2 * t * (C * β + D * α) := by linarith
    _ = 2 * (b * C - a * D - t * (C * β + D * α)) := by ring
    _ < 0 := by linarith

/-- Ratio of the second reflected endpoint transports. -/
def thetaCuspLikelihoodSecondTransportRatio (u t : ℝ) : ℝ :=
  let a := thetaCuspLikelihoodSourceLogPartitionJetTwo (u - t)
  let b := thetaCuspLikelihoodSourceLogPartitionJetTwo (u + t)
  let α := -thetaCuspLikelihoodSourceLogPartitionJetThree (u - t)
  let β := -thetaCuspLikelihoodSourceLogPartitionJetThree (u + t)
  (α + β) / (2 * (a + b) + t * (α - β))

theorem hasDerivAt_secondTransportRatio
    {u t : ℝ} (ht : 0 ≤ t) (htu : t ≤ u) :
    let a := thetaCuspLikelihoodSourceLogPartitionJetTwo (u - t)
    let b := thetaCuspLikelihoodSourceLogPartitionJetTwo (u + t)
    let α := -thetaCuspLikelihoodSourceLogPartitionJetThree (u - t)
    let β := -thetaCuspLikelihoodSourceLogPartitionJetThree (u + t)
    let C := thetaCuspLikelihoodSourceLogPartitionJetFour (u - t)
    let D := thetaCuspLikelihoodSourceLogPartitionJetFour (u + t)
    HasDerivAt (thetaCuspLikelihoodSecondTransportRatio u)
      (((C - D) * (2 * (a + b) + t * (α - β)) -
          (α + β) * (3 * (α - β) + t * (C + D))) /
        (2 * (a + b) + t * (α - β)) ^ (2 : ℕ)) t := by
  dsimp only
  let h := thetaCuspLikelihoodSourceLogPartitionJetTwo
  let αf : ℝ → ℝ := fun x => -thetaCuspLikelihoodSourceLogPartitionJetThree x
  let a : ℝ → ℝ := fun s => h (u - s)
  let b : ℝ → ℝ := fun s => h (u + s)
  let α : ℝ → ℝ := fun s => αf (u - s)
  let β : ℝ → ℝ := fun s => αf (u + s)
  let C := thetaCuspLikelihoodSourceLogPartitionJetFour (u - t)
  let D := thetaCuspLikelihoodSourceLogPartitionJetFour (u + t)
  have hl0 : 0 ≤ u - t := by linarith
  have hr0 : 0 ≤ u + t := by linarith
  have hBl := thetaCuspLikelihoodCoordinate_pos hl0
  have hBr := thetaCuspLikelihoodCoordinate_pos hr0
  have ha : HasDerivAt a (α t) t := by
    have hraw := (hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetTwo hBl).comp t
      ((hasDerivAt_const t u).sub (hasDerivAt_id t))
    refine (hraw.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _ => rfl)).congr_deriv ?_
    simp only [α, αf]
    ring
  have hb : HasDerivAt b (-β t) t := by
    have hraw := (hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetTwo hBr).comp t
      ((hasDerivAt_const t u).add (hasDerivAt_id t))
    refine (hraw.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _ => rfl)).congr_deriv ?_
    simp only [β, αf]
    ring
  have hα : HasDerivAt α C t := by
    have hraw :=
      ((hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetThree hBl).neg.comp t
        ((hasDerivAt_const t u).sub (hasDerivAt_id t)))
    refine (hraw.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _ => rfl)).congr_deriv ?_
    simp only [C]
    ring
  have hβ : HasDerivAt β (-D) t := by
    have hraw :=
      ((hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetThree hBr).neg.comp t
        ((hasDerivAt_const t u).add (hasDerivAt_id t)))
    refine (hraw.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _ => rfl)).congr_deriv ?_
    simp only [D]
    ring
  let num : ℝ → ℝ := α + β
  let den : ℝ → ℝ := fun s => 2 * (a s + b s) + s * (α s - β s)
  have hnum : HasDerivAt num (C - D) t := by
    exact (hα.add hβ).congr_deriv (by ring)
  have hden : HasDerivAt den (3 * (α t - β t) + t * (C + D)) t := by
    have hraw := ((ha.add hb).const_mul 2).add
      ((hasDerivAt_id t).mul (hα.sub hβ))
    refine (hraw.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _ => rfl)).congr_deriv ?_
    simp only [Pi.sub_apply, id_eq]
    ring
  have hαPos : 0 < α t := by
    simpa only [α, αf] using neg_pos.mpr
      (thetaCuspLikelihoodSourceLogPartitionJetThree_neg hl0)
  have hβPos : 0 < β t := by
    simpa only [β, αf] using neg_pos.mpr
      (thetaCuspLikelihoodSourceLogPartitionJetThree_neg hr0)
  have hαβ : β t ≤ α t := by
    by_cases hzero : t = 0
    · subst t
      simpa only [α, β, αf, sub_zero, add_zero] using
        (le_rfl : αf u ≤ αf u)
    · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm hzero)
      have hlt : u - t < u + t := by linarith
      have hmono := strictMonoOn_thetaCuspLikelihoodSourceLogPartitionJetThree
        (show u - t ∈ Set.Ici (0 : ℝ) by exact hl0)
        (show u + t ∈ Set.Ici (0 : ℝ) by exact hr0) hlt
      dsimp only [α, β, αf]
      linarith
  have haPos : 0 < a t := by
    simpa only [a, h] using thetaCuspLikelihoodSourceLogPartitionJetTwo_pos hl0
  have hbPos : 0 < b t := by
    simpa only [b, h] using thetaCuspLikelihoodSourceLogPartitionJetTwo_pos hr0
  have hdenPos : 0 < den t := by
    dsimp only [den]
    have : 0 ≤ t * (α t - β t) := mul_nonneg ht (sub_nonneg.mpr hαβ)
    positivity
  have hquot := hnum.div hden hdenPos.ne'
  have hfun : thetaCuspLikelihoodSecondTransportRatio u = num / den := by
    funext s
    dsimp only [thetaCuspLikelihoodSecondTransportRatio,
      num, den, a, b, α, β, αf, h, Pi.add_apply, Pi.div_apply]
  rw [hfun]
  simpa only [num, den, a, b, α, β, αf, h, C, D, Pi.add_apply] using hquot

theorem strictAntiOn_secondTransportRatio
    {u T : ℝ} (hT : 0 < T) (hTu : T ≤ u)
    (hscale : 6 ≤ thetaCuspSingleAtomReflectionScale 1 (u - T)) :
    StrictAntiOn (thetaCuspLikelihoodSecondTransportRatio u) (Set.Icc 0 T) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc 0 T)
  · intro t ht
    have hd := hasDerivAt_secondTransportRatio ht.1 (ht.2.trans hTu)
    exact hd.continuousAt.continuousWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    have htu : t ≤ u := ht.2.le.trans hTu
    have hscaleT : 6 ≤ thetaCuspSingleAtomReflectionScale 1 (u - t) :=
      hscale.trans (scale_mono (by linarith [ht.2]))
    rw [(hasDerivAt_secondTransportRatio ht.1.le htu).deriv]
    have hl0 : 0 ≤ u - t := by linarith [ht.2, hTu]
    have hr0 : 0 ≤ u + t := by linarith [ht.1, hl0]
    have hmono := strictMonoOn_thetaCuspLikelihoodSourceLogPartitionJetThree
      (show u - t ∈ Set.Ici (0 : ℝ) by exact Set.mem_Ici.mpr hl0)
      (show u + t ∈ Set.Ici (0 : ℝ) by exact Set.mem_Ici.mpr hr0)
      (by linarith [ht.1] : u - t < u + t)
    have hαβ : 0 <
        (-thetaCuspLikelihoodSourceLogPartitionJetThree (u - t)) -
          (-thetaCuspLikelihoodSourceLogPartitionJetThree (u + t)) := by
      linarith
    have hdenPos : 0 <
        2 * (thetaCuspLikelihoodSourceLogPartitionJetTwo (u - t) +
          thetaCuspLikelihoodSourceLogPartitionJetTwo (u + t)) +
        t * ((-thetaCuspLikelihoodSourceLogPartitionJetThree (u - t)) -
          (-thetaCuspLikelihoodSourceLogPartitionJetThree (u + t))) := by
      have ha := thetaCuspLikelihoodSourceLogPartitionJetTwo_pos hl0
      have hb := thetaCuspLikelihoodSourceLogPartitionJetTwo_pos hr0
      have hfirst : 0 < 2 *
          (thetaCuspLikelihoodSourceLogPartitionJetTwo (u - t) +
            thetaCuspLikelihoodSourceLogPartitionJetTwo (u + t)) := by positivity
      have hsecond : 0 ≤ t *
          ((-thetaCuspLikelihoodSourceLogPartitionJetThree (u - t)) -
            (-thetaCuspLikelihoodSourceLogPartitionJetThree (u + t))) :=
        mul_nonneg ht.1.le hαβ.le
      exact add_pos_of_pos_of_nonneg hfirst hsecond
    exact div_neg_of_neg_of_pos
      (thetaCuspLikelihood_secondTransportNumerator_neg ht.1 htu hscaleT)
      (sq_pos_of_pos hdenPos)

private theorem exists_derivRatio_eq_incrementRatio
    {f g f' g' : ℝ → ℝ} {a b : ℝ}
    (hab : a < b)
    (hfcont : ContinuousOn f (Set.Icc a b))
    (hgcont : ContinuousOn g (Set.Icc a b))
    (hfderiv : ∀ x ∈ Set.Ioo a b, HasDerivAt f (f' x) x)
    (hgderiv : ∀ x ∈ Set.Ioo a b, HasDerivAt g (g' x) x)
    (hgInc : g b - g a ≠ 0)
    (hg' : ∀ x ∈ Set.Ioo a b, g' x ≠ 0) :
    ∃ c ∈ Set.Ioo a b,
      f' c / g' c = (f b - f a) / (g b - g a) := by
  let lam := (f b - f a) / (g b - g a)
  let k : ℝ → ℝ := fun x => f x - lam * g x
  let k' : ℝ → ℝ := fun x => f' x - lam * g' x
  have hkcont : ContinuousOn k (Set.Icc a b) := by
    exact hfcont.sub (continuousOn_const.mul hgcont)
  have hkderiv : ∀ x ∈ Set.Ioo a b, HasDerivAt k (k' x) x := by
    intro x hx
    have hraw := (hfderiv x hx).sub ((hgderiv x hx).const_mul lam)
    refine (hraw.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _ => rfl)).congr_deriv ?_
    ring
  obtain ⟨c, hc, hcslope⟩ :=
    exists_hasDerivAt_eq_slope k k' hab hkcont hkderiv
  have hkEnds : k b - k a = 0 := by
    dsimp only [k, lam]
    field_simp [hgInc]
    ring
  have hk'zero : k' c = 0 := by rw [hcslope, hkEnds]; simp
  refine ⟨c, hc, ?_⟩
  have hlinear : f' c = lam * g' c := by
    dsimp only [k'] at hk'zero
    linarith
  rw [div_eq_iff (hg' c hc)]
  exact hlinear

private theorem div_derivativeNumerator_neg_of_strictAnti_derivRatio
    {f g f' g' : ℝ → ℝ} {a b x : ℝ}
    (hab : a < b) (hx : x ∈ Set.Ioc a b)
    (hfa : f a = 0) (hga : g a = 0)
    (hfcont : ContinuousOn f (Set.Icc a b))
    (hgcont : ContinuousOn g (Set.Icc a b))
    (hfderiv : ∀ y ∈ Set.Icc a b, HasDerivAt f (f' y) y)
    (hgderiv : ∀ y ∈ Set.Icc a b, HasDerivAt g (g' y) y)
    (hg'pos : ∀ y ∈ Set.Ioc a b, 0 < g' y)
    (hratio : StrictAntiOn (fun y => f' y / g' y) (Set.Ioc a b)) :
    f' x * g x - f x * g' x < 0 := by
  have hxIcc : x ∈ Set.Icc a b := ⟨hx.1.le, hx.2⟩
  have hgmono : StrictMonoOn g (Set.Icc a b) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc a b)
    · intro y hy
      exact (hgderiv y hy).continuousAt.continuousWithinAt
    · intro y hy
      rw [interior_Icc] at hy
      rw [(hgderiv y ⟨hy.1.le, hy.2.le⟩).deriv]
      exact hg'pos y ⟨hy.1, hy.2.le⟩
  have hgx : 0 < g x := by
    rw [← hga]
    exact hgmono (show a ∈ Set.Icc a b by exact ⟨le_rfl, hab.le⟩) hxIcc hx.1
  have hfcontAx : ContinuousOn f (Set.Icc a x) :=
    hfcont.mono (by intro y hy; exact ⟨hy.1, hy.2.trans hx.2⟩)
  have hgcontAx : ContinuousOn g (Set.Icc a x) :=
    hgcont.mono (by intro y hy; exact ⟨hy.1, hy.2.trans hx.2⟩)
  obtain ⟨c, hc, hcRatio⟩ := exists_derivRatio_eq_incrementRatio
    hx.1 hfcontAx hgcontAx
    (fun y hy => hfderiv y ⟨hy.1.le, hy.2.le.trans hx.2⟩)
    (fun y hy => hgderiv y ⟨hy.1.le, hy.2.le.trans hx.2⟩)
    (by rw [hga]; simpa only [sub_zero] using hgx.ne')
    (fun y hy => (hg'pos y ⟨hy.1, hy.2.le.trans hx.2⟩).ne')
  have hcIoc : c ∈ Set.Ioc a b := ⟨hc.1, hc.2.le.trans hx.2⟩
  have hratioCx := hratio hcIoc hx hc.2
  have hquot : f' x / g' x < f x / g x := by
    change f' x / g' x < f' c / g' c at hratioCx
    rw [hcRatio, hfa, hga, sub_zero, sub_zero] at hratioCx
    exact hratioCx
  have hcross := (div_lt_div_iff₀ (hg'pos x hx) hgx).mp hquot
  linarith

private theorem strictAntiOn_div_of_strictAnti_derivRatio
    {f g f' g' : ℝ → ℝ} {a b : ℝ}
    (hab : a < b)
    (hfa : f a = 0) (hga : g a = 0)
    (hfcont : ContinuousOn f (Set.Icc a b))
    (hgcont : ContinuousOn g (Set.Icc a b))
    (hfderiv : ∀ y ∈ Set.Icc a b, HasDerivAt f (f' y) y)
    (hgderiv : ∀ y ∈ Set.Icc a b, HasDerivAt g (g' y) y)
    (hg'pos : ∀ y ∈ Set.Ioc a b, 0 < g' y)
    (hratio : StrictAntiOn (fun y => f' y / g' y) (Set.Ioc a b)) :
    StrictAntiOn (fun y => f y / g y) (Set.Ioc a b) := by
  have hgmono : StrictMonoOn g (Set.Icc a b) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc a b)
    · intro y hy
      exact (hgderiv y hy).continuousAt.continuousWithinAt
    · intro y hy
      rw [interior_Icc] at hy
      rw [(hgderiv y ⟨hy.1.le, hy.2.le⟩).deriv]
      exact hg'pos y ⟨hy.1, hy.2.le⟩
  apply strictAntiOn_of_deriv_neg (convex_Ioc a b)
  · intro x hx
    have hxIcc : x ∈ Set.Icc a b := ⟨hx.1.le, hx.2⟩
    have hgx : 0 < g x := by
      rw [← hga]
      exact hgmono (show a ∈ Set.Icc a b by exact ⟨le_rfl, hab.le⟩) hxIcc hx.1
    have hd := (hfderiv x hxIcc).div (hgderiv x hxIcc) hgx.ne'
    exact hd.continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioc] at hx
    have hxIoc : x ∈ Set.Ioc a b := ⟨hx.1, hx.2.le⟩
    have hxIcc : x ∈ Set.Icc a b := ⟨hx.1.le, hx.2.le⟩
    have hgx : 0 < g x := by
      rw [← hga]
      exact hgmono (show a ∈ Set.Icc a b by exact ⟨le_rfl, hab.le⟩) hxIcc hx.1
    change deriv (f / g) x < 0
    rw [((hfderiv x hxIcc).div (hgderiv x hxIcc) hgx.ne').deriv]
    exact div_neg_of_neg_of_pos
      (div_derivativeNumerator_neg_of_strictAnti_derivRatio
        hab hxIoc hfa hga hfcont hgcont hfderiv hgderiv hg'pos hratio)
      (sq_pos_of_pos hgx)

def thetaCuspLikelihoodFirstTransportNumerator (u t : ℝ) : ℝ :=
  c5LikelihoodScaleMixedJetOne u t

def thetaCuspLikelihoodFirstTransportDenominator (u t : ℝ) : ℝ :=
  -thetaCuspReflectedLikelihoodCumulantJetOne u t -
    t * thetaCuspReflectedLikelihoodCumulantJetTwo u t

def thetaCuspLikelihoodSecondTransportNumerator (u t : ℝ) : ℝ :=
  c5LikelihoodScaleMixedJetTwo u t

def thetaCuspLikelihoodSecondTransportDenominator (u t : ℝ) : ℝ :=
  let a := thetaCuspLikelihoodSourceLogPartitionJetTwo (u - t)
  let b := thetaCuspLikelihoodSourceLogPartitionJetTwo (u + t)
  let α := -thetaCuspLikelihoodSourceLogPartitionJetThree (u - t)
  let β := -thetaCuspLikelihoodSourceLogPartitionJetThree (u + t)
  2 * (a + b) + t * (α - β)

theorem hasDerivAt_firstTransportNumerator
    {u t : ℝ} (ht : 0 ≤ t) (htu : t ≤ u) :
    HasDerivAt (thetaCuspLikelihoodFirstTransportNumerator u)
      (thetaCuspLikelihoodSecondTransportNumerator u t) t := by
  have hl0 : 0 ≤ u - t := by linarith
  have hr0 : 0 ≤ u + t := by linarith
  have hl := (hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetTwo
    (thetaCuspLikelihoodCoordinate_pos hl0)).comp t
      ((hasDerivAt_const t u).sub (hasDerivAt_id t))
  have hr := (hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetTwo
    (thetaCuspLikelihoodCoordinate_pos hr0)).comp t
      ((hasDerivAt_const t u).add (hasDerivAt_id t))
  have hraw := hl.sub hr
  refine (hraw.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun _ => rfl)).congr_deriv ?_
  unfold thetaCuspLikelihoodSecondTransportNumerator
    c5LikelihoodScaleMixedJetTwo
  ring

theorem hasDerivAt_firstTransportDenominator
    {u t : ℝ} (ht : 0 ≤ t) (htu : t ≤ u) :
    HasDerivAt (thetaCuspLikelihoodFirstTransportDenominator u)
      (thetaCuspLikelihoodSecondTransportDenominator u t) t := by
  have hplus := thetaCuspLikelihoodCoordinate_pos (show 0 ≤ u + t by linarith)
  have hminus := thetaCuspLikelihoodCoordinate_pos (show 0 ≤ u - t by linarith)
  have h1 := hasDerivAt_thetaCuspReflectedLikelihoodCumulantJetOne hplus hminus
  have h2 := hasDerivAt_thetaCuspReflectedLikelihoodCumulantJetTwo hplus hminus
  have hraw := h1.neg.sub ((hasDerivAt_id t).mul h2)
  refine (hraw.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun _ => rfl)).congr_deriv ?_
  simp only [id_eq]
  unfold thetaCuspLikelihoodSecondTransportDenominator
    thetaCuspReflectedLikelihoodCumulantJetTwo
    thetaCuspReflectedLikelihoodCumulantJetThree
  ring

theorem secondTransportDenominator_pos
    {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    0 < thetaCuspLikelihoodSecondTransportDenominator u t := by
  have hl0 : 0 ≤ u - t := by linarith
  have hr0 : 0 ≤ u + t := by linarith
  have ha := thetaCuspLikelihoodSourceLogPartitionJetTwo_pos hl0
  have hb := thetaCuspLikelihoodSourceLogPartitionJetTwo_pos hr0
  have hmono := strictMonoOn_thetaCuspLikelihoodSourceLogPartitionJetThree
    (show u - t ∈ Set.Ici (0 : ℝ) by exact Set.mem_Ici.mpr hl0)
    (show u + t ∈ Set.Ici (0 : ℝ) by exact Set.mem_Ici.mpr hr0)
    (by linarith : u - t < u + t)
  have hdiff : 0 <
      (-thetaCuspLikelihoodSourceLogPartitionJetThree (u - t)) -
        (-thetaCuspLikelihoodSourceLogPartitionJetThree (u + t)) := by linarith
  unfold thetaCuspLikelihoodSecondTransportDenominator
  exact add_pos_of_pos_of_nonneg (mul_pos (by norm_num) (add_pos ha hb))
    (mul_nonneg ht.le hdiff.le)

theorem secondTransportRatio_eq
    (u t : ℝ) :
    thetaCuspLikelihoodSecondTransportNumerator u t /
        thetaCuspLikelihoodSecondTransportDenominator u t =
      thetaCuspLikelihoodSecondTransportRatio u t := by
  unfold thetaCuspLikelihoodSecondTransportNumerator
    thetaCuspLikelihoodSecondTransportDenominator
    thetaCuspLikelihoodSecondTransportRatio
    c5LikelihoodScaleMixedJetTwo
  ring

theorem strictAntiOn_firstTransportRatio
    {u T : ℝ} (hT : 0 < T) (hTu : T ≤ u)
    (hscale : 6 ≤ thetaCuspSingleAtomReflectionScale 1 (u - T)) :
    StrictAntiOn
      (fun t => thetaCuspLikelihoodFirstTransportNumerator u t /
        thetaCuspLikelihoodFirstTransportDenominator u t)
      (Set.Ioc 0 T) := by
  let f := thetaCuspLikelihoodFirstTransportNumerator u
  let g := thetaCuspLikelihoodFirstTransportDenominator u
  let f' := thetaCuspLikelihoodSecondTransportNumerator u
  let g' := thetaCuspLikelihoodSecondTransportDenominator u
  have hfderiv : ∀ t ∈ Set.Icc (0 : ℝ) T, HasDerivAt f (f' t) t := by
    intro t ht
    exact hasDerivAt_firstTransportNumerator ht.1 (ht.2.trans hTu)
  have hgderiv : ∀ t ∈ Set.Icc (0 : ℝ) T, HasDerivAt g (g' t) t := by
    intro t ht
    exact hasDerivAt_firstTransportDenominator ht.1 (ht.2.trans hTu)
  have hfcont : ContinuousOn f (Set.Icc (0 : ℝ) T) := by
    intro t ht
    exact (hfderiv t ht).continuousAt.continuousWithinAt
  have hgcont : ContinuousOn g (Set.Icc (0 : ℝ) T) := by
    intro t ht
    exact (hgderiv t ht).continuousAt.continuousWithinAt
  have hg'pos : ∀ t ∈ Set.Ioc (0 : ℝ) T, 0 < g' t := by
    intro t ht
    exact secondTransportDenominator_pos ht.1 (ht.2.trans hTu)
  have hratio : StrictAntiOn (fun t => f' t / g' t) (Set.Ioc (0 : ℝ) T) := by
    have h := strictAntiOn_secondTransportRatio hT hTu hscale
    intro x hx y hy hxy
    change thetaCuspLikelihoodSecondTransportNumerator u y /
        thetaCuspLikelihoodSecondTransportDenominator u y <
      thetaCuspLikelihoodSecondTransportNumerator u x /
        thetaCuspLikelihoodSecondTransportDenominator u x
    rw [secondTransportRatio_eq, secondTransportRatio_eq]
    exact h ⟨hx.1.le, hx.2⟩ ⟨hy.1.le, hy.2⟩ hxy
  have hfa : f 0 = 0 := by
    unfold f thetaCuspLikelihoodFirstTransportNumerator
      c5LikelihoodScaleMixedJetOne
    ring_nf
  have hga : g 0 = 0 := by
    unfold g thetaCuspLikelihoodFirstTransportDenominator
      thetaCuspReflectedLikelihoodCumulantJetOne
      thetaCuspReflectedLikelihoodCumulantJetTwo
    ring_nf
  exact strictAntiOn_div_of_strictAnti_derivRatio hT hfa hga
    hfcont hgcont hfderiv hgderiv hg'pos hratio

def thetaCuspLikelihoodZerothTransportNumerator (u t : ℝ) : ℝ :=
  c5LikelihoodScaleActionJetOne u t

def thetaCuspLikelihoodZerothTransportDenominator (u t : ℝ) : ℝ :=
  -t * thetaCuspReflectedLikelihoodCumulantJetOne u t

theorem hasDerivAt_zerothTransportNumerator
    {u t : ℝ} (ht : 0 ≤ t) (htu : t ≤ u) :
    HasDerivAt (thetaCuspLikelihoodZerothTransportNumerator u)
      (thetaCuspLikelihoodFirstTransportNumerator u t) t := by
  have hl0 : 0 ≤ u - t := by linarith
  have hr0 : 0 ≤ u + t := by linarith
  have hl := (hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetOne
    (thetaCuspLikelihoodCoordinate_pos hl0)).comp t
      ((hasDerivAt_const t u).sub (hasDerivAt_id t))
  have hr := (hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetOne
    (thetaCuspLikelihoodCoordinate_pos hr0)).comp t
      ((hasDerivAt_const t u).add (hasDerivAt_id t))
  have hraw := (hasDerivAt_const t
    (2 * thetaCuspLikelihoodSourceLogPartitionJetOne u)).sub hr |>.sub hl
  refine (hraw.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun _ => rfl)).congr_deriv ?_
  unfold thetaCuspLikelihoodFirstTransportNumerator
    c5LikelihoodScaleMixedJetOne
  ring

theorem hasDerivAt_zerothTransportDenominator
    {u t : ℝ} (ht : 0 ≤ t) (htu : t ≤ u) :
    HasDerivAt (thetaCuspLikelihoodZerothTransportDenominator u)
      (thetaCuspLikelihoodFirstTransportDenominator u t) t := by
  have hplus := thetaCuspLikelihoodCoordinate_pos (show 0 ≤ u + t by linarith)
  have hminus := thetaCuspLikelihoodCoordinate_pos (show 0 ≤ u - t by linarith)
  have h1 := hasDerivAt_thetaCuspReflectedLikelihoodCumulantJetOne hplus hminus
  have hraw := ((hasDerivAt_id t).mul h1).neg
  have hfun : thetaCuspLikelihoodZerothTransportDenominator u =
      -(id * thetaCuspReflectedLikelihoodCumulantJetOne u) := by
    funext s
    unfold thetaCuspLikelihoodZerothTransportDenominator
    simp only [Pi.neg_apply, Pi.mul_apply, id_eq]
    ring
  rw [hfun]
  refine hraw.congr_deriv ?_
  unfold thetaCuspLikelihoodFirstTransportDenominator
  simp only [id_eq]
  ring

theorem firstTransportDenominator_pos
    {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    0 < thetaCuspLikelihoodFirstTransportDenominator u t := by
  have h1 := thetaCuspReflectedLikelihoodCumulantJetOne_neg ht htu
  have h2 := thetaCuspReflectedLikelihoodCumulantJetTwo_neg ht htu
  unfold thetaCuspLikelihoodFirstTransportDenominator
  have hmul : 0 < t * (-thetaCuspReflectedLikelihoodCumulantJetTwo u t) :=
    mul_pos ht (neg_pos.mpr h2)
  nlinarith

/-- **Lower-transport curvature closure.** The literal affine C5 likelihood homotopy has
strictly positive constant second lower-velocity transport throughout the structural chamber. -/
theorem thetaCuspC5LikelihoodHomotopy_velocityCenterTwo_pos
    {u t : ℝ} (ht : 0 < t) (htu : t ≤ u)
    (hscale : 6 ≤ thetaCuspSingleAtomReflectionScale 1 (u - t)) :
    0 < (thetaCuspC5LikelihoodHomotopyData u t).velocityCenterTwo := by
  let f := thetaCuspLikelihoodZerothTransportNumerator u
  let g := thetaCuspLikelihoodZerothTransportDenominator u
  let f' := thetaCuspLikelihoodFirstTransportNumerator u
  let g' := thetaCuspLikelihoodFirstTransportDenominator u
  have hfderiv : ∀ s ∈ Set.Icc (0 : ℝ) t, HasDerivAt f (f' s) s := by
    intro s hs
    exact hasDerivAt_zerothTransportNumerator hs.1 (hs.2.trans htu)
  have hgderiv : ∀ s ∈ Set.Icc (0 : ℝ) t, HasDerivAt g (g' s) s := by
    intro s hs
    exact hasDerivAt_zerothTransportDenominator hs.1 (hs.2.trans htu)
  have hfcont : ContinuousOn f (Set.Icc (0 : ℝ) t) := by
    intro s hs
    exact (hfderiv s hs).continuousAt.continuousWithinAt
  have hgcont : ContinuousOn g (Set.Icc (0 : ℝ) t) := by
    intro s hs
    exact (hgderiv s hs).continuousAt.continuousWithinAt
  have hg'pos : ∀ s ∈ Set.Ioc (0 : ℝ) t, 0 < g' s := by
    intro s hs
    exact firstTransportDenominator_pos hs.1 (hs.2.trans htu)
  have hratio : StrictAntiOn (fun s => f' s / g' s) (Set.Ioc (0 : ℝ) t) := by
    exact strictAntiOn_firstTransportRatio ht htu hscale
  have hfa : f 0 = 0 := by
    unfold f thetaCuspLikelihoodZerothTransportNumerator
      c5LikelihoodScaleActionJetOne
    ring_nf
  have hga : g 0 = 0 := by
    unfold g thetaCuspLikelihoodZerothTransportDenominator
    ring
  have hneg := div_derivativeNumerator_neg_of_strictAnti_derivRatio
    ht (show t ∈ Set.Ioc (0 : ℝ) t by exact ⟨ht, le_rfl⟩)
    hfa hga hfcont hgcont hfderiv hgderiv hg'pos hratio
  have hhalf : 0 <
      thetaCuspReflectedLikelihoodCumulantJetOne u t *
          (t * c5LikelihoodScaleMixedJetOne u t) -
        (thetaCuspReflectedLikelihoodCumulantJetOne u t +
          t * thetaCuspReflectedLikelihoodCumulantJetTwo u t) *
            c5LikelihoodScaleActionJetOne u t := by
    dsimp only [f, g, f', g',
      thetaCuspLikelihoodZerothTransportNumerator,
      thetaCuspLikelihoodZerothTransportDenominator,
      thetaCuspLikelihoodFirstTransportNumerator,
      thetaCuspLikelihoodFirstTransportDenominator] at hneg
    nlinarith
  unfold thetaCuspC5LikelihoodHomotopyData C5LikelihoodAffineData.velocityCenterTwo
  dsimp only
  nlinarith

end

end RHTower
