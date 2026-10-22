import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspLikelihoodSeventhEighthSourceJets
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspLikelihoodSixthScoreRayTransform

/-!
# Exact exponential-ray transform of the eighth likelihood score

The literal eighth source score is negative near the spectral support edge, so pointwise
positivity fails for the dominant `n = 2` theta component.  Its spectral carrier is not a point:
it is one Dirac mass plus one Lebesgue ray.  Exact incomplete-Laplace integration shows that the
combined point--ray mass is nevertheless strictly positive.  After clearing the positive ninth
power of `A - 3/2`, the dominant certificate has positive coefficients in `A - 157/50`.
-/

open MeasureTheory Set

namespace RHTower

noncomputable section

def thetaCuspLikelihoodEighthSourceScoreDerivOne (z : ℝ) : ℝ :=
  8 * z ^ 7 - 196 * z ^ 6 + 1596 * z ^ 5 - 5250 * z ^ 4 +
    6804 * z ^ 3 - 2898 * z ^ 2 + 254 * z - 1

def thetaCuspLikelihoodEighthSourceScoreDerivTwo (z : ℝ) : ℝ :=
  56 * z ^ 6 - 1176 * z ^ 5 + 7980 * z ^ 4 - 21000 * z ^ 3 +
    20412 * z ^ 2 - 5796 * z + 254

def thetaCuspLikelihoodEighthSourceScoreDerivThree (z : ℝ) : ℝ :=
  336 * z ^ 5 - 5880 * z ^ 4 + 31920 * z ^ 3 - 63000 * z ^ 2 +
    40824 * z - 5796

def thetaCuspLikelihoodEighthSourceScoreDerivFour (z : ℝ) : ℝ :=
  1680 * z ^ 4 - 23520 * z ^ 3 + 95760 * z ^ 2 - 126000 * z + 40824

def thetaCuspLikelihoodEighthSourceScoreDerivFive (z : ℝ) : ℝ :=
  6720 * z ^ 3 - 70560 * z ^ 2 + 191520 * z - 126000

def thetaCuspLikelihoodEighthSourceScoreDerivSix (z : ℝ) : ℝ :=
  20160 * z ^ 2 - 141120 * z + 191520

def thetaCuspLikelihoodEighthSourceScoreDerivSeven (z : ℝ) : ℝ :=
  40320 * z - 141120

def thetaCuspLikelihoodEighthSourceScoreDerivEight (_z : ℝ) : ℝ :=
  40320

/-- Finite Taylor operator produced by integrating the eighth score on an exponential ray. -/
def thetaCuspLikelihoodEighthSourceScoreRayTransform (r z : ℝ) : ℝ :=
  thetaCuspLikelihoodEighthSourceScore z +
    r * thetaCuspLikelihoodEighthSourceScoreDerivOne z +
    r ^ 2 * thetaCuspLikelihoodEighthSourceScoreDerivTwo z +
    r ^ 3 * thetaCuspLikelihoodEighthSourceScoreDerivThree z +
    r ^ 4 * thetaCuspLikelihoodEighthSourceScoreDerivFour z +
    r ^ 5 * thetaCuspLikelihoodEighthSourceScoreDerivFive z +
    r ^ 6 * thetaCuspLikelihoodEighthSourceScoreDerivSix z +
    r ^ 7 * thetaCuspLikelihoodEighthSourceScoreDerivSeven z +
    r ^ 8 * thetaCuspLikelihoodEighthSourceScoreDerivEight z

/-- Second exponential-ray Taylor operator.  The coefficient `k+1` is the exact extra factor
created by convolving two half-line rays. -/
def thetaCuspLikelihoodEighthSourceScoreDoubleRayTransform (r z : ℝ) : ℝ :=
  thetaCuspLikelihoodEighthSourceScore z +
    2 * r * thetaCuspLikelihoodEighthSourceScoreDerivOne z +
    3 * r ^ 2 * thetaCuspLikelihoodEighthSourceScoreDerivTwo z +
    4 * r ^ 3 * thetaCuspLikelihoodEighthSourceScoreDerivThree z +
    5 * r ^ 4 * thetaCuspLikelihoodEighthSourceScoreDerivFour z +
    6 * r ^ 5 * thetaCuspLikelihoodEighthSourceScoreDerivFive z +
    7 * r ^ 6 * thetaCuspLikelihoodEighthSourceScoreDerivSix z +
    8 * r ^ 7 * thetaCuspLikelihoodEighthSourceScoreDerivSeven z +
    9 * r ^ 8 * thetaCuspLikelihoodEighthSourceScoreDerivEight z

/-- Exponential-ray Taylor transform of the leading eighth monomial. -/
def thetaCuspLikelihoodEighthMonomialRayTransform (r z : ℝ) : ℝ :=
  z ^ 8 + 8 * r * z ^ 7 + 56 * r ^ 2 * z ^ 6 +
    336 * r ^ 3 * z ^ 5 + 1680 * r ^ 4 * z ^ 4 +
    6720 * r ^ 5 * z ^ 3 + 20160 * r ^ 6 * z ^ 2 +
    40320 * r ^ 7 * z + 40320 * r ^ 8

/-- Every Taylor coefficient is nonnegative in the stable spectral chamber `z ≥ 24`. -/
theorem thetaCuspLikelihoodEighthSourceScoreRayTransform_nonneg_of_twentyFour_le
    {r z : ℝ} (hr : 0 ≤ r) (hz : 24 ≤ z) :
    0 ≤ thetaCuspLikelihoodEighthSourceScoreRayTransform r z := by
  let s := z - 24
  have hs : 0 ≤ s := by
    dsimp only [s]
    linarith
  rw [show z = 24 + s by dsimp only [s]; ring]
  dsimp [thetaCuspLikelihoodEighthSourceScoreRayTransform,
    thetaCuspLikelihoodEighthSourceScore,
    thetaCuspLikelihoodEighthSourceScoreDerivOne,
    thetaCuspLikelihoodEighthSourceScoreDerivTwo,
    thetaCuspLikelihoodEighthSourceScoreDerivThree,
    thetaCuspLikelihoodEighthSourceScoreDerivFour,
    thetaCuspLikelihoodEighthSourceScoreDerivFive,
    thetaCuspLikelihoodEighthSourceScoreDerivSix,
    thetaCuspLikelihoodEighthSourceScoreDerivSeven,
    thetaCuspLikelihoodEighthSourceScoreDerivEight]
  ring_nf
  positivity

/-- In the stable chamber, at least one hundredth of the leading eighth-moment transform
survives the signed source score. -/
theorem one_hundredth_mul_thetaCuspLikelihoodEighthMonomialRayTransform_le
    {r z : ℝ} (hr : 0 ≤ r) (hz : 24 ≤ z) :
    (1 / 100 : ℝ) * thetaCuspLikelihoodEighthMonomialRayTransform r z ≤
      thetaCuspLikelihoodEighthSourceScoreRayTransform r z := by
  let s := z - 24
  have hs : 0 ≤ s := by
    dsimp only [s]
    linarith
  rw [show z = 24 + s by dsimp only [s]; ring]
  unfold thetaCuspLikelihoodEighthSourceScoreRayTransform
    thetaCuspLikelihoodEighthMonomialRayTransform
    thetaCuspLikelihoodEighthSourceScore
    thetaCuspLikelihoodEighthSourceScoreDerivOne
    thetaCuspLikelihoodEighthSourceScoreDerivTwo
    thetaCuspLikelihoodEighthSourceScoreDerivThree
    thetaCuspLikelihoodEighthSourceScoreDerivFour
    thetaCuspLikelihoodEighthSourceScoreDerivFive
    thetaCuspLikelihoodEighthSourceScoreDerivSix
    thetaCuspLikelihoodEighthSourceScoreDerivSeven
    thetaCuspLikelihoodEighthSourceScoreDerivEight
  apply sub_nonneg.mp
  ring_nf
  positivity

/-- In the stable chamber, one thirtieth of the leading eighth-moment transform survives.
This is the strongest simple reciprocal certificate shared with the dominant gap-three ray. -/
theorem one_thirtieth_mul_thetaCuspLikelihoodEighthMonomialRayTransform_le
    {r z : ℝ} (hr : 0 ≤ r) (hz : 24 ≤ z) :
    (1 / 30 : ℝ) * thetaCuspLikelihoodEighthMonomialRayTransform r z ≤
      thetaCuspLikelihoodEighthSourceScoreRayTransform r z := by
  let s := z - 24
  have hs : 0 ≤ s := by
    dsimp only [s]
    linarith
  rw [show z = 24 + s by dsimp only [s]; ring]
  unfold thetaCuspLikelihoodEighthSourceScoreRayTransform
    thetaCuspLikelihoodEighthMonomialRayTransform
    thetaCuspLikelihoodEighthSourceScore
    thetaCuspLikelihoodEighthSourceScoreDerivOne
    thetaCuspLikelihoodEighthSourceScoreDerivTwo
    thetaCuspLikelihoodEighthSourceScoreDerivThree
    thetaCuspLikelihoodEighthSourceScoreDerivFour
    thetaCuspLikelihoodEighthSourceScoreDerivFive
    thetaCuspLikelihoodEighthSourceScoreDerivSix
    thetaCuspLikelihoodEighthSourceScoreDerivSeven
    thetaCuspLikelihoodEighthSourceScoreDerivEight
  apply sub_nonneg.mp
  ring_nf
  positivity

private theorem integrableOn_pow_mul_exp_neg_rate_eighth
    (n : ℕ) {B : ℝ} (hB : 0 < B) :
    IntegrableOn (fun u : ℝ => u ^ n * Real.exp (-(B * u))) (Ioi 0) := by
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hn : (-1 : ℝ) < (n : ℝ) := by linarith
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow
    (p := (1 : ℝ)) (s := (n : ℝ)) (b := B) hn (by norm_num) hB
  convert h using 1
  funext u
  simp only [Real.rpow_one]
  rw [Real.rpow_natCast]
  congr 1
  ring_nf

private theorem setIntegral_Ioi_comp_add_right_eighth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℝ → E) (a h : ℝ) :
    (∫ y in Ioi (a - h), F (y + h)) = ∫ x in Ioi a, F x := by
  have hmp : MeasurePreserving (fun y : ℝ => y + h) volume volume :=
    measurePreserving_add_right volume h
  have hemb : MeasurableEmbedding (fun y : ℝ => y + h) :=
    measurableEmbedding_addRight h
  have hpre : (fun y : ℝ => y + h) ⁻¹' Ioi a = Ioi (a - h) := by
    ext y
    simp [Set.mem_Ioi, sub_lt_iff_lt_add]
  have h1 := hmp.setIntegral_preimage_emb hemb F (Ioi a)
  rw [hpre] at h1
  exact h1

/-- The literal eighth score is integrable on every nonnegative positive-rate ray. -/
theorem integrableOn_thetaCuspLikelihoodEighthSourceScore_mul_exp_neg_rate
    (A : ℝ) {d B : ℝ} (hd : 0 ≤ d) (hB : 0 < B) :
    IntegrableOn (fun t : ℝ =>
      thetaCuspLikelihoodEighthSourceScore (A * t) * Real.exp (-(B * t)))
      (Ioi d) := by
  have hmono (m : ℕ) :
      IntegrableOn (fun t : ℝ => t ^ m * Real.exp (-(B * t))) (Ioi d) :=
    (integrableOn_pow_mul_exp_neg_rate_eighth m hB).mono_set fun t ht =>
      lt_of_le_of_lt hd ht
  have h8 := (hmono 8).const_mul (A ^ 8)
  have h7 := (hmono 7).const_mul (28 * A ^ 7)
  have h6 := (hmono 6).const_mul (266 * A ^ 6)
  have h5 := (hmono 5).const_mul (1050 * A ^ 5)
  have h4 := (hmono 4).const_mul (1701 * A ^ 4)
  have h3 := (hmono 3).const_mul (966 * A ^ 3)
  have h2 := (hmono 2).const_mul (127 * A ^ 2)
  have h1 := (hmono 1).const_mul A
  change Integrable (fun t : ℝ =>
    thetaCuspLikelihoodEighthSourceScore (A * t) * Real.exp (-(B * t)))
      (volume.restrict (Ioi d))
  have hsum := (((((((h8.sub h7).add h6).sub h5).add h4).sub h3).add h2).sub h1)
  convert hsum using 1
  funext t
  simp only [Pi.add_apply, Pi.sub_apply]
  unfold thetaCuspLikelihoodEighthSourceScore
  ring

/-- Exact incomplete-Laplace transform of the literal eighth score. -/
theorem integral_Ioi_thetaCuspLikelihoodEighthSourceScore_mul_exp_neg_rate
    (A d : ℝ) {B : ℝ} (hB : 0 < B) :
    (∫ t : ℝ in Ioi d,
      thetaCuspLikelihoodEighthSourceScore (A * t) * Real.exp (-(B * t))) =
      Real.exp (-(B * d)) / B *
        thetaCuspLikelihoodEighthSourceScoreRayTransform (A / B) (A * d) := by
  let z := A * d
  let c : ℕ → ℝ := fun k =>
    match k with
    | 0 => thetaCuspLikelihoodEighthSourceScore z
    | 1 => A * thetaCuspLikelihoodEighthSourceScoreDerivOne z
    | 2 => A ^ 2 * thetaCuspLikelihoodEighthSourceScoreDerivTwo z / 2
    | 3 => A ^ 3 * thetaCuspLikelihoodEighthSourceScoreDerivThree z / 6
    | 4 => A ^ 4 * thetaCuspLikelihoodEighthSourceScoreDerivFour z / 24
    | 5 => A ^ 5 * thetaCuspLikelihoodEighthSourceScoreDerivFive z / 120
    | 6 => A ^ 6 * thetaCuspLikelihoodEighthSourceScoreDerivSix z / 720
    | 7 => A ^ 7 * thetaCuspLikelihoodEighthSourceScoreDerivSeven z / 5040
    | 8 => A ^ 8 * thetaCuspLikelihoodEighthSourceScoreDerivEight z / 40320
    | _ => 0
  have htrans := setIntegral_Ioi_comp_add_right_eighth
    (fun t : ℝ => thetaCuspLikelihoodEighthSourceScore (A * t) *
      Real.exp (-(B * t))) d d
  rw [sub_self] at htrans
  rw [← htrans]
  have hfun : (fun u : ℝ =>
      thetaCuspLikelihoodEighthSourceScore (A * (u + d)) *
        Real.exp (-(B * (u + d)))) =
      fun u => Real.exp (-(B * d)) *
        (∑ k ∈ Finset.range 9, c k * (u ^ k * Real.exp (-(B * u)))) := by
    funext u
    have hexp : Real.exp (-(B * (u + d))) =
        Real.exp (-(B * d)) * Real.exp (-(B * u)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hexp]
    norm_num [Finset.sum_range_succ, c]
    dsimp [z, thetaCuspLikelihoodEighthSourceScore,
      thetaCuspLikelihoodEighthSourceScoreDerivOne,
      thetaCuspLikelihoodEighthSourceScoreDerivTwo,
      thetaCuspLikelihoodEighthSourceScoreDerivThree,
      thetaCuspLikelihoodEighthSourceScoreDerivFour,
      thetaCuspLikelihoodEighthSourceScoreDerivFive,
      thetaCuspLikelihoodEighthSourceScoreDerivSix,
      thetaCuspLikelihoodEighthSourceScoreDerivSeven,
      thetaCuspLikelihoodEighthSourceScoreDerivEight]
    ring
  rw [hfun, integral_const_mul, integral_finsetSum]
  · have hI0 : (∫ u : ℝ in Ioi 0, Real.exp (-(B * u))) = 1 / B := by
      simpa using integral_Ioi_pow_mul_exp_neg_rate 0 hB
    have hI1 : (∫ u : ℝ in Ioi 0, u * Real.exp (-(B * u))) = 1 / B ^ 2 := by
      simpa using integral_Ioi_pow_mul_exp_neg_rate 1 hB
    simp only [integral_const_mul]
    norm_num [Finset.sum_range_succ, c, hI0, hI1,
      integral_Ioi_pow_mul_exp_neg_rate 0 hB,
      integral_Ioi_pow_mul_exp_neg_rate 1 hB,
      integral_Ioi_pow_mul_exp_neg_rate 2 hB,
      integral_Ioi_pow_mul_exp_neg_rate 3 hB,
      integral_Ioi_pow_mul_exp_neg_rate 4 hB,
      integral_Ioi_pow_mul_exp_neg_rate 5 hB,
      integral_Ioi_pow_mul_exp_neg_rate 6 hB,
      integral_Ioi_pow_mul_exp_neg_rate 7 hB,
      integral_Ioi_pow_mul_exp_neg_rate 8 hB]
    dsimp [thetaCuspLikelihoodEighthSourceScoreRayTransform, z]
    field_simp [hB.ne']
  · intro k hk
    exact (integrableOn_pow_mul_exp_neg_rate_eighth k hB).const_mul _

/-- Exact incomplete-Laplace transform with one ray-convolution length.  This is the analytic
identity behind the ray--ray sector of the two-particle eighth score. -/
theorem integral_Ioi_sub_mul_thetaCuspLikelihoodEighthSourceScore_mul_exp_neg_rate
    (A d : ℝ) {B : ℝ} (hB : 0 < B) :
    (∫ t : ℝ in Ioi d, (t - d) * thetaCuspLikelihoodEighthSourceScore (A * t) *
        Real.exp (-(B * t))) =
      Real.exp (-(B * d)) / B ^ 2 *
        thetaCuspLikelihoodEighthSourceScoreDoubleRayTransform (A / B) (A * d) := by
  let z := A * d
  let c : ℕ → ℝ := fun k =>
    match k with
    | 0 => thetaCuspLikelihoodEighthSourceScore z
    | 1 => A * thetaCuspLikelihoodEighthSourceScoreDerivOne z
    | 2 => A ^ 2 * thetaCuspLikelihoodEighthSourceScoreDerivTwo z / 2
    | 3 => A ^ 3 * thetaCuspLikelihoodEighthSourceScoreDerivThree z / 6
    | 4 => A ^ 4 * thetaCuspLikelihoodEighthSourceScoreDerivFour z / 24
    | 5 => A ^ 5 * thetaCuspLikelihoodEighthSourceScoreDerivFive z / 120
    | 6 => A ^ 6 * thetaCuspLikelihoodEighthSourceScoreDerivSix z / 720
    | 7 => A ^ 7 * thetaCuspLikelihoodEighthSourceScoreDerivSeven z / 5040
    | 8 => A ^ 8 * thetaCuspLikelihoodEighthSourceScoreDerivEight z / 40320
    | _ => 0
  have htrans := setIntegral_Ioi_comp_add_right_eighth
    (fun t : ℝ => (t - d) * thetaCuspLikelihoodEighthSourceScore (A * t) *
      Real.exp (-(B * t))) d d
  rw [sub_self] at htrans
  rw [← htrans]
  have hfun : (fun u : ℝ =>
      (u + d - d) * thetaCuspLikelihoodEighthSourceScore (A * (u + d)) *
        Real.exp (-(B * (u + d)))) =
      fun u => Real.exp (-(B * d)) *
        (∑ k ∈ Finset.range 9, c k * (u ^ (k + 1) * Real.exp (-(B * u)))) := by
    funext u
    have hexp : Real.exp (-(B * (u + d))) =
        Real.exp (-(B * d)) * Real.exp (-(B * u)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hexp]
    norm_num [Finset.sum_range_succ, c]
    dsimp [z, thetaCuspLikelihoodEighthSourceScore,
      thetaCuspLikelihoodEighthSourceScoreDerivOne,
      thetaCuspLikelihoodEighthSourceScoreDerivTwo,
      thetaCuspLikelihoodEighthSourceScoreDerivThree,
      thetaCuspLikelihoodEighthSourceScoreDerivFour,
      thetaCuspLikelihoodEighthSourceScoreDerivFive,
      thetaCuspLikelihoodEighthSourceScoreDerivSix,
      thetaCuspLikelihoodEighthSourceScoreDerivSeven,
      thetaCuspLikelihoodEighthSourceScoreDerivEight]
    ring
  rw [hfun, integral_const_mul, integral_finsetSum]
  · have hI1 : (∫ u : ℝ in Ioi 0, u * Real.exp (-(B * u))) = 1 / B ^ 2 := by
      simpa using integral_Ioi_pow_mul_exp_neg_rate 1 hB
    simp only [integral_const_mul]
    norm_num [Finset.sum_range_succ, c, hI1,
      integral_Ioi_pow_mul_exp_neg_rate 1 hB,
      integral_Ioi_pow_mul_exp_neg_rate 2 hB,
      integral_Ioi_pow_mul_exp_neg_rate 3 hB,
      integral_Ioi_pow_mul_exp_neg_rate 4 hB,
      integral_Ioi_pow_mul_exp_neg_rate 5 hB,
      integral_Ioi_pow_mul_exp_neg_rate 6 hB,
      integral_Ioi_pow_mul_exp_neg_rate 7 hB,
      integral_Ioi_pow_mul_exp_neg_rate 8 hB,
      integral_Ioi_pow_mul_exp_neg_rate 9 hB]
    dsimp [thetaCuspLikelihoodEighthSourceScoreDoubleRayTransform, z]
    field_simp [hB.ne']
    ring
  · intro k hk
    exact (integrableOn_pow_mul_exp_neg_rate_eighth (k + 1) hB).const_mul _

/-- Exact incomplete-Laplace transform of the leading eighth monomial. -/
theorem integral_Ioi_thetaCuspLikelihoodEighthMonomial_mul_exp_neg_rate
    (A d : ℝ) {B : ℝ} (hB : 0 < B) :
    (∫ t : ℝ in Ioi d, (A * t) ^ 8 * Real.exp (-(B * t))) =
      Real.exp (-(B * d)) / B *
        thetaCuspLikelihoodEighthMonomialRayTransform (A / B) (A * d) := by
  let z := A * d
  let c : ℕ → ℝ := fun k =>
    match k with
    | 0 => z ^ 8
    | 1 => 8 * A * z ^ 7
    | 2 => 28 * A ^ 2 * z ^ 6
    | 3 => 56 * A ^ 3 * z ^ 5
    | 4 => 70 * A ^ 4 * z ^ 4
    | 5 => 56 * A ^ 5 * z ^ 3
    | 6 => 28 * A ^ 6 * z ^ 2
    | 7 => 8 * A ^ 7 * z
    | 8 => A ^ 8
    | _ => 0
  have htrans := setIntegral_Ioi_comp_add_right_eighth
    (fun t : ℝ => (A * t) ^ 8 * Real.exp (-(B * t))) d d
  rw [sub_self] at htrans
  rw [← htrans]
  have hfun : (fun u : ℝ =>
      (A * (u + d)) ^ 8 * Real.exp (-(B * (u + d)))) =
      fun u => Real.exp (-(B * d)) *
        (∑ k ∈ Finset.range 9, c k * (u ^ k * Real.exp (-(B * u)))) := by
    funext u
    have hexp : Real.exp (-(B * (u + d))) =
        Real.exp (-(B * d)) * Real.exp (-(B * u)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hexp]
    norm_num [Finset.sum_range_succ, c]
    dsimp only [z]
    ring
  rw [hfun, integral_const_mul, integral_finsetSum]
  · have hI0 : (∫ u : ℝ in Ioi 0, Real.exp (-(B * u))) = 1 / B := by
      simpa using integral_Ioi_pow_mul_exp_neg_rate 0 hB
    have hI1 : (∫ u : ℝ in Ioi 0, u * Real.exp (-(B * u))) = 1 / B ^ 2 := by
      simpa using integral_Ioi_pow_mul_exp_neg_rate 1 hB
    simp only [integral_const_mul]
    norm_num [Finset.sum_range_succ, c, hI0, hI1,
      integral_Ioi_pow_mul_exp_neg_rate 0 hB,
      integral_Ioi_pow_mul_exp_neg_rate 1 hB,
      integral_Ioi_pow_mul_exp_neg_rate 2 hB,
      integral_Ioi_pow_mul_exp_neg_rate 3 hB,
      integral_Ioi_pow_mul_exp_neg_rate 4 hB,
      integral_Ioi_pow_mul_exp_neg_rate 5 hB,
      integral_Ioi_pow_mul_exp_neg_rate 6 hB,
      integral_Ioi_pow_mul_exp_neg_rate 7 hB,
      integral_Ioi_pow_mul_exp_neg_rate 8 hB]
    dsimp [thetaCuspLikelihoodEighthMonomialRayTransform, z]
    field_simp [hB.ne']
    ring
  · intro k hk
    exact (integrableOn_pow_mul_exp_neg_rate_eighth k hB).const_mul _

set_option maxRecDepth 10000 in
/-- Exact point--ray compensation: the dominant gap-three component has positive eighth score
mass throughout the physical source chamber, although its point score is negative near the seam. -/
theorem thetaCuspLikelihoodDominantEighthScoreCore_pos
    {A : ℝ} (hA : (157 / 50 : ℝ) ≤ A) :
    0 < 16 * thetaCuspLikelihoodEighthSourceScore (3 * A) +
      18 / (A - 3 / 2) *
        thetaCuspLikelihoodEighthSourceScoreRayTransform
          (A / (A - 3 / 2)) (3 * A) := by
  let B := A - 3 / 2
  have hB : 0 < B := by
    dsimp only [B]
    linarith
  let s := A - 157 / 50
  have hs : 0 ≤ s := by
    dsimp only [s]
    linarith
  let E := 16 * thetaCuspLikelihoodEighthSourceScore (3 * A) +
    18 / B * thetaCuspLikelihoodEighthSourceScoreRayTransform (A / B) (3 * A)
  have hmul : 0 < B ^ 9 * E := by
    dsimp only [E]
    unfold thetaCuspLikelihoodEighthSourceScoreRayTransform
      thetaCuspLikelihoodEighthSourceScore
      thetaCuspLikelihoodEighthSourceScoreDerivOne
      thetaCuspLikelihoodEighthSourceScoreDerivTwo
      thetaCuspLikelihoodEighthSourceScoreDerivThree
      thetaCuspLikelihoodEighthSourceScoreDerivFour
      thetaCuspLikelihoodEighthSourceScoreDerivFive
      thetaCuspLikelihoodEighthSourceScoreDerivSix
      thetaCuspLikelihoodEighthSourceScoreDerivSeven
      thetaCuspLikelihoodEighthSourceScoreDerivEight
    field_simp [hB.ne']
    dsimp only [B]
    rw [show A = 157 / 50 + s by dsimp only [s]; ring]
    ring_nf
    positivity
  dsimp only [E, B] at hmul
  exact pos_of_mul_pos_right hmul (pow_nonneg hB.le 9)

set_option maxRecDepth 10000 in
/-- Quantitative point--ray compensation: the dominant score retains more than one hundredth of
its leading eighth-moment mass on the whole physical chamber. -/
theorem one_hundredth_mul_thetaCuspLikelihoodDominantEighthMomentCore_lt
    {A : ℝ} (hA : (157 / 50 : ℝ) ≤ A) :
    (1 / 100 : ℝ) *
        (16 * (3 * A) ^ 8 + 18 / (A - 3 / 2) *
          thetaCuspLikelihoodEighthMonomialRayTransform
            (A / (A - 3 / 2)) (3 * A)) <
      16 * thetaCuspLikelihoodEighthSourceScore (3 * A) +
        18 / (A - 3 / 2) *
          thetaCuspLikelihoodEighthSourceScoreRayTransform
            (A / (A - 3 / 2)) (3 * A) := by
  let B := A - 3 / 2
  have hB : 0 < B := by
    dsimp only [B]
    linarith
  let s := A - 157 / 50
  have hs : 0 ≤ s := by
    dsimp only [s]
    linarith
  let E := 16 * thetaCuspLikelihoodEighthSourceScore (3 * A) +
      18 / B * thetaCuspLikelihoodEighthSourceScoreRayTransform (A / B) (3 * A) -
    (1 / 100 : ℝ) * (16 * (3 * A) ^ 8 + 18 / B *
      thetaCuspLikelihoodEighthMonomialRayTransform (A / B) (3 * A))
  have hmul : 0 < B ^ 9 * E := by
    dsimp only [E]
    unfold thetaCuspLikelihoodEighthSourceScoreRayTransform
      thetaCuspLikelihoodEighthMonomialRayTransform
      thetaCuspLikelihoodEighthSourceScore
      thetaCuspLikelihoodEighthSourceScoreDerivOne
      thetaCuspLikelihoodEighthSourceScoreDerivTwo
      thetaCuspLikelihoodEighthSourceScoreDerivThree
      thetaCuspLikelihoodEighthSourceScoreDerivFour
      thetaCuspLikelihoodEighthSourceScoreDerivFive
      thetaCuspLikelihoodEighthSourceScoreDerivSix
      thetaCuspLikelihoodEighthSourceScoreDerivSeven
      thetaCuspLikelihoodEighthSourceScoreDerivEight
    field_simp [hB.ne']
    dsimp only [B]
    rw [show A = 157 / 50 + s by dsimp only [s]; ring]
    ring_nf
    positivity
  dsimp only [E, B] at hmul
  have hE : 0 < E := pos_of_mul_pos_right hmul (pow_nonneg hB.le 9)
  dsimp only [E, B] at hE
  linarith

set_option maxRecDepth 10000 in
/-- Quantitative point--ray compensation at the common sharp reciprocal: the dominant
gap-three component retains more than one thirtieth of leading eighth-moment mass. -/
theorem one_thirtieth_mul_thetaCuspLikelihoodDominantEighthMomentCore_lt
    {A : ℝ} (hA : (157 / 50 : ℝ) ≤ A) :
    (1 / 30 : ℝ) *
        (16 * (3 * A) ^ 8 + 18 / (A - 3 / 2) *
          thetaCuspLikelihoodEighthMonomialRayTransform
            (A / (A - 3 / 2)) (3 * A)) <
      16 * thetaCuspLikelihoodEighthSourceScore (3 * A) +
        18 / (A - 3 / 2) *
          thetaCuspLikelihoodEighthSourceScoreRayTransform
            (A / (A - 3 / 2)) (3 * A) := by
  let B := A - 3 / 2
  have hB : 0 < B := by
    dsimp only [B]
    linarith
  let s := A - 157 / 50
  have hs : 0 ≤ s := by
    dsimp only [s]
    linarith
  let E := 16 * thetaCuspLikelihoodEighthSourceScore (3 * A) +
      18 / B * thetaCuspLikelihoodEighthSourceScoreRayTransform (A / B) (3 * A) -
    (1 / 30 : ℝ) * (16 * (3 * A) ^ 8 + 18 / B *
      thetaCuspLikelihoodEighthMonomialRayTransform (A / B) (3 * A))
  have hmul : 0 < B ^ 9 * E := by
    dsimp only [E]
    unfold thetaCuspLikelihoodEighthSourceScoreRayTransform
      thetaCuspLikelihoodEighthMonomialRayTransform
      thetaCuspLikelihoodEighthSourceScore
      thetaCuspLikelihoodEighthSourceScoreDerivOne
      thetaCuspLikelihoodEighthSourceScoreDerivTwo
      thetaCuspLikelihoodEighthSourceScoreDerivThree
      thetaCuspLikelihoodEighthSourceScoreDerivFour
      thetaCuspLikelihoodEighthSourceScoreDerivFive
      thetaCuspLikelihoodEighthSourceScoreDerivSix
      thetaCuspLikelihoodEighthSourceScoreDerivSeven
      thetaCuspLikelihoodEighthSourceScoreDerivEight
    field_simp [hB.ne']
    dsimp only [B]
    rw [show A = 157 / 50 + s by dsimp only [s]; ring]
    ring_nf
    positivity
  dsimp only [E, B] at hmul
  have hE : 0 < E := pos_of_mul_pos_right hmul (pow_nonneg hB.le 9)
  dsimp only [E, B] at hE
  linarith

end

end RHTower
