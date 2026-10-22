import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspLikelihoodHighCumulantCalibration

/-!
# Seventh and eighth theta likelihood cumulants

The higher theta-tail likelihood has mass below `1/400`.  All-pairs spectral moment domination
iterates to four-, six-, and eight-fold products, so every negative even-grade term in the
eighth moment--cumulant formula has a common `m₈` budget.  The exact budget is below `1/3`,
leaving the strict quantitative law `κ₈ > (2/3) m₈`.
-/

namespace RHTower

noncomputable section

/-- Seventh cumulant of the normalized higher-tail likelihood state. -/
def thetaCuspLikelihoodSeventhCumulant (B : ℝ) : ℝ :=
  thetaCuspLikelihoodNormalizedMoment B 7 -
    7 * thetaCuspLikelihoodMean B * thetaCuspLikelihoodNormalizedMoment B 6 -
    21 * thetaCuspLikelihoodNormalizedMoment B 2 * thetaCuspLikelihoodNormalizedMoment B 5 -
    35 * thetaCuspLikelihoodNormalizedMoment B 3 * thetaCuspLikelihoodNormalizedMoment B 4 +
    42 * thetaCuspLikelihoodMean B ^ (2 : ℕ) * thetaCuspLikelihoodNormalizedMoment B 5 +
    210 * thetaCuspLikelihoodMean B * thetaCuspLikelihoodNormalizedMoment B 2 *
      thetaCuspLikelihoodNormalizedMoment B 4 +
    140 * thetaCuspLikelihoodMean B * thetaCuspLikelihoodNormalizedMoment B 3 ^ (2 : ℕ) +
    210 * thetaCuspLikelihoodNormalizedMoment B 2 ^ (2 : ℕ) *
      thetaCuspLikelihoodNormalizedMoment B 3 -
    210 * thetaCuspLikelihoodMean B ^ (3 : ℕ) * thetaCuspLikelihoodNormalizedMoment B 4 -
    1260 * thetaCuspLikelihoodMean B ^ (2 : ℕ) * thetaCuspLikelihoodNormalizedMoment B 2 *
      thetaCuspLikelihoodNormalizedMoment B 3 -
    630 * thetaCuspLikelihoodMean B * thetaCuspLikelihoodNormalizedMoment B 2 ^ (3 : ℕ) +
    840 * thetaCuspLikelihoodMean B ^ (4 : ℕ) * thetaCuspLikelihoodNormalizedMoment B 3 +
    2520 * thetaCuspLikelihoodMean B ^ (3 : ℕ) * thetaCuspLikelihoodNormalizedMoment B 2 ^ (2 : ℕ) -
    2520 * thetaCuspLikelihoodMean B ^ (5 : ℕ) * thetaCuspLikelihoodNormalizedMoment B 2 +
    720 * thetaCuspLikelihoodMean B ^ (7 : ℕ)

/-- Eighth cumulant of the normalized higher-tail likelihood state. -/
def thetaCuspLikelihoodEighthCumulant (B : ℝ) : ℝ :=
  thetaCuspLikelihoodNormalizedMoment B 8 -
    8 * thetaCuspLikelihoodMean B * thetaCuspLikelihoodNormalizedMoment B 7 -
    28 * thetaCuspLikelihoodNormalizedMoment B 2 * thetaCuspLikelihoodNormalizedMoment B 6 -
    56 * thetaCuspLikelihoodNormalizedMoment B 3 * thetaCuspLikelihoodNormalizedMoment B 5 -
    35 * thetaCuspLikelihoodNormalizedMoment B 4 ^ (2 : ℕ) +
    56 * thetaCuspLikelihoodMean B ^ (2 : ℕ) * thetaCuspLikelihoodNormalizedMoment B 6 +
    336 * thetaCuspLikelihoodMean B * thetaCuspLikelihoodNormalizedMoment B 2 *
      thetaCuspLikelihoodNormalizedMoment B 5 +
    560 * thetaCuspLikelihoodMean B * thetaCuspLikelihoodNormalizedMoment B 3 *
      thetaCuspLikelihoodNormalizedMoment B 4 +
    420 * thetaCuspLikelihoodNormalizedMoment B 2 ^ (2 : ℕ) *
      thetaCuspLikelihoodNormalizedMoment B 4 +
    560 * thetaCuspLikelihoodNormalizedMoment B 2 *
      thetaCuspLikelihoodNormalizedMoment B 3 ^ (2 : ℕ) -
    336 * thetaCuspLikelihoodMean B ^ (3 : ℕ) * thetaCuspLikelihoodNormalizedMoment B 5 -
    2520 * thetaCuspLikelihoodMean B ^ (2 : ℕ) * thetaCuspLikelihoodNormalizedMoment B 2 *
      thetaCuspLikelihoodNormalizedMoment B 4 -
    1680 * thetaCuspLikelihoodMean B ^ (2 : ℕ) * thetaCuspLikelihoodNormalizedMoment B 3 ^ (2 : ℕ) -
    5040 * thetaCuspLikelihoodMean B * thetaCuspLikelihoodNormalizedMoment B 2 ^ (2 : ℕ) *
      thetaCuspLikelihoodNormalizedMoment B 3 -
    630 * thetaCuspLikelihoodNormalizedMoment B 2 ^ (4 : ℕ) +
    1680 * thetaCuspLikelihoodMean B ^ (4 : ℕ) * thetaCuspLikelihoodNormalizedMoment B 4 +
    13440 * thetaCuspLikelihoodMean B ^ (3 : ℕ) * thetaCuspLikelihoodNormalizedMoment B 2 *
      thetaCuspLikelihoodNormalizedMoment B 3 +
    10080 * thetaCuspLikelihoodMean B ^ (2 : ℕ) * thetaCuspLikelihoodNormalizedMoment B 2 ^ (3 : ℕ) -
    6720 * thetaCuspLikelihoodMean B ^ (5 : ℕ) * thetaCuspLikelihoodNormalizedMoment B 3 -
    25200 * thetaCuspLikelihoodMean B ^ (4 : ℕ) * thetaCuspLikelihoodNormalizedMoment B 2 ^ (2 : ℕ) +
    20160 * thetaCuspLikelihoodMean B ^ (6 : ℕ) * thetaCuspLikelihoodNormalizedMoment B 2 -
    5040 * thetaCuspLikelihoodMean B ^ (8 : ℕ)

/-- Sixth cumulant differentiates to negative seventh cumulant under likelihood cooling. -/
theorem hasDerivAt_thetaCuspLikelihoodSixthCumulant {B : ℝ} (hB : 0 < B) :
    HasDerivAt thetaCuspLikelihoodSixthCumulant (-thetaCuspLikelihoodSeventhCumulant B) B := by
  have hm := hasDerivAt_thetaCuspLikelihoodMean hB
  have he2 := hasDerivAt_thetaCuspLikelihoodNormalizedMoment hB 2
  have he3 := hasDerivAt_thetaCuspLikelihoodNormalizedMoment hB 3
  have he4 := hasDerivAt_thetaCuspLikelihoodNormalizedMoment hB 4
  have he5 := hasDerivAt_thetaCuspLikelihoodNormalizedMoment hB 5
  have he6 := hasDerivAt_thetaCuspLikelihoodNormalizedMoment hB 6
  unfold thetaCuspLikelihoodSixthCumulant thetaCuspLikelihoodSeventhCumulant
  convert ((((((((((he6.sub ((hm.mul he5).const_mul 6)).sub
    ((he2.mul he4).const_mul 15)).sub ((he3.pow 2).const_mul 10)).add
    (((hm.pow 2).mul he4).const_mul 30)).add
    (((hm.mul he2).mul he3).const_mul 120)).sub
    (((hm.pow 3).mul he3).const_mul 120)).add
    ((he2.pow 3).const_mul 30)).sub
    (((hm.pow 2).mul (he2.pow 2)).const_mul 270)).add
    (((hm.pow 4).mul he2).const_mul 360)).sub
    ((hm.pow 6).const_mul 120)) using 1
  any_goals rfl
  · funext q
    simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply]
    ring
  · simp only [Nat.reduceAdd,
      thetaCuspLikelihoodVariance_eq_normalizedMoment_two_sub_mean_sq,
      Pi.mul_apply, Pi.pow_apply]
    ring

/-- Seventh cumulant differentiates to negative eighth cumulant under likelihood cooling. -/
theorem hasDerivAt_thetaCuspLikelihoodSeventhCumulant
    {B : ℝ} (hB : 0 < B) :
    HasDerivAt thetaCuspLikelihoodSeventhCumulant
      (-thetaCuspLikelihoodEighthCumulant B) B := by
  have hm := hasDerivAt_thetaCuspLikelihoodMean hB
  have he2 := hasDerivAt_thetaCuspLikelihoodNormalizedMoment hB 2
  have he3 := hasDerivAt_thetaCuspLikelihoodNormalizedMoment hB 3
  have he4 := hasDerivAt_thetaCuspLikelihoodNormalizedMoment hB 4
  have he5 := hasDerivAt_thetaCuspLikelihoodNormalizedMoment hB 5
  have he6 := hasDerivAt_thetaCuspLikelihoodNormalizedMoment hB 6
  have he7 := hasDerivAt_thetaCuspLikelihoodNormalizedMoment hB 7
  unfold thetaCuspLikelihoodSeventhCumulant thetaCuspLikelihoodEighthCumulant
  convert ((((((((((((((he7.sub ((hm.mul he6).const_mul 7)).sub
    ((he2.mul he5).const_mul 21)).sub ((he3.mul he4).const_mul 35)).add
    (((hm.pow 2).mul he5).const_mul 42)).add
    (((hm.mul he2).mul he4).const_mul 210)).add
    ((hm.mul (he3.pow 2)).const_mul 140)).add
    (((he2.pow 2).mul he3).const_mul 210)).sub
    (((hm.pow 3).mul he4).const_mul 210)).sub
    ((((hm.pow 2).mul he2).mul he3).const_mul 1260)).sub
    ((hm.mul (he2.pow 3)).const_mul 630)).add
    (((hm.pow 4).mul he3).const_mul 840)).add
    (((hm.pow 3).mul (he2.pow 2)).const_mul 2520)).sub
    (((hm.pow 5).mul he2).const_mul 2520)).add
    ((hm.pow 7).const_mul 720)) using 1
  any_goals rfl
  · funext q
    simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply]
    ring
  · simp only [Nat.reduceAdd,
      thetaCuspLikelihoodVariance_eq_normalizedMoment_two_sub_mean_sq,
      Pi.mul_apply, Pi.pow_apply]
    ring

private theorem moment_nonneg {B : ℝ} (hB : 0 < B) (i : ℕ) :
    0 ≤ thetaCuspLikelihoodNormalizedMoment B i := by
  unfold thetaCuspLikelihoodNormalizedMoment
  exact div_nonneg (thetaCuspHigherLikelihoodSpectralMoment_nonneg i)
    (thetaCuspLikelihoodPartition_pos hB).le

private theorem moment_fourfold_le
    {B : ℝ} (hB : 0 < B) (i j k l : ℕ) :
    thetaCuspLikelihoodNormalizedMoment B i *
          thetaCuspLikelihoodNormalizedMoment B j *
        thetaCuspLikelihoodNormalizedMoment B k *
      thetaCuspLikelihoodNormalizedMoment B l ≤
    thetaCuspLikelihoodTailProbability B ^ (3 : ℕ) *
      thetaCuspLikelihoodNormalizedMoment B (i + j + k + l) := by
  let e := thetaCuspLikelihoodNormalizedMoment B
  let p := thetaCuspLikelihoodTailProbability B
  have hp : 0 ≤ p := by
    dsimp only [p, thetaCuspLikelihoodTailProbability]
    exact moment_nonneg hB 0
  have hij : e i * e j ≤ p * e (i + j) := by
    simpa only [e, p] using
      thetaCuspLikelihoodNormalizedMoment_mul_le_tailProbability_mul hB i j
  have hkl : e k * e l ≤ p * e (k + l) := by
    simpa only [e, p] using
      thetaCuspLikelihoodNormalizedMoment_mul_le_tailProbability_mul hB k l
  have hsum : e (i + j) * e (k + l) ≤ p * e ((i + j) + (k + l)) := by
    simpa only [e, p] using
      thetaCuspLikelihoodNormalizedMoment_mul_le_tailProbability_mul
        hB (i + j) (k + l)
  calc
    e i * e j * e k * e l = (e i * e j) * (e k * e l) := by ring
    _ ≤ (p * e (i + j)) * (p * e (k + l)) := by
      exact mul_le_mul hij hkl
        (mul_nonneg (moment_nonneg hB k) (moment_nonneg hB l))
        (mul_nonneg hp (moment_nonneg hB (i + j)))
    _ = p ^ (2 : ℕ) * (e (i + j) * e (k + l)) := by ring
    _ ≤ p ^ (2 : ℕ) * (p * e ((i + j) + (k + l))) :=
      mul_le_mul_of_nonneg_left hsum (sq_nonneg p)
    _ = p ^ (3 : ℕ) * e (i + j + k + l) := by
      simp only [e, p]
      ring_nf

private theorem moment_sixfold_le
    {B : ℝ} (hB : 0 < B) (i j k l u v : ℕ) :
    thetaCuspLikelihoodNormalizedMoment B i *
            thetaCuspLikelihoodNormalizedMoment B j *
          thetaCuspLikelihoodNormalizedMoment B k *
        thetaCuspLikelihoodNormalizedMoment B l *
      thetaCuspLikelihoodNormalizedMoment B u *
      thetaCuspLikelihoodNormalizedMoment B v ≤
    thetaCuspLikelihoodTailProbability B ^ (5 : ℕ) *
      thetaCuspLikelihoodNormalizedMoment B (i + j + k + l + u + v) := by
  let e := thetaCuspLikelihoodNormalizedMoment B
  let p := thetaCuspLikelihoodTailProbability B
  have hp : 0 ≤ p := by
    dsimp only [p, thetaCuspLikelihoodTailProbability]
    exact moment_nonneg hB 0
  have h4 := moment_fourfold_le hB i j k l
  have h2 := thetaCuspLikelihoodNormalizedMoment_mul_le_tailProbability_mul hB u v
  have hsum := thetaCuspLikelihoodNormalizedMoment_mul_le_tailProbability_mul
    hB (i + j + k + l) (u + v)
  change e i * e j * e k * e l ≤ p ^ (3 : ℕ) * e (i + j + k + l) at h4
  change e u * e v ≤ p * e (u + v) at h2
  change e (i + j + k + l) * e (u + v) ≤
    p * e ((i + j + k + l) + (u + v)) at hsum
  calc
    e i * e j * e k * e l * e u * e v =
        (e i * e j * e k * e l) * (e u * e v) := by ring
    _ ≤ (p ^ (3 : ℕ) * e (i + j + k + l)) * (p * e (u + v)) := by
      exact mul_le_mul h4 h2
        (mul_nonneg (moment_nonneg hB u) (moment_nonneg hB v))
        (mul_nonneg (pow_nonneg hp 3) (moment_nonneg hB (i + j + k + l)))
    _ = p ^ (4 : ℕ) * (e (i + j + k + l) * e (u + v)) := by ring
    _ ≤ p ^ (4 : ℕ) * (p * e ((i + j + k + l) + (u + v))) :=
      mul_le_mul_of_nonneg_left hsum (pow_nonneg hp 4)
    _ = p ^ (5 : ℕ) * e (i + j + k + l + u + v) := by
      simp only [e, p]
      ring_nf

private theorem moment_eightfold_le
    {B : ℝ} (hB : 0 < B) (i j k l u v w r : ℕ) :
    thetaCuspLikelihoodNormalizedMoment B i *
                thetaCuspLikelihoodNormalizedMoment B j *
              thetaCuspLikelihoodNormalizedMoment B k *
            thetaCuspLikelihoodNormalizedMoment B l *
          thetaCuspLikelihoodNormalizedMoment B u *
        thetaCuspLikelihoodNormalizedMoment B v *
      thetaCuspLikelihoodNormalizedMoment B w *
      thetaCuspLikelihoodNormalizedMoment B r ≤
    thetaCuspLikelihoodTailProbability B ^ (7 : ℕ) *
      thetaCuspLikelihoodNormalizedMoment B (i + j + k + l + u + v + w + r) := by
  let e := thetaCuspLikelihoodNormalizedMoment B
  let p := thetaCuspLikelihoodTailProbability B
  have hp : 0 ≤ p := by
    dsimp only [p, thetaCuspLikelihoodTailProbability]
    exact moment_nonneg hB 0
  have ha := moment_fourfold_le hB i j k l
  have hb := moment_fourfold_le hB u v w r
  have hsum := thetaCuspLikelihoodNormalizedMoment_mul_le_tailProbability_mul
    hB (i + j + k + l) (u + v + w + r)
  change e i * e j * e k * e l ≤ p ^ (3 : ℕ) * e (i + j + k + l) at ha
  change e u * e v * e w * e r ≤ p ^ (3 : ℕ) * e (u + v + w + r) at hb
  change e (i + j + k + l) * e (u + v + w + r) ≤
    p * e ((i + j + k + l) + (u + v + w + r)) at hsum
  calc
    e i * e j * e k * e l * e u * e v * e w * e r =
        (e i * e j * e k * e l) * (e u * e v * e w * e r) := by ring
    _ ≤ (p ^ (3 : ℕ) * e (i + j + k + l)) *
        (p ^ (3 : ℕ) * e (u + v + w + r)) := by
      exact mul_le_mul ha hb
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg (moment_nonneg hB u) (moment_nonneg hB v))
            (moment_nonneg hB w))
          (moment_nonneg hB r))
        (mul_nonneg (pow_nonneg hp 3) (moment_nonneg hB (i + j + k + l)))
    _ = p ^ (6 : ℕ) * (e (i + j + k + l) * e (u + v + w + r)) := by ring
    _ ≤ p ^ (6 : ℕ) * (p * e ((i + j + k + l) + (u + v + w + r))) :=
      mul_le_mul_of_nonneg_left hsum (pow_nonneg hp 6)
    _ = p ^ (7 : ℕ) * e (i + j + k + l + u + v + w + r) := by
      simp only [e, p]
      ring_nf

/-- More than two thirds of the normalized eighth moment survives cumulant subtraction. -/
theorem two_thirds_mul_thetaCuspLikelihoodNormalizedMoment_eight_lt_eighthCumulant_coordinate
    {x : ℝ} (hx : 0 ≤ x) :
    (2 / 3 : ℝ) * thetaCuspLikelihoodNormalizedMoment
        (thetaCuspLikelihoodCoordinate x) 8 <
      thetaCuspLikelihoodEighthCumulant (thetaCuspLikelihoodCoordinate x) := by
  let B := thetaCuspLikelihoodCoordinate x
  let p := thetaCuspLikelihoodTailProbability B
  let e := thetaCuspLikelihoodNormalizedMoment B
  let m := thetaCuspLikelihoodMean B
  have hB : 0 < B := by simpa only [B] using thetaCuspLikelihoodCoordinate_pos hx
  have hm : 0 < m := by simpa only [m] using thetaCuspLikelihoodMean_pos hB
  have he (i : ℕ) : 0 ≤ e i := by
    simpa only [e] using moment_nonneg hB i
  have he8 : 0 < e 8 := by
    have h2 : 0 < e 2 := by
      simpa only [e] using thetaCuspLikelihoodNormalizedMoment_two_pos hB
    have h23 := three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hB 2
    have h34 := three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hB 3
    have h45 := three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hB 4
    have h56 := three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hB 5
    have h67 := three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hB 6
    have h78 := three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hB 7
    change 3 * e 2 ≤ e 3 at h23
    change 3 * e 3 ≤ e 4 at h34
    change 3 * e 4 ≤ e 5 at h45
    change 3 * e 5 ≤ e 6 at h56
    change 3 * e 6 ≤ e 7 at h67
    change 3 * e 7 ≤ e 8 at h78
    nlinarith
  have hpSmall : 400 * p < 1 := by
    simpa only [B, p] using
      four_hundred_mul_thetaCuspLikelihoodTailProbability_coordinate_lt_one hx
  have hp : 0 < p := by
    have hmle : m ^ (2 : ℕ) ≤ p * e 2 := by
      simpa only [m, e, p, thetaCuspLikelihoodNormalizedMoment_one_eq_mean,
        show 1 + 1 = 2 by norm_num, pow_two] using
        thetaCuspLikelihoodNormalizedMoment_mul_le_tailProbability_mul hB 1 1
    by_contra hpnot
    have hpnonpos : p ≤ 0 := le_of_not_gt hpnot
    have hrhs : p * e 2 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hpnonpos (he 2)
    nlinarith [sq_pos_of_pos hm]
  have hp0 : 0 ≤ p := hp.le
  have h2 (i j : ℕ) : e i * e j ≤ p * e (i + j) := by
    simpa only [e, p] using
      thetaCuspLikelihoodNormalizedMoment_mul_le_tailProbability_mul hB i j
  have h4 (i j k l : ℕ) : e i * e j * e k * e l ≤
      p ^ (3 : ℕ) * e (i + j + k + l) := by
    simpa only [e, p] using moment_fourfold_le hB i j k l
  have h6 (i j k l u v : ℕ) : e i * e j * e k * e l * e u * e v ≤
      p ^ (5 : ℕ) * e (i + j + k + l + u + v) := by
    simpa only [e, p] using moment_sixfold_le hB i j k l u v
  have h8 (i j k l u v w r : ℕ) :
      e i * e j * e k * e l * e u * e v * e w * e r ≤
        p ^ (7 : ℕ) * e (i + j + k + l + u + v + w + r) := by
    simpa only [e, p] using moment_eightfold_le hB i j k l u v w r
  have hm1 : m = e 1 := by
    simpa only [m, e] using
      (thetaCuspLikelihoodNormalizedMoment_one_eq_mean (B := B)).symm
  have hpair :
      8 * m * e 7 + 28 * e 2 * e 6 + 56 * e 3 * e 5 + 35 * e 4 ^ (2 : ℕ) ≤
        127 * p * e 8 := by
    rw [hm1, pow_two]
    nlinarith [h2 1 7, h2 2 6, h2 3 5, h2 4 4]
  have hfour :
      336 * m ^ (3 : ℕ) * e 5 + 2520 * m ^ (2 : ℕ) * e 2 * e 4 +
          1680 * m ^ (2 : ℕ) * e 3 ^ (2 : ℕ) + 5040 * m * e 2 ^ (2 : ℕ) * e 3 +
        630 * e 2 ^ (4 : ℕ) ≤ 10206 * p ^ (3 : ℕ) * e 8 := by
    rw [hm1]
    nlinarith [h4 1 1 1 5, h4 1 1 2 4, h4 1 1 3 3,
      h4 1 2 2 3, h4 2 2 2 2]
  have hsix :
      6720 * m ^ (5 : ℕ) * e 3 + 25200 * m ^ (4 : ℕ) * e 2 ^ (2 : ℕ) ≤
        31920 * p ^ (5 : ℕ) * e 8 := by
    rw [hm1]
    nlinarith [h6 1 1 1 1 1 3, h6 1 1 1 1 2 2]
  have height : 5040 * m ^ (8 : ℕ) ≤ 5040 * p ^ (7 : ℕ) * e 8 := by
    rw [hm1]
    nlinarith [h8 1 1 1 1 1 1 1 1]
  have hp3 : p ^ (3 : ℕ) < (1 / 400 : ℝ) ^ (3 : ℕ) :=
    pow_lt_pow_left₀ (by nlinarith : p < (1 / 400 : ℝ)) hp0 (by norm_num)
  have hp5 : p ^ (5 : ℕ) < (1 / 400 : ℝ) ^ (5 : ℕ) :=
    pow_lt_pow_left₀ (by nlinarith : p < (1 / 400 : ℝ)) hp0 (by norm_num)
  have hp7 : p ^ (7 : ℕ) < (1 / 400 : ℝ) ^ (7 : ℕ) :=
    pow_lt_pow_left₀ (by nlinarith : p < (1 / 400 : ℝ)) hp0 (by norm_num)
  have hbudget :
      127 * p + 10206 * p ^ (3 : ℕ) + 31920 * p ^ (5 : ℕ) + 5040 * p ^ (7 : ℕ) < 1 / 3 := by
    norm_num at hp3 hp5 hp7 ⊢
    nlinarith
  have hloss :
      (127 * p + 10206 * p ^ (3 : ℕ) + 31920 * p ^ (5 : ℕ) + 5040 * p ^ (7 : ℕ)) * e 8 <
        (1 / 3 : ℝ) * e 8 :=
    mul_lt_mul_of_pos_right hbudget he8
  have hpositive : 0 ≤
      56 * m ^ (2 : ℕ) * e 6 + 336 * m * e 2 * e 5 + 560 * m * e 3 * e 4 +
        420 * e 2 ^ (2 : ℕ) * e 4 + 560 * e 2 * e 3 ^ (2 : ℕ) +
      1680 * m ^ (4 : ℕ) * e 4 + 13440 * m ^ (3 : ℕ) * e 2 * e 3 +
        10080 * m ^ (2 : ℕ) * e 2 ^ (3 : ℕ) + 20160 * m ^ (6 : ℕ) * e 2 := by
    have he2nonneg := he 2
    have he3nonneg := he 3
    have he4nonneg := he 4
    have he5nonneg := he 5
    have he6nonneg := he 6
    positivity
  dsimp only [B] at hB
  change (2 / 3 : ℝ) * e 8 < thetaCuspLikelihoodEighthCumulant B
  unfold thetaCuspLikelihoodEighthCumulant
  dsimp only [e, m]
  dsimp only [e, m] at hpair hfour hsix height hloss hpositive
  nlinarith

/-- Eighth likelihood cumulant is strictly positive on the nonnegative source half-line. -/
theorem thetaCuspLikelihoodEighthCumulant_pos
    {x : ℝ} (hx : 0 ≤ x) :
    0 < thetaCuspLikelihoodEighthCumulant
      (thetaCuspLikelihoodCoordinate x) := by
  have hlower :=
    two_thirds_mul_thetaCuspLikelihoodNormalizedMoment_eight_lt_eighthCumulant_coordinate hx
  have hmoment := moment_nonneg (thetaCuspLikelihoodCoordinate_pos hx) 8
  nlinarith

/-- Hypothesis-free square-parameter form of eighth likelihood-cumulant positivity. -/
theorem thetaCuspLikelihoodEighthCumulant_sq_pos (x : ℝ) :
    0 < thetaCuspLikelihoodEighthCumulant
      (thetaCuspLikelihoodCoordinate (x ^ (2 : ℕ))) :=
  thetaCuspLikelihoodEighthCumulant_pos (sq_nonneg x)

end

end RHTower
