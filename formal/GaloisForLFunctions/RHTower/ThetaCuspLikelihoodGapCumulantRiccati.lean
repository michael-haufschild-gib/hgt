import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodStrictCooling
import GaloisForLFunctions.RHTower.ThetaCuspCassiniMarkovBoundaryTransport
import GaloisForLFunctions.RHTower.ThetaCuspFullReflectionFourthTuran
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Theta likelihood support-gap cumulants and reflected Riccati law

The already formalized sharp spectral support edge `3`, combined with modular seam calibration,
forces quantitative moment recurrences and alternating low cumulants for the total likelihood
state.  These signs prove strict reflected Riccati positivity for the likelihood component.

The atom and likelihood actions have opposite first- and second-jet signs.  Their mixed Riccati
term is therefore strictly negative.  The final theorem replaces the former opaque completed
correction hypothesis by exact domination of this negative channel by the two positive component
margins.
-/

open MeasureTheory Set

namespace RHTower

noncomputable section

/-- Normalized higher-tail moment in the total likelihood state, whose remaining unit mass lies at
spectral coordinate zero. -/
def thetaCuspLikelihoodNormalizedMoment (B : ℝ) (m : ℕ) : ℝ :=
  thetaCuspHigherLikelihoodSpectralMoment B m /
    thetaCuspLikelihoodPartition B

/-- Probability carried by the positive higher-tail component of the total likelihood state. -/
def thetaCuspLikelihoodTailProbability (B : ℝ) : ℝ :=
  thetaCuspLikelihoodNormalizedMoment B 0

/-- Fourth cumulant of the total likelihood state. -/
def thetaCuspLikelihoodFourthCumulant (B : ℝ) : ℝ :=
  thetaCuspLikelihoodNormalizedMoment B 4 -
    4 * thetaCuspLikelihoodMean B *
      thetaCuspLikelihoodNormalizedMoment B 3 -
    3 * thetaCuspLikelihoodNormalizedMoment B 2 ^ 2 +
    12 * thetaCuspLikelihoodMean B ^ 2 *
      thetaCuspLikelihoodNormalizedMoment B 2 -
    6 * thetaCuspLikelihoodMean B ^ 4

/-- The sharp support edge `3` gives a one-step recurrence for every tilted moment. -/
theorem three_mul_thetaCuspHigherLikelihoodSpectralMoment_le_succ
    {B : ℝ} (hB : 0 < B) (m : ℕ) :
    3 * thetaCuspHigherLikelihoodSpectralMoment B m ≤
      thetaCuspHigherLikelihoodSpectralMoment B (m + 1) := by
  unfold thetaCuspHigherLikelihoodSpectralMoment
  rw [← integral_const_mul]
  apply integral_mono_ae
    ((integrable_pow_thetaCuspHigherLikelihoodTiltedMeasure m hB).const_mul 3)
    (integrable_pow_thetaCuspHigherLikelihoodTiltedMeasure (m + 1) hB)
  filter_upwards
    [ae_three_le_thetaCuspHigherLikelihoodTiltedMeasure B] with r hr
  rw [pow_succ]
  have hr0 : 0 ≤ r := le_trans (by norm_num) hr
  have hpow : 0 ≤ r ^ m := pow_nonneg hr0 m
  nlinarith [mul_nonneg hpow (sub_nonneg.mpr hr)]

/-- The support recurrence persists after normalization by the positive partition. -/
theorem three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ
    {B : ℝ} (hB : 0 < B) (m : ℕ) :
    3 * thetaCuspLikelihoodNormalizedMoment B m ≤
      thetaCuspLikelihoodNormalizedMoment B (m + 1) := by
  have hpart := thetaCuspLikelihoodPartition_pos hB
  have hrec :=
    three_mul_thetaCuspHigherLikelihoodSpectralMoment_le_succ hB m
  unfold thetaCuspLikelihoodNormalizedMoment
  rw [show
    3 * (thetaCuspHigherLikelihoodSpectralMoment B m /
        thetaCuspLikelihoodPartition B) =
      (3 * thetaCuspHigherLikelihoodSpectralMoment B m) /
        thetaCuspLikelihoodPartition B by ring]
  apply (div_le_div_iff_of_pos_right hpart).2
  exact hrec

/-- The normalized first moment is exactly the total likelihood mean. -/
theorem thetaCuspLikelihoodNormalizedMoment_one_eq_mean (B : ℝ) :
    thetaCuspLikelihoodNormalizedMoment B 1 =
      thetaCuspLikelihoodMean B := by
  rfl

/-- The normalized second raw moment is strictly positive. -/
theorem thetaCuspLikelihoodNormalizedMoment_two_pos
    {B : ℝ} (hB : 0 < B) :
    0 < thetaCuspLikelihoodNormalizedMoment B 2 := by
  have hrec :=
    three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hB 1
  rw [thetaCuspLikelihoodNormalizedMoment_one_eq_mean] at hrec
  nlinarith [thetaCuspLikelihoodMean_pos hB]

/-- The normalized fourth raw moment is strictly positive. -/
theorem thetaCuspLikelihoodNormalizedMoment_four_pos
    {B : ℝ} (hB : 0 < B) :
    0 < thetaCuspLikelihoodNormalizedMoment B 4 := by
  have h2 := thetaCuspLikelihoodNormalizedMoment_two_pos hB
  have h23 :=
    three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hB 2
  have h34 :=
    three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hB 3
  nlinarith

/-- Strict Hankel positivity on the non-adjacent coordinates `0,2` gives the exact
Cauchy--Schwarz moment inequality needed for the fourth cumulant. -/
theorem sq_thetaCuspHigherLikelihoodSpectralMoment_two_lt_zero_mul_four
    {B : ℝ} (hB : 0 < B) :
    thetaCuspHigherLikelihoodSpectralMoment B 2 ^ 2 <
      thetaCuspHigherLikelihoodSpectralMoment B 0 *
        thetaCuspHigherLikelihoodSpectralMoment B 4 := by
  let e : Fin 2 → Fin 3 := fun i => ⟨2 * i.1, by omega⟩
  have he : Function.Injective e := by
    intro i j hij
    apply Fin.ext
    have hval := congrArg Fin.val hij
    dsimp [e] at hval
    omega
  have hdet :=
    ((thetaCuspHigherLikelihoodSpectralMoment_hankel_posDef hB 3).submatrix he).det_pos
  simpa [HTGeometry.momentHankelMatrix, e, Matrix.det_fin_two, pow_two] using hdet

/-- Normalized Cauchy--Schwarz: `e₂² < p e₄`. -/
theorem sq_thetaCuspLikelihoodNormalizedMoment_two_lt_tailProbability_mul_four
    {B : ℝ} (hB : 0 < B) :
    thetaCuspLikelihoodNormalizedMoment B 2 ^ 2 <
      thetaCuspLikelihoodTailProbability B *
        thetaCuspLikelihoodNormalizedMoment B 4 := by
  have hraw :=
    sq_thetaCuspHigherLikelihoodSpectralMoment_two_lt_zero_mul_four hB
  have hpart := thetaCuspLikelihoodPartition_pos hB
  change
    (thetaCuspHigherLikelihoodSpectralMoment B 2 /
        thetaCuspLikelihoodPartition B) ^ 2 <
      (thetaCuspHigherLikelihoodSpectralMoment B 0 /
          thetaCuspLikelihoodPartition B) *
        (thetaCuspHigherLikelihoodSpectralMoment B 4 /
          thetaCuspLikelihoodPartition B)
  rw [div_pow]
  rw [show
    (thetaCuspHigherLikelihoodSpectralMoment B 0 /
          thetaCuspLikelihoodPartition B) *
        (thetaCuspHigherLikelihoodSpectralMoment B 4 /
          thetaCuspLikelihoodPartition B) =
      (thetaCuspHigherLikelihoodSpectralMoment B 0 *
          thetaCuspHigherLikelihoodSpectralMoment B 4) /
        thetaCuspLikelihoodPartition B ^ 2 by ring]
  exact (div_lt_div_iff_of_pos_right (sq_pos_of_pos hpart)).2 hraw

/-- The exact first-atom boundary slope is strictly below one half, using only `π > 3`. -/
theorem thetaCuspFirstAtomBoundaryLogSlope_lt_one_half :
    thetaCuspFirstAtomBoundaryLogSlope < 1 / 2 := by
  have hpi := Real.pi_gt_three
  have hden : 0 < 2 * Real.pi - 3 := by nlinarith
  have hfrac : 6 / (2 * Real.pi - 3) < 2 := by
    apply (div_lt_iff₀ hden).2
    nlinarith
  unfold thetaCuspFirstAtomBoundaryLogSlope
  nlinarith

/-- Uniform small-mean law on the nonnegative theta-source half-line. -/
theorem twelve_mul_thetaCuspLikelihoodMean_coordinate_lt_one
    {x : ℝ} (hx : 0 ≤ x) :
    12 * thetaCuspLikelihoodMean (thetaCuspLikelihoodCoordinate x) < 1 := by
  have hm :=
    thetaCuspLikelihoodMean_pos (thetaCuspLikelihoodCoordinate_pos hx)
  have hcal :=
    two_pi_mul_thetaCuspLikelihoodMean_coordinate_le_boundarySlope hx
  have hpi : 6 < 2 * Real.pi := by nlinarith [Real.pi_gt_three]
  have hmul :
      6 * thetaCuspLikelihoodMean (thetaCuspLikelihoodCoordinate x) <
        2 * Real.pi *
          thetaCuspLikelihoodMean (thetaCuspLikelihoodCoordinate x) :=
    mul_lt_mul_of_pos_right hpi hm
  nlinarith [thetaCuspFirstAtomBoundaryLogSlope_lt_one_half]

/-- The positive tail probability is at most one third of the total mean. -/
theorem three_mul_thetaCuspLikelihoodTailProbability_le_mean
    {B : ℝ} (hB : 0 < B) :
    3 * thetaCuspLikelihoodTailProbability B ≤
      thetaCuspLikelihoodMean B := by
  have h := three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hB 0
  simp only [zero_add, thetaCuspLikelihoodNormalizedMoment_one_eq_mean] at h
  exact h

/-- **Strict support-gap overdispersion.**  On the theta-source half-line, variance exceeds twice
the mean. -/
theorem two_mul_thetaCuspLikelihoodMean_lt_variance_coordinate
    {x : ℝ} (hx : 0 ≤ x) :
    2 * thetaCuspLikelihoodMean (thetaCuspLikelihoodCoordinate x) <
      thetaCuspLikelihoodVariance (thetaCuspLikelihoodCoordinate x) := by
  let B := thetaCuspLikelihoodCoordinate x
  let m := thetaCuspLikelihoodMean B
  let e2 := thetaCuspLikelihoodNormalizedMoment B 2
  have hB : 0 < B := by
    simpa only [B] using thetaCuspLikelihoodCoordinate_pos hx
  have hm : 0 < m := by
    simpa only [m] using thetaCuspLikelihoodMean_pos hB
  have hmSmall : 12 * m < 1 := by
    simpa only [B, m] using
      twelve_mul_thetaCuspLikelihoodMean_coordinate_lt_one hx
  have he2 : 3 * m ≤ e2 := by
    have hrec :=
      three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hB 1
    simpa only [thetaCuspLikelihoodNormalizedMoment_one_eq_mean, m, e2] using hrec
  change 2 * m < e2 - m ^ 2
  nlinarith [sq_pos_of_pos hm]

/-- The third cumulant dominates twice the normalized second raw moment. -/
theorem two_mul_thetaCuspLikelihoodNormalizedMoment_two_lt_thirdCumulant_coordinate
    {x : ℝ} (hx : 0 ≤ x) :
    2 * thetaCuspLikelihoodNormalizedMoment
          (thetaCuspLikelihoodCoordinate x) 2 <
      thetaCuspLikelihoodThirdCumulant
        (thetaCuspLikelihoodCoordinate x) := by
  let B := thetaCuspLikelihoodCoordinate x
  let m := thetaCuspLikelihoodMean B
  let e2 := thetaCuspLikelihoodNormalizedMoment B 2
  let e3 := thetaCuspLikelihoodNormalizedMoment B 3
  have hB : 0 < B := by
    simpa only [B] using thetaCuspLikelihoodCoordinate_pos hx
  have hm : 0 < m := by
    simpa only [m] using thetaCuspLikelihoodMean_pos hB
  have hmSmall : 12 * m < 1 := by
    simpa only [B, m] using
      twelve_mul_thetaCuspLikelihoodMean_coordinate_lt_one hx
  have he2 : 0 < e2 := by
    simpa only [e2] using thetaCuspLikelihoodNormalizedMoment_two_pos hB
  have he3 : 3 * e2 ≤ e3 := by
    simpa only [e2, e3] using
      three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hB 2
  have hcoef : 0 < 1 - 3 * m := by linarith
  have hprod : 0 < (1 - 3 * m) * e2 := mul_pos hcoef he2
  have hm3 : 0 < m ^ 3 := pow_pos hm 3
  change 2 * e2 < e3 - 3 * m * e2 + 2 * m ^ 3
  nlinarith

/-- In particular, the third cumulant dominates twice the variance. -/
theorem two_mul_thetaCuspLikelihoodVariance_lt_thirdCumulant_coordinate
    {x : ℝ} (hx : 0 ≤ x) :
    2 * thetaCuspLikelihoodVariance (thetaCuspLikelihoodCoordinate x) <
      thetaCuspLikelihoodThirdCumulant (thetaCuspLikelihoodCoordinate x) := by
  let m :=
    thetaCuspLikelihoodMean (thetaCuspLikelihoodCoordinate x)
  let e2 :=
    thetaCuspLikelihoodNormalizedMoment (thetaCuspLikelihoodCoordinate x) 2
  let v :=
    thetaCuspLikelihoodVariance (thetaCuspLikelihoodCoordinate x)
  let k3 :=
    thetaCuspLikelihoodThirdCumulant (thetaCuspLikelihoodCoordinate x)
  have hk : 2 * e2 < k3 := by
    simpa only [e2, k3] using
    two_mul_thetaCuspLikelihoodNormalizedMoment_two_lt_thirdCumulant_coordinate hx
  have hm : 0 < m := by
    simpa only [m] using
    thetaCuspLikelihoodMean_pos (thetaCuspLikelihoodCoordinate_pos hx)
  have hvEq : v = e2 - m ^ 2 := by
    rfl
  change 2 * v < k3
  rw [hvEq]
  nlinarith [sq_pos_of_pos hm]

/-- The third cumulant is strictly positive along the nonnegative source half-line. -/
theorem thetaCuspLikelihoodThirdCumulant_coordinate_pos
    {x : ℝ} (hx : 0 ≤ x) :
    0 < thetaCuspLikelihoodThirdCumulant
      (thetaCuspLikelihoodCoordinate x) := by
  exact lt_trans
    (mul_pos (by norm_num)
      (thetaCuspLikelihoodVariance_pos
        (thetaCuspLikelihoodCoordinate_pos hx)))
    (two_mul_thetaCuspLikelihoodVariance_lt_thirdCumulant_coordinate hx)

/-- The fourth cumulant is the negative derivative of the third cumulant. -/
theorem hasDerivAt_thetaCuspLikelihoodNormalizedMoment
    {B : ℝ} (hB : 0 < B) (m : ℕ) :
    HasDerivAt (fun q => thetaCuspLikelihoodNormalizedMoment q m)
      (-thetaCuspLikelihoodNormalizedMoment B (m + 1) +
        thetaCuspLikelihoodMean B *
          thetaCuspLikelihoodNormalizedMoment B m) B := by
  have hm :=
    hasDerivAt_thetaCuspHigherLikelihoodSpectralMoment m hB
  have hpart := hasDerivAt_thetaCuspLikelihoodPartition hB
  have hpartPos := thetaCuspLikelihoodPartition_pos hB
  unfold thetaCuspLikelihoodNormalizedMoment
  refine (hm.div hpart hpartPos.ne').congr_deriv ?_
  simp only [thetaCuspLikelihoodMean]
  field_simp [hpartPos.ne']
  ring

/-- Variance is the normalized second raw moment minus the squared mean. -/
theorem thetaCuspLikelihoodVariance_eq_normalizedMoment_two_sub_mean_sq
    (B : ℝ) :
    thetaCuspLikelihoodVariance B =
      thetaCuspLikelihoodNormalizedMoment B 2 -
        thetaCuspLikelihoodMean B ^ 2 := by
  rfl

/-- The fourth cumulant is the negative derivative of the third cumulant. -/
theorem hasDerivAt_thetaCuspLikelihoodThirdCumulant
    {B : ℝ} (hB : 0 < B) :
    HasDerivAt thetaCuspLikelihoodThirdCumulant
      (-thetaCuspLikelihoodFourthCumulant B) B := by
  have hmean := hasDerivAt_thetaCuspLikelihoodMean hB
  have heTwo := hasDerivAt_thetaCuspLikelihoodNormalizedMoment hB 2
  have heThree := hasDerivAt_thetaCuspLikelihoodNormalizedMoment hB 3
  have hraw :=
    (heThree.sub ((hmean.mul heTwo).const_mul 3)).add
      ((hmean.pow 3).const_mul 2)
  unfold thetaCuspLikelihoodThirdCumulant
    thetaCuspLikelihoodFourthCumulant
  convert hraw using 1
  any_goals rfl
  · funext q
    simp only [thetaCuspLikelihoodNormalizedMoment, Pi.add_apply, Pi.sub_apply,
      Pi.mul_apply, Pi.pow_apply]
    ring
  · simp only [Nat.reduceAdd,
      thetaCuspLikelihoodVariance_eq_normalizedMoment_two_sub_mean_sq]
    ring

/-- The fourth cumulant strictly dominates twice the third cumulant on the source half-line. -/
theorem two_mul_thetaCuspLikelihoodThirdCumulant_lt_fourthCumulant_coordinate
    {x : ℝ} (hx : 0 ≤ x) :
    2 * thetaCuspLikelihoodThirdCumulant
          (thetaCuspLikelihoodCoordinate x) <
      thetaCuspLikelihoodFourthCumulant
        (thetaCuspLikelihoodCoordinate x) := by
  let B := thetaCuspLikelihoodCoordinate x
  let p := thetaCuspLikelihoodTailProbability B
  let m := thetaCuspLikelihoodMean B
  let e2 := thetaCuspLikelihoodNormalizedMoment B 2
  let e3 := thetaCuspLikelihoodNormalizedMoment B 3
  let e4 := thetaCuspLikelihoodNormalizedMoment B 4
  have hB : 0 < B := by
    simpa only [B] using thetaCuspLikelihoodCoordinate_pos hx
  have hm : 0 < m := by
    simpa only [m] using thetaCuspLikelihoodMean_pos hB
  have hmSmall : 12 * m < 1 := by
    simpa only [B, m] using
      twelve_mul_thetaCuspLikelihoodMean_coordinate_lt_one hx
  have he2 : 0 < e2 := by
    simpa only [e2] using thetaCuspLikelihoodNormalizedMoment_two_pos hB
  have he4 : 0 < e4 := by
    simpa only [e4] using thetaCuspLikelihoodNormalizedMoment_four_pos hB
  have hp : 3 * p ≤ m := by
    simpa only [p, m] using
      three_mul_thetaCuspLikelihoodTailProbability_le_mean hB
  have he2lower : 3 * m ≤ e2 := by
    have hrec :=
      three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hB 1
    simpa only [thetaCuspLikelihoodNormalizedMoment_one_eq_mean, m, e2] using hrec
  have he3upper : e3 ≤ e4 / 3 := by
    have hrec :=
      three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hB 3
    dsimp [e3, e4] at hrec
    linarith
  have he2sq : e2 ^ 2 < p * e4 := by
    simpa only [B, p, e2, e4] using
      sq_thetaCuspLikelihoodNormalizedMoment_two_lt_tailProbability_mul_four hB
  have hcross : 3 * e2 ^ 2 < m * e4 := by
    have hpMul : 3 * p * e4 ≤ m * e4 :=
      mul_le_mul_of_nonneg_right hp he4.le
    nlinarith [mul_lt_mul_of_pos_left he2sq (by norm_num : (0 : ℝ) < 3)]
  have hcoefThree : 0 < 4 * m + 2 := by linarith
  have he3scaled :
      (4 * m + 2) * e3 ≤ (4 * m + 2) * (e4 / 3) :=
    mul_le_mul_of_nonneg_left he3upper hcoefThree.le
  have hcoef : 0 < (1 - 7 * m) / 3 := by linarith
  have hcoefMul : 0 < ((1 - 7 * m) / 3) * e4 :=
    mul_pos hcoef he4
  have hfirst :
      0 < e4 - (4 * m + 2) * e3 - 3 * e2 ^ 2 := by
    nlinarith
  have hrestCoeff : 0 < 12 * m ^ 2 + 6 * m := by positivity
  have hrestScaled :
      (12 * m ^ 2 + 6 * m) * (3 * m) ≤
        (12 * m ^ 2 + 6 * m) * e2 :=
    mul_le_mul_of_nonneg_left he2lower hrestCoeff.le
  have hpoly : 0 < 9 + 16 * m - 3 * m ^ 2 := by nlinarith [sq_nonneg m]
  have hrestPositive : 0 < 2 * m ^ 2 * (9 + 16 * m - 3 * m ^ 2) := by
    positivity
  have hrest :
      0 <
        (12 * m ^ 2 + 6 * m) * e2 -
          6 * m ^ 4 - 4 * m ^ 3 := by
    nlinarith
  change
    2 * (e3 - 3 * m * e2 + 2 * m ^ 3) <
      e4 - 4 * m * e3 - 3 * e2 ^ 2 +
        12 * m ^ 2 * e2 - 6 * m ^ 4
  nlinarith

/-- Fourth source-coordinate jet of the logarithmic likelihood partition. -/
def thetaCuspLikelihoodSourceLogPartitionJetFour (x : ℝ) : ℝ :=
  16 * thetaCuspSingleAtomReflectionScale 1 x ^ 4 *
      thetaCuspLikelihoodFourthCumulant (thetaCuspLikelihoodCoordinate x) -
    96 * thetaCuspSingleAtomReflectionScale 1 x ^ 3 *
      thetaCuspLikelihoodThirdCumulant (thetaCuspLikelihoodCoordinate x) +
    112 * thetaCuspSingleAtomReflectionScale 1 x ^ 2 *
      thetaCuspLikelihoodVariance (thetaCuspLikelihoodCoordinate x) -
    16 * thetaCuspSingleAtomReflectionScale 1 x *
      thetaCuspLikelihoodMean (thetaCuspLikelihoodCoordinate x)

/-- Exact fourth source jet obtained by differentiating the cumulant-three expression. -/
theorem hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetThree
    {x : ℝ} (hB : 0 < thetaCuspLikelihoodCoordinate x) :
    HasDerivAt thetaCuspLikelihoodSourceLogPartitionJetThree
      (thetaCuspLikelihoodSourceLogPartitionJetFour x) x := by
  have hscale := hasDerivAt_thetaCuspSingleAtomReflectionScale_one x
  have hcoord := hasDerivAt_thetaCuspLikelihoodCoordinate x
  have hmean :=
    (hasDerivAt_thetaCuspLikelihoodMean hB).comp x hcoord
  have hvariance :=
    (hasDerivAt_thetaCuspLikelihoodVariance hB).comp x hcoord
  have hthird :=
    (hasDerivAt_thetaCuspLikelihoodThirdCumulant hB).comp x hcoord
  unfold thetaCuspLikelihoodSourceLogPartitionJetThree
    thetaCuspLikelihoodSourceLogPartitionJetFour
  convert
    ((((hscale.pow 3).mul hthird).const_mul (-8)).add
        (((hscale.pow 2).mul hvariance).const_mul 24)).sub
      ((hscale.mul hmean).const_mul 8) using 1
  any_goals rfl
  · funext y
    simp only [Function.comp_apply, Pi.add_apply, Pi.sub_apply, Pi.mul_apply,
      Pi.pow_apply]
    ring
  · simp only [Function.comp_apply, Pi.pow_apply]
    ring

/-- The source log-partition second jet is strictly positive. -/
theorem thetaCuspLikelihoodSourceLogPartitionJetTwo_pos
    {x : ℝ} (hx : 0 ≤ x) :
    0 < thetaCuspLikelihoodSourceLogPartitionJetTwo x := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let m := thetaCuspLikelihoodMean (thetaCuspLikelihoodCoordinate x)
  let v := thetaCuspLikelihoodVariance (thetaCuspLikelihoodCoordinate x)
  have hA : 3 < A := by
    simpa only [A] using
      three_lt_thetaCuspSingleAtomReflectionScale (n := 1) (by norm_num) hx
  have hm : 0 < m := by
    simpa only [m] using
      thetaCuspLikelihoodMean_pos (thetaCuspLikelihoodCoordinate_pos hx)
  have hv : 2 * m < v := by
    simpa only [m, v] using
      two_mul_thetaCuspLikelihoodMean_lt_variance_coordinate hx
  have hAv : m < A * v := by
    have hleft : m < 2 * A * m := by
      nlinarith [mul_pos (sub_pos.mpr hA) hm]
    have hright : 2 * A * m < A * v := by
      simpa only [mul_assoc, mul_left_comm, mul_comm] using
        mul_lt_mul_of_pos_left hv (show 0 < A by linarith)
    exact hleft.trans hright
  dsimp [A, m, v] at *
  unfold thetaCuspLikelihoodSourceLogPartitionJetTwo
  nlinarith [mul_pos (by linarith : 0 <
      thetaCuspSingleAtomReflectionScale 1 x) (sub_pos.mpr hAv)]

/-- The source log-partition third jet is strictly negative. -/
theorem thetaCuspLikelihoodSourceLogPartitionJetThree_neg
    {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspLikelihoodSourceLogPartitionJetThree x < 0 := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let m := thetaCuspLikelihoodMean (thetaCuspLikelihoodCoordinate x)
  let v := thetaCuspLikelihoodVariance (thetaCuspLikelihoodCoordinate x)
  let k3 := thetaCuspLikelihoodThirdCumulant (thetaCuspLikelihoodCoordinate x)
  have hA : 3 < A := by
    simpa only [A] using
      three_lt_thetaCuspSingleAtomReflectionScale (n := 1) (by norm_num) hx
  have hm : 0 < m := by
    simpa only [m] using
      thetaCuspLikelihoodMean_pos (thetaCuspLikelihoodCoordinate_pos hx)
  have hv : 0 < v := by
    simpa only [v] using
      thetaCuspLikelihoodVariance_pos (thetaCuspLikelihoodCoordinate_pos hx)
  have hk : 2 * v < k3 := by
    simpa only [v, k3] using
      two_mul_thetaCuspLikelihoodVariance_lt_thirdCumulant_coordinate hx
  have hAk : 3 * v < A * k3 := by
    have h1 : 2 * A * v < A * k3 := by
      simpa only [mul_assoc, mul_left_comm, mul_comm] using
        mul_lt_mul_of_pos_left hk (show 0 < A by linarith)
    have h2 : 6 * v < 2 * A * v := by
      nlinarith [mul_pos (sub_pos.mpr hA) hv]
    linarith
  have hA2k : 3 * A * v < A ^ 2 * k3 := by
    nlinarith [mul_pos (by linarith : 0 < A) (sub_pos.mpr hAk)]
  have hbracket : 0 < A ^ 2 * k3 - 3 * A * v + m := by linarith
  dsimp [A, m, v, k3] at *
  unfold thetaCuspLikelihoodSourceLogPartitionJetThree
  nlinarith [mul_pos (by linarith : 0 <
      thetaCuspSingleAtomReflectionScale 1 x) hbracket]

/-- The source log-partition fourth jet is strictly positive. -/
theorem thetaCuspLikelihoodSourceLogPartitionJetFour_pos
    {x : ℝ} (hx : 0 ≤ x) :
    0 < thetaCuspLikelihoodSourceLogPartitionJetFour x := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let m := thetaCuspLikelihoodMean (thetaCuspLikelihoodCoordinate x)
  let v := thetaCuspLikelihoodVariance (thetaCuspLikelihoodCoordinate x)
  let k3 := thetaCuspLikelihoodThirdCumulant (thetaCuspLikelihoodCoordinate x)
  let k4 := thetaCuspLikelihoodFourthCumulant (thetaCuspLikelihoodCoordinate x)
  have hA : 3 < A := by
    simpa only [A] using
      three_lt_thetaCuspSingleAtomReflectionScale (n := 1) (by norm_num) hx
  have hm : 0 < m := by
    simpa only [m] using
      thetaCuspLikelihoodMean_pos (thetaCuspLikelihoodCoordinate_pos hx)
  have hv : 2 * m < v := by
    simpa only [m, v] using
      two_mul_thetaCuspLikelihoodMean_lt_variance_coordinate hx
  have hk3 : 0 < k3 := by
    simpa only [k3] using thetaCuspLikelihoodThirdCumulant_coordinate_pos hx
  have hk4 : 2 * k3 < k4 := by
    simpa only [k3, k4] using
      two_mul_thetaCuspLikelihoodThirdCumulant_lt_fourthCumulant_coordinate hx
  have hAk : 6 * k3 < A * k4 := by
    have h1 : 2 * A * k3 < A * k4 := by
      simpa only [mul_assoc, mul_left_comm, mul_comm] using
        mul_lt_mul_of_pos_left hk4 (show 0 < A by linarith)
    have h2 : 6 * k3 < 2 * A * k3 := by
      nlinarith [mul_pos (sub_pos.mpr hA) hk3]
    linarith
  have hfirst : 0 < A ^ 2 * (A * k4 - 6 * k3) := by positivity
  have hsecond : 0 < 7 * A * v - m := by
    have hAv : 6 * m < A * v := by
      have h1 : 2 * A * m < A * v := by
        simpa only [mul_assoc, mul_left_comm, mul_comm] using
          mul_lt_mul_of_pos_left hv (show 0 < A by linarith)
      have h2 : 6 * m < 2 * A * m := by
        nlinarith [mul_pos (sub_pos.mpr hA) hm]
      linarith
    nlinarith
  have hbracket :
      0 < A ^ 3 * k4 - 6 * A ^ 2 * k3 + 7 * A * v - m := by
    nlinarith [hfirst]
  dsimp [A, m, v, k3, k4] at *
  unfold thetaCuspLikelihoodSourceLogPartitionJetFour
  nlinarith [mul_pos (by linarith : 0 <
      thetaCuspSingleAtomReflectionScale 1 x) hbracket]

/-- The cumulant source log-partition is the existing higher-to-first likelihood log. -/
theorem thetaCuspLikelihoodSourceLogPartition_eq_higherLikelihoodLog
    {x : ℝ} (hx : 0 < x) :
    thetaCuspLikelihoodSourceLogPartition x =
      thetaCuspHigherLikelihoodLog x := by
  unfold thetaCuspLikelihoodSourceLogPartition
    thetaCuspLikelihoodPartition thetaCuspHigherLikelihoodLog
  rw [thetaCuspHigherLikelihoodSpectralResponse_coordinate hx]

private theorem thetaCuspLikelihoodSourceLogPartition_eventuallyEq_higherLikelihoodLog
    {x : ℝ} (hx : 0 < x) :
    thetaCuspLikelihoodSourceLogPartition =ᶠ[nhds x]
      thetaCuspHigherLikelihoodLog := by
  filter_upwards [Ioi_mem_nhds hx] with y hy
  exact thetaCuspLikelihoodSourceLogPartition_eq_higherLikelihoodLog hy

/-- Existing first likelihood log jet equals the cumulant source jet. -/
theorem thetaCuspLikelihoodSourceLogPartitionJetOne_eq_higherLikelihoodLogJetOne
    {x : ℝ} (hx : 0 < x) :
    thetaCuspLikelihoodSourceLogPartitionJetOne x =
      thetaCuspHigherLikelihoodLogJetOne x := by
  have hB := thetaCuspLikelihoodCoordinate_pos hx.le
  have hl := hasDerivAt_thetaCuspLikelihoodSourceLogPartition hB
  have hr := (hasDerivAt_thetaCuspHigherLikelihoodLog hx).congr_of_eventuallyEq
    (thetaCuspLikelihoodSourceLogPartition_eventuallyEq_higherLikelihoodLog hx)
  exact hl.unique hr

private theorem thetaCuspLikelihoodSourceLogPartitionJetOne_eventuallyEq_higherLikelihoodLogJetOne
    {x : ℝ} (hx : 0 < x) :
    thetaCuspLikelihoodSourceLogPartitionJetOne =ᶠ[nhds x]
      thetaCuspHigherLikelihoodLogJetOne := by
  filter_upwards [Ioi_mem_nhds hx] with y hy
  exact thetaCuspLikelihoodSourceLogPartitionJetOne_eq_higherLikelihoodLogJetOne hy

/-- Existing second likelihood log jet equals the cumulant source jet. -/
theorem thetaCuspLikelihoodSourceLogPartitionJetTwo_eq_higherLikelihoodLogJetTwo
    {x : ℝ} (hx : 0 < x) :
    thetaCuspLikelihoodSourceLogPartitionJetTwo x =
      thetaCuspHigherLikelihoodLogJetTwo x := by
  have hB := thetaCuspLikelihoodCoordinate_pos hx.le
  have hl := hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetOne hB
  have hr := (hasDerivAt_thetaCuspHigherLikelihoodLogJetOne hx).congr_of_eventuallyEq
    (thetaCuspLikelihoodSourceLogPartitionJetOne_eventuallyEq_higherLikelihoodLogJetOne hx)
  exact hl.unique hr

private theorem thetaCuspLikelihoodSourceLogPartitionJetTwo_eventuallyEq_higherLikelihoodLogJetTwo
    {x : ℝ} (hx : 0 < x) :
    thetaCuspLikelihoodSourceLogPartitionJetTwo =ᶠ[nhds x]
      thetaCuspHigherLikelihoodLogJetTwo := by
  filter_upwards [Ioi_mem_nhds hx] with y hy
  exact thetaCuspLikelihoodSourceLogPartitionJetTwo_eq_higherLikelihoodLogJetTwo hy

/-- Existing third likelihood log jet equals the cumulant source jet. -/
theorem thetaCuspLikelihoodSourceLogPartitionJetThree_eq_higherLikelihoodLogJetThree
    {x : ℝ} (hx : 0 < x) :
    thetaCuspLikelihoodSourceLogPartitionJetThree x =
      thetaCuspHigherLikelihoodLogJetThree x := by
  have hB := thetaCuspLikelihoodCoordinate_pos hx.le
  have hl := hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetTwo hB
  have hr := (hasDerivAt_thetaCuspHigherLikelihoodLogJetTwo hx).congr_of_eventuallyEq
    (thetaCuspLikelihoodSourceLogPartitionJetTwo_eventuallyEq_higherLikelihoodLogJetTwo hx)
  exact hl.unique hr

private theorem thetaCuspLikelihoodSourceLogPartitionJetThree_eventuallyEq_higherLikelihoodLogJetThree
    {x : ℝ} (hx : 0 < x) :
    thetaCuspLikelihoodSourceLogPartitionJetThree =ᶠ[nhds x]
      thetaCuspHigherLikelihoodLogJetThree := by
  filter_upwards [Ioi_mem_nhds hx] with y hy
  exact thetaCuspLikelihoodSourceLogPartitionJetThree_eq_higherLikelihoodLogJetThree hy

/-- Existing fourth likelihood log jet equals the new support-gap cumulant expression. -/
theorem thetaCuspLikelihoodSourceLogPartitionJetFour_eq_higherLikelihoodLogJetFour
    {x : ℝ} (hx : 0 < x) :
    thetaCuspLikelihoodSourceLogPartitionJetFour x =
      thetaCuspHigherLikelihoodLogJetFour x := by
  have hB := thetaCuspLikelihoodCoordinate_pos hx.le
  have hl := hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetThree hB
  have hr := (hasDerivAt_thetaCuspHigherLikelihoodLogJetThree hx).congr_of_eventuallyEq
    (thetaCuspLikelihoodSourceLogPartitionJetThree_eventuallyEq_higherLikelihoodLogJetThree hx)
  exact hl.unique hr

/-- The previously only lower-bounded fourth likelihood log jet is in fact strictly positive. -/
theorem thetaCuspHigherLikelihoodLogJetFour_pos
    {x : ℝ} (hx : 0 < x) :
    0 < thetaCuspHigherLikelihoodLogJetFour x := by
  rw [← thetaCuspLikelihoodSourceLogPartitionJetFour_eq_higherLikelihoodLogJetFour hx]
  exact thetaCuspLikelihoodSourceLogPartitionJetFour_pos hx.le

/-- First source jet is strictly increasing on the nonnegative half-line. -/
theorem strictMonoOn_thetaCuspLikelihoodSourceLogPartitionJetOne :
    StrictMonoOn thetaCuspLikelihoodSourceLogPartitionJetOne (Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 0)
  · intro x hx
    exact (hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetOne
      (thetaCuspLikelihoodCoordinate_pos hx)).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    rw [(hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetOne
      (thetaCuspLikelihoodCoordinate_pos hx.le)).deriv]
    exact thetaCuspLikelihoodSourceLogPartitionJetTwo_pos hx.le

/-- Third source jet is strictly increasing on the nonnegative half-line. -/
theorem strictMonoOn_thetaCuspLikelihoodSourceLogPartitionJetThree :
    StrictMonoOn thetaCuspLikelihoodSourceLogPartitionJetThree (Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 0)
  · intro x hx
    exact (hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetThree
      (thetaCuspLikelihoodCoordinate_pos hx)).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    rw [(hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetThree
      (thetaCuspLikelihoodCoordinate_pos hx.le)).deriv]
    exact thetaCuspLikelihoodSourceLogPartitionJetFour_pos hx.le

/-- The reflected likelihood first jet is strictly negative away from the seam. -/
theorem thetaCuspReflectedLikelihoodCumulantJetOne_neg
    {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    thetaCuspReflectedLikelihoodCumulantJetOne u t < 0 := by
  unfold thetaCuspReflectedLikelihoodCumulantJetOne
  exact sub_neg.mpr
    (strictMonoOn_thetaCuspLikelihoodSourceLogPartitionJetOne
      (by simp; linarith) (by simp; linarith) (by linarith))

/-- The reflected likelihood second jet is strictly negative. -/
theorem thetaCuspReflectedLikelihoodCumulantJetTwo_neg
    {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    thetaCuspReflectedLikelihoodCumulantJetTwo u t < 0 := by
  have hminus :=
    thetaCuspLikelihoodSourceLogPartitionJetTwo_pos
      (show 0 ≤ u - t by linarith)
  have hplus :=
    thetaCuspLikelihoodSourceLogPartitionJetTwo_pos
      (show 0 ≤ u + t by linarith)
  unfold thetaCuspReflectedLikelihoodCumulantJetTwo
  linarith

/-- The reflected likelihood third jet is strictly negative. -/
theorem thetaCuspReflectedLikelihoodCumulantJetThree_neg
    {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    thetaCuspReflectedLikelihoodCumulantJetThree u t < 0 := by
  unfold thetaCuspReflectedLikelihoodCumulantJetThree
  exact sub_neg.mpr
    (strictMonoOn_thetaCuspLikelihoodSourceLogPartitionJetThree
      (by simp; linarith) (by simp; linarith) (by linarith))

/-- **Unconditional likelihood Riccati law.**  The reflected higher-tail likelihood action has
strictly positive Riccati margin throughout the same-half-line chamber. -/
theorem thetaCuspReflectedLikelihoodCumulantRiccatiMargin_pos
    {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    0 < thetaCuspReflectedLikelihoodCumulantRiccatiMargin u t := by
  have h1 := thetaCuspReflectedLikelihoodCumulantJetOne_neg ht htu
  have h2 := thetaCuspReflectedLikelihoodCumulantJetTwo_neg ht htu
  have h3 := thetaCuspReflectedLikelihoodCumulantJetThree_neg ht htu
  unfold thetaCuspReflectedLikelihoodCumulantRiccatiMargin
  nlinarith [mul_pos (neg_pos.mpr h1) (neg_pos.mpr h2)]

/-- Exact mixed Riccati term between the first atom and the higher likelihood action. -/
def thetaCuspReflectedAtomLikelihoodRiccatiCross (u t : ℝ) : ℝ :=
  2 * (thetaCuspSingleAtomReflectedActionJetOne
        (thetaCuspSingleAtomReflectionScale 1 u)
        (thetaCuspSingleAtomReflectionDefect t)
        (2 * Real.sinh (2 * t)) *
      thetaCuspReflectedLikelihoodCumulantJetTwo u t +
    thetaCuspReflectedLikelihoodCumulantJetOne u t *
      thetaCuspSingleAtomReflectedActionJetTwo
        (thetaCuspSingleAtomReflectionScale 1 u)
        (thetaCuspSingleAtomReflectionDefect t))

/-- The first atom's reflected first jet is strictly positive. -/
theorem thetaCuspSingleAtomReflectedActionJetOne_pos_of_sameHalfLine
    {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    0 < thetaCuspSingleAtomReflectedActionJetOne
      (thetaCuspSingleAtomReflectionScale 1 u)
      (thetaCuspSingleAtomReflectionDefect t)
      (2 * Real.sinh (2 * t)) := by
  let A := thetaCuspSingleAtomReflectionScale 1 u
  let z := thetaCuspSingleAtomReflectionDefect t
  let l := thetaCuspSingleAtomReflectionLambda A
  let r := thetaCuspSingleAtomReflectionFactor A z
  have hu : 0 ≤ u := le_trans ht.le htu
  have hA : 3 < A := by
    simpa only [A] using
      three_lt_thetaCuspSingleAtomReflectionScale (n := 1) (by norm_num) hu
  have hl : 0 < l := by
    simpa only [l] using thetaCuspSingleAtomReflectionLambda_pos hA
  have hr : 0 < r := by
    simpa only [A, z, r] using
      thetaCuspSingleAtomReflectionFactor_pos_of_sameHalfLine
        (n := 1) (by norm_num) ht.le htu
  have hslope : 0 < thetaCuspSingleAtomReflectionSlope A z := by
    unfold thetaCuspSingleAtomReflectionSlope
    positivity
  have hz' : 0 < 2 * Real.sinh (2 * t) := by
    have := Real.sinh_pos_iff.mpr (show 0 < 2 * t by linarith)
    positivity
  unfold thetaCuspSingleAtomReflectedActionJetOne
  exact mul_pos hslope hz'

/-- The first atom's reflected second jet is strictly positive. -/
theorem thetaCuspSingleAtomReflectedActionJetTwo_pos_of_sameHalfLine
    {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    0 < thetaCuspSingleAtomReflectedActionJetTwo
      (thetaCuspSingleAtomReflectionScale 1 u)
      (thetaCuspSingleAtomReflectionDefect t) := by
  let A := thetaCuspSingleAtomReflectionScale 1 u
  let z := thetaCuspSingleAtomReflectionDefect t
  let l := thetaCuspSingleAtomReflectionLambda A
  let r := thetaCuspSingleAtomReflectionFactor A z
  have hu : 0 ≤ u := le_trans ht.le htu
  have hA : 3 < A := by
    simpa only [A] using
      three_lt_thetaCuspSingleAtomReflectionScale (n := 1) (by norm_num) hu
  have hl : 0 < l := by
    simpa only [l] using thetaCuspSingleAtomReflectionLambda_pos hA
  have hr : 0 < r := by
    simpa only [A, z, r] using
      thetaCuspSingleAtomReflectionFactor_pos_of_sameHalfLine
        (n := 1) (by norm_num) ht.le htu
  have hz : 0 < z := by
    dsimp [z, thetaCuspSingleAtomReflectionDefect]
    exact sub_pos.mpr (Real.one_lt_cosh.mpr (by linarith))
  have hslope : 0 < thetaCuspSingleAtomReflectionSlope A z := by
    unfold thetaCuspSingleAtomReflectionSlope
    positivity
  unfold thetaCuspSingleAtomReflectedActionJetTwo
  dsimp only
  positivity

/-- The atom--likelihood mixed Riccati channel is strictly negative. -/
theorem thetaCuspReflectedAtomLikelihoodRiccatiCross_neg
    {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    thetaCuspReflectedAtomLikelihoodRiccatiCross u t < 0 := by
  have ha1 :=
    thetaCuspSingleAtomReflectedActionJetOne_pos_of_sameHalfLine ht htu
  have ha2 :=
    thetaCuspSingleAtomReflectedActionJetTwo_pos_of_sameHalfLine ht htu
  have hl1 := thetaCuspReflectedLikelihoodCumulantJetOne_neg ht htu
  have hl2 := thetaCuspReflectedLikelihoodCumulantJetTwo_neg ht htu
  unfold thetaCuspReflectedAtomLikelihoodRiccatiCross
  nlinarith [mul_neg_of_pos_of_neg ha1 hl2, mul_neg_of_neg_of_pos hl1 ha2]

/-- The old cumulant correction is exactly likelihood margin plus mixed interference. -/
theorem thetaCuspReflectedLikelihoodCumulantCorrection_eq_margin_add_cross
    (u t : ℝ) :
    thetaCuspReflectedLikelihoodCumulantCorrection u t =
      thetaCuspReflectedLikelihoodCumulantRiccatiMargin u t +
        thetaCuspReflectedAtomLikelihoodRiccatiCross u t := by
  rfl

/-- Exact three-channel decomposition of the completed Riccati margin. -/
theorem thetaCuspCompletedReflectedCumulantRiccatiMargin_eq_atom_add_likelihood_add_cross
    (u t : ℝ) :
    thetaCuspCompletedReflectedCumulantRiccatiMargin u t =
      thetaCuspSingleAtomReflectedRiccatiMargin
          (thetaCuspSingleAtomReflectionScale 1 u)
          (thetaCuspSingleAtomReflectionDefect t)
          (2 * Real.sinh (2 * t)) +
        thetaCuspReflectedLikelihoodCumulantRiccatiMargin u t +
        thetaCuspReflectedAtomLikelihoodRiccatiCross u t := by
  rw [thetaCuspCompletedReflectedCumulantRiccatiMargin_eq_atom_add_correction,
    thetaCuspReflectedLikelihoodCumulantCorrection_eq_margin_add_cross]
  ring

/-- **Exact remaining same-half-line obstruction.**  Both component margins are now unconditional
and positive; completed positivity is equivalent to their domination of the unique negative
atom--likelihood interference channel. -/
theorem thetaCuspCompletedReflectedCumulantRiccatiMargin_pos_iff_cross_domination
    (u t : ℝ) :
    0 < thetaCuspCompletedReflectedCumulantRiccatiMargin u t ↔
      -thetaCuspReflectedAtomLikelihoodRiccatiCross u t <
        thetaCuspSingleAtomReflectedRiccatiMargin
            (thetaCuspSingleAtomReflectionScale 1 u)
            (thetaCuspSingleAtomReflectionDefect t)
            (2 * Real.sinh (2 * t)) +
          thetaCuspReflectedLikelihoodCumulantRiccatiMargin u t := by
  rw [thetaCuspCompletedReflectedCumulantRiccatiMargin_eq_atom_add_likelihood_add_cross]
  constructor <;> intro h <;> linarith

end

end RHTower
