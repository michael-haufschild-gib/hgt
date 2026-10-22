import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspLikelihoodEighthScoreRayTransform

/-!
# Strict positivity of the ordinary eighth theta likelihood source jet

The complete higher-tail spectral measure splits into theta atom-rays.  The dominant gap-three
component is positive only after exact Dirac--ray compensation; every later component begins in
the pointwise positive score chamber.  Summing these positive masses proves strict positivity of
the full ordinary eighth source jet on the physical half-line.
-/

open MeasureTheory Set

namespace RHTower

noncomputable section

/-- Normalized one-particle ordinary eighth source score of the higher theta likelihood. -/
def thetaCuspLikelihoodSourceOrdinaryJetEight (x : ℝ) : ℝ :=
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  256 * (A ^ 8 * thetaCuspLikelihoodNormalizedMoment B 8 -
    28 * A ^ 7 * thetaCuspLikelihoodNormalizedMoment B 7 +
    266 * A ^ 6 * thetaCuspLikelihoodNormalizedMoment B 6 -
    1050 * A ^ 5 * thetaCuspLikelihoodNormalizedMoment B 5 +
    1701 * A ^ 4 * thetaCuspLikelihoodNormalizedMoment B 4 -
    966 * A ^ 3 * thetaCuspLikelihoodNormalizedMoment B 3 +
    127 * A ^ 2 * thetaCuspLikelihoodNormalizedMoment B 2 -
    A * thetaCuspLikelihoodMean B)

theorem integrable_thetaCuspLikelihoodEighthSourceScore_mul_exp_neg_higherSpectral
    (A : ℝ) {B : ℝ} (hB : 0 < B) :
    Integrable (fun t : ℝ =>
      thetaCuspLikelihoodEighthSourceScore (A * t) * Real.exp (-(B * t)))
      thetaCuspHigherLikelihoodSpectralMeasure := by
  have h8 :=
    (integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure 8 hB).const_mul (A ^ 8)
  have h7 :=
    (integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure 7 hB).const_mul (28 * A ^ 7)
  have h6 :=
    (integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure 6 hB).const_mul (266 * A ^ 6)
  have h5 :=
    (integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure 5 hB).const_mul (1050 * A ^ 5)
  have h4 :=
    (integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure 4 hB).const_mul (1701 * A ^ 4)
  have h3 :=
    (integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure 3 hB).const_mul (966 * A ^ 3)
  have h2 :=
    (integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure 2 hB).const_mul (127 * A ^ 2)
  have h1 :=
    (integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure 1 hB).const_mul A
  have hsum := (((((((h8.sub h7).add h6).sub h5).add h4).sub h3).add h2).sub h1)
  convert hsum using 1
  funext t
  simp only [Pi.add_apply, Pi.sub_apply]
  unfold thetaCuspLikelihoodEighthSourceScore
  ring

/-- The ordinary eighth jet is the normalized integral of the literal eighth score. -/
theorem thetaCuspLikelihoodSourceOrdinaryJetEight_eq_spectralIntegral
    {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspLikelihoodSourceOrdinaryJetEight x =
      256 / thetaCuspLikelihoodPartition (thetaCuspLikelihoodCoordinate x) *
        (∫ t : ℝ, thetaCuspLikelihoodEighthSourceScore
              (thetaCuspSingleAtomReflectionScale 1 x * t) *
            Real.exp (-(thetaCuspLikelihoodCoordinate x * t))
          ∂thetaCuspHigherLikelihoodSpectralMeasure) := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  have hB : 0 < B := by
    simpa only [B] using thetaCuspLikelihoodCoordinate_pos hx
  have h8 := integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure 8 hB
  have h7 := integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure 7 hB
  have h6 := integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure 6 hB
  have h5 := integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure 5 hB
  have h4 := integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure 4 hB
  have h3 := integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure 3 hB
  have h2 := integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure 2 hB
  have h1 := integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure 1 hB
  have hscore :
      (∫ t : ℝ, thetaCuspLikelihoodEighthSourceScore (A * t) * Real.exp (-(B * t))
        ∂thetaCuspHigherLikelihoodSpectralMeasure) =
      A ^ 8 * thetaCuspHigherLikelihoodSpectralMoment B 8 -
        28 * A ^ 7 * thetaCuspHigherLikelihoodSpectralMoment B 7 +
        266 * A ^ 6 * thetaCuspHigherLikelihoodSpectralMoment B 6 -
        1050 * A ^ 5 * thetaCuspHigherLikelihoodSpectralMoment B 5 +
        1701 * A ^ 4 * thetaCuspHigherLikelihoodSpectralMoment B 4 -
        966 * A ^ 3 * thetaCuspHigherLikelihoodSpectralMoment B 3 +
        127 * A ^ 2 * thetaCuspHigherLikelihoodSpectralMoment B 2 -
        A * thetaCuspHigherLikelihoodSpectralMoment B 1 := by
    let f8 : ℝ → ℝ := fun t => A ^ 8 * (t ^ 8 * Real.exp (-(B * t)))
    let f7 : ℝ → ℝ := fun t => (28 * A ^ 7) * (t ^ 7 * Real.exp (-(B * t)))
    let f6 : ℝ → ℝ := fun t => (266 * A ^ 6) * (t ^ 6 * Real.exp (-(B * t)))
    let f5 : ℝ → ℝ := fun t => (1050 * A ^ 5) * (t ^ 5 * Real.exp (-(B * t)))
    let f4 : ℝ → ℝ := fun t => (1701 * A ^ 4) * (t ^ 4 * Real.exp (-(B * t)))
    let f3 : ℝ → ℝ := fun t => (966 * A ^ 3) * (t ^ 3 * Real.exp (-(B * t)))
    let f2 : ℝ → ℝ := fun t => (127 * A ^ 2) * (t ^ 2 * Real.exp (-(B * t)))
    let f1 : ℝ → ℝ := fun t => A * (t ^ 1 * Real.exp (-(B * t)))
    have hf8 : Integrable f8 thetaCuspHigherLikelihoodSpectralMeasure := by
      simpa only [f8, neg_mul] using h8.const_mul (A ^ 8)
    have hf7 : Integrable f7 thetaCuspHigherLikelihoodSpectralMeasure := by
      simpa only [f7, neg_mul] using h7.const_mul (28 * A ^ 7)
    have hf6 : Integrable f6 thetaCuspHigherLikelihoodSpectralMeasure := by
      simpa only [f6, neg_mul] using h6.const_mul (266 * A ^ 6)
    have hf5 : Integrable f5 thetaCuspHigherLikelihoodSpectralMeasure := by
      simpa only [f5, neg_mul] using h5.const_mul (1050 * A ^ 5)
    have hf4 : Integrable f4 thetaCuspHigherLikelihoodSpectralMeasure := by
      simpa only [f4, neg_mul] using h4.const_mul (1701 * A ^ 4)
    have hf3 : Integrable f3 thetaCuspHigherLikelihoodSpectralMeasure := by
      simpa only [f3, neg_mul] using h3.const_mul (966 * A ^ 3)
    have hf2 : Integrable f2 thetaCuspHigherLikelihoodSpectralMeasure := by
      simpa only [f2, neg_mul] using h2.const_mul (127 * A ^ 2)
    have hf1 : Integrable f1 thetaCuspHigherLikelihoodSpectralMeasure := by
      simpa only [f1, neg_mul] using h1.const_mul A
    rw [show (fun t : ℝ => thetaCuspLikelihoodEighthSourceScore (A * t) *
        Real.exp (-(B * t))) = (((((((f8 - f7) + f6) - f5) + f4) - f3) + f2) - f1) by
      funext t
      dsimp [f8, f7, f6, f5, f4, f3, f2, f1,
        thetaCuspLikelihoodEighthSourceScore]
      ring]
    rw [integral_sub' (((((hf8.sub hf7).add hf6).sub hf5).add hf4).sub hf3 |>.add hf2) hf1,
      integral_add' ((((hf8.sub hf7).add hf6).sub hf5).add hf4 |>.sub hf3) hf2,
      integral_sub' (((hf8.sub hf7).add hf6).sub hf5 |>.add hf4) hf3,
      integral_add' ((hf8.sub hf7).add hf6 |>.sub hf5) hf4,
      integral_sub' (hf8.sub hf7 |>.add hf6) hf5,
      integral_add' (hf8.sub hf7) hf6, integral_sub' hf8 hf7]
    simp only [f8, f7, f6, f5, f4, f3, f2, f1, integral_const_mul]
    have hM (m : ℕ) :
        (∫ t : ℝ, t ^ m * Real.exp (-(B * t))
          ∂thetaCuspHigherLikelihoodSpectralMeasure) =
          thetaCuspHigherLikelihoodSpectralMoment B m := by
      rw [thetaCuspHigherLikelihoodSpectralMoment_eq_integral]
      apply integral_congr_ae
      filter_upwards with t
      congr 1
      ring
    rw [hM 8, hM 7, hM 6, hM 5, hM 4, hM 3, hM 2, hM 1]
  rw [thetaCuspLikelihoodSourceOrdinaryJetEight]
  dsimp only [A, B] at hscore ⊢
  rw [hscore]
  unfold thetaCuspLikelihoodNormalizedMoment thetaCuspLikelihoodMean
  ring

/-- Literal integrated eighth-score mass of one higher theta atom-ray. -/
def thetaCuspLikelihoodAtomEighthScoreMass (n : ℕ) (A B : ℝ) : ℝ :=
  ∫ t : ℝ, thetaCuspLikelihoodEighthSourceScore (A * t) * Real.exp (-(B * t))
    ∂thetaCuspAtomLikelihoodSpectralMeasure n

/-- Exact point--ray evaluation of one atom's eighth-score mass. -/
theorem thetaCuspLikelihoodAtomEighthScoreMass_eq
    (n : ℕ) (hn : 2 ≤ n) (A : ℝ) {B : ℝ} (hB : 0 < B) :
    thetaCuspLikelihoodAtomEighthScoreMass n A B =
      thetaCuspLikelihoodAtomWeight n *
        (thetaCuspLikelihoodEighthSourceScore (A * thetaCuspLikelihoodGap n) *
          Real.exp (-(B * thetaCuspLikelihoodGap n))) +
      thetaCuspLikelihoodRayWeight n *
        (Real.exp (-(B * thetaCuspLikelihoodGap n)) / B *
          thetaCuspLikelihoodEighthSourceScoreRayTransform (A / B)
            (A * thetaCuspLikelihoodGap n)) := by
  let f : ℝ → ℝ := fun t =>
    thetaCuspLikelihoodEighthSourceScore (A * t) * Real.exp (-(B * t))
  have hd : Integrable f (Measure.dirac (thetaCuspLikelihoodGap n)) :=
    integrable_dirac (by dsimp [f]; finiteness)
  have hd0 : 0 ≤ thetaCuspLikelihoodGap n := (thetaCuspLikelihoodGap_pos hn).le
  have hr : Integrable f (volume.restrict (Ioi (thetaCuspLikelihoodGap n))) := by
    change IntegrableOn f (Ioi (thetaCuspLikelihoodGap n))
    simpa only [f] using
      integrableOn_thetaCuspLikelihoodEighthSourceScore_mul_exp_neg_rate A hd0 hB
  have hd' : Integrable f
      (ENNReal.ofReal (thetaCuspLikelihoodAtomWeight n) •
        Measure.dirac (thetaCuspLikelihoodGap n)) := hd.smul_measure (by simp)
  have hr' : Integrable f
      (ENNReal.ofReal (thetaCuspLikelihoodRayWeight n) •
        volume.restrict (Ioi (thetaCuspLikelihoodGap n))) := hr.smul_measure (by simp)
  rw [thetaCuspLikelihoodAtomEighthScoreMass,
    thetaCuspAtomLikelihoodSpectralMeasure,
    integral_add_measure hd' hr', integral_smul_measure, integral_dirac,
    integral_smul_measure]
  change ENNReal.toReal (ENNReal.ofReal (thetaCuspLikelihoodAtomWeight n)) *
      f (thetaCuspLikelihoodGap n) +
    ENNReal.toReal (ENNReal.ofReal (thetaCuspLikelihoodRayWeight n)) *
      (∫ t : ℝ in Ioi (thetaCuspLikelihoodGap n), f t) = _
  rw [ENNReal.toReal_ofReal (thetaCuspLikelihoodAtomWeight_pos (by omega)).le,
    ENNReal.toReal_ofReal (thetaCuspLikelihoodRayWeight_pos hn).le,
    integral_Ioi_thetaCuspLikelihoodEighthSourceScore_mul_exp_neg_rate A
      (thetaCuspLikelihoodGap n) hB]

/-- The dominant gap-three atom-ray has strictly positive integrated eighth score. -/
theorem thetaCuspLikelihoodDominantAtomEighthScoreMass_pos
    {A B : ℝ} (hA : (157 / 50 : ℝ) ≤ A) (hBA : B = A - 3 / 2) :
    0 < thetaCuspLikelihoodAtomEighthScoreMass 2 A B := by
  have hB : 0 < B := by rw [hBA]; linarith
  rw [thetaCuspLikelihoodAtomEighthScoreMass_eq 2 (by norm_num) A hB]
  norm_num [thetaCuspLikelihoodGap, thetaCuspLikelihoodAtomWeight,
    thetaCuspLikelihoodRayWeight]
  have hcore := thetaCuspLikelihoodDominantEighthScoreCore_pos hA
  rw [hBA]
  have hpref : 0 < Real.exp (-(9 / 2 : ℝ)) * Real.exp (-((A - 3 / 2) * 3)) := by
    positivity
  calc
    0 < (Real.exp (-(9 / 2 : ℝ)) * Real.exp (-((A - 3 / 2) * 3))) *
        (16 * thetaCuspLikelihoodEighthSourceScore (3 * A) +
          18 / (A - 3 / 2) * thetaCuspLikelihoodEighthSourceScoreRayTransform
            (A / (A - 3 / 2)) (3 * A)) := mul_pos hpref hcore
    _ = _ := by ring

/-- Every stable atom-ray `n ≥ 3` has strictly positive integrated eighth score. -/
theorem thetaCuspLikelihoodStableAtomEighthScoreMass_pos
    {n : ℕ} (hn : 3 ≤ n) {A B : ℝ}
    (hA : Real.pi ≤ A) (hBA : B = A - 3 / 2) :
    0 < thetaCuspLikelihoodAtomEighthScoreMass n A B := by
  let d := thetaCuspLikelihoodGap n
  have hd : 8 ≤ d := by
    dsimp [d, thetaCuspLikelihoodGap]
    have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  have hA0 : 0 < A := Real.pi_pos.trans_le hA
  have hB : 0 < B := by rw [hBA]; nlinarith [Real.pi_gt_three]
  have hAt : 24 ≤ A * d := by
    have hmul := mul_le_mul hA hd (by norm_num : (0 : ℝ) ≤ 8) hA0.le
    nlinarith [Real.pi_gt_three]
  have hpoint := thetaCuspLikelihoodEighthSourceScore_pos_of_fourteen_le
    (hAt.trans' (by norm_num))
  have hray :=
    thetaCuspLikelihoodEighthSourceScoreRayTransform_nonneg_of_twentyFour_le
      (div_nonneg hA0.le hB.le) hAt
  rw [thetaCuspLikelihoodAtomEighthScoreMass_eq n (by omega) A hB]
  change _ * (thetaCuspLikelihoodEighthSourceScore (A * d) * _) +
    _ * (_ / B * thetaCuspLikelihoodEighthSourceScoreRayTransform
      (A / B) (A * d)) > 0
  have ha := thetaCuspLikelihoodAtomWeight_pos (lt_of_lt_of_le (by omega) hn)
  have hr := thetaCuspLikelihoodRayWeight_pos (by omega : 2 ≤ n)
  positivity

theorem integral_thetaCuspLikelihoodEighthSourceScore_eq_tsum_atom
    (A : ℝ) {B : ℝ} (hB : 0 < B) :
    (∫ t : ℝ, thetaCuspLikelihoodEighthSourceScore (A * t) * Real.exp (-(B * t))
      ∂thetaCuspHigherLikelihoodSpectralMeasure) =
      ∑' k : ℕ, thetaCuspLikelihoodAtomEighthScoreMass (k + 2) A B := by
  rw [thetaCuspHigherLikelihoodSpectralMeasure,
    integral_sum_measure
      (integrable_thetaCuspLikelihoodEighthSourceScore_mul_exp_neg_higherSpectral A hB)]
  rfl

theorem summable_thetaCuspLikelihoodAtomEighthScoreMass
    (A : ℝ) {B : ℝ} (hB : 0 < B) :
    Summable (fun k : ℕ => thetaCuspLikelihoodAtomEighthScoreMass (k + 2) A B) := by
  let f : ℝ → ℝ := fun t =>
    thetaCuspLikelihoodEighthSourceScore (A * t) * Real.exp (-(B * t))
  have hInt :=
    integrable_thetaCuspLikelihoodEighthSourceScore_mul_exp_neg_higherSpectral A hB
  rw [thetaCuspHigherLikelihoodSpectralMeasure] at hInt
  have hnorm := hInt.summable_integral
  apply Summable.of_norm_bounded hnorm
  intro k
  exact norm_integral_le_integral_norm _

/-- The complete higher-tail spectral integral of the eighth score is strictly positive. -/
theorem integral_thetaCuspLikelihoodEighthSourceScore_pos
    {A B : ℝ} (hA : (157 / 50 : ℝ) ≤ A)
    (hApi : Real.pi ≤ A) (hBA : B = A - 3 / 2) :
    0 < ∫ t : ℝ, thetaCuspLikelihoodEighthSourceScore (A * t) * Real.exp (-(B * t))
      ∂thetaCuspHigherLikelihoodSpectralMeasure := by
  have hB : 0 < B := by rw [hBA]; linarith
  have hs := summable_thetaCuspLikelihoodAtomEighthScoreMass A hB
  have hnonneg : ∀ k : ℕ,
      0 ≤ thetaCuspLikelihoodAtomEighthScoreMass (k + 2) A B := by
    intro k
    cases k with
    | zero =>
        simpa using (thetaCuspLikelihoodDominantAtomEighthScoreMass_pos hA hBA).le
    | succ k =>
        exact (thetaCuspLikelihoodStableAtomEighthScoreMass_pos
          (n := k + 3) (by omega) hApi hBA).le
  have hfirst : 0 < thetaCuspLikelihoodAtomEighthScoreMass (0 + 2) A B := by
    simpa using thetaCuspLikelihoodDominantAtomEighthScoreMass_pos hA hBA
  rw [integral_thetaCuspLikelihoodEighthSourceScore_eq_tsum_atom A hB]
  exact hs.tsum_pos hnonneg 0 hfirst

/-- The ordinary eighth theta likelihood source jet is strictly positive on `x ≥ 0`. -/
theorem thetaCuspLikelihoodSourceOrdinaryJetEight_pos
    {x : ℝ} (hx : 0 ≤ x) :
    0 < thetaCuspLikelihoodSourceOrdinaryJetEight x := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  have hApi : Real.pi ≤ A := by
    dsimp [A, thetaCuspSingleAtomReflectionScale]
    norm_num
    have he : 1 ≤ Real.exp (2 * x) := Real.one_le_exp (by linarith)
    simpa only [mul_one] using mul_le_mul_of_nonneg_left he Real.pi_pos.le
  have hA : (157 / 50 : ℝ) ≤ A := by
    have hpi := Real.pi_gt_d2
    norm_num at hpi
    linarith
  have hBA : B = A - 3 / 2 := by
    dsimp [A, B, thetaCuspLikelihoodCoordinate, thetaCuspSingleAtomReflectionScale]
    norm_num
    rw [show Real.exp (2 * x) = Real.exp x ^ 2 by
      rw [show 2 * x = x + x by ring, Real.exp_add]
      ring]
  have hB : 0 < B := by rw [hBA]; linarith
  rw [thetaCuspLikelihoodSourceOrdinaryJetEight_eq_spectralIntegral hx]
  exact mul_pos
    (div_pos (by norm_num) (thetaCuspLikelihoodPartition_pos hB))
    (integral_thetaCuspLikelihoodEighthSourceScore_pos hA hApi hBA)

/-! ### Quantitative survival of the leading eighth moment -/

/-- Integrated leading eighth-monomial mass of one higher theta atom-ray. -/
def thetaCuspLikelihoodAtomEighthMonomialMass (n : ℕ) (A B : ℝ) : ℝ :=
  ∫ t : ℝ, (A * t) ^ 8 * Real.exp (-(B * t))
    ∂thetaCuspAtomLikelihoodSpectralMeasure n

private theorem integrableOn_pow_mul_exp_neg_rate_eighthMonomial
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

/-- Exact point--ray evaluation of one leading eighth-monomial mass. -/
theorem thetaCuspLikelihoodAtomEighthMonomialMass_eq
    (n : ℕ) (hn : 2 ≤ n) (A : ℝ) {B : ℝ} (hB : 0 < B) :
    thetaCuspLikelihoodAtomEighthMonomialMass n A B =
      thetaCuspLikelihoodAtomWeight n *
        ((A * thetaCuspLikelihoodGap n) ^ 8 *
          Real.exp (-(B * thetaCuspLikelihoodGap n))) +
      thetaCuspLikelihoodRayWeight n *
        (Real.exp (-(B * thetaCuspLikelihoodGap n)) / B *
          thetaCuspLikelihoodEighthMonomialRayTransform (A / B)
            (A * thetaCuspLikelihoodGap n)) := by
  let f : ℝ → ℝ := fun t => (A * t) ^ 8 * Real.exp (-(B * t))
  have hd : Integrable f (Measure.dirac (thetaCuspLikelihoodGap n)) :=
    integrable_dirac (by dsimp [f]; finiteness)
  have hd0 : 0 ≤ thetaCuspLikelihoodGap n := (thetaCuspLikelihoodGap_pos hn).le
  have hr : Integrable f (volume.restrict (Ioi (thetaCuspLikelihoodGap n))) := by
    change IntegrableOn f (Ioi (thetaCuspLikelihoodGap n))
    have hmono :=
      (integrableOn_pow_mul_exp_neg_rate_eighthMonomial 8 hB).mono_set fun t ht =>
        lt_of_le_of_lt hd0 ht
    exact (hmono.const_mul (A ^ 8)).congr (by
      filter_upwards with t
      dsimp [f]
      ring)
  have hd' : Integrable f
      (ENNReal.ofReal (thetaCuspLikelihoodAtomWeight n) •
        Measure.dirac (thetaCuspLikelihoodGap n)) := hd.smul_measure (by simp)
  have hr' : Integrable f
      (ENNReal.ofReal (thetaCuspLikelihoodRayWeight n) •
        volume.restrict (Ioi (thetaCuspLikelihoodGap n))) := hr.smul_measure (by simp)
  rw [thetaCuspLikelihoodAtomEighthMonomialMass,
    thetaCuspAtomLikelihoodSpectralMeasure,
    integral_add_measure hd' hr', integral_smul_measure, integral_dirac,
    integral_smul_measure]
  change ENNReal.toReal (ENNReal.ofReal (thetaCuspLikelihoodAtomWeight n)) *
      f (thetaCuspLikelihoodGap n) +
    ENNReal.toReal (ENNReal.ofReal (thetaCuspLikelihoodRayWeight n)) *
      (∫ t : ℝ in Ioi (thetaCuspLikelihoodGap n), f t) = _
  rw [ENNReal.toReal_ofReal (thetaCuspLikelihoodAtomWeight_pos (by omega)).le,
    ENNReal.toReal_ofReal (thetaCuspLikelihoodRayWeight_pos hn).le,
    integral_Ioi_thetaCuspLikelihoodEighthMonomial_mul_exp_neg_rate A
      (thetaCuspLikelihoodGap n) hB]

/-- Dominant component retains strictly more than one hundredth of its leading eighth moment. -/
theorem one_hundredth_mul_thetaCuspLikelihoodDominantAtomEighthMonomialMass_lt
    {A B : ℝ} (hA : (157 / 50 : ℝ) ≤ A) (hBA : B = A - 3 / 2) :
    (1 / 100 : ℝ) * thetaCuspLikelihoodAtomEighthMonomialMass 2 A B <
      thetaCuspLikelihoodAtomEighthScoreMass 2 A B := by
  have hB : 0 < B := by rw [hBA]; linarith
  rw [thetaCuspLikelihoodAtomEighthMonomialMass_eq 2 (by norm_num) A hB,
    thetaCuspLikelihoodAtomEighthScoreMass_eq 2 (by norm_num) A hB]
  norm_num [thetaCuspLikelihoodGap, thetaCuspLikelihoodAtomWeight,
    thetaCuspLikelihoodRayWeight]
  have hcore := one_hundredth_mul_thetaCuspLikelihoodDominantEighthMomentCore_lt hA
  rw [hBA]
  let p := Real.exp (-(9 / 2 : ℝ)) * Real.exp (-((A - 3 / 2) * 3))
  have hp : 0 < p := by dsimp only [p]; positivity
  have hexp : Real.exp (-((A - 3 / 2) * 3)) = Real.exp (9 / 2 - A * 3) := by
    congr 1
    ring
  calc
    (1 / 100 : ℝ) *
        (Real.exp (-(9 / 2 : ℝ)) * 16 *
            ((A * 3) ^ 8 * Real.exp (-((A - 3 / 2) * 3))) +
          Real.exp (-(9 / 2 : ℝ)) * (3 / 2 : ℝ) * 4 * 3 *
            (Real.exp (-((A - 3 / 2) * 3)) / (A - 3 / 2) *
              thetaCuspLikelihoodEighthMonomialRayTransform
                (A / (A - 3 / 2)) (A * 3))) =
      p * ((1 / 100 : ℝ) * (16 * (3 * A) ^ 8 + 18 / (A - 3 / 2) *
        thetaCuspLikelihoodEighthMonomialRayTransform
          (A / (A - 3 / 2)) (3 * A))) := by
      dsimp only [p]
      rw [hexp]
      ring
    _ < p * (16 * thetaCuspLikelihoodEighthSourceScore (3 * A) +
        18 / (A - 3 / 2) * thetaCuspLikelihoodEighthSourceScoreRayTransform
          (A / (A - 3 / 2)) (3 * A)) := mul_lt_mul_of_pos_left hcore hp
    _ = _ := by
      dsimp only [p]
      rw [hexp]
      ring

/-- Stable components retain at least one hundredth of their leading eighth moment. -/
theorem one_hundredth_mul_thetaCuspLikelihoodStableAtomEighthMonomialMass_le
    {n : ℕ} (hn : 3 ≤ n) {A B : ℝ}
    (hA : Real.pi ≤ A) (hBA : B = A - 3 / 2) :
    (1 / 100 : ℝ) * thetaCuspLikelihoodAtomEighthMonomialMass n A B ≤
      thetaCuspLikelihoodAtomEighthScoreMass n A B := by
  let d := thetaCuspLikelihoodGap n
  have hd : 8 ≤ d := by
    dsimp [d, thetaCuspLikelihoodGap]
    have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  have hA0 : 0 < A := Real.pi_pos.trans_le hA
  have hB : 0 < B := by rw [hBA]; nlinarith [Real.pi_gt_three]
  have hAt : 24 ≤ A * d := by
    have hmul := mul_le_mul hA hd (by norm_num : (0 : ℝ) ≤ 8) hA0.le
    nlinarith [Real.pi_gt_three]
  have hpoint := one_hundredth_mul_thetaCuspLikelihoodEighthMonomialRayTransform_le
    (r := 0) (z := A * d) (by norm_num) hAt
  have hray := one_hundredth_mul_thetaCuspLikelihoodEighthMonomialRayTransform_le
    (r := A / B) (z := A * d) (div_nonneg hA0.le hB.le) hAt
  norm_num [thetaCuspLikelihoodEighthMonomialRayTransform,
    thetaCuspLikelihoodEighthSourceScoreRayTransform] at hpoint
  rw [thetaCuspLikelihoodAtomEighthMonomialMass_eq n (by omega) A hB,
    thetaCuspLikelihoodAtomEighthScoreMass_eq n (by omega) A hB]
  change (1 / 100 : ℝ) *
      (_ * ((A * d) ^ 8 * _) + _ * (_ / B *
        thetaCuspLikelihoodEighthMonomialRayTransform (A / B) (A * d))) ≤
    _ * (thetaCuspLikelihoodEighthSourceScore (A * d) * _) +
      _ * (_ / B * thetaCuspLikelihoodEighthSourceScoreRayTransform
        (A / B) (A * d))
  have ha := (thetaCuspLikelihoodAtomWeight_pos
    (lt_of_lt_of_le (by omega) hn)).le
  have hr := (thetaCuspLikelihoodRayWeight_pos (by omega : 2 ≤ n)).le
  have hexp := (Real.exp_pos (-(B * d))).le
  have hdiv : 0 ≤ Real.exp (-(B * d)) / B := div_nonneg hexp hB.le
  have hpoint' : (1 / 100 : ℝ) *
      (thetaCuspLikelihoodAtomWeight n * ((A * d) ^ 8 * Real.exp (-(B * d)))) ≤
      thetaCuspLikelihoodAtomWeight n *
        (thetaCuspLikelihoodEighthSourceScore (A * d) * Real.exp (-(B * d))) := by
    calc
      _ = (thetaCuspLikelihoodAtomWeight n * Real.exp (-(B * d))) *
          ((1 / 100 : ℝ) * (A * d) ^ 8) := by ring
      _ ≤ (thetaCuspLikelihoodAtomWeight n * Real.exp (-(B * d))) *
          thetaCuspLikelihoodEighthSourceScore (A * d) :=
        mul_le_mul_of_nonneg_left hpoint (mul_nonneg ha hexp)
      _ = _ := by ring
  have hray' : (1 / 100 : ℝ) *
      (thetaCuspLikelihoodRayWeight n * (Real.exp (-(B * d)) / B *
        thetaCuspLikelihoodEighthMonomialRayTransform (A / B) (A * d))) ≤
      thetaCuspLikelihoodRayWeight n * (Real.exp (-(B * d)) / B *
        thetaCuspLikelihoodEighthSourceScoreRayTransform (A / B) (A * d)) := by
    calc
      _ = (thetaCuspLikelihoodRayWeight n * (Real.exp (-(B * d)) / B)) *
          ((1 / 100 : ℝ) *
            thetaCuspLikelihoodEighthMonomialRayTransform (A / B) (A * d)) := by ring
      _ ≤ (thetaCuspLikelihoodRayWeight n * (Real.exp (-(B * d)) / B)) *
          thetaCuspLikelihoodEighthSourceScoreRayTransform (A / B) (A * d) :=
        mul_le_mul_of_nonneg_left hray (mul_nonneg hr hdiv)
      _ = _ := by ring
  dsimp only [d]
  nlinarith

/-- Dominant gap-three component retains more than one thirtieth of its leading eighth moment. -/
theorem one_thirtieth_mul_thetaCuspLikelihoodDominantAtomEighthMonomialMass_lt
    {A B : ℝ} (hA : (157 / 50 : ℝ) ≤ A) (hBA : B = A - 3 / 2) :
    (1 / 30 : ℝ) * thetaCuspLikelihoodAtomEighthMonomialMass 2 A B <
      thetaCuspLikelihoodAtomEighthScoreMass 2 A B := by
  have hB : 0 < B := by rw [hBA]; linarith
  rw [thetaCuspLikelihoodAtomEighthMonomialMass_eq 2 (by norm_num) A hB,
    thetaCuspLikelihoodAtomEighthScoreMass_eq 2 (by norm_num) A hB]
  norm_num [thetaCuspLikelihoodGap, thetaCuspLikelihoodAtomWeight,
    thetaCuspLikelihoodRayWeight]
  have hcore := one_thirtieth_mul_thetaCuspLikelihoodDominantEighthMomentCore_lt hA
  rw [hBA]
  let p := Real.exp (-(9 / 2 : ℝ)) * Real.exp (-((A - 3 / 2) * 3))
  have hp : 0 < p := by dsimp only [p]; positivity
  have hexp : Real.exp (-((A - 3 / 2) * 3)) = Real.exp (9 / 2 - A * 3) := by
    congr 1
    ring
  calc
    (1 / 30 : ℝ) *
        (Real.exp (-(9 / 2 : ℝ)) * 16 *
            ((A * 3) ^ 8 * Real.exp (-((A - 3 / 2) * 3))) +
          Real.exp (-(9 / 2 : ℝ)) * (3 / 2 : ℝ) * 4 * 3 *
            (Real.exp (-((A - 3 / 2) * 3)) / (A - 3 / 2) *
              thetaCuspLikelihoodEighthMonomialRayTransform
                (A / (A - 3 / 2)) (A * 3))) =
      p * ((1 / 30 : ℝ) * (16 * (3 * A) ^ 8 + 18 / (A - 3 / 2) *
        thetaCuspLikelihoodEighthMonomialRayTransform
          (A / (A - 3 / 2)) (3 * A))) := by
      dsimp only [p]
      rw [hexp]
      ring
    _ < p * (16 * thetaCuspLikelihoodEighthSourceScore (3 * A) +
        18 / (A - 3 / 2) * thetaCuspLikelihoodEighthSourceScoreRayTransform
          (A / (A - 3 / 2)) (3 * A)) := mul_lt_mul_of_pos_left hcore hp
    _ = _ := by
      dsimp only [p]
      rw [hexp]
      ring

/-- Stable components retain at least one thirtieth of their leading eighth moment. -/
theorem one_thirtieth_mul_thetaCuspLikelihoodStableAtomEighthMonomialMass_le
    {n : ℕ} (hn : 3 ≤ n) {A B : ℝ}
    (hA : Real.pi ≤ A) (hBA : B = A - 3 / 2) :
    (1 / 30 : ℝ) * thetaCuspLikelihoodAtomEighthMonomialMass n A B ≤
      thetaCuspLikelihoodAtomEighthScoreMass n A B := by
  let d := thetaCuspLikelihoodGap n
  have hd : 8 ≤ d := by
    dsimp [d, thetaCuspLikelihoodGap]
    have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  have hA0 : 0 < A := Real.pi_pos.trans_le hA
  have hB : 0 < B := by rw [hBA]; nlinarith [Real.pi_gt_three]
  have hAt : 24 ≤ A * d := by
    have hmul := mul_le_mul hA hd (by norm_num : (0 : ℝ) ≤ 8) hA0.le
    nlinarith [Real.pi_gt_three]
  have hpoint := one_thirtieth_mul_thetaCuspLikelihoodEighthMonomialRayTransform_le
    (r := 0) (z := A * d) (by norm_num) hAt
  have hray := one_thirtieth_mul_thetaCuspLikelihoodEighthMonomialRayTransform_le
    (r := A / B) (z := A * d) (div_nonneg hA0.le hB.le) hAt
  norm_num [thetaCuspLikelihoodEighthMonomialRayTransform,
    thetaCuspLikelihoodEighthSourceScoreRayTransform] at hpoint
  rw [thetaCuspLikelihoodAtomEighthMonomialMass_eq n (by omega) A hB,
    thetaCuspLikelihoodAtomEighthScoreMass_eq n (by omega) A hB]
  change (1 / 30 : ℝ) *
      (_ * ((A * d) ^ 8 * _) + _ * (_ / B *
        thetaCuspLikelihoodEighthMonomialRayTransform (A / B) (A * d))) ≤
    _ * (thetaCuspLikelihoodEighthSourceScore (A * d) * _) +
      _ * (_ / B * thetaCuspLikelihoodEighthSourceScoreRayTransform
        (A / B) (A * d))
  have ha := (thetaCuspLikelihoodAtomWeight_pos
    (lt_of_lt_of_le (by omega) hn)).le
  have hr := (thetaCuspLikelihoodRayWeight_pos (by omega : 2 ≤ n)).le
  have hexp := (Real.exp_pos (-(B * d))).le
  have hdiv : 0 ≤ Real.exp (-(B * d)) / B := div_nonneg hexp hB.le
  have hpoint' : (1 / 30 : ℝ) *
      (thetaCuspLikelihoodAtomWeight n * ((A * d) ^ 8 * Real.exp (-(B * d)))) ≤
      thetaCuspLikelihoodAtomWeight n *
        (thetaCuspLikelihoodEighthSourceScore (A * d) * Real.exp (-(B * d))) := by
    calc
      _ = (thetaCuspLikelihoodAtomWeight n * Real.exp (-(B * d))) *
          ((1 / 30 : ℝ) * (A * d) ^ 8) := by ring
      _ ≤ (thetaCuspLikelihoodAtomWeight n * Real.exp (-(B * d))) *
          thetaCuspLikelihoodEighthSourceScore (A * d) :=
        mul_le_mul_of_nonneg_left hpoint (mul_nonneg ha hexp)
      _ = _ := by ring
  have hray' : (1 / 30 : ℝ) *
      (thetaCuspLikelihoodRayWeight n * (Real.exp (-(B * d)) / B *
        thetaCuspLikelihoodEighthMonomialRayTransform (A / B) (A * d))) ≤
      thetaCuspLikelihoodRayWeight n * (Real.exp (-(B * d)) / B *
        thetaCuspLikelihoodEighthSourceScoreRayTransform (A / B) (A * d)) := by
    calc
      _ = (thetaCuspLikelihoodRayWeight n * (Real.exp (-(B * d)) / B)) *
          ((1 / 30 : ℝ) *
            thetaCuspLikelihoodEighthMonomialRayTransform (A / B) (A * d)) := by ring
      _ ≤ (thetaCuspLikelihoodRayWeight n * (Real.exp (-(B * d)) / B)) *
          thetaCuspLikelihoodEighthSourceScoreRayTransform (A / B) (A * d) :=
        mul_le_mul_of_nonneg_left hray (mul_nonneg hr hdiv)
      _ = _ := by ring
  dsimp only [d]
  nlinarith

theorem summable_thetaCuspLikelihoodAtomEighthMonomialMass
    (A : ℝ) {B : ℝ} (hB : 0 < B) :
    Summable (fun k : ℕ => thetaCuspLikelihoodAtomEighthMonomialMass (k + 2) A B) := by
  let f : ℝ → ℝ := fun t => (A * t) ^ 8 * Real.exp (-(B * t))
  have hInt : Integrable f thetaCuspHigherLikelihoodSpectralMeasure := by
    have h :=
      (integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure 8 hB).const_mul
        (A ^ 8)
    convert h using 1
    funext t
    dsimp [f]
    ring
  rw [thetaCuspHigherLikelihoodSpectralMeasure] at hInt
  exact Summable.of_norm_bounded hInt.summable_integral fun k =>
    norm_integral_le_integral_norm _

/-- The complete ordinary score retains more than one hundredth of the leading eighth moment. -/
theorem one_hundredth_mul_spectralMoment_eight_lt_eighthScoreIntegral
    {A B : ℝ} (hA : (157 / 50 : ℝ) ≤ A) (hApi : Real.pi ≤ A)
    (hBA : B = A - 3 / 2) :
    (1 / 100 : ℝ) * A ^ 8 * thetaCuspHigherLikelihoodSpectralMoment B 8 <
      ∫ t : ℝ, thetaCuspLikelihoodEighthSourceScore (A * t) * Real.exp (-(B * t))
        ∂thetaCuspHigherLikelihoodSpectralMeasure := by
  have hB : 0 < B := by rw [hBA]; linarith
  have hm := summable_thetaCuspLikelihoodAtomEighthMonomialMass A hB
  have hs := summable_thetaCuspLikelihoodAtomEighthScoreMass A hB
  have hscaled := hm.mul_left (1 / 100 : ℝ)
  have hle : ∀ k : ℕ,
      (1 / 100 : ℝ) * thetaCuspLikelihoodAtomEighthMonomialMass (k + 2) A B ≤
        thetaCuspLikelihoodAtomEighthScoreMass (k + 2) A B := by
    intro k
    cases k with
    | zero =>
        exact (one_hundredth_mul_thetaCuspLikelihoodDominantAtomEighthMonomialMass_lt
          hA hBA).le
    | succ k =>
        exact one_hundredth_mul_thetaCuspLikelihoodStableAtomEighthMonomialMass_le
          (n := k + 3) (by omega) hApi hBA
  have hstrict := one_hundredth_mul_thetaCuspLikelihoodDominantAtomEighthMonomialMass_lt
    hA hBA
  have hsumlt := hscaled.tsum_lt_tsum (i := 0) hle (by simpa using hstrict) hs
  rw [integral_thetaCuspLikelihoodEighthSourceScore_eq_tsum_atom A hB]
  rw [tsum_mul_left] at hsumlt
  have hmoment :
      (∑' k : ℕ, thetaCuspLikelihoodAtomEighthMonomialMass (k + 2) A B) =
        A ^ 8 * thetaCuspHigherLikelihoodSpectralMoment B 8 := by
    let f : ℝ → ℝ := fun t => (A * t) ^ 8 * Real.exp (-(B * t))
    have hInt : Integrable f thetaCuspHigherLikelihoodSpectralMeasure := by
      have hi :=
        (integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure 8 hB).const_mul
          (A ^ 8)
      convert hi using 1
      funext t
      dsimp [f]
      ring
    have hglobal : (∫ t : ℝ, f t ∂thetaCuspHigherLikelihoodSpectralMeasure) =
        ∑' k : ℕ, thetaCuspLikelihoodAtomEighthMonomialMass (k + 2) A B := by
      rw [thetaCuspHigherLikelihoodSpectralMeasure, integral_sum_measure hInt]
      rfl
    calc
      (∑' k : ℕ, thetaCuspLikelihoodAtomEighthMonomialMass (k + 2) A B) =
          ∫ t : ℝ, f t ∂thetaCuspHigherLikelihoodSpectralMeasure := hglobal.symm
      _ = A ^ 8 * (∫ t : ℝ, t ^ 8 * Real.exp (-(B * t))
          ∂thetaCuspHigherLikelihoodSpectralMeasure) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with t
        dsimp [f]
        ring
      _ = A ^ 8 * thetaCuspHigherLikelihoodSpectralMoment B 8 := by
        rw [thetaCuspHigherLikelihoodSpectralMoment_eq_integral]
        congr 1
        apply integral_congr_ae
        filter_upwards with t
        ring
  rw [hmoment] at hsumlt
  simpa only [mul_assoc] using hsumlt

/-- The complete ordinary score retains more than one thirtieth of the leading eighth moment. -/
theorem one_thirtieth_mul_spectralMoment_eight_lt_eighthScoreIntegral
    {A B : ℝ} (hA : (157 / 50 : ℝ) ≤ A) (hApi : Real.pi ≤ A)
    (hBA : B = A - 3 / 2) :
    (1 / 30 : ℝ) * A ^ 8 * thetaCuspHigherLikelihoodSpectralMoment B 8 <
      ∫ t : ℝ, thetaCuspLikelihoodEighthSourceScore (A * t) * Real.exp (-(B * t))
        ∂thetaCuspHigherLikelihoodSpectralMeasure := by
  have hB : 0 < B := by rw [hBA]; linarith
  have hm := summable_thetaCuspLikelihoodAtomEighthMonomialMass A hB
  have hs := summable_thetaCuspLikelihoodAtomEighthScoreMass A hB
  have hscaled := hm.mul_left (1 / 30 : ℝ)
  have hle : ∀ k : ℕ,
      (1 / 30 : ℝ) * thetaCuspLikelihoodAtomEighthMonomialMass (k + 2) A B ≤
        thetaCuspLikelihoodAtomEighthScoreMass (k + 2) A B := by
    intro k
    cases k with
    | zero =>
        exact (one_thirtieth_mul_thetaCuspLikelihoodDominantAtomEighthMonomialMass_lt
          hA hBA).le
    | succ k =>
        exact one_thirtieth_mul_thetaCuspLikelihoodStableAtomEighthMonomialMass_le
          (n := k + 3) (by omega) hApi hBA
  have hstrict := one_thirtieth_mul_thetaCuspLikelihoodDominantAtomEighthMonomialMass_lt
    hA hBA
  have hsumlt := hscaled.tsum_lt_tsum (i := 0) hle (by simpa using hstrict) hs
  rw [integral_thetaCuspLikelihoodEighthSourceScore_eq_tsum_atom A hB]
  rw [tsum_mul_left] at hsumlt
  have hmoment :
      (∑' k : ℕ, thetaCuspLikelihoodAtomEighthMonomialMass (k + 2) A B) =
        A ^ 8 * thetaCuspHigherLikelihoodSpectralMoment B 8 := by
    let f : ℝ → ℝ := fun t => (A * t) ^ 8 * Real.exp (-(B * t))
    have hInt : Integrable f thetaCuspHigherLikelihoodSpectralMeasure := by
      have hi :=
        (integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure 8 hB).const_mul
          (A ^ 8)
      convert hi using 1
      funext t
      dsimp [f]
      ring
    have hglobal : (∫ t : ℝ, f t ∂thetaCuspHigherLikelihoodSpectralMeasure) =
        ∑' k : ℕ, thetaCuspLikelihoodAtomEighthMonomialMass (k + 2) A B := by
      rw [thetaCuspHigherLikelihoodSpectralMeasure, integral_sum_measure hInt]
      rfl
    calc
      (∑' k : ℕ, thetaCuspLikelihoodAtomEighthMonomialMass (k + 2) A B) =
          ∫ t : ℝ, f t ∂thetaCuspHigherLikelihoodSpectralMeasure := hglobal.symm
      _ = A ^ 8 * (∫ t : ℝ, t ^ 8 * Real.exp (-(B * t))
          ∂thetaCuspHigherLikelihoodSpectralMeasure) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with t
        dsimp [f]
        ring
      _ = A ^ 8 * thetaCuspHigherLikelihoodSpectralMoment B 8 := by
        rw [thetaCuspHigherLikelihoodSpectralMoment_eq_integral]
        congr 1
        apply integral_congr_ae
        filter_upwards with t
        ring
  rw [hmoment] at hsumlt
  simpa only [mul_assoc] using hsumlt

/-- Quantitative normalized form: the ordinary eighth jet retains `64/25` copies of its
normalized leading eighth spectral monomial. -/
theorem sixtyFourTwentyFifths_mul_normalizedMoment_eight_lt_ordinaryJetEight
    {x : ℝ} (hx : 0 ≤ x) :
    (64 / 25 : ℝ) * thetaCuspSingleAtomReflectionScale 1 x ^ 8 *
        thetaCuspLikelihoodNormalizedMoment (thetaCuspLikelihoodCoordinate x) 8 <
      thetaCuspLikelihoodSourceOrdinaryJetEight x := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  let P := thetaCuspLikelihoodPartition B
  have hApi : Real.pi ≤ A := by
    dsimp [A, thetaCuspSingleAtomReflectionScale]
    norm_num
    have he : 1 ≤ Real.exp (2 * x) := Real.one_le_exp (by linarith)
    simpa only [mul_one] using mul_le_mul_of_nonneg_left he Real.pi_pos.le
  have hA : (157 / 50 : ℝ) ≤ A := by
    have hpi := Real.pi_gt_d2
    norm_num at hpi
    linarith
  have hBA : B = A - 3 / 2 := by
    dsimp [A, B, thetaCuspLikelihoodCoordinate, thetaCuspSingleAtomReflectionScale]
    norm_num
    rw [show Real.exp (2 * x) = Real.exp x ^ 2 by
      rw [show 2 * x = x + x by ring, Real.exp_add]
      ring]
  have hB : 0 < B := by rw [hBA]; linarith
  have hP : 0 < P := by simpa only [P] using thetaCuspLikelihoodPartition_pos hB
  have hglobal := one_hundredth_mul_spectralMoment_eight_lt_eighthScoreIntegral
    hA hApi hBA
  have hcoeff : 0 < 256 / P := div_pos (by norm_num) hP
  have hscaled := mul_lt_mul_of_pos_left hglobal hcoeff
  rw [thetaCuspLikelihoodSourceOrdinaryJetEight_eq_spectralIntegral hx]
  calc
    (64 / 25 : ℝ) * thetaCuspSingleAtomReflectionScale 1 x ^ 8 *
        thetaCuspLikelihoodNormalizedMoment (thetaCuspLikelihoodCoordinate x) 8 =
      (256 / P) * ((1 / 100 : ℝ) * A ^ 8 *
        thetaCuspHigherLikelihoodSpectralMoment B 8) := by
      dsimp only [A, B]
      unfold thetaCuspLikelihoodNormalizedMoment
      dsimp only [P]
      field_simp [hP.ne']
      ring
    _ < (256 / P) *
        (∫ t : ℝ, thetaCuspLikelihoodEighthSourceScore (A * t) *
          Real.exp (-(B * t)) ∂thetaCuspHigherLikelihoodSpectralMeasure) := hscaled
    _ = _ := by rfl

/-- Sharpened normalized form: the ordinary eighth jet retains `128/15` copies of its
normalized leading eighth spectral monomial. -/
theorem oneHundredTwentyEightFifteenths_mul_normalizedMoment_eight_lt_ordinaryJetEight
    {x : ℝ} (hx : 0 ≤ x) :
    (128 / 15 : ℝ) * thetaCuspSingleAtomReflectionScale 1 x ^ 8 *
        thetaCuspLikelihoodNormalizedMoment (thetaCuspLikelihoodCoordinate x) 8 <
      thetaCuspLikelihoodSourceOrdinaryJetEight x := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  let P := thetaCuspLikelihoodPartition B
  have hApi : Real.pi ≤ A := by
    dsimp [A, thetaCuspSingleAtomReflectionScale]
    norm_num
    have he : 1 ≤ Real.exp (2 * x) := Real.one_le_exp (by linarith)
    simpa only [mul_one] using mul_le_mul_of_nonneg_left he Real.pi_pos.le
  have hA : (157 / 50 : ℝ) ≤ A := by
    have hpi := Real.pi_gt_d2
    norm_num at hpi
    linarith
  have hBA : B = A - 3 / 2 := by
    dsimp [A, B, thetaCuspLikelihoodCoordinate, thetaCuspSingleAtomReflectionScale]
    norm_num
    rw [show Real.exp (2 * x) = Real.exp x ^ 2 by
      rw [show 2 * x = x + x by ring, Real.exp_add]
      ring]
  have hB : 0 < B := by rw [hBA]; linarith
  have hP : 0 < P := by simpa only [P] using thetaCuspLikelihoodPartition_pos hB
  have hglobal := one_thirtieth_mul_spectralMoment_eight_lt_eighthScoreIntegral
    hA hApi hBA
  have hcoeff : 0 < 256 / P := div_pos (by norm_num) hP
  have hscaled := mul_lt_mul_of_pos_left hglobal hcoeff
  rw [thetaCuspLikelihoodSourceOrdinaryJetEight_eq_spectralIntegral hx]
  calc
    (128 / 15 : ℝ) * thetaCuspSingleAtomReflectionScale 1 x ^ 8 *
        thetaCuspLikelihoodNormalizedMoment (thetaCuspLikelihoodCoordinate x) 8 =
      (256 / P) * ((1 / 30 : ℝ) * A ^ 8 *
        thetaCuspHigherLikelihoodSpectralMoment B 8) := by
      dsimp only [A, B]
      unfold thetaCuspLikelihoodNormalizedMoment
      dsimp only [P]
      field_simp [hP.ne']
      ring
    _ < (256 / P) *
        (∫ t : ℝ, thetaCuspLikelihoodEighthSourceScore (A * t) *
          Real.exp (-(B * t)) ∂thetaCuspHigherLikelihoodSpectralMeasure) := hscaled
    _ = _ := by rfl

end

end RHTower
