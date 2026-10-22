import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspLikelihoodSixthScoreRayTransform
import GaloisForLFunctions.RHTower.BorelCaratheodoryCeiling

open MeasureTheory Set

/-!
# Uniform sixth-score bound for the stable theta tower

The dominant square-gap-three atom requires coefficient-faithful evaluation.  Every later atom
has gap at least eight.  On that stable tower the exact ray Taylor operator costs at most twice
the leading sixth monomial, and point plus ray costs at most three copies of the existing sixth
Gaussian reflection weight.  A sharpened symbolic Gaussian sum makes the complete tail uniform.
-/

namespace RHTower

noncomputable section

theorem thetaLikelihoodSixthScoreRayTransformPolynomial_two_le
    {y : ℝ} (hy : 16 ≤ y) :
    thetaLikelihoodSixthScoreRayTransformPolynomial 2 y ≤
      2 * (y + 9) ^ 6 := by
  let s := y - 16
  have hs : 0 ≤ s := by dsimp [s]; linarith
  rw [show y = 16 + s by dsimp [s]; ring]
  dsimp [thetaLikelihoodSixthScoreRayTransformPolynomial,
    thetaLikelihoodSixthScoreShift, thetaLikelihoodSixthScoreShiftDerivOne,
    thetaLikelihoodSixthScoreShiftDerivTwo,
    thetaLikelihoodSixthScoreShiftDerivThree,
    thetaLikelihoodSixthScoreShiftDerivFour,
    thetaLikelihoodSixthScoreShiftDerivFive,
    thetaLikelihoodSixthScoreShiftDerivSix]
  apply sub_nonneg.mp
  ring_nf
  positivity

theorem thetaLikelihoodSixthScoreRayTransformPolynomial_le_two_pow
    {r y : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 2) (hy : 16 ≤ y) :
    thetaLikelihoodSixthScoreRayTransformPolynomial r y ≤
      2 * (y + 9) ^ 6 := by
  have hy0 : 0 ≤ y := by linarith
  have hmono :
      thetaLikelihoodSixthScoreRayTransformPolynomial r y ≤
        thetaLikelihoodSixthScoreRayTransformPolynomial 2 y := by
    have hr2 := pow_le_pow_left₀ hr0 hr 2
    have hr3 := pow_le_pow_left₀ hr0 hr 3
    have hr4 := pow_le_pow_left₀ hr0 hr 4
    have hr5 := pow_le_pow_left₀ hr0 hr 5
    have hr6 := pow_le_pow_left₀ hr0 hr 6
    dsimp [thetaLikelihoodSixthScoreRayTransformPolynomial,
      thetaLikelihoodSixthScoreShift, thetaLikelihoodSixthScoreShiftDerivOne,
      thetaLikelihoodSixthScoreShiftDerivTwo,
      thetaLikelihoodSixthScoreShiftDerivThree,
      thetaLikelihoodSixthScoreShiftDerivFour,
      thetaLikelihoodSixthScoreShiftDerivFive,
      thetaLikelihoodSixthScoreShiftDerivSix]
    nlinarith [sq_nonneg y, pow_nonneg hy0 3, pow_nonneg hy0 4,
      pow_nonneg hy0 5, pow_nonneg hy0 6]
  exact hmono.trans (thetaLikelihoodSixthScoreRayTransformPolynomial_two_le hy)

/-- The sixth power-exponential scale is decreasing after the stable-tower edge. -/
theorem thetaSixthScalePowExp_le_pi
    {A d : ℝ} (hA : Real.pi ≤ A) (hd : 8 ≤ d) :
    A ^ 6 * Real.exp (-A * d) ≤
      Real.pi ^ 6 * Real.exp (-Real.pi * d) := by
  let u := Real.pi * d / 6
  let v := A * d / 6
  have hu : 1 ≤ u := by
    dsimp [u]
    nlinarith [Real.pi_gt_three]
  have huv : u ≤ v := by
    dsimp [u, v]
    nlinarith
  have hmono := mul_exp_neg_antitone hu huv
  have hu0 : 0 ≤ u * Real.exp (-u) :=
    mul_nonneg (by linarith) (Real.exp_pos _).le
  have hv0 : 0 ≤ v * Real.exp (-v) :=
    mul_nonneg (by linarith) (Real.exp_pos _).le
  have hpow := pow_le_pow_left₀ hv0 hmono 6
  have hd0 : 0 < d := by linarith
  have hleft : A ^ 6 * Real.exp (-A * d) =
      (6 / d) ^ 6 * (v * Real.exp (-v)) ^ 6 := by
    dsimp [v]
    rw [mul_pow, ← Real.exp_nat_mul]
    field_simp [hd0.ne']
    congr 1
    ring
  have hright : Real.pi ^ 6 * Real.exp (-Real.pi * d) =
      (6 / d) ^ 6 * (u * Real.exp (-u)) ^ 6 := by
    dsimp [u]
    rw [mul_pow, ← Real.exp_nat_mul]
    field_simp [hd0.ne']
    congr 1
    ring
  rw [hleft, hright]
  gcongr

/-- Literal sixth-score mass of one higher theta atom. -/
def thetaCuspLikelihoodAtomSixthScoreMass (n : ℕ) (A B : ℝ) : ℝ :=
  ∫ t : ℝ, thetaLikelihoodSixthScore (A * t) * Real.exp (-(B * t))
    ∂thetaCuspAtomLikelihoodSpectralMeasure n

/-- Exact point-ray evaluation of one atom's sixth-score mass. -/
theorem thetaCuspLikelihoodAtomSixthScoreMass_eq
    (n : ℕ) (hn : 2 ≤ n) (A : ℝ) {B : ℝ} (hB : 0 < B) :
    thetaCuspLikelihoodAtomSixthScoreMass n A B =
      thetaCuspLikelihoodAtomWeight n *
          (thetaLikelihoodSixthScore (A * thetaCuspLikelihoodGap n) *
            Real.exp (-(B * thetaCuspLikelihoodGap n))) +
        thetaCuspLikelihoodRayWeight n *
          (Real.exp (-(B * thetaCuspLikelihoodGap n)) / B *
            thetaLikelihoodSixthScoreRayTransformPolynomial
              (A / B) (A * thetaCuspLikelihoodGap n - 9)) := by
  let f : ℝ → ℝ := fun t =>
    thetaLikelihoodSixthScore (A * t) * Real.exp (-(B * t))
  have hd : Integrable f (Measure.dirac (thetaCuspLikelihoodGap n)) :=
    integrable_dirac (by dsimp [f]; finiteness)
  have hd0 : 0 ≤ thetaCuspLikelihoodGap n :=
    (thetaCuspLikelihoodGap_pos hn).le
  have hr : Integrable f
      (volume.restrict (Ioi (thetaCuspLikelihoodGap n))) := by
    change IntegrableOn f (Ioi (thetaCuspLikelihoodGap n))
    simpa only [f] using
      integrableOn_thetaLikelihoodSixthScore_mul_exp_neg_rate A hd0 hB
  have hd' : Integrable f
      (ENNReal.ofReal (thetaCuspLikelihoodAtomWeight n) •
        Measure.dirac (thetaCuspLikelihoodGap n)) := hd.smul_measure (by simp)
  have hr' : Integrable f
      (ENNReal.ofReal (thetaCuspLikelihoodRayWeight n) •
        volume.restrict (Ioi (thetaCuspLikelihoodGap n))) :=
    hr.smul_measure (by simp)
  rw [thetaCuspLikelihoodAtomSixthScoreMass,
    thetaCuspAtomLikelihoodSpectralMeasure,
    integral_add_measure hd' hr', integral_smul_measure, integral_dirac,
    integral_smul_measure]
  change ENNReal.toReal (ENNReal.ofReal (thetaCuspLikelihoodAtomWeight n)) *
      f (thetaCuspLikelihoodGap n) +
    ENNReal.toReal (ENNReal.ofReal (thetaCuspLikelihoodRayWeight n)) *
      (∫ t : ℝ in Ioi (thetaCuspLikelihoodGap n), f t) = _
  have ha0 : 0 ≤ thetaCuspLikelihoodAtomWeight n := by
    unfold thetaCuspLikelihoodAtomWeight
    positivity
  have hr0 : 0 ≤ thetaCuspLikelihoodRayWeight n := by
    unfold thetaCuspLikelihoodRayWeight
    positivity
  rw [ENNReal.toReal_ofReal ha0, ENNReal.toReal_ofReal hr0,
    integral_Ioi_thetaLikelihoodSixthScore_mul_exp_neg_rate A
      (thetaCuspLikelihoodGap n) hB]

/-- Every stable atom is bounded by three copies of its sixth Gaussian reflection weight. -/
theorem thetaCuspLikelihoodAtomSixthScoreMass_le
    {n : ℕ} (hn : 3 ≤ n) {A B : ℝ} (hA : Real.pi ≤ A)
    (hBA : B = A - 3 / 2) :
    thetaCuspLikelihoodAtomSixthScoreMass n A B ≤
      3 * Real.pi ^ 6 * thetaCuspReflectionJetTailWeight 6 (n - 2) := by
  let d := thetaCuspLikelihoodGap n
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : 8 ≤ d := by
    dsimp [d, thetaCuspLikelihoodGap]
    nlinarith
  have hB : 0 < B := by rw [hBA]; nlinarith [Real.pi_gt_three]
  have hB41 : (3 / 2 : ℝ) < B := by
    rw [hBA]
    nlinarith [Real.pi_gt_three]
  have hA0 : 0 < A := lt_of_lt_of_le Real.pi_pos hA
  have hz : (47 / 5 : ℝ) < A * d := by
    have hmul := mul_le_mul hA hd (by norm_num : (0 : ℝ) ≤ 8) hA0.le
    nlinarith [Real.pi_gt_d2]
  have hy : 16 ≤ A * d - 9 := by
    have hmul := mul_le_mul hA hd (by norm_num : (0 : ℝ) ≤ 8) hA0.le
    nlinarith [Real.pi_gt_d2]
  have hr0 : 0 ≤ A / B := div_nonneg hA0.le hB.le
  have hr : A / B ≤ 2 := by
    apply (div_le_iff₀ hB).2
    rw [hBA]
    linarith
  have hpointScore := thetaLikelihoodSixthScore_le_pow_six hz
  have hrayPoly :=
    thetaLikelihoodSixthScoreRayTransformPolynomial_le_two_pow hr0 hr hy
  have hrayPoly' :
      thetaLikelihoodSixthScoreRayTransformPolynomial (A / B) (A * d - 9) ≤
        2 * (A * d) ^ 6 := by
    convert hrayPoly using 1
    ring
  have hexp :
      Real.exp (-(3 / 2 : ℝ) * d) * Real.exp (-(B * d)) =
        Real.exp (-A * d) := by
    rw [← Real.exp_add]
    rw [hBA]
    congr 1
    ring
  have hpoint :
      thetaCuspLikelihoodAtomWeight n *
          (thetaLikelihoodSixthScore (A * d) * Real.exp (-(B * d))) ≤
        (n : ℝ) ^ 4 * d ^ 6 * (A ^ 6 * Real.exp (-A * d)) := by
    unfold thetaCuspLikelihoodAtomWeight
    calc
      _ ≤ Real.exp (-(3 / 2 : ℝ) * d) * (n : ℝ) ^ 4 *
          ((A * d) ^ 6 * Real.exp (-(B * d))) := by gcongr
      _ = _ := by
        rw [mul_pow]
        rw [show Real.exp (-(3 / 2 : ℝ) * d) * (n : ℝ) ^ 4 *
            (A ^ 6 * d ^ 6 * Real.exp (-(B * d))) =
          (n : ℝ) ^ 4 * A ^ 6 * d ^ 6 *
            (Real.exp (-(3 / 2 : ℝ) * d) * Real.exp (-(B * d))) by ring,
          hexp]
        ring
  have hray :
      thetaCuspLikelihoodRayWeight n *
          (Real.exp (-(B * d)) / B *
            thetaLikelihoodSixthScoreRayTransformPolynomial
              (A / B) (A * d - 9)) ≤
        2 * (n : ℝ) ^ 4 * d ^ 6 * (A ^ 6 * Real.exp (-A * d)) := by
    have hnd : (n : ℝ) ^ 2 * d ≤ (n : ℝ) ^ 4 := by
      dsimp [d, thetaCuspLikelihoodGap]
      nlinarith [sq_nonneg (n : ℝ)]
    unfold thetaCuspLikelihoodRayWeight
    calc
      _ ≤ Real.exp (-(3 / 2 : ℝ) * d) * (3 / 2 : ℝ) * (n : ℝ) ^ 2 * d *
          (Real.exp (-(B * d)) / B * (2 * (A * d) ^ 6)) := by gcongr
      _ = (3 / B) * ((n : ℝ) ^ 2 * d) * d ^ 6 *
          (A ^ 6 * Real.exp (-A * d)) := by
        rw [mul_pow]
        rw [show Real.exp (-(3 / 2 : ℝ) * d) * (3 / 2 : ℝ) *
            (n : ℝ) ^ 2 * d *
              (Real.exp (-(B * d)) / B * (2 * (A ^ 6 * d ^ 6))) =
          (3 / B) * ((n : ℝ) ^ 2 * d) * d ^ 6 * A ^ 6 *
            (Real.exp (-(3 / 2 : ℝ) * d) * Real.exp (-(B * d))) by ring,
          hexp]
        ring
      _ ≤ 2 * (n : ℝ) ^ 4 * d ^ 6 *
          (A ^ 6 * Real.exp (-A * d)) := by
        have hthree : 3 / B < 2 := by
          apply (div_lt_iff₀ hB).2
          linarith
        gcongr
  have hscale := thetaSixthScalePowExp_le_pi hA hd
  rw [thetaCuspLikelihoodAtomSixthScoreMass_eq n (by omega) A hB]
  change _ * (thetaLikelihoodSixthScore (A * d) * _) +
    _ * (_ / B * thetaLikelihoodSixthScoreRayTransformPolynomial
      (A / B) (A * d - 9)) ≤ _
  have hsum :
      thetaCuspLikelihoodAtomWeight n *
          (thetaLikelihoodSixthScore (A * d) * Real.exp (-(B * d))) +
        thetaCuspLikelihoodRayWeight n *
          (Real.exp (-(B * d)) / B *
            thetaLikelihoodSixthScoreRayTransformPolynomial
              (A / B) (A * d - 9)) ≤
        3 * (n : ℝ) ^ 4 * d ^ 6 * (A ^ 6 * Real.exp (-A * d)) := by
    nlinarith
  calc
    _ ≤ 3 * (n : ℝ) ^ 4 * d ^ 6 * (A ^ 6 * Real.exp (-A * d)) := hsum
    _ ≤ 3 * (n : ℝ) ^ 4 * d ^ 6 *
        (Real.pi ^ 6 * Real.exp (-Real.pi * d)) := by gcongr
    _ = 3 * Real.pi ^ 6 * thetaCuspReflectionJetTailWeight 6 (n - 2) := by
      unfold thetaCuspReflectionJetTailWeight
      have hnsub : n - 2 + 2 = n := by omega
      simp only [hnsub]
      rw [show 3 * (n : ℝ) ^ 4 * d ^ 6 *
          (Real.pi ^ 6 * Real.exp (-Real.pi * d)) =
        3 * Real.pi ^ 6 *
          ((n : ℝ) ^ 4 * d ^ 6 * Real.exp (-Real.pi * d)) by ring]
      dsimp only [d, thetaCuspLikelihoodGap]

theorem exp_neg_two_pi_lt_one_div_hundred :
    Real.exp (-2 * Real.pi) < (1 : ℝ) / 100 := by
  let z := 2 * Real.pi
  have hz : 6 < z := by dsimp [z]; nlinarith [Real.pi_gt_three]
  have hz0 : 0 ≤ z := by linarith
  have he0 := Real.sum_le_exp_of_nonneg hz0 5
  have he : 1 + z + z ^ 2 / 2 + z ^ 3 / 6 + z ^ 4 / 24 ≤ Real.exp z := by
    norm_num [Finset.sum_range_succ] at he0 ⊢
    exact he0
  have hz2 : 36 < z ^ 2 := by nlinarith [sq_nonneg (z - 6)]
  have hz3 : 216 < z ^ 3 := by
    have hmul := mul_lt_mul_of_pos_right hz2 (by linarith : 0 < z)
    nlinarith
  have hz4 : 1296 < z ^ 4 := by
    have hmul := mul_lt_mul_of_pos_right hz3 (by linarith : 0 < z)
    nlinarith
  have hexp : 100 < Real.exp z := by nlinarith
  rw [show -2 * Real.pi = -z by dsimp [z]; ring, Real.exp_neg]
  simpa only [one_div] using
    (one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 100) hexp)

theorem exp_neg_seven_pi_lt_one_div_oneHundredTwentyMillion :
    Real.exp (-7 * Real.pi) < (1 : ℝ) / 120000000 := by
  rw [show -7 * Real.pi = -3 * Real.pi + (-2 * Real.pi) +
      (-2 * Real.pi) by ring, Real.exp_add, Real.exp_add]
  have h3 := thetaCusp_exp_neg_three_pi_lt
  have h2 := exp_neg_two_pi_lt_one_div_hundred
  calc
    (Real.exp (-3 * Real.pi) * Real.exp (-2 * Real.pi)) *
          Real.exp (-2 * Real.pi) <
        ((1 / 12000 : ℝ) * (1 / 100 : ℝ)) * Real.exp (-2 * Real.pi) := by
      gcongr
    _ < ((1 / 12000 : ℝ) * (1 / 100 : ℝ)) * (1 / 100 : ℝ) := by gcongr
    _ = (1 : ℝ) / 120000000 := by norm_num

theorem exp_neg_eight_pi_lt_one_div_fourteenBillionFourHundredMillion :
    Real.exp (-8 * Real.pi) < (1 : ℝ) / 14400000000 := by
  rw [show -8 * Real.pi = -3 * Real.pi + (-3 * Real.pi) +
      (-2 * Real.pi) by ring, Real.exp_add, Real.exp_add]
  have h3 := thetaCusp_exp_neg_three_pi_lt
  have h2 := exp_neg_two_pi_lt_one_div_hundred
  calc
    (Real.exp (-3 * Real.pi) * Real.exp (-3 * Real.pi)) *
          Real.exp (-2 * Real.pi) <
        ((1 / 12000 : ℝ) * (1 / 12000 : ℝ)) * Real.exp (-2 * Real.pi) := by
      gcongr
    _ < ((1 / 12000 : ℝ) * (1 / 12000 : ℝ)) * (1 / 100 : ℝ) := by gcongr
    _ = (1 : ℝ) / 14400000000 := by norm_num

private theorem thetaCusp_nat_add_three_pow_sixteen_le (k : ℕ) :
    (((k + 3 : ℕ) : ℝ) ^ 16) ≤ 43046721 * (65536 : ℝ) ^ k := by
  have hnat : k + 3 ≤ 3 * 2 ^ k := by
    induction k with
    | zero => norm_num
    | succ k ih =>
        rw [pow_succ]
        omega
  have hcast : ((k + 3 : ℕ) : ℝ) ≤ (3 * 2 ^ k : ℕ) := by exact_mod_cast hnat
  calc
    (((k + 3 : ℕ) : ℝ) ^ 16) ≤ (((3 * 2 ^ k : ℕ) : ℝ) ^ 16) := by gcongr
    _ = 43046721 * (65536 : ℝ) ^ k := by
      push_cast
      rw [mul_pow]
      norm_num
      calc
        (((2 : ℝ) ^ k) ^ 16) = (2 : ℝ) ^ (k * 16) := by rw [pow_mul]
        _ = (2 : ℝ) ^ (16 * k) := by rw [Nat.mul_comm]
        _ = ((2 : ℝ) ^ 16) ^ k := by rw [pow_mul]
        _ = (65536 : ℝ) ^ k := by norm_num

private theorem thetaCusp_tail_exponent_seven_add_three_le (k : ℕ) :
    Real.exp (-Real.pi * (((k + 3 : ℕ) : ℝ) ^ 2 - 1)) ≤
      Real.exp (-8 * Real.pi) * (Real.exp (-7 * Real.pi)) ^ k := by
  have hsquare :
      (8 : ℝ) + 7 * k ≤ (((k + 3 : ℕ) : ℝ) ^ 2 - 1) := by
    rcases k with _ | k
    · norm_num
    · push_cast
      nlinarith [sq_nonneg (k : ℝ)]
  have hexponent :
      -Real.pi * (((k + 3 : ℕ) : ℝ) ^ 2 - 1) ≤
        -8 * Real.pi + (k : ℕ) * (-7 * Real.pi) := by
    nlinarith [Real.pi_pos]
  calc
    _ ≤ Real.exp (-8 * Real.pi + (k : ℕ) * (-7 * Real.pi)) :=
      Real.exp_le_exp.mpr hexponent
    _ = _ := by rw [Real.exp_add, Real.exp_nat_mul]

theorem thetaCuspReflectionJetTailWeight_six_tail_le_geometric (k : ℕ) :
    thetaCuspReflectionJetTailWeight 6 (k + 1) ≤
      (1 / 300 : ℝ) * ((1 / 1000 : ℝ) ^ k) := by
  let n : ℕ := k + 3
  have hpow := thetaCusp_nat_add_three_pow_sixteen_le k
  have hexp := thetaCusp_tail_exponent_seven_add_three_le k
  have hbase : Real.exp (-8 * Real.pi) ≤ (1 : ℝ) / 14400000000 :=
    exp_neg_eight_pi_lt_one_div_fourteenBillionFourHundredMillion.le
  have hratio : 65536 * Real.exp (-7 * Real.pi) ≤ (1 / 1000 : ℝ) := by
    nlinarith [exp_neg_seven_pi_lt_one_div_oneHundredTwentyMillion]
  have hn : (3 : ℝ) ≤ n := by exact_mod_cast (by dsimp [n]; omega : 3 ≤ n)
  have hd : 0 ≤ (n : ℝ) ^ 2 - 1 := by nlinarith
  have hdle : ((n : ℝ) ^ 2 - 1) ^ 6 ≤ ((n : ℝ) ^ 2) ^ 6 :=
    pow_le_pow_left₀ hd (by linarith) 6
  unfold thetaCuspReflectionJetTailWeight
  dsimp only [n]
  calc
    ((n : ℝ) ^ 4 * ((n : ℝ) ^ 2 - 1) ^ 6 *
          Real.exp (-Real.pi * ((n : ℝ) ^ 2 - 1))) ≤
        (n : ℝ) ^ 4 * ((n : ℝ) ^ 2) ^ 6 *
          Real.exp (-Real.pi * ((n : ℝ) ^ 2 - 1)) := by gcongr
    _ = (n : ℝ) ^ 16 * Real.exp (-Real.pi * ((n : ℝ) ^ 2 - 1)) := by
      rw [← pow_mul, ← pow_add]
    _ ≤ (43046721 * (65536 : ℝ) ^ k) *
        (Real.exp (-8 * Real.pi) * (Real.exp (-7 * Real.pi)) ^ k) := by gcongr
    _ = 43046721 * Real.exp (-8 * Real.pi) *
        (65536 * Real.exp (-7 * Real.pi)) ^ k := by ring
    _ ≤ 43046721 * ((1 : ℝ) / 14400000000) *
        ((1 / 1000 : ℝ) ^ k) := by gcongr
    _ ≤ (1 / 300 : ℝ) * ((1 / 1000 : ℝ) ^ k) := by
      gcongr
      norm_num

/-- The complete Gaussian sixth weight beyond the dominant atom is uniformly tiny. -/
theorem tsum_thetaCuspReflectionJetTailWeight_six_tail_le :
    (∑' k : ℕ, thetaCuspReflectionJetTailWeight 6 (k + 1)) ≤
      (10 / 2997 : ℝ) := by
  have hs : Summable (fun k : ℕ => thetaCuspReflectionJetTailWeight 6 (k + 1)) :=
    (summable_nat_add_iff 1).2 (summable_thetaCuspReflectionJetTailWeight 6)
  have hgeo : Summable (fun k : ℕ =>
      (1 / 300 : ℝ) * ((1 / 1000 : ℝ) ^ k)) :=
    (summable_geometric_of_norm_lt_one
      (by norm_num : ‖(1 / 1000 : ℝ)‖ < 1)).mul_left _
  calc
    (∑' k : ℕ, thetaCuspReflectionJetTailWeight 6 (k + 1)) ≤
        ∑' k : ℕ, (1 / 300 : ℝ) * ((1 / 1000 : ℝ) ^ k) :=
      Summable.tsum_le_tsum
        thetaCuspReflectionJetTailWeight_six_tail_le_geometric hs hgeo
    _ = (1 / 300 : ℝ) * (1 - (1 / 1000 : ℝ))⁻¹ := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    _ = (10 / 2997 : ℝ) := by norm_num

/-- Each stable atom's literal sixth-score mass is nonnegative. -/
theorem thetaCuspLikelihoodAtomSixthScoreMass_nonneg
    {n : ℕ} (hn : 3 ≤ n) {A B : ℝ} (hA : Real.pi ≤ A)
    (hBA : B = A - 3 / 2) :
    0 ≤ thetaCuspLikelihoodAtomSixthScoreMass n A B := by
  let d := thetaCuspLikelihoodGap n
  have hd : 8 ≤ d := by
    dsimp [d, thetaCuspLikelihoodGap]
    have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  have hA0 : 0 < A := lt_of_lt_of_le Real.pi_pos hA
  have hB : 0 < B := by rw [hBA]; nlinarith [Real.pi_gt_three]
  have hy : 16 ≤ A * d - 9 := by
    have hmul := mul_le_mul hA hd (by norm_num : (0 : ℝ) ≤ 8) hA0.le
    nlinarith [Real.pi_gt_d2]
  have hyr : 0 ≤ A / B := div_nonneg hA0.le hB.le
  have hpoint : 0 ≤ thetaLikelihoodSixthScore (A * d) := by
    rw [thetaLikelihoodSixthScore_eq_shiftNine]
    dsimp [thetaLikelihoodSixthScoreShift]
    positivity
  have hray : 0 ≤
      thetaLikelihoodSixthScoreRayTransformPolynomial (A / B) (A * d - 9) := by
    dsimp [thetaLikelihoodSixthScoreRayTransformPolynomial,
      thetaLikelihoodSixthScoreShift, thetaLikelihoodSixthScoreShiftDerivOne,
      thetaLikelihoodSixthScoreShiftDerivTwo,
      thetaLikelihoodSixthScoreShiftDerivThree,
      thetaLikelihoodSixthScoreShiftDerivFour,
      thetaLikelihoodSixthScoreShiftDerivFive,
      thetaLikelihoodSixthScoreShiftDerivSix]
    positivity
  rw [thetaCuspLikelihoodAtomSixthScoreMass_eq n (by omega) A hB]
  change _ * (thetaLikelihoodSixthScore (A * d) * _) +
    _ * (_ / B * thetaLikelihoodSixthScoreRayTransformPolynomial
      (A / B) (A * d - 9)) ≥ 0
  have ha : 0 ≤ thetaCuspLikelihoodAtomWeight n := by
    unfold thetaCuspLikelihoodAtomWeight
    positivity
  have hr : 0 ≤ thetaCuspLikelihoodRayWeight n := by
    unfold thetaCuspLikelihoodRayWeight
    positivity
  positivity

/-- The literal sixth-score masses of every atom after `n=2` form a summable tower. -/
theorem summable_thetaCuspLikelihoodStableAtomSixthScoreMass
    {A B : ℝ} (hA : Real.pi ≤ A) (hBA : B = A - 3 / 2) :
    Summable (fun k : ℕ => thetaCuspLikelihoodAtomSixthScoreMass (k + 3) A B) := by
  have hmajor :=
    (summable_nat_add_iff 1).2 (summable_thetaCuspReflectionJetTailWeight 6) |>.mul_left
      (3 * Real.pi ^ 6)
  apply Summable.of_norm_bounded hmajor
  intro k
  rw [Real.norm_eq_abs, abs_of_nonneg
    (thetaCuspLikelihoodAtomSixthScoreMass_nonneg (by omega) hA hBA)]
  simpa only [show k + 3 - 2 = k + 1 by omega] using
    thetaCuspLikelihoodAtomSixthScoreMass_le (n := k + 3) (by omega) hA hBA

/-- Uniform aperture-independent bound for the complete stable sixth-score tower. -/
theorem tsum_thetaCuspLikelihoodStableAtomSixthScoreMass_le
    {A B : ℝ} (hA : Real.pi ≤ A) (hBA : B = A - 3 / 2) :
    (∑' k : ℕ, thetaCuspLikelihoodAtomSixthScoreMass (k + 3) A B) ≤
      (10 / 999 : ℝ) * Real.pi ^ 6 := by
  have hs := summable_thetaCuspLikelihoodStableAtomSixthScoreMass hA hBA
  have hw : Summable (fun k : ℕ =>
      (3 * Real.pi ^ 6) * thetaCuspReflectionJetTailWeight 6 (k + 1)) :=
    ((summable_nat_add_iff 1).2 (summable_thetaCuspReflectionJetTailWeight 6)).mul_left _
  calc
    (∑' k : ℕ, thetaCuspLikelihoodAtomSixthScoreMass (k + 3) A B) ≤
        ∑' k : ℕ, (3 * Real.pi ^ 6) *
          thetaCuspReflectionJetTailWeight 6 (k + 1) := by
      apply Summable.tsum_le_tsum _ hs hw
      intro k
      simpa only [show k + 3 - 2 = k + 1 by omega] using
        thetaCuspLikelihoodAtomSixthScoreMass_le
          (n := k + 3) (by omega) hA hBA
    _ = (3 * Real.pi ^ 6) *
        (∑' k : ℕ, thetaCuspReflectionJetTailWeight 6 (k + 1)) := by
      rw [tsum_mul_left]
    _ ≤ (3 * Real.pi ^ 6) * (10 / 2997 : ℝ) := by
      gcongr
      exact tsum_thetaCuspReflectionJetTailWeight_six_tail_le
    _ = (10 / 999 : ℝ) * Real.pi ^ 6 := by ring

end

end RHTower
