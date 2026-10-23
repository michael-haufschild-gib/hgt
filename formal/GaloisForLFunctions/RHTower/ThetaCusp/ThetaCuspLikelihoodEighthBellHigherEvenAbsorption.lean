import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspLikelihoodEighthBellGrades

/-!
# Higher-even Bell grades land in the completed eighth Fock loss

The order-eight Bell grades `4`, `6`, and `8` are bounded directly by the corresponding
positive-particle compositions.  Iterated likelihood moment multiplication supplies one tail
probability for every merge.  Their exact coefficients then fit below `q^(7 : ℕ) r^(q-1)` for
`q = 4, 6, 8`, hence below the already summable higher-even Fock loss.

Only Bell grade two remains outside this connector; it requires the exact ordered pair trace.
-/

namespace RHTower

open MeasureTheory

noncomputable section

theorem thetaCuspLikelihoodNormalizedMoment_nonneg
    {B : ℝ} (hB : 0 < B) (m : ℕ) :
    0 ≤ thetaCuspLikelihoodNormalizedMoment B m := by
  unfold thetaCuspLikelihoodNormalizedMoment
  exact div_nonneg (thetaCuspHigherLikelihoodSpectralMoment_nonneg m)
    (thetaCuspLikelihoodPartition_pos hB).le

/-- Four normalized moments cost at most three powers of tail probability. -/
theorem thetaCuspLikelihoodNormalizedMoment_four_mul_le
    {B : ℝ} (hB : 0 < B) (i j k l : ℕ) :
    thetaCuspLikelihoodNormalizedMoment B i *
          thetaCuspLikelihoodNormalizedMoment B j *
        (thetaCuspLikelihoodNormalizedMoment B k *
          thetaCuspLikelihoodNormalizedMoment B l) ≤
      thetaCuspLikelihoodTailProbability B ^ (3 : ℕ) *
        thetaCuspLikelihoodNormalizedMoment B (i + j + (k + l)) := by
  let p := thetaCuspLikelihoodTailProbability B
  let e := thetaCuspLikelihoodNormalizedMoment B
  have hp : 0 ≤ p := by
    dsimp only [p, thetaCuspLikelihoodTailProbability]
    exact thetaCuspLikelihoodNormalizedMoment_nonneg hB 0
  have he (m : ℕ) : 0 ≤ e m := by
    simpa only [e] using thetaCuspLikelihoodNormalizedMoment_nonneg hB m
  have hij : e i * e j ≤ p * e (i + j) := by
    simpa only [p, e] using
      thetaCuspLikelihoodNormalizedMoment_mul_le_tailProbability_mul hB i j
  have hkl : e k * e l ≤ p * e (k + l) := by
    simpa only [p, e] using
      thetaCuspLikelihoodNormalizedMoment_mul_le_tailProbability_mul hB k l
  have hmerge : e (i + j) * e (k + l) ≤
      p * e ((i + j) + (k + l)) := by
    simpa only [p, e] using
      thetaCuspLikelihoodNormalizedMoment_mul_le_tailProbability_mul hB (i + j) (k + l)
  calc
    e i * e j * (e k * e l) ≤ (p * e (i + j)) * (p * e (k + l)) :=
      mul_le_mul hij hkl (mul_nonneg (he k) (he l)) (mul_nonneg hp (he (i + j)))
    _ = p ^ (2 : ℕ) * (e (i + j) * e (k + l)) := by ring
    _ ≤ p ^ (2 : ℕ) * (p * e ((i + j) + (k + l))) := by gcongr
    _ = p ^ (3 : ℕ) * e (i + j + (k + l)) := by ring

/-- Six normalized moments cost at most five powers of tail probability. -/
theorem thetaCuspLikelihoodNormalizedMoment_six_mul_le
    {B : ℝ} (hB : 0 < B) (i j k l m n : ℕ) :
    (thetaCuspLikelihoodNormalizedMoment B i *
          thetaCuspLikelihoodNormalizedMoment B j *
        (thetaCuspLikelihoodNormalizedMoment B k *
          thetaCuspLikelihoodNormalizedMoment B l)) *
        (thetaCuspLikelihoodNormalizedMoment B m *
          thetaCuspLikelihoodNormalizedMoment B n) ≤
      thetaCuspLikelihoodTailProbability B ^ (5 : ℕ) *
        thetaCuspLikelihoodNormalizedMoment B (i + j + (k + l) + (m + n)) := by
  let p := thetaCuspLikelihoodTailProbability B
  let e := thetaCuspLikelihoodNormalizedMoment B
  have hp : 0 ≤ p := by
    dsimp only [p, thetaCuspLikelihoodTailProbability]
    exact thetaCuspLikelihoodNormalizedMoment_nonneg hB 0
  have he (a : ℕ) : 0 ≤ e a := by
    simpa only [e] using thetaCuspLikelihoodNormalizedMoment_nonneg hB a
  have hfour : e i * e j * (e k * e l) ≤
      p ^ (3 : ℕ) * e (i + j + (k + l)) := by
    simpa only [p, e] using
      thetaCuspLikelihoodNormalizedMoment_four_mul_le hB i j k l
  have hpair : e m * e n ≤ p * e (m + n) := by
    simpa only [p, e] using
      thetaCuspLikelihoodNormalizedMoment_mul_le_tailProbability_mul hB m n
  have hmerge : e (i + j + (k + l)) * e (m + n) ≤
      p * e (i + j + (k + l) + (m + n)) := by
    simpa only [p, e] using thetaCuspLikelihoodNormalizedMoment_mul_le_tailProbability_mul
      hB (i + j + (k + l)) (m + n)
  calc
    (e i * e j * (e k * e l)) * (e m * e n) ≤
        (p ^ (3 : ℕ) * e (i + j + (k + l))) * (p * e (m + n)) :=
      mul_le_mul hfour hpair (mul_nonneg (he m) (he n))
        (mul_nonneg (pow_nonneg hp 3) (he (i + j + (k + l))))
    _ = p ^ (4 : ℕ) * (e (i + j + (k + l)) * e (m + n)) := by ring
    _ ≤ p ^ (4 : ℕ) * (p * e (i + j + (k + l) + (m + n))) := by gcongr
    _ = p ^ (5 : ℕ) * e (i + j + (k + l) + (m + n)) := by ring

/-- Eight normalized moments cost at most seven powers of tail probability. -/
theorem thetaCuspLikelihoodNormalizedMoment_eight_mul_le
    {B : ℝ} (hB : 0 < B) (i j k l m n o q : ℕ) :
    (thetaCuspLikelihoodNormalizedMoment B i *
          thetaCuspLikelihoodNormalizedMoment B j *
        (thetaCuspLikelihoodNormalizedMoment B k *
          thetaCuspLikelihoodNormalizedMoment B l)) *
      (thetaCuspLikelihoodNormalizedMoment B m *
          thetaCuspLikelihoodNormalizedMoment B n *
        (thetaCuspLikelihoodNormalizedMoment B o *
          thetaCuspLikelihoodNormalizedMoment B q)) ≤
      thetaCuspLikelihoodTailProbability B ^ (7 : ℕ) *
        thetaCuspLikelihoodNormalizedMoment B
          (i + j + (k + l) + (m + n + (o + q))) := by
  let p := thetaCuspLikelihoodTailProbability B
  let e := thetaCuspLikelihoodNormalizedMoment B
  have hp : 0 ≤ p := by
    dsimp only [p, thetaCuspLikelihoodTailProbability]
    exact thetaCuspLikelihoodNormalizedMoment_nonneg hB 0
  have he (a : ℕ) : 0 ≤ e a := by
    simpa only [e] using thetaCuspLikelihoodNormalizedMoment_nonneg hB a
  have hleft : e i * e j * (e k * e l) ≤
      p ^ (3 : ℕ) * e (i + j + (k + l)) := by
    simpa only [p, e] using
      thetaCuspLikelihoodNormalizedMoment_four_mul_le hB i j k l
  have hright : e m * e n * (e o * e q) ≤
      p ^ (3 : ℕ) * e (m + n + (o + q)) := by
    simpa only [p, e] using
      thetaCuspLikelihoodNormalizedMoment_four_mul_le hB m n o q
  have hmerge : e (i + j + (k + l)) * e (m + n + (o + q)) ≤
      p * e (i + j + (k + l) + (m + n + (o + q))) := by
    simpa only [p, e] using thetaCuspLikelihoodNormalizedMoment_mul_le_tailProbability_mul
      hB (i + j + (k + l)) (m + n + (o + q))
  calc
    (e i * e j * (e k * e l)) * (e m * e n * (e o * e q)) ≤
        (p ^ (3 : ℕ) * e (i + j + (k + l))) *
          (p ^ (3 : ℕ) * e (m + n + (o + q))) :=
      mul_le_mul hleft hright
        (mul_nonneg (mul_nonneg (he m) (he n)) (mul_nonneg (he o) (he q)))
        (mul_nonneg (pow_nonneg hp 3) (he (i + j + (k + l))))
    _ = p ^ (6 : ℕ) *
        (e (i + j + (k + l)) * e (m + n + (o + q))) := by ring
    _ ≤ p ^ (6 : ℕ) *
        (p * e (i + j + (k + l) + (m + n + (o + q)))) := by gcongr
    _ = p ^ (7 : ℕ) * e (i + j + (k + l) + (m + n + (o + q))) := by ring

/-- The first five positive ordinary jets lie below their leading tilted moments. -/
theorem thetaCuspLikelihoodEighthBellJets_one_to_five_le_leading
    {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspLikelihoodEighthBellJetOne x ≤
        2 * thetaCuspSingleAtomReflectionScale 1 x *
          thetaCuspLikelihoodMean (thetaCuspLikelihoodCoordinate x) ∧
    thetaCuspLikelihoodEighthBellJetTwo x ≤
        4 * thetaCuspSingleAtomReflectionScale 1 x ^ (2 : ℕ) *
          thetaCuspLikelihoodNormalizedMoment (thetaCuspLikelihoodCoordinate x) 2 ∧
    thetaCuspLikelihoodEighthBellJetThree x ≤
        8 * thetaCuspSingleAtomReflectionScale 1 x ^ (3 : ℕ) *
          thetaCuspLikelihoodNormalizedMoment (thetaCuspLikelihoodCoordinate x) 3 ∧
    thetaCuspLikelihoodEighthBellJetFour x ≤
        16 * thetaCuspSingleAtomReflectionScale 1 x ^ (4 : ℕ) *
          thetaCuspLikelihoodNormalizedMoment (thetaCuspLikelihoodCoordinate x) 4 ∧
    thetaCuspLikelihoodEighthBellJetFive x ≤
        32 * thetaCuspSingleAtomReflectionScale 1 x ^ (5 : ℕ) *
          thetaCuspLikelihoodNormalizedMoment (thetaCuspLikelihoodCoordinate x) 5 := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  let e1 := thetaCuspLikelihoodMean B
  let e2 := thetaCuspLikelihoodNormalizedMoment B 2
  let e3 := thetaCuspLikelihoodNormalizedMoment B 3
  let e4 := thetaCuspLikelihoodNormalizedMoment B 4
  let e5 := thetaCuspLikelihoodNormalizedMoment B 5
  have hB : 0 < B := by simpa only [B] using thetaCuspLikelihoodCoordinate_pos hx
  have hA : 3 < A := by
    simpa only [A] using
      three_lt_thetaCuspSingleAtomReflectionScale (n := 1) (by norm_num) hx
  have hA0 : 0 < A := by linarith
  have he1 : 0 < e1 := by simpa only [e1] using thetaCuspLikelihoodMean_pos hB
  have he2 : 0 < e2 := by
    simpa only [e2] using thetaCuspLikelihoodNormalizedMoment_two_pos hB
  have he12 : 3 * e1 ≤ e2 := by
    simpa only [e1, e2, thetaCuspLikelihoodNormalizedMoment_one_eq_mean] using
      three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hB 1
  have he23 : 3 * e2 ≤ e3 := by
    simpa only [e2, e3] using
      three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hB 2
  have he34 : 3 * e3 ≤ e4 := by
    simpa only [e3, e4] using
      three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hB 3
  have he45 : 3 * e4 ≤ e5 := by
    simpa only [e4, e5] using
      three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hB 4
  have he3 : 0 < e3 := lt_of_lt_of_le (mul_pos (by norm_num) he2) he23
  have he4 : 0 < e4 := lt_of_lt_of_le (mul_pos (by norm_num) he3) he34
  have he5 : 0 < e5 := lt_of_lt_of_le (mul_pos (by norm_num) he4) he45
  constructor
  · rfl
  constructor
  · unfold thetaCuspLikelihoodEighthBellJetTwo
    dsimp only [A, B, e1, e2]
    nlinarith [mul_pos hA0 he1]
  constructor
  · unfold thetaCuspLikelihoodEighthBellJetThree
    dsimp only [A, B, e1, e2, e3]
    have htail := mul_le_mul_of_nonneg_left he12 (mul_nonneg hA0.le hA0.le)
    nlinarith [mul_pos hA0 he1]
  constructor
  · unfold thetaCuspLikelihoodEighthBellJetFour
    dsimp only [A, B, e1, e2, e3, e4]
    have hAe3 : 3 * e3 < A * e3 := mul_lt_mul_of_pos_right hA he3
    have hseven : 7 * e2 ≤ A * e3 := by nlinarith
    have hscaled := mul_le_mul_of_nonneg_left hseven (sq_nonneg A)
    nlinarith [mul_pos hA0 he1]
  · unfold thetaCuspLikelihoodEighthBellJetFive
    dsimp only [A, B, e1, e2, e3, e4, e5]
    have hAe4 : 3 * e4 < A * e4 := mul_lt_mul_of_pos_right hA he4
    have htwentyfive : 25 * e3 ≤ 10 * A * e4 := by nlinarith
    have hscaled := mul_le_mul_of_nonneg_left htwentyfive (pow_nonneg hA0.le 3)
    have hAe12 := mul_le_mul_of_nonneg_left he12 hA0.le
    have hAA : A ≤ A ^ (2 : ℕ) := by nlinarith [sq_nonneg (A - 1)]
    have hAe2 := mul_le_mul_of_nonneg_right hAA he2.le
    nlinarith

/-- Full atom-ray monomial trace equals the unnormalized leading eighth spectral moment. -/
theorem tsum_thetaCuspLikelihoodAtomEighthMonomialMass_eq_spectralMoment
    (A : ℝ) {B : ℝ} (hB : 0 < B) :
    (∑' k : ℕ, thetaCuspLikelihoodAtomEighthMonomialMass (k + 2) A B) =
      A ^ (8 : ℕ) * thetaCuspHigherLikelihoodSpectralMoment B 8 := by
  let f : ℝ → ℝ := fun t => (A * t) ^ (8 : ℕ) * Real.exp (-(B * t))
  have hInt : Integrable f thetaCuspHigherLikelihoodSpectralMeasure := by
    have hi :=
      (integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure 8 hB).const_mul
        (A ^ (8 : ℕ))
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
    _ = A ^ (8 : ℕ) * (∫ t : ℝ, t ^ (8 : ℕ) * Real.exp (-(B * t))
        ∂thetaCuspHigherLikelihoodSpectralMeasure) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with t
      dsimp [f]
      ring
    _ = A ^ (8 : ℕ) * thetaCuspHigherLikelihoodSpectralMoment B 8 := by
      rw [thetaCuspHigherLikelihoodSpectralMoment_eq_integral]
      congr 1
      apply integral_congr_ae
      filter_upwards with t
      ring

/-- Bell grades `4`, `6`, and `8` fit inside the completed higher-even Fock loss. -/
theorem thetaCuspLikelihoodEighthBellHigherEvenLoss_le_fock
    {x : ℝ} (hx : 0 ≤ x) :
    6 * thetaCuspLikelihoodEighthBellGradeFour x +
          120 * thetaCuspLikelihoodEighthBellGradeSix x +
        5040 * thetaCuspLikelihoodEighthBellGradeEight x ≤
      (256 / thetaCuspLikelihoodPartition (thetaCuspLikelihoodCoordinate x)) *
        thetaCuspLikelihoodEighthHigherEvenFockLoss x := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  let P := thetaCuspLikelihoodPartition B
  let r := thetaCuspHigherLikelihoodSpectralResponse B
  let p := thetaCuspLikelihoodTailProbability B
  let e1 := thetaCuspLikelihoodMean B
  let e2 := thetaCuspLikelihoodNormalizedMoment B 2
  let e3 := thetaCuspLikelihoodNormalizedMoment B 3
  let e4 := thetaCuspLikelihoodNormalizedMoment B 4
  let e5 := thetaCuspLikelihoodNormalizedMoment B 5
  let e8 := thetaCuspLikelihoodNormalizedMoment B 8
  let b1 := thetaCuspLikelihoodEighthBellJetOne x
  let b2 := thetaCuspLikelihoodEighthBellJetTwo x
  let b3 := thetaCuspLikelihoodEighthBellJetThree x
  let b4 := thetaCuspLikelihoodEighthBellJetFour x
  let b5 := thetaCuspLikelihoodEighthBellJetFive x
  have hB : 0 < B := by simpa only [B] using thetaCuspLikelihoodCoordinate_pos hx
  have hA : 0 < A := by
    exact Real.pi_pos.trans_le (by
      dsimp only [A, thetaCuspSingleAtomReflectionScale]
      norm_num
      have he : 1 ≤ Real.exp (2 * x) := Real.one_le_exp (by linarith)
      linarith only [mul_le_mul_of_nonneg_left he Real.pi_pos.le])
  have hP : 0 < P := by simpa only [P] using thetaCuspLikelihoodPartition_pos hB
  have hr : 0 ≤ r := by
    dsimp only [r]
    rw [← thetaCuspHigherLikelihoodSpectralMoment_zero_eq_response hB]
    exact thetaCuspHigherLikelihoodSpectralMoment_nonneg 0
  have hp : 0 ≤ p := by
    dsimp only [p, thetaCuspLikelihoodTailProbability]
    exact thetaCuspLikelihoodNormalizedMoment_nonneg hB 0
  have he1 : 0 < e1 := by simpa only [e1] using thetaCuspLikelihoodMean_pos hB
  have he2 : 0 ≤ e2 := by
    simpa only [e2] using thetaCuspLikelihoodNormalizedMoment_nonneg hB 2
  have he3 : 0 ≤ e3 := by
    simpa only [e3] using thetaCuspLikelihoodNormalizedMoment_nonneg hB 3
  have he4 : 0 ≤ e4 := by
    simpa only [e4] using thetaCuspLikelihoodNormalizedMoment_nonneg hB 4
  have he5 : 0 ≤ e5 := by
    simpa only [e5] using thetaCuspLikelihoodNormalizedMoment_nonneg hB 5
  have he8 : 0 ≤ e8 := by
    simpa only [e8] using thetaCuspLikelihoodNormalizedMoment_nonneg hB 8
  have hpos := thetaCuspLikelihoodEighthBellJets_one_to_six_pos hx
  have hb1 : 0 < b1 := by simpa only [b1] using hpos.1
  have hb2 : 0 < b2 := by simpa only [b2] using hpos.2.1
  have hb3 : 0 < b3 := by simpa only [b3] using hpos.2.2.1
  have hb4 : 0 < b4 := by simpa only [b4] using hpos.2.2.2.1
  have hb5 : 0 < b5 := by simpa only [b5] using hpos.2.2.2.2.1
  rcases thetaCuspLikelihoodEighthBellJets_one_to_five_le_leading hx with
    ⟨hb1le, hb2le, hb3le, hb4le, hb5le⟩
  have hb1le' : b1 ≤ 2 * A * e1 := by simpa only [b1, A, B, e1] using hb1le
  have hb2le' : b2 ≤ 4 * A ^ (2 : ℕ) * e2 := by simpa only [b2, A, B, e2] using hb2le
  have hb3le' : b3 ≤ 8 * A ^ (3 : ℕ) * e3 := by simpa only [b3, A, B, e3] using hb3le
  have hb4le' : b4 ≤ 16 * A ^ (4 : ℕ) * e4 := by simpa only [b4, A, B, e4] using hb4le
  have hb5le' : b5 ≤ 32 * A ^ (5 : ℕ) * e5 := by simpa only [b5, A, B, e5] using hb5le
  have hpEq : p = r / (1 + r) := by
    dsimp only [p, r, thetaCuspLikelihoodTailProbability,
      thetaCuspLikelihoodNormalizedMoment, thetaCuspLikelihoodPartition]
    rw [thetaCuspHigherLikelihoodSpectralMoment_zero_eq_response hB]
  have hden : 0 < 1 + r := by linarith
  have hpr : p ≤ r := by
    rw [hpEq]
    apply (div_le_iff₀ hden).2
    linarith only [sq_nonneg r]
  have hp3r3 : p ^ (3 : ℕ) ≤ r ^ (3 : ℕ) := pow_le_pow_left₀ hp hpr 3
  have hp5r5 : p ^ (5 : ℕ) ≤ r ^ (5 : ℕ) := pow_le_pow_left₀ hp hpr 5
  have hp7r7 : p ^ (7 : ℕ) ≤ r ^ (7 : ℕ) := pow_le_pow_left₀ hp hpr 7

  have h1115 : e1 * e1 * (e1 * e5) ≤ p ^ (3 : ℕ) * e8 := by
    simpa only [e1, e5, e8, thetaCuspLikelihoodNormalizedMoment_one_eq_mean,
      show 1 + 1 + (1 + 5) = 8 by norm_num] using
      thetaCuspLikelihoodNormalizedMoment_four_mul_le hB 1 1 1 5
  have h1124 : e1 * e1 * (e2 * e4) ≤ p ^ (3 : ℕ) * e8 := by
    simpa only [e1, e2, e4, e8, thetaCuspLikelihoodNormalizedMoment_one_eq_mean,
      show 1 + 1 + (2 + 4) = 8 by norm_num] using
      thetaCuspLikelihoodNormalizedMoment_four_mul_le hB 1 1 2 4
  have h1133 : e1 * e1 * (e3 * e3) ≤ p ^ (3 : ℕ) * e8 := by
    simpa only [e1, e3, e8, thetaCuspLikelihoodNormalizedMoment_one_eq_mean,
      show 1 + 1 + (3 + 3) = 8 by norm_num] using
      thetaCuspLikelihoodNormalizedMoment_four_mul_le hB 1 1 3 3
  have h1223 : e1 * e2 * (e2 * e3) ≤ p ^ (3 : ℕ) * e8 := by
    simpa only [e1, e2, e3, e8, thetaCuspLikelihoodNormalizedMoment_one_eq_mean,
      show 1 + 2 + (2 + 3) = 8 by norm_num] using
      thetaCuspLikelihoodNormalizedMoment_four_mul_le hB 1 2 2 3
  have h2222 : e2 * e2 * (e2 * e2) ≤ p ^ (3 : ℕ) * e8 := by
    simpa only [e2, e8, show 2 + 2 + (2 + 2) = 8 by norm_num] using
      thetaCuspLikelihoodNormalizedMoment_four_mul_le hB 2 2 2 2

  have hb1115 : b1 ^ (3 : ℕ) * b5 ≤ 256 * A ^ (8 : ℕ) * p ^ (3 : ℕ) * e8 := by
    calc
      b1 ^ (3 : ℕ) * b5 ≤ (2 * A * e1) ^ (3 : ℕ) * (32 * A ^ (5 : ℕ) * e5) := by gcongr
      _ = 256 * A ^ (8 : ℕ) * (e1 * e1 * (e1 * e5)) := by ring
      _ ≤ 256 * A ^ (8 : ℕ) * (p ^ (3 : ℕ) * e8) := by gcongr
      _ = 256 * A ^ (8 : ℕ) * p ^ (3 : ℕ) * e8 := by ring
  have hb1124 : b1 ^ (2 : ℕ) * b2 * b4 ≤ 256 * A ^ (8 : ℕ) * p ^ (3 : ℕ) * e8 := by
    calc
      b1 ^ (2 : ℕ) * b2 * b4 ≤ (2 * A * e1) ^ (2 : ℕ) * (4 * A ^ (2 : ℕ) * e2) *
          (16 * A ^ (4 : ℕ) * e4) := by gcongr
      _ = 256 * A ^ (8 : ℕ) * (e1 * e1 * (e2 * e4)) := by ring
      _ ≤ 256 * A ^ (8 : ℕ) * (p ^ (3 : ℕ) * e8) := by gcongr
      _ = 256 * A ^ (8 : ℕ) * p ^ (3 : ℕ) * e8 := by ring
  have hb1133 : b1 ^ (2 : ℕ) * b3 ^ (2 : ℕ) ≤ 256 * A ^ (8 : ℕ) * p ^ (3 : ℕ) * e8 := by
    calc
      b1 ^ (2 : ℕ) * b3 ^ (2 : ℕ) ≤ (2 * A * e1) ^ (2 : ℕ) * (8 * A ^ (3 : ℕ) * e3) ^ (2 : ℕ) := by gcongr
      _ = 256 * A ^ (8 : ℕ) * (e1 * e1 * (e3 * e3)) := by ring
      _ ≤ 256 * A ^ (8 : ℕ) * (p ^ (3 : ℕ) * e8) := by gcongr
      _ = 256 * A ^ (8 : ℕ) * p ^ (3 : ℕ) * e8 := by ring
  have hb1223 : b1 * b2 ^ (2 : ℕ) * b3 ≤ 256 * A ^ (8 : ℕ) * p ^ (3 : ℕ) * e8 := by
    calc
      b1 * b2 ^ (2 : ℕ) * b3 ≤ (2 * A * e1) * (4 * A ^ (2 : ℕ) * e2) ^ (2 : ℕ) *
          (8 * A ^ (3 : ℕ) * e3) := by gcongr
      _ = 256 * A ^ (8 : ℕ) * (e1 * e2 * (e2 * e3)) := by ring
      _ ≤ 256 * A ^ (8 : ℕ) * (p ^ (3 : ℕ) * e8) := by gcongr
      _ = 256 * A ^ (8 : ℕ) * p ^ (3 : ℕ) * e8 := by ring
  have hb2222 : b2 ^ (4 : ℕ) ≤ 256 * A ^ (8 : ℕ) * p ^ (3 : ℕ) * e8 := by
    calc
      b2 ^ (4 : ℕ) ≤ (4 * A ^ (2 : ℕ) * e2) ^ (4 : ℕ) := by gcongr
      _ = 256 * A ^ (8 : ℕ) * (e2 * e2 * (e2 * e2)) := by ring
      _ ≤ 256 * A ^ (8 : ℕ) * (p ^ (3 : ℕ) * e8) := by gcongr
      _ = 256 * A ^ (8 : ℕ) * p ^ (3 : ℕ) * e8 := by ring
  have hgrade4 : thetaCuspLikelihoodEighthBellGradeFour x ≤
      1701 * (256 * A ^ (8 : ℕ) * p ^ (3 : ℕ) * e8) := by
    dsimp only [thetaCuspLikelihoodEighthBellGradeFour, b1, b2, b3, b4, b5]
    linarith only [hb1115, hb1124, hb1133, hb1223, hb2222]
  have hgrade4r : 6 * thetaCuspLikelihoodEighthBellGradeFour x ≤
      256 * (4 : ℝ) ^ (7 : ℕ) * r ^ (3 : ℕ) * A ^ (8 : ℕ) * e8 := by
    have hscale := mul_le_mul_of_nonneg_right hp3r3
      (mul_nonneg (pow_nonneg hA.le 8) he8)
    have hmass : 0 ≤ r ^ (3 : ℕ) * (A ^ (8 : ℕ) * e8) :=
      mul_nonneg (pow_nonneg hr 3) (mul_nonneg (pow_nonneg hA.le 8) he8)
    linarith only [hgrade4, hscale, hmass]

  have h111113 : (e1 * e1 * (e1 * e1)) * (e1 * e3) ≤ p ^ (5 : ℕ) * e8 := by
    simpa only [e1, e3, e8, thetaCuspLikelihoodNormalizedMoment_one_eq_mean,
      show 1 + 1 + (1 + 1) + (1 + 3) = 8 by norm_num] using
      thetaCuspLikelihoodNormalizedMoment_six_mul_le hB 1 1 1 1 1 3
  have h111122 : (e1 * e1 * (e1 * e1)) * (e2 * e2) ≤ p ^ (5 : ℕ) * e8 := by
    simpa only [e1, e2, e8, thetaCuspLikelihoodNormalizedMoment_one_eq_mean,
      show 1 + 1 + (1 + 1) + (2 + 2) = 8 by norm_num] using
      thetaCuspLikelihoodNormalizedMoment_six_mul_le hB 1 1 1 1 2 2
  have hb111113 : b1 ^ (5 : ℕ) * b3 ≤ 256 * A ^ (8 : ℕ) * p ^ (5 : ℕ) * e8 := by
    calc
      b1 ^ (5 : ℕ) * b3 ≤ (2 * A * e1) ^ (5 : ℕ) * (8 * A ^ (3 : ℕ) * e3) := by gcongr
      _ = 256 * A ^ (8 : ℕ) * ((e1 * e1 * (e1 * e1)) * (e1 * e3)) := by ring
      _ ≤ 256 * A ^ (8 : ℕ) * (p ^ (5 : ℕ) * e8) := by gcongr
      _ = 256 * A ^ (8 : ℕ) * p ^ (5 : ℕ) * e8 := by ring
  have hb111122 : b1 ^ (4 : ℕ) * b2 ^ (2 : ℕ) ≤ 256 * A ^ (8 : ℕ) * p ^ (5 : ℕ) * e8 := by
    calc
      b1 ^ (4 : ℕ) * b2 ^ (2 : ℕ) ≤ (2 * A * e1) ^ (4 : ℕ) * (4 * A ^ (2 : ℕ) * e2) ^ (2 : ℕ) := by gcongr
      _ = 256 * A ^ (8 : ℕ) * ((e1 * e1 * (e1 * e1)) * (e2 * e2)) := by ring
      _ ≤ 256 * A ^ (8 : ℕ) * (p ^ (5 : ℕ) * e8) := by gcongr
      _ = 256 * A ^ (8 : ℕ) * p ^ (5 : ℕ) * e8 := by ring
  have hgrade6 : thetaCuspLikelihoodEighthBellGradeSix x ≤
      266 * (256 * A ^ (8 : ℕ) * p ^ (5 : ℕ) * e8) := by
    dsimp only [thetaCuspLikelihoodEighthBellGradeSix, b1, b2, b3]
    linarith only [hb111113, hb111122]
  have hgrade6r : 120 * thetaCuspLikelihoodEighthBellGradeSix x ≤
      256 * (6 : ℝ) ^ (7 : ℕ) * r ^ (5 : ℕ) * A ^ (8 : ℕ) * e8 := by
    have hscale := mul_le_mul_of_nonneg_right hp5r5
      (mul_nonneg (pow_nonneg hA.le 8) he8)
    calc
      120 * thetaCuspLikelihoodEighthBellGradeSix x ≤
          120 * (266 * (256 * A ^ (8 : ℕ) * p ^ (5 : ℕ) * e8)) := by gcongr
      _ = (120 * 266 * 256 : ℝ) * (p ^ (5 : ℕ) * (A ^ (8 : ℕ) * e8)) := by ring
      _ ≤ (120 * 266 * 256 : ℝ) * (r ^ (5 : ℕ) * (A ^ (8 : ℕ) * e8)) := by gcongr
      _ ≤ (256 * (6 : ℝ) ^ (7 : ℕ)) * (r ^ (5 : ℕ) * (A ^ (8 : ℕ) * e8)) := by
        exact mul_le_mul_of_nonneg_right (by norm_num)
          (mul_nonneg (pow_nonneg hr 5)
            (mul_nonneg (pow_nonneg hA.le 8) he8))
      _ = 256 * (6 : ℝ) ^ (7 : ℕ) * r ^ (5 : ℕ) * A ^ (8 : ℕ) * e8 := by ring

  have hones : (e1 * e1 * (e1 * e1)) * (e1 * e1 * (e1 * e1)) ≤
      p ^ (7 : ℕ) * e8 := by
    simpa only [e1, e8, thetaCuspLikelihoodNormalizedMoment_one_eq_mean,
      show 1 + 1 + (1 + 1) + (1 + 1 + (1 + 1)) = 8 by norm_num] using
      thetaCuspLikelihoodNormalizedMoment_eight_mul_le hB 1 1 1 1 1 1 1 1
  have hbEight : b1 ^ (8 : ℕ) ≤ 256 * A ^ (8 : ℕ) * p ^ (7 : ℕ) * e8 := by
    calc
      b1 ^ (8 : ℕ) ≤ (2 * A * e1) ^ (8 : ℕ) := by gcongr
      _ = 256 * A ^ (8 : ℕ) * ((e1 * e1 * (e1 * e1)) *
          (e1 * e1 * (e1 * e1))) := by ring
      _ ≤ 256 * A ^ (8 : ℕ) * (p ^ (7 : ℕ) * e8) := by gcongr
      _ = 256 * A ^ (8 : ℕ) * p ^ (7 : ℕ) * e8 := by ring
  have hgrade8r : 5040 * thetaCuspLikelihoodEighthBellGradeEight x ≤
      256 * (8 : ℝ) ^ (7 : ℕ) * r ^ (7 : ℕ) * A ^ (8 : ℕ) * e8 := by
    have hscale := mul_le_mul_of_nonneg_right hp7r7
      (mul_nonneg (pow_nonneg hA.le 8) he8)
    dsimp only [thetaCuspLikelihoodEighthBellGradeEight, b1] at hbEight ⊢
    calc
      5040 * thetaCuspLikelihoodEighthBellJetOne x ^ (8 : ℕ) ≤
          5040 * (256 * A ^ (8 : ℕ) * p ^ (7 : ℕ) * e8) := by gcongr
      _ = (5040 * 256 : ℝ) * (p ^ (7 : ℕ) * (A ^ (8 : ℕ) * e8)) := by ring
      _ ≤ (5040 * 256 : ℝ) * (r ^ (7 : ℕ) * (A ^ (8 : ℕ) * e8)) := by gcongr
      _ ≤ (256 * (8 : ℝ) ^ (7 : ℕ)) * (r ^ (7 : ℕ) * (A ^ (8 : ℕ) * e8)) := by
        exact mul_le_mul_of_nonneg_right (by norm_num)
          (mul_nonneg (pow_nonneg hr 7)
            (mul_nonneg (pow_nonneg hA.le 8) he8))
      _ = 256 * (8 : ℝ) ^ (7 : ℕ) * r ^ (7 : ℕ) * A ^ (8 : ℕ) * e8 := by ring

  let f : ℕ → ℝ := fun m =>
    (((2 * (m + 2) : ℕ) : ℝ) ^ (7 : ℕ)) * r ^ (2 * (m + 2) - 1)
  have hrSmall : 399 * r < 1 := by
    simpa only [B, r] using
      three_hundred_ninety_nine_mul_thetaCuspHigherLikelihoodSpectralResponse_lt_one hx
  have hs : Summable f := by
    simpa only [f] using
      (summable_thetaCuspLikelihoodEighthHigherEvenSectorTail_and_le hr hrSmall).1
  have hrem : 0 ≤ ∑' m : ℕ, f (m + 3) := tsum_nonneg fun m => by
    dsimp only [f]
    positivity
  have hfinite :
      (4 : ℝ) ^ (7 : ℕ) * r ^ (3 : ℕ) + (6 : ℝ) ^ (7 : ℕ) * r ^ (5 : ℕ) + (8 : ℝ) ^ (7 : ℕ) * r ^ (7 : ℕ) ≤
        thetaCuspLikelihoodEighthHigherEvenSectorTail r := by
    have hsplit := hs.sum_add_tsum_nat_add 3
    have hsum : (∑ m ∈ Finset.range 3, f m) ≤ ∑' m : ℕ, f m := by
      rw [← hsplit]
      exact le_add_of_nonneg_right hrem
    norm_num [thetaCuspLikelihoodEighthHigherEvenSectorTail, f,
      Finset.sum_range_succ] at hsum ⊢
    exact hsum
  have hbell :
      6 * thetaCuspLikelihoodEighthBellGradeFour x +
            120 * thetaCuspLikelihoodEighthBellGradeSix x +
          5040 * thetaCuspLikelihoodEighthBellGradeEight x ≤
        256 * A ^ (8 : ℕ) * e8 * thetaCuspLikelihoodEighthHigherEvenSectorTail r := by
    have hcoef0 : 0 ≤ 256 * A ^ (8 : ℕ) * e8 := by positivity
    have htailScaled := mul_le_mul_of_nonneg_left hfinite hcoef0
    calc
      6 * thetaCuspLikelihoodEighthBellGradeFour x +
            120 * thetaCuspLikelihoodEighthBellGradeSix x +
          5040 * thetaCuspLikelihoodEighthBellGradeEight x ≤
        256 * (4 : ℝ) ^ (7 : ℕ) * r ^ (3 : ℕ) * A ^ (8 : ℕ) * e8 +
            256 * (6 : ℝ) ^ (7 : ℕ) * r ^ (5 : ℕ) * A ^ (8 : ℕ) * e8 +
          256 * (8 : ℝ) ^ (7 : ℕ) * r ^ (7 : ℕ) * A ^ (8 : ℕ) * e8 :=
        add_le_add (add_le_add hgrade4r hgrade6r) hgrade8r
      _ = (256 * A ^ (8 : ℕ) * e8) *
          ((4 : ℝ) ^ (7 : ℕ) * r ^ (3 : ℕ) + (6 : ℝ) ^ (7 : ℕ) * r ^ (5 : ℕ) +
            (8 : ℝ) ^ (7 : ℕ) * r ^ (7 : ℕ)) := by ring
      _ ≤ (256 * A ^ (8 : ℕ) * e8) *
          thetaCuspLikelihoodEighthHigherEvenSectorTail r := htailScaled
      _ = 256 * A ^ (8 : ℕ) * e8 *
          thetaCuspLikelihoodEighthHigherEvenSectorTail r := by ring
  have hmass := tsum_thetaCuspLikelihoodAtomEighthMonomialMass_eq_spectralMoment A hB
  have hM8 : thetaCuspHigherLikelihoodSpectralMoment B 8 = P * e8 := by
    change thetaCuspHigherLikelihoodSpectralMoment B 8 =
      P * (thetaCuspHigherLikelihoodSpectralMoment B 8 / P)
    exact (mul_div_cancel₀ (thetaCuspHigherLikelihoodSpectralMoment B 8) hP.ne').symm
  have hfock : thetaCuspLikelihoodEighthHigherEvenFockLoss x =
      thetaCuspLikelihoodEighthHigherEvenSectorTail r * A ^ (8 : ℕ) * (P * e8) := by
    unfold thetaCuspLikelihoodEighthHigherEvenFockLoss
    dsimp only [A, B, r]
    rw [hmass, hM8]
    ring
  rw [hfock]
  change _ ≤ (256 / P) *
    (thetaCuspLikelihoodEighthHigherEvenSectorTail r * A ^ (8 : ℕ) * (P * e8))
  rw [show (256 / P) *
      (thetaCuspLikelihoodEighthHigherEvenSectorTail r * A ^ (8 : ℕ) * (P * e8)) =
        256 * A ^ (8 : ℕ) * e8 * thetaCuspLikelihoodEighthHigherEvenSectorTail r by
    field_simp [hP.ne']]
  exact hbell

end

end RHTower
