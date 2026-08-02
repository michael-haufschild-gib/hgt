import GaloisForLFunctions.RHTower.EulerPrimitiveCommonTestPolarizedChainSource

/-!
# Canonical transverse four-unit orientation of the Euler boundary source

The polarized Euler boundary has a diagonal common-test channel.  Projecting
the pole-centered Fisher score onto that channel leaves the explicit
head/tail residual

`((1 - exp (-t)) h(t), -exp (-t) h(t))`,

where `h(t) = 2(1-t)`.  This file proves, without a divisor or RH premise,
that the residual is orthogonal to every common Laplace test and has exact
norm square three.  Its canonical normalization by `2 / sqrt 3` is therefore
a source-derived transverse orientation of norm square four.

This is the boundary vector required before scalar trace.  Identifying its
transported common-test column with the actual Xi Ward column is a separate
global landing theorem.
-/

open Filter MeasureTheory Set

namespace RHTower

noncomputable section

private theorem integrableOn_eulerPrimitive_pow_exp_neg_rate
    (k : ℕ) {r : ℝ} (hr : 0 < r) :
    IntegrableOn
      (fun t : ℝ => t ^ k * Real.exp (-(r * t))) (Ioi 0) := by
  have hvalue := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (k : ℝ) + 1) (r := r) (by positivity) hr
  have hne :
      (∫ t : ℝ in Ioi 0,
        t ^ ((k : ℝ) + 1 - 1) *
          Real.exp (-(r * t))) ≠ 0 := by
    rw [hvalue]
    positivity
  have hint :
      IntegrableOn
        (fun t : ℝ =>
          t ^ ((k : ℝ) + 1 - 1) *
            Real.exp (-(r * t))) (Ioi 0) :=
    Integrable.of_integral_ne_zero hne
  simpa only [add_sub_cancel_right, Real.rpow_natCast] using hint

private theorem integral_eulerPrimitive_pow_exp_neg_rate
    (k : ℕ) {r : ℝ} (hr : 0 < r) :
    (∫ t : ℝ in Ioi 0, t ^ k * Real.exp (-(r * t))) =
      (1 / r : ℝ) ^ (k + 1) * k.factorial := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (k : ℝ) + 1) (r := r) (by positivity) hr
  simp only [add_sub_cancel_right, Real.rpow_natCast] at h
  rw [Real.Gamma_nat_eq_factorial] at h
  rw [show (k : ℝ) + 1 = ((k + 1 : ℕ) : ℝ) by norm_cast] at h
  rw [Real.rpow_natCast] at h
  simpa using h

private def eulerPrimitiveBoundaryScoreRateEnergy
    (r t : ℝ) : ℝ :=
  4 * (1 - t) ^ 2 * Real.exp (-(r * t))

private theorem integrableOn_eulerPrimitiveBoundaryScoreRateEnergy
    {r : ℝ} (hr : 0 < r) :
    IntegrableOn
      (eulerPrimitiveBoundaryScoreRateEnergy r) (Ioi 0) := by
  have h0 := integrableOn_eulerPrimitive_pow_exp_neg_rate 0 hr
  have h1 := integrableOn_eulerPrimitive_pow_exp_neg_rate 1 hr
  have h2 := integrableOn_eulerPrimitive_pow_exp_neg_rate 2 hr
  have hpoly :
      eulerPrimitiveBoundaryScoreRateEnergy r =
        fun t : ℝ =>
          4 * (t ^ 0 * Real.exp (-(r * t))) -
            8 * (t ^ 1 * Real.exp (-(r * t))) +
              4 * (t ^ 2 * Real.exp (-(r * t))) := by
    funext t
    unfold eulerPrimitiveBoundaryScoreRateEnergy
    ring
  rw [hpoly]
  exact ((h0.const_mul 4).sub (h1.const_mul 8)).add
    (h2.const_mul 4)

private theorem integral_eulerPrimitiveBoundaryScoreRateEnergy
    {r : ℝ} (hr : 0 < r) :
    (∫ t : ℝ in Ioi 0,
      eulerPrimitiveBoundaryScoreRateEnergy r t) =
        4 * ((1 / r : ℝ) ^ 1 * (0 : ℕ).factorial) -
          8 * ((1 / r : ℝ) ^ 2 * (1 : ℕ).factorial) +
            4 * ((1 / r : ℝ) ^ 3 * (2 : ℕ).factorial) := by
  have h0 := integrableOn_eulerPrimitive_pow_exp_neg_rate 0 hr
  have h1 := integrableOn_eulerPrimitive_pow_exp_neg_rate 1 hr
  have h2 := integrableOn_eulerPrimitive_pow_exp_neg_rate 2 hr
  have hpoly :
      eulerPrimitiveBoundaryScoreRateEnergy r =
        fun t : ℝ =>
          4 * (t ^ 0 * Real.exp (-(r * t))) -
            8 * (t ^ 1 * Real.exp (-(r * t))) +
              4 * (t ^ 2 * Real.exp (-(r * t))) := by
    funext t
    unfold eulerPrimitiveBoundaryScoreRateEnergy
    ring
  rw [hpoly]
  rw [show
    (∫ t : ℝ in Ioi 0,
      4 * (t ^ 0 * Real.exp (-(r * t))) -
        8 * (t ^ 1 * Real.exp (-(r * t))) +
          4 * (t ^ 2 * Real.exp (-(r * t)))) =
      (∫ t : ℝ in Ioi 0,
        4 * (t ^ 0 * Real.exp (-(r * t))) -
          8 * (t ^ 1 * Real.exp (-(r * t)))) +
        ∫ t : ℝ in Ioi 0,
          4 * (t ^ 2 * Real.exp (-(r * t))) by
      simpa only [Pi.add_apply, Pi.sub_apply] using
        integral_add
          ((h0.const_mul 4).sub (h1.const_mul 8))
          (h2.const_mul 4)]
  rw [show
    (∫ t : ℝ in Ioi 0,
      4 * (t ^ 0 * Real.exp (-(r * t))) -
        8 * (t ^ 1 * Real.exp (-(r * t)))) =
      (∫ t : ℝ in Ioi 0,
        4 * (t ^ 0 * Real.exp (-(r * t)))) -
        ∫ t : ℝ in Ioi 0,
          8 * (t ^ 1 * Real.exp (-(r * t))) by
      simpa only [Pi.sub_apply] using
        integral_sub (h0.const_mul 4) (h1.const_mul 8)]
  rw [integral_const_mul, integral_const_mul, integral_const_mul,
    integral_eulerPrimitive_pow_exp_neg_rate 0 hr,
    integral_eulerPrimitive_pow_exp_neg_rate 1 hr,
    integral_eulerPrimitive_pow_exp_neg_rate 2 hr]

private theorem integral_eulerPrimitiveBoundaryScoreRateEnergy_one :
    (∫ t : ℝ in Ioi 0,
      eulerPrimitiveBoundaryScoreRateEnergy 1 t) = 4 := by
  rw [integral_eulerPrimitiveBoundaryScoreRateEnergy (by norm_num)]
  norm_num

private theorem integral_eulerPrimitiveBoundaryScoreRateEnergy_two :
    (∫ t : ℝ in Ioi 0,
      eulerPrimitiveBoundaryScoreRateEnergy 2 t) = 1 := by
  rw [integral_eulerPrimitiveBoundaryScoreRateEnergy (by norm_num)]
  norm_num

/--
Orthogonal residual of the pole-centered score after projection onto the
diagonal common-test channel.
-/
def eulerPrimitiveBoundaryTransverseScoreRaw :
    EulerPrimitiveBoundaryPolarizedFeature :=
  (fun t =>
      (eulerPrimitiveBoundaryTailWeight t : ℂ) *
        eulerPrimitiveBoundaryPolarizedScore.1 t,
    fun t =>
      -(eulerPrimitiveBoundaryHeadWeight t : ℂ) *
        eulerPrimitiveBoundaryPolarizedScore.1 t)

theorem eulerPrimitiveBoundaryPolarizedPairing_test_transverseScoreRaw
    {a : ℂ} :
    eulerPrimitiveBoundaryPolarizedPairing
        (eulerPrimitiveBoundaryPolarizedTest a)
        eulerPrimitiveBoundaryTransverseScoreRaw = 0 := by
  rw [eulerPrimitiveBoundaryPolarizedPairing]
  have hsecond :
      (fun t : ℝ =>
        (eulerPrimitiveBoundaryTailWeight t : ℂ) *
          (eulerPrimitiveBoundaryPolarizedTest a).2 t *
            star (eulerPrimitiveBoundaryTransverseScoreRaw.2 t)) =
        fun t : ℝ =>
          -((eulerPrimitiveBoundaryHeadWeight t : ℂ) *
            (eulerPrimitiveBoundaryPolarizedTest a).1 t *
              star (eulerPrimitiveBoundaryTransverseScoreRaw.1 t)) := by
    funext t
    simp only [eulerPrimitiveBoundaryTransverseScoreRaw,
      eulerPrimitiveBoundaryPolarizedTest, map_mul, map_neg,
      RCLike.star_def, Complex.conj_ofReal,
      eulerPrimitiveBoundaryPolarizedScore]
    ring_nf
  rw [hsecond, integral_neg, add_neg_cancel]

private def eulerPrimitiveBoundaryTransverseScoreRawHeadEnergy
    (t : ℝ) : ℝ :=
  eulerPrimitiveBoundaryHeadWeight t *
    eulerPrimitiveBoundaryTailWeight t ^ 2 *
      (4 * (1 - t) ^ 2)

private def eulerPrimitiveBoundaryTransverseScoreRawTailEnergy
    (t : ℝ) : ℝ :=
  eulerPrimitiveBoundaryTailWeight t *
    eulerPrimitiveBoundaryHeadWeight t ^ 2 *
      (4 * (1 - t) ^ 2)

private theorem
    integrableOn_eulerPrimitiveBoundaryTransverseScoreRawHeadEnergy :
    IntegrableOn
      eulerPrimitiveBoundaryTransverseScoreRawHeadEnergy (Ioi 0) := by
  have h1 :=
    integrableOn_eulerPrimitiveBoundaryScoreRateEnergy
      (r := (1 : ℝ)) (by norm_num)
  have h2 :=
    integrableOn_eulerPrimitiveBoundaryScoreRateEnergy
      (r := (2 : ℝ)) (by norm_num)
  have h3 :=
    integrableOn_eulerPrimitiveBoundaryScoreRateEnergy
      (r := (3 : ℝ)) (by norm_num)
  have heq :
      eulerPrimitiveBoundaryTransverseScoreRawHeadEnergy =
        fun t : ℝ =>
          eulerPrimitiveBoundaryScoreRateEnergy 1 t -
            2 * eulerPrimitiveBoundaryScoreRateEnergy 2 t +
              eulerPrimitiveBoundaryScoreRateEnergy 3 t := by
    funext t
    unfold eulerPrimitiveBoundaryTransverseScoreRawHeadEnergy
      eulerPrimitiveBoundaryScoreRateEnergy
      eulerPrimitiveBoundaryHeadWeight
      eulerPrimitiveBoundaryTailWeight
    rw [show Real.exp (-(2 * t)) = Real.exp (-t) ^ 2 by
      rw [pow_two, ← Real.exp_add]
      congr 1 <;> ring,
      show Real.exp (-(3 * t)) = Real.exp (-t) ^ 3 by
        calc
          Real.exp (-(3 * t)) =
              Real.exp (-t + (-t + -t)) := by congr 1 <;> ring
          _ = Real.exp (-t) ^ 3 := by
            rw [Real.exp_add, Real.exp_add]
            ring]
    ring
  rw [heq]
  exact ((h1.sub (h2.const_mul 2)).add h3)

private theorem
    integrableOn_eulerPrimitiveBoundaryTransverseScoreRawTailEnergy :
    IntegrableOn
      eulerPrimitiveBoundaryTransverseScoreRawTailEnergy (Ioi 0) := by
  have h2 :=
    integrableOn_eulerPrimitiveBoundaryScoreRateEnergy
      (r := (2 : ℝ)) (by norm_num)
  have h3 :=
    integrableOn_eulerPrimitiveBoundaryScoreRateEnergy
      (r := (3 : ℝ)) (by norm_num)
  have heq :
      eulerPrimitiveBoundaryTransverseScoreRawTailEnergy =
        fun t : ℝ =>
          eulerPrimitiveBoundaryScoreRateEnergy 2 t -
            eulerPrimitiveBoundaryScoreRateEnergy 3 t := by
    funext t
    unfold eulerPrimitiveBoundaryTransverseScoreRawTailEnergy
      eulerPrimitiveBoundaryScoreRateEnergy
      eulerPrimitiveBoundaryHeadWeight
      eulerPrimitiveBoundaryTailWeight
    rw [show Real.exp (-(2 * t)) = Real.exp (-t) ^ 2 by
      rw [pow_two, ← Real.exp_add]
      congr 1 <;> ring,
      show Real.exp (-(3 * t)) = Real.exp (-t) ^ 3 by
        calc
          Real.exp (-(3 * t)) =
              Real.exp (-t + (-t + -t)) := by congr 1 <;> ring
          _ = Real.exp (-t) ^ 3 := by
            rw [Real.exp_add, Real.exp_add]
            ring]
    ring
  rw [heq]
  exact h2.sub h3

theorem eulerPrimitiveBoundaryPolarizedPairing_transverseScoreRaw :
    eulerPrimitiveBoundaryPolarizedPairing
        eulerPrimitiveBoundaryTransverseScoreRaw
        eulerPrimitiveBoundaryTransverseScoreRaw = 3 := by
  rw [eulerPrimitiveBoundaryPolarizedPairing]
  have hhead :
      (fun t : ℝ =>
        (eulerPrimitiveBoundaryHeadWeight t : ℂ) *
          eulerPrimitiveBoundaryTransverseScoreRaw.1 t *
            star (eulerPrimitiveBoundaryTransverseScoreRaw.1 t)) =
        fun t : ℝ =>
          (eulerPrimitiveBoundaryTransverseScoreRawHeadEnergy t : ℂ) := by
    funext t
    simp only [eulerPrimitiveBoundaryTransverseScoreRaw,
      eulerPrimitiveBoundaryPolarizedScore, map_mul,
      RCLike.star_def, Complex.conj_ofReal, map_ofNat, map_one,
      map_sub]
    push_cast
    unfold eulerPrimitiveBoundaryTransverseScoreRawHeadEnergy
    push_cast
    ring
  have htail :
      (fun t : ℝ =>
        (eulerPrimitiveBoundaryTailWeight t : ℂ) *
          eulerPrimitiveBoundaryTransverseScoreRaw.2 t *
            star (eulerPrimitiveBoundaryTransverseScoreRaw.2 t)) =
        fun t : ℝ =>
          (eulerPrimitiveBoundaryTransverseScoreRawTailEnergy t : ℂ) := by
    funext t
    simp only [eulerPrimitiveBoundaryTransverseScoreRaw,
      eulerPrimitiveBoundaryPolarizedScore, map_mul, map_neg,
      RCLike.star_def, Complex.conj_ofReal, map_ofNat, map_one,
      map_sub]
    push_cast
    unfold eulerPrimitiveBoundaryTransverseScoreRawTailEnergy
    push_cast
    ring
  rw [hhead, htail, integral_complex_ofReal, integral_complex_ofReal,
    ← Complex.ofReal_add]
  have hsum :
      (∫ t : ℝ in Ioi 0,
          eulerPrimitiveBoundaryTransverseScoreRawHeadEnergy t) +
        ∫ t : ℝ in Ioi 0,
          eulerPrimitiveBoundaryTransverseScoreRawTailEnergy t =
        ∫ t : ℝ in Ioi 0,
          (eulerPrimitiveBoundaryScoreRateEnergy 1 t -
            eulerPrimitiveBoundaryScoreRateEnergy 2 t) := by
    rw [← integral_add
      integrableOn_eulerPrimitiveBoundaryTransverseScoreRawHeadEnergy
      integrableOn_eulerPrimitiveBoundaryTransverseScoreRawTailEnergy]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    unfold eulerPrimitiveBoundaryTransverseScoreRawHeadEnergy
      eulerPrimitiveBoundaryTransverseScoreRawTailEnergy
      eulerPrimitiveBoundaryScoreRateEnergy
      eulerPrimitiveBoundaryHeadWeight
      eulerPrimitiveBoundaryTailWeight
    simp only [one_mul]
    change
      Real.exp (-t) * (1 - Real.exp (-t)) ^ 2 *
            (4 * (1 - t) ^ 2) +
          (1 - Real.exp (-t)) * Real.exp (-t) ^ 2 *
            (4 * (1 - t) ^ 2) =
        4 * (1 - t) ^ 2 * Real.exp (-t) -
          4 * (1 - t) ^ 2 * Real.exp (-(2 * t))
    rw [show Real.exp (-(2 * t)) = Real.exp (-t) ^ 2 by
      rw [pow_two, ← Real.exp_add]
      congr 1 <;> ring]
    ring
  rw [hsum, integral_sub
    (integrableOn_eulerPrimitiveBoundaryScoreRateEnergy
      (r := (1 : ℝ)) (by norm_num))
    (integrableOn_eulerPrimitiveBoundaryScoreRateEnergy
      (r := (2 : ℝ)) (by norm_num)),
    integral_eulerPrimitiveBoundaryScoreRateEnergy_one,
    integral_eulerPrimitiveBoundaryScoreRateEnergy_two]
  norm_num

/-- Simultaneous scalar multiplication of the two polarized source legs. -/
def eulerPrimitiveBoundaryPolarizedScale
    (c : ℂ) (x : EulerPrimitiveBoundaryPolarizedFeature) :
    EulerPrimitiveBoundaryPolarizedFeature :=
  (fun t => c * x.1 t, fun t => c * x.2 t)

theorem eulerPrimitiveBoundaryPolarizedPairing_scale_right
    (c : ℂ) (x y : EulerPrimitiveBoundaryPolarizedFeature) :
    eulerPrimitiveBoundaryPolarizedPairing x
        (eulerPrimitiveBoundaryPolarizedScale c y) =
      star c * eulerPrimitiveBoundaryPolarizedPairing x y := by
  unfold eulerPrimitiveBoundaryPolarizedPairing
    eulerPrimitiveBoundaryPolarizedScale
  rw [mul_add, ← integral_const_mul, ← integral_const_mul]
  congr 1 <;>
    apply setIntegral_congr_fun measurableSet_Ioi <;>
      intro t ht <;>
        simp only [star_mul] <;>
          ring

theorem eulerPrimitiveBoundaryPolarizedPairing_scale_left
    (c : ℂ) (x y : EulerPrimitiveBoundaryPolarizedFeature) :
    eulerPrimitiveBoundaryPolarizedPairing
        (eulerPrimitiveBoundaryPolarizedScale c x) y =
      c * eulerPrimitiveBoundaryPolarizedPairing x y := by
  unfold eulerPrimitiveBoundaryPolarizedPairing
    eulerPrimitiveBoundaryPolarizedScale
  rw [mul_add, ← integral_const_mul, ← integral_const_mul]
  congr 1 <;>
    apply setIntegral_congr_fun measurableSet_Ioi <;>
      intro t ht <;>
        ring

/-- Canonical normalization of the transverse source orientation. -/
def eulerPrimitiveBoundaryTransverseFourUnit :
    EulerPrimitiveBoundaryPolarizedFeature :=
  eulerPrimitiveBoundaryPolarizedScale
    (((2 / Real.sqrt 3 : ℝ) : ℂ))
    eulerPrimitiveBoundaryTransverseScoreRaw

theorem eulerPrimitiveBoundaryPolarizedPairing_test_transverseFourUnit
    {a : ℂ} :
    eulerPrimitiveBoundaryPolarizedPairing
        (eulerPrimitiveBoundaryPolarizedTest a)
        eulerPrimitiveBoundaryTransverseFourUnit = 0 := by
  rw [eulerPrimitiveBoundaryTransverseFourUnit,
    eulerPrimitiveBoundaryPolarizedPairing_scale_right,
    eulerPrimitiveBoundaryPolarizedPairing_test_transverseScoreRaw,
    mul_zero]

theorem eulerPrimitiveBoundaryPolarizedPairing_transverseFourUnit :
    eulerPrimitiveBoundaryPolarizedPairing
        eulerPrimitiveBoundaryTransverseFourUnit
        eulerPrimitiveBoundaryTransverseFourUnit = 4 := by
  rw [eulerPrimitiveBoundaryTransverseFourUnit,
    eulerPrimitiveBoundaryPolarizedPairing_scale_left,
    eulerPrimitiveBoundaryPolarizedPairing_scale_right,
    eulerPrimitiveBoundaryPolarizedPairing_transverseScoreRaw]
  rw [show
    star (((2 / Real.sqrt 3 : ℝ) : ℂ)) =
      (((2 / Real.sqrt 3 : ℝ) : ℂ)) by
        exact Complex.conj_ofReal _]
  have hscale :
      (2 / Real.sqrt 3 : ℝ) *
          ((2 / Real.sqrt 3 : ℝ) * 3) = 4 := by
    have hsqrt : Real.sqrt 3 ≠ 0 := by positivity
    field_simp
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  exact_mod_cast hscale

end

end RHTower
