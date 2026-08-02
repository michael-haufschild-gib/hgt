import GaloisForLFunctions.RHTower.EulerPrimitiveCommonTestBoundaryTransgression

/-!
# Polarized head/tail chain source for the primitive Euler boundary

The unshifted Hardy kernel in the primitive-current boundary is not a
scalar limit.  It is the sum of two positive source channels:

`1 / (a + star b) =
  1 / (1 + a + star b) +
  [1 / (a + star b) - 1 / (1 + a + star b)]`.

This file realizes those channels before scalarization on the half-line.
The head has weight `exp (-t)` and the complementary tail has weight
`1 - exp (-t)`.  Both observe the same Laplace test `exp (-a t)`.
The pole-centered Fisher score is the vector `(2(1-t), 0)`; its exact
source norm is four.

The head/tail weights also force a singular pointwise Hodge rotation.
Writing `q(t) = sqrt(exp t - 1)`, the rotation

`J(f,g)(t) = (q(t) g(t), -f(t)/q(t))`

is defined on the open source ray, squares to `-1`, and exactly exchanges
the two weighted energies.  Its `1/q(t)` coefficient is singular at the
source point.  Thus the four-unit source is now an explicit polarized
chain object on which reflection-odd transport can act before trace.

No Xi divisor, Ward response, or RH premise enters the construction.
-/

open Complex MeasureTheory Set Filter Topology Matrix
open scoped ComplexOrder

namespace RHTower

noncomputable section

/-! ## Weighted two-channel source -/

/-- Head and complementary-tail half-line channels before scalar trace. -/
abbrev EulerPrimitiveBoundaryPolarizedFeature :=
  (ℝ → ℂ) × (ℝ → ℂ)

/-- Compact-head weight. -/
def eulerPrimitiveBoundaryHeadWeight (t : ℝ) : ℝ :=
  Real.exp (-t)

/-- Escaping Hardy-tail weight. -/
def eulerPrimitiveBoundaryTailWeight (t : ℝ) : ℝ :=
  1 - Real.exp (-t)

/-- Weighted sesquilinear observation of two head/tail source vectors. -/
def eulerPrimitiveBoundaryPolarizedPairing
    (x y : EulerPrimitiveBoundaryPolarizedFeature) : ℂ :=
  (∫ t : ℝ in Ioi 0,
      (eulerPrimitiveBoundaryHeadWeight t : ℂ) *
        x.1 t * star (y.1 t)) +
    ∫ t : ℝ in Ioi 0,
      (eulerPrimitiveBoundaryTailWeight t : ℂ) *
        x.2 t * star (y.2 t)

/-- Common Laplace test on both sides of the moving horizon. -/
def eulerPrimitiveBoundaryPolarizedTest
    (a : ℂ) : EulerPrimitiveBoundaryPolarizedFeature :=
  (fun t => Complex.exp (-a * (t : ℂ)),
    fun t => Complex.exp (-a * (t : ℂ)))

/-- Pole-centered source score, retained in the compact-head leg. -/
def eulerPrimitiveBoundaryPolarizedScore :
    EulerPrimitiveBoundaryPolarizedFeature :=
  (fun t => 2 * (1 - (t : ℂ)), fun _ => 0)

theorem eulerPrimitiveBoundaryHeadWeight_add_tailWeight (t : ℝ) :
    eulerPrimitiveBoundaryHeadWeight t +
        eulerPrimitiveBoundaryTailWeight t = 1 := by
  simp [eulerPrimitiveBoundaryHeadWeight,
    eulerPrimitiveBoundaryTailWeight]

theorem eulerPrimitiveBoundaryHeadWeight_pos (t : ℝ) :
    0 < eulerPrimitiveBoundaryHeadWeight t :=
  Real.exp_pos _

theorem eulerPrimitiveBoundaryTailWeight_pos
    {t : ℝ} (ht : 0 < t) :
    0 < eulerPrimitiveBoundaryTailWeight t := by
  rw [eulerPrimitiveBoundaryTailWeight, sub_pos]
  exact Real.exp_lt_one_iff.mpr (by linarith)

/-! ### Half-line moment infrastructure -/

private theorem integrableOn_eulerPrimitive_pow_exp_neg
    (k : ℕ) :
    IntegrableOn
      (fun t : ℝ => t ^ k * Real.exp (-t)) (Ioi 0) := by
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hvalue := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (k : ℝ) + 1) (r := (1 : ℝ)) hk (by norm_num)
  have hne :
      (∫ t : ℝ in Ioi 0,
        t ^ ((k : ℝ) + 1 - 1) *
          Real.exp (-((1 : ℝ) * t))) ≠ 0 := by
    rw [hvalue]
    positivity
  have hint :
      IntegrableOn
        (fun t : ℝ =>
          t ^ ((k : ℝ) + 1 - 1) *
            Real.exp (-((1 : ℝ) * t))) (Ioi 0) :=
    Integrable.of_integral_ne_zero hne
  simpa only [add_sub_cancel_right, Real.rpow_natCast,
    one_mul] using hint

private theorem integral_eulerPrimitive_pow_exp_neg
    (k : ℕ) :
    (∫ t : ℝ in Ioi 0, t ^ k * Real.exp (-t)) =
      k.factorial := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (k : ℝ) + 1) (r := (1 : ℝ))
    (by positivity) (by norm_num)
  simp only [add_sub_cancel_right, Real.rpow_natCast,
    one_mul, one_div, inv_one] at h
  rw [Real.Gamma_nat_eq_factorial] at h
  simpa using h

private theorem integrableOn_eulerPrimitive_id_mul_cexp
    {c : ℂ} (hc : c.re < 0) :
    IntegrableOn
      (fun t : ℝ => (t : ℂ) * Complex.exp (c * (t : ℂ)))
      (Ioi 0) := by
  let a : ℝ := -c.re
  have ha : 0 < a := by
    dsimp only [a]
    linarith
  have hmajor :
      IntegrableOn
        (fun t : ℝ => t ^ 1 * Real.exp (-a * t)) (Ioi 0) := by
    have h :=
      integrableOn_rpow_mul_exp_neg_mul_rpow
        (s := (1 : ℝ)) (p := (1 : ℝ)) (b := a)
        (by norm_num) (by norm_num) ha
    apply h.congr_fun
    · intro t ht
      have ht0 : 0 < t := mem_Ioi.mp ht
      simp [Real.rpow_one]
    · exact measurableSet_Ioi
  change Integrable
    (fun t : ℝ => (t : ℂ) * Complex.exp (c * (t : ℂ)))
    (volume.restrict (Ioi 0))
  apply Integrable.mono hmajor
  · exact
      (Complex.continuous_ofReal.mul
        ((Complex.continuous_ofReal.const_mul c).cexp))
        |>.aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 ≤ t := ht.le
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ht0, Complex.norm_exp]
    simp only [Complex.mul_re, ofReal_re, ofReal_im,
      mul_zero, sub_zero, pow_one]
    dsimp only [a]
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg ht0 (Real.exp_pos _).le)]
    ring_nf
    exact le_rfl

private theorem tendsto_eulerPrimitive_id_mul_cexp_zero
    {c : ℂ} (hc : c.re < 0) :
    Tendsto
      (fun t : ℝ => (t : ℂ) * Complex.exp (c * (t : ℂ)))
      atTop (nhds 0) := by
  let a : ℝ := -c.re
  have ha : 0 < a := by
    dsimp only [a]
    linarith
  have hscale : Tendsto (fun t : ℝ => a * t) atTop atTop :=
    tendsto_id.const_mul_atTop ha
  have hscaled :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hscale
  have hreal :
      Tendsto (fun t : ℝ => t * Real.exp (-a * t))
        atTop (nhds 0) := by
    have hmul :=
      (tendsto_const_nhds :
        Tendsto (fun _ : ℝ => a⁻¹) atTop (nhds a⁻¹)).mul hscaled
    convert hmul using 1
    · funext t
      simp only [Function.comp_apply, pow_one]
      rw [mul_assoc a t (Real.exp (-(a * t))),
        ← mul_assoc a⁻¹ a (t * Real.exp (-(a * t))),
        inv_mul_cancel₀ ha.ne', one_mul]
      congr 1
      ring_nf
    · simp
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply hreal.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ht, Complex.norm_exp]
  simp only [Complex.mul_re, ofReal_re, ofReal_im,
    mul_zero, sub_zero]
  dsimp only [a]
  congr 1
  ring_nf

private theorem integral_eulerPrimitive_id_mul_cexp
    {c : ℂ} (hc : c.re < 0) :
    (∫ t : ℝ in Ioi 0,
      (t : ℂ) * Complex.exp (c * (t : ℂ))) =
      1 / c ^ 2 := by
  have hc0 : c ≠ 0 := by
    intro h
    rw [h] at hc
    norm_num at hc
  have hint :=
    intervalIntegral_tendsto_integral_Ioi 0
      (integrableOn_eulerPrimitive_id_mul_cexp hc) tendsto_id
  have hexp :
      Tendsto
        (fun t : ℝ => Complex.exp (c * (t : ℂ)))
        atTop (nhds 0) := by
    simpa [Complex.tendsto_exp_nhds_zero_iff] using
      tendsto_const_nhds.neg_mul_atTop hc tendsto_id
  have hid := tendsto_eulerPrimitive_id_mul_cexp_zero hc
  have hboundary :
      Tendsto
        (fun t : ℝ =>
          (c * (t : ℂ) - 1) *
            Complex.exp (c * (t : ℂ)))
        atTop (nhds 0) := by
    have hlin := (hid.const_mul c).sub hexp
    convert hlin using 1
    · funext t
      ring
    · simp
  have hrhs :
      Tendsto
        (fun b : ℝ =>
          ((c * b - 1) * Complex.exp (c * b)) / c ^ 2 -
            ((c * (0 : ℝ) - 1) *
              Complex.exp (c * (0 : ℝ))) / c ^ 2)
        atTop (nhds (1 / c ^ 2)) := by
    have h :=
      (hboundary.div_const (c ^ 2)).sub_const
        (((c * (0 : ℝ) - 1) *
          Complex.exp (c * (0 : ℝ))) / c ^ 2)
    simpa only [ofReal_zero, mul_zero, zero_sub,
      Complex.exp_zero, one_mul, neg_div, zero_div,
      sub_neg_eq_add, zero_add, neg_one_mul, neg_neg] using h
  apply tendsto_nhds_unique hint
  convert hrhs using 1
  funext b
  exact integral_id_mul_cexp c hc0 0 b

/-! ## Exact Laplace realization -/

theorem eulerPrimitiveBoundaryPolarizedPairing_test_test
    {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    eulerPrimitiveBoundaryPolarizedPairing
        (eulerPrimitiveBoundaryPolarizedTest a)
        (eulerPrimitiveBoundaryPolarizedTest b) =
      1 / (a + star b) := by
  have hab : 0 < (a + star b).re := by
    simp only [add_re, RCLike.star_def, conj_re]
    linarith
  have hab1 : 0 < (1 + a + star b).re := by
    simp only [add_re, one_re, RCLike.star_def, conj_re]
    linarith
  have hhead :
      (∫ t : ℝ in Ioi 0,
        (eulerPrimitiveBoundaryHeadWeight t : ℂ) *
          (eulerPrimitiveBoundaryPolarizedTest a).1 t *
            star ((eulerPrimitiveBoundaryPolarizedTest b).1 t)) =
        1 / (1 + a + star b) := by
    rw [← integral_cauchyFeaturePair hab1]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    simp only [eulerPrimitiveBoundaryHeadWeight,
      eulerPrimitiveBoundaryPolarizedTest, RCLike.star_def]
    rw [← Complex.exp_conj, Complex.ofReal_exp]
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    simp
    ring
  have htail :
      (∫ t : ℝ in Ioi 0,
        (eulerPrimitiveBoundaryTailWeight t : ℂ) *
          (eulerPrimitiveBoundaryPolarizedTest a).2 t *
            star ((eulerPrimitiveBoundaryPolarizedTest b).2 t)) =
        1 / (a + star b) - 1 / (1 + a + star b) := by
    have h0 :
        IntegrableOn
          (fun t : ℝ =>
            Complex.exp (-(a + star b) * (t : ℂ))) (Ioi 0) :=
      integrableOn_exp_mul_complex_Ioi (by
        simp only [neg_re, add_re, RCLike.star_def, conj_re]
        linarith) 0
    have h1 :
        IntegrableOn
          (fun t : ℝ =>
            Complex.exp (-(1 + a + star b) * (t : ℂ))) (Ioi 0) :=
      integrableOn_exp_mul_complex_Ioi (by
        simp only [neg_re, add_re, one_re, RCLike.star_def, conj_re]
        linarith) 0
    rw [← integral_cauchyFeaturePair hab,
      ← integral_cauchyFeaturePair hab1, ← integral_sub h0 h1]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    simp only [eulerPrimitiveBoundaryTailWeight,
      eulerPrimitiveBoundaryPolarizedTest, RCLike.star_def]
    rw [← Complex.exp_conj]
    push_cast
    have hbase :
        Complex.exp (-a * (t : ℂ)) *
            Complex.exp ((starRingEnd ℂ) (-b * (t : ℂ))) =
          Complex.exp
            (-(a + (starRingEnd ℂ) b) * (t : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      simp
      ring
    rw [mul_assoc, hbase]
    rw [show
      Complex.exp
          (-(1 + a + (starRingEnd ℂ) b) * (t : ℂ)) =
        Complex.exp (-(t : ℂ)) *
          Complex.exp
            (-(a + (starRingEnd ℂ) b) * (t : ℂ)) by
      rw [← Complex.exp_add]
      congr 1
      ring]
    ring
  rw [eulerPrimitiveBoundaryPolarizedPairing, hhead, htail]
  ring

theorem eulerPrimitiveBoundaryPolarizedPairing_test_score
    {a : ℂ} (ha : 0 < a.re) :
    eulerPrimitiveBoundaryPolarizedPairing
        (eulerPrimitiveBoundaryPolarizedTest a)
        eulerPrimitiveBoundaryPolarizedScore =
      2 * a / (1 + a) ^ 2 := by
  let c : ℂ := -(1 + a)
  have hc : c.re < 0 := by
    dsimp only [c]
    simp only [neg_re, add_re, one_re]
    linarith
  have hden : 0 < (1 + a).re := by
    simp only [add_re, one_re]
    linarith
  have h0 :
      IntegrableOn
        (fun t : ℝ => Complex.exp (c * (t : ℂ))) (Ioi 0) :=
    integrableOn_exp_mul_complex_Ioi hc 0
  have h1 :
      IntegrableOn
        (fun t : ℝ =>
          (t : ℂ) * Complex.exp (c * (t : ℂ))) (Ioi 0) :=
    integrableOn_eulerPrimitive_id_mul_cexp hc
  have hfun :
      (fun t : ℝ =>
        (eulerPrimitiveBoundaryHeadWeight t : ℂ) *
          (eulerPrimitiveBoundaryPolarizedTest a).1 t *
            star (eulerPrimitiveBoundaryPolarizedScore.1 t)) =
        fun t : ℝ =>
          2 * (Complex.exp (c * (t : ℂ)) -
            (t : ℂ) * Complex.exp (c * (t : ℂ))) := by
    funext t
    have hexp :
        (eulerPrimitiveBoundaryHeadWeight t : ℂ) *
            (eulerPrimitiveBoundaryPolarizedTest a).1 t =
          Complex.exp (c * (t : ℂ)) := by
      simp only [eulerPrimitiveBoundaryHeadWeight,
        eulerPrimitiveBoundaryPolarizedTest]
      rw [Complex.ofReal_exp, ← Complex.exp_add]
      congr 1
      dsimp only [c]
      push_cast
      ring
    rw [hexp]
    have hscorestar :
        star (2 * (1 - (t : ℂ))) =
          2 * (1 - (t : ℂ)) := by
      simp
    change
      Complex.exp (c * (t : ℂ)) *
          star (2 * (1 - (t : ℂ))) =
        2 * (Complex.exp (c * (t : ℂ)) -
          (t : ℂ) * Complex.exp (c * (t : ℂ)))
    rw [hscorestar]
    ring
  rw [eulerPrimitiveBoundaryPolarizedPairing, hfun]
  simp only [eulerPrimitiveBoundaryPolarizedScore,
    star_zero, mul_zero, integral_zero, add_zero]
  rw [integral_const_mul, integral_sub h0 h1]
  have hexpIntegral :
      (∫ t : ℝ in Ioi 0, Complex.exp (c * (t : ℂ))) =
        1 / (1 + a) := by
    simpa only [c, neg_mul] using
      (integral_cauchyFeaturePair hden)
  rw [hexpIntegral, integral_eulerPrimitive_id_mul_cexp hc]
  dsimp only [c]
  have hne : 1 + a ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [add_re, one_re, zero_re] at hre
    linarith
  field_simp [hne]
  ring

private theorem integral_eulerPrimitive_score_energy :
    (∫ t : ℝ in Ioi 0,
      4 * (1 - t) ^ 2 * Real.exp (-t)) = 4 := by
  have h0 := integrableOn_eulerPrimitive_pow_exp_neg 0
  have h1 := integrableOn_eulerPrimitive_pow_exp_neg 1
  have h2 := integrableOn_eulerPrimitive_pow_exp_neg 2
  have hpoly :
      (fun t : ℝ => 4 * (1 - t) ^ 2 * Real.exp (-t)) =
        fun t : ℝ =>
          4 * (t ^ 0 * Real.exp (-t)) -
            8 * (t ^ 1 * Real.exp (-t)) +
              4 * (t ^ 2 * Real.exp (-t)) := by
    funext t
    ring
  rw [hpoly]
  have hadd :
      (∫ t : ℝ in Ioi 0,
        4 * (t ^ 0 * Real.exp (-t)) -
          8 * (t ^ 1 * Real.exp (-t)) +
            4 * (t ^ 2 * Real.exp (-t))) =
        (∫ t : ℝ in Ioi 0,
          4 * (t ^ 0 * Real.exp (-t)) -
            8 * (t ^ 1 * Real.exp (-t))) +
          ∫ t : ℝ in Ioi 0,
            4 * (t ^ 2 * Real.exp (-t)) := by
    simpa only [Pi.add_apply, Pi.sub_apply] using
      integral_add
        ((h0.const_mul 4).sub (h1.const_mul 8))
        (h2.const_mul 4)
  have hsub :
      (∫ t : ℝ in Ioi 0,
        4 * (t ^ 0 * Real.exp (-t)) -
          8 * (t ^ 1 * Real.exp (-t))) =
        (∫ t : ℝ in Ioi 0,
          4 * (t ^ 0 * Real.exp (-t))) -
          ∫ t : ℝ in Ioi 0,
            8 * (t ^ 1 * Real.exp (-t)) := by
    simpa only [Pi.sub_apply] using
      integral_sub (h0.const_mul 4) (h1.const_mul 8)
  rw [hadd, hsub,
    integral_const_mul, integral_const_mul, integral_const_mul,
    integral_eulerPrimitive_pow_exp_neg 0,
    integral_eulerPrimitive_pow_exp_neg 1,
    integral_eulerPrimitive_pow_exp_neg 2]
  norm_num

theorem eulerPrimitiveBoundaryPolarizedPairing_score_score :
    eulerPrimitiveBoundaryPolarizedPairing
        eulerPrimitiveBoundaryPolarizedScore
        eulerPrimitiveBoundaryPolarizedScore = 4 := by
  rw [eulerPrimitiveBoundaryPolarizedPairing]
  simp [eulerPrimitiveBoundaryPolarizedScore]
  have hfun :
      (fun t : ℝ =>
        (eulerPrimitiveBoundaryHeadWeight t : ℂ) *
          (2 * (1 - (t : ℂ))) *
            (2 * (1 - (t : ℂ)))) =
        fun t : ℝ =>
          ((4 * (1 - t) ^ 2 * Real.exp (-t) : ℝ) : ℂ) := by
    funext t
    rw [eulerPrimitiveBoundaryHeadWeight]
    norm_cast
    ring_nf
  rw [hfun, integral_complex_ofReal,
    integral_eulerPrimitive_score_energy]
  norm_num

theorem eulerPrimitiveBoundaryPolarizedPairing_score_test
    {a : ℂ} (ha : 0 < a.re) :
    eulerPrimitiveBoundaryPolarizedPairing
        eulerPrimitiveBoundaryPolarizedScore
        (eulerPrimitiveBoundaryPolarizedTest a) =
      star (2 * a / (1 + a) ^ 2) := by
  have hstarpos : 0 < (star a).re := by
    simpa only [RCLike.star_def, conj_re] using ha
  have h :=
    eulerPrimitiveBoundaryPolarizedPairing_test_score hstarpos
  calc
    eulerPrimitiveBoundaryPolarizedPairing
        eulerPrimitiveBoundaryPolarizedScore
        (eulerPrimitiveBoundaryPolarizedTest a) =
      eulerPrimitiveBoundaryPolarizedPairing
        (eulerPrimitiveBoundaryPolarizedTest (star a))
        eulerPrimitiveBoundaryPolarizedScore := by
          unfold eulerPrimitiveBoundaryPolarizedPairing
          simp only [eulerPrimitiveBoundaryPolarizedScore,
            eulerPrimitiveBoundaryPolarizedTest, star_zero,
            mul_zero, zero_mul, integral_zero, add_zero]
          apply setIntegral_congr_fun measurableSet_Ioi
          intro t ht
          have hexpstar :
              star (Complex.exp (-a * (t : ℂ))) =
                Complex.exp (-(star a) * (t : ℂ)) := by
            change
              (starRingEnd ℂ)
                  (Complex.exp (-a * (t : ℂ))) =
                Complex.exp (-(star a) * (t : ℂ))
            rw [← Complex.exp_conj]
            congr 1
            simp
          have hscorestar :
              star (2 * (1 - (t : ℂ))) =
                2 * (1 - (t : ℂ)) := by
            simp
          change
            (eulerPrimitiveBoundaryHeadWeight t : ℂ) *
                  (2 * (1 - (t : ℂ))) *
                star (Complex.exp (-a * (t : ℂ))) =
              (eulerPrimitiveBoundaryHeadWeight t : ℂ) *
                  Complex.exp (-(star a) * (t : ℂ)) *
                star (2 * (1 - (t : ℂ)))
          rw [hexpstar, hscorestar]
          ring
    _ = 2 * star a / (1 + star a) ^ 2 := h
    _ = star (2 * a / (1 + a) ^ 2) := by simp

/-! ## Singular Hodge rotation -/

/-- Forced head/tail density ratio on the open source ray. -/
def eulerPrimitiveBoundaryHodgeScale (t : ℝ) : ℝ :=
  Real.sqrt (Real.exp t - 1)

/--
Pointwise singular Hodge rotation.  It is used only on `t > 0`, where its
denominator is nonzero.
-/
def eulerPrimitiveBoundaryOddHodge
    (x : EulerPrimitiveBoundaryPolarizedFeature) :
    EulerPrimitiveBoundaryPolarizedFeature :=
  (fun t =>
      (eulerPrimitiveBoundaryHodgeScale t : ℂ) * x.2 t,
    fun t =>
      -x.1 t / (eulerPrimitiveBoundaryHodgeScale t : ℂ))

theorem eulerPrimitiveBoundaryHodgeScale_pos
    {t : ℝ} (ht : 0 < t) :
    0 < eulerPrimitiveBoundaryHodgeScale t := by
  rw [eulerPrimitiveBoundaryHodgeScale, Real.sqrt_pos]
  exact sub_pos.mpr (Real.one_lt_exp_iff.mpr ht)

theorem eulerPrimitiveBoundaryOddHodge_sq
    (x : EulerPrimitiveBoundaryPolarizedFeature)
    {t : ℝ} (ht : 0 < t) :
    (eulerPrimitiveBoundaryOddHodge
        (eulerPrimitiveBoundaryOddHodge x)).1 t = -x.1 t ∧
      (eulerPrimitiveBoundaryOddHodge
        (eulerPrimitiveBoundaryOddHodge x)).2 t = -x.2 t := by
  have hq :
      (eulerPrimitiveBoundaryHodgeScale t : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr
      (eulerPrimitiveBoundaryHodgeScale_pos ht).ne'
  constructor <;>
    simp [eulerPrimitiveBoundaryOddHodge] <;>
    field_simp [hq]

theorem eulerPrimitiveBoundaryHodgeScale_sq
    {t : ℝ} (ht : 0 < t) :
    eulerPrimitiveBoundaryHodgeScale t ^ 2 =
      Real.exp t - 1 := by
  rw [eulerPrimitiveBoundaryHodgeScale, Real.sq_sqrt]
  exact sub_nonneg.mpr (Real.one_le_exp_iff.mpr ht.le)

/--
The singular Hodge rotation exchanges head and tail energy exactly.  This
is the local four-unit conservation law before integration or trace.
-/
theorem eulerPrimitiveBoundaryOddHodge_pointwise_energy
    (x : EulerPrimitiveBoundaryPolarizedFeature)
    {t : ℝ} (ht : 0 < t) :
    eulerPrimitiveBoundaryHeadWeight t *
          Complex.normSq ((eulerPrimitiveBoundaryOddHodge x).1 t) +
        eulerPrimitiveBoundaryTailWeight t *
          Complex.normSq ((eulerPrimitiveBoundaryOddHodge x).2 t) =
      eulerPrimitiveBoundaryTailWeight t * Complex.normSq (x.2 t) +
        eulerPrimitiveBoundaryHeadWeight t * Complex.normSq (x.1 t) := by
  have hqpos := eulerPrimitiveBoundaryHodgeScale_pos ht
  have hq : eulerPrimitiveBoundaryHodgeScale t ≠ 0 := hqpos.ne'
  have hqsq := eulerPrimitiveBoundaryHodgeScale_sq ht
  have hexp : Real.exp t ≠ 0 := (Real.exp_pos t).ne'
  have hsub : Real.exp t - 1 ≠ 0 :=
    (sub_pos.mpr (Real.one_lt_exp_iff.mpr ht)).ne'
  simp only [eulerPrimitiveBoundaryOddHodge,
    Complex.normSq_mul, Complex.normSq_ofReal,
    Complex.normSq_neg, Complex.normSq_div]
  have hqsq' :
      eulerPrimitiveBoundaryHodgeScale t *
          eulerPrimitiveBoundaryHodgeScale t =
        Real.exp t - 1 := by
    simpa [pow_two] using hqsq
  rw [hqsq']
  unfold eulerPrimitiveBoundaryHeadWeight
    eulerPrimitiveBoundaryTailWeight
  rw [show Real.exp (-t) = (Real.exp t)⁻¹ by
    rw [← Real.exp_neg, Real.exp_neg]]
  field_simp [hexp, hsub]

theorem eulerPrimitiveBoundaryOddHodge_score_pairing :
    eulerPrimitiveBoundaryPolarizedPairing
        (eulerPrimitiveBoundaryOddHodge
          eulerPrimitiveBoundaryPolarizedScore)
        (eulerPrimitiveBoundaryOddHodge
          eulerPrimitiveBoundaryPolarizedScore) = 4 := by
  have htail :
      (∫ t : ℝ in Ioi 0,
        (eulerPrimitiveBoundaryTailWeight t : ℂ) *
          (eulerPrimitiveBoundaryOddHodge
            eulerPrimitiveBoundaryPolarizedScore).2 t *
          star ((eulerPrimitiveBoundaryOddHodge
            eulerPrimitiveBoundaryPolarizedScore).2 t)) =
        ∫ t : ℝ in Ioi 0,
          (eulerPrimitiveBoundaryHeadWeight t : ℂ) *
            eulerPrimitiveBoundaryPolarizedScore.1 t *
            star (eulerPrimitiveBoundaryPolarizedScore.1 t) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have ht0 : 0 < t := mem_Ioi.mp ht
    have henergy :=
      eulerPrimitiveBoundaryOddHodge_pointwise_energy
        eulerPrimitiveBoundaryPolarizedScore ht0
    have henergy' :
        eulerPrimitiveBoundaryTailWeight t *
            Complex.normSq
              ((eulerPrimitiveBoundaryOddHodge
                eulerPrimitiveBoundaryPolarizedScore).2 t) =
          eulerPrimitiveBoundaryHeadWeight t *
            Complex.normSq
              (eulerPrimitiveBoundaryPolarizedScore.1 t) := by
      simpa [eulerPrimitiveBoundaryOddHodge,
        eulerPrimitiveBoundaryPolarizedScore] using henergy
    change
      (eulerPrimitiveBoundaryTailWeight t : ℂ) *
            (eulerPrimitiveBoundaryOddHodge
              eulerPrimitiveBoundaryPolarizedScore).2 t *
          star ((eulerPrimitiveBoundaryOddHodge
            eulerPrimitiveBoundaryPolarizedScore).2 t) =
        (eulerPrimitiveBoundaryHeadWeight t : ℂ) *
            eulerPrimitiveBoundaryPolarizedScore.1 t *
          star (eulerPrimitiveBoundaryPolarizedScore.1 t)
    rw [mul_assoc, mul_assoc]
    rw [show
        (eulerPrimitiveBoundaryOddHodge
              eulerPrimitiveBoundaryPolarizedScore).2 t *
            star ((eulerPrimitiveBoundaryOddHodge
              eulerPrimitiveBoundaryPolarizedScore).2 t) =
          (Complex.normSq
            ((eulerPrimitiveBoundaryOddHodge
              eulerPrimitiveBoundaryPolarizedScore).2 t) : ℂ) by
        exact Complex.mul_conj _,
      show
        eulerPrimitiveBoundaryPolarizedScore.1 t *
            star (eulerPrimitiveBoundaryPolarizedScore.1 t) =
          (Complex.normSq
            (eulerPrimitiveBoundaryPolarizedScore.1 t) : ℂ) by
        exact Complex.mul_conj _]
    exact_mod_cast henergy'
  calc
    eulerPrimitiveBoundaryPolarizedPairing
        (eulerPrimitiveBoundaryOddHodge
          eulerPrimitiveBoundaryPolarizedScore)
        (eulerPrimitiveBoundaryOddHodge
          eulerPrimitiveBoundaryPolarizedScore) =
      (∫ t : ℝ in Ioi 0,
        (eulerPrimitiveBoundaryTailWeight t : ℂ) *
          (eulerPrimitiveBoundaryOddHodge
            eulerPrimitiveBoundaryPolarizedScore).2 t *
          star ((eulerPrimitiveBoundaryOddHodge
            eulerPrimitiveBoundaryPolarizedScore).2 t)) := by
              rw [eulerPrimitiveBoundaryPolarizedPairing]
              simp [eulerPrimitiveBoundaryOddHodge,
                eulerPrimitiveBoundaryPolarizedScore]
    _ = (∫ t : ℝ in Ioi 0,
          (eulerPrimitiveBoundaryHeadWeight t : ℂ) *
            eulerPrimitiveBoundaryPolarizedScore.1 t *
            star (eulerPrimitiveBoundaryPolarizedScore.1 t)) :=
      htail
    _ = eulerPrimitiveBoundaryPolarizedPairing
        eulerPrimitiveBoundaryPolarizedScore
        eulerPrimitiveBoundaryPolarizedScore := by
          rw [eulerPrimitiveBoundaryPolarizedPairing]
          simp [eulerPrimitiveBoundaryPolarizedScore]
    _ = 4 := eulerPrimitiveBoundaryPolarizedPairing_score_score

/-! ## Existing four-unit matrix is the Gram of the polarized source -/

/-- Finite packet of common tests together with distinguished source score. -/
def eulerPrimitiveBoundaryPolarizedAugmentedFeature
    {N : ℕ} (a : Fin N → ℂ) :
    Fin N ⊕ Unit → EulerPrimitiveBoundaryPolarizedFeature
  | Sum.inl i => eulerPrimitiveBoundaryPolarizedTest (a i)
  | Sum.inr _ => eulerPrimitiveBoundaryPolarizedScore

/-- Gram observed directly on the two-channel source carrier. -/
def eulerPrimitiveBoundaryPolarizedSourceGram
    {N : ℕ} (a : Fin N → ℂ) :
    Matrix (Fin N ⊕ Unit) (Fin N ⊕ Unit) ℂ :=
  fun i j =>
    eulerPrimitiveBoundaryPolarizedPairing
      (eulerPrimitiveBoundaryPolarizedAugmentedFeature a i)
      (eulerPrimitiveBoundaryPolarizedAugmentedFeature a j)

/--
The source-side unshifted four-unit matrix is literally the Gram of the
polarized half-line chain.  This identifies all four blocks, including the
source norm `4`; no matrix completion is inserted.
-/
theorem eulerPrimitiveBoundaryPolarizedSourceGram_eq
    {N : ℕ} (a : Fin N → ℂ) (ha : ∀ i, 0 < (a i).re) :
    eulerPrimitiveBoundaryPolarizedSourceGram a =
      eulerPrimitiveBoundaryFullHardyFisherGram a := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · exact
      eulerPrimitiveBoundaryPolarizedPairing_test_test
        (ha i) (ha j)
  · rcases j with ⟨⟩
    simpa [eulerPrimitiveBoundaryPolarizedSourceGram,
      eulerPrimitiveBoundaryPolarizedAugmentedFeature,
      eulerPrimitiveBoundaryFullHardyFisherGram,
      eulerPrimitiveBoundaryFisherColumn] using
        (eulerPrimitiveBoundaryPolarizedPairing_test_score
          (ha i))
  · rcases i with ⟨⟩
    simpa [eulerPrimitiveBoundaryPolarizedSourceGram,
      eulerPrimitiveBoundaryPolarizedAugmentedFeature,
      eulerPrimitiveBoundaryFullHardyFisherGram,
      eulerPrimitiveBoundaryFisherColumn] using
        (eulerPrimitiveBoundaryPolarizedPairing_score_test
          (ha j))
  · rcases i with ⟨⟩
    rcases j with ⟨⟩
    simpa [eulerPrimitiveBoundaryPolarizedSourceGram,
      eulerPrimitiveBoundaryPolarizedAugmentedFeature,
      eulerPrimitiveBoundaryFullHardyFisherGram] using
        eulerPrimitiveBoundaryPolarizedPairing_score_score

/--
Unconditional source positivity now belongs to the explicit polarized
chain carrier.  The matrix theorem is a corollary of that identification.
-/
theorem eulerPrimitiveBoundaryPolarizedSourceGram_posSemidef
    {N : ℕ} (a : Fin N → ℂ) (ha : ∀ i, 0 < (a i).re) :
    (eulerPrimitiveBoundaryPolarizedSourceGram a).PosSemidef := by
  rw [eulerPrimitiveBoundaryPolarizedSourceGram_eq a ha]
  exact eulerPrimitiveBoundaryFullHardyFisherGram_posSemidef a ha

end

end RHTower
