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

open Complex MeasureTheory Set

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

end

end RHTower
