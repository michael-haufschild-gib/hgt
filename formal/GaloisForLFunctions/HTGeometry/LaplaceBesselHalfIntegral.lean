import Mathlib

/-!
# The Cauchy–Schlömilch substitution and the `K_{1/2}` Laplace–Bessel integral

The map `y ↦ py − q/y` (`p, q > 0`) is an increasing bijection of `(0, ∞)` onto `ℝ` with Jacobian
`p + q/y²`, so `∫_{y>0}(p + q/y²)e^{−(py−q/y)²}dy = √π`. The reflection `y ↦ q/(py)` exchanges the
two halves of the Jacobian, which gives the Cauchy–Schlömilch identity
`∫_{y>0} e^{−(py−q/y)²} dy = √π/(2p)` (`integral_exp_neg_schlomilch_sq`).

Completing the square and substituting `x = y²` gives the half-integer Bessel identity
(`integral_rpow_neg_half_mul_exp_neg_div_sub_mul`):

`∫_0^∞ x^{−1/2} e^{−a/x − bx} dx = √(π/b) e^{−2√(ab)}`   (`a, b > 0`).

This is the Laplace step in Hamburger's characterization of `ζ` by its functional equation: it
turns the dual theta series `Σ b_n e^{−πn²/x}` into the exponential series `Σ b_n e^{−2πnt}/t`.
-/

open MeasureTheory Set Real

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- The Cauchy–Schlömilch map `y ↦ p y − q/y`. -/
def schlomilchMap (p q : ℝ) (y : ℝ) : ℝ := p * y - q / y

theorem hasDerivWithinAt_schlomilchMap (p q : ℝ) {y : ℝ} (hy : y ∈ Ioi (0 : ℝ)) :
    HasDerivWithinAt (schlomilchMap p q) (p + q / y ^ 2) (Ioi 0) y := by
  have hy0 : y ≠ 0 := ne_of_gt hy
  have h1 : HasDerivAt (fun y : ℝ => p * y) p y := by simpa using (hasDerivAt_id y).const_mul p
  have h2 : HasDerivAt (fun y : ℝ => q * y⁻¹) (q * -(y ^ 2)⁻¹) y := (hasDerivAt_inv hy0).const_mul q
  have h3 := h1.sub h2
  have hfun : schlomilchMap p q = fun y : ℝ => p * y - q * y⁻¹ := by
    funext z; simp [schlomilchMap, div_eq_mul_inv]
  rw [hfun]
  have hval : p - q * -(y ^ 2)⁻¹ = p + q / y ^ 2 := by rw [div_eq_mul_inv]; ring
  rw [← hval]
  exact h3.hasDerivWithinAt

theorem schlomilchMap_strictMonoOn {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    StrictMonoOn (schlomilchMap p q) (Ioi 0) := by
  intro x hx y hy hxy
  simp only [schlomilchMap]
  have hx0 : 0 < x := hx
  have hy0 : 0 < y := hy
  have h1 : p * x < p * y := mul_lt_mul_of_pos_left hxy hp
  have h2 : q / y < q / x := div_lt_div_of_pos_left hq hx0 hxy
  linarith

theorem schlomilchMap_image {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    schlomilchMap p q '' Ioi 0 = univ := by
  refine eq_univ_of_forall fun v => ?_
  set r := (v + Real.sqrt (v ^ 2 + 4 * p * q)) / (2 * p) with hr
  have hdisc : 0 ≤ v ^ 2 + 4 * p * q := by positivity
  have hsq := Real.sq_sqrt hdisc
  have hsqrt_gt : |v| < Real.sqrt (v ^ 2 + 4 * p * q) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_lt_sqrt (sq_nonneg v) (by nlinarith [mul_pos hp hq])
  have hrpos : 0 < r := by
    rw [hr]
    apply div_pos _ (by linarith)
    have := neg_abs_le v
    linarith
  refine ⟨r, hrpos, ?_⟩
  have hr0 : r ≠ 0 := ne_of_gt hrpos
  have h2p : 2 * p * r = v + Real.sqrt (v ^ 2 + 4 * p * q) := by
    rw [hr]; field_simp
  have hroot : p * r ^ 2 - v * r - q = 0 := by
    have hs : Real.sqrt (v ^ 2 + 4 * p * q) = 2 * p * r - v := by linarith
    have : (2 * p * r - v) ^ 2 = v ^ 2 + 4 * p * q := by rw [← hs]; exact hsq
    have hp4 : 4 * p * (p * r ^ 2 - v * r - q) = 0 := by nlinarith [this]
    have hp4' : (4 * p) ≠ 0 := by positivity
    have := mul_eq_zero.mp hp4
    rcases this with h | h
    · exact absurd h hp4'
    · exact h
  simp only [schlomilchMap]
  have hqr : q / r = p * r - v := by
    rw [div_eq_iff hr0]
    nlinarith [hroot]
  rw [hqr]
  ring

/-- `∫_{y>0} (p + q/y²) e^{−(py − q/y)²} dy = √π`. -/
theorem integral_schlomilch_jacobian {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    ∫ y in Ioi (0 : ℝ), (p + q / y ^ 2) * Real.exp (-(schlomilchMap p q y) ^ 2) = √π := by
  have hcv := integral_image_eq_integral_abs_deriv_smul (measurableSet_Ioi)
    (fun y hy => hasDerivWithinAt_schlomilchMap p q hy)
    (schlomilchMap_strictMonoOn hp hq).injOn (fun v : ℝ => Real.exp (-v ^ 2))
  rw [schlomilchMap_image hp hq, Measure.restrict_univ] at hcv
  have hg : ∫ v : ℝ, Real.exp (-v ^ 2) = √π := by
    have := integral_gaussian 1
    simpa using this
  rw [hg] at hcv
  rw [hcv]
  refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
  have hpos : 0 < p + q / y ^ 2 := by
    have : 0 < q / y ^ 2 := div_pos hq (pow_pos hy 2)
    linarith
  simp [abs_of_pos hpos, smul_eq_mul]

theorem integrableOn_schlomilch_jacobian {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    IntegrableOn (fun y => (p + q / y ^ 2) * Real.exp (-(schlomilchMap p q y) ^ 2)) (Ioi 0) := by
  have hiff := integrableOn_image_iff_integrableOn_abs_deriv_smul (measurableSet_Ioi)
    (fun y hy => hasDerivWithinAt_schlomilchMap p q hy)
    (schlomilchMap_strictMonoOn hp hq).injOn (fun v : ℝ => Real.exp (-v ^ 2))
  rw [schlomilchMap_image hp hq] at hiff
  have hint : IntegrableOn (fun v : ℝ => Real.exp (-v ^ 2)) univ := by
    rw [integrableOn_univ]
    have := integrable_exp_neg_mul_sq (b := 1) one_pos
    simpa using this
  have h := hiff.mp hint
  refine h.congr_fun (fun y hy => ?_) measurableSet_Ioi
  have hpos : 0 < p + q / y ^ 2 := by
    have : 0 < q / y ^ 2 := div_pos hq (pow_pos hy 2)
    linarith
  simp [abs_of_pos hpos, smul_eq_mul]

theorem schlomilchMap_reflect {p q z : ℝ} (hp : 0 < p) (hq : 0 < q) (hz : 0 < z) :
    schlomilchMap p q (q / (p * z)) = -schlomilchMap p q z := by
  have hq0 : q ≠ 0 := ne_of_gt hq
  simp only [schlomilchMap]
  have hp0 : p ≠ 0 := ne_of_gt hp
  have hz0 : z ≠ 0 := ne_of_gt hz
  field_simp
  ring

/-- The reflection `y ↦ q/(py)` exchanges the two halves of the Jacobian:
`∫ (q/y²) e^{−S²} = ∫ p e^{−S²}` over `y > 0`. -/
theorem integral_q_div_sq_eq_integral_p {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    ∫ y in Ioi (0 : ℝ), q / y ^ 2 * Real.exp (-(schlomilchMap p q y) ^ 2) =
      ∫ y in Ioi (0 : ℝ), p * Real.exp (-(schlomilchMap p q y) ^ 2) := by
  set g : ℝ → ℝ := fun z => q / (p * z) with hg
  have hderiv : ∀ z ∈ Ioi (0 : ℝ), HasDerivWithinAt g (-(q / (p * z ^ 2))) (Ioi 0) z := by
    intro z hz
    have hz0 : z ≠ 0 := ne_of_gt hz
    have hp0 : p ≠ 0 := ne_of_gt hp
    have h := ((hasDerivAt_inv hz0).const_mul (q / p)).hasDerivWithinAt (s := Ioi 0)
    have hfun : g = fun z => q / p * z⁻¹ := by
      funext w
      simp only [hg, div_eq_mul_inv, mul_inv]
      ring
    have hval : q / p * -(z ^ 2)⁻¹ = -(q / (p * z ^ 2)) := by
      simp only [div_eq_mul_inv, mul_inv]
      ring
    rw [hfun, ← hval]
    exact h
  have hanti : StrictAntiOn g (Ioi 0) := by
    intro x hx y hy hxy
    simp only [hg]
    exact div_lt_div_of_pos_left hq (mul_pos hp hx) (mul_lt_mul_of_pos_left hxy hp)
  have hinj : InjOn g (Ioi 0) := hanti.injOn
  have himg : g '' Ioi 0 = Ioi 0 := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact div_pos hq (mul_pos hp hz)
    · intro hy
      refine ⟨q / (p * y), div_pos hq (mul_pos hp hy), ?_⟩
      simp only [hg]
      have hy0 : y ≠ 0 := ne_of_gt hy
      have hp0 : p ≠ 0 := ne_of_gt hp
      have hq0 : q ≠ 0 := ne_of_gt hq
      field_simp
  have hcv := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv hinj
    (fun y => p * Real.exp (-(schlomilchMap p q y) ^ 2))
  rw [himg] at hcv
  rw [hcv]
  refine setIntegral_congr_fun measurableSet_Ioi fun z hz => ?_
  have hpos : 0 < q / (p * z ^ 2) := div_pos hq (mul_pos hp (pow_pos hz 2))
  simp only [smul_eq_mul, hg]
  rw [abs_neg, abs_of_pos hpos, schlomilchMap_reflect hp hq hz, neg_sq]
  have hp0 : p ≠ 0 := ne_of_gt hp
  have hz0 : z ≠ 0 := ne_of_gt hz
  field_simp

/-- **Cauchy–Schlömilch.**  `∫_{y>0} e^{−(py − q/y)²} dy = √π/(2p)` for `p, q > 0`. -/
theorem integral_exp_neg_schlomilch_sq {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    ∫ y in Ioi (0 : ℝ), Real.exp (-(schlomilchMap p q y) ^ 2) = √π / (2 * p) := by
  set E : ℝ → ℝ := fun y => Real.exp (-(schlomilchMap p q y) ^ 2) with hE
  have hint := integrableOn_schlomilch_jacobian hp hq
  have hmeasE : AEStronglyMeasurable E (volume.restrict (Ioi (0 : ℝ))) := by
    have hcont : ContinuousOn E (Ioi 0) := by
      have hin : ContinuousOn (fun y : ℝ => -(schlomilchMap p q y) ^ 2) (Ioi 0) := by
        simp only [schlomilchMap]
        exact (((continuousOn_const.mul continuousOn_id).sub
          (continuousOn_const.div continuousOn_id fun y hy => ne_of_gt hy)).pow 2).neg
      exact Real.continuous_exp.comp_continuousOn hin
    exact hcont.aestronglyMeasurable measurableSet_Ioi
  have hA : IntegrableOn (fun y => p * E y) (Ioi 0) := by
    refine Integrable.mono' hint (hmeasE.const_mul p) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun y hy => ?_)
    have hy2 : 0 ≤ q / y ^ 2 := div_nonneg hq.le (sq_nonneg y)
    have hEpos : 0 ≤ E y := (Real.exp_pos _).le
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hp.le hEpos)]
    nlinarith
  have hB : IntegrableOn (fun y => q / y ^ 2 * E y) (Ioi 0) := by
    refine Integrable.mono' hint ?_ ?_
    · have hcont : ContinuousOn (fun y : ℝ => q / y ^ 2) (Ioi 0) := by
        intro y hy
        exact (continuousAt_const.div (continuousAt_id.pow 2)
          (pow_ne_zero 2 (ne_of_gt hy))).continuousWithinAt
      exact (hcont.aestronglyMeasurable measurableSet_Ioi).mul hmeasE
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun y hy => ?_)
      have hy2 : 0 ≤ q / y ^ 2 := div_nonneg hq.le (sq_nonneg y)
      have hEpos : 0 ≤ E y := (Real.exp_pos _).le
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hy2 hEpos)]
      nlinarith
  have htot := integral_schlomilch_jacobian hp hq
  have hsplit : ∫ y in Ioi (0 : ℝ), (p + q / y ^ 2) * E y =
      (∫ y in Ioi (0 : ℝ), p * E y) + ∫ y in Ioi (0 : ℝ), q / y ^ 2 * E y := by
    rw [← integral_add hA hB]
    refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
    ring
  have hrefl := integral_q_div_sq_eq_integral_p hp hq
  have hmain : 2 * ∫ y in Ioi (0 : ℝ), p * E y = √π := by
    rw [← htot]
    change _ = ∫ y in Ioi (0 : ℝ), (p + q / y ^ 2) * E y
    rw [hsplit]
    rw [show (∫ y in Ioi (0 : ℝ), q / y ^ 2 * E y) = ∫ y in Ioi (0 : ℝ), p * E y from hrefl]
    ring
  have hpE : ∫ y in Ioi (0 : ℝ), p * E y = p * ∫ y in Ioi (0 : ℝ), E y := integral_const_mul p _
  rw [hpE] at hmain
  have hp0 : p ≠ 0 := ne_of_gt hp
  field_simp
  linarith

/-- `∫_{y>0} e^{−by² − a/y²} dy = (√π/(2√b)) e^{−2√(ab)}` for `a, b > 0`. -/
theorem integral_exp_neg_mul_sq_sub_div_sq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ y in Ioi (0 : ℝ), Real.exp (-(b * y ^ 2) - a / y ^ 2) =
      Real.exp (-(2 * √(a * b))) * (√π / (2 * √b)) := by
  have hsb : 0 < √b := Real.sqrt_pos.mpr hb
  have hsa : 0 < √a := Real.sqrt_pos.mpr ha
  rw [← integral_exp_neg_schlomilch_sq hsb hsa, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
  have hy0 : y ≠ 0 := ne_of_gt hy
  simp only [schlomilchMap]
  rw [← Real.exp_add]
  congr 1
  have h1 : √b ^ 2 = b := Real.sq_sqrt hb.le
  have h2 : √a ^ 2 = a := Real.sq_sqrt ha.le
  have h3 : √(a * b) = √a * √b := Real.sqrt_mul ha.le b
  rw [h3]
  field_simp
  ring_nf
  rw [h1, h2]
  ring

/-- **The Laplace–Bessel integral.**  For `a, b > 0`,
`∫_0^∞ x^{−1/2} e^{−a/x − bx} dx = √(π/b) · e^{−2√(ab)}`. This is the `K_{1/2}` Bessel identity, used
in the Laplace step of Hamburger's theorem. -/
theorem integral_rpow_neg_half_mul_exp_neg_div_sub_mul {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ x in Ioi (0 : ℝ), x ^ (-(1 / 2 : ℝ)) * Real.exp (-(a / x) - b * x) =
      √(π / b) * Real.exp (-(2 * √(a * b))) := by
  have hsub := integral_comp_rpow_Ioi
    (fun x : ℝ => x ^ (-(1 / 2 : ℝ)) * Real.exp (-(a / x) - b * x)) (p := 2) (by norm_num)
  rw [← hsub]
  have hstep : ∫ x in Ioi (0 : ℝ), (|(2 : ℝ)| * x ^ ((2 : ℝ) - 1)) •
      ((x ^ (2 : ℝ)) ^ (-(1 / 2 : ℝ)) * Real.exp (-(a / x ^ (2 : ℝ)) - b * x ^ (2 : ℝ))) =
      ∫ x in Ioi (0 : ℝ), 2 * Real.exp (-(b * x ^ 2) - a / x ^ 2) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hx0 : 0 < x := hx
    have hx2 : x ^ (2 : ℝ) = x ^ 2 := by norm_cast
    have hpow : (x ^ (2 : ℝ)) ^ (-(1 / 2 : ℝ)) = x⁻¹ := by
      rw [← Real.rpow_mul hx0.le]
      norm_num
      exact Real.rpow_neg_one x
    have hx1 : x ^ ((2 : ℝ) - 1) = x := by norm_num
    rw [smul_eq_mul, hpow, hx1, hx2, abs_two]
    have hxne : x ≠ 0 := ne_of_gt hx0
    field_simp
    ring_nf
  rw [hstep, integral_const_mul, integral_exp_neg_mul_sq_sub_div_sq ha hb]
  have hsb : 0 < √b := Real.sqrt_pos.mpr hb
  rw [Real.sqrt_div' π hb.le]
  field_simp

end GaloisForLFunctions.HTGeometry
