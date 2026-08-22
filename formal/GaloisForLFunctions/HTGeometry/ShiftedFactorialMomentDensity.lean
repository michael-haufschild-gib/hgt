import GaloisForLFunctions.HTGeometry.SqrtExponentialMoments
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# The shifted factorial representing density

The shifted factorial moment sequence `(2n+1)! S_{n+1}` of a compactly supported measure `ν` is
represented by an explicit Lebesgue density on the half line,

`ρ(x) = (∫_{y>0} exp (-√(x/y)) dν(y)) / 2`,

obtained by superposing the scaled base densities `e^{-√(x/y)}/2`, whose `n`-th moments are
`y^{n+1}·2·(2n+1)!`.  Fubini turns the superposition into the moment identity.

`RHTower/SuzukiStieltjesMoments.lean` carries the general-scale integrability
`t^n e^{-c√t}`; the unit-scale statement is reproved here to keep this file off the Suzuki stack.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Set

noncomputable section

theorem integrableOn_pow_mul_expNegSqrt (n : ℕ) :
    IntegrableOn (fun a : ℝ => a ^ n * Real.exp (-Real.sqrt a)) (Ioi 0) volume := by
  have hderiv : ∀ x ∈ Set.Ioi (0:ℝ), HasDerivWithinAt (fun t : ℝ => t ^ 2) (2 * x)
      (Set.Ioi 0) x := by
    intro x _
    have h : HasDerivAt (fun t : ℝ => t ^ 2) (2 * x ^ 1) x := by simpa using hasDerivAt_pow 2 x
    simpa using h.hasDerivWithinAt
  have hiff := MeasureTheory.integrableOn_image_iff_integrableOn_abs_deriv_smul
    (s := Ioi (0:ℝ)) (f := fun t : ℝ => t ^ 2) (f' := fun t : ℝ => 2 * t)
    measurableSet_Ioi hderiv injOn_sq_Ioi_zero
    (fun a : ℝ => a ^ n * Real.exp (-Real.sqrt a))
  rw [image_sq_Ioi_zero] at hiff
  rw [hiff]
  have hgam := Real.GammaIntegral_convergent (s := ((2 * n + 2 : ℕ) : ℝ)) (by positivity)
  have hconst : IntegrableOn
      (fun t : ℝ => 2 * (Real.exp (-t) * t ^ (((2 * n + 2 : ℕ) : ℝ) - 1))) (Ioi 0) volume :=
    hgam.const_mul 2
  refine hconst.congr_fun (fun t ht => ?_) measurableSet_Ioi
  have ht' : (0:ℝ) < t := ht
  show 2 * (Real.exp (-t) * t ^ (((2 * n + 2 : ℕ) : ℝ) - 1))
      = |2 * t| • ((t ^ 2) ^ n * Real.exp (-Real.sqrt (t ^ 2)))
  rw [Real.sqrt_sq ht'.le, abs_of_pos (by linarith : (0:ℝ) < 2 * t), smul_eq_mul, ← pow_mul,
    show ((2 * n + 2 : ℕ) : ℝ) - 1 = ((2 * n + 1 : ℕ) : ℝ) by push_cast; ring]
  rw [Real.rpow_natCast t (2 * n + 1)]
  ring

/-- The scaled square-root exponential kernel. -/
def sqrtExpDensity (y x : ℝ) : ℝ := Real.exp (-Real.sqrt (x / y))

theorem integrableOn_pow_mul_sqrtExpDensity {y : ℝ} (hy : 0 < y) (n : ℕ) :
    IntegrableOn (fun x : ℝ => x ^ n * sqrtExpDensity y x) (Ioi 0) volume := by
  have hiff := MeasureTheory.integrableOn_Ioi_comp_mul_left_iff
    (fun x : ℝ => x ^ n * sqrtExpDensity y x) 0 hy
  rw [mul_zero] at hiff
  refine hiff.1 ?_
  have hb : IntegrableOn (fun a : ℝ => y ^ n * (a ^ n * Real.exp (-Real.sqrt a)))
      (Ioi 0) volume := (integrableOn_pow_mul_expNegSqrt n).const_mul (y ^ n)
  refine hb.congr_fun (fun a ha => ?_) measurableSet_Ioi
  have ha' : (0:ℝ) < a := ha
  show y ^ n * (a ^ n * Real.exp (-Real.sqrt a))
      = (y * a) ^ n * sqrtExpDensity y (y * a)
  rw [sqrtExpDensity, mul_div_cancel_left₀ a (ne_of_gt hy), mul_pow]
  ring

theorem integral_pow_mul_sqrtExpDensity {y : ℝ} (hy : 0 < y) (n : ℕ) :
    (∫ x in Ioi (0:ℝ), x ^ n * sqrtExpDensity y x)
      = y ^ (n + 1) * (2 * (Nat.factorial (2 * n + 1) : ℝ)) := by
  have hsub := MeasureTheory.integral_comp_mul_left_Ioi
    (fun x : ℝ => x ^ n * sqrtExpDensity y x) 0 hy
  rw [mul_zero] at hsub
  have hpoint : ∀ a ∈ Ioi (0:ℝ),
      (y * a) ^ n * sqrtExpDensity y (y * a) = y ^ n * (a ^ n * Real.exp (-Real.sqrt a)) := by
    intro a ha
    rw [sqrtExpDensity, mul_div_cancel_left₀ a (ne_of_gt hy), mul_pow]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpoint] at hsub
  rw [MeasureTheory.integral_const_mul, integral_pow_mul_exp_neg_sqrt n] at hsub
  have hyne : (y : ℝ) ≠ 0 := ne_of_gt hy
  rw [smul_eq_mul] at hsub
  field_simp at hsub ⊢
  rw [← hsub]
  ring

/-! ### The representing density -/

/-- The density of the shifted factorial representing measure. -/
def factorialMomentDensity (nu : Measure ℝ) (x : ℝ) : ℝ :=
  (∫ y, sqrtExpDensity y x ∂(nu.restrict (Ioi 0))) / 2

theorem sqrtExpDensity_nonneg (y x : ℝ) : 0 ≤ sqrtExpDensity y x := Real.exp_nonneg _

theorem sqrtExpDensity_le_one (y x : ℝ) : sqrtExpDensity y x ≤ 1 := by
  rw [sqrtExpDensity]
  refine Real.exp_le_one_iff.2 ?_
  simp only [neg_nonpos]
  exact Real.sqrt_nonneg _

theorem measurable_uncurry_sqrtExpDensity :
    Measurable (Function.uncurry fun (y x : ℝ) => sqrtExpDensity y x) := by
  unfold Function.uncurry sqrtExpDensity
  fun_prop

theorem factorialMomentDensity_nonneg (nu : Measure ℝ) (x : ℝ) :
    0 ≤ factorialMomentDensity nu x := by
  refine div_nonneg ?_ (by norm_num)
  exact integral_nonneg fun y => sqrtExpDensity_nonneg y x

theorem integrable_uncurry_pow_mul_sqrtExpDensity {nu : Measure ℝ} [IsFiniteMeasure nu]
    {R : ℝ} (hsupp : ∀ᵐ y ∂nu, y ∈ Icc 0 R) (n : ℕ) :
    Integrable (Function.uncurry fun (y x : ℝ) => x ^ n * sqrtExpDensity y x)
      ((nu.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
  have hmeas : AEStronglyMeasurable
      (Function.uncurry fun (y x : ℝ) => x ^ n * sqrtExpDensity y x)
      ((nu.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
    refine Measurable.aestronglyMeasurable ?_
    have h1 : Measurable fun p : ℝ × ℝ => p.2 ^ n := (measurable_snd).pow_const n
    exact h1.mul measurable_uncurry_sqrtExpDensity
  rw [MeasureTheory.integrable_prod_iff hmeas]
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact integrableOn_pow_mul_sqrtExpDensity hy n
  · have hval : ∀ y ∈ Ioi (0:ℝ),
        (∫ x in Ioi (0:ℝ), ‖(Function.uncurry fun (y x : ℝ) => x ^ n * sqrtExpDensity y x) (y, x)‖)
          = y ^ (n + 1) * (2 * (Nat.factorial (2 * n + 1) : ℝ)) := by
      intro y hy
      have hy' : (0:ℝ) < y := hy
      rw [← integral_pow_mul_sqrtExpDensity hy' n]
      refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
      have hx' : (0:ℝ) < x := hx
      show ‖x ^ n * sqrtExpDensity y x‖ = x ^ n * sqrtExpDensity y x
      rw [Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (by positivity) (sqrtExpDensity_nonneg y x))]
    have hbdd : IntegrableOn
        (fun y : ℝ => y ^ (n + 1) * (2 * (Nat.factorial (2 * n + 1) : ℝ))) (Ioi 0) nu := by
      refine Integrable.mono' (g := fun y : ℝ => |R| ^ (n+1) * (2 * (Nat.factorial (2*n+1) : ℝ)))
        (integrable_const _) ?_ ?_
      · exact ((measurable_id.pow_const (n+1)).mul_const _).aestronglyMeasurable
      · filter_upwards [ae_restrict_of_ae hsupp, ae_restrict_mem measurableSet_Ioi] with y hy hy0
        have hy' : (0:ℝ) < y := hy0
        have hyR : y ≤ R := hy.2
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        calc y ^ (n+1) ≤ R ^ (n+1) := pow_le_pow_left₀ hy'.le hyR _
          _ ≤ |R| ^ (n+1) := pow_le_pow_left₀ (by linarith) (le_abs_self R) _
    refine hbdd.congr_fun (fun y hy => ?_) measurableSet_Ioi
    exact (hval y hy).symm

theorem integrableOn_pow_mul_factorialMomentDensity {nu : Measure ℝ} [IsFiniteMeasure nu]
    {R : ℝ} (hsupp : ∀ᵐ y ∂nu, y ∈ Icc 0 R) (n : ℕ) :
    IntegrableOn (fun x : ℝ => x ^ n * factorialMomentDensity nu x) (Ioi 0) volume := by
  have hprod := integrable_uncurry_pow_mul_sqrtExpDensity hsupp n
  have hright : IntegrableOn
      (fun x : ℝ => ∫ t in Ioi (0:ℝ), x ^ n * sqrtExpDensity t x ∂nu) (Ioi 0) volume :=
    MeasureTheory.Integrable.integral_prod_right hprod
  have h2 : IntegrableOn
      (fun x : ℝ => (1/2 : ℝ) * (∫ t in Ioi (0:ℝ), x ^ n * sqrtExpDensity t x ∂nu))
      (Ioi 0) volume := hright.const_mul _
  refine h2.congr_fun (fun x hx => ?_) measurableSet_Ioi
  show (1/2 : ℝ) * (∫ t in Ioi (0:ℝ), x ^ n * sqrtExpDensity t x ∂nu)
      = x ^ n * factorialMomentDensity nu x
  rw [factorialMomentDensity, MeasureTheory.integral_const_mul]
  ring

theorem integral_pow_mul_factorialMomentDensity {nu : Measure ℝ} [IsFiniteMeasure nu]
    {R : ℝ} (hsupp : ∀ᵐ y ∂nu, y ∈ Icc 0 R) (n : ℕ) :
    (∫ x in Ioi (0:ℝ), x ^ n * factorialMomentDensity nu x)
      = (Nat.factorial (2 * n + 1) : ℝ) * ∫ y in Ioi (0:ℝ), y ^ (n + 1) ∂nu := by
  have hprod := integrable_uncurry_pow_mul_sqrtExpDensity hsupp n
  have hswap := MeasureTheory.integral_integral_swap hprod
  have hLHS : (∫ t in Ioi (0:ℝ), (∫ x in Ioi (0:ℝ), x ^ n * sqrtExpDensity t x) ∂nu)
      = (2 * (Nat.factorial (2 * n + 1) : ℝ)) * ∫ y in Ioi (0:ℝ), y ^ (n + 1) ∂nu := by
    rw [← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht' : (0:ℝ) < t := ht
    rw [integral_pow_mul_sqrtExpDensity ht' n]
    ring
  have hRHS : (∫ x in Ioi (0:ℝ), (∫ t in Ioi (0:ℝ), x ^ n * sqrtExpDensity t x ∂nu))
      = 2 * ∫ x in Ioi (0:ℝ), x ^ n * factorialMomentDensity nu x := by
    rw [← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    rw [factorialMomentDensity, MeasureTheory.integral_const_mul]
    ring
  rw [hLHS, hRHS] at hswap
  linarith [hswap]

/-! ### The representing measure -/

theorem measurable_factorialMomentDensity (nu : Measure ℝ) [SFinite nu] :
    Measurable (factorialMomentDensity nu) := by
  unfold factorialMomentDensity
  refine Measurable.div_const ?_ 2
  exact (StronglyMeasurable.integral_prod_right'
    (f := fun p : ℝ × ℝ => sqrtExpDensity p.2 p.1)
    (by
      have : Measurable fun p : ℝ × ℝ => sqrtExpDensity p.2 p.1 := by
        unfold sqrtExpDensity
        fun_prop
      exact this.stronglyMeasurable)).measurable

/-- The shifted factorial representing measure. -/
def factorialMomentMeasure (nu : Measure ℝ) : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity fun x => ENNReal.ofReal (factorialMomentDensity nu x)

theorem integral_factorialMomentMeasure {nu : Measure ℝ} [IsFiniteMeasure nu] (g : ℝ → ℝ) :
    (∫ x, g x ∂(factorialMomentMeasure nu))
      = ∫ x in Ioi (0:ℝ), factorialMomentDensity nu x * g x := by
  rw [factorialMomentMeasure,
    integral_withDensity_eq_integral_toReal_smul
      ((measurable_factorialMomentDensity nu).ennreal_ofReal)
      (by filter_upwards with x using ENNReal.ofReal_lt_top) g]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  rw [smul_eq_mul, ENNReal.toReal_ofReal (factorialMomentDensity_nonneg nu x)]

theorem integrableOn_factorialMomentDensity {nu : Measure ℝ} [IsFiniteMeasure nu]
    {R : ℝ} (hsupp : ∀ᵐ y ∂nu, y ∈ Icc 0 R) :
    IntegrableOn (factorialMomentDensity nu) (Ioi 0) volume := by
  have h := integrableOn_pow_mul_factorialMomentDensity hsupp 0
  refine h.congr_fun (fun x hx => ?_) measurableSet_Ioi
  simp

theorem isFiniteMeasure_factorialMomentMeasure {nu : Measure ℝ} [IsFiniteMeasure nu]
    {R : ℝ} (hsupp : ∀ᵐ y ∂nu, y ∈ Icc 0 R) :
    IsFiniteMeasure (factorialMomentMeasure nu) := by
  constructor
  rw [factorialMomentMeasure, MeasureTheory.withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  have hint := integrableOn_factorialMomentDensity hsupp
  have hfin := hint.2
  rw [MeasureTheory.hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall fun x => factorialMomentDensity_nonneg nu x)] at hfin
  exact hfin

theorem integrable_pow_factorialMomentMeasure {nu : Measure ℝ} [IsFiniteMeasure nu]
    {R : ℝ} (hsupp : ∀ᵐ y ∂nu, y ∈ Icc 0 R) (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n) (factorialMomentMeasure nu) := by
  rw [factorialMomentMeasure, MeasureTheory.integrable_withDensity_iff
    ((measurable_factorialMomentDensity nu).ennreal_ofReal)
    (by filter_upwards with x using ENNReal.ofReal_lt_top)]
  have h := integrableOn_pow_mul_factorialMomentDensity hsupp n
  refine h.congr_fun (fun x hx => ?_) measurableSet_Ioi
  rw [ENNReal.toReal_ofReal (factorialMomentDensity_nonneg nu x)]

theorem integral_pow_factorialMomentMeasure {nu : Measure ℝ} [IsFiniteMeasure nu]
    {R : ℝ} (hsupp : ∀ᵐ y ∂nu, y ∈ Icc 0 R) (n : ℕ) :
    (∫ x, x ^ n ∂(factorialMomentMeasure nu))
      = (Nat.factorial (2 * n + 1) : ℝ) * ∫ y in Ioi (0:ℝ), y ^ (n + 1) ∂nu := by
  rw [integral_factorialMomentMeasure]
  rw [← integral_pow_mul_factorialMomentDensity hsupp n]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  ring

/-! ### The Hardy window -/

theorem integrableOn_expNegSqrt_scale {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun a : ℝ => Real.exp (-(c * Real.sqrt a))) (Ioi 0) volume := by
  have hderiv : ∀ x ∈ Set.Ioi (0:ℝ), HasDerivWithinAt (fun t : ℝ => t ^ 2) (2 * x)
      (Set.Ioi 0) x := by
    intro x _
    have h : HasDerivAt (fun t : ℝ => t ^ 2) (2 * x ^ 1) x := by simpa using hasDerivAt_pow 2 x
    simpa using h.hasDerivWithinAt
  have hiff := MeasureTheory.integrableOn_image_iff_integrableOn_abs_deriv_smul
    (s := Ioi (0:ℝ)) (f := fun t : ℝ => t ^ 2) (f' := fun t : ℝ => 2 * t)
    measurableSet_Ioi hderiv injOn_sq_Ioi_zero
    (fun a : ℝ => Real.exp (-(c * Real.sqrt a)))
  rw [image_sq_Ioi_zero] at hiff
  rw [hiff]
  have hbase := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (1:ℝ)) (p := (1:ℝ)) (b := c)
    (by norm_num) (by norm_num) hc
  have hconst : IntegrableOn
      (fun t : ℝ => 2 * (t ^ (1:ℝ) * Real.exp (-c * t ^ (1:ℝ)))) (Ioi 0) volume :=
    hbase.const_mul 2
  refine hconst.congr_fun (fun t ht => ?_) measurableSet_Ioi
  have ht' : (0:ℝ) < t := ht
  show 2 * (t ^ (1:ℝ) * Real.exp (-c * t ^ (1:ℝ)))
      = |2 * t| • Real.exp (-(c * Real.sqrt (t ^ 2)))
  rw [Real.rpow_one, Real.sqrt_sq ht'.le, abs_of_pos (by linarith : (0:ℝ) < 2 * t),
    smul_eq_mul]
  ring_nf

theorem factorialMomentDensity_le {nu : Measure ℝ} [IsFiniteMeasure nu]
    {R : ℝ} (hsupp : ∀ᵐ y ∂nu, y ∈ Icc 0 R) {x : ℝ} (hx : 0 < x) :
    factorialMomentDensity nu x
      ≤ (nu Set.univ).toReal * Real.exp (-(Real.sqrt x / Real.sqrt R)) := by
  have hint : Integrable (fun y => sqrtExpDensity y x) (nu.restrict (Ioi 0)) := by
    refine Integrable.mono' (integrable_const 1) ?_ ?_
    · exact (measurable_uncurry_sqrtExpDensity.comp
        (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    · filter_upwards with y
      rw [Real.norm_eq_abs, abs_of_nonneg (sqrtExpDensity_nonneg y x)]
      exact sqrtExpDensity_le_one y x
  have hbound : ∀ᵐ y ∂(nu.restrict (Ioi 0)),
      sqrtExpDensity y x ≤ Real.exp (-(Real.sqrt x / Real.sqrt R)) := by
    filter_upwards [ae_restrict_of_ae hsupp, ae_restrict_mem measurableSet_Ioi] with y hy hy0
    have hy' : (0:ℝ) < y := hy0
    have hyR : y ≤ R := hy.2
    rw [sqrtExpDensity]
    refine Real.exp_le_exp.2 ?_
    have hsq : Real.sqrt x / Real.sqrt R ≤ Real.sqrt (x / y) := by
      rw [Real.sqrt_div hx.le]
      refine div_le_div_of_nonneg_left (Real.sqrt_nonneg x) (Real.sqrt_pos.2 hy') ?_
      exact Real.sqrt_le_sqrt hyR
    linarith
  have hmono := integral_mono_ae hint (integrable_const
    (Real.exp (-(Real.sqrt x / Real.sqrt R)))) hbound
  rw [integral_const, smul_eq_mul] at hmono
  have hle : ((nu.restrict (Ioi 0)) Set.univ).toReal ≤ (nu Set.univ).toReal := by
    refine ENNReal.toReal_mono (measure_ne_top nu _) ?_
    rw [Measure.restrict_apply_univ]
    exact measure_mono (Set.subset_univ _)
  have hE : (0:ℝ) ≤ Real.exp (-(Real.sqrt x / Real.sqrt R)) := Real.exp_nonneg _
  rw [factorialMomentDensity]
  have hstep : (∫ y, sqrtExpDensity y x ∂(nu.restrict (Ioi 0))) / 2
      ≤ ((nu Set.univ).toReal * Real.exp (-(Real.sqrt x / Real.sqrt R))) / 2 := by
    refine div_le_div_of_nonneg_right ?_ (by norm_num)
    exact hmono.trans (mul_le_mul_of_nonneg_right hle hE)
  have hnn : (0:ℝ) ≤ (nu Set.univ).toReal * Real.exp (-(Real.sqrt x / Real.sqrt R)) := by
    exact mul_nonneg ENNReal.toReal_nonneg hE
  linarith

/-- **The Hardy window.**  The representing measure has a square-root exponential moment below the
support ceiling, which is Lin's determinacy hypothesis. -/
theorem integrable_exp_sqrt_factorialMomentMeasure {nu : Measure ℝ} [IsFiniteMeasure nu]
    {R : ℝ} (hR : 0 < R) (hsupp : ∀ᵐ y ∂nu, y ∈ Icc 0 R) {c : ℝ}
    (hcR : c < 1 / Real.sqrt R) :
    Integrable (fun x : ℝ => Real.exp (c * Real.sqrt x)) (factorialMomentMeasure nu) := by
  have hRs : (0:ℝ) < Real.sqrt R := Real.sqrt_pos.2 hR
  set eps : ℝ := 1 / Real.sqrt R - c with heps
  have hepspos : 0 < eps := by rw [heps]; linarith
  rw [factorialMomentMeasure, MeasureTheory.integrable_withDensity_iff
    ((measurable_factorialMomentDensity nu).ennreal_ofReal)
    (by filter_upwards with x using ENNReal.ofReal_lt_top)]
  refine Integrable.mono'
    (g := fun x : ℝ => (nu Set.univ).toReal * Real.exp (-(eps * Real.sqrt x)))
    ((integrableOn_expNegSqrt_scale hepspos).const_mul _) ?_ ?_
  · refine AEStronglyMeasurable.mul ?_ ?_
    · exact (Real.continuous_exp.comp (by fun_prop)).aestronglyMeasurable
    · exact ((measurable_factorialMomentDensity nu).ennreal_ofReal.ennreal_toReal).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx' : (0:ℝ) < x := hx
    rw [ENNReal.toReal_ofReal (factorialMomentDensity_nonneg nu x), Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (Real.exp_nonneg _) (factorialMomentDensity_nonneg nu x))]
    calc Real.exp (c * Real.sqrt x) * factorialMomentDensity nu x
        ≤ Real.exp (c * Real.sqrt x) *
            ((nu Set.univ).toReal * Real.exp (-(Real.sqrt x / Real.sqrt R))) :=
          mul_le_mul_of_nonneg_left (factorialMomentDensity_le hsupp hx') (Real.exp_nonneg _)
      _ = (nu Set.univ).toReal * Real.exp (-(eps * Real.sqrt x)) := by
          rw [heps]
          rw [show -((1 / Real.sqrt R - c) * Real.sqrt x)
              = c * Real.sqrt x + -(Real.sqrt x / Real.sqrt R) by field_simp; ring]
          rw [Real.exp_add]
          ring

end

end GaloisForLFunctions.HTGeometry
