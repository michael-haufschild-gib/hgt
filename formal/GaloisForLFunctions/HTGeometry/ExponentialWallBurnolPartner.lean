import GaloisForLFunctions.HTGeometry.SquareIntegrableKernelOperator
import GaloisForLFunctions.HTGeometry.FredholmDeterminantTracePowers
import GaloisForLFunctions.HTGeometry.OperatorFredholmGerm
import GaloisForLFunctions.HTGeometry.ExponentialLaplaceValue
import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaStokesWallExponentialCubicCoherenceValue
import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaStokesWallCubicKernelL2Limit

/-!
# The exponential wall operator and its Burnol partner

Let `μ(dx) = e^{-x} dx` on `(0, ∞)` and `κ(x, y) = 8 (xy)^{3/2}/(x + y)³`.  The wall operator
`(A f)(x) = ∫ κ(x, y) f(y) μ(dy)` factors through the Burnol features
`v_x(r) = 2 x^{3/2} r e^{-xr}` on `L²((0, ∞), dr)`: with `(V f)(r) = ∫ v_x(r) f(x) μ(dx)`,

`‖v_x‖² = 4x³ ∫ r² e^{-2xr} dr = 1`,  `⟨v_x, v_y⟩ = 4(xy)^{3/2} ∫ r² e^{-(x+y)r} dr = κ(x, y)`,

so `V` is Hilbert–Schmidt with `‖V‖²_HS = 1` and `A = V*V`.  The opposite-order partner `B = VV*` is
the integral operator on `L²((0, ∞), dr)` with the weighted Hankel kernel

`b(r, s) = 4rs ∫ x³ e^{-(1 + r + s)x} dx = 24rs/(1 + r + s)⁴`.

Both are positive and Schatten-one with trace `1`, they have the same nonzero eigenvalues with the
same multiplicities, and their Fredholm determinants coincide.
-/

open MeasureTheory Set Filter Topology ProbabilityTheory ContinuousLinearMap
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-! ## Gamma integrals -/

theorem integrableOn_pow_mul_exp_neg_mul_Ioi (n : ℕ) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => t ^ n * Real.exp (-(c * t))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (n : ℝ)) (p := 1) (b := c)
    (by have := n.cast_nonneg (α := ℝ); linarith) le_rfl hc
  refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp [Real.rpow_natCast, neg_mul]

theorem integral_pow_mul_exp_neg_mul_Ioi (n : ℕ) {c : ℝ} (hc : 0 < c) :
    ∫ t in Ioi (0 : ℝ), t ^ n * Real.exp (-(c * t)) = n.factorial / c ^ (n + 1) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (n : ℝ) + 1) (r := c) (by positivity) hc
  have hcongr : ∫ t in Ioi (0 : ℝ), t ^ ((n : ℝ) + 1 - 1) * Real.exp (-(c * t))
      = ∫ t in Ioi (0 : ℝ), t ^ n * Real.exp (-(c * t)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [add_sub_cancel_right, Real.rpow_natCast]
  rw [hcongr] at h
  rw [h, Real.Gamma_nat_eq_factorial,
    show ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast, one_div,
    inv_pow]
  field_simp

theorem lintegral_pow_mul_exp_neg_mul_Ioi (n : ℕ) {c : ℝ} (hc : 0 < c) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ n * Real.exp (-(c * t)))
      = ENNReal.ofReal (n.factorial / c ^ (n + 1)) := by
  rw [← integral_pow_mul_exp_neg_mul_Ioi n hc]
  refine (ofReal_integral_eq_lintegral_ofReal (integrableOn_pow_mul_exp_neg_mul_Ioi n hc) ?_).symm
  exact (ae_restrict_iff' measurableSet_Ioi).mpr
    (Eventually.of_forall fun t ht => by have : 0 < t := ht; positivity)

/-! ## The exponential law -/

local instance isProbabilityMeasure_expMeasure_one_local : IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure one_pos

theorem ae_pos_expMeasure_one : ∀ᵐ x ∂(expMeasure 1), 0 < x := by
  have h : expMeasure 1 (Iic 0) = 0 := by
    rw [← Iio_union_right]
    exact measure_union_null expMeasure_one_Iio_zero (expMeasure_one_singleton 0)
  have hset : {a : ℝ | ¬ 0 < a} = Iic 0 := by
    ext a
    simp
  rw [ae_iff, hset]
  exact h

/-- `∫ f d(expMeasure 1) = ∫_{x > 0} e^{-x} f(x) dx`. -/
theorem integral_expMeasure_one {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) : ∫ x, f x ∂(expMeasure 1) = ∫ x in Ioi 0, Real.exp (-x) • f x := by
  rw [expMeasure_one_eq_withDensity, integral_withDensity_eq_integral_toReal_smul
    measurable_exponentialPDF_one (Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  rw [← setIntegral_eq_integral_of_ae_compl_eq_zero (s := Ioi (0 : ℝ))]
  · refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hx0 : (0 : ℝ) ≤ x := le_of_lt hx
    rw [exponentialPDF_of_nonneg hx0, ENNReal.toReal_ofReal (by positivity)]
    ring_nf
  · have hnull : volume ({0} : Set ℝ) = 0 := Real.volume_singleton
    have h0 : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by
      rw [ae_iff]
      simp only [ne_eq, not_not, setOf_eq_eq_singleton]
      exact hnull
    filter_upwards [h0] with x hx hxs
    have hneg : x < 0 := lt_of_le_of_ne (not_lt.mp hxs) hx
    rw [exponentialPDF_of_neg hneg]
    simp

/-- `∫⁻ f d(expMeasure 1) = ∫⁻_{x > 0} e^{-x} f(x) dx`. -/
theorem lintegral_expMeasure_one {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x ∂(expMeasure 1) = ∫⁻ x in Ioi 0, ENNReal.ofReal (Real.exp (-x)) * f x := by
  rw [expMeasure_one_eq_withDensity,
    lintegral_withDensity_eq_lintegral_mul _ measurable_exponentialPDF_one hf,
    ← lintegral_add_compl _ measurableSet_Ioi]
  have hzero : ∫⁻ y in (Ioi (0 : ℝ))ᶜ, (exponentialPDF 1 * f) y = 0 := by
    rw [compl_Ioi, setLIntegral_congr (Iio_ae_eq_Iic (a := (0 : ℝ))).symm]
    refine setLIntegral_eq_zero measurableSet_Iio fun y hy => ?_
    simp [Pi.mul_apply, exponentialPDF_of_neg hy]
  rw [hzero, add_zero]
  refine setLIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
  rw [Pi.mul_apply, exponentialPDF_of_nonneg (le_of_lt hy)]
  ring_nf

/-! ## The Burnol features -/

/-- The Burnol feature `v_x(r) = 2 x^{3/2} r e^{-xr}`, indexed by the output variable `r`. -/
def burnolFeature (r x : ℝ) : ℝ := 2 * Real.sqrt x ^ 3 * r * Real.exp (-(x * r))

theorem continuous_burnolFeature : Continuous fun p : ℝ × ℝ => burnolFeature p.1 p.2 := by
  unfold burnolFeature
  fun_prop

theorem sqrt_pow_three_mul {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt x ^ 3 * Real.sqrt y ^ 3 = x * y * Real.sqrt (x * y) := by
  rw [← mul_pow, ← Real.sqrt_mul hx, pow_succ, Real.sq_sqrt (mul_nonneg hx hy)]

theorem sqrt_pow_six {x : ℝ} (hx : 0 ≤ x) : (Real.sqrt x ^ 3) ^ 2 = x ^ 3 := by
  rw [← pow_mul, show 3 * 2 = 2 * 3 by rfl, pow_mul, Real.sq_sqrt hx]

theorem burnolFeature_mul {r s x : ℝ} (hx : 0 ≤ x) :
    burnolFeature r x * burnolFeature s x = 4 * r * s * (x ^ 3 * Real.exp (-(x * (r + s)))) := by
  unfold burnolFeature
  have h6 := sqrt_pow_six hx
  have hexp : Real.exp (-(x * r)) * Real.exp (-(x * s)) = Real.exp (-(x * (r + s))) := by
    rw [← Real.exp_add]
    ring_nf
  calc 2 * Real.sqrt x ^ 3 * r * Real.exp (-(x * r)) * (2 * Real.sqrt x ^ 3 * s *
        Real.exp (-(x * s)))
      = 4 * r * s * ((Real.sqrt x ^ 3) ^ 2 * (Real.exp (-(x * r)) * Real.exp (-(x * s)))) := by
        ring
    _ = _ := by rw [h6, hexp]

theorem burnolFeature_mul_left {r x y : ℝ} :
    burnolFeature r x * burnolFeature r y
      = 4 * (Real.sqrt x ^ 3 * Real.sqrt y ^ 3) * (r ^ 2 * Real.exp (-((x + y) * r))) := by
  unfold burnolFeature
  have hexp : Real.exp (-(x * r)) * Real.exp (-(y * r)) = Real.exp (-((x + y) * r)) := by
    rw [← Real.exp_add]
    ring_nf
  calc 2 * Real.sqrt x ^ 3 * r * Real.exp (-(x * r)) * (2 * Real.sqrt y ^ 3 * r *
        Real.exp (-(y * r)))
      = 4 * (Real.sqrt x ^ 3 * Real.sqrt y ^ 3) * (r ^ 2 *
          (Real.exp (-(x * r)) * Real.exp (-(y * r)))) := by ring
    _ = _ := by rw [hexp]

/-- **`⟨v_x, v_y⟩ = κ(x, y)`.** -/
theorem integral_burnolFeature_mul {x y : ℝ} (hxy : 0 < x + y) :
    ∫ r in Ioi (0 : ℝ), burnolFeature r x * burnolFeature r y
      = RHTower.routePPrimitiveGammaJuliaStokesWallCubicKernel x y := by
  simp_rw [burnolFeature_mul_left]
  rw [integral_const_mul, integral_pow_mul_exp_neg_mul_Ioi 2 hxy,
    RHTower.routePPrimitiveGammaJuliaStokesWallCubicKernel]
  norm_num
  field_simp
  ring

/-- **`‖v_x‖² = 1`** for `x > 0`. -/
theorem integral_burnolFeature_sq {x : ℝ} (hx : 0 < x) :
    ∫ r in Ioi (0 : ℝ), burnolFeature r x ^ 2 = 1 := by
  simp_rw [sq]
  rw [integral_burnolFeature_mul (by linarith),
    RHTower.routePPrimitiveGammaJuliaStokesWallCubicKernel, mul_assoc 8, ← sq, sqrt_pow_six hx.le]
  field_simp
  ring

/-- **The co-Gram kernel** `∫ v_x(r) v_x(s) μ(dx) = 24rs/(1 + r + s)⁴`. -/
theorem integral_burnolFeature_mul_expMeasure {r s : ℝ} (hrs : 0 < 1 + r + s) :
    ∫ x, burnolFeature r x * burnolFeature s x ∂(expMeasure 1)
      = 24 * r * s / (1 + r + s) ^ 4 := by
  rw [integral_expMeasure_one]
  have hcongr : ∫ x in Ioi (0 : ℝ), Real.exp (-x) • (burnolFeature r x * burnolFeature s x)
      = ∫ x in Ioi (0 : ℝ), 4 * r * s * (x ^ 3 * Real.exp (-((1 + r + s) * x))) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    rw [smul_eq_mul, burnolFeature_mul (le_of_lt hx)]
    have : Real.exp (-x) * Real.exp (-(x * (r + s))) = Real.exp (-((1 + r + s) * x)) := by
      rw [← Real.exp_add]
      ring_nf
    calc Real.exp (-x) * (4 * r * s * (x ^ 3 * Real.exp (-(x * (r + s)))))
        = 4 * r * s * (x ^ 3 * (Real.exp (-x) * Real.exp (-(x * (r + s))))) := by ring
      _ = _ := by rw [this]
  rw [hcongr, integral_const_mul, integral_pow_mul_exp_neg_mul_Ioi 3 hrs]
  norm_num [Nat.factorial]
  field_simp
  ring

/-! ## The Burnol synthesis operator -/

theorem enorm_ofReal_sq (t : ℝ) : ‖(t : ℂ)‖ₑ ^ 2 = ENNReal.ofReal (t ^ 2) := by
  rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
    ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]

theorem burnolFeature_sq_eq {x : ℝ} (hx : 0 ≤ x) (r : ℝ) :
    burnolFeature r x ^ 2 = 4 * x ^ 3 * (r ^ 2 * Real.exp (-((2 * x) * r))) := by
  rw [sq, burnolFeature_mul_left, sqrt_pow_three_mul hx hx, Real.sqrt_mul_self hx]
  ring_nf

theorem lintegral_burnolFeature_sq {x : ℝ} (hx : 0 < x) :
    ∫⁻ r, ‖((burnolFeature r x : ℝ) : ℂ)‖ₑ ^ 2 ∂halfLineMeasure = 1 := by
  simp_rw [enorm_ofReal_sq]
  have hint : IntegrableOn (fun r => burnolFeature r x ^ 2) (Ioi 0) := by
    have h : IntegrableOn (fun r => 4 * x ^ 3 * (r ^ 2 * Real.exp (-((2 * x) * r)))) (Ioi 0) :=
      (integrableOn_pow_mul_exp_neg_mul_Ioi 2 (show 0 < 2 * x by linarith)).const_mul _
    exact IntegrableOn.congr_fun h (fun r _ => (burnolFeature_sq_eq hx.le r).symm)
      measurableSet_Ioi
  rw [halfLineMeasure, setLIntegral_congr Ioi_ae_eq_Ici.symm,
    ← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun r => sq_nonneg _),
    integral_burnolFeature_sq hx, ENNReal.ofReal_one]

theorem lintegral_lintegral_burnolFeature :
    ∫⁻ r, ∫⁻ x, ‖((burnolFeature r x : ℝ) : ℂ)‖ₑ ^ 2 ∂(expMeasure 1) ∂halfLineMeasure = 1 := by
  have hm : Measurable (Function.uncurry fun (r x : ℝ) => ‖((burnolFeature r x : ℝ) : ℂ)‖ₑ ^ 2) :=
    ((Complex.continuous_ofReal.comp continuous_burnolFeature).measurable.enorm).pow_const 2
  rw [lintegral_lintegral_swap hm.aemeasurable]
  have h : ∫⁻ x, ∫⁻ r, ‖((burnolFeature r x : ℝ) : ℂ)‖ₑ ^ 2 ∂halfLineMeasure ∂(expMeasure 1)
      = ∫⁻ _, 1 ∂(expMeasure 1) := by
    refine lintegral_congr_ae ?_
    filter_upwards [ae_pos_expMeasure_one] with x hx
    exact lintegral_burnolFeature_sq hx
  rw [h, lintegral_const, measure_univ, one_mul]

/-- The Burnol feature kernel `(r, x) ↦ v_x(r)` from `L²(μ)` to `L²((0, ∞), dr)`. -/
def burnolKernel : SqIntKernel halfLineMeasure (expMeasure 1) where
  toFun r x := (burnolFeature r x : ℂ)
  measurable := (Complex.continuous_ofReal.comp continuous_burnolFeature).measurable
  energy_lt_top := by rw [lintegral_lintegral_burnolFeature]; exact ENNReal.one_lt_top

theorem burnolKernel_energy : burnolKernel.energy = 1 := lintegral_lintegral_burnolFeature

/-- The Burnol synthesis operator `(V f)(r) = ∫ v_x(r) f(x) μ(dx)`. -/
def burnolSynthesis : Lp ℂ 2 (expMeasure 1) →L[ℂ] Lp ℂ 2 halfLineMeasure := burnolKernel.op

theorem isHilbertSchmidt_burnolSynthesis : IsHilbertSchmidt burnolSynthesis :=
  burnolKernel.isHilbertSchmidt_op

/-! ## The wall operator -/

/-- The wall kernel `κ(x, y) = 8 (xy)^{3/2}/(x + y)³`. -/
def wallCubicKernel (x y : ℝ) : ℝ := RHTower.routePPrimitiveGammaJuliaStokesWallCubicKernel x y

theorem wallCubicKernel_sq {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    wallCubicKernel x y ^ 2
      = RHTower.routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence x y := by
  rw [wallCubicKernel, RHTower.routePPrimitiveGammaJuliaStokesWallCubicKernel_sq hx hy,
    RHTower.routePPrimitiveGammaJuliaStokesWallCubicCoherence,
    RHTower.routePBaseCauchyCubicNormalizedCoherenceSq,
    RHTower.routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence]
  ring_nf

theorem continuous_wallCubicKernel_sq :
    Measurable fun p : ℝ × ℝ => wallCubicKernel p.1 p.2 := by
  unfold wallCubicKernel RHTower.routePPrimitiveGammaJuliaStokesWallCubicKernel
  fun_prop

/-- `∬ κ² dμ dμ = 16/35`. -/
theorem lintegral_lintegral_wallCubicKernel :
    ∫⁻ x, ∫⁻ y, ‖((wallCubicKernel x y : ℝ) : ℂ)‖ₑ ^ 2 ∂(expMeasure 1) ∂(expMeasure 1)
      = ENNReal.ofReal (16 / 35) := by
  simp_rw [enorm_ofReal_sq]
  have hm : Measurable fun p : ℝ × ℝ => wallCubicKernel p.1 p.2 ^ 2 :=
    continuous_wallCubicKernel_sq.pow_const 2
  rw [← lintegral_prod _ (hm.ennreal_ofReal).aemeasurable]
  have hae : (fun p : ℝ × ℝ => ENNReal.ofReal (wallCubicKernel p.1 p.2 ^ 2))
      =ᵐ[(expMeasure 1).prod (expMeasure 1)] fun p => ENNReal.ofReal
        (RHTower.routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence p.1 p.2) := by
    filter_upwards [GaloisForLFunctions.HTGeometry.ae_nonneg_fst_prod (expMeasure 1) (expMeasure 1)
        expMeasure_one_Iio_zero,
      GaloisForLFunctions.HTGeometry.ae_nonneg_snd_prod (expMeasure 1) (expMeasure 1)
        expMeasure_one_Iio_zero] with p h1 h2
    rw [wallCubicKernel_sq h1 h2]
  rw [lintegral_congr_ae hae, ← ofReal_integral_eq_lintegral_ofReal
    RHTower.integrable_routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence_exp_prod,
    RHTower.integral_routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence_exp_prod_eq]
  filter_upwards [GaloisForLFunctions.HTGeometry.ae_nonneg_fst_prod (expMeasure 1) (expMeasure 1)
      expMeasure_one_Iio_zero,
    GaloisForLFunctions.HTGeometry.ae_nonneg_snd_prod (expMeasure 1) (expMeasure 1)
      expMeasure_one_Iio_zero] with p h1 h2
  exact (RHTower.routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence_zero_le_one h1 h2).1

/-- The wall kernel `κ` on `L²(μ)`. -/
def wallKernel : SqIntKernel (expMeasure 1) (expMeasure 1) where
  toFun x y := (wallCubicKernel x y : ℂ)
  measurable := Complex.measurable_ofReal.comp continuous_wallCubicKernel_sq
  energy_lt_top := by rw [lintegral_lintegral_wallCubicKernel]; exact ENNReal.ofReal_lt_top

theorem wallKernel_energy : wallKernel.energy = ENNReal.ofReal (16 / 35) :=
  lintegral_lintegral_wallCubicKernel

/-- **(EWHC.1).**  The wall operator `(A f)(x) = ∫ κ(x, y) f(y) μ(dy)`. -/
def wallOperator : Lp ℂ 2 (expMeasure 1) →L[ℂ] Lp ℂ 2 (expMeasure 1) := wallKernel.op

/-- **(EWHC.4).**  `A = V*V`. -/
theorem wallOperator_eq_adjoint_comp :
    wallOperator = adjoint burnolSynthesis ∘L burnolSynthesis := by
  rw [burnolSynthesis, burnolKernel.adjoint_op, ← SqIntKernel.op_comp, wallOperator]
  refine SqIntKernel.op_congr _ ?_
  filter_upwards [ae_pos_expMeasure_one] with x hx
  filter_upwards [ae_pos_expMeasure_one] with y hy
  change (wallCubicKernel x y : ℂ)
    = ∫ r, (starRingEnd ℂ) ((burnolFeature r x : ℝ) : ℂ) * ((burnolFeature r y : ℝ) : ℂ)
      ∂halfLineMeasure
  simp_rw [Complex.conj_ofReal, ← Complex.ofReal_mul]
  rw [integral_complex_ofReal, halfLineMeasure, integral_Ici_eq_integral_Ioi,
    integral_burnolFeature_mul (by linarith)]
  rfl

/-- **(EWHC.5).**  The partner `B = VV*`. -/
def partnerOperator : Lp ℂ 2 halfLineMeasure →L[ℂ] Lp ℂ 2 halfLineMeasure :=
  burnolSynthesis ∘L adjoint burnolSynthesis

/-- The partner kernel. -/
def partnerKernel : SqIntKernel halfLineMeasure halfLineMeasure :=
  burnolKernel.comp burnolKernel.adjoint

theorem partnerOperator_eq : partnerOperator = partnerKernel.op := by
  show burnolKernel.op ∘L adjoint burnolKernel.op = (burnolKernel.comp burnolKernel.adjoint).op
  rw [SqIntKernel.op_comp, SqIntKernel.adjoint_op]

/-- **(EWHC.5).**  `b(r, s) = 24rs/(1 + r + s)⁴`. -/
theorem partnerKernel_toFun {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) :
    partnerKernel.toFun r s = ((24 * r * s / (1 + r + s) ^ 4 : ℝ) : ℂ) := by
  change ∫ x, ((burnolFeature r x : ℝ) : ℂ) * (starRingEnd ℂ) ((burnolFeature s x : ℝ) : ℂ)
    ∂(expMeasure 1) = _
  simp_rw [Complex.conj_ofReal, ← Complex.ofReal_mul]
  rw [integral_complex_ofReal, integral_burnolFeature_mul_expMeasure (by linarith)]

/-- **(EWHC.5).**  `(B g)(r) = ∫ 24rs/(1 + r + s)⁴ g(s) ds`. -/
theorem partnerOperator_apply (g : Lp ℂ 2 halfLineMeasure) :
    (partnerOperator g : ℝ → ℂ) =ᵐ[halfLineMeasure]
      fun r => ∫ s, ((24 * r * s / (1 + r + s) ^ 4 : ℝ) : ℂ) * g s ∂halfLineMeasure := by
  rw [partnerOperator_eq]
  have hr : ∀ᵐ r ∂halfLineMeasure, 0 ≤ r := ae_restrict_mem measurableSet_Ici
  filter_upwards [partnerKernel.op_coeFn g, hr] with r h hr
  rw [h, SqIntKernel.apply]
  refine setIntegral_congr_fun measurableSet_Ici fun s hs => ?_
  rw [partnerKernel_toFun hr hs]

end GaloisForLFunctions.HTGeometry
