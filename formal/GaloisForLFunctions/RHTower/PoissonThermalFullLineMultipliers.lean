import GaloisForLFunctions.RHTower.PoissonThermalSymbolCalculus
import GaloisForLFunctions.HTGeometry.L2ConvolutionFourierMultiplier
import GaloisForLFunctions.HTGeometry.FlatPrimitiveFourierCalculus
import GaloisForLFunctions.HTGeometry.SechSquareConvolutionKernel

/-!
# The full-line thermal Poisson operators as Fourier multipliers

On `L²(ℝ)` let `W_full` be convolution by `h(x) = sech²(x/2)` and `J_full = i[X, W_full]`
(bounded extension), whose kernel is `i (x - y) h(x - y)`.  In mathlib's Fourier convention
`𝓕 f (w) = ∫ e^{-2πixw} f(x) dx`, write `ξ = -2πw` for the frequency of the convention
`f̂(ξ) = ∫ f(x) e^{iξx} dx`.  Then:

* `𝓕 h (w) = m(ξ)` and `𝓕 (i x h) (w) = m'(ξ)`, with `m(ξ) = 4πξ/sinh(πξ)`;
* `W_full` and `J_full` are the Fourier multipliers with symbols `m(ξ)` and `m'(ξ)`;
* `J_full f = i (X W_full f - W_full X f)` for every `f` in the domain of `X`;
* `|m'(ξ)| ≤ ∫ |x| h(x) dx`, so `G(t) = m'(-1/t)` is bounded;
* in the bounded Borel calculus of the flat primitive `S = iH` (the maximal multiplier by
  `σ = -1/ξ`), `W_full = F(S)` and `J_full = G(S)`;
* `sgn m'(ξ) = sgn σ` everywhere, hence `sgn(J_full) = sgn(S)`.
-/

noncomputable section
set_option autoImplicit false

open MeasureTheory FourierTransform Filter Set Topology Real
open scoped ENNReal NNReal

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-! ### Fourier transforms of the kernel and of its tilt -/

theorem sechSqHalfSymbol_eq_thermalSymbol (ξ : ℝ) : sechSqHalfSymbol ξ = thermalSymbol ξ := by
  rw [sechSqHalfSymbol_eq]
  by_cases h : ξ = 0
  · rw [if_pos h, h, thermalSymbol_zero]; simp
  · rw [if_neg h, thermalSymbol_of_ne h]
    have hpos : 0 < π * ξ / Real.sinh (π * ξ) := by
      have := thermalSymbol_pos ξ
      rw [thermalSymbol_of_ne h] at this; linarith
    congr 1
    rw [show 4 * π * |ξ| / |Real.sinh (π * ξ)| = 4 * |π * ξ / Real.sinh (π * ξ)| by
      rw [abs_div, abs_mul, abs_of_pos Real.pi_pos]; ring, abs_of_pos hpos]

/-- The kernel `h(x) = sech²(x/2)` as a complex function. -/
def thermalKernel (x : ℝ) : ℂ := (sechSqHalf x : ℂ)

/-- The kernel `i x h(x)` of `J_full`. -/
def thermalTiltKernel (x : ℝ) : ℂ := Complex.I * ((x * sechSqHalf x : ℝ) : ℂ)

theorem measurable_thermalKernel : Measurable thermalKernel :=
  Complex.measurable_ofReal.comp measurable_sechSqHalf

theorem integrable_thermalKernel : Integrable thermalKernel := integrable_sechSqHalf.ofReal

theorem measurable_thermalTiltKernel : Measurable thermalTiltKernel :=
  measurable_const.mul (Complex.measurable_ofReal.comp (measurable_id.mul measurable_sechSqHalf))

theorem norm_thermalTiltKernel (x : ℝ) : ‖thermalTiltKernel x‖ = |x| * sechSqHalf x := by
  rw [thermalTiltKernel, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_mul, abs_of_pos (sechSqHalf_pos x)]

theorem integrable_thermalTiltKernel : Integrable thermalTiltKernel := by
  refine (integrable_norm_iff measurable_thermalTiltKernel.aestronglyMeasurable).mp ?_
  simp_rw [norm_thermalTiltKernel]
  exact integrable_abs_mul_sechSqHalf

/-- The first absolute moment `∫ |x| h(x) dx`, the Schur bound of `J_full`. -/
def thermalTiltMass : ℝ := ∫ x, |x| * sechSqHalf x

theorem thermalTiltMass_nonneg : 0 ≤ thermalTiltMass :=
  integral_nonneg fun x => mul_nonneg (abs_nonneg x) (sechSqHalf_pos x).le

/-- `𝓕 h (w) = m(2πw)`. -/
theorem fourier_thermalKernel' (w : ℝ) : 𝓕 thermalKernel w = thermalSymbol (2 * π * w) := by
  rw [Real.fourier_real_eq, ← sechSqHalfSymbol_eq_thermalSymbol, sechSqHalfSymbol]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [thermalKernel, Circle.smul_def, Real.fourierChar_apply, smul_eq_mul]
  rw [mul_comm]
  congr 2
  push_cast
  ring

/-- **The multiplier of `W_full`:** `𝓕 h (w) = m(ξ)`, `ξ = -2πw`. -/
theorem fourier_thermalKernel (w : ℝ) : 𝓕 thermalKernel w = thermalSymbol (-(2 * π * w)) := by
  rw [fourier_thermalKernel', thermalSymbol_even]

/-- **The multiplier of `J_full`:** `𝓕 (i x h) (w) = m'(ξ)`, `ξ = -2πw`. -/
theorem fourier_thermalTiltKernel (w : ℝ) :
    𝓕 thermalTiltKernel w = thermalSymbolDeriv (-(2 * π * w)) := by
  have hxf : Integrable fun x : ℝ => x • thermalKernel x := by
    refine integrable_abs_mul_sechSqHalf.mono' (measurable_id.smul measurable_thermalKernel :
      Measurable fun x : ℝ => x • thermalKernel x).aestronglyMeasurable (Eventually.of_forall fun x => le_of_eq ?_)
    rw [norm_smul, thermalKernel, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (sechSqHalf_pos x)]
  have h1 := Real.hasDerivAt_fourier integrable_thermalKernel hxf w
  have hsym : 𝓕 thermalKernel = fun w => ((thermalSymbol (2 * π * w) : ℝ) : ℂ) :=
    funext fourier_thermalKernel'
  have h2 : HasDerivAt (fun w => ((thermalSymbol (2 * π * w) : ℝ) : ℂ))
      ((thermalSymbolDeriv (2 * π * w) * (2 * π) : ℝ) : ℂ) w := by
    have hlin : HasDerivAt (fun w : ℝ => 2 * π * w) (2 * π) w := by
      simpa using (hasDerivAt_id w).const_mul (2 * π)
    exact ((hasDerivAt_thermalSymbol (2 * π * w)).comp w hlin).ofReal_comp
  rw [hsym] at h1
  have huniq := h1.unique h2
  have e : (fun x : ℝ => (-2 * (π : ℂ) * Complex.I * (x : ℂ)) • thermalKernel x) =
      fun x => (-(2 * π : ℂ)) * thermalTiltKernel x := by
    funext x
    simp only [thermalKernel, thermalTiltKernel, smul_eq_mul]
    push_cast
    ring
  rw [e, fourier_const_mul_apply] at huniq
  have hpi : (-(2 * π : ℂ)) ≠ 0 := by
    have : (2 * π : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (2 * π : ℝ) ≠ 0)
    exact neg_ne_zero.mpr this
  have := congrArg (fun z => z / (-(2 * π : ℂ))) huniq
  rw [mul_div_cancel_left₀ _ hpi] at this
  rw [this, show -(2 * π * w) = -(2 * π * w) from rfl, thermalSymbolDeriv_neg]
  field_simp
  push_cast
  ring

/-- **`m'` is bounded:** `|m'(ξ)| ≤ ∫ |x| h(x) dx`. -/
theorem abs_thermalSymbolDeriv_le (ξ : ℝ) : |thermalSymbolDeriv ξ| ≤ thermalTiltMass := by
  have h := norm_fourier_apply_le_integral_norm thermalTiltKernel (-(ξ / (2 * π)))
  rw [fourier_thermalTiltKernel, show -(2 * π * -(ξ / (2 * π))) = ξ by field_simp,
    Complex.norm_real, Real.norm_eq_abs] at h
  simpa only [norm_thermalTiltKernel, thermalTiltMass] using h

/-- `G` is bounded by the same constant. -/
theorem abs_primitiveThermalSymbolDeriv_le (t : ℝ) :
    |primitiveThermalSymbolDeriv t| ≤ thermalTiltMass := by
  unfold primitiveThermalSymbolDeriv
  split_ifs
  · simpa using thermalTiltMass_nonneg
  · exact abs_thermalSymbolDeriv_le _

/-! ### The operators -/

/-- The full-line Poisson/Mertens bulk `W_full`: convolution by `h`. -/
def thermalConvOp : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  (convolutionKernel thermalKernel measurable_thermalKernel integrable_thermalKernel).op

/-- The full-line clock commutator `J_full`: convolution by `i x h(x)`. -/
def thermalCommOp : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  (convolutionKernel thermalTiltKernel measurable_thermalTiltKernel integrable_thermalTiltKernel).op

theorem measurable_thermalSymbol_freq :
    Measurable fun w : ℝ => ((thermalSymbol (-(2 * π * w)) : ℝ) : ℂ) :=
  Complex.measurable_ofReal.comp (measurable_thermalSymbol.comp (by fun_prop))

theorem measurable_thermalSymbolDeriv_freq :
    Measurable fun w : ℝ => ((thermalSymbolDeriv (-(2 * π * w)) : ℝ) : ℂ) :=
  Complex.measurable_ofReal.comp (measurable_thermalSymbolDeriv.comp (by fun_prop))

theorem norm_thermalSymbol_freq_le (w : ℝ) : ‖((thermalSymbol (-(2 * π * w)) : ℝ) : ℂ)‖ ≤ 4 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (thermalSymbol_pos _)]
  exact thermalSymbol_le_four _

theorem norm_thermalSymbolDeriv_freq_le (w : ℝ) :
    ‖((thermalSymbolDeriv (-(2 * π * w)) : ℝ) : ℂ)‖ ≤ thermalTiltMass := by
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact abs_thermalSymbolDeriv_le _

/-- **(1) `W_full ↔ m`.** -/
theorem thermalConvOp_eq_fourierMulCLM :
    thermalConvOp = fourierMulCLM measurable_thermalSymbol_freq (by norm_num)
      norm_thermalSymbol_freq_le := by
  rw [thermalConvOp, convolutionKernel_op_eq_fourierMulCLM]
  exact fourierMulCLM_congr_ae _ _ _ _ _ _ (Eventually.of_forall fourier_thermalKernel)

/-- **(1) `J_full ↔ m'`.** -/
theorem thermalCommOp_eq_fourierMulCLM :
    thermalCommOp = fourierMulCLM measurable_thermalSymbolDeriv_freq thermalTiltMass_nonneg
      norm_thermalSymbolDeriv_freq_le := by
  rw [thermalCommOp, convolutionKernel_op_eq_fourierMulCLM]
  exact fourierMulCLM_congr_ae _ _ _ _ _ _ (Eventually.of_forall fourier_thermalTiltKernel)

theorem isSelfAdjoint_thermalConvOp : IsSelfAdjoint thermalConvOp := by
  rw [thermalConvOp_eq_fourierMulCLM]
  exact isSelfAdjoint_fourierMulCLM _ _ _ fun w => Complex.conj_ofReal _

/-- `J_full` is a bounded self-adjoint operator. -/
theorem isSelfAdjoint_thermalCommOp : IsSelfAdjoint thermalCommOp := by
  rw [thermalCommOp_eq_fourierMulCLM]
  exact isSelfAdjoint_fourierMulCLM _ _ _ fun w => Complex.conj_ofReal _

/-- **`J_full = i[X, W_full]`.**  For `f ∈ L²` with `x f ∈ L²` (represented by `g`),
`J_full f = i (x · W_full f - W_full g)` almost everywhere, so `J_full` is the bounded extension of
the commutator from the domain of `X`. -/
theorem thermalCommOp_ae_eq_commutator (f g : Lp ℂ 2 (volume : Measure ℝ))
    (hg : (g : ℝ → ℂ) =ᵐ[volume] fun x => (x : ℂ) * f x) :
    (thermalCommOp f : ℝ → ℂ) =ᵐ[volume]
      fun y => Complex.I * ((y : ℂ) * (thermalConvOp f : ℝ → ℂ) y - (thermalConvOp g : ℝ → ℂ) y) := by
  have hIg : ((Complex.I • g : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume]
      fun x => Complex.I * (x : ℂ) * f x := by
    filter_upwards [Lp.coeFn_smul Complex.I g, hg] with x h1 h2
    rw [h1, Pi.smul_apply, h2, smul_eq_mul, mul_assoc]
  have hk : ∀ y z, (convolutionKernel thermalTiltKernel measurable_thermalTiltKernel
      integrable_thermalTiltKernel).toFun y z = (Complex.I * (y : ℂ) - Complex.I * (z : ℂ)) *
      (convolutionKernel thermalKernel measurable_thermalKernel integrable_thermalKernel).toFun y z := by
    intro y z
    simp only [convolutionKernel_toFun, thermalTiltKernel, thermalKernel]
    push_cast
    ring
  have h := SchurKernel.op_ae_eq_commutator _ _ (fun x : ℝ => Complex.I * (x : ℂ)) hk f
    (Complex.I • g) hIg
  have hsmul : ((thermalConvOp (Complex.I • g) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume]
      fun y => Complex.I * (thermalConvOp g : ℝ → ℂ) y := by
    rw [map_smul]
    filter_upwards [Lp.coeFn_smul Complex.I (thermalConvOp g)] with y hy
    rw [hy, Pi.smul_apply, smul_eq_mul]
  filter_upwards [h, hsmul] with y h1 h2
  rw [thermalCommOp, h1]
  change Complex.I * (y : ℂ) * (thermalConvOp f : ℝ → ℂ) y -
    (thermalConvOp (Complex.I • g) : ℝ → ℂ) y = _
  rw [h2]
  ring

/-! ### `W_full = F(S)`, `J_full = G(S)` -/

theorem measurable_primitiveThermalSymbol_ofReal :
    Measurable fun t : ℝ => ((primitiveThermalSymbol t : ℝ) : ℂ) :=
  Complex.measurable_ofReal.comp measurable_primitiveThermalSymbol

theorem measurable_primitiveThermalSymbolDeriv_ofReal :
    Measurable fun t : ℝ => ((primitiveThermalSymbolDeriv t : ℝ) : ℂ) :=
  Complex.measurable_ofReal.comp measurable_primitiveThermalSymbolDeriv

theorem norm_primitiveThermalSymbol_le (t : ℝ) : ‖((primitiveThermalSymbol t : ℝ) : ℂ)‖ ≤ 4 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (primitiveThermalSymbol_nonneg t)]
  exact primitiveThermalSymbol_le_four t

theorem norm_primitiveThermalSymbolDeriv_le (t : ℝ) :
    ‖((primitiveThermalSymbolDeriv t : ℝ) : ℂ)‖ ≤ thermalTiltMass := by
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact abs_primitiveThermalSymbolDeriv_le t

theorem ae_ne_zero_real : ∀ᵐ w ∂(volume : Measure ℝ), w ≠ 0 := by
  filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (μ := (volume : Measure ℝ)) (0 : ℝ))]
    with w hw using hw

theorem neg_one_div_neg_two_pi_mul (w : ℝ) : -1 / -(2 * π * w) = flatSymbol w := by
  rw [flatSymbol, neg_div_neg_eq, one_div]

/-- **(1) `W_full = F(S)`** in the bounded Borel calculus of the flat primitive. -/
theorem thermalConvOp_eq_flatCalculus :
    thermalConvOp = flatCalculus measurable_primitiveThermalSymbol_ofReal (by norm_num)
      norm_primitiveThermalSymbol_le := by
  rw [thermalConvOp_eq_fourierMulCLM]
  refine fourierMulCLM_congr_ae _ _ _ _ _ _ ?_
  filter_upwards [ae_ne_zero_real] with w hw
  have hξ : -(2 * π * w) ≠ 0 := by
    have := Real.pi_pos; exact neg_ne_zero.mpr (by positivity)
  rw [← neg_one_div_neg_two_pi_mul, primitiveThermalSymbol_neg_inv hξ]

/-- **(1) `J_full = G(S)`** in the bounded Borel calculus of the flat primitive. -/
theorem thermalCommOp_eq_flatCalculus :
    thermalCommOp = flatCalculus measurable_primitiveThermalSymbolDeriv_ofReal
      thermalTiltMass_nonneg norm_primitiveThermalSymbolDeriv_le := by
  rw [thermalCommOp_eq_fourierMulCLM]
  refine fourierMulCLM_congr_ae _ _ _ _ _ _ ?_
  filter_upwards [ae_ne_zero_real] with w hw
  have hξ : -(2 * π * w) ≠ 0 := by
    have := Real.pi_pos; exact neg_ne_zero.mpr (by positivity)
  rw [← neg_one_div_neg_two_pi_mul, primitiveThermalSymbolDeriv_neg_inv hξ]

/-! ### Orientation: `sgn(J_full) = sgn(S)` -/

theorem measurable_sign_ofReal : Measurable fun t : ℝ => ((SignType.sign t : ℝ) : ℂ) := by
  have e : (fun t : ℝ => ((SignType.sign t : ℝ) : ℂ)) =
      fun t => if 0 < t then 1 else if t < 0 then -1 else 0 := by
    funext t
    rcases lt_trichotomy t 0 with h | h | h
    · simp [h, sign_neg h, not_lt.mpr h.le]
    · simp [h]
    · simp [h, sign_pos h]
  rw [e]
  exact Measurable.ite measurableSet_Ioi measurable_const
    (Measurable.ite measurableSet_Iio measurable_const measurable_const)

theorem norm_sign_ofReal_le (t : ℝ) : ‖((SignType.sign t : ℝ) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs]
  rcases lt_trichotomy t 0 with h | h | h
  · simp [sign_neg h]
  · simp [h]
  · simp [sign_pos h]

/-- **(2) at the symbol level:** `sgn m'(ξ) = sgn σ` at every frequency (`ξ = -2πw`). -/
theorem sign_thermalCommSymbol (w : ℝ) :
    SignType.sign (thermalSymbolDeriv (-(2 * π * w))) = SignType.sign (flatSymbol w) := by
  rw [sign_thermalSymbolDeriv, neg_one_div_neg_two_pi_mul]

/-- `sgn ∘ G = sgn`. -/
theorem sign_comp_primitiveThermalSymbolDeriv :
    (fun t : ℝ => ((SignType.sign (primitiveThermalSymbolDeriv t) : ℝ) : ℂ)) =
      fun t => ((SignType.sign t : ℝ) : ℂ) :=
  funext fun t => by rw [sign_primitiveThermalSymbolDeriv]

/-- The sign of `J_full` in its own bounded Borel calculus: the multiplier by `sgn m'(ξ)`. -/
def thermalCommSign : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  fourierMulCLM (measurable_sign_ofReal.comp (measurable_thermalSymbolDeriv.comp (by fun_prop) :
    Measurable fun w : ℝ => thermalSymbolDeriv (-(2 * π * w)))) zero_le_one
    fun w => norm_sign_ofReal_le _

/-- The sign of `S` in its bounded Borel calculus. -/
def flatPrimitiveSign : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  flatCalculus measurable_sign_ofReal zero_le_one norm_sign_ofReal_le

/-- **(2) `sgn(J_full) = sgn(S)`.** -/
theorem thermalCommSign_eq_flatPrimitiveSign : thermalCommSign = flatPrimitiveSign :=
  fourierMulCLM_congr_ae _ _ _ _ _ _ (Eventually.of_forall fun w => by
    simp only [Function.comp_apply, sign_thermalCommSymbol])

/-- `sgn(G(S)) = sgn(S)`: the composite calculus of `sgn ∘ G` is `sgn(S)`. -/
theorem flatCalculus_sign_comp_primitiveThermalSymbolDeriv :
    flatCalculus (measurable_sign_ofReal.comp measurable_primitiveThermalSymbolDeriv) zero_le_one
      (fun _ => norm_sign_ofReal_le _) = flatPrimitiveSign :=
  fourierMulCLM_congr_ae _ _ _ _ _ _ (Eventually.of_forall fun w => by
    simp only [Function.comp_apply, sign_primitiveThermalSymbolDeriv])

/-- **The Gram alone loses the orientation, the commutator restores it.**  The symbol of
`W_full` is even, that of `J_full` is odd with sign `sgn σ`, and the joint symbol is injective. -/
theorem thermal_orientation :
    (∀ ξ, thermalSymbol (-ξ) = thermalSymbol ξ) ∧
    (∀ ξ, thermalSymbolDeriv (-ξ) = -thermalSymbolDeriv ξ) ∧
    (∀ ξ, SignType.sign (thermalSymbolDeriv ξ) = SignType.sign (-1 / ξ)) ∧
    Function.Injective (fun ξ => (thermalSymbol ξ, thermalSymbolDeriv ξ)) :=
  ⟨thermalSymbol_even, thermalSymbolDeriv_neg, sign_thermalSymbolDeriv,
    thermalSymbol_joint_injective⟩

end RHTower
