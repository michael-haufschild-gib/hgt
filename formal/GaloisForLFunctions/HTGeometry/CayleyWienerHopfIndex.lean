import GaloisForLFunctions.HTGeometry.L2ConvolutionFourierMultiplier
import GaloisForLFunctions.HTGeometry.BoundedFredholmStability
import GaloisForLFunctions.RHTower.SoninL2Model
import GaloisForLFunctions.HTGeometry.CompactKernelL2Representation
import GaloisForLFunctions.HTGeometry.ApertureStableKTheory

/-!
# The Wiener–Hopf index of the Cayley generator

On `L²(ℝ)` let `P₊` be the half-line projection and `V` the convolution with `k(t) = eᵗ 1_{t ≤ 0}`,
`(Vf)(y) = ∫_{z ≥ y} e^{y-z} f(z) dz`.

* `𝓕 k (w) = 1/(1 - 2πiw)`, so `U = 1 - 2V` is the Fourier multiplier with the **Cayley symbol**
  `c(w) = (-1 - 2πiw)/(1 - 2πiw)`, which is unimodular: `U` is unitary.  In the half-angle
  coordinate `w = tan(θ/2)/(2π)` the symbol is `-e^{iθ}`, a loop of winding number one.
* `V` never carries the left half-line into the right one, `P₊ V (1 - P₊) = 0`, and leaks from the
  right to the left with rank one, `(1 - P₊) V P₊ = |φ₋⟩⟨φ₊|`, `φ₊ = e^{-z}1_{z ≥ 0}`,
  `φ₋ = e^{y}1_{y < 0}`.
* Hence the **Wiener–Hopf lift** `T = P₊ U P₊ + (1 - P₊)` satisfies `T T* = 1` and
  `T* T = 1 - 2|φ₊⟩⟨φ₊|`: it is onto with kernel `ℂ φ₊`, Fredholm of index `1`.

So the cone winding `δ(1)` of the endpoint unit, the winding of the Cayley symbol and the analytic
Wiener–Hopf index of its lift are the same integer `1` (`cone_winding_eq_wienerHopf_index`).
-/

set_option autoImplicit false

open MeasureTheory Set Filter FourierTransform
open scoped ENNReal InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

local instance factTwoNeTopCayleyWH : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩

/-! ## The Cayley convolution kernel -/

/-- The Cayley kernel `k(t) = eᵗ 1_{t ≤ 0}`. -/
def cayleyKernel (t : ℝ) : ℂ := (Iic (0 : ℝ)).indicator (fun t => ((Real.exp t : ℝ) : ℂ)) t

theorem measurable_cayleyKernel : Measurable cayleyKernel :=
  (Complex.measurable_ofReal.comp Real.measurable_exp).indicator measurableSet_Iic

theorem integrable_cayleyKernel : Integrable cayleyKernel :=
  (integrable_indicator_iff measurableSet_Iic).mpr (integrableOn_exp_Iic 0).ofReal

theorem cayleyKernel_of_pos {t : ℝ} (ht : 0 < t) : cayleyKernel t = 0 :=
  indicator_of_notMem (by simpa using ht) _

theorem cayleyKernel_of_nonpos {t : ℝ} (ht : t ≤ 0) : cayleyKernel t = ((Real.exp t : ℝ) : ℂ) :=
  indicator_of_mem ht _

/-- The Volterra operator `(Vf)(y) = ∫_{z ≥ y} e^{y - z} f(z) dz`, convolution with `k`. -/
def cayleyVolterra : L2Real →L[ℂ] L2Real :=
  (convolutionKernel cayleyKernel measurable_cayleyKernel integrable_cayleyKernel).op

theorem cayleyVolterra_ae (f : L2Real) :
    (cayleyVolterra f : ℝ → ℂ) =ᵐ[volume] fun y => ∫ z, cayleyKernel (y - z) * f z := by
  filter_upwards [(convolutionKernel cayleyKernel measurable_cayleyKernel
    integrable_cayleyKernel).op_coeFn f] with y hy
  rw [cayleyVolterra, hy]
  rfl

/-- The half-line projection `P₊ = 1_{[0, ∞)}`. -/
abbrev halfProj : L2Real →L[ℂ] L2Real := RHTower.indicatorCutoff (Ici 0) measurableSet_Ici

theorem halfProj_ae (f : L2Real) :
    (halfProj f : ℝ → ℂ) =ᵐ[volume] (Ici (0 : ℝ)).indicator fun x => f x :=
  RHTower.indicatorCutoff_ae _ _ f

theorem one_sub_halfProj_ae (f : L2Real) :
    ((1 - halfProj) f : ℝ → ℂ) =ᵐ[volume] (Iio (0 : ℝ)).indicator fun x => f x := by
  filter_upwards [Lp.coeFn_sub f (halfProj f), halfProj_ae f] with x h1 h2
  rw [sub_apply, one_apply_eq_self, h1, Pi.sub_apply, h2]
  by_cases hx : 0 ≤ x
  · rw [indicator_of_mem (mem_Ici.mpr hx), indicator_of_notMem (by simpa using hx), sub_self]
  · rw [indicator_of_notMem (by simpa using hx), indicator_of_mem (by simpa using hx), sub_zero]

/-- **The Volterra operator does not carry the left half-line to the right one**:
`P₊ V (1 - P₊) = 0`. -/
theorem halfProj_cayleyVolterra_one_sub : halfProj * cayleyVolterra * (1 - halfProj) = 0 := by
  ext1 f
  refine Lp.ext ?_
  filter_upwards [halfProj_ae (cayleyVolterra ((1 - halfProj) f)),
    cayleyVolterra_ae ((1 - halfProj) f), Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)]
    with y h1 h2 h3
  change (halfProj (cayleyVolterra ((1 - halfProj) f)) : ℝ → ℂ) y =
    ((0 : L2Real →L[ℂ] L2Real) f : ℝ → ℂ) y
  rw [zero_apply, h1, h3]
  by_cases hy : 0 ≤ y
  · rw [indicator_of_mem (mem_Ici.mpr hy), h2]
    have hz : (fun z => cayleyKernel (y - z) * ((1 - halfProj) f) z) =ᵐ[volume] fun _ => 0 := by
      filter_upwards [one_sub_halfProj_ae f] with z hz
      rw [hz]
      by_cases hz0 : z < 0
      · rw [cayleyKernel_of_pos (by linarith), zero_mul]
      · rw [indicator_of_notMem (by simpa using hz0), mul_zero]
    rw [integral_congr_ae hz, integral_zero]
    rfl
  · rw [indicator_of_notMem (by simpa using hy)]
    rfl

/-! ## The two exponential half-line vectors -/

/-- `φ₊(z) = e^{-z} 1_{z ≥ 0}`. -/
def expPlusFun (z : ℝ) : ℂ := (Ici (0 : ℝ)).indicator (fun z => ((Real.exp (-z) : ℝ) : ℂ)) z

/-- `φ₋(y) = e^{y} 1_{y < 0}`. -/
def expMinusFun (y : ℝ) : ℂ := (Iio (0 : ℝ)).indicator (fun y => ((Real.exp y : ℝ) : ℂ)) y

theorem integrableOn_exp_neg_two_Ici : IntegrableOn (fun z : ℝ => Real.exp (-(2 * z))) (Ici 0) := by
  have h := exp_neg_integrableOn_Ioi 0 (b := 2) (by norm_num)
  refine (integrableOn_Ici_iff_integrableOn_Ioi).mpr ?_
  simpa [neg_mul] using h

theorem memLp_expPlusFun : MemLp expPlusFun 2 volume := by
  refine (memLp_two_iff_integrable_sq_norm ?_).mpr ?_
  · exact ((Complex.measurable_ofReal.comp (Real.measurable_exp.comp measurable_neg)).indicator
      measurableSet_Ici).aestronglyMeasurable
  · have heq : (fun z => ‖expPlusFun z‖ ^ 2) =
        (Ici (0 : ℝ)).indicator fun z => Real.exp (-(2 * z)) := by
      funext z
      by_cases hz : z ∈ Ici (0 : ℝ)
      · rw [expPlusFun, indicator_of_mem hz, indicator_of_mem hz, Complex.norm_real,
          Real.norm_of_nonneg (Real.exp_pos _).le, ← Real.exp_nat_mul]
        congr 1
        push_cast
        ring
      · rw [expPlusFun, indicator_of_notMem hz, indicator_of_notMem hz, norm_zero]
        norm_num
    rw [heq]
    exact (integrable_indicator_iff measurableSet_Ici).mpr integrableOn_exp_neg_two_Ici

theorem memLp_expMinusFun : MemLp expMinusFun 2 volume := by
  refine (memLp_two_iff_integrable_sq_norm ?_).mpr ?_
  · exact ((Complex.measurable_ofReal.comp Real.measurable_exp).indicator
      measurableSet_Iio).aestronglyMeasurable
  · have heq : (fun y => ‖expMinusFun y‖ ^ 2) =
        (Iio (0 : ℝ)).indicator fun y => Real.exp (2 * y) := by
      funext y
      by_cases hy : y ∈ Iio (0 : ℝ)
      · rw [expMinusFun, indicator_of_mem hy, indicator_of_mem hy, Complex.norm_real,
          Real.norm_of_nonneg (Real.exp_pos _).le, ← Real.exp_nat_mul]
        push_cast
        ring_nf
      · rw [expMinusFun, indicator_of_notMem hy, indicator_of_notMem hy, norm_zero]
        norm_num
    rw [heq]
    refine (integrable_indicator_iff measurableSet_Iio).mpr ?_
    exact (integrableOn_Iic_iff_integrableOn_Iio).mp (integrableOn_exp_mul_Iic (by norm_num) 0)

/-- `φ₊ ∈ L²(ℝ)`. -/
def expPlus : L2Real := memLp_expPlusFun.toLp _

/-- `φ₋ ∈ L²(ℝ)`. -/
def expMinus : L2Real := memLp_expMinusFun.toLp _

theorem expPlus_ae : (expPlus : ℝ → ℂ) =ᵐ[volume] expPlusFun := MemLp.coeFn_toLp _

theorem expMinus_ae : (expMinus : ℝ → ℂ) =ᵐ[volume] expMinusFun := MemLp.coeFn_toLp _

theorem inner_expPlus (f : L2Real) :
    inner ℂ expPlus f = ∫ z, expPlusFun z * f z := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [expPlus_ae] with z hz
  rw [hz]
  simp only [RCLike.inner_apply, expPlusFun]
  by_cases h : z ∈ Ici (0 : ℝ)
  · rw [indicator_of_mem h, Complex.conj_ofReal, mul_comm]
  · rw [indicator_of_notMem h, map_zero, zero_mul, mul_zero]

/-- **The Volterra operator leaks across the origin in one direction only, and with rank one**:
`(1 - P₊) V P₊ = |φ₋⟩⟨φ₊|`. -/
theorem one_sub_halfProj_cayleyVolterra_halfProj :
    (1 - halfProj) * cayleyVolterra * halfProj = InnerProductSpace.rankOne ℂ expMinus expPlus := by
  ext1 f
  refine Lp.ext ?_
  filter_upwards [one_sub_halfProj_ae (cayleyVolterra (halfProj f)),
    cayleyVolterra_ae (halfProj f), expMinus_ae,
    Lp.coeFn_smul (inner ℂ expPlus f) expMinus] with y h1 h2 h3 h4
  change ((1 - halfProj) (cayleyVolterra (halfProj f)) : ℝ → ℂ) y =
    ((InnerProductSpace.rankOne ℂ expMinus expPlus) f : ℝ → ℂ) y
  rw [InnerProductSpace.rankOne_def, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
    h1, h4, Pi.smul_apply, h3, smul_eq_mul]
  by_cases hy : y < 0
  · rw [indicator_of_mem (mem_Iio.mpr hy), h2, expMinusFun, indicator_of_mem (mem_Iio.mpr hy),
      inner_expPlus, mul_comm, ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [halfProj_ae f] with z hz
    rw [hz]
    by_cases hz0 : 0 ≤ z
    · rw [indicator_of_mem (mem_Ici.mpr hz0), expPlusFun, indicator_of_mem (mem_Ici.mpr hz0),
        cayleyKernel_of_nonpos (by linarith)]
      rw [show y - z = y + -z by ring, Real.exp_add]
      push_cast
      ring
    · rw [indicator_of_notMem (by simpa using hz0), expPlusFun,
        indicator_of_notMem (by simpa using hz0)]
      ring
  · rw [indicator_of_notMem (by simpa using hy), expMinusFun,
      indicator_of_notMem (by simpa using hy), mul_zero]

/-! ## The Cayley symbol -/

/-- `∫_{v ≤ 0} e^{a v} dv = 1/a` for `Re a > 0`. -/
theorem integral_exp_mul_complex_Iic_zero {a : ℂ} (ha : 0 < a.re) :
    ∫ v in Iic (0 : ℝ), Complex.exp (a * v) = 1 / a := by
  have h := integral_comp_neg_Iic (E := ℂ) 0 (fun x : ℝ => Complex.exp (-a * x))
  simp only [neg_zero] at h
  have h2 : (fun x : ℝ => Complex.exp (-a * ((-x : ℝ) : ℂ))) = fun x : ℝ => Complex.exp (a * x) := by
    funext x
    push_cast
    ring_nf
  rw [h2] at h
  rw [h, integral_exp_mul_complex_Ioi (by simpa using ha)]
  have ha0 : a ≠ 0 := fun h0 => by simp [h0] at ha
  field_simp
  simp

/-- **The Fourier transform of the Cayley kernel**: `𝓕 k (w) = 1 / (1 - 2πiw)`. -/
theorem fourier_cayleyKernel (w : ℝ) :
    𝓕 cayleyKernel w = 1 / (1 - 2 * Real.pi * w * Complex.I) := by
  rw [Real.fourier_real_eq]
  have h : (fun v : ℝ => 𝐞 (-(v * w)) • cayleyKernel v) =
      (Iic (0 : ℝ)).indicator fun v => Complex.exp ((1 - 2 * Real.pi * w * Complex.I) * v) := by
    funext v
    by_cases hv : v ∈ Iic (0 : ℝ)
    · rw [indicator_of_mem hv, cayleyKernel_of_nonpos hv, Circle.smul_def, Real.fourierChar_apply,
        smul_eq_mul, Complex.ofReal_exp, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    · rw [indicator_of_notMem hv, cayleyKernel, indicator_of_notMem hv, smul_zero]
  rw [h, integral_indicator measurableSet_Iic, integral_exp_mul_complex_Iic_zero (by simp)]

/-- The Cayley symbol `c(w) = 1 - 2/(1 - 2πiw) = (-1 - 2πiw)/(1 - 2πiw)`. -/
def cayleySymbol (w : ℝ) : ℂ := 1 - 2 * 𝓕 cayleyKernel w

theorem cayleySymbol_eq (w : ℝ) :
    cayleySymbol w = (-1 - 2 * Real.pi * w * Complex.I) / (1 - 2 * Real.pi * w * Complex.I) := by
  have hne : (1 - 2 * Real.pi * w * Complex.I) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  rw [cayleySymbol, fourier_cayleyKernel]
  field_simp
  ring

/-- **The Cayley symbol is unimodular.** -/
theorem norm_cayleySymbol (w : ℝ) : ‖cayleySymbol w‖ = 1 := by
  have hne : (1 - 2 * Real.pi * w * Complex.I) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  rw [cayleySymbol_eq, norm_div, div_eq_one_iff_eq (norm_ne_zero_iff.mpr hne)]
  have h1 : (-1 - 2 * Real.pi * w * Complex.I) = -(starRingEnd ℂ) (1 - 2 * Real.pi * w * Complex.I) := by
    simp [map_sub, Complex.conj_ofReal, map_ofNat]
    ring
  rw [h1, norm_neg, Complex.norm_conj]

theorem measurable_cayleySymbol : Measurable cayleySymbol :=
  measurable_const.sub (measurable_const.mul
    (continuous_fourier_of_integrable' integrable_cayleyKernel).measurable)

theorem norm_fourier_cayleyKernel_le (w : ℝ) : ‖𝓕 cayleyKernel w‖ ≤ ∫ x, ‖cayleyKernel x‖ :=
  norm_fourier_apply_le_integral_norm cayleyKernel w

/-- The Cayley unitary `U = 1 - 2V`. -/
def cayleyUnitary : L2Real →L[ℂ] L2Real := 1 - (2 : ℂ) • cayleyVolterra

/-- **`U` is the Fourier multiplier with the Cayley symbol.** -/
theorem cayleyUnitary_eq_fourierMulCLM :
    cayleyUnitary = fourierMulCLM measurable_cayleySymbol zero_le_one
      (fun w => (norm_cayleySymbol w).le) := by
  have hV := convolutionKernel_op_eq_fourierMulCLM cayleyKernel measurable_cayleyKernel
    integrable_cayleyKernel
  have h1 := fourierMulCLM_eq_id (E := ℝ) (φ := fun _ => (1 : ℂ)) measurable_const zero_le_one
    (fun _ => by simp) (Filter.Eventually.of_forall fun _ => rfl)
  have h2 := fourierMulCLM_smul (E := ℝ)
    (continuous_fourier_of_integrable' integrable_cayleyKernel).measurable
    (measurable_const.mul (continuous_fourier_of_integrable' integrable_cayleyKernel).measurable)
    (integral_nonneg fun x => norm_nonneg (cayleyKernel x))
    (norm_fourier_apply_le_integral_norm cayleyKernel)
    (by positivity : (0 : ℝ) ≤ 2 * ∫ x, ‖cayleyKernel x‖)
    (fun w => by
      simp only [Pi.mul_apply]
      rw [norm_mul]
      simpa using mul_le_mul_of_nonneg_left (norm_fourier_cayleyKernel_le w) (by norm_num : (0:ℝ) ≤ 2))
    2 (Filter.Eventually.of_forall fun _ => rfl)
  have h3 := fourierMulCLM_sub (E := ℝ) (φ := fun _ => (1 : ℂ))
    (ψ := fun w => 2 * 𝓕 cayleyKernel w) measurable_const
    (measurable_const.mul (continuous_fourier_of_integrable' integrable_cayleyKernel).measurable)
    measurable_cayleySymbol zero_le_one (fun _ => by simp)
    (by positivity : (0 : ℝ) ≤ 2 * ∫ x, ‖cayleyKernel x‖)
    (fun w => by
      rw [norm_mul]
      simpa using mul_le_mul_of_nonneg_left (norm_fourier_cayleyKernel_le w) (by norm_num : (0:ℝ) ≤ 2))
    zero_le_one (fun w => (norm_cayleySymbol w).le)
    (Filter.Eventually.of_forall fun _ => rfl)
  rw [h3, h1, h2, ← hV]
  rfl

theorem conj_cayleySymbol_mul (w : ℝ) :
    (starRingEnd ℂ) (cayleySymbol w) * cayleySymbol w = 1 := by
  rw [Complex.conj_mul', norm_cayleySymbol]
  simp

/-- **`U` is unitary.** -/
theorem adjoint_cayleyUnitary_mul : ContinuousLinearMap.adjoint cayleyUnitary * cayleyUnitary = 1 := by
  have hconj : Measurable fun w => (starRingEnd ℂ) (cayleySymbol w) :=
    Complex.continuous_conj.measurable.comp measurable_cayleySymbol
  rw [cayleyUnitary_eq_fourierMulCLM, adjoint_fourierMulCLM measurable_cayleySymbol hconj
    zero_le_one (fun w => (norm_cayleySymbol w).le) zero_le_one
    (fun w => by rw [Complex.norm_conj]; exact (norm_cayleySymbol w).le) (fun _ => rfl)]
  rw [ContinuousLinearMap.mul_def, fourierMulCLM_comp (χ := fun _ => (1 : ℂ)) hconj
    measurable_cayleySymbol measurable_const zero_le_one (fun w => by rw [Complex.norm_conj]; exact (norm_cayleySymbol w).le)
    zero_le_one (fun w => (norm_cayleySymbol w).le) zero_le_one (fun _ => by simp)
    (Filter.Eventually.of_forall fun w => (conj_cayleySymbol_mul w).symm)]
  exact fourierMulCLM_eq_id _ _ _ (Filter.Eventually.of_forall fun _ => rfl)

theorem cayleyUnitary_mul_adjoint : cayleyUnitary * ContinuousLinearMap.adjoint cayleyUnitary = 1 := by
  have hconj : Measurable fun w => (starRingEnd ℂ) (cayleySymbol w) :=
    Complex.continuous_conj.measurable.comp measurable_cayleySymbol
  rw [cayleyUnitary_eq_fourierMulCLM, adjoint_fourierMulCLM measurable_cayleySymbol hconj
    zero_le_one (fun w => (norm_cayleySymbol w).le) zero_le_one
    (fun w => by rw [Complex.norm_conj]; exact (norm_cayleySymbol w).le) (fun _ => rfl)]
  rw [ContinuousLinearMap.mul_def, fourierMulCLM_comp (χ := fun _ => (1 : ℂ))
    measurable_cayleySymbol hconj measurable_const zero_le_one (fun w => (norm_cayleySymbol w).le)
    zero_le_one (fun w => by rw [Complex.norm_conj]; exact (norm_cayleySymbol w).le)
    zero_le_one (fun _ => by simp)
    (Filter.Eventually.of_forall fun w => by rw [mul_comm]; exact (conj_cayleySymbol_mul w).symm)]
  exact fourierMulCLM_eq_id _ _ _ (Filter.Eventually.of_forall fun _ => rfl)

/-! ## Norms of the exponential vectors -/

theorem integral_exp_neg_two_Ici : ∫ z in Ici (0 : ℝ), Complex.exp (-2 * z) = 1 / 2 := by
  rw [integral_Ici_eq_integral_Ioi, integral_exp_mul_complex_Ioi (by norm_num)]
  simp

theorem integral_exp_two_Iio : ∫ y in Iio (0 : ℝ), Complex.exp (2 * y) = 1 / 2 := by
  rw [← integral_Iic_eq_integral_Iio, integral_exp_mul_complex_Iic_zero (by norm_num)]

theorem inner_expPlus_self : inner ℂ expPlus expPlus = 1 / 2 := by
  rw [inner_expPlus, ← integral_exp_neg_two_Ici, ← integral_indicator measurableSet_Ici]
  refine integral_congr_ae ?_
  filter_upwards [expPlus_ae] with z hz
  rw [hz, expPlusFun]
  by_cases h : z ∈ Ici (0 : ℝ)
  · rw [indicator_of_mem h, indicator_of_mem h, ← Complex.ofReal_mul, ← Real.exp_add,
      Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  · rw [indicator_of_notMem h, indicator_of_notMem h, zero_mul]

theorem inner_expMinus (f : L2Real) :
    inner ℂ expMinus f = ∫ y, expMinusFun y * f y := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [expMinus_ae] with y hy
  rw [hy]
  simp only [RCLike.inner_apply, expMinusFun]
  by_cases h : y ∈ Iio (0 : ℝ)
  · rw [indicator_of_mem h, Complex.conj_ofReal, mul_comm]
  · rw [indicator_of_notMem h, map_zero, zero_mul, mul_zero]

theorem inner_expMinus_self : inner ℂ expMinus expMinus = 1 / 2 := by
  rw [inner_expMinus, ← integral_exp_two_Iio, ← integral_indicator measurableSet_Iio]
  refine integral_congr_ae ?_
  filter_upwards [expMinus_ae] with y hy
  rw [hy, expMinusFun]
  by_cases h : y ∈ Iio (0 : ℝ)
  · rw [indicator_of_mem h, indicator_of_mem h, ← Complex.ofReal_mul, ← Real.exp_add,
      Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  · rw [indicator_of_notMem h, indicator_of_notMem h, zero_mul]

theorem expPlus_ne_zero : expPlus ≠ 0 := by
  intro h
  have := inner_expPlus_self
  rw [h, inner_zero_left] at this
  norm_num at this

/-! ## The Wiener–Hopf lift of the Cayley unitary -/

/-- **The Wiener–Hopf lift** `T = P₊ U P₊ + (1 - P₊)` of the Cayley unitary. -/
def cayleyWienerHopf : L2Real →L[ℂ] L2Real :=
  halfProj * cayleyUnitary * halfProj + (1 - halfProj)

theorem adjoint_halfProj : ContinuousLinearMap.adjoint halfProj = halfProj := by
  have h := (RHTower.indicatorCutoff_isStarProjection (Ici 0) measurableSet_Ici).isSelfAdjoint
  rw [← ContinuousLinearMap.star_eq_adjoint]
  exact h

theorem halfProj_mul_self : halfProj * halfProj = halfProj :=
  (RHTower.indicatorCutoff_idempotent (Ici 0) measurableSet_Ici).eq

theorem halfProj_cayleyUnitary_one_sub : halfProj * cayleyUnitary * (1 - halfProj) = 0 := by
  have hPQ : halfProj * (1 - halfProj) = 0 := by rw [mul_sub, mul_one, halfProj_mul_self, sub_self]
  have h := halfProj_cayleyVolterra_one_sub
  have hexp : halfProj * cayleyUnitary * (1 - halfProj) =
      halfProj * (1 - halfProj) - (2 : ℂ) • (halfProj * cayleyVolterra * (1 - halfProj)) := by
    rw [cayleyUnitary]
    simp only [mul_sub, sub_mul, mul_one, mul_smul_comm, smul_mul_assoc, smul_sub]
    abel
  rw [hexp, hPQ, h, smul_zero, sub_zero]

theorem one_sub_halfProj_cayleyUnitary_halfProj :
    (1 - halfProj) * cayleyUnitary * halfProj =
      (-2 : ℂ) • InnerProductSpace.rankOne ℂ expMinus expPlus := by
  have hQP : (1 - halfProj) * halfProj = 0 := by rw [sub_mul, one_mul, halfProj_mul_self, sub_self]
  have h := one_sub_halfProj_cayleyVolterra_halfProj
  have hexp : (1 - halfProj) * cayleyUnitary * halfProj =
      (1 - halfProj) * halfProj - (2 : ℂ) • ((1 - halfProj) * cayleyVolterra * halfProj) := by
    rw [cayleyUnitary]
    simp only [mul_sub, sub_mul, mul_one, one_mul, mul_smul_comm, smul_mul_assoc, smul_sub]
  rw [hexp, hQP, h, zero_sub, neg_smul]

theorem star_halfProj : star halfProj = halfProj := by
  rw [ContinuousLinearMap.star_eq_adjoint, adjoint_halfProj]

theorem star_cayleyUnitary_mul : star cayleyUnitary * cayleyUnitary = 1 := by
  rw [ContinuousLinearMap.star_eq_adjoint, adjoint_cayleyUnitary_mul]

theorem cayleyUnitary_mul_star : cayleyUnitary * star cayleyUnitary = 1 := by
  rw [ContinuousLinearMap.star_eq_adjoint, cayleyUnitary_mul_adjoint]

/-- `P₊ U = P₊ U P₊`. -/
theorem halfProj_mul_cayleyUnitary : halfProj * cayleyUnitary = halfProj * cayleyUnitary * halfProj := by
  have h := halfProj_cayleyUnitary_one_sub
  rw [mul_sub, mul_one] at h
  exact sub_eq_zero.mp h

theorem cayleyWienerHopf_eq : cayleyWienerHopf = halfProj * cayleyUnitary + (1 - halfProj) := by
  rw [cayleyWienerHopf, ← halfProj_mul_cayleyUnitary]

theorem star_cayleyWienerHopf :
    star cayleyWienerHopf = star cayleyUnitary * halfProj + (1 - halfProj) := by
  rw [cayleyWienerHopf_eq, star_add, star_sub, star_one, star_mul, star_halfProj]

/-- **`T T* = 1`: the Wiener–Hopf lift is a co-isometry.** -/
theorem cayleyWienerHopf_mul_star : cayleyWienerHopf * star cayleyWienerHopf = 1 := by
  have hP := halfProj_mul_self
  have hPUQ := halfProj_cayleyUnitary_one_sub
  have hPU := halfProj_mul_cayleyUnitary
  have hUU := cayleyUnitary_mul_star
  -- `Q U* P = (P U Q)* = 0`
  have hQUP : (1 - halfProj) * star cayleyUnitary * halfProj = 0 := by
    have := congrArg star hPUQ
    rw [star_mul, star_mul, star_sub, star_one, star_halfProj, star_zero] at this
    rw [← this, mul_assoc]
  rw [star_cayleyWienerHopf, cayleyWienerHopf_eq]
  calc (halfProj * cayleyUnitary + (1 - halfProj)) * (star cayleyUnitary * halfProj + (1 - halfProj))
      = halfProj * (cayleyUnitary * star cayleyUnitary) * halfProj +
          halfProj * cayleyUnitary * (1 - halfProj) +
          (1 - halfProj) * star cayleyUnitary * halfProj + (1 - halfProj) * (1 - halfProj) := by
        noncomm_ring
    _ = halfProj + (1 - halfProj) := by
        rw [hUU, mul_one, hP, hPUQ, hQUP, sub_mul, one_mul, mul_sub, mul_one, hP, sub_self,
          sub_zero]
        abel
    _ = 1 := by abel

/-- **`T* T = 1 - 2 |φ₊⟩⟨φ₊|`.** -/
theorem star_cayleyWienerHopf_mul :
    star cayleyWienerHopf * cayleyWienerHopf = 1 - (2 : ℂ) • InnerProductSpace.rankOne ℂ expPlus expPlus := by
  have hP := halfProj_mul_self
  have hPU := halfProj_mul_cayleyUnitary
  have hUU := star_cayleyUnitary_mul
  have hR := one_sub_halfProj_cayleyUnitary_halfProj
  set R := InnerProductSpace.rankOne ℂ expMinus expPlus
  -- `(Q U P)* (Q U P) = 4 R* R = 2 |φ₊⟩⟨φ₊|`
  have hRR : star R * R = (1 / 2 : ℂ) • InnerProductSpace.rankOne ℂ expPlus expPlus := by
    rw [ContinuousLinearMap.star_eq_adjoint, InnerProductSpace.adjoint_rankOne, ContinuousLinearMap.mul_def,
      InnerProductSpace.rankOne_comp_rankOne, inner_expMinus_self]
  have hQ : (1 - halfProj) * (1 - halfProj) = 1 - halfProj := by
    rw [sub_mul, one_mul, mul_sub, mul_one, hP, sub_self, sub_zero]
  have hdefect : halfProj * star cayleyUnitary * (1 - halfProj) * cayleyUnitary * halfProj =
      (2 : ℂ) • InnerProductSpace.rankOne ℂ expPlus expPlus := by
    have h1 : halfProj * star cayleyUnitary * (1 - halfProj) =
        star ((1 - halfProj) * cayleyUnitary * halfProj) := by
      rw [star_mul, star_mul, star_sub, star_one, star_halfProj, mul_assoc]
    calc halfProj * star cayleyUnitary * (1 - halfProj) * cayleyUnitary * halfProj
        = halfProj * star cayleyUnitary * ((1 - halfProj) * (1 - halfProj)) * cayleyUnitary *
            halfProj := by rw [hQ]
      _ = (halfProj * star cayleyUnitary * (1 - halfProj)) *
            ((1 - halfProj) * cayleyUnitary * halfProj) := by noncomm_ring
      _ = star ((-2 : ℂ) • R) * ((-2 : ℂ) • R) := by rw [h1, hR]
      _ = (2 : ℂ) • InnerProductSpace.rankOne ℂ expPlus expPlus := by
          rw [star_smul, smul_mul_smul_comm, hRR, smul_smul]
          norm_num
  rw [star_cayleyWienerHopf, cayleyWienerHopf_eq]
  calc (star cayleyUnitary * halfProj + (1 - halfProj)) * (halfProj * cayleyUnitary + (1 - halfProj))
      = star cayleyUnitary * (halfProj * halfProj) * cayleyUnitary +
          star cayleyUnitary * (halfProj * (1 - halfProj)) +
          (1 - halfProj) * halfProj * cayleyUnitary + (1 - halfProj) * (1 - halfProj) := by
        noncomm_ring
    _ = star cayleyUnitary * halfProj * cayleyUnitary + (1 - halfProj) := by
        rw [hP, hQ, mul_sub, mul_one, hP, sub_self, sub_mul, one_mul, hP, sub_self, mul_zero,
          zero_mul, add_zero, add_zero, mul_assoc]
    _ = 1 - (2 : ℂ) • InnerProductSpace.rankOne ℂ expPlus expPlus := by
        have h2 : star cayleyUnitary * halfProj * cayleyUnitary =
            halfProj * star cayleyUnitary * halfProj * cayleyUnitary * halfProj := by
          have hs : star cayleyUnitary * halfProj = halfProj * star cayleyUnitary * halfProj := by
            have := congrArg star hPU
            rw [star_mul, star_mul, star_mul, star_halfProj] at this
            rw [mul_assoc]
            exact this
          calc star cayleyUnitary * halfProj * cayleyUnitary
              = halfProj * star cayleyUnitary * halfProj * cayleyUnitary := by rw [hs]
            _ = halfProj * star cayleyUnitary * (halfProj * cayleyUnitary) := by noncomm_ring
            _ = halfProj * star cayleyUnitary * (halfProj * cayleyUnitary * halfProj) := by
                rw [← hPU]
            _ = halfProj * star cayleyUnitary * halfProj * cayleyUnitary * halfProj := by
                noncomm_ring
        rw [h2]
        have h3 : halfProj * star cayleyUnitary * halfProj * cayleyUnitary * halfProj =
            halfProj * (star cayleyUnitary * cayleyUnitary) * halfProj -
              halfProj * star cayleyUnitary * (1 - halfProj) * cayleyUnitary * halfProj := by
          noncomm_ring
        rw [h3, hUU, mul_one, hP, hdefect]
        abel

/-! ## Kernel, range and index -/

theorem star_cayleyWienerHopf_mul_apply (x : L2Real) :
    (star cayleyWienerHopf * cayleyWienerHopf) x = x - (2 * inner ℂ expPlus x) • expPlus := by
  rw [star_cayleyWienerHopf_mul, sub_apply, one_apply_eq_self, smul_apply,
    InnerProductSpace.rankOne_apply, smul_smul]

theorem inner_cayleyWienerHopf_self (x : L2Real) :
    inner ℂ (cayleyWienerHopf x) (cayleyWienerHopf x) =
      inner ℂ ((star cayleyWienerHopf * cayleyWienerHopf) x) x := by
  rw [mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_left]

theorem cayleyWienerHopf_expPlus : cayleyWienerHopf expPlus = 0 := by
  have h0 : (star cayleyWienerHopf * cayleyWienerHopf) expPlus = 0 := by
    rw [star_cayleyWienerHopf_mul_apply, inner_expPlus_self]
    norm_num
  have hinner := inner_cayleyWienerHopf_self expPlus
  rw [h0, inner_zero_left] at hinner
  exact inner_self_eq_zero.mp hinner

/-- **The kernel of the Wiener–Hopf lift is the line `ℂ φ₊`.** -/
theorem ker_cayleyWienerHopf :
    LinearMap.ker (cayleyWienerHopf : L2Real →ₗ[ℂ] L2Real) = ℂ ∙ expPlus := by
  ext x
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, Submodule.mem_span_singleton]
  constructor
  · intro hx
    have h := star_cayleyWienerHopf_mul_apply x
    rw [mul_apply_eq_comp, hx, map_zero] at h
    exact ⟨2 * inner ℂ expPlus x, (sub_eq_zero.mp h.symm).symm⟩
  · rintro ⟨c, rfl⟩
    rw [map_smul, cayleyWienerHopf_expPlus, smul_zero]

/-- **The Wiener–Hopf lift is onto.** -/
theorem range_cayleyWienerHopf :
    LinearMap.range (cayleyWienerHopf : L2Real →ₗ[ℂ] L2Real) = ⊤ := by
  refine eq_top_iff.mpr fun y _ => ⟨star cayleyWienerHopf y, ?_⟩
  change cayleyWienerHopf (star cayleyWienerHopf y) = y
  rw [← mul_apply_eq_comp, cayleyWienerHopf_mul_star, one_apply_eq_self]

/-- **The Wiener–Hopf lift of the Cayley unitary is Fredholm.** -/
theorem isFredholmOp_cayleyWienerHopf : IsFredholmOp cayleyWienerHopf where
  finiteDimensional_ker := by
    rw [ker_cayleyWienerHopf]
    infer_instance
  isClosed_range := by
    rw [range_cayleyWienerHopf]
    exact isClosed_univ
  finiteDimensional_coker := by
    rw [range_cayleyWienerHopf]
    infer_instance

/-- **The analytic Wiener–Hopf index of the Cayley generator is `1`.** -/
theorem fredholmIndex_cayleyWienerHopf : fredholmIndex cayleyWienerHopf = 1 := by
  rw [fredholmIndex, ker_cayleyWienerHopf, range_cayleyWienerHopf, finrank_span_singleton
    expPlus_ne_zero]
  have : Module.finrank ℂ (L2Real ⧸ (⊤ : Submodule ℂ L2Real)) = 0 :=
    Module.finrank_zero_of_subsingleton
  rw [this]
  norm_num

/-! ## The winding of the Cayley symbol -/

/-- **In the half-angle coordinate the Cayley symbol is `-e^{iθ}`**:
`c(tan(θ/2)/(2π)) = -e^{iθ}` for `|θ| < π`. -/
theorem cayleySymbol_tan_half {θ : ℝ} (hθ : θ ∈ Ioo (-Real.pi) Real.pi) :
    cayleySymbol (Real.tan (θ / 2) / (2 * Real.pi)) = -Complex.exp (θ * Complex.I) := by
  set c := Real.cos (θ / 2)
  set s := Real.sin (θ / 2)
  have hc : c ≠ 0 := by
    refine (Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩).ne'
    · linarith [hθ.1]
    · linarith [hθ.2]
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  have hcs : (c : ℂ) ^ 2 + (s : ℂ) ^ 2 = 1 := by
    have := Real.cos_sq_add_sin_sq (θ / 2)
    exact_mod_cast this
  have hE : Complex.exp (θ * Complex.I) = ((c : ℂ) + (s : ℂ) * Complex.I) ^ 2 := by
    have h1 : (θ : ℂ) * Complex.I = 2 * (((θ / 2 : ℝ) : ℂ) * Complex.I) := by push_cast; ring
    rw [h1, show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, Complex.exp_nat_mul, Complex.exp_mul_I,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have hw : (2 * (Real.pi : ℂ) * ((Real.tan (θ / 2) / (2 * Real.pi) : ℝ) : ℂ)) = (s : ℂ) / c := by
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    rw [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_ofNat, Real.tan_eq_sin_div_cos,
      Complex.ofReal_div]
    field_simp
    change (s : ℂ) * (c : ℂ) / (c : ℂ) = s
    rw [mul_div_assoc, div_self hcC, mul_one]
  rw [cayleySymbol_eq, hw, hE]
  have hden : (1 - (s : ℂ) / c * Complex.I) ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    simp [Complex.div_re] at this
  rw [div_eq_iff hden]
  field_simp
  linear_combination ((c : ℂ) + (s : ℂ) * Complex.I) * hcs -
    ((c : ℂ) + (s : ℂ) * Complex.I) * (s : ℂ) ^ 2 * Complex.I_sq

/-- The Cayley loop `θ ↦ -e^{iθ}` on `[-π, π]`, the symbol on the one-point compactification. -/
theorem isLoop_cayleyLoop : _root_.RHTower.IsLoop (fun θ : ℝ => -Complex.exp (θ * Complex.I))
    (-Real.pi) Real.pi :=
  ⟨by fun_prop, fun θ => neg_ne_zero.mpr (Complex.exp_ne_zero _), by
    simp only [Complex.ofReal_neg, neg_mul, Complex.exp_neg, Complex.exp_pi_mul_I, inv_neg,
      inv_one]⟩

/-- **The Cayley symbol winds once.** -/
theorem windingNumber_cayleyLoop :
    _root_.RHTower.windingNumber (fun θ : ℝ => -Complex.exp (θ * Complex.I)) (-Real.pi) Real.pi = 1 := by
  have h := _root_.RHTower.contLog_increment isLoop_cayleyLoop
    (L := fun θ : ℝ => (θ + Real.pi : ℝ) * Complex.I) (by fun_prop) (fun θ => by
      push_cast
      rw [add_mul, Complex.exp_add, Complex.exp_pi_mul_I]
      ring)
  have h2pi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Complex.I_ne_zero, Real.pi_ne_zero]
  have : ((_root_.RHTower.windingNumber (fun θ : ℝ => -Complex.exp (θ * Complex.I)) (-Real.pi)
      Real.pi : ℤ) : ℂ) = 1 := by
    have h' : (((Real.pi + Real.pi : ℝ) : ℂ) * Complex.I - ((-Real.pi + Real.pi : ℝ) : ℂ) * Complex.I) =
        1 * (2 * (Real.pi : ℂ) * Complex.I) := by push_cast; ring
    rw [h'] at h
    exact (mul_right_cancel₀ h2pi h).symm
  exact_mod_cast this

/-! ## One transgression -/

/-- **The cone winding and the analytic Wiener–Hopf index are one transgression**: the Cayley
symbol winds once, its Wiener–Hopf lift has Fredholm index one, and the cone boundary
`δ(1) = [exp(2πi e_1)]` of the endpoint unit winds once in `K₁(J_T)`. -/
theorem cone_winding_eq_wienerHopf_index
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {T : H →L[ℂ] H} (hT : T.IsPositive) (hcpt : IsCompactOperator T)
    (hinj : Function.Injective T) (hH : ¬ FiniteDimensional ℂ H) :
    stableK₁Winding hT hcpt hinj hH (stableConnectingMap hT hcpt hinj hH 1) =
        fredholmIndex cayleyWienerHopf ∧
      fredholmIndex cayleyWienerHopf =
        _root_.RHTower.windingNumber (fun θ : ℝ => -Complex.exp (θ * Complex.I)) (-Real.pi)
          Real.pi := by
  rw [stableK₁Winding_connectingMap, fredholmIndex_cayleyWienerHopf, windingNumber_cayleyLoop]
  exact ⟨rfl, rfl⟩

end GaloisForLFunctions.HTGeometry
