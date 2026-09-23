import GaloisForLFunctions.RHTower.SuzukiCCMMixedScrewWeilBridge
import GaloisForLFunctions.RHTower.CCMRestrictedWeilPolarConstrainedRightContinuity
import GaloisForLFunctions.RHTower.CCMRestrictedWeilPolarGroundEnergy
import GaloisForLFunctions.RHTower.SuzukiScrewTestRayEnergy

/-!
# The polar translate multiplier

A finite combination of translates `M∗f = Σ_k μ_k f(· − τ_k)` multiplies every exponential moment
`∫ e^{zx} f` by the symbol `Σ_k μ_k e^{zτ_k}`.  The five-term symmetric combination with symbol
`(cosh(zh) − 1)(cosh(zh) − cosh(h/2))` kills the moments at `z = 0` (zero mean) and at `z = ±1/2`
(the two pole constraints of the restricted Weil form).  Hence `M∗u` is a pole-vanishing smooth
interior source for **every** smooth interior source `u`, and its derivative test `M∗u'` is a
zero-mean smooth test whose Suzuki ray coefficients are those of `u'` multiplied by the spectral
symbol `(cos(γh) − 1)(cos(γh) − cosh(h/2))`.

Consequences recorded here:
* `isPolarConstrained_polarTranslate`: the multiplied source is pole-vanishing;
* `ccmRestrictedWeilSourceQuadratic_toCCMFormVector_eq_smoothForm`: the CCM restricted quadratic of a
  smooth interior source is the real part of Suzuki's smooth form of its derivative;
* `suzukiScrewSmoothForm_polarTranslateTest_re_nonneg_of_polarGroundEnergy_nonneg`: nonnegativity of
  the pole-vanishing ground energy at one larger aperture makes Suzuki's form nonnegative on every
  multiplied zero-mean test;
* the ray-coefficient multiplier rules.
-/

open Complex MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

/-! ## Translate combinations -/

/-- `Σ_k μ_k f(x − τ_k)`. -/
def translateCombo {n : ℕ} (μ τ : Fin n → ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∑ k, (μ k : ℂ) * f (x - τ k)

/-- The exponential symbol `Σ_k μ_k e^{z τ_k}`. -/
def translateSymbol {n : ℕ} (μ τ : Fin n → ℝ) (z : ℂ) : ℂ :=
  ∑ k, (μ k : ℂ) * Complex.exp (z * (τ k : ℂ))

/-- Multiplying by any function preserves compact support. -/
theorem hasCompactSupport_mul_of_right {f : ℝ → ℂ} (hf : HasCompactSupport f) (g : ℝ → ℂ) :
    HasCompactSupport (fun x => g x * f x) :=
  hf.mono fun x hx => by
    rw [Function.mem_support] at hx ⊢
    intro h0
    exact hx (by rw [h0, mul_zero])

theorem hasCompactSupport_translate {f : ℝ → ℂ} (hf : HasCompactSupport f) (τ : ℝ) :
    HasCompactSupport (fun x => f (x - τ)) :=
  (hf.comp_homeomorph (Homeomorph.subRight τ)).mono fun x hx => hx

theorem translateCombo_eq_zero_of_forall {n : ℕ} (μ τ : Fin n → ℝ) (f : ℝ → ℂ) {x : ℝ}
    (h : ∀ k, f (x - τ k) = 0) : translateCombo μ τ f x = 0 := by
  simp [translateCombo, h]

theorem contDiff_translateCombo {n : ℕ} (μ τ : Fin n → ℝ) {f : ℝ → ℂ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) : ContDiff ℝ (⊤ : ℕ∞) (translateCombo μ τ f) := by
  unfold translateCombo
  exact ContDiff.sum fun k _ => contDiff_const.mul (hf.comp (contDiff_id.sub contDiff_const))

theorem continuous_translateCombo {n : ℕ} (μ τ : Fin n → ℝ) {f : ℝ → ℂ} (hf : Continuous f) :
    Continuous (translateCombo μ τ f) := by
  unfold translateCombo
  fun_prop

theorem support_translateCombo_subset {n : ℕ} (μ τ : Fin n → ℝ) {f : ℝ → ℂ} {a T : ℝ}
    (hsupp : Function.support f ⊆ Icc (-a) a) (hτ : ∀ k, |τ k| ≤ T) :
    Function.support (translateCombo μ τ f) ⊆ Icc (-(a + T)) (a + T) := by
  intro x hx
  rw [Function.mem_support] at hx
  have hex : ∃ k, f (x - τ k) ≠ 0 := by
    by_contra hall
    exact hx (translateCombo_eq_zero_of_forall μ τ f fun k => by
      by_contra h
      exact hall ⟨k, h⟩)
  obtain ⟨k, hk⟩ := hex
  have hmem := hsupp (Function.mem_support.mpr hk)
  rw [mem_Icc] at hmem ⊢
  have := abs_le.mp (hτ k)
  constructor <;> linarith

theorem hasCompactSupport_translateCombo {n : ℕ} (μ τ : Fin n → ℝ) {f : ℝ → ℂ} {a T : ℝ}
    (hsupp : Function.support f ⊆ Icc (-a) a) (hτ : ∀ k, |τ k| ≤ T) :
    HasCompactSupport (translateCombo μ τ f) :=
  IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _)
    (closure_minimal (support_translateCombo_subset μ τ hsupp hτ) isClosed_Icc)

/-- **Exponential moments of a translate combination.** -/
theorem integral_cexp_mul_translateCombo {n : ℕ} (μ τ : Fin n → ℝ) {f : ℝ → ℂ}
    (hf : Continuous f) (hsupp : HasCompactSupport f) (z : ℂ) :
    ∫ x : ℝ, Complex.exp (z * (x : ℂ)) * translateCombo μ τ f x =
      translateSymbol μ τ z * ∫ y : ℝ, Complex.exp (z * (y : ℂ)) * f y := by
  have hterm : ∀ k : Fin n,
      Integrable (fun x : ℝ => Complex.exp (z * (x : ℂ)) * ((μ k : ℂ) * f (x - τ k))) := by
    intro k
    have hc : Continuous (fun x : ℝ => Complex.exp (z * (x : ℂ)) * ((μ k : ℂ) * f (x - τ k))) := by
      fun_prop
    have hs : HasCompactSupport (fun x : ℝ => (μ k : ℂ) * f (x - τ k)) :=
      hasCompactSupport_mul_of_right (hasCompactSupport_translate hsupp (τ k)) _
    exact hc.integrable_of_hasCompactSupport (hasCompactSupport_mul_of_right hs _)
  have hsum : (fun x : ℝ => Complex.exp (z * (x : ℂ)) * translateCombo μ τ f x) =
      fun x : ℝ => ∑ k, Complex.exp (z * (x : ℂ)) * ((μ k : ℂ) * f (x - τ k)) := by
    funext x
    unfold translateCombo
    rw [Finset.mul_sum]
  unfold translateSymbol
  rw [hsum, integral_finset_sum _ (fun k _ => hterm k), Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hkey : (fun x : ℝ => Complex.exp (z * (x : ℂ)) * ((μ k : ℂ) * f (x - τ k))) =
      fun x => (fun y : ℝ => Complex.exp (z * ((y + τ k : ℝ) : ℂ)) * ((μ k : ℂ) * f y)) (x - τ k) := by
    funext x
    simp only [sub_add_cancel]
  have hshift := MeasureTheory.integral_sub_right_eq_self (μ := volume)
    (fun y : ℝ => Complex.exp (z * ((y + τ k : ℝ) : ℂ)) * ((μ k : ℂ) * f y)) (τ k)
  rw [hkey, hshift]
  have hsplit : (fun y : ℝ => Complex.exp (z * ((y + τ k : ℝ) : ℂ)) * ((μ k : ℂ) * f y)) =
      fun y : ℝ => ((μ k : ℂ) * Complex.exp (z * (τ k : ℂ))) * (Complex.exp (z * (y : ℂ)) * f y) := by
    funext y
    push_cast
    rw [mul_add, Complex.exp_add]
    ring
  rw [hsplit, integral_const_mul]

theorem integral_translateCombo {n : ℕ} (μ τ : Fin n → ℝ) {f : ℝ → ℂ}
    (hf : Continuous f) (hsupp : HasCompactSupport f) :
    ∫ x : ℝ, translateCombo μ τ f x = translateSymbol μ τ 0 * ∫ y : ℝ, f y := by
  have := integral_cexp_mul_translateCombo μ τ hf hsupp 0
  simpa using this

theorem deriv_translateCombo {n : ℕ} (μ τ : Fin n → ℝ) {f : ℝ → ℂ} (hf : Differentiable ℝ f) :
    deriv (translateCombo μ τ f) = translateCombo μ τ (deriv f) := by
  funext x
  have hderiv : HasDerivAt (translateCombo μ τ f) (translateCombo μ τ (deriv f) x) x := by
    unfold translateCombo
    refine HasDerivAt.fun_sum (𝕜 := ℝ) fun k _ => ?_
    have h2 : HasDerivAt f (deriv f (x - τ k)) (x - τ k) := (hf _).hasDerivAt
    exact (h2.comp_sub_const x (τ k)).const_mul (μ k : ℂ)
  exact hderiv.deriv

/-! ## The five-term polar multiplier -/

/-- Translation weights `(½ + cosh(h/2), −(1+cosh(h/2))/2, −(1+cosh(h/2))/2, ¼, ¼)`. -/
def polarMultiplierWeight (h : ℝ) : Fin 5 → ℝ :=
  ![1 / 2 + Real.cosh (h / 2), -(1 + Real.cosh (h / 2)) / 2, -(1 + Real.cosh (h / 2)) / 2,
    1 / 4, 1 / 4]

/-- Translation shifts `(0, h, −h, 2h, −2h)`. -/
def polarMultiplierShift (h : ℝ) : Fin 5 → ℝ := ![0, h, -h, 2 * h, -(2 * h)]

/-- The symbol `(cosh(zh) − 1)(cosh(zh) − cosh(h/2))`, written with exponentials. -/
def polarMultiplierSymbol (h : ℝ) (z : ℂ) : ℂ :=
  ((Complex.exp (z * h) + Complex.exp (-(z * h))) / 2 - 1) *
    ((Complex.exp (z * h) + Complex.exp (-(z * h))) / 2 - (Real.cosh (h / 2) : ℂ))

theorem polarMultiplierShift_abs_le {h : ℝ} (hh : 0 < h) (k : Fin 5) :
    |polarMultiplierShift h k| ≤ 2 * h := by
  fin_cases k <;> simp [polarMultiplierShift, abs_le] <;>
    first | (constructor <;> linarith) | linarith

theorem translateSymbol_polarMultiplier (h : ℝ) (z : ℂ) :
    translateSymbol (polarMultiplierWeight h) (polarMultiplierShift h) z =
      polarMultiplierSymbol h z := by
  unfold translateSymbol polarMultiplierWeight polarMultiplierShift polarMultiplierSymbol
  simp only [Fin.sum_univ_five, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.tail_cons]
  have e0 : Complex.exp (z * ((0 : ℝ) : ℂ)) = 1 := by simp
  have e2 : Complex.exp (z * ((2 * h : ℝ) : ℂ)) = Complex.exp (z * h) ^ (2 : ℕ) := by
    rw [sq, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have em : Complex.exp (z * ((-h : ℝ) : ℂ)) = Complex.exp (-(z * h)) := by
    congr 1
    push_cast
    ring
  have em2 : Complex.exp (z * ((-(2 * h) : ℝ) : ℂ)) = Complex.exp (-(z * h)) ^ (2 : ℕ) := by
    rw [sq, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hEF : Complex.exp (z * h) * Complex.exp (-(z * h)) = 1 := by
    rw [← Complex.exp_add]
    simp
  rw [e0, e2, em, em2]
  push_cast
  linear_combination (-1 / 2 : ℂ) * hEF

theorem polarMultiplierSymbol_zero (h : ℝ) : polarMultiplierSymbol h 0 = 0 := by
  unfold polarMultiplierSymbol
  simp

theorem polarMultiplierSymbol_half (h : ℝ) : polarMultiplierSymbol h (1 / 2) = 0 := by
  unfold polarMultiplierSymbol
  have hc : ((Complex.exp ((1 / 2 : ℂ) * h) + Complex.exp (-((1 / 2 : ℂ) * h))) / 2 -
      (Real.cosh (h / 2) : ℂ)) = 0 := by
    rw [Real.cosh_eq]
    push_cast
    ring_nf
  rw [hc, mul_zero]

theorem polarMultiplierSymbol_neg_half (h : ℝ) : polarMultiplierSymbol h (-1 / 2) = 0 := by
  unfold polarMultiplierSymbol
  have hc : ((Complex.exp ((-1 / 2 : ℂ) * h) + Complex.exp (-((-1 / 2 : ℂ) * h))) / 2 -
      (Real.cosh (h / 2) : ℂ)) = 0 := by
    rw [Real.cosh_eq]
    push_cast
    ring_nf
  rw [hc, mul_zero]

/-- The spectral symbol at `z = ±iγ`: `(cos(γh) − 1)(cos(γh) − cosh(h/2))`. -/
def polarMultiplierSpectral (h : ℝ) (γ : ℂ) : ℂ :=
  (Complex.cos (γ * h) - 1) * (Complex.cos (γ * h) - (Real.cosh (h / 2) : ℂ))

theorem polarMultiplierSymbol_neg_I_mul (h : ℝ) (γ : ℂ) :
    polarMultiplierSymbol h (-(I * γ)) = polarMultiplierSpectral h γ := by
  unfold polarMultiplierSymbol polarMultiplierSpectral
  have hcos : Complex.cos (γ * h) =
      (Complex.exp (-(I * γ) * h) + Complex.exp (-(-(I * γ) * h))) / 2 := by
    rw [Complex.cos]
    congr 1
    rw [add_comm]
    congr 1 <;> congr 1 <;> ring
  rw [hcos]

theorem polarMultiplierSymbol_I_mul (h : ℝ) (γ : ℂ) :
    polarMultiplierSymbol h (I * γ) = polarMultiplierSpectral h γ := by
  unfold polarMultiplierSymbol polarMultiplierSpectral
  have hcos : Complex.cos (γ * h) =
      (Complex.exp (I * γ * h) + Complex.exp (-(I * γ * h))) / 2 := by
    rw [Complex.cos]
    congr 1
    congr 1 <;> congr 1 <;> ring
  rw [hcos]

/-! ## The multiplied smooth interior source -/

/-- The aperture enlarged by `2h + 1`. -/
def SuzukiPositiveAperture.enlarge (a : SuzukiPositiveAperture) (h : ℝ) (hh : 0 < h) :
    SuzukiPositiveAperture :=
  ⟨a.1 + 2 * h + 1, by linarith [a.2]⟩

/-- `M∗u` as a smooth interior source at the enlarged aperture. -/
def CCMComplexSmoothInteriorSource.polarTranslate {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) {h : ℝ} (hh : 0 < h) :
    CCMComplexSmoothInteriorSource (a.enlarge h hh) where
  toFun := translateCombo (polarMultiplierWeight h) (polarMultiplierShift h) u
  smooth := contDiff_translateCombo _ _ u.smooth
  hasCompactSupport := hasCompactSupport_translateCombo _ _
    (u.support_subset.trans Ioo_subset_Icc_self) (polarMultiplierShift_abs_le hh)
  tsupport_subset := by
    refine (closure_minimal (support_translateCombo_subset _ _
      (u.support_subset.trans Ioo_subset_Icc_self) (polarMultiplierShift_abs_le hh))
      isClosed_Icc).trans ?_
    intro x hx
    rw [mem_Icc] at hx
    simp only [SuzukiPositiveAperture.enlarge, mem_Ioo]
    constructor <;> linarith

@[simp] theorem CCMComplexSmoothInteriorSource.polarTranslate_apply {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) {h : ℝ} (hh : 0 < h) (x : ℝ) :
    u.polarTranslate hh x = translateCombo (polarMultiplierWeight h) (polarMultiplierShift h) u x :=
  rfl

/-- **The multiplied source is pole-vanishing.** -/
theorem isPolarConstrained_polarTranslate {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) {h : ℝ} (hh : 0 < h) :
    IsPolarConstrained (a.enlarge h hh) (u.polarTranslate hh).toCCMFormVector := by
  unfold IsPolarConstrained
  rw [inner_ccmPolarApertureVector_ccmComplexSmoothFormVector,
    inner_ccmPolarApertureVector_ccmComplexSmoothFormVector]
  have hplus := integral_cexp_mul_translateCombo (polarMultiplierWeight h) (polarMultiplierShift h)
    u.continuous u.hasCompactSupport (1 / 2 : ℂ)
  have hminus := integral_cexp_mul_translateCombo (polarMultiplierWeight h) (polarMultiplierShift h)
    u.continuous u.hasCompactSupport (-1 / 2 : ℂ)
  rw [translateSymbol_polarMultiplier, polarMultiplierSymbol_half, zero_mul] at hplus
  rw [translateSymbol_polarMultiplier, polarMultiplierSymbol_neg_half, zero_mul] at hminus
  constructor
  · rw [← hplus]
    congr 1
    funext x
    rw [Complex.ofReal_exp]
    push_cast
    rfl
  · rw [← hminus]
    congr 1
    funext x
    rw [Complex.ofReal_exp]
    push_cast
    rfl

theorem deriv_polarTranslate {a : SuzukiPositiveAperture} (u : CCMComplexSmoothInteriorSource a)
    {h : ℝ} (hh : 0 < h) :
    deriv (u.polarTranslate hh) =
      translateCombo (polarMultiplierWeight h) (polarMultiplierShift h) (deriv u) := by
  change deriv (translateCombo (polarMultiplierWeight h) (polarMultiplierShift h) u) = _
  exact deriv_translateCombo _ _ (u.smooth.differentiable (by simp))

/-! ## The CCM quadratic of a smooth source is Suzuki's form of its derivative -/

theorem ccmRestrictedWeilSourceQuadratic_toCCMFormVector_eq_smoothForm
    {a : SuzukiPositiveAperture} (u : CCMComplexSmoothInteriorSource a) :
    ccmRestrictedWeilSourceQuadratic a u.toCCMFormVector =
      (suzukiScrewSmoothForm u.toSuzukiSmoothCompactTest.toDerivativeZeroMean
        u.toSuzukiSmoothCompactTest.toDerivativeZeroMean).re := by
  rw [← ccmRestrictedWeilForm_self_re_eq_source,
    ccmRestrictedWeilForm_complexSmooth_eq_screwOperator,
    inner_suzukiScrewZeroMeanOperator_complexSmoothDerivative_eq_smoothForm]

/-- Suzuki's smooth form depends only on the underlying function. -/
theorem suzukiScrewSmoothForm_congr_coe {a b : ℝ} (φ : SuzukiSmoothZeroMeanTest a)
    (ψ : SuzukiSmoothZeroMeanTest b) (hfun : (φ : ℝ → ℂ) = ψ) :
    suzukiScrewSmoothForm φ φ = suzukiScrewSmoothForm ψ ψ := by
  unfold suzukiScrewSmoothForm
  rw [hfun]

/-- Nonnegative pole-vanishing ground energy makes the CCM quadratic nonnegative on every
pole-vanishing vector. -/
theorem ccmRestrictedWeilSourceQuadratic_nonneg_of_polarGroundEnergy_nonneg
    {a : SuzukiPositiveAperture} (hμ : 0 ≤ ccmRestrictedWeilPolarGroundEnergy a)
    {u : CCMArchimedeanFormDomain a} (hu : IsPolarConstrained a u) :
    0 ≤ ccmRestrictedWeilSourceQuadratic a u := by
  have h := ccmRestrictedWeilPolarGroundEnergy_mul_le a u hu
  have h0 : 0 ≤ ccmRestrictedWeilPolarGroundEnergy a * ‖ccmArchimedeanFormToAperture a u‖ ^ (2 : ℕ) :=
    mul_nonneg hμ (sq_nonneg _)
  linarith

/-! ## Primitives of zero-mean tests -/

/-- The primitive `x ↦ ∫_{−a−1}^x φ` of a zero-mean smooth test. -/
def SuzukiSmoothZeroMeanTest.zeroMeanPrimitive {a : ℝ} (φ : SuzukiSmoothZeroMeanTest a) (x : ℝ) : ℂ :=
  ∫ t in (-a - 1)..x, (φ : ℝ → ℂ) t

theorem SuzukiSmoothZeroMeanTest.hasDerivAt_zeroMeanPrimitive {a : ℝ} (φ : SuzukiSmoothZeroMeanTest a)
    (x : ℝ) : HasDerivAt φ.zeroMeanPrimitive (φ x) x :=
  intervalIntegral.integral_hasDerivAt_right (φ.continuous.intervalIntegrable _ _)
    (φ.continuous.stronglyMeasurableAtFilter _ _) φ.continuous.continuousAt

theorem SuzukiSmoothZeroMeanTest.deriv_zeroMeanPrimitive {a : ℝ} (φ : SuzukiSmoothZeroMeanTest a) :
    deriv φ.zeroMeanPrimitive = φ :=
  funext fun x => (φ.hasDerivAt_zeroMeanPrimitive x).deriv

theorem SuzukiSmoothZeroMeanTest.contDiff_zeroMeanPrimitive {a : ℝ} (φ : SuzukiSmoothZeroMeanTest a) :
    ContDiff ℝ (⊤ : ℕ∞) φ.zeroMeanPrimitive := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun x => (φ.hasDerivAt_zeroMeanPrimitive x).differentiableAt, ?_⟩
  rw [φ.deriv_zeroMeanPrimitive]
  exact φ.smooth

theorem SuzukiSmoothZeroMeanTest.apply_eq_zero_of_notMem {a : ℝ} (φ : SuzukiSmoothZeroMeanTest a)
    {t : ℝ} (ht : t ∉ Icc (-a) a) : φ t = 0 := by
  by_contra h
  exact ht (φ.support_subset (Function.mem_support.mpr h))

theorem SuzukiSmoothZeroMeanTest.zeroMeanPrimitive_eq_zero_of_lt {a : ℝ} (φ : SuzukiSmoothZeroMeanTest a)
    {x : ℝ} (hx : x < -a) : φ.zeroMeanPrimitive x = 0 := by
  unfold SuzukiSmoothZeroMeanTest.zeroMeanPrimitive
  have hzero : EqOn (φ : ℝ → ℂ) 0 (uIcc (-a - 1) x) := by
    intro t ht
    rw [uIcc, mem_Icc] at ht
    apply φ.apply_eq_zero_of_notMem
    rw [mem_Icc]
    intro hmem
    have hle : t ≤ max (-a - 1) x := ht.2
    have : max (-a - 1) x < -a := max_lt (by linarith) hx
    linarith [hmem.1]
  rw [intervalIntegral.integral_congr hzero]
  simp

theorem SuzukiSmoothZeroMeanTest.zeroMeanPrimitive_eq_zero_of_gt {a : ℝ} (φ : SuzukiSmoothZeroMeanTest a)
    {x : ℝ} (hx : a < x) : φ.zeroMeanPrimitive x = 0 := by
  rcases le_or_gt (-a - 1) x with hle | hlt
  · unfold SuzukiSmoothZeroMeanTest.zeroMeanPrimitive
    rw [intervalIntegral.integral_of_le hle,
      setIntegral_eq_integral_of_forall_compl_eq_zero]
    · exact φ.integral_zero
    · intro t ht
      apply φ.apply_eq_zero_of_notMem
      intro hmem
      rw [mem_Icc] at hmem
      apply ht
      rw [mem_Ioc]
      constructor <;> linarith
  · exact φ.zeroMeanPrimitive_eq_zero_of_lt (by linarith)

theorem SuzukiSmoothZeroMeanTest.support_zeroMeanPrimitive_subset {a : ℝ}
    (φ : SuzukiSmoothZeroMeanTest a) : Function.support φ.zeroMeanPrimitive ⊆ Icc (-a) a := by
  intro x hx
  rw [Function.mem_support] at hx
  rw [mem_Icc]
  constructor
  · by_contra h
    exact hx (φ.zeroMeanPrimitive_eq_zero_of_lt (by linarith))
  · by_contra h
    exact hx (φ.zeroMeanPrimitive_eq_zero_of_gt (by linarith))

/-- The primitive as a smooth interior source at any aperture exceeding `a`. -/
def SuzukiSmoothZeroMeanTest.zeroMeanPrimitiveSource {a : ℝ} (φ : SuzukiSmoothZeroMeanTest a)
    (A : SuzukiPositiveAperture) (hA : a < A.1) : CCMComplexSmoothInteriorSource A where
  toFun := φ.zeroMeanPrimitive
  smooth := φ.contDiff_zeroMeanPrimitive
  hasCompactSupport :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _)
      (closure_minimal φ.support_zeroMeanPrimitive_subset isClosed_Icc)
  tsupport_subset := by
    refine (closure_minimal φ.support_zeroMeanPrimitive_subset isClosed_Icc).trans ?_
    intro x hx
    rw [mem_Icc] at hx
    rw [mem_Ioo]
    constructor <;> linarith

@[simp] theorem SuzukiSmoothZeroMeanTest.zeroMeanPrimitiveSource_apply {a : ℝ}
    (φ : SuzukiSmoothZeroMeanTest a) (A : SuzukiPositiveAperture) (hA : a < A.1) (x : ℝ) :
    φ.zeroMeanPrimitiveSource A hA x = φ.zeroMeanPrimitive x := rfl

/-! ## The multiplied zero-mean test -/

/-- `M∗φ` as a zero-mean smooth test on `[-(a+2h), a+2h]`. -/
def SuzukiSmoothZeroMeanTest.polarTranslateTest {a : ℝ} (φ : SuzukiSmoothZeroMeanTest a)
    {h : ℝ} (hh : 0 < h) : SuzukiSmoothZeroMeanTest (a + 2 * h) where
  toFun := translateCombo (polarMultiplierWeight h) (polarMultiplierShift h) φ
  smooth := contDiff_translateCombo _ _ φ.smooth
  support_subset := support_translateCombo_subset _ _ φ.support_subset (polarMultiplierShift_abs_le hh)
  integral_zero := by
    rw [integral_translateCombo _ _ φ.continuous φ.hasCompactSupport,
      translateSymbol_polarMultiplier, polarMultiplierSymbol_zero, zero_mul]

@[simp] theorem SuzukiSmoothZeroMeanTest.polarTranslateTest_apply {a : ℝ}
    (φ : SuzukiSmoothZeroMeanTest a) {h : ℝ} (hh : 0 < h) (x : ℝ) :
    φ.polarTranslateTest hh x =
      translateCombo (polarMultiplierWeight h) (polarMultiplierShift h) φ x := rfl

/-- The derivative test of the multiplied primitive is the multiplied test. -/
theorem deriv_polarTranslate_zeroMeanPrimitiveSource {a : ℝ} (φ : SuzukiSmoothZeroMeanTest a)
    (A : SuzukiPositiveAperture) (hA : a < A.1) {h : ℝ} (hh : 0 < h) :
    ((φ.zeroMeanPrimitiveSource A hA).polarTranslate hh).toSuzukiSmoothCompactTest.toDerivativeZeroMean
      = ((φ.polarTranslateTest hh : SuzukiSmoothZeroMeanTest (a + 2 * h)) : ℝ → ℂ) := by
  rw [SuzukiSmoothCompactTest.coe_toDerivativeZeroMean]
  show deriv (translateCombo (polarMultiplierWeight h) (polarMultiplierShift h) φ.zeroMeanPrimitive) =
    translateCombo (polarMultiplierWeight h) (polarMultiplierShift h) φ
  rw [deriv_translateCombo _ _ (fun x => (φ.hasDerivAt_zeroMeanPrimitive x).differentiableAt),
    φ.deriv_zeroMeanPrimitive]

/-- **Constrained positivity at the enlarged aperture gives Suzuki positivity of every multiplied
zero-mean test.** -/
theorem suzukiScrewSmoothForm_polarTranslateTest_re_nonneg_of_polarGroundEnergy_nonneg
    {a : ℝ} (φ : SuzukiSmoothZeroMeanTest a) (A : SuzukiPositiveAperture) (hA : a < A.1)
    {h : ℝ} (hh : 0 < h)
    (hμ : 0 ≤ ccmRestrictedWeilPolarGroundEnergy (A.enlarge h hh)) :
    0 ≤ (suzukiScrewSmoothForm (φ.polarTranslateTest hh) (φ.polarTranslateTest hh)).re := by
  have hq := ccmRestrictedWeilSourceQuadratic_nonneg_of_polarGroundEnergy_nonneg hμ
    (isPolarConstrained_polarTranslate (φ.zeroMeanPrimitiveSource A hA) hh)
  rw [ccmRestrictedWeilSourceQuadratic_toCCMFormVector_eq_smoothForm,
    suzukiScrewSmoothForm_congr_coe _ (φ.polarTranslateTest hh)
      (deriv_polarTranslate_zeroMeanPrimitiveSource φ A hA hh)] at hq
  exact hq

/-! ## Ray coefficients of the multiplied test -/

theorem integrable_cexp_mul_test {a : ℝ} (φ : SuzukiSmoothZeroMeanTest a) (z : ℂ) :
    Integrable (fun u : ℝ => Complex.exp (z * (u : ℂ)) * (φ : ℝ → ℂ) u) := by
  have hc : Continuous fun u : ℝ => Complex.exp (z * (u : ℂ)) * (φ : ℝ → ℂ) u := by
    have := φ.continuous
    fun_prop
  exact hc.integrable_of_hasCompactSupport (hasCompactSupport_mul_of_right φ.hasCompactSupport _)

/-- `∫ e^{zu} φ = B_z(φ)` for a zero-mean test, where `B_z(φ) = ∫ (e^{zu} − 1) φ`. -/
theorem integral_cexp_mul_test_eq {a : ℝ} (φ : SuzukiSmoothZeroMeanTest a) (z : ℂ) :
    ∫ u : ℝ, Complex.exp (z * (u : ℂ)) * (φ : ℝ → ℂ) u =
      ∫ u : ℝ, (Complex.exp (z * (u : ℂ)) - 1) * (φ : ℝ → ℂ) u := by
  have h1 := integrable_cexp_mul_test φ z
  have h2 := φ.integrable
  have hfun : (fun u : ℝ => (Complex.exp (z * (u : ℂ)) - 1) * (φ : ℝ → ℂ) u) =
      fun u : ℝ => Complex.exp (z * (u : ℂ)) * (φ : ℝ → ℂ) u - (φ : ℝ → ℂ) u := by
    funext u
    ring
  rw [hfun, integral_sub h1 h2, φ.integral_zero, sub_zero]

/-- The general splitting `∫ (e^{zu} − 1) g = ∫ e^{zu} g − ∫ g` for continuous compactly supported `g`. -/
theorem integral_expSlope_mul_split (z : ℂ) {g : ℝ → ℂ} (hg : Continuous g)
    (hgs : HasCompactSupport g) :
    ∫ u : ℝ, (Complex.exp (z * (u : ℂ)) - 1) * g u =
      (∫ u : ℝ, Complex.exp (z * (u : ℂ)) * g u) - ∫ u : ℝ, g u := by
  have h1 : Integrable fun u : ℝ => Complex.exp (z * (u : ℂ)) * g u :=
    (by fun_prop : Continuous fun u : ℝ => Complex.exp (z * (u : ℂ)) * g u)
      |>.integrable_of_hasCompactSupport (hasCompactSupport_mul_of_right hgs _)
  have h2 : Integrable g := hg.integrable_of_hasCompactSupport hgs
  rw [← integral_sub h1 h2]
  congr 1
  funext u
  ring

theorem suzukiTestRayCoef_eq_integral {a : ℝ} (φ : SuzukiSmoothZeroMeanTest a) (q : XiZeroCopy) :
    suzukiTestRayCoef φ q =
      ∫ u : ℝ, Complex.exp ((-(I * xiSpectralPoint q)) * (u : ℂ)) * (φ : ℝ → ℂ) u := by
  unfold suzukiTestRayCoef
  have hfun : (fun u : ℝ => (Complex.exp (-(I * xiSpectralPoint q * (u : ℂ))) - 1) * (φ : ℝ → ℂ) u) =
      fun u : ℝ => (Complex.exp ((-(I * xiSpectralPoint q)) * (u : ℂ)) - 1) * (φ : ℝ → ℂ) u := by
    funext u
    ring_nf
  rw [hfun, integral_expSlope_mul_split _ φ.continuous φ.hasCompactSupport, φ.integral_zero,
    sub_zero]

theorem suzukiTestRayCoefBar_eq_integral {a : ℝ} (φ : SuzukiSmoothZeroMeanTest a)
    (q : XiZeroCopy) :
    suzukiTestRayCoefBar φ q =
      ∫ t : ℝ, Complex.exp ((I * xiSpectralPoint q) * (t : ℂ)) *
        (starRingEnd ℂ) ((φ : ℝ → ℂ) t) := by
  unfold suzukiTestRayCoefBar
  have hcont : Continuous fun x : ℝ => (starRingEnd ℂ) ((φ : ℝ → ℂ) x) :=
    Complex.continuous_conj.comp φ.continuous
  have hsupp : HasCompactSupport fun x : ℝ => (starRingEnd ℂ) ((φ : ℝ → ℂ) x) :=
    φ.hasCompactSupport.mono fun x hx => by
      rw [Function.mem_support] at hx ⊢
      intro h0
      exact hx (by rw [h0, map_zero])
  have hint0 : ∫ x : ℝ, (starRingEnd ℂ) ((φ : ℝ → ℂ) x) = 0 := by
    rw [integral_conj, φ.integral_zero, map_zero]
  rw [integral_expSlope_mul_split _ hcont hsupp, hint0, sub_zero]

theorem suzukiTestRayCoef_polarTranslateTest {a : ℝ} (φ : SuzukiSmoothZeroMeanTest a)
    {h : ℝ} (hh : 0 < h) (q : XiZeroCopy) :
    suzukiTestRayCoef (φ.polarTranslateTest hh) q =
      polarMultiplierSpectral h (xiSpectralPoint q) * suzukiTestRayCoef φ q := by
  rw [suzukiTestRayCoef_eq_integral, suzukiTestRayCoef_eq_integral]
  change ∫ u : ℝ, Complex.exp ((-(I * xiSpectralPoint q)) * (u : ℂ)) *
      translateCombo (polarMultiplierWeight h) (polarMultiplierShift h) φ u = _
  rw [integral_cexp_mul_translateCombo _ _ φ.continuous φ.hasCompactSupport,
    translateSymbol_polarMultiplier, polarMultiplierSymbol_neg_I_mul]

theorem suzukiTestRayCoefBar_polarTranslateTest {a : ℝ} (φ : SuzukiSmoothZeroMeanTest a)
    {h : ℝ} (hh : 0 < h) (q : XiZeroCopy) :
    suzukiTestRayCoefBar (φ.polarTranslateTest hh) q =
      polarMultiplierSpectral h (xiSpectralPoint q) * suzukiTestRayCoefBar φ q := by
  rw [suzukiTestRayCoefBar_eq_integral, suzukiTestRayCoefBar_eq_integral]
  have hconj : (fun t : ℝ => (starRingEnd ℂ) ((φ.polarTranslateTest hh : ℝ → ℂ) t)) =
      translateCombo (polarMultiplierWeight h) (polarMultiplierShift h)
        (fun x => (starRingEnd ℂ) ((φ : ℝ → ℂ) x)) := by
    funext t
    change (starRingEnd ℂ) (translateCombo _ _ φ t) = _
    unfold translateCombo
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, Complex.conj_ofReal]
  have hcont : Continuous fun x : ℝ => (starRingEnd ℂ) ((φ : ℝ → ℂ) x) :=
    Complex.continuous_conj.comp φ.continuous
  have hsupp : HasCompactSupport fun x : ℝ => (starRingEnd ℂ) ((φ : ℝ → ℂ) x) :=
    φ.hasCompactSupport.mono fun x hx => by
      rw [Function.mem_support] at hx ⊢
      intro h0
      exact hx (by rw [h0, map_zero])
  have hfun : (fun t : ℝ => Complex.exp ((I * xiSpectralPoint q) * (t : ℂ)) *
      (starRingEnd ℂ) ((φ.polarTranslateTest hh : ℝ → ℂ) t)) =
      fun t : ℝ => Complex.exp ((I * xiSpectralPoint q) * (t : ℂ)) *
        translateCombo (polarMultiplierWeight h) (polarMultiplierShift h)
          (fun x => (starRingEnd ℂ) ((φ : ℝ → ℂ) x)) t := by
    funext t
    rw [← hconj]
  rw [hfun, integral_cexp_mul_translateCombo _ _ hcont hsupp, translateSymbol_polarMultiplier,
    polarMultiplierSymbol_I_mul]

end

end RHTower
