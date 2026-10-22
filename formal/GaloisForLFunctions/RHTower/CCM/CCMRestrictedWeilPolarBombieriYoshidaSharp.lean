import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilPolarBombieriYoshidaQuantitative

/-!
# The sharp excess cap for the constrained ground energy

Translating a zero-mean test does not change Suzuki's screw form: each ray coefficient acquires
the factor `e^{i z_q s}`, the reflected coefficient acquires `e^{-i z_q s}`, and their product is
unchanged.  Centring the two-bump test `b_t − b_0` at `±t/2` therefore keeps its form value while
halving the aperture needed to host it.  Feeding the centred polar-translated source into the
constrained Rayleigh floor shows that an exponential lower bound `μ₀(B) ≥ −C e^{εB}` on the
pole-vanishing ground energy forces the polar-weighted screw divisor to satisfy
`Re Φ(t) ≥ −K e^{(ε/2 + δ) t}`, and the threshold Widder--Landau engine then confines every Xi
zero copy to `|Im z_q| ≤ ε/2`.  Together with the attained-top negativity
`μ₀(B) ≤ −c e^{2ΘB}/B³`, the exponential rate of `−μ₀` and twice the top excess bound each other.
-/

open Complex MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

/-! ## Translation of zero-mean tests -/

/-- The translate `x ↦ φ(x + s)` of a zero-mean test, hosted at any aperture containing the
shifted support. -/
def SuzukiSmoothZeroMeanTest.translate {a : ℝ} (φ : SuzukiSmoothZeroMeanTest a) (s : ℝ)
    {l r a' : ℝ} (hsupp : Function.support (φ : ℝ → ℂ) ⊆ Icc l r)
    (hfit : Icc (l - s) (r - s) ⊆ Icc (-a') a') : SuzukiSmoothZeroMeanTest a' where
  toFun := fun x => (φ : ℝ → ℂ) (x + s)
  smooth := φ.smooth.comp (contDiff_id.add contDiff_const)
  support_subset := by
    intro x hx
    have hxs : x + s ∈ Icc l r := hsupp (by simpa [Function.mem_support] using hx)
    apply hfit
    rw [mem_Icc] at hxs ⊢
    constructor <;> linarith
  integral_zero := by
    show ∫ x : ℝ, (φ : ℝ → ℂ) (x + s) = 0
    rw [integral_add_right_eq_self (fun x => (φ : ℝ → ℂ) x) s]
    exact φ.integral_zero

@[simp] theorem SuzukiSmoothZeroMeanTest.translate_apply {a : ℝ} (φ : SuzukiSmoothZeroMeanTest a)
    (s : ℝ) {l r a' : ℝ} (hsupp : Function.support (φ : ℝ → ℂ) ⊆ Icc l r)
    (hfit : Icc (l - s) (r - s) ⊆ Icc (-a') a') (x : ℝ) :
    (φ.translate s hsupp hfit : ℝ → ℂ) x = (φ : ℝ → ℂ) (x + s) := rfl

/-- Translation law for exponential moments of a zero-integral compactly supported function. -/
theorem integral_exp_sub_one_mul_translate {ψ : ℝ → ℂ} (hψ : Continuous ψ)
    (hc : HasCompactSupport ψ) (h0 : ∫ u : ℝ, ψ u = 0) (w : ℂ) (s : ℝ) :
    ∫ u : ℝ, (cexp (w * u) - 1) * ψ (u + s)
      = cexp (-(w * s)) * ∫ u : ℝ, (cexp (w * u) - 1) * ψ u := by
  have hcont : Continuous fun u : ℝ => cexp (w * u) * ψ u := by fun_prop
  have hint : Integrable (fun u : ℝ => cexp (w * u) * ψ u) :=
    hcont.integrable_of_hasCompactSupport hc.mul_left
  have hintψ : Integrable ψ := hψ.integrable_of_hasCompactSupport hc
  have hsplit : ∀ c : ℂ, ∫ u : ℝ, (c * cexp (w * u) - 1) * ψ u
      = c * ∫ u : ℝ, cexp (w * u) * ψ u := by
    intro c
    have hfun : (fun u : ℝ => (c * cexp (w * u) - 1) * ψ u)
        = fun u : ℝ => c * (cexp (w * u) * ψ u) - ψ u := by
      funext u; ring
    rw [hfun, integral_sub (hint.const_mul c) hintψ, integral_const_mul, h0, sub_zero]
  have hlhs : (fun u : ℝ => (cexp (w * u) - 1) * ψ (u + s))
      = fun u : ℝ => (fun v : ℝ => (cexp (-(w * s)) * cexp (w * v) - 1) * ψ v) (u + s) := by
    funext u
    have hexp : cexp (w * u) = cexp (-(w * s)) * cexp (w * ((u + s : ℝ) : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    simp only
    rw [hexp]
  rw [hlhs, integral_add_right_eq_self
    (fun v : ℝ => (cexp (-(w * s)) * cexp (w * v) - 1) * ψ v) s, hsplit]
  have h1 : ∫ u : ℝ, (cexp (w * u) - 1) * ψ u = ∫ u : ℝ, cexp (w * u) * ψ u := by
    have := hsplit 1
    simpa using this
  rw [h1]

/-- The ray coefficient of a translate picks up the factor `e^{i z_q s}`. -/
theorem suzukiTestRayCoef_translate {a : ℝ} (φ : SuzukiSmoothZeroMeanTest a) (s : ℝ)
    {l r a' : ℝ} (hsupp : Function.support (φ : ℝ → ℂ) ⊆ Icc l r)
    (hfit : Icc (l - s) (r - s) ⊆ Icc (-a') a') (q : XiZeroCopy) :
    suzukiTestRayCoef (φ.translate s hsupp hfit) q
      = cexp (I * xiSpectralPoint q * s) * suzukiTestRayCoef φ q := by
  have h := integral_exp_sub_one_mul_translate φ.continuous φ.hasCompactSupport φ.integral_zero
    (-(I * xiSpectralPoint q)) s
  simp only [neg_mul, neg_neg] at h
  unfold suzukiTestRayCoef
  show ∫ u : ℝ, (cexp (-(I * xiSpectralPoint q * (u : ℂ))) - 1) * (φ : ℝ → ℂ) (u + s) = _
  exact h

/-- The reflected ray coefficient of a translate picks up the factor `e^{-i z_q s}`. -/
theorem suzukiTestRayCoefBar_translate {a : ℝ} (φ : SuzukiSmoothZeroMeanTest a) (s : ℝ)
    {l r a' : ℝ} (hsupp : Function.support (φ : ℝ → ℂ) ⊆ Icc l r)
    (hfit : Icc (l - s) (r - s) ⊆ Icc (-a') a') (q : XiZeroCopy) :
    suzukiTestRayCoefBar (φ.translate s hsupp hfit) q
      = cexp (-(I * xiSpectralPoint q * s)) * suzukiTestRayCoefBar φ q := by
  have hψc : Continuous fun t : ℝ => (starRingEnd ℂ) ((φ : ℝ → ℂ) t) :=
    Complex.continuous_conj.comp φ.continuous
  have hψs : HasCompactSupport fun t : ℝ => (starRingEnd ℂ) ((φ : ℝ → ℂ) t) :=
    φ.hasCompactSupport.comp_left (map_zero _)
  have hψ0 : ∫ t : ℝ, (starRingEnd ℂ) ((φ : ℝ → ℂ) t) = 0 := by
    rw [integral_conj, φ.integral_zero, map_zero]
  have h := integral_exp_sub_one_mul_translate hψc hψs hψ0 (I * xiSpectralPoint q) s
  unfold suzukiTestRayCoefBar
  show ∫ t : ℝ, (cexp (I * xiSpectralPoint q * (t : ℂ)) - 1)
      * (starRingEnd ℂ) ((φ : ℝ → ℂ) (t + s)) = _
  exact h

/-- **Translation invariance of the screw form on zero-mean tests.** -/
theorem suzukiScrewSmoothForm_translate {a : ℝ} (φ : SuzukiSmoothZeroMeanTest a) (s : ℝ)
    {l r a' : ℝ} (hsupp : Function.support (φ : ℝ → ℂ) ⊆ Icc l r)
    (hfit : Icc (l - s) (r - s) ⊆ Icc (-a') a') :
    suzukiScrewSmoothForm (φ.translate s hsupp hfit) (φ.translate s hsupp hfit)
      = suzukiScrewSmoothForm φ φ := by
  rw [suzukiScrewSmoothForm_eq_tsum, suzukiScrewSmoothForm_eq_tsum]
  congr 1
  funext q
  rw [suzukiTestRayCoef_translate, suzukiTestRayCoefBar_translate]
  have hunit : cexp (-(I * xiSpectralPoint q * s)) * cexp (I * xiSpectralPoint q * s) = 1 := by
    rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
  calc cexp (-(I * xiSpectralPoint q * s)) * suzukiTestRayCoefBar φ q
        * (cexp (I * xiSpectralPoint q * s) * suzukiTestRayCoef φ q) / xiSpectralPoint q ^ 2
      = (cexp (-(I * xiSpectralPoint q * s)) * cexp (I * xiSpectralPoint q * s))
        * (suzukiTestRayCoefBar φ q * suzukiTestRayCoef φ q) / xiSpectralPoint q ^ 2 := by ring
    _ = _ := by rw [hunit, one_mul]

/-- The polar translate multiplier commutes with translation. -/
theorem coe_polarTranslateTest_translate {a : ℝ} (φ : SuzukiSmoothZeroMeanTest a) (s : ℝ)
    {l r a' : ℝ} (hsupp : Function.support (φ : ℝ → ℂ) ⊆ Icc l r)
    (hfit : Icc (l - s) (r - s) ⊆ Icc (-a') a') {h : ℝ} (hh : 0 < h) :
    ((φ.translate s hsupp hfit).polarTranslateTest hh : ℝ → ℂ)
      = fun x => (φ.polarTranslateTest hh : ℝ → ℂ) (x + s) := by
  funext x
  show translateCombo (polarMultiplierWeight h) (polarMultiplierShift h)
      (φ.translate s hsupp hfit) x
    = translateCombo (polarMultiplierWeight h) (polarMultiplierShift h) φ (x + s)
  unfold translateCombo
  refine Finset.sum_congr rfl fun k _ => ?_
  show (polarMultiplierWeight h k : ℂ) * (φ : ℝ → ℂ) (x - polarMultiplierShift h k + s)
    = (polarMultiplierWeight h k : ℂ) * (φ : ℝ → ℂ) (x + s - polarMultiplierShift h k)
  rw [show x - polarMultiplierShift h k + s = x + s - polarMultiplierShift h k by ring]

/-- The screw form of the polar-translated translate equals that of the polar translate. -/
theorem suzukiScrewSmoothForm_polarTranslateTest_translate {a : ℝ}
    (φ : SuzukiSmoothZeroMeanTest a) (s : ℝ) {l r a' : ℝ}
    (hsupp : Function.support (φ : ℝ → ℂ) ⊆ Icc l r)
    (hfit : Icc (l - s) (r - s) ⊆ Icc (-a') a') {h : ℝ} (hh : 0 < h) :
    suzukiScrewSmoothForm ((φ.translate s hsupp hfit).polarTranslateTest hh)
        ((φ.translate s hsupp hfit).polarTranslateTest hh)
      = suzukiScrewSmoothForm (φ.polarTranslateTest hh) (φ.polarTranslateTest hh) := by
  have hfit' : Icc (-(a + 2 * h) - s) (a + 2 * h - s)
      ⊆ Icc (-(a + 2 * h + |s|)) (a + 2 * h + |s|) := by
    intro x hx
    rw [mem_Icc] at hx ⊢
    constructor <;> linarith [le_abs_self s, neg_le_abs s]
  rw [suzukiScrewSmoothForm_congr_coe _
      ((φ.polarTranslateTest hh).translate s (φ.polarTranslateTest hh).support_subset hfit')
      (coe_polarTranslateTest_translate φ s hsupp hfit hh),
    suzukiScrewSmoothForm_translate]

/-! ## The centred two-bump source -/

/-- The two-bump test is supported within one unit of the segment between its bump centres. -/
theorem twoBumpSeq_support_subset (t : ℝ) (n : ℕ) :
    Function.support (twoBumpSeq t n : ℝ → ℂ) ⊆ Icc (min 0 t - 1) (max 0 t + 1) := by
  intro x hx
  rw [Function.mem_support, twoBumpSeq_apply] at hx
  have hε1 := twoBumpEps_lt_one n
  have hor : suzukiCenteredBump (twoBumpEps_pos n) t x ≠ 0
      ∨ suzukiCenteredBump (twoBumpEps_pos n) 0 x ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hx
    rw [hcon.1, hcon.2, sub_zero]
    simp
  rw [mem_Icc]
  rcases hor with h | h
  · have := abs_sub_center_le_of_suzukiCenteredBump_ne_zero (twoBumpEps_pos n) h
    rw [abs_le] at this
    constructor <;> linarith [min_le_right 0 t, le_max_right 0 t]
  · have := abs_sub_center_le_of_suzukiCenteredBump_ne_zero (twoBumpEps_pos n) h
    rw [abs_le] at this
    constructor <;> linarith [min_le_left 0 t, le_max_left 0 t]

/-- Shifting the bump segment by `−t/2` fits it into the aperture `|t|/2 + 2`. -/
theorem twoBumpFit (t : ℝ) :
    Icc (min 0 t - 1 - t / 2) (max 0 t + 1 - t / 2) ⊆ Icc (-(|t| / 2 + 2)) (|t| / 2 + 2) := by
  intro x hx
  rw [mem_Icc] at hx ⊢
  rcases le_total 0 t with ht | ht
  · rw [min_eq_left ht, max_eq_right ht] at hx
    rw [abs_of_nonneg ht]
    constructor <;> linarith
  · rw [min_eq_right ht, max_eq_left ht] at hx
    rw [abs_of_nonpos ht]
    constructor <;> linarith

/-- The centred two-bump test, hosted at the aperture `|t|/2 + 2`. -/
def twoBumpSeqC (t : ℝ) (n : ℕ) : SuzukiSmoothZeroMeanTest (|t| / 2 + 2) :=
  (twoBumpSeq t n).translate (t / 2) (twoBumpSeq_support_subset t n) (twoBumpFit t)

/-- The centred aperture `|t|/2 + 3`. -/
def twoBumpApertureC (t : ℝ) : SuzukiPositiveAperture := ⟨|t| / 2 + 3, by positivity⟩

theorem twoBumpApertureC_gt (t : ℝ) : |t| / 2 + 2 < (twoBumpApertureC t).1 := by
  show |t| / 2 + 2 < |t| / 2 + 3
  linarith

/-- The polar-translated primitive source of the centred two-bump test. -/
def twoBumpSourceC (t : ℝ) (n : ℕ) :
    CCMComplexSmoothInteriorSource ((twoBumpApertureC t).enlarge 1 one_pos) :=
  ((twoBumpSeqC t n).zeroMeanPrimitiveSource (twoBumpApertureC t)
    (twoBumpApertureC_gt t)).polarTranslate one_pos

theorem suzukiScrewSmoothForm_twoBumpSeqC (t : ℝ) (n : ℕ) :
    suzukiScrewSmoothForm ((twoBumpSeqC t n).polarTranslateTest one_pos)
        ((twoBumpSeqC t n).polarTranslateTest one_pos)
      = suzukiScrewSmoothForm ((twoBumpSeq t n).polarTranslateTest one_pos)
        ((twoBumpSeq t n).polarTranslateTest one_pos) :=
  suzukiScrewSmoothForm_polarTranslateTest_translate (twoBumpSeq t n) (t / 2)
    (twoBumpSeq_support_subset t n) (twoBumpFit t) one_pos

theorem integral_norm_twoBumpSeqC_le (t : ℝ) (n : ℕ) :
    ∫ u : ℝ, ‖(twoBumpSeqC t n : ℝ → ℂ) u‖ ≤ 2 := by
  show ∫ u : ℝ, ‖(twoBumpSeq t n : ℝ → ℂ) (u + t / 2)‖ ≤ 2
  rw [integral_add_right_eq_self (fun u => ‖(twoBumpSeq t n : ℝ → ℂ) u‖) (t / 2)]
  exact integral_norm_twoBumpSeq_le t n

/-- Pointwise bound on the centred source: `5 (1 + cosh ½) · 2`. -/
theorem norm_twoBumpSourceC_le (t : ℝ) (n : ℕ) (x : ℝ) :
    ‖(twoBumpSourceC t n : ℝ → ℂ) x‖ ≤ 5 * (1 + Real.cosh (1 / 2)) * 2 := by
  have hL1 := integral_norm_twoBumpSeqC_le t n
  have hprim : ∀ y : ℝ, ‖(twoBumpSeqC t n).zeroMeanPrimitive y‖ ≤ 2 :=
    fun y => (norm_zeroMeanPrimitive_le_integral_norm _ y).trans hL1
  change ‖translateCombo (polarMultiplierWeight 1) (polarMultiplierShift 1)
    (twoBumpSeqC t n).zeroMeanPrimitive x‖ ≤ _
  unfold translateCombo
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ k : Fin 5, ‖(polarMultiplierWeight 1 k : ℂ)
      * (twoBumpSeqC t n).zeroMeanPrimitive (x - polarMultiplierShift 1 k)‖
      ≤ (1 + Real.cosh (1 / 2)) * 2 := by
    intro k
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul (abs_polarMultiplierWeight_le k) (hprim _) (norm_nonneg _) (by positivity)
  calc ∑ k : Fin 5, ‖(polarMultiplierWeight 1 k : ℂ)
        * (twoBumpSeqC t n).zeroMeanPrimitive (x - polarMultiplierShift 1 k)‖
      ≤ ∑ _k : Fin 5, (1 + Real.cosh (1 / 2)) * 2 := Finset.sum_le_sum fun k _ => hterm k
    _ = 5 * (1 + Real.cosh (1 / 2)) * 2 := by simp; ring

theorem twoBumpSourceC_support_subset (t : ℝ) (n : ℕ) :
    Function.support (twoBumpSourceC t n : ℝ → ℂ)
      ⊆ Icc (-(|t| / 2 + 2 + 2)) (|t| / 2 + 2 + 2) := by
  change Function.support (translateCombo (polarMultiplierWeight 1) (polarMultiplierShift 1)
    (twoBumpSeqC t n).zeroMeanPrimitive) ⊆ _
  have h := support_translateCombo_subset (polarMultiplierWeight 1) (polarMultiplierShift 1)
    (twoBumpSeqC t n).support_zeroMeanPrimitive_subset (polarMultiplierShift_abs_le one_pos)
  simpa using h

/-- **`L²` bound on the centred source**: `‖U‖² ≤ 200 (1 + cosh ½)² (|t|/2 + 4)`. -/
theorem norm_sq_twoBumpSourceC_le (t : ℝ) (n : ℕ) :
    ‖ccmArchimedeanFormToAperture ((twoBumpApertureC t).enlarge 1 one_pos)
        (twoBumpSourceC t n).toCCMFormVector‖ ^ 2
      ≤ 200 * (1 + Real.cosh (1 / 2)) ^ 2 * (|t| / 2 + 4) := by
  rw [norm_sq_toAperture_eq_integral]
  set B : ℝ := 5 * (1 + Real.cosh (1 / 2)) * 2 with hB
  have hzero : ∀ x ∉ Icc (-(|t| / 2 + 2 + 2)) (|t| / 2 + 2 + 2),
      ‖(twoBumpSourceC t n : ℝ → ℂ) x‖ ^ 2 = 0 := by
    intro x hx
    have : (twoBumpSourceC t n : ℝ → ℂ) x = 0 := by
      by_contra h
      exact hx (twoBumpSourceC_support_subset t n h)
    rw [this]
    simp
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  have hcont : Continuous fun x : ℝ => ‖(twoBumpSourceC t n : ℝ → ℂ) x‖ ^ 2 :=
    ((twoBumpSourceC t n).smooth.continuous.norm).pow 2
  calc ∫ x in Icc (-(|t| / 2 + 2 + 2)) (|t| / 2 + 2 + 2), ‖(twoBumpSourceC t n : ℝ → ℂ) x‖ ^ 2
      ≤ ∫ x in Icc (-(|t| / 2 + 2 + 2)) (|t| / 2 + 2 + 2), B ^ 2 := by
        refine setIntegral_mono_on hcont.integrableOn_Icc continuous_const.integrableOn_Icc
          measurableSet_Icc fun x _ => ?_
        exact pow_le_pow_left₀ (norm_nonneg _) (norm_twoBumpSourceC_le t n x) 2
    _ = 2 * (|t| / 2 + 4) * B ^ 2 := by
        rw [setIntegral_const, smul_eq_mul, Measure.real, Real.volume_Icc,
          ENNReal.toReal_ofReal (by linarith [abs_nonneg t])]
        ring
    _ = 200 * (1 + Real.cosh (1 / 2)) ^ 2 * (|t| / 2 + 4) := by
        rw [hB]; ring

/-! ## Transfer at half the aperture -/

/-- The ground-energy bound at the half aperture `|t|/2 + 6` controls the two-bump form. -/
theorem re_smoothForm_twoBump_ge_half {C ε : ℝ} (hC : 0 ≤ C)
    (h : ∀ B : SuzukiPositiveAperture,
      -(C * Real.exp (ε * B.1)) ≤ ccmRestrictedWeilPolarGroundEnergy B)
    (t : ℝ) (n : ℕ) :
    -(C * Real.exp (ε * (|t| / 2 + 6)) * (200 * (1 + Real.cosh (1 / 2)) ^ 2 * (|t| / 2 + 4)))
      ≤ (suzukiScrewSmoothForm ((twoBumpSeq t n).polarTranslateTest one_pos)
          ((twoBumpSeq t n).polarTranslateTest one_pos)).re := by
  set A' := (twoBumpApertureC t).enlarge 1 one_pos with hA'
  have hA'val : A'.1 = |t| / 2 + 6 := by
    show (twoBumpApertureC t).1 + 2 * 1 + 1 = |t| / 2 + 6
    show |t| / 2 + 3 + 2 * 1 + 1 = |t| / 2 + 6
    ring
  have hpol := isPolarConstrained_polarTranslate
    ((twoBumpSeqC t n).zeroMeanPrimitiveSource (twoBumpApertureC t) (twoBumpApertureC_gt t))
    one_pos
  have h1 := ccmRestrictedWeilPolarGroundEnergy_mul_le A' _ hpol
  rw [ccmRestrictedWeilSourceQuadratic_toCCMFormVector_eq_smoothForm,
    suzukiScrewSmoothForm_congr_coe _ ((twoBumpSeqC t n).polarTranslateTest one_pos)
      (deriv_polarTranslate_zeroMeanPrimitiveSource (twoBumpSeqC t n) (twoBumpApertureC t)
        (twoBumpApertureC_gt t) one_pos),
    suzukiScrewSmoothForm_twoBumpSeqC] at h1
  set n' : ℝ := ‖ccmArchimedeanFormToAperture A' (twoBumpSourceC t n).toCCMFormVector‖ ^ 2
    with hn'
  have hn'0 : 0 ≤ n' := by positivity
  have hn'le : n' ≤ 200 * (1 + Real.cosh (1 / 2)) ^ 2 * (|t| / 2 + 4) :=
    norm_sq_twoBumpSourceC_le t n
  have hμ := h A'
  rw [hA'val] at hμ
  have hE : 0 ≤ C * Real.exp (ε * (|t| / 2 + 6)) := by positivity
  calc -(C * Real.exp (ε * (|t| / 2 + 6)) * (200 * (1 + Real.cosh (1 / 2)) ^ 2 * (|t| / 2 + 4)))
      ≤ -(C * Real.exp (ε * (|t| / 2 + 6))) * n' := by nlinarith
    _ ≤ ccmRestrictedWeilPolarGroundEnergy A' * n' := mul_le_mul_of_nonneg_right hμ hn'0
    _ ≤ _ := h1

/-- The polar-weighted screw divisor inherits the half-rate exponential lower bound. -/
theorem re_weightedXiScrewDivisor_polar_ge_half {C ε : ℝ} (hC : 0 ≤ C)
    (h : ∀ B : SuzukiPositiveAperture,
      -(C * Real.exp (ε * B.1)) ≤ ccmRestrictedWeilPolarGroundEnergy B) (t : ℝ) :
    -(C * Real.exp (ε * (|t| / 2 + 6)) * (100 * (1 + Real.cosh (1 / 2)) ^ 2 * (|t| / 2 + 4)))
      ≤ (weightedXiScrewDivisor (polarSpectralWeight 1) t).re := by
  have hlim := (tendsto_suzukiScrewSmoothForm_polarTranslateTest_twoBumpSeq t one_pos)
  have hre := (Complex.continuous_re.tendsto _).comp hlim
  have hbound := ge_of_tendsto' hre (fun n => re_smoothForm_twoBump_ge_half hC h t n)
  simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero] at hbound
  linarith

/-- Excess cap `ε/2 + δ` from an exponential lower bound of rate `ε` on the ground energy. -/
theorem abs_im_le_half_add_of_polarGroundEnergy_ge {C ε δ : ℝ} (hC : 0 ≤ C) (hε0 : 0 ≤ ε)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hεδ : ε / 2 + δ < 1 / 2)
    (h : ∀ B : SuzukiPositiveAperture,
      -(C * Real.exp (ε * B.1)) ≤ ccmRestrictedWeilPolarGroundEnergy B)
    (q : XiZeroCopy) : |(xiSpectralPoint q).im| ≤ ε / 2 + δ := by
  have hh : (0 : ℝ) < 1 := one_pos
  set K : ℝ := C * Real.exp (ε * 6) * (100 * (1 + Real.cosh (1 / 2)) ^ 2) * 4 / δ with hK
  have hK0 : 0 ≤ K := by positivity
  have hlow : ∀ t : ℝ, 0 ≤ t →
      -(K * Real.exp ((ε / 2 + δ) * t)) ≤ (weightedXiScrewDivisor (polarSpectralWeight 1) t).re := by
    intro t ht
    have h1 := re_weightedXiScrewDivisor_polar_ge_half hC h t
    rw [abs_of_nonneg ht] at h1
    refine le_trans ?_ h1
    rw [neg_le_neg_iff]
    have hexp : Real.exp (ε * (t / 2 + 6)) = Real.exp (ε * 6) * Real.exp (ε / 2 * t) := by
      rw [← Real.exp_add]; congr 1; ring
    have hexp2 : Real.exp ((ε / 2 + δ) * t) = Real.exp (ε / 2 * t) * Real.exp (δ * t) := by
      rw [← Real.exp_add]; congr 1; ring
    have ht4 : t / 2 + 4 ≤ 4 * (1 + t) := by linarith
    have hone := one_add_le_exp_div (t := t) hδ hδ1
    have hpos : 0 ≤ C * Real.exp (ε * 6) * (100 * (1 + Real.cosh (1 / 2)) ^ 2) := by positivity
    have hE : 0 ≤ Real.exp (ε / 2 * t) := (Real.exp_pos _).le
    calc C * Real.exp (ε * (t / 2 + 6)) * (100 * (1 + Real.cosh (1 / 2)) ^ 2 * (t / 2 + 4))
        = (C * Real.exp (ε * 6) * (100 * (1 + Real.cosh (1 / 2)) ^ 2)) * Real.exp (ε / 2 * t)
            * (t / 2 + 4) := by
          rw [hexp]; ring
      _ ≤ (C * Real.exp (ε * 6) * (100 * (1 + Real.cosh (1 / 2)) ^ 2)) * Real.exp (ε / 2 * t)
            * (4 * (Real.exp (δ * t) / δ)) := by
          gcongr
          linarith
      _ = K * Real.exp ((ε / 2 + δ) * t) := by
          rw [hK, hexp2]
          field_simp
  exact abs_im_le_of_thr (polarSpectralWeight 1) K (ε / 2 + δ) (C := polarSymbolBound 1 ^ 2)
    (by positivity) (norm_polarSpectralWeight_le hh.le)
    (fun q q' hq => polarSpectralWeight_of_eq 1 hq)
    (fun q q' hq => polarSpectralWeight_of_neg 1 hq)
    (fun q him => polarSpectralWeight_ne_zero hh q him)
    hlow (fun t => weightedXiScrewDivisor_polar_im 1 t) (by linarith) hεδ q

/-- **Sharp excess cap.**  `μ₀(B) ≥ −C e^{εB}` for every aperture forces every Xi zero copy into
`|Im z_q| ≤ ε/2`, i.e. `|Re ρ − ½| ≤ ε/2`. -/
theorem abs_im_xiSpectralPoint_le_half_of_polarGroundEnergy_ge {C ε : ℝ} (hC : 0 ≤ C)
    (hε0 : 0 ≤ ε)
    (h : ∀ B : SuzukiPositiveAperture,
      -(C * Real.exp (ε * B.1)) ≤ ccmRestrictedWeilPolarGroundEnergy B)
    (q : XiZeroCopy) : |(xiSpectralPoint q).im| ≤ ε / 2 := by
  rcases le_or_gt (1 / 2 : ℝ) (ε / 2) with hε | hε
  · exact (abs_xiSpectralPoint_im_lt_half q).le.trans hε
  · refine le_of_forall_pos_le_add fun δ hδ => ?_
    set δ' : ℝ := min δ (min 1 ((1 / 2 - ε / 2) / 2)) with hδ'
    have hδ'pos : 0 < δ' := lt_min hδ (lt_min one_pos (by linarith))
    have hδ'1 : δ' ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
    have hδ'half : ε / 2 + δ' < 1 / 2 := by
      have : δ' ≤ (1 / 2 - ε / 2) / 2 := (min_le_right _ _).trans (min_le_right _ _)
      linarith
    have hδ'δ : δ' ≤ δ := min_le_left _ _
    exact (abs_im_le_half_add_of_polarGroundEnergy_ge hC hε0 hδ'pos hδ'1 hδ'half h q).trans
      (by linarith)

/-- **Rate law, lower half.**  Twice every excess is at most any exponential rate bounding the
ground energy from below. -/
theorem two_mul_abs_im_xiSpectralPoint_le_of_polarGroundEnergy_ge {C ε : ℝ} (hC : 0 ≤ C)
    (hε0 : 0 ≤ ε)
    (h : ∀ B : SuzukiPositiveAperture,
      -(C * Real.exp (ε * B.1)) ≤ ccmRestrictedWeilPolarGroundEnergy B)
    (q : XiZeroCopy) : 2 * |(xiSpectralPoint q).im| ≤ ε := by
  have := abs_im_xiSpectralPoint_le_half_of_polarGroundEnergy_ge hC hε0 h q
  linarith

end

end RHTower
