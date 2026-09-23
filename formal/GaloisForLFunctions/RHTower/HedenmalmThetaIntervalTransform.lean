import GaloisForLFunctions.RHTower.HedenmalmThetaKernelEnergy

/-!
# The divisor factorization of the theta interval anomaly

The rank-one anomaly of the normalized integer shift is the theta mass of a sliding interval,

`r_n(x) = i n^{-1/2} ∫_x^{x + log n} k(t) dt`.

Its completed transform factors through the completed transform of the source:

`ŵ_L(z) = (1 - e^{-izL})/(iz) · Ξ_C(z)`,

so the anomaly is a coboundary in the analytic divisor cokernel.  The proof is one integration by
parts on the line: the window has derivative `k(· + L) - k`, the boundary terms vanish because the
window inherits the exponential decay of the source, and the translated source integral is
`e^{-izL} Ξ_C(z)`.
-/

open MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

namespace HedenmalmThetaSource

open HedenmalmQuantile HedenmalmPrimeTranslation HedenmalmIntervalAnomaly

/-! ### Decay of the sliding window -/

theorem intervalMass_nonneg (a b : ℝ) : 0 ≤ intervalMass thetaSource a b :=
  setIntegral_nonneg measurableSet_Ioc fun t _ => (thetaSource.pos_k t).le

/-- **The sliding window inherits the exponential decay of the source.** -/
theorem intervalMass_le_exp {L : ℝ} (hL : 0 ≤ L) (x : ℝ) :
    intervalMass thetaSource x (x + L)
      ≤ (L * (thetaBound * Real.exp L)) * Real.exp (-|x|) := by
  have hC := thetaBound_nonneg
  have hbound : ∀ t ∈ Ioc x (x + L),
      thetaSource.k t ≤ thetaBound * Real.exp L * Real.exp (-|x|) := by
    intro t ht
    have hdist : |x - t| ≤ L := by
      rcases ht with ⟨h1, h2⟩
      rw [abs_of_nonpos (by linarith : x - t ≤ 0)]
      linarith
    have habs : |x| - L ≤ |t| := by
      have h := abs_sub_abs_le_abs_sub x t
      linarith
    have hexp : Real.exp (-|t|) ≤ Real.exp L * Real.exp (-|x|) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (by linarith)
    calc thetaSource.k t ≤ |thetaCuspFullSource t| := le_abs_self _
      _ ≤ thetaBound * Real.exp (-|t|) := abs_thetaCuspFullSource_le t
      _ ≤ thetaBound * (Real.exp L * Real.exp (-|x|)) :=
        mul_le_mul_of_nonneg_left hexp hC
      _ = thetaBound * Real.exp L * Real.exp (-|x|) := by ring
  have hconst : IntegrableOn (fun _ : ℝ => thetaBound * Real.exp L * Real.exp (-|x|))
      (Ioc x (x + L)) volume := by
    refine Measure.integrableOn_of_bounded
      (M := |thetaBound * Real.exp L * Real.exp (-|x|)|)
      (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top) aestronglyMeasurable_const ?_
    filter_upwards with t
    rw [Real.norm_eq_abs]
  have hle := setIntegral_mono_on thetaSource.integrable_k.integrableOn hconst
    measurableSet_Ioc hbound
  rw [setIntegral_const, Measure.real, Real.volume_Ioc,
    show x + L - x = L by ring, ENNReal.toReal_ofReal hL, smul_eq_mul] at hle
  calc intervalMass thetaSource x (x + L)
      ≤ L * (thetaBound * Real.exp L * Real.exp (-|x|)) := hle
    _ = L * (thetaBound * Real.exp L) * Real.exp (-|x|) := by ring

/-! ### The complexified window -/

/-- The complexified sliding window `W_L(x) = ∫_x^{x+L} k`. -/
def windowFun (L x : ℝ) : ℂ := ((intervalMass thetaSource x (x + L) : ℝ) : ℂ)

theorem norm_windowFun {L : ℝ} (hL : 0 ≤ L) (x : ℝ) :
    ‖windowFun L x‖ ≤ (L * (thetaBound * Real.exp L)) * Real.exp (-|x|) := by
  rw [windowFun, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (intervalMass_nonneg _ _)]
  exact intervalMass_le_exp hL x

theorem windowFun_eq_sub {L : ℝ} (hL : 0 ≤ L) (x : ℝ) :
    windowFun L x
      = (∫ y in Iic (x + L), (thetaSource.k y : ℂ)) - ∫ y in Iic x, (thetaSource.k y : ℂ) := by
  have hkC : Integrable (fun y : ℝ => (thetaSource.k y : ℂ)) (volume : Measure ℝ) :=
    thetaSource.integrable_k.ofReal
  have hsplit : (∫ y in Iic x, (thetaSource.k y : ℂ))
      + ∫ y in Ioc x (x + L), (thetaSource.k y : ℂ)
      = ∫ y in Iic (x + L), (thetaSource.k y : ℂ) := by
    rw [← MeasureTheory.setIntegral_union (Iic_disjoint_Ioc le_rfl) measurableSet_Ioc
      hkC.integrableOn hkC.integrableOn, Iic_union_Ioc_eq_Iic (by linarith)]
  have hre : windowFun L x = ∫ y in Ioc x (x + L), (thetaSource.k y : ℂ) := by
    rw [windowFun, intervalMass, integral_complex_ofReal]
  rw [hre, ← hsplit]
  ring

theorem hasDerivAt_windowFun {L : ℝ} (hL : 0 ≤ L) (x : ℝ) :
    HasDerivAt (windowFun L)
      ((thetaSource.k (x + L) : ℂ) - (thetaSource.k x : ℂ)) x := by
  have hkcont : Continuous (fun y : ℝ => (thetaSource.k y : ℂ)) :=
    Complex.continuous_ofReal.comp thetaSource.continuous_k
  have hkC : Integrable (fun y : ℝ => (thetaSource.k y : ℂ)) (volume : Measure ℝ) :=
    thetaSource.integrable_k.ofReal
  have hbase := hasDerivAt_setIntegral_Iic hkcont hkC
  have hshift : HasDerivAt (fun t : ℝ => ∫ y in Iic (t + L), (thetaSource.k y : ℂ))
      ((thetaSource.k (x + L) : ℂ)) x := by
    exact HasDerivAt.comp_add_const x L (hbase (x + L))
  have hmain := hshift.sub (hbase x)
  refine hmain.congr_of_eventuallyEq ?_
  filter_upwards with t
  exact windowFun_eq_sub hL t

/-! ### Integrability and the boundary terms -/

theorem continuous_windowFun {L : ℝ} (hL : 0 ≤ L) : Continuous (windowFun L) := by
  have h : Continuous fun x : ℝ =>
      thetaSource.mass * (thetaSource.cdfFun (x + L) - thetaSource.cdfFun x) :=
    continuous_const.mul ((thetaSource.continuous_cdfFun.comp
      (continuous_id.add continuous_const)).sub thetaSource.continuous_cdfFun)
  refine (Complex.continuous_ofReal.comp h).congr fun x => ?_
  show ((thetaSource.mass * (thetaSource.cdfFun (x + L) - thetaSource.cdfFun x) : ℝ) : ℂ)
    = windowFun L x
  rw [windowFun, mass_mul_cdfFun_sub thetaSource (by linarith : x ≤ x + L)]


/-- The dominating profile of the window against the source character. -/
theorem norm_windowFun_sourceChar_le {L : ℝ} (hL : 0 ≤ L) {z : ℂ} (_hz : |z.im| < 1) (x : ℝ) :
    ‖windowFun L x * sourceChar z x‖
      ≤ (L * (thetaBound * Real.exp L)) * Real.exp (-((1 - |z.im|) * |x|)) := by
  have hCL : (0 : ℝ) ≤ L * (thetaBound * Real.exp L) := by
    have := thetaBound_nonneg
    positivity
  have hkey : Real.exp (-z.im * x) ≤ Real.exp (|z.im| * |x|) := by
    refine Real.exp_le_exp.mpr ?_
    calc -z.im * x ≤ |(-z.im) * x| := le_abs_self _
      _ = |z.im| * |x| := by rw [abs_mul, abs_neg]
  rw [norm_mul, norm_sourceChar]
  calc ‖windowFun L x‖ * Real.exp (-z.im * x)
      ≤ ((L * (thetaBound * Real.exp L)) * Real.exp (-|x|)) * Real.exp (|z.im| * |x|) := by
        refine mul_le_mul (norm_windowFun hL x) hkey (Real.exp_pos _).le ?_
        positivity
    _ = (L * (thetaBound * Real.exp L)) * Real.exp (-((1 - |z.im|) * |x|)) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring

theorem integrable_windowFun_sourceChar {L : ℝ} (hL : 0 ≤ L) {z : ℂ} (hz : |z.im| < 1) :
    Integrable (fun x => windowFun L x * sourceChar z x) (volume : Measure ℝ) := by
  have hcpos : (0 : ℝ) < 1 - |z.im| := by linarith
  refine Integrable.mono'
    ((integrable_exp_neg_mul_abs_weightedEulerStripFourierAnalytic hcpos).const_mul (L * (thetaBound * Real.exp L))) ?_ ?_
  · exact ((continuous_windowFun hL).mul (continuous_sourceChar z)).aestronglyMeasurable
  · filter_upwards with x
    exact norm_windowFun_sourceChar_le hL hz x

theorem tendsto_windowFun_sourceChar {L : ℝ} (hL : 0 ≤ L) {z : ℂ} (hz : |z.im| < 1) :
    Tendsto (fun x => windowFun L x * sourceChar z x) atBot (𝓝 0)
      ∧ Tendsto (fun x => windowFun L x * sourceChar z x) atTop (𝓝 0) := by
  have hcpos : (0 : ℝ) < 1 - |z.im| := by linarith
  have hdomBot : Tendsto
      (fun x : ℝ => (L * (thetaBound * Real.exp L)) * Real.exp (-((1 - |z.im|) * |x|)))
      atBot (𝓝 0) := by
    have habs : Tendsto (fun x : ℝ => -((1 - |z.im|) * |x|)) atBot atBot :=
      tendsto_neg_atTop_atBot.comp
        ((tendsto_abs_atBot_atTop).const_mul_atTop hcpos)
    simpa using (Real.tendsto_exp_atBot.comp habs).const_mul (L * (thetaBound * Real.exp L))
  have hdomTop : Tendsto
      (fun x : ℝ => (L * (thetaBound * Real.exp L)) * Real.exp (-((1 - |z.im|) * |x|)))
      atTop (𝓝 0) := by
    have habs : Tendsto (fun x : ℝ => -((1 - |z.im|) * |x|)) atTop atBot :=
      tendsto_neg_atTop_atBot.comp
        ((tendsto_abs_atTop_atTop).const_mul_atTop hcpos)
    simpa using (Real.tendsto_exp_atBot.comp habs).const_mul (L * (thetaBound * Real.exp L))
  exact ⟨squeeze_zero_norm (fun x => norm_windowFun_sourceChar_le hL hz x) hdomBot,
    squeeze_zero_norm (fun x => norm_windowFun_sourceChar_le hL hz x) hdomTop⟩

/-! ### The translated source integral -/

theorem sourceChar_add (z : ℂ) (x L : ℝ) :
    sourceChar z (x + L) = sourceChar z x * Complex.exp (Complex.I * z * (L : ℂ)) := by
  rw [sourceChar, sourceChar, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem shifted_char_factor (c : ℂ) (L : ℝ) (z : ℂ) (x : ℝ) :
    c * sourceChar z x
      = Complex.exp (-(Complex.I * z * (L : ℂ))) * (c * sourceChar z (x + L)) := by
  have hcancel : Complex.exp (-(Complex.I * z * (L : ℂ)))
      * Complex.exp (Complex.I * z * (L : ℂ)) = 1 := by
    rw [← Complex.exp_add]
    simp
  rw [sourceChar_add]
  calc c * sourceChar z x = c * sourceChar z x * 1 := by ring
    _ = Complex.exp (-(Complex.I * z * (L : ℂ)))
        * (c * (sourceChar z x * Complex.exp (Complex.I * z * (L : ℂ)))) := by
        rw [← hcancel]; ring


theorem integral_shifted_k_sourceChar {L : ℝ} {z : ℂ} (hz : |z.im| < 1) :
    (∫ x : ℝ, (thetaSource.k (x + L) : ℂ) * sourceChar z x)
      = Complex.exp (-(Complex.I * z * (L : ℂ))) * XiC z := by
  have hg : Integrable (fun x : ℝ => (thetaSource.k x : ℂ) * sourceChar z x)
      (volume : Measure ℝ) := integrable_k_sourceChar thetaSource (hasShiftedTail_thetaSource hz)
  have hpt : ∀ x : ℝ, (thetaSource.k (x + L) : ℂ) * sourceChar z x
      = Complex.exp (-(Complex.I * z * (L : ℂ)))
        * ((thetaSource.k (x + L) : ℂ) * sourceChar z (x + L)) := by
    intro x
    exact shifted_char_factor (thetaSource.k (x + L) : ℂ) L z x
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), MeasureTheory.integral_const_mul]
  congr 1
  rw [MeasureTheory.integral_add_right_eq_self
    (fun x : ℝ => (thetaSource.k x : ℂ) * sourceChar z x) L]
  rw [← xiC_thetaSource hz, xiC]

/-! ### The divisor factorization -/

/-- **The sliding window transform factors through the completed source transform.**
`ŵ_L(z) = (1 - e^{-izL})/(iz) · Ξ_C(z)`. -/
theorem integral_windowFun_sourceChar {L : ℝ} (hL : 0 ≤ L) {z : ℂ} (hz : |z.im| < 1)
    (hz0 : z ≠ 0) :
    (∫ x : ℝ, windowFun L x * sourceChar z x)
      = (1 - Complex.exp (-(Complex.I * z * (L : ℂ)))) / (Complex.I * z) * XiC z := by
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  have hIz : Complex.I * z ≠ 0 := mul_ne_zero Complex.I_ne_zero hz0
  have hchar : ∀ x : ℝ, HasDerivAt (sourceChar z) (Complex.I * z * sourceChar z x) x := by
    intro x
    have hlin : HasDerivAt (fun t : ℝ => Complex.I * z * ((t : ℝ) : ℂ)) (Complex.I * z) x := by
      simpa using (hasDerivAt_id x).ofReal_comp.const_mul (Complex.I * z)
    refine hlin.cexp.congr_deriv ?_
    rw [sourceChar]
    ring
  have hprod : ∀ x : ℝ, HasDerivAt (fun t => windowFun L t * sourceChar z t)
      (((thetaSource.k (x + L) : ℂ) - (thetaSource.k x : ℂ)) * sourceChar z x
        + Complex.I * z * (windowFun L x * sourceChar z x)) x := by
    intro x
    have h := (hasDerivAt_windowFun hL x).mul (hchar x)
    refine h.congr_deriv ?_
    ring
  have hk : Integrable (fun x : ℝ => (thetaSource.k x : ℂ) * sourceChar z x)
      (volume : Measure ℝ) := integrable_k_sourceChar thetaSource (hasShiftedTail_thetaSource hz)
  have hkshift : Integrable (fun x : ℝ => (thetaSource.k (x + L) : ℂ) * sourceChar z x)
      (volume : Measure ℝ) := by
    have hcomp : Integrable
        (fun x : ℝ => (thetaSource.k (x + L) : ℂ) * sourceChar z (x + L))
        (volume : Measure ℝ) := hk.comp_add_right L
    have hpt : ∀ x : ℝ, (thetaSource.k (x + L) : ℂ) * sourceChar z x
        = Complex.exp (-(Complex.I * z * (L : ℂ)))
          * ((thetaSource.k (x + L) : ℂ) * sourceChar z (x + L)) := by
      intro x
      exact shifted_char_factor (thetaSource.k (x + L) : ℂ) L z x
    exact (hcomp.const_mul _).congr (Filter.Eventually.of_forall fun x => (hpt x).symm)
  have hwin := integrable_windowFun_sourceChar hL hz
  have hdiff : Integrable
      (fun x : ℝ => ((thetaSource.k (x + L) : ℂ) - (thetaSource.k x : ℂ)) * sourceChar z x)
      (volume : Measure ℝ) := by
    refine (hkshift.sub hk).congr (Filter.Eventually.of_forall fun x => ?_)
    show (thetaSource.k (x + L) : ℂ) * sourceChar z x - (thetaSource.k x : ℂ) * sourceChar z x
      = ((thetaSource.k (x + L) : ℂ) - (thetaSource.k x : ℂ)) * sourceChar z x
    ring
  have hderivInt : Integrable
      (fun x : ℝ => ((thetaSource.k (x + L) : ℂ) - (thetaSource.k x : ℂ)) * sourceChar z x
        + Complex.I * z * (windowFun L x * sourceChar z x)) (volume : Measure ℝ) :=
    hdiff.add (hwin.const_mul _)
  obtain ⟨hbot, htop⟩ := tendsto_windowFun_sourceChar hL hz
  have hzero := MeasureTheory.integral_of_hasDerivAt_of_tendsto hprod hderivInt hbot htop
  rw [sub_self] at hzero
  have hsplit : (∫ x : ℝ, ((thetaSource.k (x + L) : ℂ) - (thetaSource.k x : ℂ))
        * sourceChar z x)
      + Complex.I * z * ∫ x : ℝ, windowFun L x * sourceChar z x = 0 := by
    rw [← MeasureTheory.integral_const_mul,
      ← MeasureTheory.integral_add hdiff (hwin.const_mul _)]
    exact hzero
  have hfirst : (∫ x : ℝ, ((thetaSource.k (x + L) : ℂ) - (thetaSource.k x : ℂ))
        * sourceChar z x)
      = (Complex.exp (-(Complex.I * z * (L : ℂ))) - 1) * XiC z := by
    have hrw : ∀ x : ℝ, ((thetaSource.k (x + L) : ℂ) - (thetaSource.k x : ℂ)) * sourceChar z x
        = (thetaSource.k (x + L) : ℂ) * sourceChar z x
          - (thetaSource.k x : ℂ) * sourceChar z x := fun x => by ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hrw),
      MeasureTheory.integral_sub hkshift hk, integral_shifted_k_sourceChar hz,
      ← xiC, xiC_thetaSource hz]
    ring
  rw [hfirst] at hsplit
  have hJ : (∫ x : ℝ, windowFun L x * sourceChar z x) * (Complex.I * z)
      = (1 - Complex.exp (-(Complex.I * z * (L : ℂ)))) * XiC z := by
    linear_combination hsplit
  rw [div_mul_eq_mul_div, eq_div_iff hIz]
  exact hJ


/-! ### The prime anomaly and the centered window -/

/-- **The divisor factorization of the integer-shift anomaly.**  `r̂_n = q_n Ξ_C`. -/
theorem integral_integerAnomaly_sourceChar {n : ℕ} (hn : 1 ≤ n) {z : ℂ} (hz : |z.im| < 1)
    (hz0 : z ≠ 0) :
    (∫ x : ℝ, integerAnomaly thetaSource n x * sourceChar z x)
      = shiftMultiplier n z * XiC z := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hL : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hIz : Complex.I * z ≠ 0 := mul_ne_zero Complex.I_ne_zero hz0
  have hpt : ∀ x : ℝ, integerAnomaly thetaSource n x * sourceChar z x
      = (Complex.I * ((((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ))
        * (windowFun (Real.log n) x * sourceChar z x) := by
    intro x
    rw [integerAnomaly_eq_intervalMass thetaSource hn, windowFun]
    push_cast
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), MeasureTheory.integral_const_mul,
    integral_windowFun_sourceChar hL hz hz0, shiftMultiplier]
  field_simp

/-- **The divisor factorization of the centered window.**  `ĉ_n = a_n Ξ_C`. -/
theorem integral_centeredWindow_sourceChar {n : ℕ} (hn : 1 ≤ n) {z : ℂ} (hz : |z.im| < 1)
    (hz0 : z ≠ 0) :
    (∫ x : ℝ, ((centeredWindow thetaSource n x : ℝ) : ℂ) * sourceChar z x)
      = centeredMultiplier n z * XiC z := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hL : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hIz : Complex.I * z ≠ 0 := mul_ne_zero Complex.I_ne_zero hz0
  set a : ℝ := Real.log n / 2 with ha
  have hpt : ∀ x : ℝ, ((centeredWindow thetaSource n x : ℝ) : ℂ) * sourceChar z x
      = (((((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ) * Complex.exp (Complex.I * z * (a : ℂ)))
        * (windowFun (Real.log n) (x - a) * sourceChar z (x - a)) := by
    intro x
    have hwin : windowFun (Real.log n) (x - a)
        = ((intervalMass thetaSource (x - a) (x + a) : ℝ) : ℂ) := by
      rw [windowFun]
      congr 2
      rw [ha]
      ring
    have hchar : sourceChar z x = sourceChar z (x - a) * Complex.exp (Complex.I * z * (a : ℂ)) := by
      have := sourceChar_add z (x - a) a
      rw [show x - a + a = x by ring] at this
      exact this
    rw [centeredWindow, hwin, hchar]
    push_cast
    ring
  have hshift : (∫ x : ℝ, windowFun (Real.log n) (x - a) * sourceChar z (x - a))
      = ∫ x : ℝ, windowFun (Real.log n) x * sourceChar z x :=
    MeasureTheory.integral_sub_right_eq_self
      (fun x : ℝ => windowFun (Real.log n) x * sourceChar z x) a
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), MeasureTheory.integral_const_mul,
    hshift, integral_windowFun_sourceChar hL hz hz0, centeredMultiplier]
  have hexp : Complex.exp (Complex.I * z * (a : ℂ))
      * (1 - Complex.exp (-(Complex.I * z * ((Real.log n : ℝ) : ℂ))))
      = Complex.exp (Complex.I * z * ((a : ℝ) : ℂ))
        - Complex.exp (-(Complex.I * z * ((a : ℝ) : ℂ))) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    rw [ha]
    push_cast
    ring
  field_simp
  linear_combination (((((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ) * XiC z) * hexp

end HedenmalmThetaSource

end

end RHTower
