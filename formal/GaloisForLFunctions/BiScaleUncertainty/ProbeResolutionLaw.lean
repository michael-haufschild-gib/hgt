import GaloisForLFunctions.BiScaleUncertainty.BandSlopeZeroEnergyLaw

/-!
# Probe resolution: a compact source sees each zero with weight `|f̂(γ)|²`

A compact `C¹` source `f` observes the Chebyshev error through its gauge derivative
`g = f' − f/2`. Away from the cutoff the packet of `f` is the **stationary gauge convolution**

`Φ_f(τ) = ∫_0^∞ Ẽ(t) g(t − τ) dt`.

**Probe resolution law.** Under RH, if `∫_0^L Φ_f² ≤ C(1 + L) + K`, then for every finite family
of distinct critical ordinates `γ_k` with orders `n_k` of `(s − 1)ζ(s)` at `ρ_k = 1/2 + iγ_k`,

`Σ_k n_k² |f̂(γ_k)|² ≤ C`, `f̂(γ) = ∫ e^{iγv} f(v) dv`.

The bare band weighs a zero by `n²/|ρ|²` (`sum_order_sq_div_le_of_band`); a probe weighs it by
`n²|f̂(γ)|²`. The gauge derivative cancels the damping exactly: `ĝ(γ) = −ρ f̂(γ)`. A compact source
detects every zero at which its spectrum does not vanish, with no loss in height.

Mechanism. Fubini factorizes the Laplace transform of `Φ_f` as `ĝ(z) L(z)` up to a term from the
compact range `t < w`, so the Abel coefficients are `σ L_Φ(σ + iγ) → ĝ(iγ)(−n/ρ) = n f̂(γ)`; the
Abel–Bessel inequality concludes.
-/

open MeasureTheory Set Filter Topology Complex

namespace GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge

open SignedPrimePolar

noncomputable section
set_option autoImplicit false

/-- The stationary gauge convolution `Φ_f(τ) = ∫_0^∞ Ẽ(t) (f' − f/2)(t − τ) dt`. -/
def stationaryGaugeConvolution (f : ℝ → ℝ) (τ : ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), normalizedLogError t * gaugeDerivative f (t - τ)

/-- The probe transform `f̂(γ) = ∫ e^{iγv} f(v) dv`. -/
def probeTransform (f : ℝ → ℝ) (γ : ℝ) : ℂ :=
  ∫ v, Complex.exp (((γ * v : ℝ) : ℂ) * I) * (f v : ℂ)

/-! ## Elementary facts -/

private theorem exists_support_radius {g : ℝ → ℝ} (hg : HasCompactSupport g) :
    ∃ w : ℝ, 0 < w ∧ ∀ v : ℝ, w < |v| → g v = 0 := by
  obtain ⟨w, hw0, hw⟩ := hg.exists_pos_le_norm
  exact ⟨w, hw0, fun v hv => hw v (by rw [Real.norm_eq_abs]; exact hv.le)⟩

theorem integrableOn_normalizedLogError_Icc (T : ℝ) :
    IntegrableOn normalizedLogError (Icc 0 T) := by
  refine Measure.integrableOn_of_bounded (M := Chebyshev.psi (Real.exp T) + Real.exp T)
    measure_Icc_lt_top.ne measurable_normalizedLogError.aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Icc]
  exact Eventually.of_forall fun t ht => by
    rw [Real.norm_eq_abs]; exact abs_normalizedLogError_le ht.1 ht.2

theorem locallyIntegrable_indicator_normalizedLogError :
    LocallyIntegrable ((Ioi (0 : ℝ)).indicator normalizedLogError) := by
  rw [locallyIntegrable_iff]
  intro k hk
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).mp hk.isBounded
  have hsub : k ⊆ Icc (-|R|) |R| := fun x hx => by
    have := hR hx
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
    exact ⟨by linarith [abs_le.mp (this.trans (le_abs_self R)), le_abs_self R, abs_nonneg R],
      (le_abs_self x).trans (this.trans (le_abs_self R))⟩
  refine IntegrableOn.mono_set ?_ hsub
  have hsplit : Icc (-|R|) |R| ⊆ Icc (-|R|) 0 ∪ Icc 0 |R| := fun x hx => by
    rcases le_total x 0 with h | h
    · exact Or.inl ⟨hx.1, h⟩
    · exact Or.inr ⟨h, hx.2⟩
  refine IntegrableOn.mono_set (IntegrableOn.union ?_ ?_) hsplit
  · refine (integrableOn_zero).congr_fun (fun x hx => ?_) measurableSet_Icc
    rw [indicator_of_notMem (by simp only [mem_Ioi, not_lt]; exact hx.2)]
  · exact ((integrableOn_normalizedLogError_Icc |R|).indicator measurableSet_Ioi)

theorem stationaryGaugeConvolution_eq_convolution (f : ℝ → ℝ) (τ : ℝ) :
    stationaryGaugeConvolution f τ =
      convolution ((Ioi (0 : ℝ)).indicator normalizedLogError)
        (fun x => gaugeDerivative f (-x)) (ContinuousLinearMap.mul ℝ ℝ) volume τ := by
  rw [stationaryGaugeConvolution, convolution, ← integral_indicator measurableSet_Ioi]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  by_cases ht : t ∈ Ioi (0 : ℝ)
  · simp [indicator_of_mem ht, neg_sub]
  · simp [indicator_of_notMem ht]

theorem continuous_stationaryGaugeConvolution {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hfc : HasCompactSupport f) : Continuous (stationaryGaugeConvolution f) := by
  rw [show stationaryGaugeConvolution f = _ from funext (stationaryGaugeConvolution_eq_convolution f)]
  exact HasCompactSupport.continuous_convolution_right _
    ((hasCompactSupport_gaugeDerivative hfc).comp_homeomorph (Homeomorph.neg ℝ))
    locallyIntegrable_indicator_normalizedLogError
    ((continuous_gaugeDerivative hf).comp continuous_neg)

/-! ## The gauge factor -/

/-- `ĝ(iγ) = −ρ f̂(γ)` for `g = f' − f/2`, `ρ = 1/2 + iγ`: the gauge derivative cancels the
height damping of the bare band. -/
theorem integral_exp_mul_gaugeDerivative {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hfc : HasCompactSupport f) (γ : ℝ) :
    ∫ v, Complex.exp (((γ * v : ℝ) : ℂ) * I) * (gaugeDerivative f v : ℂ) =
      -((1 / 2 + γ * I) * probeTransform f γ) := by
  have hcf : Continuous f := hf.continuous
  have hcd : Continuous (deriv f) := hf.continuous_deriv le_rfl
  have hdc : HasCompactSupport (deriv f) := hfc.deriv
  set u : ℝ → ℂ := fun v => Complex.exp (((γ * v : ℝ) : ℂ) * I)
  set u' : ℝ → ℂ := fun v => (γ * I) * Complex.exp (((γ * v : ℝ) : ℂ) * I)
  have hu : ∀ x, HasDerivAt u (u' x) x := by
    intro x
    have h1 : HasDerivAt (fun v : ℝ => (((γ * v : ℝ) : ℂ) * I)) (γ * I) x := by
      have := ((hasDerivAt_id x).const_mul γ).ofReal_comp.mul_const I
      simpa using this
    have := h1.cexp
    simp only [u, u']
    convert this using 1; ring
  have hv : ∀ x, HasDerivAt (fun v => (f v : ℂ)) ((deriv f x : ℝ) : ℂ) x := fun x =>
    ((hf.differentiable one_ne_zero x).hasDerivAt).ofReal_comp
  have hcont_u : Continuous u := by simp only [u]; fun_prop
  have hcont_u' : Continuous u' := by simp only [u']; fun_prop
  have hint1 : Integrable (u * fun v => ((deriv f v : ℝ) : ℂ)) :=
    (hcont_u.mul (Complex.continuous_ofReal.comp hcd)).integrable_of_hasCompactSupport
      (hdc.comp_left Complex.ofReal_zero |>.mul_left)
  have hint2 : Integrable (u' * fun v => (f v : ℂ)) :=
    (hcont_u'.mul (Complex.continuous_ofReal.comp hcf)).integrable_of_hasCompactSupport
      (hfc.comp_left Complex.ofReal_zero |>.mul_left)
  have hint3 : Integrable (u * fun v => (f v : ℂ)) :=
    (hcont_u.mul (Complex.continuous_ofReal.comp hcf)).integrable_of_hasCompactSupport
      (hfc.comp_left Complex.ofReal_zero |>.mul_left)
  have hparts := integral_mul_deriv_eq_deriv_mul_of_integrable (fun x _ => hu x) (fun x _ => hv x)
    hint1 hint2 hint3
  have hsplit : (fun v => Complex.exp (((γ * v : ℝ) : ℂ) * I) * (gaugeDerivative f v : ℂ)) =
      fun v => u v * ((deriv f v : ℝ) : ℂ) - (1 / 2 : ℂ) * (u v * (f v : ℂ)) := by
    funext v; simp only [gaugeDerivative, u]; push_cast; ring
  have hint1' : Integrable (fun v => u v * ((deriv f v : ℝ) : ℂ)) := hint1
  have hint3' : Integrable (fun v => u v * (f v : ℂ)) := hint3
  rw [hsplit, integral_sub hint1' (hint3'.const_mul _), integral_const_mul]
  rw [hparts]
  have hu'eq : (fun x => u' x * (f x : ℂ)) = fun x => (γ * I) * (u x * (f x : ℂ)) := by
    funext x; simp only [u, u']; ring
  rw [hu'eq, integral_const_mul]
  simp only [probeTransform, u]
  ring

/-! ## Laplace factorization of the stationary convolution -/

/-- `ĝ(z) = ∫ e^{zv} g(v) dv` for `g = f' − f/2`. -/
def gaugeLaplace (f : ℝ → ℝ) (z : ℂ) : ℂ :=
  ∫ v : ℝ, Complex.exp (z * v) * (gaugeDerivative f v : ℂ)

theorem stationaryGaugeConvolution_eq_zero_of_lt {f : ℝ → ℝ} {w : ℝ} (hw0 : 0 < w)
    (hw : ∀ v : ℝ, w < |v| → gaugeDerivative f v = 0) {τ : ℝ} (hτ : τ < -w) :
    stationaryGaugeConvolution f τ = 0 := by
  rw [stationaryGaugeConvolution]
  refine setIntegral_eq_zero_of_forall_eq_zero fun t ht => ?_
  rw [hw (t - τ) (by rw [abs_of_pos (by linarith [mem_Ioi.mp ht])]; linarith [mem_Ioi.mp ht]),
    mul_zero]

/-- **Laplace factorization.** If `e^{-Re z · t} Ẽ` is integrable on the half-line, then
`e^{-zτ} Φ_f(τ)` is integrable on the line with integral `ĝ(z) L(z)`. -/
theorem integral_exp_mul_stationaryGaugeConvolution {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hfc : HasCompactSupport f) {z : ℂ}
    (hE : IntegrableOn (fun t => Real.exp (-z.re * t) * |normalizedLogError t|) (Ioi 0)) :
    Integrable (fun τ : ℝ => Complex.exp (-(z * τ)) * (stationaryGaugeConvolution f τ : ℂ)) ∧
      ∫ τ : ℝ, Complex.exp (-(z * τ)) * (stationaryGaugeConvolution f τ : ℂ) =
        gaugeLaplace f z * _root_.RHTower.criticalNormalizedChebyshevErrorLaplace z := by
  set F₁ : ℝ → ℂ := fun t => Complex.exp (-(z * t)) *
    (((Ioi (0 : ℝ)).indicator normalizedLogError t : ℝ) : ℂ)
  set G₁ : ℝ → ℂ := fun x => Complex.exp (-(z * x)) * (gaugeDerivative f (-x) : ℂ)
  have hgc : Continuous (gaugeDerivative f) := continuous_gaugeDerivative hf
  have hgs : HasCompactSupport (gaugeDerivative f) := hasCompactSupport_gaugeDerivative hfc
  have hF₁ : Integrable F₁ := by
    have hmeas : AEStronglyMeasurable F₁ volume :=
      ((by fun_prop : Continuous fun t : ℝ => Complex.exp (-(z * t))).aestronglyMeasurable.mul
        (Complex.continuous_ofReal.measurable.comp
          (measurable_normalizedLogError.indicator measurableSet_Ioi)).aestronglyMeasurable)
    refine (hE.integrable_indicator measurableSet_Ioi).mono' hmeas
      (Eventually.of_forall fun t => ?_)
    rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
    by_cases ht : t ∈ Ioi (0 : ℝ)
    · rw [indicator_of_mem ht, indicator_of_mem ht]
      simp only [neg_mul, Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, sub_zero, le_refl]
    · rw [indicator_of_notMem ht, indicator_of_notMem ht]; simp
  have hG₁ : Integrable G₁ :=
    ((by fun_prop : Continuous fun x : ℝ => Complex.exp (-(z * x))).mul
      (Complex.continuous_ofReal.comp (hgc.comp continuous_neg))).integrable_of_hasCompactSupport
      ((hgs.comp_homeomorph (Homeomorph.neg ℝ)).comp_left Complex.ofReal_zero |>.mul_left)
  have hconv : ∀ τ : ℝ, convolution F₁ G₁ (ContinuousLinearMap.mul ℂ ℂ) volume τ =
      Complex.exp (-(z * τ)) * (stationaryGaugeConvolution f τ : ℂ) := by
    intro τ
    rw [convolution_def, stationaryGaugeConvolution, ← integral_indicator measurableSet_Ioi,
      ← integral_complex_ofReal, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [ContinuousLinearMap.mul_apply', F₁, G₁]
    by_cases ht : t ∈ Ioi (0 : ℝ)
    · rw [indicator_of_mem ht, indicator_of_mem ht, neg_sub]
      have : Complex.exp (-(z * t)) * Complex.exp (-(z * ((τ - t : ℝ) : ℂ))) =
          Complex.exp (-(z * τ)) := by
        rw [← Complex.exp_add]; congr 1; push_cast; ring
      push_cast at this ⊢
      linear_combination ((normalizedLogError t : ℂ) * (gaugeDerivative f (t - τ) : ℂ)) * this
    · rw [indicator_of_notMem ht, indicator_of_notMem ht]; simp
  have hF₁int : ∫ t, F₁ t = _root_.RHTower.criticalNormalizedChebyshevErrorLaplace z := by
    rw [criticalNormalizedChebyshevErrorLaplace_eq, ← integral_indicator measurableSet_Ioi]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    by_cases ht : t ∈ Ioi (0 : ℝ)
    · simp only [F₁, indicator_of_mem ht]
    · simp only [F₁, indicator_of_notMem ht, Complex.ofReal_zero, mul_zero]
  have hG₁int : ∫ x, G₁ x = gaugeLaplace f z := by
    rw [gaugeLaplace, ← integral_neg_eq_self]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [G₁, neg_neg]
    congr 1; congr 1; push_cast; ring
  have hfun : (fun τ : ℝ => Complex.exp (-(z * τ)) * (stationaryGaugeConvolution f τ : ℂ)) =
      convolution F₁ G₁ (ContinuousLinearMap.mul ℂ ℂ) volume := (funext hconv).symm
  rw [hfun]
  refine ⟨hF₁.integrable_convolution _ hG₁, ?_⟩
  rw [integral_convolution _ hF₁ hG₁, hF₁int, hG₁int, ContinuousLinearMap.mul_apply', mul_comm]

theorem continuous_gaugeLaplace_vertical {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hfc : HasCompactSupport f) (γ : ℝ) :
    Continuous fun σ : ℝ => gaugeLaplace f ((σ : ℂ) + γ * I) := by
  obtain ⟨w, hw0, hw⟩ := exists_support_radius (hasCompactSupport_gaugeDerivative hfc)
  have heq : (fun σ : ℝ => gaugeLaplace f ((σ : ℂ) + γ * I)) = fun σ : ℝ =>
      ∫ v in Icc (-w) w, Complex.exp (((σ : ℂ) + γ * I) * v) * (gaugeDerivative f v : ℂ) := by
    funext σ
    rw [gaugeLaplace, setIntegral_eq_integral_of_forall_compl_eq_zero fun v hv => ?_]
    rw [hw v (by
      simp only [mem_Icc, not_and_or, not_le] at hv
      rcases hv with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith), Complex.ofReal_zero, mul_zero]
  rw [heq]
  exact continuous_parametric_integral_of_continuous
    (by
      have hgc := continuous_gaugeDerivative hf
      fun_prop) isCompact_Icc

/-! ## The probe resolution law -/

/-- **Abel coefficient of a probe.** Under RH, if `(s − 1)ζ(s)` has order `n` at
`ρ = 1/2 + iγ`, then `σ ∫_0^∞ e^{-σt} Φ_f(t) e^{-iγt} dt → n f̂(γ)` as `σ → 0⁺`. -/
theorem tendsto_abel_stationaryGaugeConvolution (hRH : RiemannHypothesis) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) {γ : ℝ} {n : ℤ}
    (horder : meromorphicOrderAt _root_.RHTower.zetaResidueUnit (1 / 2 + γ * I) = n) :
    Tendsto (fun σ : ℝ => (σ : ℂ) * ∫ t in Ioi (0 : ℝ),
        ((Real.exp (-σ * t) * stationaryGaugeConvolution f t : ℝ) : ℂ) * criticalCharacter γ t)
      (𝓝[>] 0) (𝓝 ((n : ℂ) * probeTransform f γ)) := by
  have hXi := _root_.RHTower.riemannHypothesis_iff_xiZeroHalfPlaneBound_zero.1 hRH
  obtain ⟨w, hw0, hw⟩ := exists_support_radius (hasCompactSupport_gaugeDerivative hfc)
  set Φ := stationaryGaugeConvolution f
  have hΦc : Continuous Φ := continuous_stationaryGaugeConvolution hf hfc
  set ρ : ℂ := 1 / 2 + γ * I with hρ
  have hρ0 : ρ ≠ 0 := fun h => by have := congrArg Complex.re h; simp [hρ] at this
  -- the Abel coefficient of `Ẽ`
  have horder' : meromorphicOrderAt _root_.RHTower.zetaResidueUnit
      (((1 / 2 + 0 : ℝ) : ℂ) + γ * I) = n := by
    rw [show (((1 / 2 + 0 : ℝ) : ℂ) + γ * I) = 1 / 2 + γ * I by push_cast; ring]; exact horder
  have hL := tendsto_abel_laplace_of_halfPlane le_rfl (by norm_num) hXi horder'
  simp only [zero_add, add_zero, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_ofNat] at hL
  -- the gauge factor at `σ + iγ`
  have hG : Tendsto (fun σ : ℝ => gaugeLaplace f ((σ : ℂ) + γ * I)) (𝓝[>] 0)
      (𝓝 (gaugeLaplace f ((0 : ℝ) + γ * I))) :=
    ((continuous_gaugeLaplace_vertical hf hfc γ).tendsto 0).mono_left nhdsWithin_le_nhds
  have hG0 : gaugeLaplace f (((0 : ℝ) : ℂ) + γ * I) = -(ρ * probeTransform f γ) := by
    rw [← integral_exp_mul_gaugeDerivative hf hfc γ, gaugeLaplace]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    push_cast; ring_nf
  -- the compact remainder on `(-w, 0]`
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := -w) (b := 0)).exists_bound_of_continuousOn
    hΦc.continuousOn
  have hrem : Tendsto (fun σ : ℝ => (σ : ℂ) * ∫ τ in Iic (0 : ℝ),
      Complex.exp (-(((σ : ℂ) + γ * I) * (τ : ℂ))) * (Φ τ : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    have hbound : ∀ σ : ℝ, 0 < σ → σ ≤ 1 → ‖∫ τ in Iic (0 : ℝ),
        Complex.exp (-(((σ : ℂ) + γ * I) * (τ : ℂ))) * (Φ τ : ℂ)‖ ≤ Real.exp w * M * w := by
      intro σ hσ hσ1
      have hzero : ∀ τ ∈ Iic (0 : ℝ), τ ∉ Icc (-w) 0 →
          Complex.exp (-(((σ : ℂ) + γ * I) * (τ : ℂ))) * (Φ τ : ℂ) = 0 := by
        intro τ hτ hnot
        have : τ < -w := by
          by_contra h; exact hnot ⟨not_lt.mp h, hτ⟩
        simp [Φ, stationaryGaugeConvolution_eq_zero_of_lt hw0 hw this]
      rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Iic Icc_subset_Iic_self
        fun τ hτ => hzero τ hτ.1 hτ.2]
      have hb : ∀ τ ∈ Icc (-w) (0 : ℝ),
          ‖Complex.exp (-(((σ : ℂ) + γ * I) * (τ : ℂ))) * (Φ τ : ℂ)‖ ≤ Real.exp w * M := by
        intro τ hτ
        rw [norm_mul, Complex.norm_exp, Complex.norm_real]
        have hre : (-(((σ : ℂ) + γ * I) * τ)).re = -σ * τ := by simp
        rw [hre]
        exact mul_le_mul (Real.exp_le_exp.mpr (by nlinarith [hτ.1, hτ.2]))
          (hM τ hτ) (norm_nonneg _) (Real.exp_pos _).le
      have := norm_setIntegral_le_of_norm_le_const (μ := volume) measure_Icc_lt_top hb
      rw [Real.volume_real_Icc_of_le (by linarith), sub_neg_eq_add, zero_add] at this
      exact this
    refine squeeze_zero_norm' ?_ (by
      have : Tendsto (fun σ : ℝ => σ * (Real.exp w * M * w)) (𝓝[>] 0) (𝓝 (0 * (Real.exp w * M * w))) :=
        (tendsto_id.mono_left nhdsWithin_le_nhds).mul_const _
      simpa using this)
    filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)]
      with σ hσ hσ1
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hσ]
    exact mul_le_mul_of_nonneg_left (hbound σ hσ hσ1.2.le) hσ.le
  -- assemble
  have hlim := ((hG.mul hL).sub hrem)
  rw [hG0, sub_zero] at hlim
  have htarget : -(ρ * probeTransform f γ) * (-(n : ℂ) / ρ) = (n : ℂ) * probeTransform f γ := by
    field_simp
  rw [htarget] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  change (0 : ℝ) < σ at hσ
  -- integrability of `e^{-σt}|Ẽ|` from RH
  obtain ⟨B, hB0, hB⟩ :=
    exists_abs_normalizedLogError_le_of_xiZeroHalfPlaneBound le_rfl (half_pos hσ) hXi
  have hE : IntegrableOn (fun t => Real.exp (-((σ : ℂ) + γ * I).re * t) *
      |normalizedLogError t|) (Ioi 0) := by
    have hre : ((σ : ℂ) + γ * I).re = σ := by simp
    simp only [hre]
    refine ((exp_neg_integrableOn_Ioi 0 (half_pos hσ)).const_mul B).mono'
      ((by fun_prop : Continuous fun t : ℝ => Real.exp (-σ * t)).aestronglyMeasurable.mul
        measurable_normalizedLogError.abs.aestronglyMeasurable) ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun t ht => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc Real.exp (-σ * t) * |normalizedLogError t| ≤
        Real.exp (-σ * t) * (B * Real.exp (σ / 2 * t)) :=
          mul_le_mul_of_nonneg_left (hB t (le_of_lt ht)) (Real.exp_pos _).le
      _ = B * Real.exp (-(σ / 2) * t) := by
          rw [mul_left_comm, ← Real.exp_add]; congr 2; ring
  obtain ⟨hint, hfull⟩ := integral_exp_mul_stationaryGaugeConvolution hf hfc hE
  rw [← integral_add_compl measurableSet_Ioi hint, compl_Ioi] at hfull
  have hpt : ∀ t : ℝ, ((Real.exp (-σ * t) * Φ t : ℝ) : ℂ) * criticalCharacter γ t =
      Complex.exp (-(((σ : ℂ) + γ * I) * t)) * (Φ t : ℂ) := by
    intro t
    rw [criticalCharacter, Complex.ofReal_mul, Complex.ofReal_exp]
    have : Complex.exp (-(((σ : ℂ) + γ * I) * t)) =
        Complex.exp ((-σ * t : ℝ) : ℂ) * Complex.exp ((-(γ * t) : ℝ) * I) := by
      rw [← Complex.exp_add]; push_cast; ring_nf
    rw [this]; ring
  have hkey : ∫ τ in Ioi (0 : ℝ), Complex.exp (-(((σ : ℂ) + γ * I) * τ)) * (Φ τ : ℂ) =
      gaugeLaplace f ((σ : ℂ) + γ * I) *
        _root_.RHTower.criticalNormalizedChebyshevErrorLaplace ((σ : ℂ) + γ * I) -
      ∫ τ in Iic (0 : ℝ), Complex.exp (-(((σ : ℂ) + γ * I) * τ)) * (Φ τ : ℂ) := by
    rw [← hfull]; ring
  show _ = (σ : ℂ) * ∫ t in Ioi (0 : ℝ),
    ((Real.exp (-σ * t) * Φ t : ℝ) : ℂ) * criticalCharacter γ t
  simp_rw [hpt]
  rw [hkey]
  ring

/-- **Probe resolution law.** Under RH, if the stationary gauge convolution of a compact `C¹`
source `f` has a linear band, `∫_0^L Φ_f² ≤ C(1 + L) + K`, then for every finite family of
distinct critical ordinates `γ_k`, with `n_k` the order of `(s − 1)ζ(s)` at `1/2 + iγ_k`,
`Σ_k n_k² |f̂(γ_k)|² ≤ C`. -/
theorem sum_order_sq_mul_probe_le (hRH : RiemannHypothesis) {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hfc : HasCompactSupport f) {C K : ℝ}
    (hband : ∀ L : ℝ, 0 ≤ L →
      ∫ t in Icc 0 L, stationaryGaugeConvolution f t ^ 2 ≤ C * (1 + L) + K)
    {ι : Type*} (s : Finset ι) (γ : ι → ℝ) (hγ : Set.InjOn γ s) (n : ι → ℤ)
    (horder : ∀ k ∈ s,
      meromorphicOrderAt _root_.RHTower.zetaResidueUnit (1 / 2 + γ k * I) = n k) :
    ∑ k ∈ s, (n k : ℝ) ^ 2 * ‖probeTransform f (γ k)‖ ^ 2 ≤ C := by
  have hC := nonneg_of_linear_band hband
  have hΦc := continuous_stationaryGaugeConvolution hf hfc
  have hΦ2 : ∀ T : ℝ, IntegrableOn (fun t => stationaryGaugeConvolution f t ^ 2) (Icc 0 T) :=
    fun T => (hΦc.pow 2).integrableOn_Icc
  have h := sum_norm_sq_le_of_abel hΦc.measurable
    (fun σ hσ => (abel_energy_of_linear_band hΦc.measurable hΦ2 hC hband hσ).1)
    (fun σ hσ => (abel_energy_of_linear_band hΦc.measurable hΦ2 hC hband hσ).2)
    (a := fun σ => C * (1 + σ) + K * σ) (A := C)
    (by
      have hσ : Tendsto (fun σ : ℝ => σ) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      simpa using ((tendsto_const_nhds (x := (1 : ℝ)).add hσ).const_mul C).add
        (hσ.const_mul K))
    s γ hγ (fun k => (n k : ℂ) * probeTransform f (γ k))
    (fun k hk => tendsto_abel_stationaryGaugeConvolution hRH hf hfc (horder k hk))
  refine le_of_eq_of_le (Finset.sum_congr rfl fun k _ => ?_) h
  rw [norm_mul, mul_pow, Complex.norm_intCast, sq_abs]

end

end GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge
