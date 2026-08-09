import GaloisForLFunctions.HTGeometry.InterfinityGeometry.SpectralEulerConstant
import GaloisForLFunctions.HTGeometry.InterfinityGeometry.SpectralLogarithmicHorizon
import GaloisForLFunctions.HTGeometry.InterfinityGeometry.SpectralComplexDeficient

/-!
# The rotated exponential-integral constant

At the cut the two halves of the rotated regularized Gamma integral evaluate the principal
logarithm:

`∫₀¹ (e^{-wt} − 1)/t dt + ∫₁^∞ e^{-wt}/t dt = −γ − Log w`,  `Re w > 0`.

Both sides are holomorphic on the right half-plane with derivative `−1/w`, so their difference is
constant; at `w = 1` the left side is the real exponential-integral constant `−γ`.
-/

namespace GaloisForLFunctions.HTGeometry.Interfinity

open MeasureTheory Set Filter Topology Complex

noncomputable section

/-! ## The sharp real law -/

theorem gammaHead_zero_eq : gammaHead 0 = ∫ t in (0 : ℝ)..1, gammaDefect 0 t := by
  rw [gammaHead, intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]

theorem gammaTail_zero_eq : gammaTail 0 = ∫ t in Ioi (1 : ℝ), Real.exp (-t) / t := by
  rw [gammaTail]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  rw [zero_sub, Real.rpow_neg_one, div_eq_mul_inv]

theorem integrableOn_expDivId_Ioi : IntegrableOn (fun t : ℝ => Real.exp (-t) / t) (Ioi 1) := by
  have h := integrableOn_gammaTailFun (a := 0) (by norm_num)
  refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
  show Real.exp (-t) * t ^ (0 - 1 : ℝ) = Real.exp (-t) / t
  rw [zero_sub, Real.rpow_neg_one, div_eq_mul_inv]

/-- **The sharp logarithmic law for the cut integral.** -/
theorem tendsto_cutIntegral_zero_add_log :
    Tendsto (fun V : ℝ => cutIntegral 0 V + Real.log V) atTop
      (𝓝 (-Real.eulerMascheroniConstant)) := by
  have htail : Tendsto (fun V : ℝ => ∫ t in (1 : ℝ)..V, Real.exp (-t) / t) atTop
      (𝓝 (∫ t in Ioi (1 : ℝ), Real.exp (-t) / t)) :=
    intervalIntegral_tendsto_integral_Ioi 1 integrableOn_expDivId_Ioi tendsto_id
  have hlim : Tendsto (fun V : ℝ =>
      (∫ t in (0 : ℝ)..1, gammaDefect 0 t) + ∫ t in (1 : ℝ)..V, Real.exp (-t) / t) atTop
      (𝓝 (gammaHead 0 + gammaTail 0)) := by
    rw [gammaHead_zero_eq, gammaTail_zero_eq]
    exact tendsto_const_nhds.add htail
  rw [gammaHead_add_gammaTail] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with V hV
  rw [cutIntegral_zero_split hV]
  ring

/-- **The sharp logarithmic contact law.**  At the cut the transported finite part of a smooth
chart is `− c h(0)(log V + γ) + o(1)`. -/
theorem tendsto_transportedFinitePart_log_sharp (c : ℝ) {h : ℝ → ℝ} (hh : IsSmoothReal h) :
    Tendsto (fun V : ℝ => transportedFinitePart c 0 V h +
      c * h 0 * (Real.log V + Real.eulerMascheroniConstant)) atTop (𝓝 0) := by
  set r : ℝ → ℝ := hadamardAvg 0 (deriv h) with hrdef
  have hrS : IsSmoothReal r := isSmoothReal_hadamardAvg 0 hh.derivSmooth
  have hrc : Continuous r := hrS.continuous
  have hr : ∀ s, h s = h 0 + s * r s := hadamard_eq hh
  obtain ⟨B₀, hB₀⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hrc.continuousOn
  set B : ℝ := max B₀ 0 with hBdef
  have hB0 : 0 ≤ B := le_max_right _ _
  have hB : ∀ s ∈ Ioo (0 : ℝ) 1, |r s| ≤ B := fun s hs =>
    le_trans (hB₀ s ⟨hs.1.le, hs.2.le⟩) (le_max_left _ _)
  have hcut : Tendsto (fun V : ℝ =>
      cutIntegral 0 V + Real.log V + Real.eulerMascheroniConstant) atTop
      (𝓝 (-Real.eulerMascheroniConstant + Real.eulerMascheroniConstant)) :=
    tendsto_cutIntegral_zero_add_log.add_const _
  rw [neg_add_cancel] at hcut
  have hrem := tendsto_remainderIntegral_zero hrc hB0 hB
  have hmain : Tendsto (fun V : ℝ => c * (h 0 *
      (cutIntegral 0 V + Real.log V + Real.eulerMascheroniConstant) +
      remainderIntegral 0 V r)) atTop (𝓝 (c * (h 0 * 0 + 0))) :=
    Tendsto.const_mul c ((hcut.const_mul (h 0)).add hrem)
  rw [show c * (h 0 * 0 + 0) = 0 by ring] at hmain
  refine hmain.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with V hV
  rw [transportedFinitePart_split c (by norm_num) hV hr hrc hB0 hB, div_zero]
  ring

/-! ## The rotated halves -/

/-- The head of the rotated regularized Gamma integral at the cut. -/
def clogHead (w : ℂ) : ℂ := ∫ t in Ioo (0 : ℝ) 1, cgammaDefect 0 w t

/-- The tail of the rotated ordinary Gamma integral at the cut. -/
def clogTail (w : ℂ) : ℂ := ∫ t in Ioi (1 : ℝ), cgammaOrd 0 w t

theorem integrableOn_cgammaOrd_Ioi_one {a : ℝ} (ha : a ≤ 1) {w : ℂ} (hw : 0 < w.re) :
    IntegrableOn (cgammaOrd a w) (Ioi 1) := by
  have hdom : IntegrableOn (fun t : ℝ => Real.exp (-(w.re * t))) (Ioi 1) := by
    have h := exp_neg_integrableOn_Ioi (1 : ℝ) hw
    refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
    ring_nf
  refine Integrable.mono' hdom
    (measurable_cgammaOrd a w measurableSet_Ioi fun t ht => lt_trans zero_lt_one ht) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht1 : (1 : ℝ) ≤ t := le_of_lt ht
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht1
  have hpow : t ^ (a - 1) ≤ 1 := by
    have h := Real.rpow_le_rpow_of_exponent_le ht1 (by linarith : a - 1 ≤ 0)
    rwa [Real.rpow_zero] at h
  have hpow0 : (0 : ℝ) < t ^ (a - 1) := Real.rpow_pos_of_pos ht0 _
  have hexp : (0 : ℝ) < Real.exp (-(w.re * t)) := Real.exp_pos _
  rw [norm_cgammaOrd a w ht0]
  nlinarith

/-! ## The common derivative -/

theorem cgammaDeriv_zero {w : ℂ} {t : ℝ} (ht : 0 < t) :
    cgammaDeriv 0 w t = -Complex.exp (-(w * t)) := by
  have hne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (ne_of_gt ht)
  have hpow : ((t ^ (0 - 1 : ℝ) : ℝ) : ℂ) = ((t : ℂ))⁻¹ := by
    rw [zero_sub, Real.rpow_neg_one]
    push_cast
    ring
  rw [cgammaDeriv, hpow]
  field_simp

theorem cgammaOrdDeriv_zero {w : ℂ} {t : ℝ} (ht : 0 < t) :
    cgammaOrdDeriv 0 w t = -Complex.exp (-(w * t)) := by
  have hne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (ne_of_gt ht)
  have hpow : ((t ^ (0 - 1 : ℝ) : ℝ) : ℂ) = ((t : ℂ))⁻¹ := by
    rw [zero_sub, Real.rpow_neg_one]
    push_cast
    ring
  rw [cgammaOrdDeriv, hpow]
  field_simp

theorem hasDerivAt_clogHead {w : ℂ} (hw : 0 < w.re) :
    HasDerivAt clogHead (∫ t in Ioo (0 : ℝ) 1, cgammaDeriv 0 w t) w := by
  set δ : ℝ := w.re / 2 with hδdef
  have hδ : 0 < δ := by positivity
  have hball : ∀ v ∈ Metric.ball w δ, δ ≤ v.re := by
    intro v hv
    have hlt : ‖v - w‖ < δ := by simpa [Complex.dist_eq] using hv
    have hre : |(v - w).re| ≤ ‖v - w‖ := Complex.abs_re_le_norm _
    have hlt2 : |v.re - w.re| < δ := by
      simpa [Complex.sub_re] using lt_of_le_of_lt hre hlt
    have h2 := (abs_lt.1 hlt2).1
    simp only [hδdef] at h2 ⊢
    linarith
  have hbound : ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) 1)), ∀ v ∈ Metric.ball w δ,
      ‖cgammaDeriv 0 v t‖ ≤ 1 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht v hv
    have ht0 : (0 : ℝ) < t := ht.1
    rw [norm_cgammaDeriv 0 v ht0, Real.rpow_zero, mul_one]
    refine Real.exp_le_one_iff.2 ?_
    have := hball v hv
    nlinarith
  have hres := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun v : ℂ => cgammaDefect 0 v) (x₀ := w) (s := Metric.ball w δ)
    (bound := fun _ : ℝ => (1 : ℝ))
    (Metric.ball_mem_nhds w hδ)
    (Filter.Eventually.of_forall fun v =>
      measurable_cgammaDefect 0 v measurableSet_Ioo fun t ht => ht.1)
    (integrableOn_cgammaDefect_Ioo_one (by norm_num) w)
    (measurable_cgammaDeriv 0 w measurableSet_Ioo fun t ht => ht.1)
    hbound (integrableOn_const (by simp) (by simp))
    (Filter.Eventually.of_forall fun t v _ => hasDerivAt_cgammaDefect 0 v t)
  exact hres.2

theorem hasDerivAt_clogTail {w : ℂ} (hw : 0 < w.re) :
    HasDerivAt clogTail (∫ t in Ioi (1 : ℝ), cgammaOrdDeriv 0 w t) w := by
  set δ : ℝ := w.re / 2 with hδdef
  have hδ : 0 < δ := by positivity
  have hball : ∀ v ∈ Metric.ball w δ, δ ≤ v.re := by
    intro v hv
    have hlt : ‖v - w‖ < δ := by simpa [Complex.dist_eq] using hv
    have hre : |(v - w).re| ≤ ‖v - w‖ := Complex.abs_re_le_norm _
    have hlt2 : |v.re - w.re| < δ := by
      simpa [Complex.sub_re] using lt_of_le_of_lt hre hlt
    have h2 := (abs_lt.1 hlt2).1
    simp only [hδdef] at h2 ⊢
    linarith
  have hdom : IntegrableOn (fun t : ℝ => Real.exp (-(δ * t))) (Ioi 1) := by
    have h := exp_neg_integrableOn_Ioi (1 : ℝ) hδ
    refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
    ring_nf
  have hbound : ∀ᵐ t ∂(volume.restrict (Ioi (1 : ℝ))), ∀ v ∈ Metric.ball w δ,
      ‖cgammaOrdDeriv 0 v t‖ ≤ Real.exp (-(δ * t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht v hv
    have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
    rw [norm_cgammaOrdDeriv 0 v ht0, Real.rpow_zero, mul_one]
    refine Real.exp_le_exp.2 ?_
    have := hball v hv
    nlinarith
  have hres := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun v : ℂ => cgammaOrd 0 v) (x₀ := w) (s := Metric.ball w δ)
    (bound := fun t : ℝ => Real.exp (-(δ * t)))
    (Metric.ball_mem_nhds w hδ)
    (Filter.Eventually.of_forall fun v =>
      measurable_cgammaOrd 0 v measurableSet_Ioi fun t ht => lt_trans zero_lt_one ht)
    (integrableOn_cgammaOrd_Ioi_one (by norm_num) hw)
    (measurable_cgammaOrdDeriv 0 w measurableSet_Ioi fun t ht => lt_trans zero_lt_one ht)
    hbound hdom
    (Filter.Eventually.of_forall fun t v _ => hasDerivAt_cgammaOrd 0 v t)
  exact hres.2

/-- The full exponential integral over the positive ray. -/
theorem integral_cexp_Ioi {w : ℂ} (hw : 0 < w.re) :
    (∫ t in Ioi (0 : ℝ), Complex.exp (-(w * t))) = w⁻¹ := by
  have hcongr : (∫ t in Ioi (0 : ℝ), cgammaOrd 1 w t) =
      ∫ t in Ioi (0 : ℝ), Complex.exp (-(w * t)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : (0 : ℝ) < t := ht
    rw [cgammaOrd, sub_self, Real.rpow_zero, Complex.ofReal_one, mul_one]
  rw [← hcongr, show (∫ t in Ioi (0 : ℝ), cgammaOrd 1 w t) = cgammaOrdIntegral 1 w from rfl,
    cgammaOrdIntegral_eq one_pos hw, Real.Gamma_one]
  have hpow : w ^ ((-1 : ℝ) : ℂ) = w⁻¹ := by
    norm_num [Complex.cpow_neg_one]
  rw [hpow, Complex.ofReal_one, one_mul]

theorem integrableOn_cexp_Ioi {w : ℂ} (hw : 0 < w.re) :
    IntegrableOn (fun t : ℝ => Complex.exp (-(w * t))) (Ioi 0) := by
  have h := integrableOn_cgammaOrd one_pos hw
  refine h.congr_fun (fun t ht => ?_) measurableSet_Ioi
  have ht0 : (0 : ℝ) < t := ht
  rw [cgammaOrd, sub_self, Real.rpow_zero, Complex.ofReal_one, mul_one]

/-- **The two halves have derivative `−1/w`.** -/
theorem hasDerivAt_clogSum {w : ℂ} (hw : 0 < w.re) :
    HasDerivAt (fun v : ℂ => clogHead v + clogTail v) (-w⁻¹) w := by
  have hhead := hasDerivAt_clogHead hw
  have htail := hasDerivAt_clogTail hw
  have hsum := hhead.add htail
  have hint := integrableOn_cexp_Ioi hw
  have hdisj : Disjoint (Ioc (0 : ℝ) 1) (Ioi 1) := by
    rw [Set.disjoint_left]
    rintro t ⟨-, ht2⟩ ht3
    exact absurd ht3 (not_lt.2 ht2)
  have hunion : Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 := by
    ext t
    simp only [mem_Ioi, mem_union, mem_Ioc]
    constructor
    · intro ht
      rcases le_or_gt t 1 with h | h
      · exact Or.inl ⟨ht, h⟩
      · exact Or.inr h
    · rintro (⟨h, -⟩ | h)
      · exact h
      · linarith
  have hsplit : (∫ t in Ioi (0 : ℝ), Complex.exp (-(w * t))) =
      (∫ t in Ioo (0 : ℝ) 1, Complex.exp (-(w * t))) +
        ∫ t in Ioi (1 : ℝ), Complex.exp (-(w * t)) := by
    rw [hunion] at hint
    have h1 : IntegrableOn (fun t : ℝ => Complex.exp (-(w * t))) (Ioc 0 1) :=
      hint.mono_set Set.subset_union_left
    have h2 : IntegrableOn (fun t : ℝ => Complex.exp (-(w * t))) (Ioi 1) :=
      hint.mono_set Set.subset_union_right
    rw [hunion, setIntegral_union hdisj measurableSet_Ioi h1 h2, integral_Ioc_eq_integral_Ioo]
  have hval : (∫ t in Ioo (0 : ℝ) 1, cgammaDeriv 0 w t) +
      ∫ t in Ioi (1 : ℝ), cgammaOrdDeriv 0 w t = -w⁻¹ := by
    have hh : (∫ t in Ioo (0 : ℝ) 1, cgammaDeriv 0 w t) =
        ∫ t in Ioo (0 : ℝ) 1, -Complex.exp (-(w * t)) :=
      setIntegral_congr_fun measurableSet_Ioo fun t ht => cgammaDeriv_zero ht.1
    have htl : (∫ t in Ioi (1 : ℝ), cgammaOrdDeriv 0 w t) =
        ∫ t in Ioi (1 : ℝ), -Complex.exp (-(w * t)) :=
      setIntegral_congr_fun measurableSet_Ioi fun t ht =>
        cgammaOrdDeriv_zero (lt_trans zero_lt_one ht)
    rw [hh, htl, integral_neg, integral_neg, ← neg_add, ← hsplit, integral_cexp_Ioi hw]
  rwa [hval] at hsum

/-! ## The rotated constant -/

theorem clogHead_one : clogHead 1 = (gammaHead 0 : ℂ) := by
  have hcongr : (∫ t in Ioo (0 : ℝ) 1, cgammaDefect 0 (1 : ℂ) t) =
      ∫ t in Ioo (0 : ℝ) 1, ((gammaDefect 0 t : ℝ) : ℂ) := by
    refine setIntegral_congr_fun measurableSet_Ioo fun t _ => ?_
    have h := cgammaDefect_ofReal 0 1 t
    rw [Complex.ofReal_one] at h
    rw [h, gammaDefect, laplaceCochain, one_mul]
  have hint : IntegrableOn (fun t : ℝ => gammaDefect 0 t) (Ioo 0 1) :=
    (integrableOn_gammaDefect_Ioc (a := 0) (by norm_num)).mono_set Ioo_subset_Ioc_self
  have hcast : (∫ t in Ioo (0 : ℝ) 1, ((gammaDefect 0 t : ℝ) : ℂ)) =
      ((∫ t in Ioo (0 : ℝ) 1, gammaDefect 0 t : ℝ) : ℂ) :=
    ContinuousLinearMap.integral_comp_comm Complex.ofRealCLM hint
  rw [clogHead, hcongr, hcast, gammaHead]

theorem clogTail_one : clogTail 1 = (gammaTail 0 : ℂ) := by
  have hcongr : (∫ t in Ioi (1 : ℝ), cgammaOrd 0 (1 : ℂ) t) =
      ∫ t in Ioi (1 : ℝ), ((Real.exp (-t) * t ^ (0 - 1 : ℝ) : ℝ) : ℂ) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    have h := cgammaOrd_ofReal 0 1 t
    rw [Complex.ofReal_one] at h
    rw [h, one_mul]
  have hint : IntegrableOn (fun t : ℝ => Real.exp (-t) * t ^ (0 - 1 : ℝ)) (Ioi 1) :=
    integrableOn_gammaTailFun (a := 0) (by norm_num)
  have hcast : (∫ t in Ioi (1 : ℝ), ((Real.exp (-t) * t ^ (0 - 1 : ℝ) : ℝ) : ℂ)) =
      ((∫ t in Ioi (1 : ℝ), Real.exp (-t) * t ^ (0 - 1 : ℝ) : ℝ) : ℂ) :=
    ContinuousLinearMap.integral_comp_comm Complex.ofRealCLM hint
  rw [clogTail, hcongr, hcast, gammaTail]

/-- **The rotated exponential-integral constant.** -/
theorem clogHead_add_clogTail {w : ℂ} (hw : 0 < w.re) :
    clogHead w + clogTail w = -(Real.eulerMascheroniConstant : ℂ) - Complex.log w := by
  set S : Set ℂ := {v : ℂ | 0 < v.re} with hSdef
  have hopen : IsOpen S := isOpen_lt continuous_const Complex.continuous_re
  have hconv : Convex ℝ S := convex_halfSpace_re_gt 0
  set F : ℂ → ℂ := fun v => clogHead v + clogTail v + Complex.log v with hFdef
  have hderiv : ∀ v ∈ S, HasDerivAt F 0 v := by
    intro v hv
    have hv' : 0 < v.re := hv
    have hlog : HasDerivAt Complex.log v⁻¹ v := Complex.hasDerivAt_log (Or.inl hv')
    have h := (hasDerivAt_clogSum hv').add hlog
    have hz : -v⁻¹ + v⁻¹ = 0 := by ring
    rw [hz] at h
    exact h
  have hdiffOn : DifferentiableOn ℂ F S := fun v hv =>
    ((hderiv v hv).differentiableAt).differentiableWithinAt
  have hzero : ∀ v ∈ S, fderivWithin ℂ F S v = 0 := by
    intro v hv
    rw [fderivWithin_of_isOpen hopen hv]
    have hfd : HasFDerivAt F (ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) 0) v :=
      hasDerivAt_iff_hasFDerivAt.1 (hderiv v hv)
    rw [hfd.fderiv]
    simp
  have hone : (1 : ℂ) ∈ S := by simp [hSdef]
  have hconst := hconv.is_const_of_fderivWithin_eq_zero (𝕜 := ℂ) hdiffOn hzero hw hone
  have hF1 : F 1 = -(Real.eulerMascheroniConstant : ℂ) := by
    show clogHead 1 + clogTail 1 + Complex.log 1 = -(Real.eulerMascheroniConstant : ℂ)
    rw [Complex.log_one, add_zero, clogHead_one, clogTail_one, ← Complex.ofReal_add,
      gammaHead_add_gammaTail, Complex.ofReal_neg]
  rw [hF1] at hconst
  have hFw : clogHead w + clogTail w + Complex.log w = -(Real.eulerMascheroniConstant : ℂ) :=
    hconst
  linear_combination hFw

end

end GaloisForLFunctions.HTGeometry.Interfinity
