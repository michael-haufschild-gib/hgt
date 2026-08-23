import GaloisForLFunctions.RHTower.ThetaCuspHawkingFullMirrorValueMixingEndpoint
import GaloisForLFunctions.RHTower.BoundedSupportFourierUncertainty
import GaloisForLFunctions.HTGeometry.RealFiniteAnalyticEscape
import GaloisForLFunctions.HTGeometry.AnalyticNullPreimage

/-!
# Generic common-coupling mixing for the full theta-cusp Hawking mirror

The exact Davies--Fulling eikonal response extends from real mirror coupling to an entire
complex-coupling function.  Consequently each fixed positive-frequency tilted sector has only
countably many real dark couplings.  Baire escape then gives one arbitrarily weak, nonzero physical
mirror coupling which activates every member of any countable positive-frequency resonance family.

This is a source-faithful full-scattering theorem, not the scalar Cayley completion.  It proves that
finite-coupling dynamics generically forces all countably many tilted sectors to mix.  It is
unconditional and therefore not an RH producer: the RH-bearing datum remains whether every sector
starts at first coupling order, rather than only at some finite order.
-/

open Complex Real MeasureTheory ProbabilityTheory Set Filter Topology
open scoped FourierTransform SchwartzMap ENNReal NNReal

noncomputable section

namespace RHTower

/-! ## Entire complex-density moment-generating transforms -/

def complexDensityMGF (X : ℝ → ℝ) (f : ℝ → ℂ) (z : ℂ) : ℂ :=
  complexMGF X (realPosMeasure f) z - complexMGF X (realNegMeasure f) z +
    Complex.I *
      (complexMGF X (imagPosMeasure f) z - complexMGF X (imagNegMeasure f) z)

private lemma complexMGF_realPosMeasure_comp_eq_integral
    {X : ℝ → ℝ} {f : ℝ → ℂ} (hf : Integrable f) (z : ℂ) :
    complexMGF X (realPosMeasure f) z =
      ∫ x : ℝ, Complex.exp (z * X x) * ((f x).re)⁺ := by
  unfold complexMGF realPosMeasure
  change (∫ x : ℝ, Complex.exp (z * X x) ∂volume.withDensity
      (fun x ↦ ENNReal.ofReal (max (f x).re 0))) =
    ∫ x : ℝ, Complex.exp (z * X x) * (max (f x).re 0 : ℝ)
  have hmeas : AEMeasurable
      (fun x ↦ ENNReal.ofReal (max (f x).re 0)) volume := by
    fun_prop
  rw [integral_withDensity_eq_integral_toReal_smul₀ hmeas]
  · apply integral_congr_ae
    filter_upwards with x
    rw [ENNReal.toReal_ofReal']
    simp only [max_eq_left (le_max_right _ _)]
    rw [Complex.real_smul]
    ring
  · filter_upwards with x
    exact ENNReal.ofReal_lt_top

private lemma complexMGF_realNegMeasure_comp_eq_integral
    {X : ℝ → ℝ} {f : ℝ → ℂ} (hf : Integrable f) (z : ℂ) :
    complexMGF X (realNegMeasure f) z =
      ∫ x : ℝ, Complex.exp (z * X x) * ((f x).re)⁻ := by
  unfold complexMGF realNegMeasure
  change (∫ x : ℝ, Complex.exp (z * X x) ∂volume.withDensity
      (fun x ↦ ENNReal.ofReal (max (-(f x).re) 0))) =
    ∫ x : ℝ, Complex.exp (z * X x) * (max (-(f x).re) 0 : ℝ)
  have hmeas : AEMeasurable
      (fun x ↦ ENNReal.ofReal (max (-(f x).re) 0)) volume := by
    fun_prop
  rw [integral_withDensity_eq_integral_toReal_smul₀ hmeas]
  · apply integral_congr_ae
    filter_upwards with x
    rw [ENNReal.toReal_ofReal']
    simp only [max_eq_left (le_max_right _ _)]
    rw [Complex.real_smul]
    ring
  · filter_upwards with x
    exact ENNReal.ofReal_lt_top

private lemma complexMGF_imagPosMeasure_comp_eq_integral
    {X : ℝ → ℝ} {f : ℝ → ℂ} (hf : Integrable f) (z : ℂ) :
    complexMGF X (imagPosMeasure f) z =
      ∫ x : ℝ, Complex.exp (z * X x) * ((f x).im)⁺ := by
  unfold complexMGF imagPosMeasure
  change (∫ x : ℝ, Complex.exp (z * X x) ∂volume.withDensity
      (fun x ↦ ENNReal.ofReal (max (f x).im 0))) =
    ∫ x : ℝ, Complex.exp (z * X x) * (max (f x).im 0 : ℝ)
  have hmeas : AEMeasurable
      (fun x ↦ ENNReal.ofReal (max (f x).im 0)) volume := by
    fun_prop
  rw [integral_withDensity_eq_integral_toReal_smul₀ hmeas]
  · apply integral_congr_ae
    filter_upwards with x
    rw [ENNReal.toReal_ofReal']
    simp only [max_eq_left (le_max_right _ _)]
    rw [Complex.real_smul]
    ring
  · filter_upwards with x
    exact ENNReal.ofReal_lt_top

private lemma complexMGF_imagNegMeasure_comp_eq_integral
    {X : ℝ → ℝ} {f : ℝ → ℂ} (hf : Integrable f) (z : ℂ) :
    complexMGF X (imagNegMeasure f) z =
      ∫ x : ℝ, Complex.exp (z * X x) * ((f x).im)⁻ := by
  unfold complexMGF imagNegMeasure
  change (∫ x : ℝ, Complex.exp (z * X x) ∂volume.withDensity
      (fun x ↦ ENNReal.ofReal (max (-(f x).im) 0))) =
    ∫ x : ℝ, Complex.exp (z * X x) * (max (-(f x).im) 0 : ℝ)
  have hmeas : AEMeasurable
      (fun x ↦ ENNReal.ofReal (max (-(f x).im) 0)) volume := by
    fun_prop
  rw [integral_withDensity_eq_integral_toReal_smul₀ hmeas]
  · apply integral_congr_ae
    filter_upwards with x
    rw [ENNReal.toReal_ofReal']
    simp only [max_eq_left (le_max_right _ _)]
    rw [Complex.real_smul]
    ring
  · filter_upwards with x
    exact ENNReal.ofReal_lt_top

theorem complexDensityMGF_analyticOnNhd_of_bounded
    {X : ℝ → ℝ} {f : ℝ → ℂ} {A B : ℝ}
    (hX : Continuous X) (hf : Integrable f)
    (hbound : ∀ x, X x ∈ Set.Icc A B) :
    AnalyticOnNhd ℂ (complexDensityMGF X f) Set.univ := by
  have hb (μ : Measure ℝ) : ∀ᵐ x ∂μ, X x ∈ Set.Icc A B :=
    Filter.Eventually.of_forall hbound
  have hp : AnalyticOnNhd ℂ (complexMGF X (realPosMeasure f)) Set.univ := by
    letI := realPosMeasure_finite hf
    exact analyticOnNhd_complexMGF_univ_of_bounded hX.aemeasurable
      (hb (realPosMeasure f))
  have hn : AnalyticOnNhd ℂ (complexMGF X (realNegMeasure f)) Set.univ := by
    letI := realNegMeasure_finite hf
    exact analyticOnNhd_complexMGF_univ_of_bounded hX.aemeasurable
      (hb (realNegMeasure f))
  have hip : AnalyticOnNhd ℂ (complexMGF X (imagPosMeasure f)) Set.univ := by
    letI := imagPosMeasure_finite hf
    exact analyticOnNhd_complexMGF_univ_of_bounded hX.aemeasurable
      (hb (imagPosMeasure f))
  have hin : AnalyticOnNhd ℂ (complexMGF X (imagNegMeasure f)) Set.univ := by
    letI := imagNegMeasure_finite hf
    exact analyticOnNhd_complexMGF_univ_of_bounded hX.aemeasurable
      (hb (imagNegMeasure f))
  exact (hp.sub hn).add (analyticOnNhd_const.mul (hip.sub hin))

private lemma integrable_exp_neg_I_mul_ofReal_mul_component
    {X g : ℝ → ℝ} (hX : AEStronglyMeasurable X) (hg : Integrable g) (t : ℝ) :
    Integrable (fun x : ℝ =>
      Complex.exp ((-Complex.I * (t : ℂ)) * X x) * (g x : ℂ)) := by
  refine hg.ofReal.bdd_mul (c := 1) ?_ ?_
  · fun_prop
  · filter_upwards with x
    rw [Complex.norm_exp]
    have hre : ((-Complex.I * (t : ℂ)) * (X x : ℂ)).re = 0 := by simp
    rw [hre, Real.exp_zero]

theorem complexDensityMGF_neg_I_ofReal_eq_integral
    {X : ℝ → ℝ} {f : ℝ → ℂ} (hX : AEStronglyMeasurable X)
    (hf : Integrable f) (t : ℝ) :
    complexDensityMGF X f (-Complex.I * (t : ℂ)) =
      ∫ x : ℝ, Complex.exp ((-Complex.I * (t : ℂ)) * X x) * f x := by
  have hrp : Integrable (fun x : ℝ =>
      Complex.exp ((-Complex.I * (t : ℂ)) * X x) *
        (((((f x).re)⁺ : ℝ)) : ℂ)) := by
    exact integrable_exp_neg_I_mul_ofReal_mul_component
      (X := X) hX hf.re.pos_part t
  have hrn : Integrable (fun x : ℝ =>
      Complex.exp ((-Complex.I * (t : ℂ)) * X x) *
        (((((f x).re)⁻ : ℝ)) : ℂ)) := by
    exact integrable_exp_neg_I_mul_ofReal_mul_component
      (X := X) hX hf.re.neg_part t
  have hip : Integrable (fun x : ℝ =>
      Complex.exp ((-Complex.I * (t : ℂ)) * X x) *
        (((((f x).im)⁺ : ℝ)) : ℂ)) := by
    exact integrable_exp_neg_I_mul_ofReal_mul_component
      (X := X) hX hf.im.pos_part t
  have hin : Integrable (fun x : ℝ =>
      Complex.exp ((-Complex.I * (t : ℂ)) * X x) *
        (((((f x).im)⁻ : ℝ)) : ℂ)) := by
    exact integrable_exp_neg_I_mul_ofReal_mul_component
      (X := X) hX hf.im.neg_part t
  have hrealDiff : Integrable (fun x : ℝ =>
      Complex.exp ((-Complex.I * (t : ℂ)) * X x) * ((f x).re)⁺ -
        Complex.exp ((-Complex.I * (t : ℂ)) * X x) * ((f x).re)⁻) :=
    hrp.sub hrn
  have himagDiff : Integrable (fun x : ℝ => Complex.I *
      (Complex.exp ((-Complex.I * (t : ℂ)) * X x) * ((f x).im)⁺ -
        Complex.exp ((-Complex.I * (t : ℂ)) * X x) * ((f x).im)⁻)) :=
    (hip.sub hin).const_mul Complex.I
  rw [complexDensityMGF,
    complexMGF_realPosMeasure_comp_eq_integral hf,
    complexMGF_realNegMeasure_comp_eq_integral hf,
    complexMGF_imagPosMeasure_comp_eq_integral hf,
    complexMGF_imagNegMeasure_comp_eq_integral hf]
  rw [← integral_sub hrp hrn, ← integral_sub hip hin, ← integral_const_mul]
  rw [← integral_add hrealDiff himagDiff]
  apply integral_congr_ae
  filter_upwards with x
  rw [← mul_sub, ← mul_sub]
  have hreC :
      (↑(((f x).re)⁺) : ℂ) - (↑(((f x).re)⁻) : ℂ) = (f x).re := by
    exact_mod_cast posPart_sub_negPart (f x).re
  have himC :
      (↑(((f x).im)⁺) : ℂ) - (↑(((f x).im)⁻) : ℂ) = (f x).im := by
    exact_mod_cast posPart_sub_negPart (f x).im
  rw [hreC, himC]
  have hf_parts : ((f x).re : ℂ) + Complex.I * (f x).im = f x := by
    simpa [mul_comm] using Complex.re_add_im (f x)
  calc
    Complex.exp ((-Complex.I * (t : ℂ)) * X x) * ((f x).re : ℂ) +
        Complex.I *
          (Complex.exp ((-Complex.I * (t : ℂ)) * X x) * ((f x).im : ℂ)) =
      Complex.exp ((-Complex.I * (t : ℂ)) * X x) *
        (((f x).re : ℂ) + Complex.I * (f x).im) := by ring
    _ = Complex.exp ((-Complex.I * (t : ℂ)) * X x) * f x := by rw [hf_parts]

/-! ## Complexified full-mirror coupling -/

private def thetaCuspHawkingCouplingDerivativeDensity
    (a total v : ℝ) : ℂ :=
  Complex.exp (((-total * v : ℝ) : ℂ) * Complex.I) *
    (-Complex.I * (thetaCuspTiltedSource a v : ℂ))

private theorem thetaCuspHawkingCouplingDerivativeDensity_integrable
    (a : ℝ) (ha : |a| < 1) (total : ℝ) :
    Integrable (thetaCuspHawkingCouplingDerivativeDensity a total) := by
  let source : 𝓢(ℝ, ℂ) := thetaCuspTiltedSchwartz a ha
  have hscaled : Integrable (fun v : ℝ => -Complex.I * source v) :=
    source.integrable.const_mul (-Complex.I)
  have hphase : AEStronglyMeasurable (fun v : ℝ =>
      Complex.exp (((-total * v : ℝ) : ℂ) * Complex.I)) := by
    apply Continuous.aestronglyMeasurable
    fun_prop
  have hmul := hscaled.bdd_mul (c := 1) hphase (by
    filter_upwards with v
    rw [Complex.norm_exp]
    simp)
  unfold thetaCuspHawkingCouplingDerivativeDensity
  change Integrable (fun v : ℝ =>
    Complex.exp (((-total * v : ℝ) : ℂ) * Complex.I) *
      (-Complex.I * source v))
  exact hmul

private def thetaCuspTiltedSourceSupBound
    (a : ℝ) (ha : |a| < 1) : ℝ :=
  SchwartzMap.seminorm ℝ 0 0 (thetaCuspTiltedSchwartzReal a ha)

private theorem thetaCuspTiltedSource_mem_Icc_supBound
    (a : ℝ) (ha : |a| < 1) (v : ℝ) :
    thetaCuspTiltedSource a v ∈
      Set.Icc 0 (thetaCuspTiltedSourceSupBound a ha) := by
  constructor
  · exact (by
      unfold thetaCuspTiltedSource
      exact (mul_pos (Real.exp_pos _) (thetaCuspFullSource_pos_all v)).le)
  · let source : 𝓢(ℝ, ℝ) := thetaCuspTiltedSchwartzReal a ha
    have hpos : 0 < thetaCuspTiltedSource a v := by
      unfold thetaCuspTiltedSource
      exact mul_pos (Real.exp_pos _) (thetaCuspFullSource_pos_all v)
    have hnorm := SchwartzMap.norm_le_seminorm ℝ source v
    simpa [source, thetaCuspTiltedSourceSupBound, Real.norm_eq_abs,
      abs_of_pos hpos] using hnorm

/-- Entire derivative of exact eikonal scattering with respect to complexified coupling. -/
def thetaCuspHawkingEikonalCouplingDerivativeEntire
    (a total : ℝ) (z : ℂ) : ℂ :=
  complexDensityMGF (thetaCuspTiltedSource a)
    (thetaCuspHawkingCouplingDerivativeDensity a total)
    (-Complex.I * z)

theorem thetaCuspHawkingEikonalCouplingDerivativeEntire_analyticOnNhd
    (a : ℝ) (ha : |a| < 1) (total : ℝ) :
    AnalyticOnNhd ℂ
      (thetaCuspHawkingEikonalCouplingDerivativeEntire a total) Set.univ := by
  have hmgf := complexDensityMGF_analyticOnNhd_of_bounded
    (X := thetaCuspTiltedSource a)
    (f := thetaCuspHawkingCouplingDerivativeDensity a total)
    (A := 0) (B := thetaCuspTiltedSourceSupBound a ha)
    (contDiff_thetaCuspTiltedSource a).continuous
    (thetaCuspHawkingCouplingDerivativeDensity_integrable a ha total)
    (thetaCuspTiltedSource_mem_Icc_supBound a ha)
  intro z _hz
  change AnalyticAt ℂ (fun q : ℂ => complexDensityMGF
    (thetaCuspTiltedSource a)
    (thetaCuspHawkingCouplingDerivativeDensity a total)
    (-Complex.I * q)) z
  exact (hmgf _ (Set.mem_univ _)).comp
    (analyticAt_const.mul analyticAt_id)

theorem thetaCuspHawkingEikonalCouplingDerivativeEntire_ofReal
    (a : ℝ) (ha : |a| < 1) (total t : ℝ) :
    thetaCuspHawkingEikonalCouplingDerivativeEntire a total (t : ℂ) =
      thetaCuspHawkingFullMirrorCouplingJetIntegral a total 1 t := by
  rw [thetaCuspHawkingEikonalCouplingDerivativeEntire,
    complexDensityMGF_neg_I_ofReal_eq_integral
      (contDiff_thetaCuspTiltedSource a).continuous.aestronglyMeasurable
      (thetaCuspHawkingCouplingDerivativeDensity_integrable a ha total)]
  rw [thetaCuspHawkingFullMirrorCouplingJetIntegral_eq_integral]
  apply integral_congr_ae
  filter_upwards with v
  simp only [thetaCuspHawkingCouplingDerivativeDensity]
  push_cast
  ring_nf

private theorem exists_thetaCuspHawkingEikonalCouplingEntirePrimitive
    (a : ℝ) (ha : |a| < 1) (total : ℝ) :
    ∃ F : ℂ → ℂ, F 0 = 0 ∧ ∀ z : ℂ,
      HasDerivAt F
        (thetaCuspHawkingEikonalCouplingDerivativeEntire a total z) z := by
  have hdiff : Differentiable ℂ
      (thetaCuspHawkingEikonalCouplingDerivativeEntire a total) :=
    fun z => (thetaCuspHawkingEikonalCouplingDerivativeEntire_analyticOnNhd
      a ha total z (Set.mem_univ z)).differentiableAt
  obtain ⟨F, hF⟩ := hdiff.isExactOn_univ
  refine ⟨fun z => F z - F 0, by simp, fun z => ?_⟩
  exact (hF z (Set.mem_univ z)).sub_const (F 0)

/-- Canonical normalized entire extension of exact eikonal coupling response. -/
def thetaCuspHawkingEikonalCouplingEntire
    (a : ℝ) (ha : |a| < 1) (total : ℝ) : ℂ → ℂ :=
  (exists_thetaCuspHawkingEikonalCouplingEntirePrimitive a ha total).choose

@[simp] theorem thetaCuspHawkingEikonalCouplingEntire_zero
    (a : ℝ) (ha : |a| < 1) (total : ℝ) :
    thetaCuspHawkingEikonalCouplingEntire a ha total 0 = 0 :=
  (exists_thetaCuspHawkingEikonalCouplingEntirePrimitive a ha total).choose_spec.1

theorem hasDerivAt_thetaCuspHawkingEikonalCouplingEntire
    (a : ℝ) (ha : |a| < 1) (total : ℝ) (z : ℂ) :
    HasDerivAt (thetaCuspHawkingEikonalCouplingEntire a ha total)
      (thetaCuspHawkingEikonalCouplingDerivativeEntire a total z) z :=
  (exists_thetaCuspHawkingEikonalCouplingEntirePrimitive a ha total).choose_spec.2 z

theorem thetaCuspHawkingEikonalCouplingEntire_analyticOnNhd
    (a : ℝ) (ha : |a| < 1) (total : ℝ) :
    AnalyticOnNhd ℂ
      (thetaCuspHawkingEikonalCouplingEntire a ha total) Set.univ :=
  analyticOnNhd_univ_iff_differentiable.mpr fun z =>
    (hasDerivAt_thetaCuspHawkingEikonalCouplingEntire
      a ha total z).differentiableAt

theorem thetaCuspHawkingEikonalCouplingEntire_ofReal
    (a : ℝ) (ha : |a| < 1) (total t : ℝ) :
    thetaCuspHawkingEikonalCouplingEntire a ha total (t : ℂ) =
      thetaCuspHawkingEikonalFourier a t total := by
  let g : ℝ → ℂ := fun q =>
    thetaCuspHawkingEikonalCouplingEntire a ha total (q : ℂ) -
      thetaCuspHawkingEikonalFourier a q total
  have hgDeriv (q : ℝ) : HasDerivAt g 0 q := by
    have hleft := (hasDerivAt_thetaCuspHawkingEikonalCouplingEntire
      a ha total (q : ℂ)).comp_ofReal
    have hright := hasDerivAt_thetaCuspHawkingEikonalFourier_all a ha total q
    rw [thetaCuspHawkingEikonalCouplingDerivativeEntire_ofReal a ha total q]
      at hleft
    change HasDerivAt
      ((fun y : ℝ => thetaCuspHawkingEikonalCouplingEntire
          a ha total (y : ℂ)) -
        fun y : ℝ => thetaCuspHawkingEikonalFourier a y total) 0 q
    simpa only [sub_self] using hleft.sub hright
  have hgDiff : Differentiable ℝ g := fun q => (hgDeriv q).differentiableAt
  have hgZero : ∀ q : ℝ, deriv g q = 0 := fun q => (hgDeriv q).deriv
  have hconst : g t = g 0 := is_const_of_deriv_eq_zero hgDiff hgZero t 0
  have heikZero : thetaCuspHawkingEikonalFourier a 0 total = 0 := by
    have hzero : thetaCuspHawkingEikonalPhaseDefect a 0 = 0 := by
      funext v
      simp [thetaCuspHawkingEikonalPhaseDefect]
    rw [thetaCuspHawkingEikonalFourier,
      Real.fourier_real_eq_integral_exp_smul, hzero]
    simp
  exact sub_eq_zero.mp (by simpa [g, heikZero] using hconst)

theorem thetaCuspHawkingEikonalFourier_analyticOnNhd_coupling
    (a : ℝ) (ha : |a| < 1) (total : ℝ) :
    AnalyticOnNhd ℝ
      (fun t : ℝ => thetaCuspHawkingEikonalFourier a t total) Set.univ := by
  have hrestrict : AnalyticOnNhd ℝ
      (fun t : ℝ => thetaCuspHawkingEikonalCouplingEntire a ha total (t : ℂ))
      Set.univ := by
    intro t _ht
    exact (thetaCuspHawkingEikonalCouplingEntire_analyticOnNhd
      a ha total (t : ℂ) (Set.mem_univ _)).restrictScalars.comp
        (Complex.ofRealCLM.analyticAt t)
  exact hrestrict.congr isOpen_univ fun t _ht =>
    thetaCuspHawkingEikonalCouplingEntire_ofReal a ha total t

theorem thetaCuspHawkingBalancedFullMirrorAmplitude_analyticOnNhd_coupling
    (a omega : ℝ) (ha : |a| < 1) :
    AnalyticOnNhd ℝ
      (fun lambda : ℝ => thetaCuspHawkingBalancedFullMirrorAmplitude
        a lambda omega) Set.univ := by
  have heik := thetaCuspHawkingEikonalFourier_analyticOnNhd_coupling
    a ha omega
  have hfun :
      (fun lambda : ℝ => thetaCuspHawkingBalancedFullMirrorAmplitude
        a lambda omega) =
      fun lambda : ℝ => ((-2 * (omega / 2) : ℝ) : ℂ) *
        thetaCuspHawkingEikonalFourier a (lambda * (omega / 2)) omega := by
    funext lambda
    unfold thetaCuspHawkingBalancedFullMirrorAmplitude
    rw [thetaCuspHawkingFullMirrorAmplitude_eq_eikonalFourier a ha]
    (congr 2; ring_nf)
  rw [hfun]
  intro lambda _hlambda
  apply analyticAt_const.mul
  exact (heik _ (Set.mem_univ _)).comp
    (analyticAt_id.mul analyticAt_const)

/-- Real mirror couplings at which one balanced tilted sector is exactly dark. -/
def thetaCuspHawkingFullMirrorDarkCouplings
    (a omega : ℝ) : Set ℝ :=
  {lambda | thetaCuspHawkingBalancedFullMirrorAmplitude a lambda omega = 0}

/-- Every fixed positive tilted sector has only countably many exactly dark real couplings. -/
theorem thetaCuspHawkingFullMirrorDarkCouplings_countable
    (a omega : ℝ) (ha : |a| < 1) (homega : 0 < omega) :
    (thetaCuspHawkingFullMirrorDarkCouplings a omega).Countable := by
  let response : ℝ → ℂ := fun lambda =>
    thetaCuspHawkingBalancedFullMirrorAmplitude a lambda omega
  let energy : ℝ → ℝ := fun lambda => Complex.normSq (response lambda)
  have hresponse : AnalyticOnNhd ℝ response Set.univ :=
    thetaCuspHawkingBalancedFullMirrorAmplitude_analyticOnNhd_coupling
      a omega ha
  have hre : AnalyticOnNhd ℝ (fun lambda => (response lambda).re) Set.univ :=
    Complex.reCLM.comp_analyticOnNhd hresponse
  have him : AnalyticOnNhd ℝ (fun lambda => (response lambda).im) Set.univ :=
    Complex.imCLM.comp_analyticOnNhd hresponse
  have henergy : AnalyticOnNhd ℝ energy Set.univ := by
    have hsum := (hre.mul hre).add (him.mul him)
    rw [show energy = fun lambda =>
        (response lambda).re * (response lambda).re +
          (response lambda).im * (response lambda).im by
      funext lambda
      simp [energy, Complex.normSq_apply]]
    exact hsum
  obtain ⟨lambda, _hlambda0, _hlambda1, hne⟩ :=
    exists_arbitrarily_weak_thetaCuspHawkingFullMirrorAmplitude_ne_zero
      a omega ha homega 1 zero_lt_one
  have henergyNe : energy lambda ≠ 0 := by
    exact (Complex.normSq_pos.mpr hne).ne'
  have hcount :=
    GaloisForLFunctions.HTGeometry.analytic_zero_set_countable
      henergy ⟨lambda, henergyNe⟩
  exact hcount.mono (by
    intro t ht
    change thetaCuspHawkingBalancedFullMirrorAmplitude a t omega = 0 at ht
    change energy t = 0
    simp [energy, response, ht])

theorem exists_arbitrarily_weak_common_thetaCuspHawkingFullMirror_mix
    {ι : Type*} [Countable ι] [Nonempty ι]
    (a omega : ι → ℝ) (ha : ∀ i, |a i| < 1)
    (homega : ∀ i, 0 < omega i) (ε : ℝ) (hε : 0 < ε) :
    ∃ lambda : ℝ, 0 < |lambda| ∧ |lambda| < ε ∧
      ∀ i, thetaCuspHawkingBalancedFullMirrorAmplitude
        (a i) lambda (omega i) ≠ 0 := by
  let response : ι → ℝ → ℂ := fun i lambda =>
    thetaCuspHawkingBalancedFullMirrorAmplitude (a i) lambda (omega i)
  let U : Set ℝ := Set.Ioo (-ε) ε
  have hUopen : IsOpen U := isOpen_Ioo
  have hUconn : IsPreconnected U := convex_Ioo (-ε) ε |>.isPreconnected
  have hUnonempty : U.Nonempty := by
    exact ⟨0, by simp [U, hε]⟩
  have hanalytic : ∀ i, AnalyticOnNhd ℝ (response i) U := by
    intro i
    exact (thetaCuspHawkingBalancedFullMirrorAmplitude_analyticOnNhd_coupling
      (a i) (omega i) (ha i)).mono (Set.subset_univ U)
  have hnontrivial : ∀ i, ∃ lambda ∈ U, response i lambda ≠ 0 := by
    intro i
    obtain ⟨lambda, hlambda0, hlambdaε, hA⟩ :=
      exists_arbitrarily_weak_thetaCuspHawkingFullMirrorAmplitude_ne_zero
        (a i) (omega i) (ha i) (homega i) ε hε
    exact ⟨lambda, by simpa [U, abs_lt] using hlambdaε, hA⟩
  obtain ⟨lambda, hlambdaU, hall⟩ :=
    GaloisForLFunctions.HTGeometry.exists_forall_neZero_of_countable_analyticOnNhd_real_local
      response U hUopen hUconn hUnonempty hanalytic hnontrivial
  have hlambdaε : |lambda| < ε := by simpa [U, abs_lt] using hlambdaU
  have hlambda0 : lambda ≠ 0 := by
    obtain ⟨i⟩ := ‹Nonempty ι›
    intro hzero
    subst lambda
    apply hall i
    have heikZero : thetaCuspHawkingEikonalFourier (a i) 0 (omega i) = 0 := by
      have hzeroPhase : thetaCuspHawkingEikonalPhaseDefect (a i) 0 = 0 := by
        funext v
        simp [thetaCuspHawkingEikonalPhaseDefect]
      rw [thetaCuspHawkingEikonalFourier,
        Real.fourier_real_eq_integral_exp_smul, hzeroPhase]
      simp
    simp only [response, thetaCuspHawkingBalancedFullMirrorAmplitude,
      thetaCuspHawkingFullMirrorAmplitude_eq_eikonalFourier (ha := ha i),
      zero_mul]
    rw [show omega i / 2 + omega i / 2 = omega i by ring, heikZero, mul_zero]
  exact ⟨lambda, abs_pos.mpr hlambda0, hlambdaε, hall⟩

end RHTower
