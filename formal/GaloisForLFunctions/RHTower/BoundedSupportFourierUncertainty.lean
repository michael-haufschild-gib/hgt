/-
BRIDGE (classical harmonic-analysis infrastructure).

An unconditional bounded-support Fourier uncertainty theorem for complex-valued L¹ functions on
ℝ. The proof builds the missing analytic continuation from finite positive density measures, uses
the identity theorem to propagate vanishing of the Fourier integral, and finishes with uniqueness
of characteristic functions. No Paley-Wiener theorem is assumed.
-/
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.MeasureTheory.VectorMeasure.WithDensity
import Mathlib.Analysis.Analytic.IsolatedZeros

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Complex
open scoped FourierTransform MeasureTheory Topology ENNReal NNReal

namespace RHTower

lemma analyticOnNhd_complexMGF_univ_of_bounded
    {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : Ω → ℝ} {a b : ℝ} (hX : AEMeasurable X μ)
    (hb : ∀ᵐ ω ∂μ, X ω ∈ Icc a b) :
    AnalyticOnNhd ℂ (complexMGF X μ) univ := by
  have hset : integrableExpSet X μ = univ := by
    apply Set.eq_univ_of_forall
    intro t
    exact integrable_exp_mul_of_mem_Icc hX hb
  simpa [hset] using (analyticOnNhd_complexMGF (X := X) (μ := μ))

noncomputable def realPosMeasure (f : ℝ → ℂ) : Measure ℝ :=
  volume.withDensity (fun x ↦ ENNReal.ofReal ((f x).re)⁺)

noncomputable def realNegMeasure (f : ℝ → ℂ) : Measure ℝ :=
  volume.withDensity (fun x ↦ ENNReal.ofReal ((f x).re)⁻)

noncomputable def imagPosMeasure (f : ℝ → ℂ) : Measure ℝ :=
  volume.withDensity (fun x ↦ ENNReal.ofReal ((f x).im)⁺)

noncomputable def imagNegMeasure (f : ℝ → ℂ) : Measure ℝ :=
  volume.withDensity (fun x ↦ ENNReal.ofReal ((f x).im)⁻)

lemma realPosMeasure_finite {f : ℝ → ℂ} (hf : Integrable f) :
    IsFiniteMeasure (realPosMeasure f) := by
  unfold realPosMeasure
  exact isFiniteMeasure_withDensity_ofReal hf.re.pos_part.2

lemma realNegMeasure_finite {f : ℝ → ℂ} (hf : Integrable f) :
    IsFiniteMeasure (realNegMeasure f) := by
  unfold realNegMeasure
  exact isFiniteMeasure_withDensity_ofReal hf.re.neg_part.2

lemma imagPosMeasure_finite {f : ℝ → ℂ} (hf : Integrable f) :
    IsFiniteMeasure (imagPosMeasure f) := by
  unfold imagPosMeasure
  exact isFiniteMeasure_withDensity_ofReal hf.im.pos_part.2

lemma imagNegMeasure_finite {f : ℝ → ℂ} (hf : Integrable f) :
    IsFiniteMeasure (imagNegMeasure f) := by
  unfold imagNegMeasure
  exact isFiniteMeasure_withDensity_ofReal hf.im.neg_part.2

lemma realPosMeasure_ae_mem_Icc {f : ℝ → ℂ} {a : ℝ} (hf : Integrable f)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (-a) a → f x = 0) :
    ∀ᵐ x ∂realPosMeasure f, x ∈ Icc (-a) a := by
  unfold realPosMeasure
  change ∀ᵐ x ∂volume.withDensity (fun x ↦ ENNReal.ofReal (max (f x).re 0)),
    x ∈ Icc (-a) a
  have hmeas : AEMeasurable (fun x ↦ ENNReal.ofReal (max (f x).re 0)) volume := by
    fun_prop
  refine (ae_withDensity_iff' (f := fun x ↦ ENNReal.ofReal (max (f x).re 0)) hmeas).2 ?_
  filter_upwards [hs] with x hx
  intro hden
  by_contra hmem
  have hzero := hx hmem
  simp [hzero] at hden

lemma realNegMeasure_ae_mem_Icc {f : ℝ → ℂ} {a : ℝ} (hf : Integrable f)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (-a) a → f x = 0) :
    ∀ᵐ x ∂realNegMeasure f, x ∈ Icc (-a) a := by
  unfold realNegMeasure
  change ∀ᵐ x ∂volume.withDensity (fun x ↦ ENNReal.ofReal (max (-(f x).re) 0)),
    x ∈ Icc (-a) a
  have hmeas : AEMeasurable (fun x ↦ ENNReal.ofReal (max (-(f x).re) 0)) volume := by
    fun_prop
  refine (ae_withDensity_iff' (f := fun x ↦ ENNReal.ofReal (max (-(f x).re) 0)) hmeas).2 ?_
  filter_upwards [hs] with x hx
  intro hden
  by_contra hmem
  have hzero := hx hmem
  simp [hzero] at hden

lemma imagPosMeasure_ae_mem_Icc {f : ℝ → ℂ} {a : ℝ} (hf : Integrable f)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (-a) a → f x = 0) :
    ∀ᵐ x ∂imagPosMeasure f, x ∈ Icc (-a) a := by
  unfold imagPosMeasure
  change ∀ᵐ x ∂volume.withDensity (fun x ↦ ENNReal.ofReal (max (f x).im 0)),
    x ∈ Icc (-a) a
  have hmeas : AEMeasurable (fun x ↦ ENNReal.ofReal (max (f x).im 0)) volume := by
    fun_prop
  refine (ae_withDensity_iff' (f := fun x ↦ ENNReal.ofReal (max (f x).im 0)) hmeas).2 ?_
  filter_upwards [hs] with x hx
  intro hden
  by_contra hmem
  have hzero := hx hmem
  simp [hzero] at hden

lemma imagNegMeasure_ae_mem_Icc {f : ℝ → ℂ} {a : ℝ} (hf : Integrable f)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (-a) a → f x = 0) :
    ∀ᵐ x ∂imagNegMeasure f, x ∈ Icc (-a) a := by
  unfold imagNegMeasure
  change ∀ᵐ x ∂volume.withDensity (fun x ↦ ENNReal.ofReal (max (-(f x).im) 0)),
    x ∈ Icc (-a) a
  have hmeas : AEMeasurable (fun x ↦ ENNReal.ofReal (max (-(f x).im) 0)) volume := by
    fun_prop
  refine (ae_withDensity_iff' (f := fun x ↦ ENNReal.ofReal (max (-(f x).im) 0)) hmeas).2 ?_
  filter_upwards [hs] with x hx
  intro hden
  by_contra hmem
  have hzero := hx hmem
  simp [hzero] at hden

lemma realPosMeasure_complexMGF_entire {f : ℝ → ℂ} {a : ℝ} (hf : Integrable f)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (-a) a → f x = 0) :
    AnalyticOnNhd ℂ (complexMGF id (realPosMeasure f)) univ := by
  letI := realPosMeasure_finite hf
  exact analyticOnNhd_complexMGF_univ_of_bounded aemeasurable_id
    (realPosMeasure_ae_mem_Icc hf hs)

lemma realNegMeasure_complexMGF_entire {f : ℝ → ℂ} {a : ℝ} (hf : Integrable f)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (-a) a → f x = 0) :
    AnalyticOnNhd ℂ (complexMGF id (realNegMeasure f)) univ := by
  letI := realNegMeasure_finite hf
  exact analyticOnNhd_complexMGF_univ_of_bounded aemeasurable_id
    (realNegMeasure_ae_mem_Icc hf hs)

lemma imagPosMeasure_complexMGF_entire {f : ℝ → ℂ} {a : ℝ} (hf : Integrable f)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (-a) a → f x = 0) :
    AnalyticOnNhd ℂ (complexMGF id (imagPosMeasure f)) univ := by
  letI := imagPosMeasure_finite hf
  exact analyticOnNhd_complexMGF_univ_of_bounded aemeasurable_id
    (imagPosMeasure_ae_mem_Icc hf hs)

lemma imagNegMeasure_complexMGF_entire {f : ℝ → ℂ} {a : ℝ} (hf : Integrable f)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (-a) a → f x = 0) :
    AnalyticOnNhd ℂ (complexMGF id (imagNegMeasure f)) univ := by
  letI := imagNegMeasure_finite hf
  exact analyticOnNhd_complexMGF_univ_of_bounded aemeasurable_id
    (imagNegMeasure_ae_mem_Icc hf hs)

noncomputable def fourierLaplace (f : ℝ → ℂ) (z : ℂ) : ℂ :=
  complexMGF id (realPosMeasure f) z - complexMGF id (realNegMeasure f) z +
    I * (complexMGF id (imagPosMeasure f) z - complexMGF id (imagNegMeasure f) z)

lemma fourierLaplace_entire {f : ℝ → ℂ} {a : ℝ} (hf : Integrable f)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (-a) a → f x = 0) :
    AnalyticOnNhd ℂ (fourierLaplace f) univ := by
  exact ((realPosMeasure_complexMGF_entire hf hs).sub
      (realNegMeasure_complexMGF_entire hf hs)).add
    (analyticOnNhd_const.mul ((imagPosMeasure_complexMGF_entire hf hs).sub
      (imagNegMeasure_complexMGF_entire hf hs)))

lemma complexMGF_realPosMeasure_eq_integral {f : ℝ → ℂ} (hf : Integrable f) (z : ℂ) :
    complexMGF id (realPosMeasure f) z =
      ∫ x : ℝ, cexp (z * x) * ((f x).re)⁺ := by
  unfold complexMGF realPosMeasure
  change (∫ x : ℝ, cexp (z * x) ∂volume.withDensity
      (fun x ↦ ENNReal.ofReal (max (f x).re 0))) =
    ∫ x : ℝ, cexp (z * x) * (max (f x).re 0 : ℝ)
  have hmeas : AEMeasurable (fun x ↦ ENNReal.ofReal (max (f x).re 0)) volume := by
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

lemma complexMGF_realNegMeasure_eq_integral {f : ℝ → ℂ} (hf : Integrable f) (z : ℂ) :
    complexMGF id (realNegMeasure f) z =
      ∫ x : ℝ, cexp (z * x) * ((f x).re)⁻ := by
  unfold complexMGF realNegMeasure
  change (∫ x : ℝ, cexp (z * x) ∂volume.withDensity
      (fun x ↦ ENNReal.ofReal (max (-(f x).re) 0))) =
    ∫ x : ℝ, cexp (z * x) * (max (-(f x).re) 0 : ℝ)
  have hmeas : AEMeasurable (fun x ↦ ENNReal.ofReal (max (-(f x).re) 0)) volume := by
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

lemma complexMGF_imagPosMeasure_eq_integral {f : ℝ → ℂ} (hf : Integrable f) (z : ℂ) :
    complexMGF id (imagPosMeasure f) z =
      ∫ x : ℝ, cexp (z * x) * ((f x).im)⁺ := by
  unfold complexMGF imagPosMeasure
  change (∫ x : ℝ, cexp (z * x) ∂volume.withDensity
      (fun x ↦ ENNReal.ofReal (max (f x).im 0))) =
    ∫ x : ℝ, cexp (z * x) * (max (f x).im 0 : ℝ)
  have hmeas : AEMeasurable (fun x ↦ ENNReal.ofReal (max (f x).im 0)) volume := by
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

lemma complexMGF_imagNegMeasure_eq_integral {f : ℝ → ℂ} (hf : Integrable f) (z : ℂ) :
    complexMGF id (imagNegMeasure f) z =
      ∫ x : ℝ, cexp (z * x) * ((f x).im)⁻ := by
  unfold complexMGF imagNegMeasure
  change (∫ x : ℝ, cexp (z * x) ∂volume.withDensity
      (fun x ↦ ENNReal.ofReal (max (-(f x).im) 0))) =
    ∫ x : ℝ, cexp (z * x) * (max (-(f x).im) 0 : ℝ)
  have hmeas : AEMeasurable (fun x ↦ ENNReal.ofReal (max (-(f x).im) 0)) volume := by
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

lemma integrable_cexp_imag_mul_of_integrable {r : ℝ → ℝ} (hr : Integrable r) (t : ℝ) :
    Integrable (fun x : ℝ ↦ cexp (((t : ℂ) * I) * x) * (r x : ℂ)) := by
  refine hr.ofReal.bdd_mul (c := 1) ?_ ?_
  · fun_prop
  · filter_upwards with x
    simp [norm_exp]

lemma fourierLaplace_neg_two_pi_I_eq_fourier {f : ℝ → ℂ} (hf : Integrable f) (w : ℝ) :
    fourierLaplace f ((-2 * Real.pi * w : ℝ) * I) = FourierTransform.fourier f w := by
  let t : ℝ := -2 * Real.pi * w
  have hrp : Integrable
      (fun x : ℝ ↦ cexp (((t : ℂ) * I) * x) * (((((f x).re)⁺ : ℝ)) : ℂ)) := by
    exact integrable_cexp_imag_mul_of_integrable hf.re.pos_part t
  have hrn : Integrable
      (fun x : ℝ ↦ cexp (((t : ℂ) * I) * x) * (((((f x).re)⁻ : ℝ)) : ℂ)) := by
    exact integrable_cexp_imag_mul_of_integrable hf.re.neg_part t
  have hip : Integrable
      (fun x : ℝ ↦ cexp (((t : ℂ) * I) * x) * (((((f x).im)⁺ : ℝ)) : ℂ)) := by
    exact integrable_cexp_imag_mul_of_integrable hf.im.pos_part t
  have hin : Integrable
      (fun x : ℝ ↦ cexp (((t : ℂ) * I) * x) * (((((f x).im)⁻ : ℝ)) : ℂ)) := by
    exact integrable_cexp_imag_mul_of_integrable hf.im.neg_part t
  have hrealDiff : Integrable (fun x : ℝ ↦
      cexp (((t : ℂ) * I) * x) * ((f x).re)⁺ -
        cexp (((t : ℂ) * I) * x) * ((f x).re)⁻) := hrp.sub hrn
  have himagDiff : Integrable (fun x : ℝ ↦ I *
      (cexp (((t : ℂ) * I) * x) * ((f x).im)⁺ -
        cexp (((t : ℂ) * I) * x) * ((f x).im)⁻)) := (hip.sub hin).const_mul I
  rw [fourierLaplace, complexMGF_realPosMeasure_eq_integral hf,
    complexMGF_realNegMeasure_eq_integral hf, complexMGF_imagPosMeasure_eq_integral hf,
    complexMGF_imagNegMeasure_eq_integral hf, Real.fourier_real_eq_integral_exp_smul]
  change (∫ x : ℝ, cexp (((t : ℂ) * I) * x) * ((f x).re)⁺) -
      (∫ x : ℝ, cexp (((t : ℂ) * I) * x) * ((f x).re)⁻) +
      I * ((∫ x : ℝ, cexp (((t : ℂ) * I) * x) * ((f x).im)⁺) -
        ∫ x : ℝ, cexp (((t : ℂ) * I) * x) * ((f x).im)⁻) =
    ∫ x : ℝ, cexp ((-2 * Real.pi * x * w : ℝ) * I) * f x
  rw [← integral_sub hrp hrn, ← integral_sub hip hin, ← integral_const_mul]
  rw [← integral_add hrealDiff himagDiff]
  apply integral_congr_ae
  filter_upwards with x
  rw [← mul_sub, ← mul_sub]
  have hre : ((f x).re)⁺ - ((f x).re)⁻ = (f x).re := posPart_sub_negPart _
  have him : ((f x).im)⁺ - ((f x).im)⁻ = (f x).im := posPart_sub_negPart _
  have hreC : (↑(((f x).re)⁺) : ℂ) - (↑(((f x).re)⁻) : ℂ) = (f x).re := by
    exact_mod_cast hre
  have himC : (↑(((f x).im)⁺) : ℂ) - (↑(((f x).im)⁻) : ℂ) = (f x).im := by
    exact_mod_cast him
  rw [hreC, himC]
  have hf_parts : ((f x).re : ℂ) + I * (f x).im = f x := by
    simpa [mul_comm] using Complex.re_add_im (f x)
  calc
    cexp (((t : ℂ) * I) * x) * ((f x).re : ℂ) +
        I * (cexp (((t : ℂ) * I) * x) * ((f x).im : ℂ)) =
      cexp (((t : ℂ) * I) * x) *
        (((f x).re : ℂ) + I * (f x).im) := by ring
    _ = cexp (((t : ℂ) * I) * x) * f x := by rw [hf_parts]
    _ = cexp ((-2 * Real.pi * x * w : ℝ) * I) * f x := by
      have hexponent : (((t : ℂ) * I) * x) =
          ((-2 * Real.pi * x * w : ℝ) : ℂ) * I := by
        simp only [t]
        push_cast
        ring
      rw [hexponent]

lemma fourierLaplace_fourierLine_analytic {f : ℝ → ℂ} {a : ℝ} (hf : Integrable f)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (-a) a → f x = 0) :
    AnalyticOnNhd ℝ (fun w : ℝ ↦ fourierLaplace f ((-2 * Real.pi * w : ℝ) * I)) univ := by
  intro w hw
  have hinner : AnalyticAt ℝ (fun u : ℝ ↦ ((-2 * Real.pi * u : ℝ) : ℂ) * I) w := by
    apply AnalyticAt.mul
    · exact (Complex.ofRealCLM.analyticAt _).comp (analyticAt_const.mul analyticAt_id)
    · exact analyticAt_const
  exact ((fourierLaplace_entire hf hs) _ (mem_univ _)).restrictScalars.comp hinner

lemma fourier_eq_zero_of_ae_zero_off_bounded {f : ℝ → ℂ} {a b : ℝ} (hf : Integrable f)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (-a) a → f x = 0)
    (hF : ∀ᵐ w ∂volume, w ∉ Icc (-b) b → FourierTransform.fourier f w = 0) :
    ∀ w, FourierTransform.fourier f w = 0 := by
  let U : Set ℝ := (Icc (-b) b)ᶜ
  have hcont : Continuous (FourierTransform.fourier f) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hf
  have hF_restrict : FourierTransform.fourier f =ᵐ[volume.restrict U] 0 := by
    refine (ae_restrict_iff' (isClosed_Icc.measurableSet.compl)).2 ?_
    filter_upwards [hF] with w hw hmem
    exact hw hmem
  have hF_on : EqOn (FourierTransform.fourier f) 0 U :=
    Measure.eqOn_open_of_ae_eq hF_restrict isClosed_Icc.isOpen_compl
      hcont.continuousOn continuous_zero.continuousOn
  let w₀ : ℝ := b + 1
  have hw₀ : b < w₀ := by simp [w₀]
  have hline_eventually :
      (fun w : ℝ ↦ fourierLaplace f ((-2 * Real.pi * w : ℝ) * I)) =ᶠ[nhds w₀] 0 := by
    filter_upwards [Ioi_mem_nhds hw₀] with w hw
    rw [fourierLaplace_neg_two_pi_I_eq_fourier hf]
    exact hF_on (by simp only [U, mem_compl_iff, mem_Icc, not_and_or, not_le]; exact Or.inr hw)
  have hline_zero : ∀ w : ℝ,
      fourierLaplace f ((-2 * Real.pi * w : ℝ) * I) = 0 := by
    intro w
    exact (AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
      (fourierLaplace_fourierLine_analytic hf hs) analyticOnNhd_const
      isPreconnected_univ (mem_univ w₀) hline_eventually) (mem_univ w)
  intro w
  rw [← fourierLaplace_neg_two_pi_I_eq_fourier hf]
  exact hline_zero w

/-- A compactly supported integrable function whose Fourier transform vanishes almost
everywhere on one nonempty open interval has identically zero Fourier transform. -/
lemma fourier_eq_zero_of_ae_zero_on_Ioo {f : ℝ → ℂ} {a c d : ℝ}
    (hf : Integrable f)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (-a) a → f x = 0)
    (hcd : c < d)
    (hF : ∀ᵐ w ∂volume, w ∈ Ioo c d → FourierTransform.fourier f w = 0) :
    ∀ w, FourierTransform.fourier f w = 0 := by
  let U : Set ℝ := Ioo c d
  have hcont : Continuous (FourierTransform.fourier f) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hf
  have hF_restrict : FourierTransform.fourier f =ᵐ[volume.restrict U] 0 := by
    refine (ae_restrict_iff' measurableSet_Ioo).2 ?_
    filter_upwards [hF] with w hw hmem
    exact hw hmem
  have hF_on : EqOn (FourierTransform.fourier f) 0 U :=
    Measure.eqOn_open_of_ae_eq hF_restrict isOpen_Ioo
      hcont.continuousOn continuous_zero.continuousOn
  let w₀ : ℝ := (c + d) / 2
  have hw₀ : w₀ ∈ U := by
    constructor <;> dsimp [w₀] <;> linarith
  have hline_eventually :
      (fun w : ℝ => fourierLaplace f ((-2 * Real.pi * w : ℝ) * I)) =ᶠ[nhds w₀] 0 := by
    filter_upwards [isOpen_Ioo.mem_nhds hw₀] with w hw
    rw [fourierLaplace_neg_two_pi_I_eq_fourier hf]
    exact hF_on hw
  have hline_zero : ∀ w : ℝ,
      fourierLaplace f ((-2 * Real.pi * w : ℝ) * I) = 0 := by
    intro w
    exact (AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
      (fourierLaplace_fourierLine_analytic hf hs) analyticOnNhd_const
      isPreconnected_univ (mem_univ w₀) hline_eventually) (mem_univ w)
  intro w
  rw [← fourierLaplace_neg_two_pi_I_eq_fourier hf]
  exact hline_zero w

open scoped ComplexConjugate in
lemma conj_fourier_ofReal {r : ℝ → ℝ} (_hr : Integrable r) (w : ℝ) :
    conj (FourierTransform.fourier (fun x ↦ (r x : ℂ)) w) =
      FourierTransform.fourier (fun x ↦ (r x : ℂ)) (-w) := by
  rw [Real.fourier_real_eq_integral_exp_smul,
    Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards with x
  rw [map_mul, ← Complex.exp_conj]
  congr 1
  · congr 1
    apply Complex.ext <;> norm_num
  · simp

lemma fourier_eq_fourier_re_add_I_mul_fourier_im {f : ℝ → ℂ} (hf : Integrable f) (w : ℝ) :
    FourierTransform.fourier f w =
      FourierTransform.fourier (fun x ↦ ((f x).re : ℂ)) w +
        I * FourierTransform.fourier (fun x ↦ ((f x).im : ℂ)) w := by
  let t : ℝ := -2 * Real.pi * w
  have hre : Integrable
      (fun x : ℝ ↦ cexp (((t : ℂ) * I) * x) * ((f x).re : ℂ)) :=
    integrable_cexp_imag_mul_of_integrable hf.re t
  have him : Integrable
      (fun x : ℝ ↦ cexp (((t : ℂ) * I) * x) * ((f x).im : ℂ)) :=
    integrable_cexp_imag_mul_of_integrable hf.im t
  have hre' : Integrable
      (fun x : ℝ ↦ cexp ((-2 * Real.pi * x * w : ℝ) * I) * ((f x).re : ℂ)) := by
    refine hf.re.ofReal.bdd_mul (c := 1) ?_ ?_
    · fun_prop
    · filter_upwards with x
      simp [norm_exp]
  have him' : Integrable
      (fun x : ℝ ↦ cexp ((-2 * Real.pi * x * w : ℝ) * I) * ((f x).im : ℂ)) := by
    refine hf.im.ofReal.bdd_mul (c := 1) ?_ ?_
    · fun_prop
    · filter_upwards with x
      simp [norm_exp]
  rw [Real.fourier_real_eq_integral_exp_smul,
    Real.fourier_real_eq_integral_exp_smul,
    Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  rw [← integral_const_mul, ← integral_add hre' (him'.const_mul I)]
  apply integral_congr_ae
  filter_upwards with x
  calc
    cexp ((-2 * Real.pi * x * w : ℝ) * I) * f x =
        cexp ((-2 * Real.pi * x * w : ℝ) * I) *
          (((f x).re : ℂ) + I * (f x).im) := by
            congr 1
            simpa [mul_comm] using (Complex.re_add_im (f x)).symm
    _ = cexp ((-2 * Real.pi * x * w : ℝ) * I) * ((f x).re : ℂ) +
        I * (cexp ((-2 * Real.pi * x * w : ℝ) * I) * ((f x).im : ℂ)) := by ring

open scoped ComplexConjugate in
lemma fourier_re_im_eq_zero_of_fourier_eq_zero {f : ℝ → ℂ} (hf : Integrable f)
    (hF : ∀ w, FourierTransform.fourier f w = 0) (w : ℝ) :
    FourierTransform.fourier (fun x ↦ ((f x).re : ℂ)) w = 0 ∧
      FourierTransform.fourier (fun x ↦ ((f x).im : ℂ)) w = 0 := by
  let R : ℂ := FourierTransform.fourier (fun x ↦ ((f x).re : ℂ)) w
  let S : ℂ := FourierTransform.fourier (fun x ↦ ((f x).im : ℂ)) w
  have hplus : R + I * S = 0 := by
    rw [← fourier_eq_fourier_re_add_I_mul_fourier_im hf w, hF w]
  have hneg := hF (-w)
  rw [fourier_eq_fourier_re_add_I_mul_fourier_im hf (-w)] at hneg
  have hReSym :
      conj (FourierTransform.fourier (fun x ↦ ((f x).re : ℂ)) w) =
        FourierTransform.fourier (fun x ↦ ((f x).re : ℂ)) (-w) := by
    exact conj_fourier_ofReal (r := fun x ↦ (f x).re) hf.re w
  have hImSym :
      conj (FourierTransform.fourier (fun x ↦ ((f x).im : ℂ)) w) =
        FourierTransform.fourier (fun x ↦ ((f x).im : ℂ)) (-w) := by
    exact conj_fourier_ofReal (r := fun x ↦ (f x).im) hf.im w
  rw [← hReSym, ← hImSym] at hneg
  have hminus : R - I * S = 0 := by
    have hc := congrArg conj hneg
    simp only [map_add, map_mul, conj_conj, conj_I, map_zero] at hc
    simpa [R, S, sub_eq_add_neg] using hc
  constructor
  · change R = 0
    linear_combination (1 / 2 : ℂ) * hplus + (1 / 2 : ℂ) * hminus
  · change S = 0
    have his : I * S = 0 := by
      linear_combination (1 / 2 : ℂ) * hplus - (1 / 2 : ℂ) * hminus
    exact (mul_eq_zero.mp his).resolve_left Complex.I_ne_zero

lemma complexMGF_pos_eq_neg_of_real_fourier_eq_zero {r : ℝ → ℝ} (hr : Integrable r)
    (hR : ∀ w, FourierTransform.fourier (fun x ↦ (r x : ℂ)) w = 0) (w : ℝ) :
    complexMGF id (realPosMeasure (fun x ↦ (r x : ℂ))) (w * I) =
      complexMGF id (realNegMeasure (fun x ↦ (r x : ℂ))) (w * I) := by
  have h := fourierLaplace_neg_two_pi_I_eq_fourier hr.ofReal (-w / (2 * Real.pi))
  have hRw : FourierTransform.fourier (fun x ↦ (r x : ℂ)) (-w / (2 * Real.pi)) = 0 :=
    hR (-w / (2 * Real.pi))
  have hzero := h.trans hRw
  have hz : ((-2 * Real.pi * (-w / (2 * Real.pi)) : ℝ) * I) = w * I := by
    have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
    congr 1
    field_simp
  rw [hz] at hzero
  unfold fourierLaplace at hzero
  simp [imagPosMeasure, imagNegMeasure] at hzero
  exact sub_eq_zero.mp hzero

lemma ae_eq_zero_of_real_fourier_eq_zero {r : ℝ → ℝ} (hr : Integrable r)
    (hR : ∀ w, FourierTransform.fourier (fun x ↦ (r x : ℂ)) w = 0) :
    r =ᵐ[volume] 0 := by
  let f : ℝ → ℂ := fun x ↦ (r x : ℂ)
  let muPos : Measure ℝ := realPosMeasure f
  let muNeg : Measure ℝ := realNegMeasure f
  letI : IsFiniteMeasure muPos := realPosMeasure_finite hr.ofReal
  letI : IsFiniteMeasure muNeg := realNegMeasure_finite hr.ofReal
  have hchar : charFun muPos = charFun muNeg := by
    funext w
    rw [← complexMGF_id_mul_I, ← complexMGF_id_mul_I]
    exact complexMGF_pos_eq_neg_of_real_fourier_eq_zero hr hR w
  have hmeasure : muPos = muNeg := Measure.ext_of_charFun hchar
  have hmeasPos : AEMeasurable (fun x ↦ ENNReal.ofReal ((r x)⁺)) volume := by
    fun_prop
  have hmeasNeg : AEMeasurable (fun x ↦ ENNReal.ofReal ((r x)⁻)) volume := by
    fun_prop
  have hdensity : (fun x ↦ ENNReal.ofReal ((r x)⁺)) =ᵐ[volume]
      (fun x ↦ ENNReal.ofReal ((r x)⁻)) := by
    apply (withDensity_eq_iff_of_sigmaFinite hmeasPos hmeasNeg).1
    simpa [muPos, muNeg, f, realPosMeasure, realNegMeasure] using hmeasure
  filter_upwards [hdensity] with x hx
  have hparts : (r x)⁺ = (r x)⁻ := by
    apply_fun ENNReal.toReal at hx
    simpa [ENNReal.toReal_ofReal (posPart_nonneg _),
      ENNReal.toReal_ofReal (negPart_nonneg _)] using hx
  simpa only [Pi.zero_apply] using (show r x = 0 by
    rw [← posPart_sub_negPart (r x), hparts, sub_self])

/-- Fourier injectivity for integrable complex functions, in the exact pointwise-zero form used
after analytic continuation from an interval. -/
theorem integrable_ae_eq_zero_of_fourier_eq_zero {f : ℝ → ℂ} (hf : Integrable f)
    (hFzero : ∀ w, FourierTransform.fourier f w = 0) :
    f =ᵐ[volume] 0 := by
  have hReF : ∀ w, FourierTransform.fourier (fun x ↦ ((f x).re : ℂ)) w = 0 :=
    fun w ↦ (fourier_re_im_eq_zero_of_fourier_eq_zero hf hFzero w).1
  have hImF : ∀ w, FourierTransform.fourier (fun x ↦ ((f x).im : ℂ)) w = 0 :=
    fun w ↦ (fourier_re_im_eq_zero_of_fourier_eq_zero hf hFzero w).2
  have hRe := ae_eq_zero_of_real_fourier_eq_zero hf.re hReF
  have hIm := ae_eq_zero_of_real_fourier_eq_zero hf.im hImF
  filter_upwards [hRe, hIm] with x hxRe hxIm
  apply Complex.ext
  · simpa using hxRe
  · simpa using hxIm

/-- An integrable complex-valued function and its Fourier integral cannot both have bounded
essential support unless the function vanishes almost everywhere. -/
theorem integrable_fourier_uncertainty {f : ℝ → ℂ} {a b : ℝ} (hf : Integrable f)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (-a) a → f x = 0)
    (hF : ∀ᵐ w ∂volume,
      w ∉ Icc (-b) b → FourierTransform.fourier f w = 0) :
    f =ᵐ[volume] 0 := by
  have hFzero := fourier_eq_zero_of_ae_zero_off_bounded hf hs hF
  have hReF : ∀ w, FourierTransform.fourier (fun x ↦ ((f x).re : ℂ)) w = 0 :=
    fun w ↦ (fourier_re_im_eq_zero_of_fourier_eq_zero hf hFzero w).1
  have hImF : ∀ w, FourierTransform.fourier (fun x ↦ ((f x).im : ℂ)) w = 0 :=
    fun w ↦ (fourier_re_im_eq_zero_of_fourier_eq_zero hf hFzero w).2
  have hRe := ae_eq_zero_of_real_fourier_eq_zero hf.re hReF
  have hIm := ae_eq_zero_of_real_fourier_eq_zero hf.im hImF
  filter_upwards [hRe, hIm] with x hxRe hxIm
  apply Complex.ext
  · simpa using hxRe
  · simpa using hxIm


end RHTower
