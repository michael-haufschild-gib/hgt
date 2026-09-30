import GaloisForLFunctions.RHTower.ThetaWeightedTranslationDomain
import GaloisForLFunctions.RHTower.ThetaWeightedHistoryProperness
import GaloisForLFunctions.RHTower.XiThetaL2Cyclicity
import GaloisForLFunctions.HTGeometry.L2MeasureCongruence

/-!
# Collapse of the actual theta derivative history at the unweighted endpoint

The literal theta translation curve is Hilbert-holomorphic on its full
Gaussian strip. Its origin jets are the ordinary source derivatives, so
their closed span contains every real translate. Exact dilation transports
the existing normalized theta cyclicity certificate to this orbit.
-/

open MeasureTheory Set Metric Filter Topology

namespace RHTower

open HedenmalmThetaSource DominatedL2Sections GaloisForLFunctions.HTGeometry MellinL2

noncomputable section

attribute [local instance 2000] Real.measurableSpace
attribute [local instance 2000] NormedSpace.complexToReal

theorem thetaPowerWeightedMeasure_zero : thetaPowerWeightedMeasure 0 = (volume : Measure ℝ) := by
  unfold thetaPowerWeightedMeasure
  simp only [neg_zero, Real.rpow_zero, ENNReal.ofReal_one]
  exact withDensity_one

/-- Canonical representative-preserving identification of the endpoint carrier. -/
def thetaUnweightedVolumeEquiv :
    Lp ℂ 2 (thetaPowerWeightedMeasure 0) ≃ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  l2MeasureCongruence thetaPowerWeightedMeasure_zero

theorem thetaUnweightedVolumeEquiv_coe (f : Lp ℂ 2 (thetaPowerWeightedMeasure 0)) :
    (thetaUnweightedVolumeEquiv f : ℝ → ℂ) = (f : ℝ → ℂ) :=
  l2MeasureCongruence_coe thetaPowerWeightedMeasure_zero f

/-- With no reciprocal weight, Gaussian slack is the entire source strip. -/
theorem thetaWeightedTranslationDomain_zero : thetaWeightedTranslationDomain 0 = thetaCuspStrip := by
  ext z
  constructor
  · exact fun hz => hz.1
  · intro hz
    change |z.im| < Real.pi / 4 at hz
    refine ⟨hz, ?_⟩
    have hc : 0 < Real.cos (2 * z.im) :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [(abs_lt.mp hz).1],
        by linarith [(abs_lt.mp hz).2]⟩
    exact mul_pos (mul_pos (by norm_num) (Real.exp_pos _)) hc

/-- The actual source curve on the full connected Gaussian strip. -/
def thetaUnweightedTranslationFamily : Family (thetaPowerWeightedMeasure 0) where
  domain := thetaCuspStrip
  isOpen_domain := isOpen_thetaCuspStrip
  value z x := thetaCuspStripSource ((x : ℂ) + z)
  measurable z hz := (continuous_thetaCuspStripSource_translation hz).aestronglyMeasurable
  holomorphic x := by
    intro z hz
    have hp : (x : ℂ) + z ∈ thetaCuspStrip := by
      simpa only [thetaCuspStrip, mem_setOf_eq, Complex.add_im, Complex.ofReal_im, zero_add] using hz
    exact ((differentiableAt_thetaCuspStripSource hp).comp z (by fun_prop)).differentiableWithinAt
  local_bound z hz := by
    have hdomain : z ∈ thetaWeightedTranslationDomain 0 := by
      rw [thetaWeightedTranslationDomain_zero]
      exact hz
    obtain ⟨δ, A, hδ, hA, hzδ, hδ4, hmargin⟩ :=
      theta_weighted_rectangle_exists_of_domain 0 hdomain
    have hzrect : z ∈ thetaTranslationRectangle δ A := ⟨hA, hzδ⟩
    obtain ⟨R, hR, hsub⟩ := Metric.isOpen_iff.mp
      (isOpen_thetaTranslationRectangle δ A) z hzrect
    refine ⟨R, hR, ?_, thetaRectangleGaussianMajorant δ A,
      thetaRectangleGaussianMajorant_memLp_of_nonneg δ A 0
        ((abs_nonneg z.re).trans hA.le) hδ.le hδ4 (by norm_num) hmargin, ?_⟩
    · intro w hw
      change |w.im| < Real.pi / 4
      exact (hsub hw).2.trans (by linarith)
    · intro x w hw
      exact norm_thetaCuspStripSource_translate_le_rectangle δ A hδ.le hδ4 w
        (hsub hw).1.le (hsub hw).2.le x

theorem thetaUnweightedTranslationFamily_section {z : ℂ} (hz : z ∈ thetaCuspStrip) :
    thetaUnweightedTranslationFamily.section z = thetaWeightedTranslationClass 0 z :=
  Family.section_eq_l2Family _ hz

theorem differentiableOn_thetaUnweightedTranslationFamily :
    DifferentiableOn ℂ thetaUnweightedTranslationFamily.section thetaCuspStrip :=
  thetaUnweightedTranslationFamily.differentiableOn_section

theorem analyticOnNhd_thetaUnweightedTranslationFamily :
    AnalyticOnNhd ℂ thetaUnweightedTranslationFamily.section thetaCuspStrip :=
  thetaUnweightedTranslationFamily.analytic_section

private theorem zero_mem_strip : (0 : ℂ) ∈ thetaCuspStrip := by
  change |(0 : ℂ).im| < Real.pi / 4
  simp only [Complex.zero_im, abs_zero]
  positivity

private theorem thetaUnweightedTranslationFamily_pointwise_jet (n : ℕ) (x : ℝ) :
    iteratedDeriv n (fun z => thetaUnweightedTranslationFamily.value z x) 0 =
      ((iteratedDeriv n thetaCuspFullSource x : ℝ) : ℂ) := by
  change iteratedDeriv n (fun z => thetaCuspStripSource ((x : ℂ) + z)) 0 = _
  rw [iteratedDeriv_comp_const_add]
  simp only [add_zero, thetaCuspStripSource_iteratedDeriv_ofReal]

/-- Each ordinary derivative is genuinely admitted at the endpoint. -/
theorem thetaUnweightedDerivative_memLp (n : ℕ) :
    MemLp (fun x : ℝ => ((iteratedDeriv n thetaCuspFullSource x : ℝ) : ℂ)) 2
      (thetaPowerWeightedMeasure 0) := by
  have h := thetaUnweightedTranslationFamily.memLp_iteratedDeriv n zero_mem_strip
  convert h using 1
  funext x
  exact (thetaUnweightedTranslationFamily_pointwise_jet n x).symm

theorem thetaUnweightedDerivativeVector_coe (n : ℕ) :
    (thetaWeightedDerivativeVector 0 n : ℝ → ℂ) =ᵐ[volume]
      fun x => ((iteratedDeriv n thetaCuspFullSource x : ℝ) : ℂ) := by
  rw [thetaWeightedDerivativeVector, l2Family_eq_toLp (thetaPowerWeightedMeasure 0)
    (fun _ x => ((iteratedDeriv n thetaCuspFullSource x : ℝ) : ℂ)) 0
    (thetaUnweightedDerivative_memLp n)]
  exact (thetaPowerWeightedMeasure_ae_eq 0).mp (thetaUnweightedDerivative_memLp n).coeFn_toLp

/-- The Hilbert jets are precisely the existing actual endpoint generators. -/
theorem thetaUnweightedTranslationFamily_iteratedDeriv_zero (n : ℕ) :
    iteratedDeriv n thetaUnweightedTranslationFamily.section 0 = thetaWeightedDerivativeVector 0 n := by
  rw [thetaWeightedDerivativeVector, l2Family_eq_toLp (thetaPowerWeightedMeasure 0)
    (fun _ x => ((iteratedDeriv n thetaCuspFullSource x : ℝ) : ℂ)) 0
    (thetaUnweightedDerivative_memLp n)]
  apply Lp.ext
  filter_upwards [thetaUnweightedTranslationFamily.coe_iteratedDeriv_section n zero_mem_strip,
    (thetaUnweightedDerivative_memLp n).coeFn_toLp] with x hx hy
  exact hx.trans ((thetaUnweightedTranslationFamily_pointwise_jet n x).trans hy.symm)

/-- Analytic uniqueness includes the entire strip orbit in actual derivative history. -/
theorem thetaUnweightedTranslationClass_mem_derivativeHistory {z : ℂ} (hz : z ∈ thetaCuspStrip) :
    thetaWeightedTranslationClass 0 z ∈ thetaWeightedDerivativeHistory 0 := by
  have h := thetaUnweightedTranslationFamily.section_mem_closed_span_jets
    isPreconnected_thetaCuspStrip zero_mem_strip hz
  have he : (fun n : ℕ => iteratedDeriv n thetaUnweightedTranslationFamily.section 0) =
      thetaWeightedDerivativeVector 0 := by
    funext n
    exact thetaUnweightedTranslationFamily_iteratedDeriv_zero n
  rw [he, thetaUnweightedTranslationFamily_section hz] at h
  exact h

/-- Literal unscaled real translations in ordinary Lebesgue `L²`. -/
def thetaUnweightedRealTranslation (a : ℝ) : Lp ℂ 2 (volume : Measure ℝ) :=
  thetaUnweightedVolumeEquiv (thetaWeightedTranslationClass 0 (a : ℂ))

theorem thetaUnweightedRealTranslation_coe (a : ℝ) :
    (thetaUnweightedRealTranslation a : ℝ → ℂ) =ᵐ[volume]
      fun x => (thetaCuspFullSource (x+a) : ℂ) := by
  rw [thetaUnweightedRealTranslation, thetaUnweightedVolumeEquiv_coe]
  have ha : (a : ℂ) ∈ thetaCuspStrip := by
    change |(a : ℂ).im| < Real.pi / 4
    simp only [Complex.ofReal_im, abs_zero]
    positivity
  have h := thetaUnweightedTranslationFamily.section_coe ha
  rw [thetaUnweightedTranslationFamily_section ha] at h
  filter_upwards [(thetaPowerWeightedMeasure_ae_eq 0).mp h] with x hx
  rw [hx]
  change thetaCuspStripSource ((x : ℂ) + (a : ℂ)) = _
  rw [← Complex.ofReal_add, thetaCuspStripSource_ofReal]

/-- Exact normalization and dilation of every real source translate. -/
theorem xiThetaTranslationOrbit_eq_dilation (a : ℝ) :
    xiThetaTranslationOrbit a = (Real.sqrt (2*Real.pi) : ℂ) •
      dilationUnitary (2*Real.pi) (by positivity)
        (thetaUnweightedRealTranslation ((2*Real.pi)*a)) := by
  rw [xiThetaTranslationOrbit, xiThetaSourceL2, additiveTranslation_toLp]
  apply Lp.ext
  have hphase := (thetaUnweightedRealTranslation_coe ((2*Real.pi)*a)).comp_tendsto
    (realMul_quasiMeasurePreserving (2*Real.pi) (by positivity)).tendsto_ae
  filter_upwards [(schwartzTranslate a xiThetaSchwartzSource).coeFn_toLp
      (p := 2) (μ := (volume : Measure ℝ)),
    Lp.coeFn_smul (Real.sqrt (2*Real.pi) : ℂ)
      (dilationUnitary (2*Real.pi) (by positivity)
        (thetaUnweightedRealTranslation ((2*Real.pi)*a))),
    dilation_ae (2*Real.pi) (by positivity)
      (thetaUnweightedRealTranslation ((2*Real.pi)*a)), hphase] with x hl hs hd ht
  dsimp only [Function.comp_apply] at ht
  rw [hl, hs]
  change xiThetaSchwartzSource (x+a) = (Real.sqrt (2*Real.pi) : ℂ) *
    dilation (2*Real.pi) (by positivity) (thetaUnweightedRealTranslation ((2*Real.pi)*a)) x
  rw [hd, ht, xiThetaSchwartzSource_apply]
  have hscale : (Real.sqrt (2*Real.pi) : ℂ) * (Real.sqrt (2*Real.pi) : ℂ) =
      (2*Real.pi : ℝ) := by
    exact_mod_cast (by rw [← pow_two, Real.sq_sqrt (by positivity)] :
      Real.sqrt (2*Real.pi) * Real.sqrt (2*Real.pi) = 2*Real.pi)
  rw [← mul_assoc, hscale]
  congr 2
  ring

/-- Wiener cyclicity for the actual unscaled theta source. -/
theorem isCyclicFamily_thetaUnweightedRealTranslation :
    IsCyclicFamily (𝕜 := ℂ) thetaUnweightedRealTranslation := by
  apply dense_span_of_forall_dual_eq_zero
  intro L hL
  let U := dilationUnitary (2*Real.pi) (by positivity)
  let LX : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] ℂ :=
    L.comp U.symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hLX (a : ℝ) : LX (xiThetaTranslationOrbit a) = 0 := by
    rw [xiThetaTranslationOrbit_eq_dilation]
    change L (U.symm ((Real.sqrt (2*Real.pi) : ℂ) •
      U (thetaUnweightedRealTranslation ((2*Real.pi)*a)))) = 0
    rw [map_smul, U.symm_apply_apply, map_smul, hL, smul_zero]
  have hzero := continuousLinearFunctional_eq_zero_of_isCyclicFamily
    isCyclicFamily_xiThetaTranslationOrbit LX hLX
  apply ContinuousLinearMap.ext
  intro f
  have h := congrArg (fun M : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] ℂ => M (U f)) hzero
  change L (U.symm (U f)) = 0 at h
  simpa using h

/-- The actual derivative history is the whole unweighted endpoint carrier. -/
theorem thetaWeightedDerivativeHistory_zero_eq_top : thetaWeightedDerivativeHistory 0 = ⊤ := by
  apply Submodule.dense_iff_topologicalClosure_eq_top.mp
  apply dense_span_of_forall_dual_eq_zero
  intro L hL
  have hker : thetaWeightedDerivativeHistory 0 ≤ L.ker := by
    apply (Submodule.span ℂ (range (thetaWeightedDerivativeVector 0))).topologicalClosure_minimal
      (Submodule.span_le.mpr ?_) L.isClosed_ker
    rintro _ ⟨n, rfl⟩
    exact hL n
  let LV : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] ℂ :=
    L.comp thetaUnweightedVolumeEquiv.symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hLV (a : ℝ) : LV (thetaUnweightedRealTranslation a) = 0 := by
    change L (thetaUnweightedVolumeEquiv.symm
      (thetaUnweightedVolumeEquiv (thetaWeightedTranslationClass 0 (a : ℂ)))) = 0
    rw [thetaUnweightedVolumeEquiv.symm_apply_apply]
    apply hker
    apply thetaUnweightedTranslationClass_mem_derivativeHistory
    change |(a : ℂ).im| < Real.pi / 4
    simp only [Complex.ofReal_im, abs_zero]
    positivity
  have hzero := continuousLinearFunctional_eq_zero_of_isCyclicFamily
    isCyclicFamily_thetaUnweightedRealTranslation LV hLV
  apply ContinuousLinearMap.ext
  intro f
  have h := congrArg (fun M : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] ℂ =>
    M (thetaUnweightedVolumeEquiv f)) hzero
  change L (thetaUnweightedVolumeEquiv.symm (thetaUnweightedVolumeEquiv f)) = 0 at h
  simpa using h

/-- Exact positive-weight properness and unweighted endpoint collapse. -/
theorem thetaDerivativeHistory_endpoint_dichotomy :
    (∀ q : ℝ, 0 < q → q < 2 → thetaWeightedDerivativeHistory q ≠ ⊤) ∧
      thetaWeightedDerivativeHistory 0 = ⊤ :=
  ⟨thetaWeightedDerivativeHistory_ne_top, thetaWeightedDerivativeHistory_zero_eq_top⟩

end

end RHTower
