import GaloisForLFunctions.RHTower.ThetaPowerWeightedDerivativeHistory
import GaloisForLFunctions.RHTower.ThetaArithmeticWeightedAdmission
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# Sharp real theta translation admission and complete derivative history

Every literal real shift belongs to `L²(k^(-q) dx)` exactly below its
strict two-ended Gaussian threshold. Equality is excluded. For every
`0 < q < 2`, the closed span of all admitted real translates is exactly
the closed span of the actual ordinary theta derivatives.
-/

open MeasureTheory Set Filter Topology

namespace RHTower

open HedenmalmThetaSource DominatedL2Sections GaloisForLFunctions.HTGeometry

noncomputable section

/-- Literal real translation of the complete theta source. -/
def thetaRealShiftSource (a x : ℝ) : ℝ := thetaCuspFullSource (x + a)

theorem continuous_thetaRealShiftSource (a : ℝ) : Continuous (thetaRealShiftSource a) :=
  contDiff_thetaCuspFullSource.continuous.comp (continuous_id.add continuous_const)

theorem thetaRealShiftSource_neg (a x : ℝ) :
    thetaRealShiftSource a (-x) = thetaRealShiftSource (-a) x := by
  change thetaCuspFullSource (-x + a) = thetaCuspFullSource (x + -a)
  rw [show -x + a = -(x + -a) by ring, thetaCuspFullSource_neg]

theorem thetaRealShiftPowerEnergy_neg (q a x : ℝ) :
    thetaPowerWeightedEnergy q (thetaRealShiftSource a) (-x) =
      thetaPowerWeightedEnergy q (thetaRealShiftSource (-a)) x := by
  simp only [thetaPowerWeightedEnergy, thetaRealShiftSource_neg, thetaCuspFullSource_neg]

/-- The complete dangerous-cusp energy has the exact positive first-atom ratio. -/
theorem thetaRealShiftSource_negative_energy_ratio (q a : ℝ) :
    Tendsto (fun x => thetaPowerWeightedEnergy q (thetaRealShiftSource a) (-x) /
      thetaShiftPowerEnvelope q a x) atTop
      (𝓝 ((4 * Real.pi ^ 2) ^ 2 * (4 * Real.pi ^ 2) ^ (-q))) := by
  have hshift : Tendsto (fun x : ℝ => x - a) atTop atTop := by
    simpa [sub_eq_add_neg] using
      tendsto_atTop_add_const_right atTop (-a) (tendsto_id (α := ℝ))
  have hf : Tendsto (fun x => thetaRealShiftSource a (-x) / thetaEnvelope (x - a))
      atTop (𝓝 (4 * Real.pi ^ 2)) := by
    apply (thetaCuspFullSource_div_envelope_tendsto.comp hshift).congr'
    filter_upwards with x
    change thetaCuspFullSource (x - a) / thetaEnvelope (x - a) = _
    rw [thetaRealShiftSource, show -x + a = -(x - a) by ring, thetaCuspFullSource_neg]
  have hpower := (Real.continuousAt_rpow_const (4 * Real.pi ^ 2) (-q)
    (Or.inl (by positivity))).tendsto.comp thetaCuspFullSource_div_envelope_tendsto
  apply ((hf.pow 2).mul hpower).congr'
  filter_upwards with x
  simp only [Function.comp_def]
  rw [Real.div_rpow (thetaCuspFullSource_pos_all x).le (thetaEnvelope_pos x).le]
  dsimp only [thetaPowerWeightedEnergy, thetaShiftPowerEnvelope]
  rw [thetaCuspFullSource_neg]
  field_simp [(thetaEnvelope_pos (x - a)).ne',
    (Real.rpow_pos_of_pos (thetaEnvelope_pos x) (-q)).ne']

/-- Every shift under its strict two-ended threshold is a genuine complex Hilbert vector. -/
theorem thetaRealShiftSource_ofReal_memLp (q a : ℝ) (hq : 0 < q)
    (hqa : q < 2 * Real.exp (-2 * |a|)) :
    MemLp (fun x : ℝ => (thetaRealShiftSource a x : ℂ)) 2
      (thetaPowerWeightedMeasure q) := by
  obtain ⟨δ, A, hδ, haA, hδ4, hmargin⟩ := theta_weighted_rectangle_exists |a| q hqa
  have hA : 0 ≤ A := (abs_nonneg a).trans haA.le
  have h := thetaCuspStripSource_translation_memLp δ A q hA hδ.le hδ4 hq hmargin
    (a : ℂ) (by simpa only [Complex.ofReal_re] using haA.le)
    (by simpa only [Complex.ofReal_im, abs_zero] using hδ.le)
  have he : (fun x : ℝ => thetaCuspStripSource ((x : ℂ) + (a : ℂ))) =
      fun x : ℝ => (thetaRealShiftSource a x : ℂ) := by
    funext x
    rw [← Complex.ofReal_add, thetaCuspStripSource_ofReal]
    rfl
  rwa [he] at h

private theorem not_integrable_thetaRealShiftSource_energy_nonneg
    (q a : ℝ) (ha : 0 ≤ a) (hqa : 2 * Real.exp (-2 * a) ≤ q) :
    ¬ Integrable (thetaPowerWeightedEnergy q (thetaRealShiftSource a)) := by
  let E := thetaPowerWeightedEnergy q (thetaRealShiftSource a)
  let L := (4 * Real.pi ^ 2) ^ 2 * (4 * Real.pi ^ 2) ^ (-q)
  have hL : 0 < L := by dsimp [L]; positivity
  obtain ⟨ε, hε, hmodel⟩ := thetaShiftPowerEnvelope_eventually_bounded_below q a ha hqa
  have hlim := thetaRealShiftSource_negative_energy_ratio q a
  have hhalf : L / 2 < L := by linarith
  have hlarge : ∀ᶠ x : ℝ in atTop, ε * (L / 2) ≤ E (-x) := by
    filter_upwards [hlim.eventually (Ioi_mem_nhds hhalf), hmodel] with x hx hm
    have hratio : L / 2 * thetaShiftPowerEnvelope q a x ≤ E (-x) :=
      (le_div_iff₀ (thetaShiftPowerEnvelope_pos q a x)).mp hx.le
    have hcompare := mul_le_mul_of_nonneg_left hm (by linarith : 0 ≤ L / 2)
    nlinarith
  intro hint
  have hn : Integrable (fun x : ℝ => E (-x)) := by
    simpa only [Function.comp_def] using
      (Measure.measurePreserving_neg (volume : Measure ℝ)).integrable_comp_of_integrable hint
  obtain ⟨R, hR⟩ := eventually_atTop.1 hlarge
  have hC : 0 < ε * (L / 2) := mul_pos hε (by linarith)
  have hconst : IntegrableOn (fun _ : ℝ => ε * (L / 2)) (Ioi R) := by
    refine MeasureTheory.Integrable.mono (hn.integrableOn (s := Ioi R))
      continuous_const.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.norm_eq_abs, abs_of_pos hC, Real.norm_eq_abs,
      abs_of_nonneg (thetaPowerWeightedEnergy_nonneg q _ (-x))]
    exact hR x hx.le
  rw [MeasureTheory.integrableOn_const_iff (by finiteness), Real.volume_Ioi] at hconst
  simp [hε.ne', hL.ne'] at hconst

/-- Both signs fail at their exact Gaussian boundary and everywhere beyond it. -/
theorem not_integrable_thetaRealShiftSource_energy (q a : ℝ)
    (hqa : 2 * Real.exp (-2 * |a|) ≤ q) :
    ¬ Integrable (thetaPowerWeightedEnergy q (thetaRealShiftSource a)) := by
  by_cases ha : 0 ≤ a
  · exact not_integrable_thetaRealShiftSource_energy_nonneg q a ha
      (by simpa only [abs_of_nonneg ha] using hqa)
  · intro hint
    have hneg : a < 0 := lt_of_not_ge ha
    have hflip : Integrable (thetaPowerWeightedEnergy q (thetaRealShiftSource (-a))) := by
      simpa only [Function.comp_def, thetaRealShiftPowerEnergy_neg] using
        (Measure.measurePreserving_neg (volume : Measure ℝ)).integrable_comp_of_integrable hint
    exact not_integrable_thetaRealShiftSource_energy_nonneg q (-a) (by linarith)
      (by simpa only [abs_of_neg hneg] using hqa) hflip

/-- Exact unconditional shift admission in the actual complex weighted Hilbert carrier. -/
theorem thetaRealShiftSource_ofReal_memLp_iff (q a : ℝ) (hq : 0 < q) :
    MemLp (fun x : ℝ => (thetaRealShiftSource a x : ℂ)) 2
      (thetaPowerWeightedMeasure q) ↔ q < 2 * Real.exp (-2 * |a|) := by
  constructor
  · intro hm
    have hint := (memLp_ofReal_thetaPowerWeightedMeasure_iff q
      (continuous_thetaRealShiftSource a)).mp hm
    by_contra hqa
    exact not_integrable_thetaRealShiftSource_energy q a (le_of_not_gt hqa) hint
  · exact thetaRealShiftSource_ofReal_memLp q a hq

theorem thetaRealShiftSource_memLp_iff (q a : ℝ) (hq : 0 < q) :
    MemLp (thetaRealShiftSource a) 2 (thetaPowerWeightedMeasure q) ↔
      q < 2 * Real.exp (-2 * |a|) := by
  rw [memLp_thetaPowerWeightedMeasure_iff q (continuous_thetaRealShiftSource a),
    ← memLp_ofReal_thetaPowerWeightedMeasure_iff q (continuous_thetaRealShiftSource a)]
  exact thetaRealShiftSource_ofReal_memLp_iff q a hq

/-- The literal paper boundary is `log(2/q)/2`, with strict admission. -/
theorem thetaRealShiftSource_threshold_iff (q a : ℝ) (hq : 0 < q) :
    q < 2 * Real.exp (-2 * |a|) ↔ |a| < Real.log (2 / q) / 2 := by
  calc
    q < 2 * Real.exp (-2 * |a|) ↔ q * Real.exp (2 * |a|) < 2 := by
      rw [show -2 * |a| = -(2 * |a|) by ring, Real.exp_neg,
        ← div_eq_mul_inv, lt_div_iff₀ (Real.exp_pos _)]
    _ ↔ Real.exp (2 * |a|) < 2 / q := by
      rw [lt_div_iff₀ hq]
      simp only [mul_comm]
    _ ↔ 2 * |a| < Real.log (2 / q) :=
      (Real.lt_log_iff_exp_lt (by positivity : 0 < 2 / q)).symm
    _ ↔ |a| < Real.log (2 / q) / 2 := by constructor <;> intro h <;> linarith

theorem thetaRealShiftSource_ofReal_memLp_iff_log (q a : ℝ) (hq : 0 < q) :
    MemLp (fun x : ℝ => (thetaRealShiftSource a x : ℂ)) 2
      (thetaPowerWeightedMeasure q) ↔ |a| < Real.log (2 / q) / 2 :=
  (thetaRealShiftSource_ofReal_memLp_iff q a hq).trans
    (thetaRealShiftSource_threshold_iff q a hq)

theorem thetaRealShiftSource_memLp_iff_log (q a : ℝ) (hq : 0 < q) :
    MemLp (thetaRealShiftSource a) 2 (thetaPowerWeightedMeasure q) ↔
      |a| < Real.log (2 / q) / 2 :=
  (thetaRealShiftSource_memLp_iff q a hq).trans (thetaRealShiftSource_threshold_iff q a hq)

/-- The original reciprocal theta weight has exactly the paper's open real interval. -/
theorem thetaRealShiftSource_memLp_reciprocal_iff (a : ℝ) :
    MemLp (thetaRealShiftSource a) 2 (thetaPowerWeightedMeasure 1) ↔
      |a| < Real.log 2 / 2 := by
  simpa only [div_one] using thetaRealShiftSource_memLp_iff_log 1 a (by norm_num)

/-- Parameters are exactly the genuinely admitted real theta shifts. -/
abbrev ThetaAdmittedRealShift (q : ℝ) := {a : ℝ // q < 2 * Real.exp (-2 * |a|)}

/-- Literal closed span of every admitted real translate in the fixed weighted carrier. -/
def thetaWeightedRealTranslationHistory (q : ℝ) :
    Submodule ℂ (Lp ℂ 2 (thetaPowerWeightedMeasure q)) :=
  (Submodule.span ℂ (range fun a : ThetaAdmittedRealShift q =>
    thetaWeightedTranslationClass q ((a : ℝ) : ℂ))).topologicalClosure

/-- Every admitted real shift, of either sign, belongs to actual derivative history. -/
theorem thetaWeightedTranslationClass_mem_derivativeHistory_of_abs (q a : ℝ) (hq : 0 < q)
    (hqa : q < 2 * Real.exp (-2 * |a|)) :
    thetaWeightedTranslationClass q (a : ℂ) ∈ thetaWeightedDerivativeHistory q := by
  obtain ⟨δ, A, hδ, haA, hδ4, hmargin⟩ := theta_weighted_rectangle_exists |a| q hqa
  have hA : 0 ≤ A := (abs_nonneg a).trans haA.le
  have hzero : (0 : ℂ) ∈ thetaTranslationRectangle δ A := by
    change |(0 : ℂ).re| < A ∧ |(0 : ℂ).im| < δ
    simpa using And.intro (lt_of_le_of_lt (abs_nonneg a) haA) hδ
  have haU : (a : ℂ) ∈ thetaTranslationRectangle δ A := by
    change |(a : ℂ).re| < A ∧ |(a : ℂ).im| < δ
    simpa only [Complex.ofReal_re, Complex.ofReal_im, abs_zero] using And.intro haA hδ
  let F := thetaWeightedTranslationFamily q δ A hA hδ.le hδ4 hq hmargin
  have h := F.section_mem_closed_span_jets
    (convex_thetaTranslationRectangle δ A).isPreconnected hzero haU
  have he : (fun n : ℕ => iteratedDeriv n F.section 0) = thetaWeightedDerivativeVector q := by
    funext n
    exact thetaWeightedTranslationFamily_iteratedDeriv_zero q δ A hA hδ.le hδ4 hq hmargin hzero n
  rw [he, thetaWeightedTranslationFamily_section q δ A hA hδ.le hδ4 hq hmargin haU] at h
  exact h

theorem thetaWeightedRealTranslationHistory_le_derivativeHistory (q : ℝ) (hq : 0 < q) :
    thetaWeightedRealTranslationHistory q ≤ thetaWeightedDerivativeHistory q := by
  apply (Submodule.span ℂ (range fun a : ThetaAdmittedRealShift q =>
    thetaWeightedTranslationClass q ((a : ℝ) : ℂ))).topologicalClosure_minimal
    (Submodule.span_le.mpr ?_) (Submodule.isClosed_topologicalClosure _)
  rintro _ ⟨a, rfl⟩
  exact thetaWeightedTranslationClass_mem_derivativeHistory_of_abs q a hq a.property

private theorem tendsto_thetaRealAxis_nhdsNE :
    Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[≠] (0 : ℝ)) (𝓝[≠] (0 : ℂ)) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · exact (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t ht
    simp only [mem_compl_iff, mem_singleton_iff] at ht ⊢
    exact fun h => ht (Complex.ofReal_inj.mp h)

/-- Analytic uniqueness on the literal real orbit puts every actual jet in its closed span. -/
theorem thetaWeightedDerivativeVector_mem_realTranslationHistory
    (q : ℝ) (hq : 0 < q) (hq2 : q < 2) (n : ℕ) :
    thetaWeightedDerivativeVector q n ∈ thetaWeightedRealTranslationHistory q := by
  change thetaWeightedDerivativeVector q n ∈
    (Submodule.span ℂ (range fun a : ThetaAdmittedRealShift q =>
      thetaWeightedTranslationClass q ((a : ℝ) : ℂ))).topologicalClosure
  rw [RHTower.mem_topologicalClosure_span_iff_forall_dual]
  intro L hL
  obtain ⟨δ, A, hδ, hA, hδ4, hmargin⟩ := theta_weighted_rectangle_exists 0 q (by simpa using hq2)
  have hzero : (0 : ℂ) ∈ thetaTranslationRectangle δ A := by
    change |(0 : ℂ).re| < A ∧ |(0 : ℂ).im| < δ
    simpa using And.intro hA hδ
  let F := thetaWeightedTranslationFamily q δ A hA.le hδ.le hδ4 hq hmargin
  let g : ℂ → ℂ := fun z => L (F.section z)
  have hg : AnalyticOnNhd ℂ g F.domain := by
    apply DifferentiableOn.analyticOnNhd _ F.isOpen_domain
    intro z hz
    exact (L.hasFDerivAt.comp_hasDerivAt z
      (F.hasDerivAt_section hz)).differentiableAt.differentiableWithinAt
  have hreal : ∀ᶠ t : ℝ in 𝓝 0, g (t : ℂ) = 0 := by
    filter_upwards [Ioo_mem_nhds (by linarith : -A < 0) hA] with t ht
    have htA : |t| < A := abs_lt.mpr ht
    have hqa : q < 2 * Real.exp (-2 * |t|) := by
      have he := Real.exp_le_exp.mpr (by linarith : -2 * A ≤ -2 * |t|)
      have hc := mul_le_mul_of_nonneg_left (Real.cos_le_one (2 * δ))
        (by positivity : 0 ≤ 2 * Real.exp (-2 * A))
      nlinarith
    have htU : (t : ℂ) ∈ thetaTranslationRectangle δ A := by
      change |(t : ℂ).re| < A ∧ |(t : ℂ).im| < δ
      simpa only [Complex.ofReal_re, Complex.ofReal_im, abs_zero] using And.intro htA hδ
    dsimp only [g]
    rw [thetaWeightedTranslationFamily_section q δ A hA.le hδ.le hδ4 hq hmargin htU]
    exact hL ⟨t, hqa⟩
  have hfreq : ∃ᶠ z : ℂ in 𝓝[≠] 0, g z = 0 :=
    tendsto_thetaRealAxis_nhdsNE.frequently
      (hreal.filter_mono nhdsWithin_le_nhds).frequently
  have he : g =ᶠ[𝓝 0] (0 : ℂ → ℂ) :=
    (hg 0 hzero).frequently_zero_iff_eventually_zero.mp hfreq
  have hjet := he.iteratedDeriv_eq n
  rw [iteratedDeriv_const_zero] at hjet
  change iteratedDeriv n (fun z => L (F.section z)) 0 = 0 at hjet
  rw [iteratedDeriv_clm_comp_eqOn F.isOpen_domain L F.differentiableOn_section n hzero] at hjet
  change L (iteratedDeriv n
    (thetaWeightedTranslationFamily q δ A hA.le hδ.le hδ4 hq hmargin).section 0) = 0 at hjet
  rw [thetaWeightedTranslationFamily_iteratedDeriv_zero q δ A hA.le hδ.le hδ4 hq hmargin hzero n] at hjet
  exact hjet

theorem thetaWeightedDerivativeHistory_le_realTranslationHistory
    (q : ℝ) (hq : 0 < q) (hq2 : q < 2) :
    thetaWeightedDerivativeHistory q ≤ thetaWeightedRealTranslationHistory q := by
  apply (Submodule.span ℂ (range (thetaWeightedDerivativeVector q))).topologicalClosure_minimal
    (Submodule.span_le.mpr ?_) (Submodule.isClosed_topologicalClosure _)
  rintro _ ⟨n, rfl⟩
  exact thetaWeightedDerivativeVector_mem_realTranslationHistory q hq hq2 n

/-- Exact equality of both literal closed histories throughout the positive weighted scale. -/
theorem thetaWeightedDerivativeHistory_eq_realTranslationHistory
    (q : ℝ) (hq : 0 < q) (hq2 : q < 2) :
    thetaWeightedDerivativeHistory q = thetaWeightedRealTranslationHistory q :=
  le_antisymm (thetaWeightedDerivativeHistory_le_realTranslationHistory q hq hq2)
    (thetaWeightedRealTranslationHistory_le_derivativeHistory q hq)

theorem thetaWeightedDerivativeHistory_reciprocal_eq_realTranslationHistory :
    thetaWeightedDerivativeHistory 1 = thetaWeightedRealTranslationHistory 1 :=
  thetaWeightedDerivativeHistory_eq_realTranslationHistory 1 (by norm_num) (by norm_num)

end

end RHTower
