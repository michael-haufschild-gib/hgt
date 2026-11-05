import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheLogarithmicFormHasItsCutoffIdentity
import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheLogarithmicAndWeilFormDomainsAgree
import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheHalfLineLogarithmicGreenSolutionsHaveBoundaryValues

/-!
# Actual Weil Riesz vectors localize to the logarithmic half-line

Overlapping endpoint cutoffs turn the actual interval equation into the
positive half-line equation. The full forcing is bounded, and Green uniqueness
identifies both localized Riesz vectors with their literal renewal solutions.
-/

open MeasureTheory Set Filter Topology Complex
open scoped FourierTransform ENNReal InnerProductSpace
noncomputable section
namespace GaloisForLFunctions.CanonicalSystemOfTheWindowTower
open _root_.RHTower HTGeometry

/-- Restriction to the closed positive half-line, with its actual support subtype. -/
def logarithmicHalfLineRestriction (f : RealLineL2) : LogarithmicHalfLineL2 :=
  ⟨indicatorCutoff (Ici (0 : ℝ)) measurableSet_Ici f, by
    rw [mem_halfLineL2_iff]
    filter_upwards [indicatorCutoff_ae (Ici (0 : ℝ)) measurableSet_Ici f] with x hx
    intro hneg
    rw [hx, indicator_of_notMem (s := Ici (0 : ℝ)) (not_le.mpr hneg)]⟩

theorem inner_logarithmicHalfLineRestriction (v : LogarithmicHalfLineL2) (f : RealLineL2) :
    inner ℂ v (logarithmicHalfLineRestriction f) = inner ℂ (v : RealLineL2) f := by
  change inner ℂ (v : RealLineL2) (indicatorCutoff (Ici (0 : ℝ)) measurableSet_Ici f) = _
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [indicatorCutoff_ae (Ici (0 : ℝ)) measurableSet_Ici f,
    (mem_halfLineL2_iff (v : RealLineL2)).mp v.property] with x hx hv
  rw [hx]
  by_cases hpos : 0 ≤ x
  · rw [indicator_of_mem (s := Ici (0 : ℝ)) hpos]
  · rw [indicator_of_notMem (s := Ici (0 : ℝ)) hpos, hv (lt_of_not_ge hpos)]
    simp only [inner_zero_left]

theorem logarithmicHalfLineRestriction_bounded (f : RealLineL2) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ᵐ x ∂volume, ‖f x‖ ≤ C) :
    ∀ᵐ x ∂volume, ‖(logarithmicHalfLineRestriction f : RealLineL2) x‖ ≤ C := by
  filter_upwards [indicatorCutoff_ae (Ici (0 : ℝ)) measurableSet_Ici f, hf] with x hx hfx
  change ‖(indicatorCutoff (Ici (0 : ℝ)) measurableSet_Ici f) x‖ ≤ C
  rw [hx]
  by_cases hpos : 0 ≤ x
  · rwa [indicator_of_mem (s := Ici (0 : ℝ)) hpos]
  · rw [indicator_of_notMem (s := Ici (0 : ℝ)) hpos, norm_zero]
    exact hC

/-- The explicit overlapping endpoint cutoff attached to an aperture. -/
def logarithmicApertureEndpointCutoff (a : SuzukiPositiveAperture) : RealLineL2 →L[ℂ] RealLineL2 :=
  logarithmicCutoffMultiplier (continuous_logarithmicEndpointCutoff a.1).measurable
    zero_le_one (logarithmicEndpointCutoff_abs_le a.1)

/-- The aperture cutoff acts by its literal real multiplier almost everywhere. -/
theorem logarithmicApertureEndpointCutoff_coeFn (a : SuzukiPositiveAperture) (f : RealLineL2) :
    (logarithmicApertureEndpointCutoff a f : ℝ → ℂ) =ᵐ[volume]
      fun x => (logarithmicEndpointCutoff a.1 x : ℂ) * f x :=
  logarithmicCutoffMultiplier_coeFn (continuous_logarithmicEndpointCutoff a.1).measurable
    zero_le_one (logarithmicEndpointCutoff_abs_le a.1) f

private theorem aperture_source_zero (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) :
    ∀ᵐ x ∂volume, x ∉ centralInterval a.1 → (f : RealLineL2) x = 0 := by
  have hc := indicatorCutoff_ae (centralInterval a.1) (measurableSet_centralInterval a.1) f.1
  rw [indicatorCutoff_suzukiApertureHilbert] at hc
  filter_upwards [hc] with x hx hn
  rw [hx, indicator_of_notMem hn]

private theorem translated_aperture_mem_halfLine (a : SuzukiPositiveAperture)
    (f : suzukiApertureHilbert a) : logTranslationCLM (-a.1) (f : RealLineL2) ∈ halfLineL2 := by
  rw [mem_halfLineL2_iff]
  have hs := (MellinL2.realTranslation_measurePreserving (-a.1)).quasiMeasurePreserving.ae
    (aperture_source_zero a f)
  filter_upwards [logarithmicTranslation_coeFn (-a.1) (f : RealLineL2), hs] with x hx hsx
  intro hneg
  rw [hx]
  change (f : RealLineL2) (x + -a.1) = 0
  apply hsx
  change ¬(-a.1 ≤ x + -a.1 ∧ x + -a.1 ≤ a.1)
  intro h
  linarith only [h.1, hneg]

private theorem endpointCutoff_mem_halfLine (a : SuzukiPositiveAperture)
    {f : RealLineL2} (hf : f ∈ halfLineL2) : logarithmicApertureEndpointCutoff a f ∈ halfLineL2 := by
  rw [mem_halfLineL2_iff]
  filter_upwards [logarithmicApertureEndpointCutoff_coeFn a f, (mem_halfLineL2_iff f).mp hf] with x hx hfz
  intro hneg
  rw [hx, hfz hneg, mul_zero]

/-- The actual localized source after moving the left aperture endpoint to zero. -/
def logarithmicApertureLeftLocalized (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) :
    LogarithmicHalfLineL2 :=
  ⟨logarithmicApertureEndpointCutoff a (logTranslationCLM (-a.1) f),
    endpointCutoff_mem_halfLine a (translated_aperture_mem_halfLine a f)⟩

/-- The localized source is the literal translated cutoff product almost everywhere. -/
theorem logarithmicApertureLeftLocalized_coeFn (a : SuzukiPositiveAperture)
    (f : suzukiApertureHilbert a) :
    ((logarithmicApertureLeftLocalized a f : RealLineL2) : ℝ → ℂ) =ᵐ[volume]
      fun x => (logarithmicEndpointCutoff a.1 x : ℂ) * (f : RealLineL2) (x - a.1) := by
  filter_upwards [logarithmicApertureEndpointCutoff_coeFn a (logTranslationCLM (-a.1) f),
    logarithmicTranslation_coeFn (-a.1) (f : RealLineL2)] with x hx ht
  change (logarithmicApertureEndpointCutoff a (logTranslationCLM (-a.1) f)) x = _
  rw [hx, ht, sub_eq_add_neg]

private theorem endpointCutoff_translated_mem_aperture (a : SuzukiPositiveAperture)
    (v : LogarithmicHalfLineL2) :
    logTranslationCLM a.1 (logarithmicApertureEndpointCutoff a v) ∈ suzukiApertureHilbert a := by
  let w := logTranslationCLM a.1 (logarithmicApertureEndpointCutoff a v)
  have hP := (logarithmicApertureEndpointCutoff_coeFn a (v : RealLineL2)).comp_tendsto
      (MellinL2.realTranslation_measurePreserving a.1).quasiMeasurePreserving.tendsto_ae
  have hv := (MellinL2.realTranslation_measurePreserving a.1).quasiMeasurePreserving.ae
    ((mem_halfLineL2_iff (v : RealLineL2)).mp v.property)
  have hw : ∀ᵐ x ∂volume, x ∉ centralInterval a.1 → w x = 0 := by
    filter_upwards [logarithmicTranslation_coeFn a.1 (logarithmicApertureEndpointCutoff a v), hP, hv] with x hx hPx hvx
    intro hout
    change (logarithmicApertureEndpointCutoff a v) (x + a.1) =
      (logarithmicEndpointCutoff a.1 (x + a.1) : ℂ) * (v : RealLineL2) (x + a.1) at hPx
    change logTranslationCLM a.1 (logarithmicApertureEndpointCutoff a v) x = 0
    rw [hx, hPx]
    change x + a.1 < 0 → (v : RealLineL2) (x + a.1) = 0 at hvx
    by_cases hleft : x < -a.1
    · rw [hvx (by linarith only [hleft]), mul_zero]
    · have hright : a.1 < x := by
        by_contra! h
        exact hout ⟨le_of_not_gt hleft, h⟩
      rw [logarithmicEndpointCutoff_eq_zero a.2 (by linarith only [hright, a.2]),
        Complex.ofReal_zero, zero_mul]
  change ∃ g : RealLineL2, indicatorCutoff (centralInterval a.1)
    (measurableSet_centralInterval a.1) g =
      logTranslationCLM a.1 (logarithmicApertureEndpointCutoff a v)
  refine ⟨w, ?_⟩
  apply Lp.ext
  filter_upwards [indicatorCutoff_ae (centralInterval a.1) (measurableSet_centralInterval a.1) w,
    hw] with x hx hwx
  rw [hx]
  by_cases hmem : x ∈ centralInterval a.1
  · rw [indicator_of_mem hmem]
  · rw [indicator_of_notMem hmem, hwx hmem]

private theorem logarithmicTranslation_cancel (a : ℝ) (f : RealLineL2) :
    logTranslationCLM a (logTranslationCLM (-a) f) = f := by
  have h : logTranslationCLM (-(-a)) (logTranslationCLM (-a) f) = f :=
    congrArg (fun T : SoninL2 →L[ℂ] SoninL2 => T f) (logTranslationCLM_neg_mul (-a))
  simpa only [neg_neg] using h

/-- The explicit bounded commutator for the endpoint cutoff. -/
def logarithmicApertureEndpointCommutator (a : SuzukiPositiveAperture) :
    SchurKernel (volume : Measure ℝ) :=
  logarithmicCutoffSchurKernel (continuous_logarithmicEndpointCutoff a.1).measurable
    (div_nonneg (by norm_num : (0 : ℝ) ≤ 2) a.2.le)
    (logarithmicEndpointCutoff_lipschitz a.2)

/-- Full forcing of the actual localized half-line equation. -/
def logarithmicApertureLeftForcing (a : SuzukiPositiveAperture)
    (u g : suzukiApertureHilbert a) : LogarithmicHalfLineL2 :=
  logarithmicHalfLineRestriction
    (logarithmicApertureEndpointCutoff a (logTranslationCLM (-a.1) g) +
      (logarithmicApertureEndpointCommutator a).op (logTranslationCLM (-a.1) u))

private theorem logarithmicTranslation_bounded (t : ℝ) {f : RealLineL2} {C : ℝ}
    (hf : ∀ᵐ x ∂volume, ‖f x‖ ≤ C) : ∀ᵐ x ∂volume, ‖logTranslationCLM t f x‖ ≤ C := by
  have hs := (MellinL2.realTranslation_measurePreserving t).quasiMeasurePreserving.ae hf
  filter_upwards [logarithmicTranslation_coeFn t f, hs] with x hx hfx
  rw [hx]
  exact hfx

private theorem logarithmicApertureEndpointCutoff_bounded (a : SuzukiPositiveAperture)
    {f : RealLineL2} {C : ℝ} (hf : ∀ᵐ x ∂volume, ‖f x‖ ≤ C) :
    ∀ᵐ x ∂volume, ‖logarithmicApertureEndpointCutoff a f x‖ ≤ C := by
  filter_upwards [logarithmicApertureEndpointCutoff_coeFn a f, hf] with x hx hfx
  rw [hx, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_right (logarithmicEndpointCutoff_abs_le a.1 x) (norm_nonneg _)).trans
    (by simpa only [one_mul] using hfx)

/-- Interval forcing localizes to the actual half-line equation on the complete form domain. -/
theorem logarithmicApertureLeftLocalized_solves (a : SuzukiPositiveAperture)
    (u g : suzukiApertureHilbert a) (hu : HasLogarithmicEnergy (u : RealLineL2))
    (hsolve : ∀ f : suzukiApertureHilbert a, HasLogarithmicEnergy (f : RealLineL2) →
      logarithmicFullForm (f : RealLineL2) (u : RealLineL2) =
        inner ℂ (f : RealLineL2) (g : RealLineL2)) :
    HasLogarithmicEnergy (logarithmicApertureLeftLocalized a u : RealLineL2) ∧
    ∀ v : LogarithmicHalfLineL2, HasLogarithmicEnergy (v : RealLineL2) →
      logarithmicHalfLineForm v (logarithmicApertureLeftLocalized a u) =
        inner ℂ v (logarithmicApertureLeftForcing a u g) := by
  let P := logarithmicApertureEndpointCutoff a
  let s : RealLineL2 := logTranslationCLM (-a.1) (u : RealLineL2)
  let K := logarithmicApertureEndpointCommutator a
  have hs : HasLogarithmicEnergy s := hasLogarithmicEnergy_translation (-a.1) hu
  have hcut {w : RealLineL2} (hw : HasLogarithmicEnergy w) : HasLogarithmicEnergy (P w) :=
    hasLogarithmicEnergy_cutoff (continuous_logarithmicEndpointCutoff a.1).measurable
      zero_le_one (logarithmicEndpointCutoff_abs_le a.1)
      (div_nonneg (by norm_num : (0 : ℝ) ≤ 2) a.2.le)
      (logarithmicEndpointCutoff_lipschitz a.2) hw
  refine ⟨hcut hs, ?_⟩
  intro v hv
  have hPv := hcut hv
  let w : suzukiApertureHilbert a :=
    ⟨logTranslationCLM a.1 (P v), endpointCutoff_translated_mem_aperture a v⟩
  have hw : HasLogarithmicEnergy (w : RealLineL2) := hasLogarithmicEnergy_translation a.1 hPv
  have he := hsolve w hw
  have hshift := logarithmicFullForm_translation a.1 hPv hs
  have hcancel : logTranslationCLM a.1 s = (u : RealLineL2) := logarithmicTranslation_cancel _ _
  rw [hcancel] at hshift
  have hmid : logarithmicFullForm (P v) s =
      inner ℂ (v : RealLineL2) (P (logTranslationCLM (-a.1) g)) := by
    calc
      _ = logarithmicFullForm (logTranslationCLM a.1 (P v)) (u : RealLineL2) := hshift.symm
      _ = inner ℂ (logTranslationCLM a.1 (P v)) (g : RealLineL2) := he
      _ = inner ℂ (P v) (logTranslationCLM (-a.1) (g : RealLineL2)) := inner_logTranslationCLM _ _ _
      _ = _ := inner_logarithmicCutoffMultiplier _ _ _ _ _
  have hcomm := logarithmicFullForm_cutoff_identity
    (continuous_logarithmicEndpointCutoff a.1).measurable zero_le_one
    (logarithmicEndpointCutoff_abs_le a.1)
    (div_nonneg (by norm_num : (0 : ℝ) ≤ 2) a.2.le)
    (logarithmicEndpointCutoff_lipschitz a.2) hs hv
  change logarithmicFullForm (v : RealLineL2) (P s) =
    inner ℂ v (logarithmicHalfLineRestriction (P (logTranslationCLM (-a.1) g) + K.op s))
  rw [inner_logarithmicHalfLineRestriction, inner_add_right]
  change logarithmicFullForm (v : RealLineL2) (P s) - logarithmicFullForm (P v) s =
    inner ℂ (v : RealLineL2) (K.op s) at hcomm
  calc
    _ = inner ℂ (v : RealLineL2) (K.op s) + logarithmicFullForm (P v) s :=
      sub_eq_iff_eq_add.mp hcomm
    _ = _ := by rw [hmid, add_comm]

/-- Reflection acts inside every literal symmetric aperture. -/
def logarithmicApertureReflection (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) :
    suzukiApertureHilbert a :=
  ⟨l2Reflection (f : RealLineL2), by
    change ∃ g : RealLineL2, indicatorCutoff (centralInterval a.1)
      (measurableSet_centralInterval a.1) g = l2Reflection (f : RealLineL2)
    refine ⟨l2Reflection (f : RealLineL2), ?_⟩
    rw [← l2Reflection_indicatorCutoff_central, indicatorCutoff_suzukiApertureHilbert]⟩

private theorem logarithmicReflection_bounded {f : RealLineL2} {C : ℝ}
    (hf : ∀ᵐ x ∂volume, ‖f x‖ ≤ C) : ∀ᵐ x ∂volume, ‖l2Reflection f x‖ ≤ C := by
  have hs := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae hf
  filter_upwards [l2Reflection_ae f, hs] with x hx hfx
  rw [hx]
  exact hfx

/-- The interval reference equation is invariant under reflection of its source and forcing. -/
theorem logarithmic_interval_equation_reflection (a : SuzukiPositiveAperture)
    (u g : suzukiApertureHilbert a)
    (hsolve : ∀ f : suzukiApertureHilbert a, HasLogarithmicEnergy (f : RealLineL2) →
      logarithmicFullForm (f : RealLineL2) (u : RealLineL2) =
        inner ℂ (f : RealLineL2) (g : RealLineL2)) :
    ∀ f : suzukiApertureHilbert a, HasLogarithmicEnergy (f : RealLineL2) →
      logarithmicFullForm (f : RealLineL2) (logarithmicApertureReflection a u : RealLineL2) =
        inner ℂ (f : RealLineL2) (logarithmicApertureReflection a g : RealLineL2) := by
  intro f hf
  have h := hsolve (logarithmicApertureReflection a f) (hasLogarithmicEnergy_reflection hf)
  have hr := logarithmicFullForm_reflection (l2Reflection (f : RealLineL2)) (u : RealLineL2)
  rw [l2Reflection_involutive] at hr
  change logarithmicFullForm (f : RealLineL2) (l2Reflection (u : RealLineL2)) =
    inner ℂ (f : RealLineL2) (l2Reflection (g : RealLineL2))
  rw [hr]
  exact h.trans (l2Reflection_symmetric _ _)

/-- Localization preserves essential boundedness with its literal cutoff and commutator constants. -/
theorem logarithmicApertureLeftForcing_bounded (a : SuzukiPositiveAperture)
    (u g : suzukiApertureHilbert a) {Cu Cg : ℝ}
    (hCu : 0 ≤ Cu) (hu : ∀ᵐ x ∂volume, ‖(u : RealLineL2) x‖ ≤ Cu)
    (hCg : 0 ≤ Cg) (hg : ∀ᵐ x ∂volume, ‖(g : RealLineL2) x‖ ≤ Cg) :
    ∀ᵐ x ∂volume, ‖(logarithmicApertureLeftForcing a u g : RealLineL2) x‖ ≤ Cg + (2 / a.1) * Cu := by
  have hLipNonneg : 0 ≤ 2 / a.1 := div_nonneg (by norm_num) a.2.le
  apply logarithmicHalfLineRestriction_bounded _ (add_nonneg hCg (mul_nonneg hLipNonneg hCu))
  have hPu := logarithmicApertureEndpointCutoff_bounded a
    (logarithmicTranslation_bounded (-a.1) hg)
  have hKu := logarithmicCutoffSchurKernel_preserves_boundedness
    (continuous_logarithmicEndpointCutoff a.1).measurable hLipNonneg
    (logarithmicEndpointCutoff_lipschitz a.2) (logTranslationCLM (-a.1) (u : RealLineL2))
    (logarithmicTranslation_bounded (-a.1) hu)
  filter_upwards [Lp.coeFn_add
    (logarithmicApertureEndpointCutoff a (logTranslationCLM (-a.1) g))
    ((logarithmicApertureEndpointCommutator a).op (logTranslationCLM (-a.1) u)), hPu, hKu]
    with x hx hPx hKx
  rw [hx, Pi.add_apply]
  exact (norm_add_le _ _).trans (add_le_add hPx hKx)

namespace WeilHilbertBeforeContact

/-- The actual localized Riesz source solves the positive half-line form equation. -/
theorem evalVector_leftLocalized_solves (a : PrecontactAperture) (z : ℂ) :
    let u := ccmArchimedeanFormToAperture a.1 (toForm a (evalVector a z))
    HasLogarithmicEnergy (logarithmicApertureLeftLocalized a.1 u : RealLineL2) ∧
    ∀ v : LogarithmicHalfLineL2, HasLogarithmicEnergy (v : RealLineL2) →
      logarithmicHalfLineForm v (logarithmicApertureLeftLocalized a.1 u) =
        inner ℂ v (logarithmicApertureLeftForcing a.1 u (logarithmicForcing a z)) := by
  exact logarithmicApertureLeftLocalized_solves a.1 _ _ (hasLogarithmicEnergy_ccm_form a.1 _)
    (fun f hf => evalVector_logarithmic_fullForm a z f hf)

/-- The localized actual Riesz vector is the unique literal Green solution. -/
theorem evalVector_leftLocalized_eq_green (a : PrecontactAperture) (z : ℂ) :
    let u := ccmArchimedeanFormToAperture a.1 (toForm a (evalVector a z))
    logarithmicApertureLeftLocalized a.1 u =
      logarithmicHalfLineGreenOperator (logarithmicApertureLeftForcing a.1 u (logarithmicForcing a z)) := by
  exact logarithmicHalfLineGreenOperator_unique _ _
    (evalVector_leftLocalized_solves a z).1 (evalVector_leftLocalized_solves a z).2

/-- Every term of the actual localized forcing is essentially bounded. -/
theorem evalVector_leftLocalized_forcing_bounded (a : PrecontactAperture) (z : ℂ) :
    let u := ccmArchimedeanFormToAperture a.1 (toForm a (evalVector a z))
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ x ∂volume,
      ‖(logarithmicApertureLeftForcing a.1 u (logarithmicForcing a z) : RealLineL2) x‖ ≤ C := by
  obtain ⟨Cu, hCu, hu⟩ := evalVector_physical_essentially_bounded a z
  obtain ⟨Cg, hCg, hg⟩ := evalVector_logarithmicForcing_bounded a z
  refine ⟨Cg + (2 / a.1.1) * Cu,
    add_nonneg hCg (mul_nonneg (div_nonneg (by norm_num) a.1.2.le) hCu), ?_⟩
  exact logarithmicApertureLeftForcing_bounded a.1 _ _ hCu hu hCg hg

/-- The actual left localized Weil solution has its exact, absolutely convergent boundary readout. -/
theorem evalVector_leftLocalized_normalized_limit (a : PrecontactAperture) (z : ℂ) :
    let u := ccmArchimedeanFormToAperture a.1 (toForm a (evalVector a z))
    let f := logarithmicApertureLeftForcing a.1 u (logarithmicForcing a z)
    Tendsto (fun x : ℝ => logarithmicGreenRepresentative f x * (Real.sqrt (Real.log (1 / x)) : ℂ))
      (𝓝[>] (0 : ℝ)) (nhds (∫ y : ℝ, (logarithmicCausalKernel y : ℂ) * (f : RealLineL2) y)) := by
  obtain ⟨C, hC, hb⟩ := evalVector_leftLocalized_forcing_bounded a z
  apply logarithmicHalfLineGreenOperator_normalized_boundary_limit _ (δ := 1) (by norm_num) hC
  filter_upwards [hb] with y hy
  exact fun _ => hy

/-- Reflection gives the actual right endpoint localization, with every Weil term retained. -/
theorem evalVector_rightLocalized_solves (a : PrecontactAperture) (z : ℂ) :
    let u := logarithmicApertureReflection a.1
      (ccmArchimedeanFormToAperture a.1 (toForm a (evalVector a z)))
    let g := logarithmicApertureReflection a.1 (logarithmicForcing a z)
    HasLogarithmicEnergy (logarithmicApertureLeftLocalized a.1 u : RealLineL2) ∧
    ∀ v : LogarithmicHalfLineL2, HasLogarithmicEnergy (v : RealLineL2) →
      logarithmicHalfLineForm v (logarithmicApertureLeftLocalized a.1 u) =
        inner ℂ v (logarithmicApertureLeftForcing a.1 u g) := by
  apply logarithmicApertureLeftLocalized_solves
  · exact hasLogarithmicEnergy_reflection (hasLogarithmicEnergy_ccm_form a.1 _)
  · exact logarithmic_interval_equation_reflection a.1 _ _
      (fun f hf => evalVector_logarithmic_fullForm a z f hf)

/-- The actual right localized Riesz vector is the unique Green solution for the reflected forcing. -/
theorem evalVector_rightLocalized_eq_green (a : PrecontactAperture) (z : ℂ) :
    let u := logarithmicApertureReflection a.1
      (ccmArchimedeanFormToAperture a.1 (toForm a (evalVector a z)))
    let g := logarithmicApertureReflection a.1 (logarithmicForcing a z)
    logarithmicApertureLeftLocalized a.1 u =
      logarithmicHalfLineGreenOperator (logarithmicApertureLeftForcing a.1 u g) := by
  exact logarithmicHalfLineGreenOperator_unique _ _
    (evalVector_rightLocalized_solves a z).1 (evalVector_rightLocalized_solves a z).2

/-- The reflected localized forcing is also essentially bounded on the whole half-line. -/
theorem evalVector_rightLocalized_forcing_bounded (a : PrecontactAperture) (z : ℂ) :
    let u := logarithmicApertureReflection a.1
      (ccmArchimedeanFormToAperture a.1 (toForm a (evalVector a z)))
    let g := logarithmicApertureReflection a.1 (logarithmicForcing a z)
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ x ∂volume,
      ‖(logarithmicApertureLeftForcing a.1 u g : RealLineL2) x‖ ≤ C := by
  obtain ⟨Cu, hCu, hu⟩ := evalVector_physical_essentially_bounded a z
  obtain ⟨Cg, hCg, hg⟩ := evalVector_logarithmicForcing_bounded a z
  refine ⟨Cg + (2 / a.1.1) * Cu,
    add_nonneg hCg (mul_nonneg (div_nonneg (by norm_num) a.1.2.le) hCu), ?_⟩
  exact logarithmicApertureLeftForcing_bounded a.1 _ _ hCu
    (logarithmicReflection_bounded hu) hCg (logarithmicReflection_bounded hg)

/-- The actual right localized solution has its normalized reflected boundary readout. -/
theorem evalVector_rightLocalized_normalized_limit (a : PrecontactAperture) (z : ℂ) :
    let u := logarithmicApertureReflection a.1
      (ccmArchimedeanFormToAperture a.1 (toForm a (evalVector a z)))
    let g := logarithmicApertureReflection a.1 (logarithmicForcing a z)
    let f := logarithmicApertureLeftForcing a.1 u g
    Tendsto (fun x : ℝ => logarithmicGreenRepresentative f x * (Real.sqrt (Real.log (1 / x)) : ℂ))
      (𝓝[>] (0 : ℝ)) (nhds (∫ y : ℝ, (logarithmicCausalKernel y : ℂ) * (f : RealLineL2) y)) := by
  obtain ⟨C, hC, hb⟩ := evalVector_rightLocalized_forcing_bounded a z
  apply logarithmicHalfLineGreenOperator_normalized_boundary_limit _ (δ := 1) (by norm_num) hC
  filter_upwards [hb] with y hy
  exact fun _ => hy

end WeilHilbertBeforeContact

#print axioms WeilHilbertBeforeContact.evalVector_leftLocalized_eq_green
#print axioms WeilHilbertBeforeContact.evalVector_rightLocalized_eq_green
#print axioms WeilHilbertBeforeContact.evalVector_leftLocalized_forcing_bounded
#print axioms WeilHilbertBeforeContact.evalVector_rightLocalized_forcing_bounded
#print axioms WeilHilbertBeforeContact.evalVector_leftLocalized_normalized_limit
#print axioms WeilHilbertBeforeContact.evalVector_rightLocalized_normalized_limit
end GaloisForLFunctions.CanonicalSystemOfTheWindowTower
