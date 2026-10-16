import GaloisForLFunctions.RHTower.EvenSectorWindowPurification
import GaloisForLFunctions.RHTower.CCMRestrictedWeilEvenSectorCrossZeros
import GaloisForLFunctions.RHTower.CCMApertureCorrelationKernel
import GaloisForLFunctions.RHTower.CCMZetaWeilSmoothIdentity

/-!
# Actual single sources for the energy completion of EWU mixtures

At fixed aperture and finite energy budget, normalized positive smooth even
polar mixtures remain single actual sources after pointwise completion of
their whole autocorrelations. The limiting source belongs to the complete
archimedean form domain at the original aperture. No choice of spectral
phases along the approximating family, smoothness of its limit, or sign of
the Weil form is assumed.
-/

open Complex MeasureTheory Set Filter Topology Zeta23
open scoped InnerProduct NNReal ComplexConjugate

noncomputable section
namespace RHTower.EvenSector
open WeilOneSided

/-- The complete physical autocorrelation, in the `EF.weilTest` orientation. -/
def energyProfile (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a)
    (h : ℝ) : ℂ := ccmApertureCorrelation a f (-h)

theorem continuous_energyProfile (a : SuzukiPositiveAperture) :
    Continuous (energyProfile a) := by
  apply continuous_pi
  intro h
  exact ((logTranslationCLM (-h)).continuous.comp continuous_subtype_val).inner
    continuous_subtype_val

theorem energyProfile_zero (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) :
    energyProfile a f 0 = (‖f‖ ^ 2 : ℝ) := by
  simp only [energyProfile, ccmApertureCorrelation, neg_zero,
    logTranslationCLM_zero_apply, inner_self_eq_norm_sq_to_K]
  simp only [Complex.ofReal_pow, Submodule.norm_coe]
  rfl

/-- Normalized even polar physical sources in the actual Weil-energy sublevel. -/
def physicalEvenPolarBudget (a : SuzukiPositiveAperture) (B : ℝ) :
    Set (suzukiApertureHilbert a) :=
  {f | ‖f‖ = 1 ∧ l2Reflection f.1 = f.1 ∧
    inner ℂ (ccmPolarApertureVector a (1 / 2)) f = 0 ∧
    inner ℂ (ccmPolarApertureVector a (-1 / 2)) f = 0 ∧
    ∃ u : CCMArchimedeanFormDomain a,
      ccmArchimedeanFormToAperture a u = f ∧ ccmRestrictedWeilSourceQuadratic a u ≤ B}

theorem isClosed_physicalEvenPolarBudget (a : SuzukiPositiveAperture) (B : ℝ) :
    IsClosed (physicalEvenPolarBudget a B) := by
  exact (isClosed_eq continuous_norm continuous_const).inter
    ((isClosed_eq (l2Reflection.continuous.comp continuous_subtype_val)
      continuous_subtype_val).inter
    ((isClosed_eq (continuous_const.inner continuous_id) continuous_const).inter
    ((isClosed_eq (continuous_const.inner continuous_id) continuous_const).inter
      (isClosed_ccmRestrictedWeilSource_sublevel a B))))

/-- Energy, mass, parity and the literal pole moments give a compact physical source set. -/
theorem isCompact_physicalEvenPolarBudget (a : SuzukiPositiveAperture) (B : ℝ) :
    IsCompact (physicalEvenPolarBudget a B) := by
  let R := Real.sqrt (max 0 (B + ‖ccmRestrictedWeilBoundedRemainder a‖))
  apply (isCompactOperator_ccmArchimedeanFormToAperture a
    |>.isCompact_closure_image_closedBall R).of_isClosed_subset
      (isClosed_physicalEvenPolarBudget a B)
  rintro f ⟨hn, -, -, -, u, rfl, hQ⟩
  apply subset_closure
  refine ⟨u, ?_, rfl⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  have hb := ccmArchimedeanFormNorm_sq_le_source_add_remainder_norm_mass a u
  rw [hn, one_pow, mul_one] at hb
  have hs : ‖u‖ ^ 2 ≤ max 0 (B + ‖ccmRestrictedWeilBoundedRemainder a‖) :=
    hb.trans (le_max_of_le_right (by linarith))
  have hr := Real.sq_sqrt (le_max_left (0 : ℝ) (B + ‖ccmRestrictedWeilBoundedRemainder a‖))
  dsimp only [R]
  nlinarith [Real.sqrt_nonneg (max 0 (B + ‖ccmRestrictedWeilBoundedRemainder a‖)),
    norm_nonneg u]

/-- Full profiles of actual normalized even polar sources of finite energy. -/
def completedEnergyProfiles (a : SuzukiPositiveAperture) (B : ℝ) : Set (ℝ → ℂ) :=
  energyProfile a '' physicalEvenPolarBudget a B

theorem isCompact_completedEnergyProfiles (a : SuzukiPositiveAperture) (B : ℝ) :
    IsCompact (completedEnergyProfiles a B) :=
  (isCompact_physicalEvenPolarBudget a B).image (continuous_energyProfile a)

theorem isClosed_completedEnergyProfiles (a : SuzukiPositiveAperture) (B : ℝ) :
    IsClosed (completedEnergyProfiles a B) :=
  (isCompact_completedEnergyProfiles a B).isClosed

theorem mem_completedEnergyProfiles_iff (a : SuzukiPositiveAperture) (B : ℝ)
    (P : ℝ → ℂ) : P ∈ completedEnergyProfiles a B ↔
    ∃ u : CCMArchimedeanFormDomain a, IsPolarConstrained a u ∧ CCMEvenSector.IsEven a u ∧
      ‖ccmArchimedeanFormToAperture a u‖ = 1 ∧ ccmRestrictedWeilSourceQuadratic a u ≤ B ∧
      energyProfile a (ccmArchimedeanFormToAperture a u) = P := by
  constructor
  · rintro ⟨f, ⟨hn, he, hp, hm, u, rfl, hQ⟩, hP⟩
    refine ⟨u, ⟨hp, hm⟩, ?_, hn, hQ, hP⟩
    apply ccmArchimedeanFormToAperture_injective a
    apply Subtype.ext
    rw [ccmArchimedeanFormToAperture_reflection, he]
  · rintro ⟨u, hp, he, hn, hQ, hP⟩
    refine ⟨ccmArchimedeanFormToAperture a u, ⟨hn, ?_, hp.1, hp.2, u, rfl, hQ⟩, hP⟩
    rw [← ccmArchimedeanFormToAperture_reflection, he]

/-- Literal energy on smooth compact profiles; its completed realization is the CCM form. -/
def nativeProfileEnergy (P : ℝ → ℂ) : ℝ :=
  (weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) P).re

def interiorMixtureProfile (a : SuzukiPositiveAperture)
    (c : InteriorWindowedSmoothEvenPolarTestFn a →₀ ℝ≥0) : ℝ → ℂ :=
  c.sum fun f t => (t : ℝ) • EF.weilTest f.1.1.1.1 f.1.1.1.1

/-- Finite positive mixtures, normalized and budgeted through their entire literal profile. -/
def nativeEnergyProfiles (a : SuzukiPositiveAperture) (B : ℝ) : Set (ℝ → ℂ) :=
  {P | ∃ c : InteriorWindowedSmoothEvenPolarTestFn a →₀ ℝ≥0,
    interiorMixtureProfile a c = P ∧ P 0 = 1 ∧ nativeProfileEnergy P ≤ B}

def interiorCCMSource {a : SuzukiPositiveAperture}
    (f : InteriorWindowedSmoothEvenPolarTestFn a) : CCMComplexSmoothInteriorSource a :=
  ⟨f.1.1.1.1, f.1.2, f.1.1.1.2.2, f.2⟩

theorem energyProfile_interiorCCMSource {a : SuzukiPositiveAperture}
    (f : InteriorWindowedSmoothEvenPolarTestFn a) :
    energyProfile a (ccmArchimedeanFormToAperture a (interiorCCMSource f).toCCMFormVector) =
      EF.weilTest f.1.1.1.1 f.1.1.1.1 := by
  funext h
  rw [energyProfile, ccmApertureCorrelation,
    inner_logTranslationCLM_ccmComplexSmoothFormVector]
  apply integral_congr_ae
  filter_upwards with x
  change star (f.1.1.1.1 (x + -h)) * f.1.1.1.1 x =
    f.1.1.1.1 x * conj (f.1.1.1.1 (-(h-x)))
  rw [neg_sub, sub_eq_add_neg, mul_comm]
  rfl

theorem sourceEnergy_interiorCCMSource {a : SuzukiPositiveAperture}
    (f : InteriorWindowedSmoothEvenPolarTestFn a) :
    ccmRestrictedWeilSourceQuadratic a (interiorCCMSource f).toCCMFormVector =
      nativeProfileEnergy (EF.weilTest f.1.1.1.1 f.1.1.1.1) := by
  rw [ccmRestrictedWeilSource_complexSmooth_eq_zetaWeil]
  change (zetaZeroConfig.W f.1.1.1.1 f.1.1.1.1).re = _
  rw [zeta_W_eq_weilFullFunctional f.1.1.1.2.1 f.1.1.1.2.2]
  rfl

theorem even_interiorCCMSource {a : SuzukiPositiveAperture}
    (f : InteriorWindowedSmoothEvenPolarTestFn a) :
    CCMEvenSector.IsEven a (interiorCCMSource f).toCCMFormVector := by
  apply ccmArchimedeanFormToAperture_injective a
  apply Subtype.ext
  rw [ccmArchimedeanFormToAperture_reflection]
  apply Lp.ext
  have hf := (interiorCCMSource f).toCCMFormVector_physical_coeFn
  have hneg := hf.comp_tendsto
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.tendsto_ae
  filter_upwards [l2Reflection_ae _, hf, hneg] with x hr hx hn
  dsimp only [Function.comp_apply] at hn
  rw [hr, hn, hx]
  exact f.1.1.2.1 x

private theorem polarMoment_eq_paperFT {a : SuzukiPositiveAperture}
    (f : CCMComplexSmoothInteriorSource a) (s : ℝ) :
    inner ℂ (ccmPolarApertureVector a s)
      (ccmArchimedeanFormToAperture a f.toCCMFormVector) =
        paperFT f (-((s : ℂ) * I)) := by
  rw [inner_ccmPolarApertureVector_ccmComplexSmoothFormVector, paperFT]
  apply integral_congr_ae
  filter_upwards with x
  rw [show I * -((s : ℂ) * I) * (x : ℂ) = ((s*x : ℝ) : ℂ) by
    push_cast; calc
      _ = (s : ℂ) * (x : ℂ) * -(I*I) := by ring
      _ = _ := by rw [I_mul_I]; ring]
  rw [Complex.ofReal_exp]
  ring

theorem polar_interiorCCMSource {a : SuzukiPositiveAperture}
    (f : InteriorWindowedSmoothEvenPolarTestFn a) :
    IsPolarConstrained a (interiorCCMSource f).toCCMFormVector := by
  have hm : paperFT f.1.1.1.1 (I/2) = 0 := f.1.1.2.2
  have hp : paperFT f.1.1.1.1 (-(I/2)) = 0 := by
    rw [paperFT_neg_of_even f.1.1.2.1, hm]
  constructor
  · rw [polarMoment_eq_paperFT]
    change paperFT f.1.1.1.1 (-(((1 / 2 : ℝ) : ℂ) * I)) = 0
    have harg : -(((1 / 2 : ℝ) : ℂ) * I) = -(I/2) := by push_cast; ring
    rw [harg]
    exact hp
  · rw [polarMoment_eq_paperFT]
    change paperFT f.1.1.1.1 (-(((-1 / 2 : ℝ) : ℂ) * I)) = 0
    have harg : -(((-1 / 2 : ℝ) : ℂ) * I) = I/2 := by push_cast; ring
    rw [harg]
    exact hm

theorem nativeEnergyProfiles_subset_completed (a : SuzukiPositiveAperture) (B : ℝ) :
    nativeEnergyProfiles a B ⊆ completedEnergyProfiles a B := by
  rintro P ⟨c, hc, hmass, hbudget⟩
  obtain ⟨f, hf⟩ := exists_interior_window_purification a c
  have hP : EF.weilTest f.1.1.1.1 f.1.1.1.1 = P := hf.trans hc
  rw [mem_completedEnergyProfiles_iff]
  refine ⟨(interiorCCMSource f).toCCMFormVector, polar_interiorCCMSource f,
    even_interiorCCMSource f, ?_, ?_, (energyProfile_interiorCCMSource f).trans hP⟩
  · have h := congrFun ((energyProfile_interiorCCMSource f).trans hP) 0
    rw [energyProfile_zero, hmass] at h
    have hs : ‖ccmArchimedeanFormToAperture a (interiorCCMSource f).toCCMFormVector‖ ^ 2 = 1 :=
      by exact_mod_cast h
    nlinarith [norm_nonneg (ccmArchimedeanFormToAperture a (interiorCCMSource f).toCCMFormVector)]
  · rwa [sourceEnergy_interiorCCMSource, hP]

/-- **Purification survives energy completion.** Every pointwise limit of
normalized, energy-budgeted finite positive even polar mixtures is the whole
autocorrelation of one actual even polar form-domain source at the same aperture. -/
theorem closure_nativeEnergyProfiles_subset_completed (a : SuzukiPositiveAperture) (B : ℝ) :
    closure (nativeEnergyProfiles a B) ⊆ completedEnergyProfiles a B :=
  closure_minimal (nativeEnergyProfiles_subset_completed a B)
    (isClosed_completedEnergyProfiles a B)

/-- The native energy completion is compact, with no loss of normalization or aperture. -/
theorem isCompact_closure_nativeEnergyProfiles (a : SuzukiPositiveAperture) (B : ℝ) :
    IsCompact (closure (nativeEnergyProfiles a B)) :=
  (isCompact_completedEnergyProfiles a B).of_isClosed_subset isClosed_closure
    (closure_nativeEnergyProfiles_subset_completed a B)

end RHTower.EvenSector
