import GaloisForLFunctions.RHTower.OddSectorWindowPurification
import GaloisForLFunctions.RHTower.EvenSectorEnergyCompletion

/-!
# Actual odd sources after energy completion

At each fixed aperture, every pointwise limit of normalized finite positive
smooth odd mixtures with a common Weil-energy budget is the autocorrelation
of one actual odd source in the complete form domain. Mass and aperture do
not escape. No spectral phase convergence or positivity of the Weil form is
assumed. The result removes rank and completion defects simultaneously.
-/

open Complex MeasureTheory Set Filter Topology Zeta23
open scoped InnerProduct NNReal ComplexConjugate

noncomputable section
namespace RHTower.OddSector
open EvenSector

/-- Actual normalized odd sources in the physical Weil-energy sublevel. -/
def physicalOddBudget (a : SuzukiPositiveAperture) (B : ℝ) :
    Set (suzukiApertureHilbert a) :=
  {f | ‖f‖=1 ∧ l2Reflection f.1=-f.1 ∧
    ∃ u : CCMArchimedeanFormDomain a,
      ccmArchimedeanFormToAperture a u=f ∧ ccmRestrictedWeilSourceQuadratic a u≤B}

theorem isClosed_physicalOddBudget (a : SuzukiPositiveAperture) (B : ℝ) :
    IsClosed (physicalOddBudget a B) := by
  exact (isClosed_eq continuous_norm continuous_const).inter
    ((isClosed_eq (l2Reflection.continuous.comp continuous_subtype_val)
      continuous_subtype_val.neg).inter
        (isClosed_ccmRestrictedWeilSource_sublevel a B))

/-- Physical compactness includes oddness, normalization, and the literal energy. -/
theorem isCompact_physicalOddBudget (a : SuzukiPositiveAperture) (B : ℝ) :
    IsCompact (physicalOddBudget a B) := by
  let R := Real.sqrt (max 0 (B+‖ccmRestrictedWeilBoundedRemainder a‖))
  apply (isCompactOperator_ccmArchimedeanFormToAperture a
    |>.isCompact_closure_image_closedBall R).of_isClosed_subset
      (isClosed_physicalOddBudget a B)
  rintro f ⟨hn,-,u,rfl,hQ⟩
  apply subset_closure
  refine ⟨u,?_,rfl⟩
  rw [Metric.mem_closedBall,dist_zero_right]
  have hb := ccmArchimedeanFormNorm_sq_le_source_add_remainder_norm_mass a u
  rw [hn,one_pow,mul_one] at hb
  have hs : ‖u‖^2 ≤ max 0 (B+‖ccmRestrictedWeilBoundedRemainder a‖) :=
    hb.trans (le_max_of_le_right (by linarith))
  have hr := Real.sq_sqrt (le_max_left (0 : ℝ) (B+‖ccmRestrictedWeilBoundedRemainder a‖))
  dsimp only [R]
  nlinarith [Real.sqrt_nonneg (max 0 (B+‖ccmRestrictedWeilBoundedRemainder a‖)),norm_nonneg u]

def completedEnergyProfiles (a : SuzukiPositiveAperture) (B : ℝ) : Set (ℝ → ℂ) :=
  energyProfile a '' physicalOddBudget a B

theorem isCompact_completedEnergyProfiles (a : SuzukiPositiveAperture) (B : ℝ) :
    IsCompact (completedEnergyProfiles a B) :=
  (isCompact_physicalOddBudget a B).image (continuous_energyProfile a)

theorem isClosed_completedEnergyProfiles (a : SuzukiPositiveAperture) (B : ℝ) :
    IsClosed (completedEnergyProfiles a B) :=
  (isCompact_completedEnergyProfiles a B).isClosed

theorem mem_completedEnergyProfiles_iff (a : SuzukiPositiveAperture) (B : ℝ)
    (P : ℝ → ℂ) : P ∈ completedEnergyProfiles a B ↔
    ∃ u : CCMArchimedeanFormDomain a, ccmArchimedeanFormReflection a u=-u ∧
      ‖ccmArchimedeanFormToAperture a u‖=1 ∧ ccmRestrictedWeilSourceQuadratic a u≤B ∧
      energyProfile a (ccmArchimedeanFormToAperture a u)=P := by
  constructor
  · rintro ⟨f,⟨hn,ho,u,rfl,hQ⟩,hP⟩
    refine ⟨u,?_,hn,hQ,hP⟩
    apply ccmArchimedeanFormToAperture_injective a
    apply Subtype.ext
    rw [ccmArchimedeanFormToAperture_reflection,map_neg,ho,Submodule.coe_neg]
  · rintro ⟨u,ho,hn,hQ,hP⟩
    refine ⟨ccmArchimedeanFormToAperture a u,⟨hn,?_,u,rfl,hQ⟩,hP⟩
    rw [← ccmArchimedeanFormToAperture_reflection,ho,map_neg,Submodule.coe_neg]

def interiorCCMSource {a : SuzukiPositiveAperture}
    (f : InteriorWindowedSmoothOddTestFn a) : CCMComplexSmoothInteriorSource a :=
  ⟨f.1.1.1.1,f.1.2,f.1.1.1.2.2,f.2⟩

theorem energyProfile_interiorCCMSource {a : SuzukiPositiveAperture}
    (f : InteriorWindowedSmoothOddTestFn a) :
    energyProfile a (ccmArchimedeanFormToAperture a (interiorCCMSource f).toCCMFormVector)=
      EF.weilTest f.1.1.1.1 f.1.1.1.1 := by
  funext h
  rw [energyProfile,ccmApertureCorrelation,inner_logTranslationCLM_ccmComplexSmoothFormVector]
  apply integral_congr_ae
  filter_upwards with x
  change star (f.1.1.1.1 (x+-h))*f.1.1.1.1 x=
    f.1.1.1.1 x*conj (f.1.1.1.1 (-(h-x)))
  rw [neg_sub,sub_eq_add_neg,mul_comm]
  rfl

theorem sourceEnergy_interiorCCMSource {a : SuzukiPositiveAperture}
    (f : InteriorWindowedSmoothOddTestFn a) :
    ccmRestrictedWeilSourceQuadratic a (interiorCCMSource f).toCCMFormVector=
      nativeProfileEnergy (EF.weilTest f.1.1.1.1 f.1.1.1.1) := by
  rw [ccmRestrictedWeilSource_complexSmooth_eq_zetaWeil]
  change (zetaZeroConfig.W f.1.1.1.1 f.1.1.1.1).re=_
  rw [zeta_W_eq_weilFullFunctional f.1.1.1.2.1 f.1.1.1.2.2]
  rfl

theorem odd_interiorCCMSource {a : SuzukiPositiveAperture}
    (f : InteriorWindowedSmoothOddTestFn a) :
    ccmArchimedeanFormReflection a (interiorCCMSource f).toCCMFormVector=
      -(interiorCCMSource f).toCCMFormVector := by
  apply ccmArchimedeanFormToAperture_injective a
  apply Subtype.ext
  rw [ccmArchimedeanFormToAperture_reflection,map_neg,Submodule.coe_neg]
  apply Lp.ext
  have hf := (interiorCCMSource f).toCCMFormVector_physical_coeFn
  have hneg := hf.comp_tendsto
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.tendsto_ae
  filter_upwards [l2Reflection_ae _,hf,hneg,Lp.coeFn_neg
    (ccmArchimedeanFormToAperture a (interiorCCMSource f).toCCMFormVector).1]
    with x hr hx hn hm
  dsimp only [Function.comp_apply] at hn
  rw [hr,hn,hm,Pi.neg_apply,hx]
  exact f.1.1.2 x

/-- Actual finite mixtures, normalized and budgeted through their full profile. -/
def nativeEnergyProfiles (a : SuzukiPositiveAperture) (B : ℝ) : Set (ℝ → ℂ) :=
  {P | ∃ (N : ℕ) (F : Fin N → InteriorWindowedSmoothOddTestFn a) (c : Fin N → ℝ≥0),
    oddMixtureProfile (fun i => (F i).1) c=P ∧ P 0=1 ∧ nativeProfileEnergy P≤B}

theorem nativeEnergyProfiles_subset_completed (a : SuzukiPositiveAperture) (B : ℝ) :
    nativeEnergyProfiles a B ⊆ completedEnergyProfiles a B := by
  rintro P ⟨N,F,c,hc,hmass,hbudget⟩
  obtain ⟨f,hf⟩ := exists_interior_window_purification a F c
  have hP : EF.weilTest f.1.1.1.1 f.1.1.1.1=P := hf.trans hc
  rw [mem_completedEnergyProfiles_iff]
  refine ⟨(interiorCCMSource f).toCCMFormVector,odd_interiorCCMSource f,
    ?_,?_,(energyProfile_interiorCCMSource f).trans hP⟩
  · have h := congrFun ((energyProfile_interiorCCMSource f).trans hP) 0
    rw [energyProfile_zero,hmass] at h
    have hs : ‖ccmArchimedeanFormToAperture a (interiorCCMSource f).toCCMFormVector‖^2=1 :=
      by exact_mod_cast h
    nlinarith [norm_nonneg (ccmArchimedeanFormToAperture a (interiorCCMSource f).toCCMFormVector)]
  · rwa [sourceEnergy_interiorCCMSource,hP]

/-- **Odd purification survives completion.** Every pointwise limit of
normalized energy-budgeted positive odd mixtures has a single actual odd
form-domain source at the same aperture and within the same energy budget. -/
theorem closure_nativeEnergyProfiles_subset_completed (a : SuzukiPositiveAperture) (B : ℝ) :
    closure (nativeEnergyProfiles a B) ⊆ completedEnergyProfiles a B :=
  closure_minimal (nativeEnergyProfiles_subset_completed a B)
    (isClosed_completedEnergyProfiles a B)

/-- There is no loss of mass or aperture in the native odd energy completion. -/
theorem isCompact_closure_nativeEnergyProfiles (a : SuzukiPositiveAperture) (B : ℝ) :
    IsCompact (closure (nativeEnergyProfiles a B)) :=
  (isCompact_completedEnergyProfiles a B).of_isClosed_subset isClosed_closure
    (closure_nativeEnergyProfiles_subset_completed a B)

end RHTower.OddSector
