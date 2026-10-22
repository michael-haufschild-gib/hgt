import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerGlobalCausalSplitting
import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerLogGaussianUniversalOrbitCriterion
import GaloisForLFunctions.RHTower.XiZerosInfinite

/-!
# A faithful global observable space inside actual Meyer cohomology

The global causal projector supplies an invariant actual source subspace on
which comparison is an isomorphism onto its whole image. All observable
endomorphisms lift faithfully and preserve composition, with no finite-support
restriction. Existing finite causal lifts are recovered exactly. The projected
log-Gaussian proves that this space is strictly larger than the union of finite
causal packets. All constructions are algebraic; continuity is not asserted.
-/

namespace RHTower
noncomputable section

/-- A global subspace of literal Meyer cohomology, rather than an entire proxy. -/
def DeningerMeyerObservableSource : Submodule ℂ DeningerMeyerStrongLogCohomology :=
  LinearMap.range deningerMeyerGlobalCausalProjector

/-- The whole actual comparison image, with no finite-packet restriction. -/
def DeningerMeyerObservableImage : Submodule ℂ DeningerArithmeticCompactOpenH1 :=
  LinearMap.range deningerMeyerCompactOpenXiComparison

def deningerMeyerObservation :
    DeningerMeyerStrongLogCohomology →ₗ[ℂ] DeningerMeyerObservableImage :=
  deningerMeyerCompactOpenXiComparison.rangeRestrict

theorem deningerMeyerObservableSource_fixed (u : DeningerMeyerObservableSource) :
    deningerMeyerGlobalCausalProjector u = u := by
  obtain ⟨v, hv⟩ := u.property
  rw [← hv, deningerMeyerGlobalCausalProjector_idempotent]

theorem deningerMeyerObservableSource_generator_mem (u : DeningerMeyerObservableSource) :
    deningerMeyerCohomologyGenerator u ∈ DeningerMeyerObservableSource := by
  refine ⟨deningerMeyerCohomologyGenerator u, ?_⟩
  rw [deningerMeyerGlobalCausalProjector_generator, deningerMeyerObservableSource_fixed]

def deningerMeyerObservableSourceGenerator : Module.End ℂ DeningerMeyerObservableSource :=
  deningerMeyerCohomologyGenerator.restrict
    (fun u hu => deningerMeyerObservableSource_generator_mem ⟨u, hu⟩)

/-- Invisible classes have zero intersection with the actual observable source space. -/
theorem deningerMeyerObservableSource_eq_zero
    (u : DeningerMeyerObservableSource) (hu : (u : DeningerMeyerStrongLogCohomology) ∈
      DeningerMeyerInvisible) : u = 0 := by
  apply Subtype.ext
  rw [← deningerMeyerObservableSource_fixed u]
  exact deningerMeyerGlobalCausalProjector_invisible ⟨u, hu⟩

def deningerMeyerObservableSourceComparison :
    DeningerMeyerObservableSource →ₗ[ℂ] DeningerMeyerObservableImage :=
  deningerMeyerObservation.comp DeningerMeyerObservableSource.subtype

theorem deningerMeyerObservableSourceComparison_bijective :
    Function.Bijective deningerMeyerObservableSourceComparison := by
  constructor
  · intro u v huv
    have hE : deningerMeyerCompactOpenXiComparison
        ((u : DeningerMeyerStrongLogCohomology) - v) = 0 := by
      rw [map_sub]
      exact sub_eq_zero.mpr (congrArg Subtype.val huv)
    exact sub_eq_zero.mp (deningerMeyerObservableSource_eq_zero (u - v) hE)
  · intro c
    obtain ⟨u, hu⟩ := c.property
    refine ⟨⟨deningerMeyerGlobalCausalProjector u, u, rfl⟩, ?_⟩
    apply Subtype.ext
    exact (deningerMeyerGlobalCausalProjector_comparison u).trans hu

/-- Comparison has an actual invariant global source model, unconditionally. -/
def deningerMeyerObservableSourceEquiv :
    DeningerMeyerObservableSource ≃ₗ[ℂ] DeningerMeyerObservableImage :=
  LinearEquiv.ofBijective deningerMeyerObservableSourceComparison
    deningerMeyerObservableSourceComparison_bijective

/-- One simultaneous section on the whole actual comparison image. -/
def deningerMeyerGlobalObservableSection :
    DeningerMeyerObservableImage →ₗ[ℂ] DeningerMeyerStrongLogCohomology :=
  DeningerMeyerObservableSource.subtype.comp
    deningerMeyerObservableSourceEquiv.symm.toLinearMap

@[simp]
theorem deningerMeyerGlobalObservableSection_observation (c : DeningerMeyerObservableImage) :
    deningerMeyerObservation (deningerMeyerGlobalObservableSection c) = c :=
  deningerMeyerObservableSourceEquiv.apply_symm_apply c

theorem deningerMeyerGlobalObservableSection_source (u : DeningerMeyerStrongLogCohomology) :
    deningerMeyerGlobalObservableSection (deningerMeyerObservation u) =
      deningerMeyerGlobalCausalProjector u := by
  have h : deningerMeyerObservableSourceEquiv.symm (deningerMeyerObservation u) =
      (⟨deningerMeyerGlobalCausalProjector u, u, rfl⟩ : DeningerMeyerObservableSource) := by
    apply deningerMeyerObservableSourceEquiv.injective
    rw [LinearEquiv.apply_symm_apply]
    apply Subtype.ext
    exact (deningerMeyerGlobalCausalProjector_comparison u).symm
  exact congrArg Subtype.val h

def deningerMeyerObservableImageGenerator : Module.End ℂ DeningerMeyerObservableImage :=
  deningerMeyerObservation.comp
    (deningerMeyerCohomologyGenerator.comp deningerMeyerGlobalObservableSection)

theorem deningerMeyerGlobalObservableSection_generator (c : DeningerMeyerObservableImage) :
    deningerMeyerCohomologyGenerator (deningerMeyerGlobalObservableSection c) =
      deningerMeyerGlobalObservableSection (deningerMeyerObservableImageGenerator c) := by
  change deningerMeyerCohomologyGenerator (deningerMeyerGlobalObservableSection c) =
    deningerMeyerGlobalObservableSection (deningerMeyerObservation
      (deningerMeyerCohomologyGenerator (deningerMeyerGlobalObservableSection c)))
  rw [deningerMeyerGlobalObservableSection_source,
    deningerMeyerGlobalCausalProjector_generator]
  exact congrArg deningerMeyerCohomologyGenerator
    (deningerMeyerObservableSource_fixed (deningerMeyerObservableSourceEquiv.symm c)).symm

theorem deningerMeyerObservableImageGenerator_observation
    (u : DeningerMeyerStrongLogCohomology) :
    deningerMeyerObservableImageGenerator (deningerMeyerObservation u) =
      deningerMeyerObservation (deningerMeyerCohomologyGenerator u) := by
  change deningerMeyerObservation (deningerMeyerCohomologyGenerator
    (deningerMeyerGlobalObservableSection (deningerMeyerObservation u))) = _
  rw [deningerMeyerGlobalObservableSection_source,
    ← deningerMeyerGlobalCausalProjector_generator]
  apply Subtype.ext
  exact deningerMeyerGlobalCausalProjector_comparison _

/-- Every global observable operator has a faithful actual-source realization. -/
def deningerMeyerGlobalObservableOperatorLift
    (B : Module.End ℂ DeningerMeyerObservableImage) :
    Module.End ℂ DeningerMeyerStrongLogCohomology :=
  deningerMeyerGlobalObservableSection.comp (B.comp deningerMeyerObservation)

theorem deningerMeyerGlobalObservableOperatorLift_comp
    (B C : Module.End ℂ DeningerMeyerObservableImage) :
    (deningerMeyerGlobalObservableOperatorLift B).comp
        (deningerMeyerGlobalObservableOperatorLift C) =
      deningerMeyerGlobalObservableOperatorLift (B.comp C) := by
  apply LinearMap.ext
  intro u
  change deningerMeyerGlobalObservableSection
    (B (deningerMeyerObservation (deningerMeyerGlobalObservableSection
      (C (deningerMeyerObservation u))))) = _
  rw [deningerMeyerGlobalObservableSection_observation]
  rfl

theorem deningerMeyerGlobalObservableOperatorLift_faithful :
    Function.Injective deningerMeyerGlobalObservableOperatorLift := by
  intro B C h
  apply LinearMap.ext
  intro c
  have he := congrArg (fun F : Module.End ℂ DeningerMeyerStrongLogCohomology =>
    deningerMeyerObservation (F (deningerMeyerGlobalObservableSection c))) h
  simpa only [deningerMeyerGlobalObservableOperatorLift, LinearMap.comp_apply,
    deningerMeyerGlobalObservableSection_observation] using he

/-- The whole endomorphism algebra, now acting on an actual invariant source subspace. -/
def deningerMeyerGlobalObservableEndEquiv :
    Module.End ℂ DeningerMeyerObservableImage ≃ₐ[ℂ]
      Module.End ℂ DeningerMeyerObservableSource :=
  deningerMeyerObservableSourceEquiv.symm.conjAlgEquiv ℂ

/-- Commutator defects are preserved exactly, so commuting observable operators
lift without any new generator-compatibility hypothesis. -/
theorem deningerMeyerGlobalObservableOperatorLift_commutator
    (B : Module.End ℂ DeningerMeyerObservableImage) :
    deningerMeyerCohomologyGenerator.comp (deningerMeyerGlobalObservableOperatorLift B) -
        (deningerMeyerGlobalObservableOperatorLift B).comp deningerMeyerCohomologyGenerator =
      deningerMeyerGlobalObservableOperatorLift
        (deningerMeyerObservableImageGenerator.comp B - B.comp deningerMeyerObservableImageGenerator) := by
  apply LinearMap.ext
  intro u
  simp only [deningerMeyerGlobalObservableOperatorLift, LinearMap.sub_apply,
    LinearMap.comp_apply, map_sub, deningerMeyerGlobalObservableSection_generator,
    deningerMeyerObservableImageGenerator_observation]

/-- The global construction reproduces every pre-existing finite causal operator. -/
theorem deningerMeyerGlobalObservableOperatorLift_finite
    (S : Finset XiDivisorSupport) (B : Module.End ℂ (DeningerMeyerFiniteXiJetPacket S)) :
    deningerMeyerGlobalObservableOperatorLift
      (deningerMeyerObservation.comp
        ((deningerMeyerFiniteXiOperatorLift S B).comp deningerMeyerGlobalObservableSection)) =
      deningerMeyerFiniteXiOperatorLift S B := by
  apply LinearMap.ext
  intro u
  change deningerMeyerGlobalObservableSection (deningerMeyerObservation
    (deningerMeyerFiniteXiOperatorLift S B
      (deningerMeyerGlobalObservableSection (deningerMeyerObservation u)))) = _
  rw [deningerMeyerGlobalObservableSection_source, deningerMeyerGlobalObservableSection_source]
  have hleft (v : DeningerMeyerStrongLogCohomology) :
      deningerMeyerGlobalCausalProjector (deningerMeyerFiniteXiOperatorLift S B v) =
        deningerMeyerFiniteXiOperatorLift S B v :=
    deningerMeyerGlobalCausalProjector_synthesis S _
  rw [hleft]
  have hE : deningerMeyerFiniteXiJetPacketLM S (deningerMeyerGlobalCausalProjector u) =
      deningerMeyerFiniteXiJetPacketLM S u := by
    funext q
    exact deningerMeyerGlobalCausalProjector_jets u q.1.1 q.2
  exact congrArg (fun c => deningerMeyerFiniteXiCausalSection S (B c)) hE

/-- The new actual source space is not exhausted by finite spectral packets. -/
theorem deningerMeyerGlobalCausalProjector_gaussian_not_finite :
    deningerMeyerGlobalCausalProjector deningerMeyerLogGaussianCohomologyClass ∉
      DeningerMeyerFiniteCausalModes := by
  rintro ⟨S, c, hc⟩
  letI : Infinite XiDivisorSupport := Set.infinite_coe_iff.mpr xiDivisorSupport_infinite
  obtain ⟨rho, hrho⟩ := Infinite.exists_notMem_finset S
  apply deningerMeyerLogGaussianCohomologyClass_evaluation_ne_zero rho
  rw [← deningerMeyerGlobalCausalProjector_jets deningerMeyerLogGaussianCohomologyClass,
    ← hc, ← deningerMeyerFiniteXiCausalProjector_synthesis S c]
  exact deningerMeyerFiniteXiCausalSection_other_jet_zero S rho hrho _ _

end
end RHTower
