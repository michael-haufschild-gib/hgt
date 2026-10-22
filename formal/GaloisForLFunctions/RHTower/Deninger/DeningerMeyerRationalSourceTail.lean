import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerArithmeticPacketDivision

/-!
# Unique division at every complex parameter after finite causal modes

Finite spectral support is detected inside actual arithmetic Meyer cohomology.
A shifted source can have finite support only if the source itself does. Thus
quotienting by all original finite causal modes removes every finite resonance,
without annihilating the projected Gaussian. All shifted generators on this
nonzero quotient are bijective, including at Xi zeros.
-/

open scoped Classical

namespace RHTower
noncomputable section

local notation "Q" => DeningerMeyerStrongLogCohomology
local notation "V" => DeningerMeyerArithmeticSource
local notation "A" => deningerMeyerArithmeticSourceGenerator

def DeningerMeyerArithmeticFiniteModes : Submodule ℂ V :=
  DeningerMeyerFiniteCausalModes.comap (V).subtype

local notation "F" => DeningerMeyerArithmeticFiniteModes

theorem deningerMeyerArithmeticFiniteModes_generator (u : V) (hu : u ∈ F) : A u ∈ F :=
  deningerMeyerFiniteCausalModes_generator_mem ⟨u, hu⟩

theorem deningerMeyerArithmeticFiniteProjector_mem_finite (S : Finset XiDivisorSupport) (u : V) :
    deningerMeyerArithmeticFiniteProjector S u ∈ F :=
  deningerMeyerFiniteXiCausalProjector_mem_finite S u

theorem deningerMeyerFiniteCausalModes_finite_jet_support (u : Q)
    (hu : u ∈ DeningerMeyerFiniteCausalModes) :
    ∃ S : Finset XiDivisorSupport, ∀ rho ∉ S, ∀ j,
      deningerMeyerXiSupportJetEvaluationLM rho j u = 0 := by
  obtain ⟨S, c, rfl⟩ := hu
  refine ⟨S, fun rho hrho j => ?_⟩
  rw [← deningerMeyerFiniteXiCausalProjector_synthesis S c]
  exact deningerMeyerFiniteXiCausalSection_other_jet_zero S rho hrho j _

/-- In the actual arithmetic source, finite jet support is an actual finite
causal source, not just an equality in the comparison recipient. -/
theorem deningerMeyerArithmeticSource_mem_finite_of_jet_support
    (S : Finset XiDivisorSupport) (u : V)
    (hu : ∀ rho ∉ S, ∀ j, deningerMeyerXiSupportJetEvaluationLM rho j u = 0) : u ∈ F := by
  have hzero : u - deningerMeyerArithmeticFiniteProjector S u = 0 := by
    apply deningerMeyerArithmeticSource_eq_zero
    apply (mem_deningerMeyerInvisible_iff _).mpr
    intro rho j
    change deningerMeyerXiSupportJetEvaluationLM rho j
      ((u : Q) - deningerMeyerFiniteXiCausalProjector S u) = 0
    rw [map_sub]
    by_cases hrho : rho ∈ S
    · have h := congrFun (deningerMeyerFiniteXiCausalProjector_jets S u) ⟨⟨rho, hrho⟩, j⟩
      change deningerMeyerXiSupportJetEvaluationLM rho j
        (deningerMeyerFiniteXiCausalProjector S u) =
          deningerMeyerXiSupportJetEvaluationLM rho j u at h
      rw [h, sub_self]
    · rw [hu rho hrho j]
      change 0 - deningerMeyerXiSupportJetEvaluationLM rho j
        (deningerMeyerFiniteXiCausalSection S _) = 0
      rw [deningerMeyerFiniteXiCausalSection_other_jet_zero S rho hrho, sub_zero]
  rw [sub_eq_zero.mp hzero]
  exact deningerMeyerArithmeticFiniteProjector_mem_finite S u

/-- A shift cannot hide an infinite source tail inside a finite causal packet. -/
theorem deningerMeyerArithmetic_shift_mem_finite_iff (rho : ℂ) (u : V) :
    A u - rho • u ∈ F ↔ u ∈ F := by
  constructor
  · intro hu
    obtain ⟨S, hS⟩ := deningerMeyerFiniteCausalModes_finite_jet_support
      ((A u - rho • u : V) : Q) hu
    apply deningerMeyerArithmeticSource_mem_finite_of_jet_support
      (S ∪ deningerMeyerWordXiSupport [rho]) u
    intro tau htau j
    have hnotS : tau ∉ S := fun h => htau (Finset.mem_union_left _ h)
    have hne : (tau : ℂ) ≠ rho := by
      intro h
      apply htau
      apply Finset.mem_union_right
      exact (mem_deningerMeyerWordXiSupport [rho] tau).mpr (List.mem_cons.mpr (Or.inl h))
    exact deningerMeyerXiJets_zero_of_shift tau rho hne (u : Q) (hS tau hnotS) j
  · intro hu
    exact (F).sub_mem (deningerMeyerArithmeticFiniteModes_generator u hu) ((F).smul_mem rho hu)

/-- The actual source quotient by all original finite causal modes. -/
abbrev DeningerMeyerRationalSourceTail := V ⧸ F

local notation "T" => DeningerMeyerRationalSourceTail

def deningerMeyerRationalTailGenerator : Module.End ℂ T :=
  (F).mapQ F A deningerMeyerArithmeticFiniteModes_generator

@[simp]
theorem deningerMeyerRationalTailGenerator_mk (u : V) :
    deningerMeyerRationalTailGenerator (Submodule.Quotient.mk u) =
      Submodule.Quotient.mk (A u) := rfl

def deningerMeyerRationalTailShift (rho : ℂ) : Module.End ℂ T :=
  deningerMeyerRationalTailGenerator - rho • LinearMap.id

/-- Unique division on the non-finite source sector holds at every complex
parameter; there is no remaining Xi exclusion. -/
theorem deningerMeyerRationalTailShift_bijective (rho : ℂ) :
    Function.Bijective (deningerMeyerRationalTailShift rho) := by
  have hzero (q : T) (hq : deningerMeyerRationalTailShift rho q = 0) : q = 0 := by
    induction q using Submodule.Quotient.induction_on with
    | H u =>
      have hmem : A u - rho • u ∈ F := by
        apply (Submodule.Quotient.mk_eq_zero F).mp
        simpa only [deningerMeyerRationalTailShift, LinearMap.sub_apply, LinearMap.smul_apply,
          LinearMap.id_apply, deningerMeyerRationalTailGenerator_mk, Submodule.Quotient.mk_sub,
          Submodule.Quotient.mk_smul] using hq
      exact (Submodule.Quotient.mk_eq_zero F).mpr
        ((deningerMeyerArithmetic_shift_mem_finite_iff rho u).mp hmem)
  constructor
  · intro u v huv
    apply sub_eq_zero.mp
    apply hzero
    rw [map_sub, huv, sub_self]
  · intro q
    induction q using Submodule.Quotient.induction_on with
    | H u =>
      refine ⟨Submodule.Quotient.mk (deningerMeyerArithmeticWordDivision [rho] u), ?_⟩
      change (Submodule.Quotient.mk
        (deningerMeyerGeneratorWord A [rho] (deningerMeyerArithmeticWordDivision [rho] u)) : T) =
          Submodule.Quotient.mk u
      rw [deningerMeyerArithmeticWordDivision_right, Submodule.Quotient.mk_sub,
        (Submodule.Quotient.mk_eq_zero F).mpr
          (deningerMeyerArithmeticFiniteProjector_mem_finite (deningerMeyerWordXiSupport [rho]) u),
        sub_zero]

def deningerMeyerRationalTailResolvent (rho : ℂ) : T ≃ₗ[ℂ] T :=
  (LinearEquiv.ofBijective (deningerMeyerRationalTailShift rho)
    (deningerMeyerRationalTailShift_bijective rho)).symm

theorem deningerMeyerRationalTailResolvent_equation (rho : ℂ) (u : T) :
    deningerMeyerRationalTailGenerator (deningerMeyerRationalTailResolvent rho u) -
      rho • deningerMeyerRationalTailResolvent rho u = u :=
  (deningerMeyerRationalTailResolvent rho).symm_apply_apply u

/-- Every tail division is represented by the canonical finite-defect division
in actual arithmetic Meyer cohomology. -/
theorem deningerMeyerRationalTailResolvent_source (rho : ℂ) (u : V) :
    deningerMeyerRationalTailResolvent rho (Submodule.Quotient.mk u) =
      Submodule.Quotient.mk (deningerMeyerArithmeticWordDivision [rho] u) := by
  apply (deningerMeyerRationalTailShift_bijective rho).1
  change (deningerMeyerRationalTailResolvent rho).symm
      (deningerMeyerRationalTailResolvent rho (Submodule.Quotient.mk u)) = _
  rw [(deningerMeyerRationalTailResolvent rho).symm_apply_apply]
  change (Submodule.Quotient.mk u : T) = Submodule.Quotient.mk
    (deningerMeyerGeneratorWord A [rho] (deningerMeyerArithmeticWordDivision [rho] u))
  rw [deningerMeyerArithmeticWordDivision_right, Submodule.Quotient.mk_sub,
    (Submodule.Quotient.mk_eq_zero F).mpr
      (deningerMeyerArithmeticFiniteProjector_mem_finite (deningerMeyerWordXiSupport [rho]) u),
    sub_zero]

def deningerMeyerRationalTailGaussian : T := Submodule.Quotient.mk
  (⟨deningerMeyerArithmeticCausalProjector deningerMeyerLogGaussianCohomologyClass,
    deningerMeyerLogGaussianCohomologyClass, rfl⟩ : V)

theorem deningerMeyerRationalTailGaussian_ne_zero : deningerMeyerRationalTailGaussian ≠ 0 := by
  intro h
  exact deningerMeyerArithmeticCausalProjector_gaussian_not_finite
    ((Submodule.Quotient.mk_eq_zero F).mp h)

instance : Nontrivial T := ⟨⟨deningerMeyerRationalTailGaussian, 0,
  deningerMeyerRationalTailGaussian_ne_zero⟩⟩

end
end RHTower
