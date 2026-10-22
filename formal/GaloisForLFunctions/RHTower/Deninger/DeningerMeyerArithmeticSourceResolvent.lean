import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerArithmeticSymmetricSplitting

/-!
# Exact global resolvents respecting the original arithmetic symmetries

The symmetric complement is an actual subspace of Meyer cohomology.  Its
generator has the exact Xi spectrum, and its resolvents intertwine the original
reflection and conjugation.  Thus symmetry-compatible division is available
simultaneously on the whole comparison image, including non-finite sources.
-/

namespace RHTower
noncomputable section

local notation "Q" => DeningerMeyerStrongLogCohomology
local notation "A" => deningerMeyerCohomologyGenerator
local notation "J" => deningerMeyerStrongLogCohomologyJ
local notation "C" => deningerMeyerCohomologyConj
local notation "P" => deningerMeyerArithmeticCausalProjector

/-- The arithmetic-symmetric complement inside literal Meyer cohomology. -/
def DeningerMeyerArithmeticSource : Submodule ℂ Q := LinearMap.range P

local notation "V" => DeningerMeyerArithmeticSource

theorem deningerMeyerArithmeticSource_fixed (u : V) : P u = u := by
  obtain ⟨v, hv⟩ := u.property
  rw [← hv, deningerMeyerArithmeticCausalProjector_idempotent]

theorem deningerMeyerArithmeticSource_generator_mem (u : V) : A u ∈ V := by
  refine ⟨A u, ?_⟩
  rw [deningerMeyerArithmeticCausalProjector_generator, deningerMeyerArithmeticSource_fixed]

theorem deningerMeyerArithmeticSource_J_mem (u : V) : J u ∈ V := by
  refine ⟨J u, ?_⟩
  rw [deningerMeyerArithmeticCausalProjector_J, deningerMeyerArithmeticSource_fixed]

theorem deningerMeyerArithmeticSource_conj_mem (u : V) : C u ∈ V := by
  refine ⟨C u, ?_⟩
  rw [deningerMeyerArithmeticCausalProjector_conj, deningerMeyerArithmeticSource_fixed]

def deningerMeyerArithmeticSourceGenerator : Module.End ℂ V :=
  (A).restrict (fun u hu => deningerMeyerArithmeticSource_generator_mem ⟨u, hu⟩)

def deningerMeyerArithmeticSourceJ : Module.End ℂ V :=
  (J).restrict (fun u hu => deningerMeyerArithmeticSource_J_mem ⟨u, hu⟩)

def deningerMeyerArithmeticSourceConj : V →ₗ⋆[ℂ] V :=
  (C).restrict (fun u hu => deningerMeyerArithmeticSource_conj_mem ⟨u, hu⟩)

local notation "Aᵥ" => deningerMeyerArithmeticSourceGenerator
local notation "Jᵥ" => deningerMeyerArithmeticSourceJ
local notation "Cᵥ" => deningerMeyerArithmeticSourceConj

@[simp]
theorem deningerMeyerArithmeticSourceJ_sq (u : V) : Jᵥ (Jᵥ u) = u :=
  Subtype.ext (deningerMeyerStrongLogCohomologyJ_sq u)

@[simp]
theorem deningerMeyerArithmeticSourceConj_sq (u : V) : Cᵥ (Cᵥ u) = u :=
  Subtype.ext (deningerMeyerCohomologyConj_sq u)

theorem deningerMeyerArithmeticSourceGenerator_J (u : V) :
    Aᵥ (Jᵥ u) = Jᵥ u - Jᵥ (Aᵥ u) :=
  Subtype.ext (deningerMeyerCohomologyGenerator_J u)

theorem deningerMeyerArithmeticSourceGenerator_conj (u : V) :
    Aᵥ (Cᵥ u) = Cᵥ (Aᵥ u) :=
  Subtype.ext (deningerMeyerCohomologyGenerator_conj u)

theorem deningerMeyerArithmeticSourceConj_J (u : V) : Cᵥ (Jᵥ u) = Jᵥ (Cᵥ u) :=
  Subtype.ext (deningerMeyerCohomologyConj_J u)

/-- Symmetrization changes the complement but loses no comparison class. -/
def deningerMeyerObservableArithmeticEquiv : DeningerMeyerObservableSource ≃ₗ[ℂ] V where
  toFun u := ⟨P u, u, rfl⟩
  invFun u := ⟨deningerMeyerGlobalCausalProjector u, u, rfl⟩
  map_add' u v := Subtype.ext ((P).map_add u v)
  map_smul' z u := Subtype.ext ((P).map_smul z u)
  left_inv u := Subtype.ext (by
    change deningerMeyerGlobalCausalProjector (P u) = (u : Q)
    rw [deningerMeyerGlobalCausalProjector_absorb_arithmetic, deningerMeyerObservableSource_fixed])
  right_inv u := Subtype.ext (by
    change P (deningerMeyerGlobalCausalProjector u) = (u : Q)
    rw [deningerMeyerArithmeticCausalProjector_absorb_old, deningerMeyerArithmeticSource_fixed])

local notation "E" => deningerMeyerObservableArithmeticEquiv

theorem deningerMeyerObservableArithmeticEquiv_generator (u : DeningerMeyerObservableSource) :
    E (deningerMeyerObservableSourceGenerator u) = Aᵥ (E u) :=
  Subtype.ext (deningerMeyerArithmeticCausalProjector_generator u)

/-- Every actual comparison class has a unique representative in the symmetric complement. -/
def deningerMeyerArithmeticSourceEquiv : V ≃ₗ[ℂ] DeningerMeyerObservableImage :=
  (E).symm.trans deningerMeyerObservableSourceEquiv

theorem deningerMeyerArithmeticSourceEquiv_comparison (u : V) :
    (deningerMeyerArithmeticSourceEquiv u : DeningerArithmeticCompactOpenH1) =
      deningerMeyerCompactOpenXiComparison u := by
  change deningerMeyerCompactOpenXiComparison (deningerMeyerGlobalCausalProjector u) = _
  exact deningerMeyerGlobalCausalProjector_comparison u

/-- Exact Xi spectrum survives imposing the original source symmetries. -/
theorem deningerMeyerArithmeticSource_spectrum :
    spectrum ℂ Aᵥ = {rho : ℂ | xi rho = 0} := by
  have h : (E).conjAlgEquiv ℂ deningerMeyerObservableSourceGenerator = Aᵥ := by
    apply LinearMap.ext
    intro u
    change E (deningerMeyerObservableSourceGenerator ((E).symm u)) = Aᵥ u
    rw [deningerMeyerObservableArithmeticEquiv_generator, (E).apply_symm_apply]
  rw [← h, AlgEquiv.spectrum_eq, deningerMeyerObservableSource_spectrum]

def deningerMeyerArithmeticResolvent (rho : {rho : ℂ // xi rho ≠ 0}) : V ≃ₗ[ℂ] V :=
  (E).symm.trans ((deningerMeyerObservableResolvent rho).trans E)

local notation "R" => deningerMeyerArithmeticResolvent

theorem deningerMeyerArithmeticResolvent_equation
    (rho : {rho : ℂ // xi rho ≠ 0}) (u : V) : Aᵥ (R rho u) - rho.val • R rho u = u := by
  change Aᵥ (E (deningerMeyerObservableResolvent rho ((E).symm u))) -
    rho.val • E (deningerMeyerObservableResolvent rho ((E).symm u)) = u
  rw [← deningerMeyerObservableArithmeticEquiv_generator, ← map_smul, ← map_sub,
    deningerMeyerObservableResolvent_equation, (E).apply_symm_apply]

theorem deningerMeyerArithmeticResolvent_symm_apply
    (rho : {rho : ℂ // xi rho ≠ 0}) (u : V) : (R rho).symm u = Aᵥ u - rho.val • u := by
  have h := deningerMeyerArithmeticResolvent_equation rho ((R rho).symm u)
  rw [(R rho).apply_symm_apply] at h
  exact h.symm

/-- The symmetric divisions form one coherent resolvent family on all actual sources. -/
theorem deningerMeyerArithmeticResolvent_identity
    (rho tau : {rho : ℂ // xi rho ≠ 0}) (u : V) :
    R rho u - R tau u = (rho.val - tau.val) • R rho (R tau u) := by
  change E (deningerMeyerObservableResolvent rho ((E).symm u)) -
      E (deningerMeyerObservableResolvent tau ((E).symm u)) =
    (rho.val - tau.val) • E (deningerMeyerObservableResolvent rho
      ((E).symm (E (deningerMeyerObservableResolvent tau ((E).symm u)))))
  rw [(E).symm_apply_apply, ← map_smul, ← map_sub, deningerMeyerObservableResolvent_identity]

def deningerMeyerRegularReflect (rho : {rho : ℂ // xi rho ≠ 0}) :
    {rho : ℂ // xi rho ≠ 0} := ⟨1 - rho.val, by
      rw [xi_one_sub]
      exact rho.property⟩

def deningerMeyerRegularConj (rho : {rho : ℂ // xi rho ≠ 0}) :
    {rho : ℂ // xi rho ≠ 0} := ⟨(starRingEnd ℂ) rho.val, by
      rw [xi_conj]
      simpa using rho.property⟩

/-- Division at reflected parameters intertwines the original source reflection. -/
theorem deningerMeyerArithmeticResolvent_J
    (rho : {rho : ℂ // xi rho ≠ 0}) (u : V) :
    R (deningerMeyerRegularReflect rho) (Jᵥ u) = -Jᵥ (R rho u) := by
  apply (R (deningerMeyerRegularReflect rho)).symm.injective
  rw [(R (deningerMeyerRegularReflect rho)).symm_apply_apply,
    deningerMeyerArithmeticResolvent_symm_apply, map_neg, smul_neg,
    deningerMeyerArithmeticSourceGenerator_J]
  have h := congrArg Jᵥ (deningerMeyerArithmeticResolvent_equation rho u)
  rw [map_sub, map_smul] at h
  rw [← h]
  change _ = -(Jᵥ (R rho u) - Jᵥ (Aᵥ (R rho u))) -
    -((1 - rho.val) • Jᵥ (R rho u))
  module

/-- Division at conjugate parameters intertwines genuine arithmetic conjugation. -/
theorem deningerMeyerArithmeticResolvent_conj
    (rho : {rho : ℂ // xi rho ≠ 0}) (u : V) :
    R (deningerMeyerRegularConj rho) (Cᵥ u) = Cᵥ (R rho u) := by
  apply (R (deningerMeyerRegularConj rho)).symm.injective
  rw [(R (deningerMeyerRegularConj rho)).symm_apply_apply,
    deningerMeyerArithmeticResolvent_symm_apply, deningerMeyerArithmeticSourceGenerator_conj]
  change Cᵥ u = Cᵥ (Aᵥ (R rho u)) - (starRingEnd ℂ) rho.val • Cᵥ (R rho u)
  rw [← LinearMap.map_smulₛₗ, ← map_sub, deningerMeyerArithmeticResolvent_equation]

/-- The symmetry-compatible model contains sources outside every finite Xi packet. -/
theorem deningerMeyerArithmeticCausalProjector_gaussian_not_finite :
    P deningerMeyerLogGaussianCohomologyClass ∉ DeningerMeyerFiniteCausalModes := by
  intro h
  apply deningerMeyerGlobalCausalProjector_gaussian_not_finite
  have he := deningerMeyerGlobalCausalProjector_finite
    ⟨P deningerMeyerLogGaussianCohomologyClass, h⟩
  rw [deningerMeyerGlobalCausalProjector_absorb_arithmetic] at he
  rw [he]
  exact h

end
end RHTower
