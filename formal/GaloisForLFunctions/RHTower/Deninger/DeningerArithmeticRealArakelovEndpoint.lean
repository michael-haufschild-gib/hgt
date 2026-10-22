import Mathlib.Data.Finsupp.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Algebra.Exact.Basic

/-!
# Algebraic graph model for a real Arakelov endpoint

The finite divisor coordinates are a finitely supported family and the archimedean coordinate
records the negative weighted sum.  Here the “principal” map is the graph embedding
`d ↦ (d, -weight d)` from the finite-divisor module itself.  This file proves that generic
algebraic graph model is exact; it does not construct the actual principal-divisor map from
arithmetic units or functions.
-/

namespace GaloisForLFunctions.RHTower

section ArakelovEndpoint

variable {P R : Type*} [CommRing R]

/-- Weighted degree of a finitely supported finite-place divisor. -/
def deningerFiniteDivisorWeight
    (weight : P → R) (d : P →₀ R) : R :=
  d.sum fun p c => c * weight p

/-- Principal Arakelov divisor: finite coordinates plus compensating
archimedean coordinate. -/
def deningerArakelovPrincipal
    (weight : P → R) (d : P →₀ R) : (P →₀ R) × R :=
  (d, -deningerFiniteDivisorWeight weight d)

/-- Total Arakelov degree. -/
def deningerArakelovDegree
    (weight : P → R) (x : (P →₀ R) × R) : R :=
  deningerFiniteDivisorWeight weight x.1 + x.2

/-- Every principal Arakelov divisor has degree zero. -/
theorem deningerArakelovDegree_principal
    (weight : P → R) (d : P →₀ R) :
    deningerArakelovDegree weight
      (deningerArakelovPrincipal weight d) = 0 := by
  simp [deningerArakelovDegree, deningerArakelovPrincipal]

/-- Finite coordinates make the principal-divisor map injective. -/
theorem deningerArakelovPrincipal_injective
    (weight : P → R) :
    Function.Injective (deningerArakelovPrincipal weight) := by
  intro d e h
  exact congrArg Prod.fst h

/-- Principal divisors are exactly the kernel of Arakelov degree. -/
theorem deningerArakelovDegree_eq_zero_iff
    (weight : P → R) (x : (P →₀ R) × R) :
    deningerArakelovDegree weight x = 0 ↔
      ∃ d : P →₀ R, deningerArakelovPrincipal weight d = x := by
  constructor
  · intro h
    refine ⟨x.1, ?_⟩
    apply Prod.ext
    · rfl
    · exact neg_eq_iff_add_eq_zero.mpr h
  · rintro ⟨d, rfl⟩
    exact deningerArakelovDegree_principal weight d

/-- The archimedean coordinate makes total degree surjective. -/
theorem deningerArakelovDegree_surjective
    (weight : P → R) :
    Function.Surjective (deningerArakelovDegree weight) := by
  intro r
  refine ⟨(0, r), ?_⟩
  simp [deningerArakelovDegree, deningerFiniteDivisorWeight]

/-- Weighted finite-divisor degree as a linear map. -/
noncomputable def deningerFiniteDivisorWeightLinear
    (weight : P → R) : (P →₀ R) →ₗ[R] R :=
  Finsupp.linearCombination R weight

@[simp]
theorem deningerFiniteDivisorWeightLinear_apply
    (weight : P → R) (d : P →₀ R) :
    deningerFiniteDivisorWeightLinear weight d =
      deningerFiniteDivisorWeight weight d := by
  rfl

/-- Principal Arakelov divisor as a linear map. -/
noncomputable def deningerArakelovPrincipalLinear
    (weight : P → R) :
    (P →₀ R) →ₗ[R] ((P →₀ R) × R) :=
  (LinearMap.id (R := R) (M := P →₀ R)).prod
    (-deningerFiniteDivisorWeightLinear weight)

/-- Total Arakelov degree as a linear map. -/
noncomputable def deningerArakelovDegreeLinear
    (weight : P → R) :
    ((P →₀ R) × R) →ₗ[R] R :=
  (deningerFiniteDivisorWeightLinear weight).comp
      (LinearMap.fst R (P →₀ R) R) +
    LinearMap.snd R (P →₀ R) R

@[simp]
theorem deningerArakelovPrincipalLinear_apply
    (weight : P → R) (d : P →₀ R) :
    deningerArakelovPrincipalLinear weight d =
      deningerArakelovPrincipal weight d :=
  rfl

@[simp]
theorem deningerArakelovDegreeLinear_apply
    (weight : P → R) (x : (P →₀ R) × R) :
    deningerArakelovDegreeLinear weight x =
      deningerArakelovDegree weight x :=
  rfl

/-- Linear principal divisor map is injective. -/
theorem deningerArakelovPrincipalLinear_injective
    (weight : P → R) :
    Function.Injective (deningerArakelovPrincipalLinear weight) :=
  deningerArakelovPrincipal_injective weight

/-- Linear Arakelov degree is surjective. -/
theorem deningerArakelovDegreeLinear_surjective
    (weight : P → R) :
    Function.Surjective (deningerArakelovDegreeLinear weight) :=
  deningerArakelovDegree_surjective weight

/-- Principal divisors and total Arakelov degree form an exact pair. -/
theorem deningerArakelov_exact_principal_degree
    (weight : P → R) :
    Function.Exact
      (deningerArakelovPrincipalLinear weight)
      (deningerArakelovDegreeLinear weight) := by
  intro x
  constructor
  · intro hx
    change deningerArakelovDegree weight x = 0 at hx
    obtain ⟨d, hd⟩ :=
      (deningerArakelovDegree_eq_zero_iff weight x).1 hx
    exact ⟨d, hd⟩
  · rintro ⟨d, rfl⟩
    change deningerArakelovDegree weight
      (deningerArakelovPrincipal weight d) = 0
    exact deningerArakelovDegree_principal weight d

end ArakelovEndpoint

end GaloisForLFunctions.RHTower
