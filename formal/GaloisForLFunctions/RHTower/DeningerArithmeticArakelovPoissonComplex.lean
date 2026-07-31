import GaloisForLFunctions.RHTower.DeningerArithmeticPoissonZetaAssembly
import GaloisForLFunctions.RHTower.DeningerArithmeticRealArakelovEndpoint

/-!
# Generic Arakelov--Poisson three-term schema

This module inserts the exact finite-plus-archimedean Arakelov endpoint into
the source Poisson--zeta three-term complex.  For an injective source map
`Z : Hcap → Hminus`, the resulting cohomology is

* `H⁰ ≃ R`;
* `H¹ ≃ Hminus / range Z`;
* `H² ≃ R`.

The middle quotient becomes Meyer's source quotient only after `Z` is instantiated by the actual
strict Poisson--zeta map and its required injectivity/intertwining laws are proved.  No such
instantiation is constructed in this module.  No zeta zero, spectral premise, assumed positivity,
or Riemann hypothesis enters the generic definitions or proofs.
-/

namespace RHTower

noncomputable section

section ArakelovPoissonComplex

variable {R Hcap Hminus Places : Type*}
variable [CommRing R]
variable [AddCommGroup Hcap] [Module R Hcap]
variable [AddCommGroup Hminus] [Module R Hminus]

open GaloisForLFunctions.RHTower

/-- Source three-term complex with the exact Arakelov divisor endpoint. -/
def deningerArakelovPoissonComplex
    (Z : Hcap →ₗ[R] Hminus)
    (weight : Places → R) :
    DeningerArithmeticThreeTermComplex
      R (R × Hcap) (Hminus × (Places →₀ R)) ((Places →₀ R) × R) :=
  deningerPoissonZetaComplex Z
    (deningerArakelovPrincipalLinear weight)

/-- Injectivity of the source Poisson map leaves the constant line in `H⁰`. -/
def deningerArakelovPoissonH0Equiv
    (Z : Hcap →ₗ[R] Hminus)
    (weight : Places → R)
    (hZ : Function.Injective Z) :
    (deningerArakelovPoissonComplex Z weight).H0 ≃ₗ[R] R :=
  deningerPoissonZetaH0Equiv Z
    (deningerArakelovPrincipalLinear weight) hZ

/-- The concrete middle cohomology is the source Poisson quotient. -/
def deningerArakelovPoissonH1Equiv
    (Z : Hcap →ₗ[R] Hminus)
    (weight : Places → R) :
    (deningerArakelovPoissonComplex Z weight).H1 ≃ₗ[R]
      Hminus ⧸ LinearMap.range Z :=
  deningerPoissonZetaH1Equiv Z
    (deningerArakelovPrincipalLinear weight)
    (deningerArakelovPrincipalLinear_injective weight)

/-- The archimedean degree identifies concrete top cohomology with `R`. -/
def deningerArakelovPoissonH2Equiv
    (Z : Hcap →ₗ[R] Hminus)
    (weight : Places → R) :
    (deningerArakelovPoissonComplex Z weight).H2 ≃ₗ[R] R :=
  (deningerPoissonZetaH2Equiv Z
      (deningerArakelovPrincipalLinear weight)).trans
    ((deningerArakelov_exact_principal_degree weight).linearEquivOfSurjective
      (deningerArakelovDegreeLinear_surjective weight))

/-- Total degree annihilates the concrete principal-divisor differential. -/
theorem deningerArakelovDegree_comp_principal
    (weight : Places → R) :
    (deningerArakelovDegreeLinear weight).comp
        (deningerArakelovPrincipalLinear weight) = 0 := by
  apply LinearMap.ext
  intro d
  simp only [LinearMap.comp_apply, deningerArakelovPrincipalLinear_apply,
    deningerArakelovDegreeLinear_apply,
    deningerArakelovDegree_principal, LinearMap.zero_apply]

/--
Arakelov degree and a skew source pairing assemble to the concrete
chain-level cup pairing.
-/
def deningerArakelovPoissonCupPairing
    (Z : Hcap →ₗ[R] Hminus)
    (weight : Places → R)
    (psi : Hminus →ₗ[R] Hminus →ₗ[R] R)
    (hpsiBoundary : ∀ f h, psi (Z f) h = 0)
    (hpsiSkew : ∀ h k, psi h k = -psi k h) :
    DeningerArithmeticThreeTermCupPairing
      (deningerArakelovPoissonComplex Z weight) :=
  deningerPoissonZetaCupPairing Z
    (deningerArakelovPrincipalLinear weight)
    (deningerArakelovDegreeLinear weight)
    psi
    (deningerArakelovDegree_comp_principal weight)
    hpsiBoundary
    hpsiSkew

/--
Concrete transverse flow with trivial action on constants and
weight-one identity action on the contractible Arakelov endpoint.
-/
def deningerArakelovPoissonFlow
    (Z : Hcap →ₗ[R] Hminus)
    (weight : Places → R)
    (thetaCap : Module.End R Hcap)
    (thetaMinus : Module.End R Hminus)
    (hZ : Z.comp thetaCap = thetaMinus.comp Z) :
    DeningerArithmeticThreeTermFlow
      R (R × Hcap) (Hminus × (Places →₀ R))
        ((Places →₀ R) × R) :=
  deningerPoissonZetaFlow Z
    (deningerArakelovPrincipalLinear weight)
    thetaCap thetaMinus
    (LinearMap.id (R := R) (M := Places →₀ R))
    (LinearMap.id (R := R) (M := (Places →₀ R) × R))
    hZ
    (by
      apply LinearMap.ext
      intro d
      rfl)

/-- Injectivity of the source map makes the concrete `H⁰` generator zero. -/
theorem deningerArakelovPoisson_thetaH0_eq_zero
    (Z : Hcap →ₗ[R] Hminus)
    (weight : Places → R)
    (thetaCap : Module.End R Hcap)
    (thetaMinus : Module.End R Hminus)
    (hZ : Z.comp thetaCap = thetaMinus.comp Z)
    (hZ_injective : Function.Injective Z) :
    (deningerArakelovPoissonFlow
      Z weight thetaCap thetaMinus hZ).thetaH0 = 0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  have hx :
      (x : R × Hcap).2 = 0 :=
    (deningerPoissonZeta_mem_cycles0_iff Z
      (deningerArakelovPrincipalLinear weight)
      hZ_injective (x : R × Hcap)).1 x.2
  change ((0 : R), thetaCap (x : R × Hcap).2) = 0
  rw [hx, map_zero]
  rfl

/-- The concrete top cohomological generator is the weight-one identity. -/
theorem deningerArakelovPoisson_thetaH2_eq_id
    (Z : Hcap →ₗ[R] Hminus)
    (weight : Places → R)
    (thetaCap : Module.End R Hcap)
    (thetaMinus : Module.End R Hminus)
    (hZ : Z.comp thetaCap = thetaMinus.comp Z) :
    (deningerArakelovPoissonFlow
      Z weight thetaCap thetaMinus hZ).thetaH2 =
        LinearMap.id := by
  apply LinearMap.ext
  intro q
  obtain ⟨d, rfl⟩ :=
    Submodule.Quotient.mk_surjective
      (deningerArakelovPoissonComplex Z weight).boundaries2 q
  rfl

/--
The concrete Arakelov endpoint and a source alternating pairing obey
the weight-one cup law.
-/
theorem deningerArakelovPoissonWeightOneCup
    (Z : Hcap →ₗ[R] Hminus)
    (weight : Places → R)
    (psi : Hminus →ₗ[R] Hminus →ₗ[R] R)
    (hpsiBoundary : ∀ f h, psi (Z f) h = 0)
    (hpsiSkew : ∀ h k, psi h k = -psi k h)
    (thetaCap : Module.End R Hcap)
    (thetaMinus : Module.End R Hminus)
    (hZ : Z.comp thetaCap = thetaMinus.comp Z)
    (hpsiTheta :
      ∀ h k,
        psi (thetaMinus h) k + psi h (thetaMinus k) =
          psi h k) :
    DeningerArithmeticThreeTermWeightOneCup
      (deningerArakelovPoissonFlow
        Z weight thetaCap thetaMinus hZ)
      (deningerArakelovPoissonCupPairing
        Z weight psi hpsiBoundary hpsiSkew) :=
  deningerPoissonZetaWeightOneCup Z
    (deningerArakelovPrincipalLinear weight)
    (deningerArakelovDegreeLinear weight)
    psi
    (deningerArakelovDegree_comp_principal weight)
    hpsiBoundary hpsiSkew
    thetaCap thetaMinus
    (LinearMap.id (R := R) (M := Places →₀ R))
    (LinearMap.id (R := R) (M := (Places →₀ R) × R))
    hZ
    (by
      apply LinearMap.ext
      intro d
      rfl)
    (by
      apply LinearMap.ext
      intro d
      rfl)
    hpsiTheta

end ArakelovPoissonComplex

end

end RHTower
