import Mathlib.RepresentationTheory.Invariants
import GaloisForLFunctions.RHTower.DeningerArithmeticThreeTermCohomology

/-!
# Degreewise coarse invariants for Deninger arithmetic cohomology

This module formalizes the algebraic fixed-section core of
`DAC_COARSE_INVARIANT_SHEAF_EXISTENCE`.

An equivariant linear map restricts to invariant submodules.  Consequently an
equivariant three-term complex restricts degreewise to a three-term complex,
and every equivariant transverse generator commuting with its differential
descends to that invariant complex.

The construction is deliberately underived: it introduces no bar complex,
group cohomology, quotient-stack comparison, zeta-zero input, or Riemann
hypothesis premise.
-/

namespace RHTower

open Representation

section InvariantMap

variable {R G A B C : Type*}
variable [CommRing R] [Group G]
variable [AddCommGroup A] [Module R A]
variable [AddCommGroup B] [Module R B]
variable [AddCommGroup C] [Module R C]

/--
An equivariant linear map restricts to the submodules of fixed vectors.
This is the sectionwise algebraic operation used by Deninger's degreewise
coarse invariant sheaf.
-/
def deningerInvariantLinearMap
    (rho : Representation R G A)
    (sigma : Representation R G B)
    (f : A →ₗ[R] B)
    (equivariant : ∀ g x, sigma g (f x) = f (rho g x)) :
    rho.invariants →ₗ[R] sigma.invariants where
  toFun x := ⟨f x, fun g => by
    rw [equivariant g x, x.property g]⟩
  map_add' x y := by
    apply Subtype.ext
    exact map_add f x.1 y.1
  map_smul' c x := by
    apply Subtype.ext
    exact map_smul f c x.1

@[simp]
theorem deningerInvariantLinearMap_apply
    (rho : Representation R G A)
    (sigma : Representation R G B)
    (f : A →ₗ[R] B)
    (equivariant : ∀ g x, sigma g (f x) = f (rho g x))
    (x : rho.invariants) :
    (deningerInvariantLinearMap rho sigma f equivariant x : B) = f x :=
  rfl

/-- Restriction to invariants preserves composition of equivariant maps. -/
theorem deningerInvariantLinearMap_comp
    (rho : Representation R G A)
    (sigma : Representation R G B)
    (tau : Representation R G C)
    (f : A →ₗ[R] B)
    (g : B →ₗ[R] C)
    (hf : ∀ gamma x, sigma gamma (f x) = f (rho gamma x))
    (hg : ∀ gamma x, tau gamma (g x) = g (sigma gamma x))
    (hgf : ∀ gamma x,
      tau gamma ((g.comp f) x) = (g.comp f) (rho gamma x)) :
    deningerInvariantLinearMap rho tau (g.comp f) hgf =
      (deningerInvariantLinearMap sigma tau g hg).comp
        (deningerInvariantLinearMap rho sigma f hf) := by
  apply LinearMap.ext
  intro x
  rfl

end InvariantMap

section InvariantComplex

variable {R G A0 A1 A2 : Type*}
variable [CommRing R] [Group G]
variable [AddCommGroup A0] [Module R A0]
variable [AddCommGroup A1] [Module R A1]
variable [AddCommGroup A2] [Module R A2]

/--
A three-term arithmetic complex with a degreewise group action commuting
with both differentials.
-/
structure DeningerEquivariantThreeTermComplex where
  rho0 : Representation R G A0
  rho1 : Representation R G A1
  rho2 : Representation R G A2
  d0 : A0 →ₗ[R] A1
  d1 : A1 →ₗ[R] A2
  d1_comp_d0 : d1.comp d0 = 0
  d0_equivariant : ∀ g x, rho1 g (d0 x) = d0 (rho0 g x)
  d1_equivariant : ∀ g x, rho2 g (d1 x) = d1 (rho1 g x)

namespace DeningerEquivariantThreeTermComplex

variable
    (C : DeningerEquivariantThreeTermComplex
      (R := R) (G := G) (A0 := A0) (A1 := A1) (A2 := A2))

/-- Degree-zero differential restricted to fixed sections. -/
def invariantD0 : C.rho0.invariants →ₗ[R] C.rho1.invariants :=
  deningerInvariantLinearMap C.rho0 C.rho1 C.d0 C.d0_equivariant

/-- Degree-one differential restricted to fixed sections. -/
def invariantD1 : C.rho1.invariants →ₗ[R] C.rho2.invariants :=
  deningerInvariantLinearMap C.rho1 C.rho2 C.d1 C.d1_equivariant

@[simp]
theorem invariantD0_apply (x : C.rho0.invariants) :
    (C.invariantD0 x : A1) = C.d0 x :=
  rfl

@[simp]
theorem invariantD1_apply (x : C.rho1.invariants) :
    (C.invariantD1 x : A2) = C.d1 x :=
  rfl

/-- The invariant differentials still compose to zero. -/
theorem invariantD1_comp_invariantD0 :
    C.invariantD1.comp C.invariantD0 = 0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  have hx := LinearMap.congr_fun C.d1_comp_d0 (x : A0)
  simpa [invariantD0, invariantD1, deningerInvariantLinearMap] using hx

/--
Deninger's degreewise fixed sections form a genuine three-term cochain
complex.
-/
def invariantComplex :
    DeningerArithmeticThreeTermComplex R
      C.rho0.invariants C.rho1.invariants C.rho2.invariants where
  d0 := C.invariantD0
  d1 := C.invariantD1
  d1_comp_d0 := C.invariantD1_comp_invariantD0

/--
An equivariant transverse generator commuting with the cover differential
descends to the degreewise invariant complex.
-/
def invariantFlow
    (theta0 : Module.End R A0)
    (theta1 : Module.End R A1)
    (theta2 : Module.End R A2)
    (theta0_equivariant :
      ∀ g x, C.rho0 g (theta0 x) = theta0 (C.rho0 g x))
    (theta1_equivariant :
      ∀ g x, C.rho1 g (theta1 x) = theta1 (C.rho1 g x))
    (theta2_equivariant :
      ∀ g x, C.rho2 g (theta2 x) = theta2 (C.rho2 g x))
    (theta_commutes_d0 : C.d0.comp theta0 = theta1.comp C.d0)
    (theta_commutes_d1 : C.d1.comp theta1 = theta2.comp C.d1) :
    DeningerArithmeticThreeTermFlow R
      C.rho0.invariants C.rho1.invariants C.rho2.invariants where
  toDeningerArithmeticThreeTermComplex := C.invariantComplex
  theta0 :=
    deningerInvariantLinearMap C.rho0 C.rho0 theta0 theta0_equivariant
  theta1 :=
    deningerInvariantLinearMap C.rho1 C.rho1 theta1 theta1_equivariant
  theta2 :=
    deningerInvariantLinearMap C.rho2 C.rho2 theta2 theta2_equivariant
  theta_commutes_d0 := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    have hx := LinearMap.congr_fun theta_commutes_d0 x.1
    change C.d0 (theta0 x.1) = theta1 (C.d0 x.1)
    exact hx
  theta_commutes_d1 := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    have hx := LinearMap.congr_fun theta_commutes_d1 x.1
    change C.d1 (theta1 x.1) = theta2 (C.d1 x.1)
    exact hx

end DeningerEquivariantThreeTermComplex

end InvariantComplex

end RHTower
