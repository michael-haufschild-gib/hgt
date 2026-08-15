import GaloisForLFunctions.RHTower.ArtinLocalEulerFactor
import Mathlib.LinearAlgebra.Charpoly.ToMatrix

/-!
# Product law for local Artin Euler polynomials

This file proves the genuine local source identity
`P_I(ρV × ρW, φ) = P_I(ρV, φ) * P_I(ρW, φ)`.
It uses the concrete product representation and an explicit linear equivalence of invariant
submodules; it introduces no global L-function or analytic interface.
-/

open Polynomial Matrix
open scoped Pointwise

noncomputable section

universe u v w x

namespace GaloisForLFunctions

variable {k : Type u} {D : Type v} {V : Type w} {W : Type x}
variable [Field k] [Group D]
variable [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

/-- The invariant submodule of a product representation is concretely the product of the
invariant submodules. -/
def invariantsProdLinearEquiv
    (ρV : Representation k D V) (ρW : Representation k D W) (I : Subgroup D) :
    Representation.invariants ((ρV.prod ρW).comp I.subtype) ≃ₗ[k]
      Representation.invariants (ρV.comp I.subtype) ×
        Representation.invariants (ρW.comp I.subtype) where
  toFun x :=
    ⟨⟨x.1.1, fun i => congrArg Prod.fst (x.property i)⟩,
      ⟨x.1.2, fun i => congrArg Prod.snd (x.property i)⟩⟩
  invFun x :=
    ⟨(x.1.1, x.2.1), fun i => Prod.ext (x.1.property i) (x.2.property i)⟩
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv x := by
    ext <;> rfl
  map_add' x y := rfl
  map_smul' a x := rfl

/-- Under `invariantsProdLinearEquiv`, Frobenius on the product invariant space is the product
of the individual Frobenius actions. -/
theorem invariantsProdLinearEquiv_conj_toInvariants
    (ρV : Representation k D V) (ρW : Representation k D W) (I : Subgroup D) [I.Normal]
    (φ : D) :
    (invariantsProdLinearEquiv ρV ρW I).conj
        ((Representation.toInvariants (ρV.prod ρW) I) φ) =
      ((Representation.toInvariants ρV I) φ).prodMap
        ((Representation.toInvariants ρW I) φ) := by
  ext x <;> rfl

variable [FiniteDimensional k V] [FiniteDimensional k W]

/-- Local Artin Euler polynomials multiply under the concrete binary direct sum of
representations. -/
theorem localEulerPolynomial_prod
    (ρV : Representation k D V) (ρW : Representation k D W) (I : Subgroup D) [I.Normal]
    (φ : D) :
    localEulerPolynomial (ρV.prod ρW) I φ =
      localEulerPolynomial ρV I φ * localEulerPolynomial ρW I φ := by
  change ((Representation.toInvariants (ρV.prod ρW) I) φ).charpoly.reverse =
    ((Representation.toInvariants ρV I) φ).charpoly.reverse *
      ((Representation.toInvariants ρW I) φ).charpoly.reverse
  rw [← LinearEquiv.charpoly_conj (invariantsProdLinearEquiv ρV ρW I)
    ((Representation.toInvariants (ρV.prod ρW) I) φ)]
  rw [invariantsProdLinearEquiv_conj_toInvariants]
  rw [LinearMap.charpoly_prodMap]
  exact Polynomial.reverse_mul_of_domain _ _

section Arithmetic

variable {R S G : Type u}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [Group G] [Finite G] [MulSemiringAction G S] [SMulCommClass G R S]
variable [Algebra.IsInvariant R S G]
variable [Module ℂ V] [FiniteDimensional ℂ V]
variable [Module ℂ W] [FiniteDimensional ℂ W]

/-- Actual Frobenius--inertia local Euler polynomials multiply under direct sums of Artin
representations. -/
theorem frobeniusInertiaEulerPolynomial_prod
    (Q : Ideal S) [Q.IsPrime] [Finite (S ⧸ Q)]
    (ρV : Representation ℂ G V) (ρW : Representation ℂ G W) :
    frobeniusInertiaEulerPolynomial (R := R) Q (ρV.prod ρW) =
      frobeniusInertiaEulerPolynomial (R := R) Q ρV *
        frobeniusInertiaEulerPolynomial (R := R) Q ρW := by
  exact localEulerPolynomial_prod
    (ρV.comp (MulAction.stabilizer G Q).subtype)
    (ρW.comp (MulAction.stabilizer G Q).subtype)
    (Q.inertia (MulAction.stabilizer G Q))
    (arithmeticFrobeniusInStabilizer (R := R) (G := G) Q)

end Arithmetic

end GaloisForLFunctions
