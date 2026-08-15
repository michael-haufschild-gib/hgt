import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.RepresentationTheory.Invariants
import Mathlib.RingTheory.Frobenius

/-!
# Frobenius--inertia local Euler polynomials for Artin representations

This file constructs the actual local Artin polynomial
`det(1 - T ρ(Frob) | V^I)`.  The generic construction uses an actual group, normal subgroup,
and finite-dimensional representation; the arithmetic adapter specializes it to Mathlib's actual
ideal inertia subgroup, decomposition stabilizer, and arithmetic Frobenius choice.

It is local source infrastructure only.  It contains no Euler-product continuation or
Artin-holomorphy assertion.
-/

open Polynomial Matrix
open scoped Pointwise

noncomputable section

universe u v w x

namespace GaloisForLFunctions

variable {k : Type u} {D : Type v} {V : Type w}
variable [Field k] [Group D] [AddCommGroup V] [Module k V]

section FiniteDimensional

variable [FiniteDimensional k V]

/-- The local Euler polynomial `det(1 - T ρ(φ) | V^I)` for a normal inertia subgroup. -/
def localEulerPolynomial
    (ρ : Representation k D V) (I : Subgroup D) [I.Normal] (φ : D) : k[X] :=
  ((Representation.toInvariants ρ I) φ).charpoly.reverse

/-- A basis-level determinant realization of `localEulerPolynomial`. -/
theorem localEulerPolynomial_eq_det
    (ρ : Representation k D V) (I : Subgroup D) [I.Normal] (φ : D) :
    localEulerPolynomial ρ I φ =
      Matrix.det (1 - (X : k[X]) •
        (LinearMap.toMatrix
          (Module.Free.chooseBasis k (Representation.invariants (ρ.comp I.subtype)))
          (Module.Free.chooseBasis k (Representation.invariants (ρ.comp I.subtype)))
          ((Representation.toInvariants ρ I) φ)).map C) := by
  rw [localEulerPolynomial, LinearMap.charpoly_def, Matrix.reverse_charpoly,
    Matrix.charpolyRev]

/-- Every local Euler polynomial has constant coefficient one. -/
theorem localEulerPolynomial_eval_zero
    (ρ : Representation k D V) (I : Subgroup D) [I.Normal] (φ : D) :
    (localEulerPolynomial ρ I φ).eval 0 = 1 := by
  rw [localEulerPolynomial_eq_det]
  exact Matrix.eval_charpolyRev

end FiniteDimensional

section FiniteImage

variable [Finite D]

/-- The action induced on inertia invariants still has finite order.  This is the finite-image
input behind root-free local Euler factors in the absolute-convergence half-plane. -/
theorem toInvariants_pow_natCard_eq_one
    (ρ : Representation k D V) (I : Subgroup D) [I.Normal] (φ : D) :
    (Representation.toInvariants ρ I φ) ^ Nat.card D = 1 := by
  rw [← map_pow, pow_card_eq_one', map_one]

end FiniteImage

/-- Inertia acts trivially on its invariant subrepresentation. -/
theorem toInvariants_frobenius_right_mul
    (ρ : Representation k D V) (I : Subgroup D) [I.Normal]
    (φ : D) (i : I) :
    (Representation.toInvariants ρ I) (φ * (i : D)) =
      (Representation.toInvariants ρ I) φ := by
  ext x
  change ρ (φ * (i : D)) x = ρ φ x
  rw [ρ.map_mul, Module.End.mul_apply]
  congr 1
  simpa using x.property i

/-- Frobenius actions on inertia invariants depend only on the quotient class modulo inertia. -/
theorem toInvariants_frobenius_eq_of_mul_inv_mem
    (ρ : Representation k D V) (I : Subgroup D) [I.Normal] (φ ψ : D)
    (hψφ : ψ * φ⁻¹ ∈ I) :
    (Representation.toInvariants ρ I) ψ = (Representation.toInvariants ρ I) φ := by
  have hφψ : φ⁻¹ * ψ ∈ I := by
    simpa [mul_assoc] using
      (inferInstance : I.Normal).conj_mem' (ψ * φ⁻¹) hψφ φ
  let i : I := ⟨φ⁻¹ * ψ, hφψ⟩
  have hψ : ψ = φ * (i : D) := by
    dsimp [i]
    group
  rw [hψ, toInvariants_frobenius_right_mul]

section FiniteDimensional

variable [FiniteDimensional k V]

/-- Frobenius local Euler polynomials depend only on the quotient class modulo inertia. -/
theorem localEulerPolynomial_eq_of_mul_inv_mem
    (ρ : Representation k D V) (I : Subgroup D) [I.Normal] (φ ψ : D)
    (hψφ : ψ * φ⁻¹ ∈ I) :
    localEulerPolynomial ρ I ψ = localEulerPolynomial ρ I φ := by
  rw [localEulerPolynomial, localEulerPolynomial,
    toInvariants_frobenius_eq_of_mul_inv_mem ρ I φ ψ hψφ]

end FiniteDimensional

variable {R S G : Type x}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [Group G] [Finite G] [MulSemiringAction G S] [SMulCommClass G R S]
variable [Algebra.IsInvariant R S G]
variable [Module ℂ V]

/-- Mathlib's chosen arithmetic Frobenius, bundled in its actual decomposition stabilizer. -/
noncomputable def arithmeticFrobeniusInStabilizer
    (Q : Ideal S) [Q.IsPrime] [Finite (S ⧸ Q)] : MulAction.stabilizer G Q :=
  ⟨arithFrobAt R G Q, IsArithFrobAt.arithFrobAt_mem_stabilizer R G Q⟩

/-- Actual Frobenius action on the invariant subspace for the inertia at a prime ideal. -/
noncomputable def frobeniusInertiaAction
    (Q : Ideal S) [Q.IsPrime] [Finite (S ⧸ Q)]
    (ρ : Representation ℂ G V) :
    Module.End ℂ (Representation.invariants
      ((ρ.comp (MulAction.stabilizer G Q).subtype).comp
        (Q.inertia (MulAction.stabilizer G Q)).subtype)) :=
  (Representation.toInvariants (ρ.comp (MulAction.stabilizer G Q).subtype)
    (Q.inertia (MulAction.stabilizer G Q)))
    (arithmeticFrobeniusInStabilizer (R := R) (G := G) Q)

section FiniteDimensional

variable [FiniteDimensional ℂ V]

/-- The actual arithmetic Frobenius action on inertia invariants has finite order. -/
theorem frobeniusInertiaAction_pow_natCard_eq_one
    (Q : Ideal S) [Q.IsPrime] [Finite (S ⧸ Q)]
    (ρ : Representation ℂ G V) :
    (frobeniusInertiaAction (R := R) Q ρ) ^ Nat.card (MulAction.stabilizer G Q) = 1 := by
  exact toInvariants_pow_natCard_eq_one _ _ _

/-- The Artin local Euler polynomial attached to Mathlib's actual arithmetic Frobenius at `Q`. -/
noncomputable def frobeniusInertiaEulerPolynomial
    (Q : Ideal S) [Q.IsPrime] [Finite (S ⧸ Q)]
    (ρ : Representation ℂ G V) : Polynomial ℂ :=
  localEulerPolynomial
    (ρ.comp (MulAction.stabilizer G Q).subtype :
      Representation ℂ (MulAction.stabilizer G Q) V)
    (Q.inertia (MulAction.stabilizer G Q))
    (arithmeticFrobeniusInStabilizer (R := R) (G := G) Q)

/-- The arithmetic local polynomial is the reversed characteristic polynomial of its actual
Frobenius--inertia action. -/
theorem frobeniusInertiaEulerPolynomial_eq_action
    (Q : Ideal S) [Q.IsPrime] [Finite (S ⧸ Q)]
    (ρ : Representation ℂ G V) :
    frobeniusInertiaEulerPolynomial (R := R) Q ρ =
      (frobeniusInertiaAction (R := R) Q ρ).charpoly.reverse := rfl

end FiniteDimensional

/-- Any arithmetic Frobenius, bundled in the actual decomposition stabilizer. -/
def anyFrobeniusInStabilizer
    (Q : Ideal S) [Q.IsPrime] {σ : G}
    (hσ : IsArithFrobAt R σ Q) : MulAction.stabilizer G Q :=
  ⟨σ, hσ.mem_stabilizer⟩

/-- Two arithmetic Frobenius lifts differ by an element of the actual inertia subgroup. -/
theorem anyFrobenius_mul_inv_mem_inertia
    (Q : Ideal S) [Q.IsPrime] [Finite (S ⧸ Q)] {σ : G}
    (hσ : IsArithFrobAt R σ Q) :
    anyFrobeniusInStabilizer (R := R) Q hσ *
        (arithmeticFrobeniusInStabilizer (R := R) (G := G) Q)⁻¹ ∈
      Q.inertia (MulAction.stabilizer G Q) := by
  apply AddSubgroup.coe_mem_inertia.mp
  change σ * (arithFrobAt R G Q)⁻¹ ∈ Q.inertia G
  exact hσ.mul_inv_mem_inertia (IsArithFrobAt.arithFrobAt R G Q)

/-- The actual Frobenius action on inertia invariants is independent of the Frobenius lift. -/
theorem frobeniusInertiaAction_eq_of_isArithFrobAt
    (Q : Ideal S) [Q.IsPrime] [Finite (S ⧸ Q)] {σ : G}
    (ρ : Representation ℂ G V) (hσ : IsArithFrobAt R σ Q) :
    (Representation.toInvariants (ρ.comp (MulAction.stabilizer G Q).subtype)
      (Q.inertia (MulAction.stabilizer G Q)))
      (anyFrobeniusInStabilizer (R := R) Q hσ) =
      frobeniusInertiaAction (R := R) Q ρ := by
  exact toInvariants_frobenius_eq_of_mul_inv_mem _ _ _ _
    (anyFrobenius_mul_inv_mem_inertia (R := R) (Q := Q) hσ)

section FiniteDimensional

variable [FiniteDimensional ℂ V]

/-- The actual Artin local Euler polynomial is independent of the arithmetic Frobenius lift. -/
theorem frobeniusInertiaEulerPolynomial_eq_of_isArithFrobAt
    (Q : Ideal S) [Q.IsPrime] [Finite (S ⧸ Q)] {σ : G}
    (ρ : Representation ℂ G V) (hσ : IsArithFrobAt R σ Q) :
    localEulerPolynomial
      (ρ.comp (MulAction.stabilizer G Q).subtype :
        Representation ℂ (MulAction.stabilizer G Q) V)
      (Q.inertia (MulAction.stabilizer G Q))
      (anyFrobeniusInStabilizer (R := R) Q hσ) =
      frobeniusInertiaEulerPolynomial (R := R) (Q := Q) ρ := by
  apply localEulerPolynomial_eq_of_mul_inv_mem
  exact anyFrobenius_mul_inv_mem_inertia (R := R) (Q := Q) hσ

/-- The actual Artin local Euler polynomial has value one at zero. -/
theorem frobeniusInertiaEulerPolynomial_eval_zero
    (Q : Ideal S) [Q.IsPrime] [Finite (S ⧸ Q)]
    (ρ : Representation ℂ G V) :
    (frobeniusInertiaEulerPolynomial (R := R) Q ρ).eval 0 = 1 :=
  localEulerPolynomial_eval_zero _ _ _

end FiniteDimensional

end GaloisForLFunctions
