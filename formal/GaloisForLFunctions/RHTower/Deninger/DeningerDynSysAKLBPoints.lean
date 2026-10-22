import GaloisForLFunctions.HTGeometry.InfiniteGaloisInvariant
import GaloisForLFunctions.HTGeometry.AlgebraicClosureGaloisCompact
import GaloisForLFunctions.RHTower.Deninger.DeningerDynSysInvariantPoints

/-!
# Proposition 3.5's affine input in Deninger's own setting

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Proposition 3.5.

For a normal domain `A` with fraction field `K`, a Galois extension `L / K` — of arbitrary degree —
and the integral closure `B` of `A` in `L`, the Galois group is profinite, acts continuously on the
discrete ring `B`, and `A` is exactly the invariant subring.  Hence Kucharczyk–Scholze Lemma 4.9
applies: homomorphisms of `B` into an algebraically closed field restrict onto those of `A`, with
fibres the Galois orbits.
-/

namespace RHTower

open MulAction

variable (A K L B : Type*) [CommRing A] [CommRing B] [Field K] [Field L]
  [Algebra A K] [Algebra B L] [IsFractionRing A K] [IsFractionRing B L]
  [Algebra A B] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L]
  [IsIntegrallyClosed A] [IsIntegralClosure B A L]
variable [Normal K L] [Algebra.IsSeparable K L]
variable {C : Type*} [Field C] [IsAlgClosed C]
variable [TopologicalSpace B] [DiscreteTopology B]

include K L in
/-- **Deninger, Proposition 3.5, affine input, surjectivity.** -/
theorem deningerAKLB_restrict_surjective [FaithfulSMul A B] :
    letI := IsIntegralClosure.MulSemiringAction A K L B
    Function.Surjective (fun ψ : B →+* C => ψ.comp (algebraMap A B)) := by
  haveI : IsGalois K L := ⟨⟩
  haveI : Algebra.IsAlgebraic K L := inferInstance
  haveI : Algebra.IsIntegral K L := Algebra.IsAlgebraic.isIntegral
  letI := IsIntegralClosure.MulSemiringAction A K L B
  haveI : Algebra.IsInvariant A B (L ≃ₐ[K] L) :=
    HTGeometry.isInvariant_of_isGalois_infinite A K L B
  haveI : ContinuousSMul (L ≃ₐ[K] L) B := HTGeometry.continuousSMul_integralClosure A K L B
  haveI : SMulCommClass (L ≃ₐ[K] L) A B := by
    refine ⟨fun g a b => ?_⟩
    show (galRestrict A K L B g) (a • b) = a • ((galRestrict A K L B g) b)
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, AlgEquiv.commutes]
  exact deningerHom_restrict_surjective (A := A) (B := B) (G := L ≃ₐ[K] L) (C := C)

omit [IsAlgClosed C] in
include K L in
/-- **Deninger, Proposition 3.5, affine input, the fibres.**  Two homomorphisms of `B` into an
algebraically closed field restrict to the same homomorphism of `A` exactly when they differ by an
element of the Galois group. -/
theorem deningerAKLB_restrict_eq_iff (ψ₁ ψ₂ : B →+* C) :
    letI := IsIntegralClosure.MulSemiringAction A K L B
    (ψ₁.comp (algebraMap A B) = ψ₂.comp (algebraMap A B)
      ↔ ∃ g : L ≃ₐ[K] L, ∀ b : B, ψ₂ b = ψ₁ (g • b)) := by
  haveI : IsGalois K L := ⟨⟩
  haveI : Algebra.IsAlgebraic K L := inferInstance
  haveI : Algebra.IsIntegral K L := Algebra.IsAlgebraic.isIntegral
  letI := IsIntegralClosure.MulSemiringAction A K L B
  haveI : Algebra.IsInvariant A B (L ≃ₐ[K] L) :=
    HTGeometry.isInvariant_of_isGalois_infinite A K L B
  haveI : ContinuousSMul (L ≃ₐ[K] L) B := HTGeometry.continuousSMul_integralClosure A K L B
  haveI : SMulCommClass (L ≃ₐ[K] L) A B := by
    refine ⟨fun g a b => ?_⟩
    show (galRestrict A K L B g) (a • b) = a • ((galRestrict A K L B g) b)
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, AlgEquiv.commutes]
  exact deningerHom_restrict_eq_iff (A := A) (B := B) (G := L ≃ₐ[K] L) ψ₁ ψ₂

end RHTower
