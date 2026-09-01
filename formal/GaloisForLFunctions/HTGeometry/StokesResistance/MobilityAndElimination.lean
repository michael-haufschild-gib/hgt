import GaloisForLFunctions.HTGeometry.SchurComplementKernel

/-!
# Mobility symmetry and force-free elimination

This module formalizes two exact reductions from Moreau,
*The Stokes resistance of an arbitrary particle: a classification of hydrodynamic symmetries*,
arXiv:2608.23907v1.

First, an invertible resistance operator and its mobility inverse have the same symmetry commutant.
Second, an invertible force/torque block can be eliminated uniquely; the remaining response is the
Schur complement already developed in the corpus. Inverse laws are carried by `LinearEquiv`, so the
public results need no auxiliary inverse hypotheses.
-/

namespace GaloisForLFunctions.HTGeometry.StokesResistance

open MonoidAlgebra Representation

variable {R G V : Type*} [CommRing R] [Group G]
  [AddCommGroup V] [Module R V]

/-- A response operator commutes with every operator in a representation. -/
def CommutesWithRepresentation (rho : Representation R G V) (T : V →ₗ[R] V) : Prop :=
  ∀ g v, rho g (T v) = T (rho g v)

/-- Moreau's resistance/mobility principle: an invertible operator and its inverse have exactly the
same representation symmetries. -/
theorem commutesWithRepresentation_toLinearMap_iff_symm
    (rho : Representation R G V) (T : V ≃ₗ[R] V) :
    CommutesWithRepresentation rho T.toLinearMap ↔
      CommutesWithRepresentation rho T.symm.toLinearMap := by
  constructor
  · intro h g v
    apply T.injective
    calc
      T (rho g (T.symm v)) = rho g (T (T.symm v)) := (h g (T.symm v)).symm
      _ = rho g v := by rw [T.apply_symm_apply]
      _ = T (T.symm (rho g v)) := by rw [T.apply_symm_apply]
  · intro h g v
    apply T.symm.injective
    calc
      T.symm (rho g (T v)) = rho g (T.symm (T v)) := (h g (T v)).symm
      _ = rho g v := by rw [T.symm_apply_apply]
      _ = T.symm (T (rho g v)) := by rw [T.symm_apply_apply]

variable {F H : Type*} [AddCommGroup F] [Module R F]
  [AddCommGroup H] [Module R H]

/-- An invertible force/torque block determines the eliminated velocity uniquely. -/
theorem boundaryEquation_eq_zero_iff
    (C : F →ₗ[R] H) (D : H ≃ₗ[R] H) (x : F) (y : H) :
    C x + D y = 0 ↔ y = -(D.symm (C x)) := by
  constructor
  · intro h
    apply D.injective
    have hDy : D y = -(C x) := by
      linear_combination (norm := module) h
    simpa using hDy
  · intro h
    simp [h]

/-- Moreau's force-free/torque-free block elimination: the full homogeneous response equation is
equivalent to the Schur-complement equation plus the uniquely eliminated velocity. -/
theorem schurBlockOperator_equiv_apply_eq_zero_iff
    (A : F →ₗ[R] F) (B : H →ₗ[R] F) (C : F →ₗ[R] H)
    (D : H ≃ₗ[R] H) (p : F × H) :
    GaloisForLFunctions.HTGeometry.schurBlockOperator A B C D.toLinearMap p = 0 ↔
      GaloisForLFunctions.HTGeometry.schurComplement A B C D.symm.toLinearMap p.1 = 0 ∧
        p.2 = -(D.symm (C p.1)) := by
  exact GaloisForLFunctions.HTGeometry.schurBlockOperator_apply_eq_zero_iff
    D.apply_symm_apply D.symm_apply_apply p

end GaloisForLFunctions.HTGeometry.StokesResistance
