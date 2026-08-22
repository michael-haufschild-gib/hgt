/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Integral norm on units

For a finite integral extension of integrally closed domains, the integral norm restricts to
units.  After passage to fraction fields, this is the ordinary field norm.  This is the
integral-unit part of the norm bridge needed before comparing local-field norms with residue
norms; no residue compatibility or local reciprocity statement is claimed here.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u v w

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/-- Norm commutes with scalar base change on a canonical tensor element.  This is the
determinant-level core of the still-to-be-proved comparison between integral and residue norms. -/
theorem algebra_norm_baseChange_tmul_one
    (R : Type u) (B : Type v) (A : Type w) [CommRing R] [CommRing B] [CommRing A]
    [Algebra R B] [Algebra R A] [Module.Free R B] [Module.Finite R B] (b : B) :
    Algebra.norm A ((1 : A) ⊗ₜ[R] b) = algebraMap R A (Algebra.norm R b) := by
  rw [Algebra.norm_apply, ← Algebra.baseChange_lmul, LinearMap.det_baseChange,
    Algebra.norm_apply]

/-- Scalar base change commutes with norm in a root algebra.  The target root algebra is the
canonical base change of the defining polynomial.  Identifying this tensor fiber with a residue
root algebra is the only additional step needed for residue-norm compatibility. -/
theorem adjoinRoot_norm_baseChange_tmul_one
    (R : Type u) (T : Type v) [CommRing R] [CommRing T] [Algebra R T]
    (p : Polynomial R) (q : Polynomial (TensorProduct R T R))
    (h : p.map Algebra.TensorProduct.includeRight.toRingHom = q)
    [Module.Free R (AdjoinRoot p)] [Module.Finite R (AdjoinRoot p)] (x : AdjoinRoot p) :
    Algebra.norm T (AdjoinRoot.tensorAlgEquiv p q h ((1 : T) ⊗ₜ[R] x)) =
      algebraMap R T (Algebra.norm R x) := by
  rw [Algebra.norm_eq_of_algEquiv (AdjoinRoot.tensorAlgEquiv p q h)]
  exact algebra_norm_baseChange_tmul_one R (AdjoinRoot p) T x

/-- The canonical scalar-extension equivalence from a root algebra to the root algebra of its
coefficientwise scalar extension. -/
noncomputable def adjoinRootScalarExtensionEquiv
    (R : Type u) (T : Type v) [CommRing R] [CommRing T] [Algebra R T]
    (p : Polynomial R) :
    TensorProduct R T (AdjoinRoot p) ≃ₐ[T] AdjoinRoot (p.map (algebraMap R T)) := by
  let q : Polynomial (TensorProduct R T R) :=
    p.map Algebra.TensorProduct.includeRight.toRingHom
  let e₀ := AdjoinRoot.tensorAlgEquiv p q rfl
  have hq : q.map (Algebra.TensorProduct.rid R T T) = p.map (algebraMap R T) := by
    ext i
    simp [q, Algebra.smul_def]
  let e₁ := AdjoinRoot.mapAlgEquiv (Algebra.TensorProduct.rid R T T) q
    (p.map (algebraMap R T)) (Associated.of_eq hq)
  exact e₀.trans e₁

/-- The scalar-extension root equivalence carries the norm of every canonical tensor image to
the scalar extension of its original norm. -/
theorem adjoinRootScalarExtensionEquiv_norm_tmul_one
    (R : Type u) (T : Type v) [CommRing R] [CommRing T] [Algebra R T]
    (p : Polynomial R) [Module.Free R (AdjoinRoot p)] [Module.Finite R (AdjoinRoot p)]
    (x : AdjoinRoot p) :
    Algebra.norm T
      (adjoinRootScalarExtensionEquiv R T p ((1 : T) ⊗ₜ[R] x)) =
      algebraMap R T (Algebra.norm R x) := by
  unfold adjoinRootScalarExtensionEquiv
  dsimp only
  rw [AlgEquiv.trans_apply, Algebra.norm_eq_of_algEquiv]
  exact adjoinRoot_norm_baseChange_tmul_one R T p _ rfl x

/-- The scalar-extension root equivalence, transported along a specified equality between the
coefficientwise scalar extension and a target polynomial. -/
noncomputable def adjoinRootScalarExtensionEquivOfMapEq
    (R : Type u) (T : Type v) [CommRing R] [CommRing T] [Algebra R T]
    (p : Polynomial R) (q : Polynomial T)
    (h : p.map (algebraMap R T) = q) :
    TensorProduct R T (AdjoinRoot p) ≃ₐ[T] AdjoinRoot q :=
  (adjoinRootScalarExtensionEquiv R T p).trans
    (AdjoinRoot.algEquivOfEq T (p.map (algebraMap R T)) q h)

/-- **Scalar-extension norm compatibility for root algebras.**  In particular, taking `T` to
be a residue field gives the norm comparison on the canonical residue fiber. -/
theorem adjoinRootScalarExtensionEquivOfMapEq_norm_tmul_one
    (R : Type u) (T : Type v) [CommRing R] [CommRing T] [Algebra R T]
    (p : Polynomial R) (q : Polynomial T)
    (h : p.map (algebraMap R T) = q)
    [Module.Free R (AdjoinRoot p)] [Module.Finite R (AdjoinRoot p)] (x : AdjoinRoot p) :
    Algebra.norm T
      (adjoinRootScalarExtensionEquivOfMapEq R T p q h ((1 : T) ⊗ₜ[R] x)) =
      algebraMap R T (Algebra.norm R x) := by
  unfold adjoinRootScalarExtensionEquivOfMapEq
  rw [AlgEquiv.trans_apply, Algebra.norm_eq_of_algEquiv]
  exact adjoinRootScalarExtensionEquiv_norm_tmul_one R T p x

/-- A coefficientwise map of root algebras is surjective whenever its coefficient map is.
This supplies the lifting step from a residue root algebra back to an integral root model. -/
theorem adjoinRoot_map_surjective_of_surjective
    (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    (φ : R →+* S) (hφ : Function.Surjective φ)
    (p : Polynomial R) (q : Polynomial S)
    (h : q ∣ p.map φ) : Function.Surjective (AdjoinRoot.map φ p q h) := by
  intro y
  obtain ⟨r, rfl⟩ := AdjoinRoot.mk_surjective y
  obtain ⟨s, hs⟩ := Polynomial.map_surjective φ hφ r
  refine ⟨AdjoinRoot.mk p s, ?_⟩
  rw [← hs, AdjoinRoot.map, AdjoinRoot.lift_mk,
    ← AdjoinRoot.aeval_eq, Polynomial.aeval_def, AdjoinRoot.algebraMap_eq,
    ← Polynomial.eval₂_map]

/-- The integral norm restricted to units of a finite integral extension. -/
noncomputable def integralNormUnits
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    [IsIntegrallyClosed A] [IsDomain A] [IsDomain B] [IsIntegrallyClosed B]
    [Algebra.IsIntegral A B] [Module.IsTorsionFree A B] [Module.Finite A B] :
    Additive Bˣ →+ Additive Aˣ :=
  (Units.map (Algebra.intNorm A B)).toAdditive

/-- On a unit, `integralNormUnits` is the unit map induced by the integral norm. -/
theorem integralNormUnits_toMul_apply
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    [IsIntegrallyClosed A] [IsDomain A] [IsDomain B] [IsIntegrallyClosed B]
    [Algebra.IsIntegral A B] [Module.IsTorsionFree A B] [Module.Finite A B] (u : Bˣ) :
    (integralNormUnits A B (Additive.ofMul u)).toMul =
      Units.map (Algebra.intNorm A B) u := rfl

/-- The integral norm on units agrees, after embedding into fraction fields, with the field norm.
This is the precise bridge from an integral unramified model to its fraction-field norm. -/
theorem algebraMap_integralNormUnit_eq_fractionField_norm
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    [IsIntegrallyClosed A] [IsDomain A] [IsDomain B] [IsIntegrallyClosed B]
    [Algebra.IsIntegral A B] [Module.IsTorsionFree A B] [Module.Finite A B] (u : Bˣ) :
    algebraMap A (FractionRing A)
        (((integralNormUnits A B (Additive.ofMul u)).toMul : Aˣ) : A) =
      Algebra.norm (FractionRing A)
        (algebraMap B (FractionRing B) ((u : Bˣ) : B)) := by
  change algebraMap A (FractionRing A) (Algebra.intNorm A B (u : B)) =
    Algebra.norm (FractionRing A) (algebraMap B (FractionRing B) (u : B))
  exact Algebra.algebraMap_intNorm_fractionRing (A := A) (B := B) (u : B)

/-- Integral unit norms compose in towers.  This is the tower law needed to assemble the norm
part of finite unramified local extensions before comparing reductions. -/
theorem integralNormUnits_trans
    (A : Type u) (B : Type v) (C : Type w)
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [IsIntegrallyClosed A] [IsIntegrallyClosed B] [IsIntegrallyClosed C]
    [IsDomain A] [IsDomain B] [IsDomain C]
    [Algebra.IsIntegral A B] [Algebra.IsIntegral B C] [Algebra.IsIntegral A C]
    [Module.IsTorsionFree A B] [Module.IsTorsionFree B C] [Module.IsTorsionFree A C]
    [Module.Finite A B] [Module.Finite B C] [Module.Finite A C] :
    integralNormUnits A C =
      (integralNormUnits A B).comp (integralNormUnits B C) := by
  apply AddMonoidHom.ext
  intro u
  apply Additive.toMul.injective
  apply Units.ext
  change Algebra.intNorm A C (u.toMul : C) =
    Algebra.intNorm A B (Algebra.intNorm B C (u.toMul : C))
  rw [Algebra.intNorm_intNorm]

end GaloisForLFunctions.HTGeometry.ABHN
