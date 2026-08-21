/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraEquations
import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Hasse detection of polynomial relations in central simple algebras

For a fixed element of a central simple algebra, evaluation of a global polynomial commutes with
scalar extension. Its vanishing is therefore detected at every completion. This applies to fixed
annihilating-polynomial and characteristic-polynomial relations, but does not assert that arbitrary
local roots glue to a global element.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u v w

open scoped TensorProduct

/-- Vanishing of a polynomial relation for a fixed CSA element is reflected by field scalar
extension. -/
theorem scalarExtensionMap_polynomial_eval₂_eq_zero_iff {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L] (A : CSA.{u, w} K)
    (p : Polynomial K) (a : A.carrier) :
    p.eval₂ (algebraMap K A.carrier) a = 0 ↔
      (p.map (algebraMap K L)).eval₂ (algebraMap L (L ⊗[K] A.carrier))
        (scalarExtensionMap (L := L) A a) = 0 := by
  have hcoeff : (algebraMap L (L ⊗[K] A.carrier)).comp (algebraMap K L) =
      algebraMap K (L ⊗[K] A.carrier) := by
    ext x
    exact (IsScalarTower.algebraMap_apply K L (L ⊗[K] A.carrier) x).symm
  rw [Polynomial.eval₂_map, hcoeff]
  have hcompat : (scalarExtensionMap (L := L) A).toRingHom.comp
      (algebraMap K A.carrier) = algebraMap K (L ⊗[K] A.carrier) := by
    ext x
    simp [scalarExtensionMap, Algebra.TensorProduct.algebraMap_apply]
  constructor
  · intro h
    calc
      p.eval₂ (algebraMap K (L ⊗[K] A.carrier))
          (scalarExtensionMap (L := L) A a) =
        p.eval₂ ((scalarExtensionMap (L := L) A).toRingHom.comp
          (algebraMap K A.carrier)) (scalarExtensionMap (L := L) A a) := by rw [hcompat]
      _ = scalarExtensionMap (L := L) A (p.eval₂ (algebraMap K A.carrier) a) :=
        (Polynomial.hom_eval₂ p (algebraMap K A.carrier)
          (scalarExtensionMap (L := L) A).toRingHom a).symm
      _ = 0 := by rw [h, map_zero]
  · intro h
    apply scalarExtensionMap_injective (L := L) A
    simpa only [map_zero] using
      (calc
        scalarExtensionMap (L := L) A (p.eval₂ (algebraMap K A.carrier) a) =
          p.eval₂ ((scalarExtensionMap (L := L) A).toRingHom.comp
            (algebraMap K A.carrier)) (scalarExtensionMap (L := L) A a) :=
          Polynomial.hom_eval₂ p (algebraMap K A.carrier)
            (scalarExtensionMap (L := L) A).toRingHom a
        _ = p.eval₂ (algebraMap K (L ⊗[K] A.carrier))
            (scalarExtensionMap (L := L) A a) := by rw [hcompat]
        _ = 0 := h)

/-- A polynomial relation for an element of a CSA over a number field holds exactly when its
coefficientwise scalar extension holds at every completed place. -/
theorem numberFieldLocalScalarExtensionMap_polynomial_eval₂_eq_zero_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (A : CSA.{u, w} K)
    (p : Polynomial K) (a : A.carrier) :
    p.eval₂ (algebraMap K A.carrier) a = 0 ↔ ∀ v : NumberFieldPlace K,
      (p.map (algebraMap K (completion K v))).eval₂
        (algebraMap (completion K v) (completion K v ⊗[K] A.carrier))
          (numberFieldLocalScalarExtensionMap K v A a) = 0 := by
  constructor
  · intro h v
    exact (scalarExtensionMap_polynomial_eval₂_eq_zero_iff (L := completion K v) A p a).mp h
  · intro h
    exact (scalarExtensionMap_polynomial_eval₂_eq_zero_iff
      (L := completion K (witnessPlace K)) A p a).mpr (h (witnessPlace K))

/-- A polynomial relation for an element of a CSA over `F(t)` holds exactly when its
coefficientwise scalar extension holds at every finite and infinite completed place. -/
theorem rationalFunctionLocalScalarExtensionMap_polynomial_eval₂_eq_zero_iff_forall_place
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, w} (RatFunc F))
    (p : Polynomial (RatFunc F)) (a : A.carrier) :
    p.eval₂ (algebraMap (RatFunc F) A.carrier) a = 0 ↔ ∀ v : RationalFunctionPlace F,
      (p.map (algebraMap (RatFunc F) (rationalFunctionCompletion F v))).eval₂
        (algebraMap (rationalFunctionCompletion F v)
          (rationalFunctionCompletion F v ⊗[RatFunc F] A.carrier))
            (rationalFunctionLocalScalarExtensionMap F v A a) = 0 := by
  constructor
  · intro h v
    exact (scalarExtensionMap_polynomial_eval₂_eq_zero_iff
      (L := rationalFunctionCompletion F v) A p a).mp h
  · intro h
    exact (scalarExtensionMap_polynomial_eval₂_eq_zero_iff
      (L := rationalFunctionCompletion F .infinite) A p a).mpr (h .infinite)

end GaloisForLFunctions.HTGeometry.ABHN
