/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.CubicCyclicGaloisAlgebra

/-!
# Scalar-extended cubic cyclic companion representations

The cubic companion representation is promoted from a ring map to an `L`-algebra map on the
scalar extension `L ⊗[K] A`. Its formulas on coefficients and the cyclic generator are explicit.
Surjectivity, which would identify this map with `M₃(L)` and prove splitting over the defining
field, remains the next open algebraic step.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open Multiplicative
open scoped TensorProduct

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]

/-- The cubic companion representation preserves the base-field algebra structure. -/
theorem cubicCyclicGaloisAlgebraRepresentation_algebraMap
    (hdeg : Module.finrank K L = 3) (a k : K) :
    cubicCyclicGaloisAlgebraRepresentation K L hdeg a
      (algebraMap K (cyclicGaloisAlgebra K L a) k) =
        algebraMap K (Matrix (Fin 3) (Fin 3) L) k := by
  change cubicCyclicGaloisAlgebraRepresentation K L hdeg a
      (cyclicGaloisAlgebraC K L a (algebraMap K L k)) = _
  rw [cubicCyclicGaloisAlgebraRepresentation, cyclicAlgebraLift_C]
  change cubicCyclicCoefficientMatrix K L (algebraMap K L k) = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cubicCyclicCoefficientMatrix, Algebra.algebraMap_eq_smul_one]

/-- The cubic companion representation as a `K`-algebra homomorphism. -/
noncomputable def cubicCyclicGaloisAlgebraRepresentationAlgHom
    (hdeg : Module.finrank K L = 3) (a : K) :
    cyclicGaloisAlgebra K L a →ₐ[K] Matrix (Fin 3) (Fin 3) L :=
  AlgHom.mk' (cubicCyclicGaloisAlgebraRepresentation K L hdeg a) (by
    intro k x
    rw [Algebra.smul_def, Algebra.smul_def, map_mul]
    rw [cubicCyclicGaloisAlgebraRepresentation_algebraMap])

/-- The cubic companion algebra map acts diagonally on coefficients. -/
theorem cubicCyclicGaloisAlgebraRepresentationAlgHom_C
    (hdeg : Module.finrank K L = 3) (a : K) (b : L) :
    cubicCyclicGaloisAlgebraRepresentationAlgHom K L hdeg a
      (cyclicGaloisAlgebraC K L a b) = cubicCyclicCoefficientMatrix K L b := by
  change cyclicAlgebraLift (cyclicGaloisGenerator K L).toRingEquiv (Module.finrank K L)
    (algebraMap K L a) (cubicCyclicCoefficientMatrixHom K L)
    (cubicCyclicGeneratorMatrix K L a)
    (cubicCyclicMatrix_actions_commute K L hdeg a)
    (cubicCyclicMatrix_cube K L hdeg a) (cyclicGaloisAlgebraC K L a b) = _
  exact cyclicAlgebraLift_C _ _ _ _ _ _ _ _

/-- The cubic companion algebra map sends the cyclic generator to its companion matrix. -/
theorem cubicCyclicGaloisAlgebraRepresentationAlgHom_X
    (hdeg : Module.finrank K L = 3) (a : K) :
    cubicCyclicGaloisAlgebraRepresentationAlgHom K L hdeg a
      (cyclicGaloisAlgebraX K L a) = cubicCyclicGeneratorMatrix K L a := by
  change cyclicAlgebraLift (cyclicGaloisGenerator K L).toRingEquiv (Module.finrank K L)
    (algebraMap K L a) (cubicCyclicCoefficientMatrixHom K L)
    (cubicCyclicGeneratorMatrix K L a)
    (cubicCyclicMatrix_actions_commute K L hdeg a)
    (cubicCyclicMatrix_cube K L hdeg a) (cyclicGaloisAlgebraX K L a) = _
  exact cyclicAlgebraLift_X _ _ _ _ _ _ _

/-- The scalar-extended cubic companion representation over its defining Galois field. -/
noncomputable def cubicCyclicGaloisAlgebraScalarExtensionRepresentation
    (hdeg : Module.finrank K L = 3) (a : K) :
    L ⊗[K] cyclicGaloisAlgebra K L a →ₐ[L] Matrix (Fin 3) (Fin 3) L :=
  Algebra.TensorProduct.lift (Algebra.ofId L (Matrix (Fin 3) (Fin 3) L))
    (cubicCyclicGaloisAlgebraRepresentationAlgHom K L hdeg a)
    (fun l x => Algebra.commutes l
      (cubicCyclicGaloisAlgebraRepresentationAlgHom K L hdeg a x))

/-- Evaluation of the scalar-extended cubic companion representation on pure tensors. -/
theorem cubicCyclicGaloisAlgebraScalarExtensionRepresentation_tmul
    (hdeg : Module.finrank K L = 3) (a : K) (l : L) (x : cyclicGaloisAlgebra K L a) :
    cubicCyclicGaloisAlgebraScalarExtensionRepresentation K L hdeg a (l ⊗ₜ[K] x) =
      l • cubicCyclicGaloisAlgebraRepresentationAlgHom K L hdeg a x := by
  rw [cubicCyclicGaloisAlgebraScalarExtensionRepresentation, Algebra.TensorProduct.lift_tmul]
  change algebraMap L (Matrix (Fin 3) (Fin 3) L) l *
      cubicCyclicGaloisAlgebraRepresentationAlgHom K L hdeg a x = _
  rw [Algebra.algebraMap_eq_smul_one, Algebra.smul_mul_assoc, one_mul]

/-- The scalar-extended cubic companion representation on a coefficient tensor. -/
theorem cubicCyclicGaloisAlgebraScalarExtensionRepresentation_C
    (hdeg : Module.finrank K L = 3) (a : K) (l b : L) :
    cubicCyclicGaloisAlgebraScalarExtensionRepresentation K L hdeg a
      (l ⊗ₜ[K] cyclicGaloisAlgebraC K L a b) =
        l • cubicCyclicCoefficientMatrix K L b := by
  rw [cubicCyclicGaloisAlgebraScalarExtensionRepresentation_tmul,
    cubicCyclicGaloisAlgebraRepresentationAlgHom_C]

/-- The scalar-extended cubic companion representation on a coefficient times the cyclic
generator. -/
theorem cubicCyclicGaloisAlgebraScalarExtensionRepresentation_C_mul_X
    (hdeg : Module.finrank K L = 3) (a : K) (l b : L) :
    cubicCyclicGaloisAlgebraScalarExtensionRepresentation K L hdeg a
      (l ⊗ₜ[K] (cyclicGaloisAlgebraC K L a b * cyclicGaloisAlgebraX K L a)) =
        l • (cubicCyclicCoefficientMatrix K L b * cubicCyclicGeneratorMatrix K L a) := by
  rw [cubicCyclicGaloisAlgebraScalarExtensionRepresentation_tmul, map_mul,
    cubicCyclicGaloisAlgebraRepresentationAlgHom_C,
    cubicCyclicGaloisAlgebraRepresentationAlgHom_X]

/-- The scalar-extended cubic companion representation on a coefficient times the square of the
cyclic generator. -/
theorem cubicCyclicGaloisAlgebraScalarExtensionRepresentation_C_mul_X_sq
    (hdeg : Module.finrank K L = 3) (a : K) (l b : L) :
    cubicCyclicGaloisAlgebraScalarExtensionRepresentation K L hdeg a
      (l ⊗ₜ[K] (cyclicGaloisAlgebraC K L a b * cyclicGaloisAlgebraX K L a ^ 2)) =
        l • (cubicCyclicCoefficientMatrix K L b * cubicCyclicGeneratorMatrix K L a ^ 2) := by
  rw [cubicCyclicGaloisAlgebraScalarExtensionRepresentation_tmul, map_mul, map_pow,
    cubicCyclicGaloisAlgebraRepresentationAlgHom_C,
    cubicCyclicGaloisAlgebraRepresentationAlgHom_X]

end GaloisForLFunctions.HTGeometry.ABHN
