/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.QuadraticCyclicGaloisAlgebra
import GaloisForLFunctions.HTGeometry.ABHN.ScalarExtensionBrauer

/-!
# Splitting quadratic cyclic Galois algebras over their defining extension

For a quadratic cyclic Galois extension `L/K`, a nonzero raw cyclic algebra becomes the full
matrix algebra `M₂(L)` after scalar extension from `K` to `L`.  The proof uses the companion
matrix representation already constructed for the raw quotient.  A coefficient moved by the
nontrivial Galois automorphism explicitly isolates all four matrix units.

This is the local splitting mechanism of the quadratic cyclic algebra: its associated Brauer
class restricts to the split class over its defining cyclic extension.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open Multiplicative
open scoped TensorProduct

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]

/-- The quadratic companion representation preserves the base-field algebra structure. -/
theorem quadraticCyclicGaloisAlgebraRepresentation_algebraMap
    (hdeg : Module.finrank K L = 2) (a k : K) :
    quadraticCyclicGaloisAlgebraRepresentation K L hdeg a
      (algebraMap K (cyclicGaloisAlgebra K L a) k) =
        algebraMap K (Matrix (Fin 2) (Fin 2) L) k := by
  change quadraticCyclicGaloisAlgebraRepresentation K L hdeg a
      (cyclicGaloisAlgebraC K L a (algebraMap K L k)) = _
  rw [quadraticCyclicGaloisAlgebraRepresentation, cyclicAlgebraLift_C]
  change quadraticCyclicCoefficientMatrix K L (algebraMap K L k) = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quadraticCyclicCoefficientMatrix, Algebra.algebraMap_eq_smul_one]

/-- The quadratic companion representation promoted to a `K`-algebra homomorphism. -/
noncomputable def quadraticCyclicGaloisAlgebraRepresentationAlgHom
    (hdeg : Module.finrank K L = 2) (a : K) :
    cyclicGaloisAlgebra K L a →ₐ[K] Matrix (Fin 2) (Fin 2) L :=
  AlgHom.mk' (quadraticCyclicGaloisAlgebraRepresentation K L hdeg a) (by
    intro k x
    rw [Algebra.smul_def, Algebra.smul_def, map_mul]
    rw [quadraticCyclicGaloisAlgebraRepresentation_algebraMap])

/-- The quadratic companion algebra homomorphism acts diagonally on coefficients. -/
theorem quadraticCyclicGaloisAlgebraRepresentationAlgHom_C
    (hdeg : Module.finrank K L = 2) (a : K) (b : L) :
    quadraticCyclicGaloisAlgebraRepresentationAlgHom K L hdeg a
      (cyclicGaloisAlgebraC K L a b) = quadraticCyclicCoefficientMatrix K L b := by
  change cyclicAlgebraLift (cyclicGaloisGenerator K L).toRingEquiv (Module.finrank K L)
    (algebraMap K L a) (quadraticCyclicCoefficientMatrixHom K L)
    (quadraticCyclicGeneratorMatrix K L a)
    (quadraticCyclicMatrix_actions_commute K L hdeg a)
    (quadraticCyclicMatrix_square K L hdeg a) (cyclicGaloisAlgebraC K L a b) = _
  exact cyclicAlgebraLift_C _ _ _ _ _ _ _ _

/-- The quadratic companion algebra homomorphism sends the cyclic generator to its companion
matrix. -/
theorem quadraticCyclicGaloisAlgebraRepresentationAlgHom_X
    (hdeg : Module.finrank K L = 2) (a : K) :
    quadraticCyclicGaloisAlgebraRepresentationAlgHom K L hdeg a
      (cyclicGaloisAlgebraX K L a) = quadraticCyclicGeneratorMatrix K L a := by
  change cyclicAlgebraLift (cyclicGaloisGenerator K L).toRingEquiv (Module.finrank K L)
    (algebraMap K L a) (quadraticCyclicCoefficientMatrixHom K L)
    (quadraticCyclicGeneratorMatrix K L a)
    (quadraticCyclicMatrix_actions_commute K L hdeg a)
    (quadraticCyclicMatrix_square K L hdeg a) (cyclicGaloisAlgebraX K L a) = _
  exact cyclicAlgebraLift_X _ _ _ _ _ _ _

/-- The companion representation after extending scalars to the defining quadratic field. -/
noncomputable def quadraticCyclicGaloisAlgebraSplittingMap
    (hdeg : Module.finrank K L = 2) (a : K) :
    L ⊗[K] cyclicGaloisAlgebra K L a →ₐ[L] Matrix (Fin 2) (Fin 2) L :=
  Algebra.TensorProduct.lift (Algebra.ofId L (Matrix (Fin 2) (Fin 2) L))
    (quadraticCyclicGaloisAlgebraRepresentationAlgHom K L hdeg a)
    (fun l x => Algebra.commutes l
      (quadraticCyclicGaloisAlgebraRepresentationAlgHom K L hdeg a x))

/-- Evaluation of the scalar-extended companion representation on pure tensors. -/
theorem quadraticCyclicGaloisAlgebraSplittingMap_tmul
    (hdeg : Module.finrank K L = 2) (a : K) (l : L) (x : cyclicGaloisAlgebra K L a) :
    quadraticCyclicGaloisAlgebraSplittingMap K L hdeg a (l ⊗ₜ[K] x) =
      l • quadraticCyclicGaloisAlgebraRepresentationAlgHom K L hdeg a x := by
  rw [quadraticCyclicGaloisAlgebraSplittingMap, Algebra.TensorProduct.lift_tmul]
  change algebraMap L (Matrix (Fin 2) (Fin 2) L) l *
      quadraticCyclicGaloisAlgebraRepresentationAlgHom K L hdeg a x = _
  rw [Algebra.algebraMap_eq_smul_one, Algebra.smul_mul_assoc, one_mul]

/-- The scalar-extended companion representation on a coefficient tensor. -/
theorem quadraticCyclicGaloisAlgebraSplittingMap_C
    (hdeg : Module.finrank K L = 2) (a : K) (l b : L) :
    quadraticCyclicGaloisAlgebraSplittingMap K L hdeg a
      (l ⊗ₜ[K] cyclicGaloisAlgebraC K L a b) =
        l • quadraticCyclicCoefficientMatrix K L b := by
  rw [quadraticCyclicGaloisAlgebraSplittingMap_tmul,
    quadraticCyclicGaloisAlgebraRepresentationAlgHom_C]

/-- The scalar-extended companion representation on a coefficient times the cyclic generator. -/
theorem quadraticCyclicGaloisAlgebraSplittingMap_C_mul_X
    (hdeg : Module.finrank K L = 2) (a : K) (l b : L) :
    quadraticCyclicGaloisAlgebraSplittingMap K L hdeg a
      (l ⊗ₜ[K] (cyclicGaloisAlgebraC K L a b * cyclicGaloisAlgebraX K L a)) =
        l • (quadraticCyclicCoefficientMatrix K L b *
          quadraticCyclicGeneratorMatrix K L a) := by
  rw [quadraticCyclicGaloisAlgebraSplittingMap_tmul, map_mul,
    quadraticCyclicGaloisAlgebraRepresentationAlgHom_C,
    quadraticCyclicGaloisAlgebraRepresentationAlgHom_X]

/-- Extending scalars to the quadratic Galois field makes the companion representation onto. -/
theorem quadraticCyclicGaloisAlgebraSplittingMap_surjective
    (hdeg : Module.finrank K L = 2) (a : K) (ha : a ≠ 0) :
    Function.Surjective (quadraticCyclicGaloisAlgebraSplittingMap K L hdeg a) := by
  obtain ⟨b, hb⟩ := quadraticCyclicGaloisGenerator_exists_not_fixed K L hdeg
  let d : L := cyclicGaloisGenerator K L b - b
  have hd : d ≠ 0 := sub_ne_zero.mpr hb
  have haL : algebraMap K L a ≠ 0 := by
    intro h
    apply ha
    exact FaithfulSMul.algebraMap_injective K L (by simpa using h)
  let e11 : L ⊗[K] cyclicGaloisAlgebra K L a :=
    d⁻¹ ⊗ₜ[K] cyclicGaloisAlgebraC K L a b -
      (d⁻¹ * b) ⊗ₜ[K] cyclicGaloisAlgebraC K L a 1
  let e00 : L ⊗[K] cyclicGaloisAlgebra K L a :=
    1 ⊗ₜ[K] cyclicGaloisAlgebraC K L a 1 - e11
  let e10 : L ⊗[K] cyclicGaloisAlgebra K L a :=
    d⁻¹ ⊗ₜ[K] (cyclicGaloisAlgebraC K L a b * cyclicGaloisAlgebraX K L a) -
      (d⁻¹ * b) ⊗ₜ[K]
        (cyclicGaloisAlgebraC K L a 1 * cyclicGaloisAlgebraX K L a)
  let e01 : L ⊗[K] cyclicGaloisAlgebra K L a :=
    (algebraMap K L a)⁻¹ ⊗ₜ[K] cyclicGaloisAlgebraX K L a -
      (algebraMap K L a)⁻¹ • e10
  have he11 : quadraticCyclicGaloisAlgebraSplittingMap K L hdeg a e11 =
      !![(0 : L), 0; 0, 1] := by
    dsimp [e11]
    rw [map_sub, quadraticCyclicGaloisAlgebraSplittingMap_C,
      quadraticCyclicGaloisAlgebraSplittingMap_C]
    ext i j
    fin_cases i <;> fin_cases j
    · simp [quadraticCyclicCoefficientMatrix]
    · simp [quadraticCyclicCoefficientMatrix]
    · simp [quadraticCyclicCoefficientMatrix]
    · simp [quadraticCyclicCoefficientMatrix, d, sub_eq_add_neg]
      calc
        _ = ((cyclicGaloisGenerator K L b - b)⁻¹) *
            (cyclicGaloisGenerator K L b - b) := by ring
        _ = 1 := inv_mul_cancel₀ hd
  have he00 : quadraticCyclicGaloisAlgebraSplittingMap K L hdeg a e00 =
      !![(1 : L), 0; 0, 0] := by
    dsimp [e00]
    rw [map_sub, quadraticCyclicGaloisAlgebraSplittingMap_C, he11]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [quadraticCyclicCoefficientMatrix]
  have he10 : quadraticCyclicGaloisAlgebraSplittingMap K L hdeg a e10 =
      !![(0 : L), 0; 1, 0] := by
    dsimp [e10]
    rw [map_sub, quadraticCyclicGaloisAlgebraSplittingMap_C_mul_X,
      quadraticCyclicGaloisAlgebraSplittingMap_C_mul_X]
    ext i j
    fin_cases i <;> fin_cases j
    · simp [quadraticCyclicCoefficientMatrix, quadraticCyclicGeneratorMatrix]
    · simp [quadraticCyclicCoefficientMatrix, quadraticCyclicGeneratorMatrix]
      ring
    · simp [quadraticCyclicCoefficientMatrix, quadraticCyclicGeneratorMatrix,
        d, sub_eq_add_neg]
      calc
        _ = ((cyclicGaloisGenerator K L b - b)⁻¹) *
            (cyclicGaloisGenerator K L b - b) := by ring
        _ = 1 := inv_mul_cancel₀ hd
    · simp [quadraticCyclicCoefficientMatrix, quadraticCyclicGeneratorMatrix]
  have he01 : quadraticCyclicGaloisAlgebraSplittingMap K L hdeg a e01 =
      !![(0 : L), 1; 0, 0] := by
    dsimp [e01]
    rw [map_sub, quadraticCyclicGaloisAlgebraSplittingMap_tmul,
      quadraticCyclicGaloisAlgebraRepresentationAlgHom_X, map_smul, he10]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [quadraticCyclicGeneratorMatrix, haL]
  intro M
  refine ⟨M 0 0 • e00 + M 0 1 • e01 + M 1 0 • e10 + M 1 1 • e11, ?_⟩
  rw [map_add, map_add, map_add, map_smul, map_smul, map_smul, map_smul, he00, he01, he10,
    he11]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The scalar-extended quadratic cyclic algebra and `M₂(L)` have the same dimension. -/
theorem quadraticCyclicGaloisAlgebraSplittingMap_finrank_eq
    (hdeg : Module.finrank K L = 2) (a : K) (ha : a ≠ 0) :
    Module.finrank L (L ⊗[K] cyclicGaloisAlgebra K L a) =
      Module.finrank L (Matrix (Fin 2) (Fin 2) L) := by
  apply le_antisymm
  · calc
      Module.finrank L (L ⊗[K] cyclicGaloisAlgebra K L a) =
          Module.finrank K (cyclicGaloisAlgebra K L a) := by
            rw [Module.finrank_tensorProduct]
            simp
      _ ≤ Module.finrank K L * Module.finrank K L :=
        cyclicGaloisAlgebra_finrank_le K L a
      _ = Module.finrank L (Matrix (Fin 2) (Fin 2) L) := by
        rw [Module.finrank_matrix, hdeg]
        norm_num
  · exact LinearMap.finrank_le_finrank_of_surjective
      (quadraticCyclicGaloisAlgebraSplittingMap_surjective K L hdeg a ha)

/-- A nonzero quadratic cyclic Galois algebra becomes the full `2 × 2` matrix algebra after
extending scalars to its defining extension. -/
noncomputable def quadraticCyclicGaloisAlgebraSplittingAlgEquiv
    (hdeg : Module.finrank K L = 2) (a : K) (ha : a ≠ 0) :
    L ⊗[K] cyclicGaloisAlgebra K L a ≃ₐ[L] Matrix (Fin 2) (Fin 2) L :=
  AlgEquiv.ofBijective (quadraticCyclicGaloisAlgebraSplittingMap K L hdeg a) ⟨
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (quadraticCyclicGaloisAlgebraSplittingMap_finrank_eq K L hdeg a ha)).mpr
        (quadraticCyclicGaloisAlgebraSplittingMap_surjective K L hdeg a ha),
    quadraticCyclicGaloisAlgebraSplittingMap_surjective K L hdeg a ha⟩

/-- The quadratic cyclic Brauer class becomes split over its defining quadratic Galois
extension. -/
theorem scalarExtensionBrauerMap_quadraticCyclicGaloisAlgebraCSA_eq_split
    (hdeg : Module.finrank K L = 2) (a : K) (ha : a ≠ 0) :
    scalarExtensionBrauerMap K L
      (brauerClass (quadraticCyclicGaloisAlgebraCSA K L hdeg a ha)) = brauerSplitClass L := by
  calc
    scalarExtensionBrauerMap K L
        (brauerClass (quadraticCyclicGaloisAlgebraCSA K L hdeg a ha)) =
        brauerClass (scalarExtensionCSA (L := L)
          (quadraticCyclicGaloisAlgebraCSA K L hdeg a ha)) := rfl
    _ = brauerClass (matrixFinCSA (scalarCSA L) 2) :=
      brauerClass_eq_of_algEquiv _ _
        (quadraticCyclicGaloisAlgebraSplittingAlgEquiv K L hdeg a ha)
    _ = brauerSplitClass L := brauerClass_matrixFinCSA_scalar_eq 2

end GaloisForLFunctions.HTGeometry.ABHN
