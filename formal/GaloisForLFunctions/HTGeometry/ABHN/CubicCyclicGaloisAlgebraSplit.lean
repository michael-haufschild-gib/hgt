/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.CubicCyclicGaloisAlgebraSplittingFields
import GaloisForLFunctions.HTGeometry.ABHN.ScalarExtensionBrauer

/-!
# Splitting cubic cyclic Galois algebras over their defining extension

The diagonal interpolation units from `CubicCyclicGaloisAlgebraSplittingFields` and the cubic
companion matrix give all nine matrix units. Thus every nonzero cubic cyclic Galois algebra splits
over its defining extension, and its Brauer class restricts to zero there.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open Multiplicative
open scoped TensorProduct

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]

/-- The scalar-extended representation sends the cyclic generator to its companion matrix. -/
theorem cubicCyclicGaloisAlgebraScalarExtensionRepresentation_X
    (hdeg : Module.finrank K L = 3) (a : K) :
    cubicCyclicGaloisAlgebraScalarExtensionRepresentation K L hdeg a
      (1 ⊗ₜ[K] cyclicGaloisAlgebraX K L a) = cubicCyclicGeneratorMatrix K L a := by
  rw [cubicCyclicGaloisAlgebraScalarExtensionRepresentation_tmul,
    cubicCyclicGaloisAlgebraRepresentationAlgHom_X]
  simp

/-- The scalar-extended representation sends the square of the cyclic generator to the square of
its companion matrix. -/
theorem cubicCyclicGaloisAlgebraScalarExtensionRepresentation_X_sq
    (hdeg : Module.finrank K L = 3) (a : K) :
    cubicCyclicGaloisAlgebraScalarExtensionRepresentation K L hdeg a
      (1 ⊗ₜ[K] (cyclicGaloisAlgebraX K L a ^ 2)) =
        cubicCyclicGeneratorMatrix K L a ^ 2 := by
  rw [cubicCyclicGaloisAlgebraScalarExtensionRepresentation_tmul, map_pow,
    cubicCyclicGaloisAlgebraRepresentationAlgHom_X]
  simp

/-- The scalar-extended cubic companion representation contains `E₀₂`. -/
theorem cubicCyclicGaloisAlgebraScalarExtensionRepresentation_exists_e02
    (hdeg : Module.finrank K L = 3) (a : K) (ha : a ≠ 0) :
    ∃ e : L ⊗[K] cyclicGaloisAlgebra K L a,
      cubicCyclicGaloisAlgebraScalarExtensionRepresentation K L hdeg a e =
        !![(0 : L), 0, 1; 0, 0, 0; 0, 0, 0] := by
  obtain ⟨e00, he00⟩ :=
    cubicCyclicGaloisAlgebraScalarExtensionRepresentation_exists_e00 K L hdeg a
  let aL : L := algebraMap K L a
  have haL : aL ≠ 0 := by
    simpa [aL] using (algebraMap K L).injective.ne ha
  let x : L ⊗[K] cyclicGaloisAlgebra K L a :=
    1 ⊗ₜ[K] cyclicGaloisAlgebraX K L a
  let e : L ⊗[K] cyclicGaloisAlgebra K L a := aL⁻¹ • (e00 * x)
  refine ⟨e, ?_⟩
  dsimp [e]
  rw [map_smul, map_mul, he00]
  have hx : cubicCyclicGaloisAlgebraScalarExtensionRepresentation K L hdeg a x =
      cubicCyclicGeneratorMatrix K L a := by
    dsimp [x]
    exact cubicCyclicGaloisAlgebraScalarExtensionRepresentation_X K L hdeg a
  rw [hx]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cubicCyclicGeneratorMatrix, aL, haL]

/-- The scalar-extended cubic companion representation contains `E₁₀`. -/
theorem cubicCyclicGaloisAlgebraScalarExtensionRepresentation_exists_e10
    (hdeg : Module.finrank K L = 3) (a : K) :
    ∃ e : L ⊗[K] cyclicGaloisAlgebra K L a,
      cubicCyclicGaloisAlgebraScalarExtensionRepresentation K L hdeg a e =
        !![(0 : L), 0, 0; 1, 0, 0; 0, 0, 0] := by
  obtain ⟨e11, he11⟩ :=
    cubicCyclicGaloisAlgebraScalarExtensionRepresentation_exists_e11 K L hdeg a
  let x : L ⊗[K] cyclicGaloisAlgebra K L a :=
    1 ⊗ₜ[K] cyclicGaloisAlgebraX K L a
  refine ⟨e11 * x, ?_⟩
  rw [map_mul, he11]
  have hx : cubicCyclicGaloisAlgebraScalarExtensionRepresentation K L hdeg a x =
      cubicCyclicGeneratorMatrix K L a := by
    dsimp [x]
    exact cubicCyclicGaloisAlgebraScalarExtensionRepresentation_X K L hdeg a
  rw [hx]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cubicCyclicGeneratorMatrix, Matrix.mul_apply, Fin.sum_univ_three]

/-- The scalar-extended cubic companion representation contains `E₂₁`. -/
theorem cubicCyclicGaloisAlgebraScalarExtensionRepresentation_exists_e21
    (hdeg : Module.finrank K L = 3) (a : K) :
    ∃ e : L ⊗[K] cyclicGaloisAlgebra K L a,
      cubicCyclicGaloisAlgebraScalarExtensionRepresentation K L hdeg a e =
        !![(0 : L), 0, 0; 0, 0, 0; 0, 1, 0] := by
  obtain ⟨e22, he22⟩ :=
    cubicCyclicGaloisAlgebraScalarExtensionRepresentation_exists_e22 K L hdeg a
  let x : L ⊗[K] cyclicGaloisAlgebra K L a :=
    1 ⊗ₜ[K] cyclicGaloisAlgebraX K L a
  refine ⟨e22 * x, ?_⟩
  rw [map_mul, he22]
  have hx : cubicCyclicGaloisAlgebraScalarExtensionRepresentation K L hdeg a x =
      cubicCyclicGeneratorMatrix K L a := by
    dsimp [x]
    exact cubicCyclicGaloisAlgebraScalarExtensionRepresentation_X K L hdeg a
  rw [hx]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cubicCyclicGeneratorMatrix, Matrix.mul_apply, Fin.sum_univ_three]

/-- The scalar-extended cubic companion representation contains `E₂₀`. -/
theorem cubicCyclicGaloisAlgebraScalarExtensionRepresentation_exists_e20
    (hdeg : Module.finrank K L = 3) (a : K) :
    ∃ e : L ⊗[K] cyclicGaloisAlgebra K L a,
      cubicCyclicGaloisAlgebraScalarExtensionRepresentation K L hdeg a e =
        !![(0 : L), 0, 0; 0, 0, 0; 1, 0, 0] := by
  obtain ⟨e22, he22⟩ :=
    cubicCyclicGaloisAlgebraScalarExtensionRepresentation_exists_e22 K L hdeg a
  let x : L ⊗[K] cyclicGaloisAlgebra K L a :=
    1 ⊗ₜ[K] (cyclicGaloisAlgebraX K L a ^ 2)
  refine ⟨e22 * x, ?_⟩
  rw [map_mul, he22]
  have hx : cubicCyclicGaloisAlgebraScalarExtensionRepresentation K L hdeg a x =
      cubicCyclicGeneratorMatrix K L a ^ 2 := by
    dsimp [x]
    exact cubicCyclicGaloisAlgebraScalarExtensionRepresentation_X_sq K L hdeg a
  rw [hx]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cubicCyclicGeneratorMatrix, Matrix.mul_apply, Fin.sum_univ_three, pow_two]

/-- The scalar-extended cubic companion representation contains `E₀₁`. -/
theorem cubicCyclicGaloisAlgebraScalarExtensionRepresentation_exists_e01
    (hdeg : Module.finrank K L = 3) (a : K) (ha : a ≠ 0) :
    ∃ e : L ⊗[K] cyclicGaloisAlgebra K L a,
      cubicCyclicGaloisAlgebraScalarExtensionRepresentation K L hdeg a e =
        !![(0 : L), 1, 0; 0, 0, 0; 0, 0, 0] := by
  obtain ⟨e00, he00⟩ :=
    cubicCyclicGaloisAlgebraScalarExtensionRepresentation_exists_e00 K L hdeg a
  let aL : L := algebraMap K L a
  have haL : aL ≠ 0 := by
    simpa [aL] using (algebraMap K L).injective.ne ha
  let x : L ⊗[K] cyclicGaloisAlgebra K L a :=
    1 ⊗ₜ[K] (cyclicGaloisAlgebraX K L a ^ 2)
  let e : L ⊗[K] cyclicGaloisAlgebra K L a := aL⁻¹ • (e00 * x)
  refine ⟨e, ?_⟩
  dsimp [e]
  rw [map_smul, map_mul, he00]
  have hx : cubicCyclicGaloisAlgebraScalarExtensionRepresentation K L hdeg a x =
      cubicCyclicGeneratorMatrix K L a ^ 2 := by
    dsimp [x]
    exact cubicCyclicGaloisAlgebraScalarExtensionRepresentation_X_sq K L hdeg a
  rw [hx]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cubicCyclicGeneratorMatrix, pow_two, Algebra.smul_def, aL, haL]

/-- The scalar-extended cubic companion representation contains `E₁₂`. -/
theorem cubicCyclicGaloisAlgebraScalarExtensionRepresentation_exists_e12
    (hdeg : Module.finrank K L = 3) (a : K) (ha : a ≠ 0) :
    ∃ e : L ⊗[K] cyclicGaloisAlgebra K L a,
      cubicCyclicGaloisAlgebraScalarExtensionRepresentation K L hdeg a e =
        !![(0 : L), 0, 0; 0, 0, 1; 0, 0, 0] := by
  obtain ⟨e11, he11⟩ :=
    cubicCyclicGaloisAlgebraScalarExtensionRepresentation_exists_e11 K L hdeg a
  let aL : L := algebraMap K L a
  have haL : aL ≠ 0 := by
    simpa [aL] using (algebraMap K L).injective.ne ha
  let x : L ⊗[K] cyclicGaloisAlgebra K L a :=
    1 ⊗ₜ[K] (cyclicGaloisAlgebraX K L a ^ 2)
  let e : L ⊗[K] cyclicGaloisAlgebra K L a := aL⁻¹ • (e11 * x)
  refine ⟨e, ?_⟩
  dsimp [e]
  rw [map_smul, map_mul, he11]
  have hx : cubicCyclicGaloisAlgebraScalarExtensionRepresentation K L hdeg a x =
      cubicCyclicGeneratorMatrix K L a ^ 2 := by
    dsimp [x]
    exact cubicCyclicGaloisAlgebraScalarExtensionRepresentation_X_sq K L hdeg a
  rw [hx]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cubicCyclicGeneratorMatrix, pow_two, Algebra.smul_def, aL, haL]

/-- The cubic scalar-extension companion representation is surjective. -/
theorem cubicCyclicGaloisAlgebraScalarExtensionRepresentation_surjective
    (hdeg : Module.finrank K L = 3) (a : K) (ha : a ≠ 0) :
    Function.Surjective
      (cubicCyclicGaloisAlgebraScalarExtensionRepresentation K L hdeg a) := by
  apply LinearMap.range_eq_top.mp
  refine (Submodule.eq_top_iff_forall_basis_mem
    (Matrix.stdBasis L (Fin 3) (Fin 3))).mpr ?_
  rintro ⟨i, j⟩
  have hstd : Matrix.stdBasis L (Fin 3) (Fin 3) (i, j) = Matrix.single i j 1 := by
    ext x y
    simp [Matrix.stdBasis]
    by_cases hix : i = x
    · subst x
      by_cases hjy : j = y
      · subst y
        simp [Matrix.single]
      · simp [Matrix.single, hjy]
    · have hxi : x ≠ i := Ne.symm hix
      simp [Matrix.single, hix, hxi]
  rw [hstd]
  change ∃ e, cubicCyclicGaloisAlgebraScalarExtensionRepresentation K L hdeg a e = _
  fin_cases i <;> fin_cases j
  · obtain ⟨e, he⟩ :=
      cubicCyclicGaloisAlgebraScalarExtensionRepresentation_exists_e00 K L hdeg a
    refine ⟨e, ?_⟩
    rw [he]
    ext x y
    fin_cases x <;> fin_cases y <;> simp [Matrix.single]

  · obtain ⟨e, he⟩ :=
      cubicCyclicGaloisAlgebraScalarExtensionRepresentation_exists_e01 K L hdeg a ha
    refine ⟨e, ?_⟩
    rw [he]
    ext x y
    fin_cases x <;> fin_cases y <;> simp [Matrix.single]
  · obtain ⟨e, he⟩ :=
      cubicCyclicGaloisAlgebraScalarExtensionRepresentation_exists_e02 K L hdeg a ha
    refine ⟨e, ?_⟩
    rw [he]
    ext x y
    fin_cases x <;> fin_cases y <;> simp [Matrix.single]
  · obtain ⟨e, he⟩ :=
      cubicCyclicGaloisAlgebraScalarExtensionRepresentation_exists_e10 K L hdeg a
    refine ⟨e, ?_⟩
    rw [he]
    ext x y
    fin_cases x <;> fin_cases y <;> simp [Matrix.single]
  · obtain ⟨e, he⟩ :=
      cubicCyclicGaloisAlgebraScalarExtensionRepresentation_exists_e11 K L hdeg a
    refine ⟨e, ?_⟩
    rw [he]
    ext x y
    fin_cases x <;> fin_cases y <;> simp [Matrix.single]
  · obtain ⟨e, he⟩ :=
      cubicCyclicGaloisAlgebraScalarExtensionRepresentation_exists_e12 K L hdeg a ha
    refine ⟨e, ?_⟩
    rw [he]
    ext x y
    fin_cases x <;> fin_cases y <;> simp [Matrix.single]
  · obtain ⟨e, he⟩ :=
      cubicCyclicGaloisAlgebraScalarExtensionRepresentation_exists_e20 K L hdeg a
    refine ⟨e, ?_⟩
    rw [he]
    ext x y
    fin_cases x <;> fin_cases y <;> simp [Matrix.single]
  · obtain ⟨e, he⟩ :=
      cubicCyclicGaloisAlgebraScalarExtensionRepresentation_exists_e21 K L hdeg a
    refine ⟨e, ?_⟩
    rw [he]
    ext x y
    fin_cases x <;> fin_cases y <;> simp [Matrix.single]
  · obtain ⟨e, he⟩ :=
      cubicCyclicGaloisAlgebraScalarExtensionRepresentation_exists_e22 K L hdeg a
    refine ⟨e, ?_⟩
    rw [he]
    ext x y
    fin_cases x <;> fin_cases y <;> simp [Matrix.single]

/-- The scalar-extended cubic cyclic algebra and `M₃(L)` have the same dimension. -/
theorem cubicCyclicGaloisAlgebraScalarExtensionRepresentation_finrank_eq
    (hdeg : Module.finrank K L = 3) (a : K) (ha : a ≠ 0) :
    Module.finrank L (L ⊗[K] cyclicGaloisAlgebra K L a) =
      Module.finrank L (Matrix (Fin 3) (Fin 3) L) := by
  apply le_antisymm
  · calc
      Module.finrank L (L ⊗[K] cyclicGaloisAlgebra K L a) =
          Module.finrank K (cyclicGaloisAlgebra K L a) := by
            rw [Module.finrank_tensorProduct]
            simp
      _ ≤ Module.finrank K L * Module.finrank K L :=
        cyclicGaloisAlgebra_finrank_le K L a
      _ = Module.finrank L (Matrix (Fin 3) (Fin 3) L) := by
        rw [Module.finrank_matrix, hdeg]
        norm_num
  · exact LinearMap.finrank_le_finrank_of_surjective
      (cubicCyclicGaloisAlgebraScalarExtensionRepresentation_surjective K L hdeg a ha)

/-- A nonzero cubic cyclic Galois algebra becomes the full `3 × 3` matrix algebra after extending
scalars to its defining cyclic Galois extension. -/
noncomputable def cubicCyclicGaloisAlgebraSplittingAlgEquiv
    (hdeg : Module.finrank K L = 3) (a : K) (ha : a ≠ 0) :
    L ⊗[K] cyclicGaloisAlgebra K L a ≃ₐ[L] Matrix (Fin 3) (Fin 3) L :=
  AlgEquiv.ofBijective (cubicCyclicGaloisAlgebraScalarExtensionRepresentation K L hdeg a) ⟨
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (cubicCyclicGaloisAlgebraScalarExtensionRepresentation_finrank_eq K L hdeg a ha)).mpr
        (cubicCyclicGaloisAlgebraScalarExtensionRepresentation_surjective K L hdeg a ha),
    cubicCyclicGaloisAlgebraScalarExtensionRepresentation_surjective K L hdeg a ha⟩

/-- The cubic cyclic Brauer class becomes split over its defining cubic Galois extension. -/
theorem scalarExtensionBrauerMap_cubicCyclicGaloisAlgebraCSA_eq_split
    (hdeg : Module.finrank K L = 3) (a : K) (ha : a ≠ 0) :
    scalarExtensionBrauerMap K L
      (brauerClass (cubicCyclicGaloisAlgebraCSA K L hdeg a ha)) = brauerSplitClass L := by
  calc
    scalarExtensionBrauerMap K L
        (brauerClass (cubicCyclicGaloisAlgebraCSA K L hdeg a ha)) =
        brauerClass (scalarExtensionCSA (L := L)
          (cubicCyclicGaloisAlgebraCSA K L hdeg a ha)) := rfl
    _ = brauerClass (matrixFinCSA (scalarCSA L) 3) :=
      brauerClass_eq_of_algEquiv _ _
        (cubicCyclicGaloisAlgebraSplittingAlgEquiv K L hdeg a ha)
    _ = brauerSplitClass L := brauerClass_matrixFinCSA_scalar_eq 3

end GaloisForLFunctions.HTGeometry.ABHN
