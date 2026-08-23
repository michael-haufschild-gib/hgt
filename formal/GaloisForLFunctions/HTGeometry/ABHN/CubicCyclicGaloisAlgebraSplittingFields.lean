/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.CubicCyclicGaloisAlgebraScalarExtension

/-!
# Diagonal matrix units for cubic cyclic algebras over the defining field

For a cubic cyclic Galois extension, Lagrange interpolation in the three conjugates of a
non-fixed field element constructs the three diagonal matrix units in the scalar-extended
companion representation.  This is the first concrete splitting-field step; off-diagonal matrix
units and surjectivity are developed separately.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open Multiplicative
open scoped TensorProduct

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]

/-- The scalar-extended cubic companion representation contains `E₀₀`. -/
theorem cubicCyclicGaloisAlgebraScalarExtensionRepresentation_exists_e00
    (hdeg : Module.finrank K L = 3) (a : K) :
    ∃ e : L ⊗[K] cyclicGaloisAlgebra K L a,
      cubicCyclicGaloisAlgebraScalarExtensionRepresentation K L hdeg a e =
        !![(1 : L), 0, 0; 0, 0, 0; 0, 0, 0] := by
  let i0 : Fin (Module.finrank K L) := Fin.cast hdeg.symm 0
  let i1 : Fin (Module.finrank K L) := Fin.cast hdeg.symm 1
  obtain ⟨b, hb⟩ := cyclicGaloisGenerator_pow_exists_apply_ne K L i1 i0 (by
    intro h
    have hval := congrArg Fin.val h
    simp [i0, i1] at hval)
  have hb' : cyclicGaloisGenerator K L b ≠ b := by
    simpa [i0, i1, AlgEquiv.coe_pow] using hb
  let s := cyclicGaloisGenerator K L
  have hcub : s ^ 3 = 1 := by
    rw [← hdeg]
    exact cyclicGaloisGenerator_pow_finrank K L
  have hcube : s (s (s b)) = b := by
    change (s ^ 3) b = b
    rw [hcub]
    rfl
  have h20 : s (s b) ≠ b := by
    intro h
    apply hb'
    have hs := congrArg s h
    have : b = s b := by simpa [hcube] using hs
    exact this.symm
  have h21 : s (s b) ≠ s b := by
    intro h
    apply hb'
    have hs := congrArg s h
    have htemp : b = s (s b) := by simpa [hcube] using hs
    exact (htemp.trans h).symm
  let d : L := (b - s (s b)) * (b - s b)
  have hd : d ≠ 0 :=
    mul_ne_zero (sub_ne_zero.mpr h20.symm) (sub_ne_zero.mpr hb'.symm)
  have h10 : b - s b ≠ 0 := sub_ne_zero.mpr hb'.symm
  let e : L ⊗[K] cyclicGaloisAlgebra K L a :=
    d⁻¹ ⊗ₜ[K] cyclicGaloisAlgebraC K L a (b ^ 2) -
      ((s (s b) + s b) * d⁻¹) ⊗ₜ[K] cyclicGaloisAlgebraC K L a b +
        (s (s b) * s b * d⁻¹) ⊗ₜ[K] cyclicGaloisAlgebraC K L a 1
  refine ⟨e, ?_⟩
  dsimp [e]
  rw [map_add, map_sub,
    cubicCyclicGaloisAlgebraScalarExtensionRepresentation_C,
    cubicCyclicGaloisAlgebraScalarExtensionRepresentation_C,
    cubicCyclicGaloisAlgebraScalarExtensionRepresentation_C]
  ext i j
  fin_cases i <;> fin_cases j
  · simp [cubicCyclicCoefficientMatrix, d, pow_two]
    field_simp [hd, h10]
    ring
  · simp [cubicCyclicCoefficientMatrix]
  · simp [cubicCyclicCoefficientMatrix]
  · simp [cubicCyclicCoefficientMatrix]
  · simp [cubicCyclicCoefficientMatrix, d, s]
    field_simp [hd]
    ring
  · simp [cubicCyclicCoefficientMatrix]
  · simp [cubicCyclicCoefficientMatrix]
  · simp [cubicCyclicCoefficientMatrix]
  · simp [cubicCyclicCoefficientMatrix, d, s]
    field_simp [hd]
    ring

/-- The scalar-extended cubic companion representation contains `E₁₁`. -/
theorem cubicCyclicGaloisAlgebraScalarExtensionRepresentation_exists_e11
    (hdeg : Module.finrank K L = 3) (a : K) :
    ∃ e : L ⊗[K] cyclicGaloisAlgebra K L a,
      cubicCyclicGaloisAlgebraScalarExtensionRepresentation K L hdeg a e =
        !![(0 : L), 0, 0; 0, 1, 0; 0, 0, 0] := by
  let i0 : Fin (Module.finrank K L) := Fin.cast hdeg.symm 0
  let i1 : Fin (Module.finrank K L) := Fin.cast hdeg.symm 1
  obtain ⟨b, hb⟩ := cyclicGaloisGenerator_pow_exists_apply_ne K L i1 i0 (by
    intro h
    have hval := congrArg Fin.val h
    simp [i0, i1] at hval)
  have hb' : cyclicGaloisGenerator K L b ≠ b := by
    simpa [i0, i1, AlgEquiv.coe_pow] using hb
  let s := cyclicGaloisGenerator K L
  have hcub : s ^ 3 = 1 := by
    rw [← hdeg]
    exact cyclicGaloisGenerator_pow_finrank K L
  have hcube : s (s (s b)) = b := by
    change (s ^ 3) b = b
    rw [hcub]
    rfl
  have h20 : s (s b) ≠ b := by
    intro h
    apply hb'
    have hs := congrArg s h
    have : b = s b := by simpa [hcube] using hs
    exact this.symm
  have h21 : s (s b) ≠ s b := by
    intro h
    apply hb'
    have hs := congrArg s h
    have htemp : b = s (s b) := by simpa [hcube] using hs
    exact (htemp.trans h).symm
  let d : L := (s (s b) - b) * (s (s b) - s b)
  have hd : d ≠ 0 :=
    mul_ne_zero (sub_ne_zero.mpr h20) (sub_ne_zero.mpr h21)
  have h21z : s (s b) - s b ≠ 0 := sub_ne_zero.mpr h21
  let e : L ⊗[K] cyclicGaloisAlgebra K L a :=
    d⁻¹ ⊗ₜ[K] cyclicGaloisAlgebraC K L a (b ^ 2) -
      ((b + s b) * d⁻¹) ⊗ₜ[K] cyclicGaloisAlgebraC K L a b +
        (b * s b * d⁻¹) ⊗ₜ[K] cyclicGaloisAlgebraC K L a 1
  refine ⟨e, ?_⟩
  dsimp [e]
  rw [map_add, map_sub,
    cubicCyclicGaloisAlgebraScalarExtensionRepresentation_C,
    cubicCyclicGaloisAlgebraScalarExtensionRepresentation_C,
    cubicCyclicGaloisAlgebraScalarExtensionRepresentation_C]
  ext i j
  fin_cases i <;> fin_cases j
  · simp [cubicCyclicCoefficientMatrix, d, s]
    field_simp [hd]
    ring
  · simp [cubicCyclicCoefficientMatrix]
  · simp [cubicCyclicCoefficientMatrix]
  · simp [cubicCyclicCoefficientMatrix]
  · simp [cubicCyclicCoefficientMatrix, d, pow_two]
    field_simp [hd, h21z]
    ring
  · simp [cubicCyclicCoefficientMatrix]
  · simp [cubicCyclicCoefficientMatrix]
  · simp [cubicCyclicCoefficientMatrix]
  · simp [cubicCyclicCoefficientMatrix, d, s]
    field_simp [hd]
    ring

/-- The scalar-extended cubic companion representation contains `E₂₂`. -/
theorem cubicCyclicGaloisAlgebraScalarExtensionRepresentation_exists_e22
    (hdeg : Module.finrank K L = 3) (a : K) :
    ∃ e : L ⊗[K] cyclicGaloisAlgebra K L a,
      cubicCyclicGaloisAlgebraScalarExtensionRepresentation K L hdeg a e =
        !![(0 : L), 0, 0; 0, 0, 0; 0, 0, 1] := by
  let i0 : Fin (Module.finrank K L) := Fin.cast hdeg.symm 0
  let i1 : Fin (Module.finrank K L) := Fin.cast hdeg.symm 1
  obtain ⟨b, hb⟩ := cyclicGaloisGenerator_pow_exists_apply_ne K L i1 i0 (by
    intro h
    have hval := congrArg Fin.val h
    simp [i0, i1] at hval)
  have hb' : cyclicGaloisGenerator K L b ≠ b := by
    simpa [i0, i1, AlgEquiv.coe_pow] using hb
  let s := cyclicGaloisGenerator K L
  have hcub : s ^ 3 = 1 := by
    rw [← hdeg]
    exact cyclicGaloisGenerator_pow_finrank K L
  have hcube : s (s (s b)) = b := by
    change (s ^ 3) b = b
    rw [hcub]
    rfl
  have h20 : s (s b) ≠ b := by
    intro h
    apply hb'
    have hs := congrArg s h
    have : b = s b := by simpa [hcube] using hs
    exact this.symm
  have h21 : s (s b) ≠ s b := by
    intro h
    apply hb'
    have hs := congrArg s h
    have htemp : b = s (s b) := by simpa [hcube] using hs
    exact (htemp.trans h).symm
  let d : L := (s b - b) * (s b - s (s b))
  have hd : d ≠ 0 :=
    mul_ne_zero (sub_ne_zero.mpr hb') (sub_ne_zero.mpr h21.symm)
  have h01z : s b - b ≠ 0 := sub_ne_zero.mpr hb'
  have h22z : s b - s (s b) ≠ 0 := sub_ne_zero.mpr h21.symm
  let e : L ⊗[K] cyclicGaloisAlgebra K L a :=
    d⁻¹ ⊗ₜ[K] cyclicGaloisAlgebraC K L a (b ^ 2) -
      ((b + s (s b)) * d⁻¹) ⊗ₜ[K] cyclicGaloisAlgebraC K L a b +
        (b * s (s b) * d⁻¹) ⊗ₜ[K] cyclicGaloisAlgebraC K L a 1
  refine ⟨e, ?_⟩
  dsimp [e]
  rw [map_add, map_sub,
    cubicCyclicGaloisAlgebraScalarExtensionRepresentation_C,
    cubicCyclicGaloisAlgebraScalarExtensionRepresentation_C,
    cubicCyclicGaloisAlgebraScalarExtensionRepresentation_C]
  ext i j
  fin_cases i <;> fin_cases j
  · simp [cubicCyclicCoefficientMatrix, d, s]
    field_simp [hd]
    ring
  · simp [cubicCyclicCoefficientMatrix, d, s]
  · simp [cubicCyclicCoefficientMatrix]
  · simp [cubicCyclicCoefficientMatrix]
  · simp [cubicCyclicCoefficientMatrix, d, s]
    field_simp [hd]
    ring
  · simp [cubicCyclicCoefficientMatrix]
  · simp [cubicCyclicCoefficientMatrix]
  · simp [cubicCyclicCoefficientMatrix]
  · simp [cubicCyclicCoefficientMatrix, d, s, pow_two]
    field_simp [hd, h22z, h01z, s]
    ring

end GaloisForLFunctions.HTGeometry.ABHN
