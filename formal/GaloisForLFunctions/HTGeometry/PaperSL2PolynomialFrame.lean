import GaloisForLFunctions.HTGeometry.PaperStableCoordinate.FrameLiftUniqueness
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# Normalized polynomial SL₂ frames are determined by their quadric data

The source's determinant-frame uniqueness theorem applies to the native
special linear matrix group. Three quadratic polynomial observables,
together with the matrix at parameter zero, recover the entire family.
The parameter index type is arbitrary, so the result also applies to
several-parameter polynomial lifts and their composition laws.
-/

namespace GaloisForLFunctions.HTGeometry

open StableCoordinate

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The native determinant-one matrix, in the source's `a,d,b,c` order. -/
def paperSL2Frame (g : Matrix.SpecialLinearGroup (Fin 2) R) : FrameLift.Frame R where
  a := g 0 0
  d := g 1 0
  b := g 0 1
  c := g 1 1
  determinant := by
    simpa only [Matrix.det_fin_two] using g.det_coe

theorem paperSL2Frame_injective :
    Function.Injective (paperSL2Frame (R := R)) := by
  intro g h heq
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j
  · exact congrArg FrameLift.Frame.a heq
  · exact congrArg FrameLift.Frame.b heq
  · exact congrArg FrameLift.Frame.d heq
  · exact congrArg FrameLift.Frame.c heq

theorem paperSL2Frame_map (φ : R →+* S) (g : Matrix.SpecialLinearGroup (Fin 2) R) :
    paperSL2Frame (Matrix.SpecialLinearGroup.map φ g) =
      (paperSL2Frame g).map φ := rfl

/-- The three source quadric coordinates as native matrix observables. -/
def paperSL2QuadricPoint (g : Matrix.SpecialLinearGroup (Fin 2) R) : Fin 3 → R :=
  ![g 0 0 * g 0 1, g 1 0 * g 1 1, g 1 0 * g 0 1]

theorem paperSL2QuadricPoint_relation (g : Matrix.SpecialLinearGroup (Fin 2) R) :
    paperSL2QuadricPoint g 0 * paperSL2QuadricPoint g 1 =
      paperSL2QuadricPoint g 2 * (paperSL2QuadricPoint g 2 + 1) := by
  have h := (paperSL2Frame g).determinant
  dsimp only [paperSL2Frame] at h
  change (g 0 0 * g 0 1) * (g 1 0 * g 1 1) =
    (g 1 0 * g 0 1) * (g 1 0 * g 0 1 + 1)
  linear_combination g 1 0 * g 0 1 * h

/-- Polynomial observables plus one exact normalization of the native matrix family. -/
noncomputable def paperSL2NormalizedData {σ : Type*}
    (g : Matrix.SpecialLinearGroup (Fin 2) (MvPolynomial σ ℂ)) :
    (Fin 3 → MvPolynomial σ ℂ) × Matrix.SpecialLinearGroup (Fin 2) ℂ :=
  (paperSL2QuadricPoint g, Matrix.SpecialLinearGroup.map MvPolynomial.constantCoeff g)

/-- The normalized observation map loses no polynomial matrix family. -/
theorem paperSL2NormalizedData_injective {σ : Type*} :
    Function.Injective (paperSL2NormalizedData (σ := σ)) := by
  intro g h heq
  have hbase := congrArg Prod.fst heq
  have hzero := congrArg Prod.snd heq
  apply paperSL2Frame_injective
  apply FrameLift.normalized_polynomial_unique
  · exact ⟨congrFun hbase 0, congrFun hbase 1, congrFun hbase 2⟩
  · rw [← paperSL2Frame_map, ← paperSL2Frame_map]
    exact congrArg paperSL2Frame hzero

end GaloisForLFunctions.HTGeometry
