import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteField.MobiusFrobenius
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# Special-linear symmetries of the Frobenius curve

For a field with `q` elements, the homogeneous equation
`u^q v - u v^q = w^(q+1)` is preserved by `SL₂` acting on `(u,v)` and
fixing `w`. The action is defined over every algebra of the base field,
including extension fields containing geometric points of the curve.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
variable (K A : Type*) [Field K] [Fintype K] [CommRing A] [Algebra K A]

/-- The affine cone over the homogeneous Frobenius curve. -/
def frobeniusCurveCone :=
  {p : (Fin 2 → A) × A //
    p.1 0 ^ Fintype.card K * p.1 1 - p.1 0 * p.1 1 ^ Fintype.card K =
      p.2 ^ (Fintype.card K + 1)}

variable {K A}

/-- Determinant-one matrices preserve the binary Frobenius form after scalar extension. -/
theorem frobeniusForm_specialLinear_invariant
    (g : Matrix.SpecialLinearGroup (Fin 2) K) (v : Fin 2 → A) :
    let w := Matrix.SpecialLinearGroup.map (algebraMap K A) g • v
    w 0 ^ Fintype.card K * w 1 - w 0 * w 1 ^ Fintype.card K =
      v 0 ^ Fintype.card K * v 1 - v 0 * v 1 ^ Fintype.card K := by
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using g.det_coe
  have h := finiteField_frobeniusForm_transform (g 0 0) (g 0 1) (g 1 0) (g 1 1)
    (v 0) (v 1)
  rw [hdet, map_one, one_mul] at h
  change (∑ j : Fin 2, algebraMap K A (g 0 j) * v j) ^ Fintype.card K *
      (∑ j : Fin 2, algebraMap K A (g 1 j) * v j) -
    (∑ j : Fin 2, algebraMap K A (g 0 j) * v j) *
      (∑ j : Fin 2, algebraMap K A (g 1 j) * v j) ^ Fintype.card K = _
  simpa only [Fin.sum_univ_two] using h

/-- The linear change of the first two coordinates preserves the full cone equation. -/
def frobeniusCurveConeMap (g : Matrix.SpecialLinearGroup (Fin 2) K)
    (p : frobeniusCurveCone K A) : frobeniusCurveCone K A :=
  ⟨(Matrix.SpecialLinearGroup.map (algebraMap K A) g • p.val.1, p.val.2),
    (frobeniusForm_specialLinear_invariant g p.val.1).trans p.property⟩

/-- The preserving coordinate changes form a group action, with inverse given by the inverse matrix. -/
instance frobeniusCurveConeMulAction :
    MulAction (Matrix.SpecialLinearGroup (Fin 2) K) (frobeniusCurveCone K A) where
  smul := frobeniusCurveConeMap
  one_smul p := by
    apply Subtype.ext
    change (Matrix.SpecialLinearGroup.map (algebraMap K A) 1 • p.val.1, p.val.2) = p.val
    rw [map_one, one_smul]
  mul_smul g h p := by
    apply Subtype.ext
    change (Matrix.SpecialLinearGroup.map (algebraMap K A) (g * h) • p.val.1, p.val.2) =
      (Matrix.SpecialLinearGroup.map (algebraMap K A) g •
        (Matrix.SpecialLinearGroup.map (algebraMap K A) h • p.val.1), p.val.2)
    rw [map_mul, mul_smul]

/-- The covering coordinate is fixed by every special-linear symmetry. -/
theorem frobeniusCurveCone_smul_last (g : Matrix.SpecialLinearGroup (Fin 2) K)
    (p : frobeniusCurveCone K A) : (g • p).val.2 = p.val.2 := rfl

end GaloisForLFunctions.ArithmeticHarmonicAnalysis
