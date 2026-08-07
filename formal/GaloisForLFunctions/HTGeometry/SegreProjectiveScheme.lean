import GaloisForLFunctions.HTGeometry.SegreDiagonalRing
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper

/-!
# Proper Segre projective scheme

The balanced diagonal monoid algebra is generated in degree one by the pair coordinates proved in
`SegreDiagonalRing`.  Mathlib's `Proj` construction therefore applies and its general valuative
criterion proves properness over the degree-zero coefficient ring.
-/

namespace GaloisForLFunctions.HTGeometry

open AlgebraicGeometry

/-- Natural standard grading on the Segre diagonal ring. -/
noncomputable abbrev SegreGrading (R : Type*) [CommRing R] (m n : ℕ) :
    ℕ → Submodule R (SegreDiagonalRing R m n) :=
  AddMonoidAlgebra.gradeBy R (segreExponentDegree m n)

noncomputable instance segreGradeZeroScalarTower (R : Type*) [CommRing R] (m n : ℕ) :
    IsScalarTower R ((SegreGrading R m n) 0) (SegreDiagonalRing R m n) :=
  IsScalarTower.of_algebraMap_eq (R := R) (S := (SegreGrading R m n) 0)
    (A := SegreDiagonalRing R m n) (fun _ => rfl)

noncomputable instance segreDiagonalRing_finiteType_over_gradeZero
    (R : Type*) [CommRing R] (m n : ℕ) :
    Algebra.FiniteType ((SegreGrading R m n) 0) (SegreDiagonalRing R m n) :=
  Algebra.FiniteType.of_restrictScalars_finiteType R ((SegreGrading R m n) 0)
    (SegreDiagonalRing R m n)

/-- Projective scheme cut out by the Segre diagonal coordinate ring. -/
noncomputable abbrev SegreProjectiveScheme (R : Type*) [CommRing R] (m n : ℕ) :=
  Proj (SegreGrading R m n)

/-- **Projectivity/properness of the Segre compactification.** -/
theorem segreProjectiveScheme_isProper (R : Type*) [CommRing R] (m n : ℕ) :
    IsProper (Proj.toSpecZero (SegreGrading R m n)) := by
  infer_instance

end GaloisForLFunctions.HTGeometry
