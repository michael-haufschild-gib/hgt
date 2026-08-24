import GaloisForLFunctions.HTGeometry.HassePredicate
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisAlgebraHasseIntertwiners
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisAlgebraHasseIntertwinerCokernels
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisAlgebraHasseGeneralizedIntertwinerDimensions
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisAlgebraHasseIntertwinerInvariants

/-!
# Cyclic-algebra intertwiner defects at every completion

For two elements of a cyclic Brauer representative, the Sylvester operator `w ↦ xw - wy`
measures conjugacy-like comparison.  Failure of its equations, nonzero kernel, prescribed kernel
or cokernel dimensions, generalized eigenspace dimensions, and regular invariants persists at
every completion.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

/-- Insolubility of an inhomogeneous Sylvester equation over a number field persists everywhere. -/
theorem numberField_cyclicGaloisAlgebra_not_exists_intertwining_defect_eq_iff_forall_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (ha : a ≠ 0) (x y z : cyclicGaloisAlgebra K L a) :
    (¬ ∃ w, x * w - w * y = z) ↔ ∀ p : NumberFieldPlace K, ¬ ∃ w,
      numberFieldLocalScalarExtensionMap K p (cyclicGaloisAlgebraCSA K L a ha) x * w -
        w * numberFieldLocalScalarExtensionMap K p (cyclicGaloisAlgebraCSA K L a ha) y =
          numberFieldLocalScalarExtensionMap K p (cyclicGaloisAlgebraCSA K L a ha) z :=
  not_iff_forall_not_of_iff_exists
    (numberField_cyclicGaloisAlgebra_exists_intertwining_defect_eq_iff_exists_place
      K L a ha x y z)

/-- Insolubility of an inhomogeneous Sylvester equation over a function field persists. -/
theorem rationalFunction_cyclicGaloisAlgebra_not_exists_intertwining_defect_eq_iff_forall_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F) (ha : a ≠ 0) (x y z : cyclicGaloisAlgebra (RatFunc F) L a) :
    (¬ ∃ w, x * w - w * y = z) ↔ ∀ p : RationalFunctionPlace F, ¬ ∃ w,
      rationalFunctionLocalScalarExtensionMap F p
          (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x * w -
        w * rationalFunctionLocalScalarExtensionMap F p
          (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) y =
          rationalFunctionLocalScalarExtensionMap F p
            (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) z :=
  not_iff_forall_not_of_iff_exists
    (rationalFunction_cyclicGaloisAlgebra_exists_intertwining_defect_eq_iff_exists_place
      F L a ha x y z)

/-- Absence of a nonzero intertwiner over a number field persists everywhere. -/
theorem numberField_cyclicGaloisAlgebra_not_exists_nonzero_intertwiner_iff_forall_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (ha : a ≠ 0) (x y : cyclicGaloisAlgebra K L a) :
    (¬ ∃ z, z ≠ 0 ∧ x * z = z * y) ↔ ∀ p : NumberFieldPlace K, ¬ ∃ z, z ≠ 0 ∧
      numberFieldLocalScalarExtensionMap K p (cyclicGaloisAlgebraCSA K L a ha) x * z =
        z * numberFieldLocalScalarExtensionMap K p (cyclicGaloisAlgebraCSA K L a ha) y :=
  not_iff_forall_not_of_iff_exists
    (numberField_cyclicGaloisAlgebra_exists_nonzero_intertwiner_iff_exists_place
      K L a ha x y)

/-- Absence of a nonzero intertwiner over a function field persists everywhere. -/
theorem rationalFunction_cyclicGaloisAlgebra_not_exists_nonzero_intertwiner_iff_forall_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F) (ha : a ≠ 0) (x y : cyclicGaloisAlgebra (RatFunc F) L a) :
    (¬ ∃ z, z ≠ 0 ∧ x * z = z * y) ↔ ∀ p : RationalFunctionPlace F, ¬ ∃ z, z ≠ 0 ∧
      rationalFunctionLocalScalarExtensionMap F p
        (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x * z =
          z * rationalFunctionLocalScalarExtensionMap F p
            (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) y :=
  not_iff_forall_not_of_iff_exists
    (rationalFunction_cyclicGaloisAlgebra_exists_nonzero_intertwiner_iff_exists_place
      F L a ha x y)

/-- A wrong Sylvester-kernel dimension over a number field persists everywhere. -/
theorem numberField_cyclicGaloisAlgebra_intertwinerFinrank_ne_iff_forall_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (ha : a ≠ 0) (x y : cyclicGaloisAlgebra K L a) (d : ℕ) :
    Module.finrank K
      (LinearMap.ker (LinearMap.mulLeft K x - LinearMap.mulRight K y)) ≠ d ↔
      ∀ p : NumberFieldPlace K,
        Module.finrank (completion K p)
          (LinearMap.ker
            (LinearMap.mulLeft (completion K p)
              (numberFieldLocalScalarExtensionMap K p
                (cyclicGaloisAlgebraCSA K L a ha) x) -
              LinearMap.mulRight (completion K p)
                (numberFieldLocalScalarExtensionMap K p
                  (cyclicGaloisAlgebraCSA K L a ha) y))) ≠ d :=
  not_iff_forall_not_of_iff_exists
    (numberField_cyclicGaloisAlgebra_intertwinerFinrank_eq_iff_exists_place
      K L a ha x y d)

/-- A wrong Sylvester-kernel dimension over a function field persists everywhere. -/
theorem rationalFunction_cyclicGaloisAlgebra_intertwinerFinrank_ne_iff_forall_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F) (ha : a ≠ 0) (x y : cyclicGaloisAlgebra (RatFunc F) L a) (d : ℕ) :
    Module.finrank (RatFunc F)
      (LinearMap.ker
        (LinearMap.mulLeft (RatFunc F) x - LinearMap.mulRight (RatFunc F) y)) ≠ d ↔
      ∀ p : RationalFunctionPlace F,
        Module.finrank (rationalFunctionCompletion F p)
          (LinearMap.ker
            (LinearMap.mulLeft (rationalFunctionCompletion F p)
              (rationalFunctionLocalScalarExtensionMap F p
                (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x) -
              LinearMap.mulRight (rationalFunctionCompletion F p)
                (rationalFunctionLocalScalarExtensionMap F p
                  (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) y))) ≠ d :=
  not_iff_forall_not_of_iff_exists
    (rationalFunction_cyclicGaloisAlgebra_intertwinerFinrank_eq_iff_exists_place
      F L a ha x y d)

/-- A wrong Sylvester-cokernel dimension over a number field persists everywhere. -/
theorem numberField_cyclicGaloisAlgebra_intertwinerCokernelFinrank_ne_iff_forall_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (ha : a ≠ 0) (x y : cyclicGaloisAlgebra K L a) (d : ℕ) :
    Module.finrank K
      (cyclicGaloisAlgebra K L a ⧸ LinearMap.range
        (LinearMap.mulLeft K x - LinearMap.mulRight K y)) ≠ d ↔
      ∀ p : NumberFieldPlace K,
        Module.finrank (completion K p)
          ((completion K p ⊗[K] cyclicGaloisAlgebra K L a) ⧸ LinearMap.range
            (LinearMap.mulLeft (completion K p)
              (numberFieldLocalScalarExtensionMap K p
                (cyclicGaloisAlgebraCSA K L a ha) x) -
              LinearMap.mulRight (completion K p)
                (numberFieldLocalScalarExtensionMap K p
                  (cyclicGaloisAlgebraCSA K L a ha) y))) ≠ d :=
  not_iff_forall_not_of_iff_exists
    (numberField_cyclicGaloisAlgebra_intertwinerCokernelFinrank_eq_iff_exists_place
      K L a ha x y d)

/-- A wrong Sylvester-cokernel dimension over a function field persists everywhere. -/
theorem rationalFunction_cyclicGaloisAlgebra_intertwinerCokernelFinrank_ne_iff_forall_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F) (ha : a ≠ 0) (x y : cyclicGaloisAlgebra (RatFunc F) L a) (d : ℕ) :
    Module.finrank (RatFunc F)
      (cyclicGaloisAlgebra (RatFunc F) L a ⧸ LinearMap.range
        (LinearMap.mulLeft (RatFunc F) x - LinearMap.mulRight (RatFunc F) y)) ≠ d ↔
      ∀ p : RationalFunctionPlace F,
        Module.finrank (rationalFunctionCompletion F p)
          ((rationalFunctionCompletion F p ⊗[RatFunc F]
              cyclicGaloisAlgebra (RatFunc F) L a) ⧸ LinearMap.range
            (LinearMap.mulLeft (rationalFunctionCompletion F p)
              (rationalFunctionLocalScalarExtensionMap F p
                (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x) -
              LinearMap.mulRight (rationalFunctionCompletion F p)
                (rationalFunctionLocalScalarExtensionMap F p
                  (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) y))) ≠ d :=
  not_iff_forall_not_of_iff_exists
    (rationalFunction_cyclicGaloisAlgebra_intertwinerCokernelFinrank_eq_iff_exists_place
      F L a ha x y d)

/-- A wrong generalized Sylvester-kernel dimension over a number field persists everywhere. -/
theorem numberField_cyclicGaloisAlgebra_intertwinerGeneralizedEigenKernel_finrank_ne_iff_forall_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (ha : a ≠ 0) (x y : cyclicGaloisAlgebra K L a) (c : K) (n d : ℕ) :
    Module.finrank K (LinearMap.ker
      ((LinearMap.mulLeft K x - LinearMap.mulRight K y - c • LinearMap.id) ^ n)) ≠ d ↔
      ∀ p : NumberFieldPlace K,
        Module.finrank (completion K p) (LinearMap.ker
          ((LinearMap.mulLeft (completion K p)
            (numberFieldLocalScalarExtensionMap K p
              (cyclicGaloisAlgebraCSA K L a ha) x) -
            LinearMap.mulRight (completion K p)
              (numberFieldLocalScalarExtensionMap K p
                (cyclicGaloisAlgebraCSA K L a ha) y) -
            (algebraMap K (completion K p) c) • LinearMap.id) ^ n)) ≠ d :=
  not_iff_forall_not_of_iff_exists
    (numberField_cyclicGaloisAlgebra_intertwinerGeneralizedEigenKernel_finrank_eq_iff_exists_place
      K L a ha x y c n d)

/-- A wrong generalized Sylvester-kernel dimension over a function field persists everywhere. -/
theorem rationalFunction_cyclicGaloisAlgebra_intertwinerGeneralizedEigenKernel_finrank_ne_iff_forall_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F) (ha : a ≠ 0) (x y : cyclicGaloisAlgebra (RatFunc F) L a)
    (c : RatFunc F) (n d : ℕ) :
    Module.finrank (RatFunc F) (LinearMap.ker
      ((LinearMap.mulLeft (RatFunc F) x - LinearMap.mulRight (RatFunc F) y -
        c • LinearMap.id) ^ n)) ≠ d ↔ ∀ p : RationalFunctionPlace F,
      Module.finrank (rationalFunctionCompletion F p) (LinearMap.ker
        ((LinearMap.mulLeft (rationalFunctionCompletion F p)
          (rationalFunctionLocalScalarExtensionMap F p
            (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x) -
          LinearMap.mulRight (rationalFunctionCompletion F p)
            (rationalFunctionLocalScalarExtensionMap F p
              (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) y) -
          (algebraMap (RatFunc F) (rationalFunctionCompletion F p) c) •
            LinearMap.id) ^ n)) ≠ d :=
  not_iff_forall_not_of_iff_exists
    (rationalFunction_cyclicGaloisAlgebra_intertwinerGeneralizedEigenKernel_finrank_eq_iff_exists_place
      F L a ha x y c n d)

/-- A wrong Sylvester characteristic polynomial over a number field persists everywhere. -/
theorem numberField_cyclicGaloisAlgebra_intertwinerCharpoly_ne_iff_forall_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (ha : a ≠ 0) (x y : cyclicGaloisAlgebra K L a) (q : Polynomial K) :
    (LinearMap.mulLeft K x - LinearMap.mulRight K y).charpoly ≠ q ↔
      ∀ p : NumberFieldPlace K,
        (LinearMap.mulLeft (completion K p)
          (numberFieldLocalScalarExtensionMap K p
            (cyclicGaloisAlgebraCSA K L a ha) x) -
          LinearMap.mulRight (completion K p)
            (numberFieldLocalScalarExtensionMap K p
              (cyclicGaloisAlgebraCSA K L a ha) y)).charpoly ≠
            q.map (algebraMap K (completion K p)) :=
  not_iff_forall_not_of_iff_exists
    (numberField_cyclicGaloisAlgebra_intertwinerCharpoly_eq_iff_exists_place
      K L a ha x y q)

/-- A wrong Sylvester characteristic polynomial over a function field persists everywhere. -/
theorem rationalFunction_cyclicGaloisAlgebra_intertwinerCharpoly_ne_iff_forall_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F) (ha : a ≠ 0) (x y : cyclicGaloisAlgebra (RatFunc F) L a)
    (q : Polynomial (RatFunc F)) :
    (LinearMap.mulLeft (RatFunc F) x - LinearMap.mulRight (RatFunc F) y).charpoly ≠ q ↔
      ∀ p : RationalFunctionPlace F,
        (LinearMap.mulLeft (rationalFunctionCompletion F p)
          (rationalFunctionLocalScalarExtensionMap F p
            (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x) -
          LinearMap.mulRight (rationalFunctionCompletion F p)
            (rationalFunctionLocalScalarExtensionMap F p
              (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) y)).charpoly ≠
            q.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p)) :=
  not_iff_forall_not_of_iff_exists
    (rationalFunction_cyclicGaloisAlgebra_intertwinerCharpoly_eq_iff_exists_place
      F L a ha x y q)

/-- A wrong Sylvester trace over a number field persists everywhere. -/
theorem numberField_cyclicGaloisAlgebra_intertwinerTrace_ne_iff_forall_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (ha : a ≠ 0) (x y : cyclicGaloisAlgebra K L a) (c : K) :
    LinearMap.trace K (cyclicGaloisAlgebra K L a)
      (LinearMap.mulLeft K x - LinearMap.mulRight K y) ≠ c ↔
      ∀ p : NumberFieldPlace K,
        LinearMap.trace (completion K p)
          (completion K p ⊗[K] cyclicGaloisAlgebra K L a)
          (LinearMap.mulLeft (completion K p)
            (numberFieldLocalScalarExtensionMap K p
              (cyclicGaloisAlgebraCSA K L a ha) x) -
            LinearMap.mulRight (completion K p)
              (numberFieldLocalScalarExtensionMap K p
                (cyclicGaloisAlgebraCSA K L a ha) y)) ≠
          algebraMap K (completion K p) c :=
  not_iff_forall_not_of_iff_exists
    (numberField_cyclicGaloisAlgebra_intertwinerTrace_eq_iff_exists_place
      K L a ha x y c)

/-- A wrong Sylvester trace over a function field persists everywhere. -/
theorem rationalFunction_cyclicGaloisAlgebra_intertwinerTrace_ne_iff_forall_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F) (ha : a ≠ 0) (x y : cyclicGaloisAlgebra (RatFunc F) L a)
    (c : RatFunc F) :
    LinearMap.trace (RatFunc F) (cyclicGaloisAlgebra (RatFunc F) L a)
      (LinearMap.mulLeft (RatFunc F) x - LinearMap.mulRight (RatFunc F) y) ≠ c ↔
      ∀ p : RationalFunctionPlace F,
        LinearMap.trace (rationalFunctionCompletion F p)
          (rationalFunctionCompletion F p ⊗[RatFunc F]
            cyclicGaloisAlgebra (RatFunc F) L a)
          (LinearMap.mulLeft (rationalFunctionCompletion F p)
            (rationalFunctionLocalScalarExtensionMap F p
              (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x) -
            LinearMap.mulRight (rationalFunctionCompletion F p)
              (rationalFunctionLocalScalarExtensionMap F p
                (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) y)) ≠
          algebraMap (RatFunc F) (rationalFunctionCompletion F p) c :=
  not_iff_forall_not_of_iff_exists
    (rationalFunction_cyclicGaloisAlgebra_intertwinerTrace_eq_iff_exists_place
      F L a ha x y c)

/-- A wrong Sylvester determinant over a number field persists everywhere. -/
theorem numberField_cyclicGaloisAlgebra_intertwinerDet_ne_iff_forall_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (ha : a ≠ 0) (x y : cyclicGaloisAlgebra K L a) (c : K) :
    LinearMap.det (LinearMap.mulLeft K x - LinearMap.mulRight K y) ≠ c ↔
      ∀ p : NumberFieldPlace K,
        LinearMap.det (LinearMap.mulLeft (completion K p)
          (numberFieldLocalScalarExtensionMap K p
            (cyclicGaloisAlgebraCSA K L a ha) x) -
          LinearMap.mulRight (completion K p)
            (numberFieldLocalScalarExtensionMap K p
              (cyclicGaloisAlgebraCSA K L a ha) y)) ≠
          algebraMap K (completion K p) c :=
  not_iff_forall_not_of_iff_exists
    (numberField_cyclicGaloisAlgebra_intertwinerDet_eq_iff_exists_place
      K L a ha x y c)

/-- A wrong Sylvester determinant over a function field persists everywhere. -/
theorem rationalFunction_cyclicGaloisAlgebra_intertwinerDet_ne_iff_forall_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F) (ha : a ≠ 0) (x y : cyclicGaloisAlgebra (RatFunc F) L a)
    (c : RatFunc F) :
    LinearMap.det
      (LinearMap.mulLeft (RatFunc F) x - LinearMap.mulRight (RatFunc F) y) ≠ c ↔
      ∀ p : RationalFunctionPlace F,
        LinearMap.det (LinearMap.mulLeft (rationalFunctionCompletion F p)
          (rationalFunctionLocalScalarExtensionMap F p
            (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x) -
          LinearMap.mulRight (rationalFunctionCompletion F p)
            (rationalFunctionLocalScalarExtensionMap F p
              (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) y)) ≠
          algebraMap (RatFunc F) (rationalFunctionCompletion F p) c :=
  not_iff_forall_not_of_iff_exists
    (rationalFunction_cyclicGaloisAlgebra_intertwinerDet_eq_iff_exists_place
      F L a ha x y c)

end GaloisForLFunctions.HTGeometry.ABHN
