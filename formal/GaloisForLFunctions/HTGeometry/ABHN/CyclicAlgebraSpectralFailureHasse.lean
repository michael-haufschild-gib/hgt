import GaloisForLFunctions.HTGeometry.HassePredicate
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisAlgebraHasseRegularInvariants
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisAlgebraHasseSpectral
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisAlgebraHasseEigenvectors
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisAlgebraHasseGeneralizedEigenDimensions

/-!
# Cyclic-algebra spectral defects at every completion

The left regular representation converts elements of an explicit cyclic Brauer representative
into linear operators.  Failure of prescribed characteristic polynomial, trace, norm,
separability, eigenvalue occurrence, or generalized eigenspace dimension persists at every
completion.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

/-- A wrong regular characteristic polynomial over a number field stays wrong everywhere. -/
theorem numberField_cyclicGaloisAlgebra_regularCharpoly_ne_iff_forall_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (ha : a ≠ 0) (x : cyclicGaloisAlgebra K L a) (q : Polynomial K) :
    (LinearMap.mulLeft K x).charpoly ≠ q ↔ ∀ v : NumberFieldPlace K,
      (LinearMap.mulLeft (completion K v)
        (numberFieldLocalScalarExtensionMap K v
          (cyclicGaloisAlgebraCSA K L a ha) x)).charpoly ≠
        q.map (algebraMap K (completion K v)) :=
  not_iff_forall_not_of_iff_exists
    (numberField_cyclicGaloisAlgebra_regularCharpoly_eq_iff_exists_place K L a ha x q)

/-- A wrong regular characteristic polynomial over a function field stays wrong everywhere. -/
theorem rationalFunction_cyclicGaloisAlgebra_regularCharpoly_ne_iff_forall_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F) (ha : a ≠ 0) (x : cyclicGaloisAlgebra (RatFunc F) L a)
    (q : Polynomial (RatFunc F)) :
    (LinearMap.mulLeft (RatFunc F) x).charpoly ≠ q ↔
      ∀ v : RationalFunctionPlace F,
        (LinearMap.mulLeft (rationalFunctionCompletion F v)
          (rationalFunctionLocalScalarExtensionMap F v
            (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x)).charpoly ≠
          q.map (algebraMap (RatFunc F) (rationalFunctionCompletion F v)) :=
  not_iff_forall_not_of_iff_exists
    (rationalFunction_cyclicGaloisAlgebra_regularCharpoly_eq_iff_exists_place
      F L a ha x q)

/-- A wrong regular trace over a number field stays wrong everywhere. -/
theorem numberField_cyclicGaloisAlgebra_regularTrace_ne_iff_forall_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a c : K) (ha : a ≠ 0) (x : cyclicGaloisAlgebra K L a) :
    LinearMap.trace K (cyclicGaloisAlgebra K L a) (LinearMap.mulLeft K x) ≠ c ↔
      ∀ p : NumberFieldPlace K,
        LinearMap.trace (completion K p)
          (completion K p ⊗[K] cyclicGaloisAlgebra K L a)
          (LinearMap.mulLeft (completion K p)
            (numberFieldLocalScalarExtensionMap K p
              (cyclicGaloisAlgebraCSA K L a ha) x)) ≠
          algebraMap K (completion K p) c :=
  not_iff_forall_not_of_iff_exists
    (numberField_cyclicGaloisAlgebra_regularTrace_eq_iff_exists_place K L a c ha x)

/-- A wrong regular trace over a function field stays wrong everywhere. -/
theorem rationalFunction_cyclicGaloisAlgebra_regularTrace_ne_iff_forall_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a c : RatFunc F) (ha : a ≠ 0) (x : cyclicGaloisAlgebra (RatFunc F) L a) :
    LinearMap.trace (RatFunc F) (cyclicGaloisAlgebra (RatFunc F) L a)
      (LinearMap.mulLeft (RatFunc F) x) ≠ c ↔ ∀ p : RationalFunctionPlace F,
      LinearMap.trace (rationalFunctionCompletion F p)
        (rationalFunctionCompletion F p ⊗[RatFunc F]
          cyclicGaloisAlgebra (RatFunc F) L a)
        (LinearMap.mulLeft (rationalFunctionCompletion F p)
          (rationalFunctionLocalScalarExtensionMap F p
            (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x)) ≠
          algebraMap (RatFunc F) (rationalFunctionCompletion F p) c :=
  not_iff_forall_not_of_iff_exists
    (rationalFunction_cyclicGaloisAlgebra_regularTrace_eq_iff_exists_place F L a c ha x)

/-- A wrong regular norm over a number field stays wrong everywhere. -/
theorem numberField_cyclicGaloisAlgebra_regularNorm_ne_iff_forall_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a c : K) (ha : a ≠ 0) (x : cyclicGaloisAlgebra K L a) :
    LinearMap.det (LinearMap.mulLeft K x) ≠ c ↔ ∀ p : NumberFieldPlace K,
      LinearMap.det (LinearMap.mulLeft (completion K p)
        (numberFieldLocalScalarExtensionMap K p
          (cyclicGaloisAlgebraCSA K L a ha) x)) ≠
        algebraMap K (completion K p) c :=
  not_iff_forall_not_of_iff_exists
    (numberField_cyclicGaloisAlgebra_regularNorm_eq_iff_exists_place K L a c ha x)

/-- A wrong regular norm over a function field stays wrong everywhere. -/
theorem rationalFunction_cyclicGaloisAlgebra_regularNorm_ne_iff_forall_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a c : RatFunc F) (ha : a ≠ 0) (x : cyclicGaloisAlgebra (RatFunc F) L a) :
    LinearMap.det (LinearMap.mulLeft (RatFunc F) x) ≠ c ↔
      ∀ p : RationalFunctionPlace F,
        LinearMap.det (LinearMap.mulLeft (rationalFunctionCompletion F p)
          (rationalFunctionLocalScalarExtensionMap F p
            (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x)) ≠
          algebraMap (RatFunc F) (rationalFunctionCompletion F p) c :=
  not_iff_forall_not_of_iff_exists
    (rationalFunction_cyclicGaloisAlgebra_regularNorm_eq_iff_exists_place F L a c ha x)

/-- Inseparability of the regular characteristic polynomial over a number field persists. -/
theorem numberField_cyclicGaloisAlgebra_regularCharpoly_not_separable_iff_forall_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (ha : a ≠ 0) (x : cyclicGaloisAlgebra K L a) :
    ¬ (LinearMap.mulLeft K x).charpoly.Separable ↔ ∀ p : NumberFieldPlace K,
      ¬ (LinearMap.mulLeft (completion K p)
        (numberFieldLocalScalarExtensionMap K p
          (cyclicGaloisAlgebraCSA K L a ha) x)).charpoly.Separable :=
  not_iff_forall_not_of_iff_exists
    (numberField_cyclicGaloisAlgebra_regularCharpoly_separable_iff_exists_place K L a ha x)

/-- Inseparability of the regular characteristic polynomial over a function field persists. -/
theorem rationalFunction_cyclicGaloisAlgebra_regularCharpoly_not_separable_iff_forall_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F) (ha : a ≠ 0) (x : cyclicGaloisAlgebra (RatFunc F) L a) :
    ¬ (LinearMap.mulLeft (RatFunc F) x).charpoly.Separable ↔
      ∀ p : RationalFunctionPlace F,
        ¬ (LinearMap.mulLeft (rationalFunctionCompletion F p)
          (rationalFunctionLocalScalarExtensionMap F p
            (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x)).charpoly.Separable :=
  not_iff_forall_not_of_iff_exists
    (rationalFunction_cyclicGaloisAlgebra_regularCharpoly_separable_iff_exists_place
      F L a ha x)

/-- Absence of a regular eigenvalue over a number field persists everywhere. -/
theorem numberField_cyclicGaloisAlgebra_mulLeft_eigenKernel_eq_bot_iff_forall_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (ha : a ≠ 0) (x : cyclicGaloisAlgebra K L a) (c : K) :
    LinearMap.ker (LinearMap.mulLeft K x - c • LinearMap.id) = ⊥ ↔
      ∀ p : NumberFieldPlace K,
        LinearMap.ker (LinearMap.mulLeft (completion K p)
          (numberFieldLocalScalarExtensionMap K p
            (cyclicGaloisAlgebraCSA K L a ha) x) -
          (algebraMap K (completion K p) c) • LinearMap.id) = ⊥ := by
  simpa only [not_ne_iff] using not_iff_forall_not_of_iff_exists
    (numberField_cyclicGaloisAlgebra_mulLeft_eigenKernel_ne_bot_iff_exists_place
      K L a ha x c)

/-- Absence of a regular eigenvalue over a function field persists everywhere. -/
theorem rationalFunction_cyclicGaloisAlgebra_mulLeft_eigenKernel_eq_bot_iff_forall_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F) (ha : a ≠ 0) (x : cyclicGaloisAlgebra (RatFunc F) L a) (c : RatFunc F) :
    LinearMap.ker (LinearMap.mulLeft (RatFunc F) x - c • LinearMap.id) = ⊥ ↔
      ∀ p : RationalFunctionPlace F,
        LinearMap.ker (LinearMap.mulLeft (rationalFunctionCompletion F p)
          (rationalFunctionLocalScalarExtensionMap F p
            (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x) -
          (algebraMap (RatFunc F) (rationalFunctionCompletion F p) c) • LinearMap.id) = ⊥ := by
  simpa only [not_ne_iff] using not_iff_forall_not_of_iff_exists
    (rationalFunction_cyclicGaloisAlgebra_mulLeft_eigenKernel_ne_bot_iff_exists_place
      F L a ha x c)

/-- A wrong generalized regular-eigenspace dimension over a number field persists everywhere. -/
theorem numberField_cyclicGaloisAlgebra_mulLeft_generalizedEigenKernel_finrank_ne_iff_forall_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (ha : a ≠ 0) (x : cyclicGaloisAlgebra K L a) (c : K) (n d : ℕ) :
    Module.finrank K (LinearMap.ker ((LinearMap.mulLeft K x - c • LinearMap.id) ^ n)) ≠ d ↔
      ∀ p : NumberFieldPlace K,
        Module.finrank (completion K p) (LinearMap.ker
          ((LinearMap.mulLeft (completion K p)
            (numberFieldLocalScalarExtensionMap K p
              (cyclicGaloisAlgebraCSA K L a ha) x) -
            (algebraMap K (completion K p) c) • LinearMap.id) ^ n)) ≠ d :=
  not_iff_forall_not_of_iff_exists
    (numberField_cyclicGaloisAlgebra_mulLeft_generalizedEigenKernel_finrank_eq_iff_exists_place
      K L a ha x c n d)

/-- A wrong generalized regular-eigenspace dimension over a function field persists everywhere. -/
theorem rationalFunction_cyclicGaloisAlgebra_mulLeft_generalizedEigenKernel_finrank_ne_iff_forall_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F) (ha : a ≠ 0) (x : cyclicGaloisAlgebra (RatFunc F) L a)
    (c : RatFunc F) (n d : ℕ) :
    Module.finrank (RatFunc F) (LinearMap.ker
      ((LinearMap.mulLeft (RatFunc F) x - c • LinearMap.id) ^ n)) ≠ d ↔
      ∀ p : RationalFunctionPlace F,
        Module.finrank (rationalFunctionCompletion F p) (LinearMap.ker
          ((LinearMap.mulLeft (rationalFunctionCompletion F p)
            (rationalFunctionLocalScalarExtensionMap F p
              (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x) -
            (algebraMap (RatFunc F) (rationalFunctionCompletion F p) c) •
              LinearMap.id) ^ n)) ≠ d :=
  not_iff_forall_not_of_iff_exists
    (rationalFunction_cyclicGaloisAlgebra_mulLeft_generalizedEigenKernel_finrank_eq_iff_exists_place
      F L a ha x c n d)

end GaloisForLFunctions.HTGeometry.ABHN
