import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraIntertwinerDimensions
import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraIntertwinerCokernels
import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraIntertwinerInvariants
import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraGeneralizedIntertwinerDimensions

/-!
# Persistence of spectral mismatches at every completion

Scalar extension preserves the exact spectral data of Sylvester operators attached to a central
simple algebra.  Consequently, a wrong global kernel dimension, cokernel dimension, generalized
eigenspace dimension, characteristic polynomial, trace, or determinant remains wrong at every
place.  These statements isolate route-neutral local obstruction terms for spectral applications.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

universe u w

/-- A wrong number-field intertwiner-space dimension remains wrong at every completion. -/
theorem numberField_intertwiner_ker_finrank_ne_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (A : CSA.{u, w} K) (a b : A.carrier) (d : ℕ) :
    Module.finrank K (LinearMap.ker (LinearMap.mulLeft K a - LinearMap.mulRight K b)) ≠ d ↔
      ∀ p : NumberFieldPlace K,
        Module.finrank (completion K p)
          (LinearMap.ker (LinearMap.mulLeft (completion K p)
            (numberFieldLocalScalarExtensionMap K p A a) - LinearMap.mulRight (completion K p)
              (numberFieldLocalScalarExtensionMap K p A b))) ≠ d := by
  have h := not_congr
    (numberFieldLocalScalarExtensionMap_intertwiner_ker_finrank_eq_iff_exists_place K A a b d)
  simpa only [not_exists] using h

/-- A wrong function-field intertwiner-space dimension remains wrong at every completion. -/
theorem rationalFunction_intertwiner_ker_finrank_ne_iff_forall_place
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, w} (RatFunc F))
    (a b : A.carrier) (d : ℕ) :
    Module.finrank (RatFunc F)
      (LinearMap.ker (LinearMap.mulLeft (RatFunc F) a - LinearMap.mulRight (RatFunc F) b)) ≠ d ↔
      ∀ p : RationalFunctionPlace F,
        Module.finrank (rationalFunctionCompletion F p)
          (LinearMap.ker (LinearMap.mulLeft (rationalFunctionCompletion F p)
            (rationalFunctionLocalScalarExtensionMap F p A a) -
              LinearMap.mulRight (rationalFunctionCompletion F p)
                (rationalFunctionLocalScalarExtensionMap F p A b))) ≠ d := by
  have h := not_congr
    (rationalFunctionLocalScalarExtensionMap_intertwiner_ker_finrank_eq_iff_exists_place
      F A a b d)
  simpa only [not_exists] using h

/-- A wrong number-field Sylvester-cokernel dimension remains wrong at every completion. -/
theorem numberField_intertwiner_cokernel_finrank_ne_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (A : CSA.{u, w} K) (a b : A.carrier) (d : ℕ) :
    Module.finrank K (A.carrier ⧸ LinearMap.range
      (LinearMap.mulLeft K a - LinearMap.mulRight K b)) ≠ d ↔
      ∀ p : NumberFieldPlace K,
        Module.finrank (completion K p) ((completion K p ⊗[K] A.carrier) ⧸ LinearMap.range
          (LinearMap.mulLeft (completion K p) (numberFieldLocalScalarExtensionMap K p A a) -
            LinearMap.mulRight (completion K p)
              (numberFieldLocalScalarExtensionMap K p A b))) ≠ d := by
  have h := not_congr
    (numberFieldLocalScalarExtensionMap_intertwiner_cokernel_finrank_eq_iff_exists_place
      K A a b d)
  simpa only [not_exists] using h

/-- A wrong function-field Sylvester-cokernel dimension remains wrong at every completion. -/
theorem rationalFunction_intertwiner_cokernel_finrank_ne_iff_forall_place
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, w} (RatFunc F))
    (a b : A.carrier) (d : ℕ) :
    Module.finrank (RatFunc F) (A.carrier ⧸ LinearMap.range
      (LinearMap.mulLeft (RatFunc F) a - LinearMap.mulRight (RatFunc F) b)) ≠ d ↔
      ∀ p : RationalFunctionPlace F,
        Module.finrank (rationalFunctionCompletion F p)
          ((rationalFunctionCompletion F p ⊗[RatFunc F] A.carrier) ⧸ LinearMap.range
            (LinearMap.mulLeft (rationalFunctionCompletion F p)
              (rationalFunctionLocalScalarExtensionMap F p A a) -
              LinearMap.mulRight (rationalFunctionCompletion F p)
                (rationalFunctionLocalScalarExtensionMap F p A b))) ≠ d := by
  have h := not_congr
    (rationalFunctionLocalScalarExtensionMap_intertwiner_cokernel_finrank_eq_iff_exists_place
      F A a b d)
  simpa only [not_exists] using h

/-- A wrong number-field generalized Sylvester eigenspace dimension persists everywhere. -/
theorem numberField_intertwiner_generalizedEigenKernel_finrank_ne_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (A : CSA.{u, w} K) (a b : A.carrier) (c : K)
    (n d : ℕ) :
    Module.finrank K (LinearMap.ker
      ((LinearMap.mulLeft K a - LinearMap.mulRight K b - c • LinearMap.id) ^ n)) ≠ d ↔
      ∀ p : NumberFieldPlace K,
        Module.finrank (completion K p) (LinearMap.ker
          ((LinearMap.mulLeft (completion K p) (numberFieldLocalScalarExtensionMap K p A a) -
            LinearMap.mulRight (completion K p) (numberFieldLocalScalarExtensionMap K p A b) -
            (algebraMap K (completion K p) c) • LinearMap.id) ^ n)) ≠ d := by
  have h := not_congr
    (numberFieldLocalScalarExtensionMap_intertwiner_generalizedEigenKernel_finrank_eq_iff_exists_place
      K A a b c n d)
  simpa only [not_exists] using h

/-- A wrong function-field generalized Sylvester eigenspace dimension persists everywhere. -/
theorem rationalFunction_intertwiner_generalizedEigenKernel_finrank_ne_iff_forall_place
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, w} (RatFunc F))
    (a b : A.carrier) (c : RatFunc F) (n d : ℕ) :
    Module.finrank (RatFunc F) (LinearMap.ker
      ((LinearMap.mulLeft (RatFunc F) a - LinearMap.mulRight (RatFunc F) b -
        c • LinearMap.id) ^ n)) ≠ d ↔
      ∀ p : RationalFunctionPlace F,
        Module.finrank (rationalFunctionCompletion F p) (LinearMap.ker
          ((LinearMap.mulLeft (rationalFunctionCompletion F p)
            (rationalFunctionLocalScalarExtensionMap F p A a) -
            LinearMap.mulRight (rationalFunctionCompletion F p)
              (rationalFunctionLocalScalarExtensionMap F p A b) -
            (algebraMap (RatFunc F) (rationalFunctionCompletion F p) c) • LinearMap.id) ^ n)) ≠ d := by
  have h := not_congr
    (rationalFunctionLocalScalarExtensionMap_intertwiner_generalizedEigenKernel_finrank_eq_iff_exists_place
      F A a b c n d)
  simpa only [not_exists] using h

/-- A wrong number-field Sylvester characteristic polynomial remains wrong at every completion. -/
theorem numberField_intertwinerCharpoly_ne_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (A : CSA.{u, w} K) (a b : A.carrier)
    (q : Polynomial K) :
    (LinearMap.mulLeft K a - LinearMap.mulRight K b).charpoly ≠ q ↔
      ∀ p : NumberFieldPlace K,
        (LinearMap.mulLeft (completion K p) (numberFieldLocalScalarExtensionMap K p A a) -
          LinearMap.mulRight (completion K p) (numberFieldLocalScalarExtensionMap K p A b)).charpoly ≠
            q.map (algebraMap K (completion K p)) := by
  have h := not_congr
    (numberFieldLocalScalarExtensionMap_intertwinerCharpoly_eq_iff_exists_place K A a b q)
  simpa only [not_exists] using h

/-- A wrong function-field Sylvester characteristic polynomial remains wrong at every completion. -/
theorem rationalFunction_intertwinerCharpoly_ne_iff_forall_place
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, w} (RatFunc F)) (a b : A.carrier)
    (q : Polynomial (RatFunc F)) :
    (LinearMap.mulLeft (RatFunc F) a - LinearMap.mulRight (RatFunc F) b).charpoly ≠ q ↔
      ∀ p : RationalFunctionPlace F,
        (LinearMap.mulLeft (rationalFunctionCompletion F p)
          (rationalFunctionLocalScalarExtensionMap F p A a) -
          LinearMap.mulRight (rationalFunctionCompletion F p)
            (rationalFunctionLocalScalarExtensionMap F p A b)).charpoly ≠
              q.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p)) := by
  have h := not_congr
    (rationalFunctionLocalScalarExtensionMap_intertwinerCharpoly_eq_iff_exists_place F A a b q)
  simpa only [not_exists] using h

/-- A wrong number-field Sylvester trace remains wrong at every completion. -/
theorem numberField_intertwinerTrace_ne_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (A : CSA.{u, w} K) (a b : A.carrier) (c : K) :
    LinearMap.trace K A.carrier (LinearMap.mulLeft K a - LinearMap.mulRight K b) ≠ c ↔
      ∀ p : NumberFieldPlace K,
        LinearMap.trace (completion K p) (completion K p ⊗[K] A.carrier)
          (LinearMap.mulLeft (completion K p) (numberFieldLocalScalarExtensionMap K p A a) -
            LinearMap.mulRight (completion K p) (numberFieldLocalScalarExtensionMap K p A b)) ≠
              algebraMap K (completion K p) c := by
  have h := not_congr
    (numberFieldLocalScalarExtensionMap_intertwinerTrace_eq_iff_exists_place K A a b c)
  simpa only [not_exists] using h

/-- A wrong function-field Sylvester trace remains wrong at every completion. -/
theorem rationalFunction_intertwinerTrace_ne_iff_forall_place
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, w} (RatFunc F)) (a b : A.carrier)
    (c : RatFunc F) :
    LinearMap.trace (RatFunc F) A.carrier
      (LinearMap.mulLeft (RatFunc F) a - LinearMap.mulRight (RatFunc F) b) ≠ c ↔
      ∀ p : RationalFunctionPlace F,
        LinearMap.trace (rationalFunctionCompletion F p)
          (rationalFunctionCompletion F p ⊗[RatFunc F] A.carrier)
          (LinearMap.mulLeft (rationalFunctionCompletion F p)
            (rationalFunctionLocalScalarExtensionMap F p A a) -
            LinearMap.mulRight (rationalFunctionCompletion F p)
              (rationalFunctionLocalScalarExtensionMap F p A b)) ≠
                algebraMap (RatFunc F) (rationalFunctionCompletion F p) c := by
  have h := not_congr
    (rationalFunctionLocalScalarExtensionMap_intertwinerTrace_eq_iff_exists_place F A a b c)
  simpa only [not_exists] using h

/-- A wrong number-field Sylvester determinant remains wrong at every completion. -/
theorem numberField_intertwinerDet_ne_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (A : CSA.{u, w} K) (a b : A.carrier) (c : K) :
    LinearMap.det (LinearMap.mulLeft K a - LinearMap.mulRight K b) ≠ c ↔
      ∀ p : NumberFieldPlace K,
        LinearMap.det (LinearMap.mulLeft (completion K p)
          (numberFieldLocalScalarExtensionMap K p A a) -
          LinearMap.mulRight (completion K p) (numberFieldLocalScalarExtensionMap K p A b)) ≠
            algebraMap K (completion K p) c := by
  have h := not_congr
    (numberFieldLocalScalarExtensionMap_intertwinerDet_eq_iff_exists_place K A a b c)
  simpa only [not_exists] using h

/-- A wrong function-field Sylvester determinant remains wrong at every completion. -/
theorem rationalFunction_intertwinerDet_ne_iff_forall_place
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, w} (RatFunc F)) (a b : A.carrier)
    (c : RatFunc F) :
    LinearMap.det (LinearMap.mulLeft (RatFunc F) a - LinearMap.mulRight (RatFunc F) b) ≠ c ↔
      ∀ p : RationalFunctionPlace F,
        LinearMap.det (LinearMap.mulLeft (rationalFunctionCompletion F p)
          (rationalFunctionLocalScalarExtensionMap F p A a) -
          LinearMap.mulRight (rationalFunctionCompletion F p)
            (rationalFunctionLocalScalarExtensionMap F p A b)) ≠
              algebraMap (RatFunc F) (rationalFunctionCompletion F p) c := by
  have h := not_congr
    (rationalFunctionLocalScalarExtensionMap_intertwinerDet_eq_iff_exists_place F A a b c)
  simpa only [not_exists] using h

end GaloisForLFunctions.HTGeometry.ABHN
