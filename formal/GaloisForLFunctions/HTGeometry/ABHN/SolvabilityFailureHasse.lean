import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraCommutator
import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraDivision
import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraIntertwiners
import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraEigenvectors
import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraUnits

/-!
# Persistence of algebraic unsolvability at every completion

Finite-dimensional equations reflected by scalar extension form rigid Hasse systems.  If a
commutator, division, Sylvester, eigenvector, or inverse problem has no global solution, it has no
solution at any completion.  These theorems expose local obstruction certificates for operator and
representation-theoretic applications without invoking global reciprocity.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u w

/-- An unsolvable number-field commutator equation remains unsolvable at every completion. -/
theorem numberField_commutator_unsolvable_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (A : CSA.{u, w} K) (a b : A.carrier) :
    (¬ ∃ x, a * x - x * a = b) ↔ ∀ p : NumberFieldPlace K, ¬ ∃ z,
      numberFieldLocalScalarExtensionMap K p A a * z -
        z * numberFieldLocalScalarExtensionMap K p A a =
          numberFieldLocalScalarExtensionMap K p A b := by
  have h := not_congr
    (numberFieldLocalScalarExtensionMap_exists_commutator_eq_iff_exists_place K A a b)
  simpa only [not_exists] using h

/-- An unsolvable function-field commutator equation remains unsolvable at every completion. -/
theorem rationalFunction_commutator_unsolvable_iff_forall_place
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, w} (RatFunc F)) (a b : A.carrier) :
    (¬ ∃ x, a * x - x * a = b) ↔ ∀ p : RationalFunctionPlace F, ¬ ∃ z,
      rationalFunctionLocalScalarExtensionMap F p A a * z -
        z * rationalFunctionLocalScalarExtensionMap F p A a =
          rationalFunctionLocalScalarExtensionMap F p A b := by
  have h := not_congr
    (rationalFunctionLocalScalarExtensionMap_exists_commutator_eq_iff_exists_place F A a b)
  simpa only [not_exists] using h

/-- An unsolvable number-field left-division equation remains unsolvable at every completion. -/
theorem numberField_mulLeft_unsolvable_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (A : CSA.{u, w} K) (a b : A.carrier) :
    (¬ ∃ x, a * x = b) ↔ ∀ p : NumberFieldPlace K, ¬ ∃ z,
      numberFieldLocalScalarExtensionMap K p A a * z =
        numberFieldLocalScalarExtensionMap K p A b := by
  have h := not_congr
    (numberFieldLocalScalarExtensionMap_exists_mulLeft_eq_iff_exists_place K A a b)
  simpa only [not_exists] using h

/-- An unsolvable number-field right-division equation remains unsolvable at every completion. -/
theorem numberField_mulRight_unsolvable_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (A : CSA.{u, w} K) (a b : A.carrier) :
    (¬ ∃ x, x * a = b) ↔ ∀ p : NumberFieldPlace K, ¬ ∃ z,
      z * numberFieldLocalScalarExtensionMap K p A a =
        numberFieldLocalScalarExtensionMap K p A b := by
  have h := not_congr
    (numberFieldLocalScalarExtensionMap_exists_mulRight_eq_iff_exists_place K A a b)
  simpa only [not_exists] using h

/-- An unsolvable function-field left-division equation remains unsolvable at every completion. -/
theorem rationalFunction_mulLeft_unsolvable_iff_forall_place
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, w} (RatFunc F)) (a b : A.carrier) :
    (¬ ∃ x, a * x = b) ↔ ∀ p : RationalFunctionPlace F, ¬ ∃ z,
      rationalFunctionLocalScalarExtensionMap F p A a * z =
        rationalFunctionLocalScalarExtensionMap F p A b := by
  have h := not_congr
    (rationalFunctionLocalScalarExtensionMap_exists_mulLeft_eq_iff_exists_place F A a b)
  simpa only [not_exists] using h

/-- An unsolvable function-field right-division equation remains unsolvable at every completion. -/
theorem rationalFunction_mulRight_unsolvable_iff_forall_place
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, w} (RatFunc F)) (a b : A.carrier) :
    (¬ ∃ x, x * a = b) ↔ ∀ p : RationalFunctionPlace F, ¬ ∃ z,
      z * rationalFunctionLocalScalarExtensionMap F p A a =
        rationalFunctionLocalScalarExtensionMap F p A b := by
  have h := not_congr
    (rationalFunctionLocalScalarExtensionMap_exists_mulRight_eq_iff_exists_place F A a b)
  simpa only [not_exists] using h

/-- An unsolvable number-field inhomogeneous intertwining equation stays unsolvable everywhere. -/
theorem numberField_intertwining_defect_unsolvable_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (A : CSA.{u, w} K) (a b c : A.carrier) :
    (¬ ∃ x, a * x - x * b = c) ↔ ∀ p : NumberFieldPlace K, ¬ ∃ z,
      numberFieldLocalScalarExtensionMap K p A a * z -
        z * numberFieldLocalScalarExtensionMap K p A b =
          numberFieldLocalScalarExtensionMap K p A c := by
  have h := not_congr
    (numberFieldLocalScalarExtensionMap_exists_intertwining_defect_eq_iff_exists_place K A a b c)
  simpa only [not_exists] using h

/-- An unsolvable function-field inhomogeneous intertwining equation stays unsolvable everywhere. -/
theorem rationalFunction_intertwining_defect_unsolvable_iff_forall_place
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, w} (RatFunc F)) (a b c : A.carrier) :
    (¬ ∃ x, a * x - x * b = c) ↔ ∀ p : RationalFunctionPlace F, ¬ ∃ z,
      rationalFunctionLocalScalarExtensionMap F p A a * z -
        z * rationalFunctionLocalScalarExtensionMap F p A b =
          rationalFunctionLocalScalarExtensionMap F p A c := by
  have h := not_congr
    (rationalFunctionLocalScalarExtensionMap_exists_intertwining_defect_eq_iff_exists_place
      F A a b c)
  simpa only [not_exists] using h

/-- Absence of a nonzero number-field intertwiner persists at every completion. -/
theorem numberField_nonzero_intertwiner_absent_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (A : CSA.{u, w} K) (a b : A.carrier) :
    (¬ ∃ x, x ≠ 0 ∧ a * x = x * b) ↔ ∀ p : NumberFieldPlace K, ¬ ∃ z,
      z ≠ 0 ∧ numberFieldLocalScalarExtensionMap K p A a * z =
        z * numberFieldLocalScalarExtensionMap K p A b := by
  have h := not_congr
    (numberFieldLocalScalarExtensionMap_exists_nonzero_intertwiner_iff_exists_place K A a b)
  simpa only [not_exists] using h

/-- Absence of a nonzero function-field intertwiner persists at every completion. -/
theorem rationalFunction_nonzero_intertwiner_absent_iff_forall_place
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, w} (RatFunc F)) (a b : A.carrier) :
    (¬ ∃ x, x ≠ 0 ∧ a * x = x * b) ↔ ∀ p : RationalFunctionPlace F, ¬ ∃ z,
      z ≠ 0 ∧ rationalFunctionLocalScalarExtensionMap F p A a * z =
        z * rationalFunctionLocalScalarExtensionMap F p A b := by
  have h := not_congr
    (rationalFunctionLocalScalarExtensionMap_exists_nonzero_intertwiner_iff_exists_place F A a b)
  simpa only [not_exists] using h

/-- Absence of a number-field left-regular eigenvalue persists at every completion. -/
theorem numberField_mulLeft_eigenKernel_eq_bot_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (A : CSA.{u, w} K)
    (x : A.carrier) (c : K) :
    LinearMap.ker (LinearMap.mulLeft K x - c • LinearMap.id) = ⊥ ↔
      ∀ p : NumberFieldPlace K,
        LinearMap.ker (LinearMap.mulLeft (completion K p)
          (numberFieldLocalScalarExtensionMap K p A x) -
          (algebraMap K (completion K p) c) • LinearMap.id) = ⊥ := by
  have h := not_congr
    (numberFieldLocalScalarExtensionMap_mulLeft_eigenKernel_ne_bot_iff_exists_place K A x c)
  simpa only [not_exists, not_ne_iff] using h

/-- Absence of a function-field left-regular eigenvalue persists at every completion. -/
theorem rationalFunction_mulLeft_eigenKernel_eq_bot_iff_forall_place
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, w} (RatFunc F))
    (x : A.carrier) (c : RatFunc F) :
    LinearMap.ker (LinearMap.mulLeft (RatFunc F) x - c • LinearMap.id) = ⊥ ↔
      ∀ p : RationalFunctionPlace F,
        LinearMap.ker (LinearMap.mulLeft (rationalFunctionCompletion F p)
          (rationalFunctionLocalScalarExtensionMap F p A x) -
          (algebraMap (RatFunc F) (rationalFunctionCompletion F p) c) • LinearMap.id) = ⊥ := by
  have h := not_congr
    (rationalFunctionLocalScalarExtensionMap_mulLeft_eigenKernel_ne_bot_iff_exists_place F A x c)
  simpa only [not_exists, not_ne_iff] using h

/-- Noninvertibility of a number-field CSA element persists at every completion. -/
theorem numberField_csaElement_not_isUnit_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (A : CSA.{u, w} K) (a : A.carrier) :
    ¬ IsUnit a ↔ ∀ p : NumberFieldPlace K,
      ¬ IsUnit (numberFieldLocalScalarExtensionMap K p A a) := by
  rw [numberFieldLocalScalarExtensionMap_isUnit_iff_exists_place]
  push Not
  rfl

/-- Noninvertibility of a function-field CSA element persists at every completion. -/
theorem rationalFunction_csaElement_not_isUnit_iff_forall_place
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, w} (RatFunc F)) (a : A.carrier) :
    ¬ IsUnit a ↔ ∀ p : RationalFunctionPlace F,
      ¬ IsUnit (rationalFunctionLocalScalarExtensionMap F p A a) := by
  rw [rationalFunctionLocalScalarExtensionMap_isUnit_iff_exists_place]
  push Not
  rfl

end GaloisForLFunctions.HTGeometry.ABHN
