import GaloisForLFunctions.HTGeometry.HassePredicate
import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraRegularCharpolySeparable
import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraRegularInvariantValues
import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraRegularInvariants
import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraGeneralizedEigenDimensions
import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraCentralizerDimensions
import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraZeroDivisors

/-!
# Regular-representation defects of central simple algebras

For every central simple algebra over a global field, completion faithfully reflects regular
spectral invariants, eigenspace and centralizer dimensions, and annihilator equations.  Each
failure below is therefore rigid at every place.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

universe u w

/-- A wrong regular characteristic polynomial in a number-field CSA persists everywhere. -/
theorem numberField_regularCharpoly_ne_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (A : CSA.{u, w} K)
    (a : A.carrier) (q : Polynomial K) :
    (LinearMap.mulLeft K a).charpoly ≠ q ↔ ∀ v : NumberFieldPlace K,
      (LinearMap.mulLeft (completion K v)
        (numberFieldLocalScalarExtensionMap K v A a)).charpoly ≠
          q.map (algebraMap K (completion K v)) :=
  not_iff_forall_not_of_iff_exists
    (numberField_regularCharpoly_eq_iff_exists_place K A a q)

/-- A wrong regular characteristic polynomial in a function-field CSA persists everywhere. -/
theorem rationalFunction_regularCharpoly_ne_iff_forall_place
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, w} (RatFunc F))
    (a : A.carrier) (q : Polynomial (RatFunc F)) :
    (LinearMap.mulLeft (RatFunc F) a).charpoly ≠ q ↔
      ∀ v : RationalFunctionPlace F,
        (LinearMap.mulLeft (rationalFunctionCompletion F v)
          (rationalFunctionLocalScalarExtensionMap F v A a)).charpoly ≠
            q.map (algebraMap (RatFunc F) (rationalFunctionCompletion F v)) :=
  not_iff_forall_not_of_iff_exists
    (rationalFunction_regularCharpoly_eq_iff_exists_place F A a q)

/-- A wrong regular trace in a number-field CSA persists everywhere. -/
theorem numberField_regularTrace_ne_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (A : CSA.{u, w} K)
    (a : A.carrier) (c : K) :
    LinearMap.trace K A.carrier (LinearMap.mulLeft K a) ≠ c ↔
      ∀ p : NumberFieldPlace K,
        LinearMap.trace (completion K p) (completion K p ⊗[K] A.carrier)
          (LinearMap.mulLeft (completion K p)
            (numberFieldLocalScalarExtensionMap K p A a)) ≠
              algebraMap K (completion K p) c :=
  not_iff_forall_not_of_iff_exists
    (numberField_regularTrace_eq_iff_exists_place K A a c)

/-- A wrong regular trace in a function-field CSA persists everywhere. -/
theorem rationalFunction_regularTrace_ne_iff_forall_place
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, w} (RatFunc F))
    (a : A.carrier) (c : RatFunc F) :
    LinearMap.trace (RatFunc F) A.carrier (LinearMap.mulLeft (RatFunc F) a) ≠ c ↔
      ∀ p : RationalFunctionPlace F,
        LinearMap.trace (rationalFunctionCompletion F p)
          (rationalFunctionCompletion F p ⊗[RatFunc F] A.carrier)
          (LinearMap.mulLeft (rationalFunctionCompletion F p)
            (rationalFunctionLocalScalarExtensionMap F p A a)) ≠
              algebraMap (RatFunc F) (rationalFunctionCompletion F p) c :=
  not_iff_forall_not_of_iff_exists
    (rationalFunction_regularTrace_eq_iff_exists_place F A a c)

/-- A wrong regular norm in a number-field CSA persists everywhere. -/
theorem numberField_regularNorm_ne_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (A : CSA.{u, w} K)
    (a : A.carrier) (c : K) :
    LinearMap.det (LinearMap.mulLeft K a) ≠ c ↔ ∀ p : NumberFieldPlace K,
      LinearMap.det (LinearMap.mulLeft (completion K p)
        (numberFieldLocalScalarExtensionMap K p A a)) ≠
          algebraMap K (completion K p) c :=
  not_iff_forall_not_of_iff_exists
    (numberField_regularNorm_eq_iff_exists_place K A a c)

/-- A wrong regular norm in a function-field CSA persists everywhere. -/
theorem rationalFunction_regularNorm_ne_iff_forall_place
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, w} (RatFunc F))
    (a : A.carrier) (c : RatFunc F) :
    LinearMap.det (LinearMap.mulLeft (RatFunc F) a) ≠ c ↔
      ∀ p : RationalFunctionPlace F,
        LinearMap.det (LinearMap.mulLeft (rationalFunctionCompletion F p)
          (rationalFunctionLocalScalarExtensionMap F p A a)) ≠
            algebraMap (RatFunc F) (rationalFunctionCompletion F p) c :=
  not_iff_forall_not_of_iff_exists
    (rationalFunction_regularNorm_eq_iff_exists_place F A a c)

/-- Inseparability of a number-field CSA regular characteristic polynomial persists everywhere. -/
theorem numberField_regularCharpoly_not_separable_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (A : CSA.{u, w} K) (a : A.carrier) :
    ¬ (LinearMap.mulLeft K a).charpoly.Separable ↔ ∀ p : NumberFieldPlace K,
      ¬ (LinearMap.mulLeft (completion K p)
        (numberFieldLocalScalarExtensionMap K p A a)).charpoly.Separable :=
  not_iff_forall_not_of_iff_exists
    (numberField_regularCharpoly_separable_iff_exists_place K A a)

/-- Inseparability of a function-field CSA regular characteristic polynomial persists everywhere. -/
theorem rationalFunction_regularCharpoly_not_separable_iff_forall_place
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, w} (RatFunc F)) (a : A.carrier) :
    ¬ (LinearMap.mulLeft (RatFunc F) a).charpoly.Separable ↔
      ∀ p : RationalFunctionPlace F,
        ¬ (LinearMap.mulLeft (rationalFunctionCompletion F p)
          (rationalFunctionLocalScalarExtensionMap F p A a)).charpoly.Separable :=
  not_iff_forall_not_of_iff_exists
    (rationalFunction_regularCharpoly_separable_iff_exists_place F A a)

/-- Nonvanishing of regular trace in a number-field CSA persists everywhere. -/
theorem numberField_regularTrace_ne_zero_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (A : CSA.{u, w} K) (a : A.carrier) :
    LinearMap.trace K A.carrier (LinearMap.mulLeft K a) ≠ 0 ↔
      ∀ p : NumberFieldPlace K,
        LinearMap.trace (completion K p) (completion K p ⊗[K] A.carrier)
          (LinearMap.mulLeft (completion K p)
            (numberFieldLocalScalarExtensionMap K p A a)) ≠ 0 :=
  not_iff_forall_not_of_iff_exists
    (numberField_regularTrace_eq_zero_iff_exists_place K A a)

/-- Nonvanishing of regular trace in a function-field CSA persists everywhere. -/
theorem rationalFunction_regularTrace_ne_zero_iff_forall_place
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, w} (RatFunc F)) (a : A.carrier) :
    LinearMap.trace (RatFunc F) A.carrier (LinearMap.mulLeft (RatFunc F) a) ≠ 0 ↔
      ∀ p : RationalFunctionPlace F,
        LinearMap.trace (rationalFunctionCompletion F p)
          (rationalFunctionCompletion F p ⊗[RatFunc F] A.carrier)
          (LinearMap.mulLeft (rationalFunctionCompletion F p)
            (rationalFunctionLocalScalarExtensionMap F p A a)) ≠ 0 :=
  not_iff_forall_not_of_iff_exists
    (rationalFunction_regularTrace_eq_zero_iff_exists_place F A a)

/-- Nonvanishing of regular norm in a number-field CSA persists everywhere. -/
theorem numberField_regularNorm_ne_zero_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (A : CSA.{u, w} K) (a : A.carrier) :
    LinearMap.det (LinearMap.mulLeft K a) ≠ 0 ↔ ∀ p : NumberFieldPlace K,
      LinearMap.det (LinearMap.mulLeft (completion K p)
        (numberFieldLocalScalarExtensionMap K p A a)) ≠ 0 :=
  not_iff_forall_not_of_iff_exists
    (numberField_regularNorm_eq_zero_iff_exists_place K A a)

/-- Nonvanishing of regular norm in a function-field CSA persists everywhere. -/
theorem rationalFunction_regularNorm_ne_zero_iff_forall_place
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, w} (RatFunc F)) (a : A.carrier) :
    LinearMap.det (LinearMap.mulLeft (RatFunc F) a) ≠ 0 ↔
      ∀ p : RationalFunctionPlace F,
        LinearMap.det (LinearMap.mulLeft (rationalFunctionCompletion F p)
          (rationalFunctionLocalScalarExtensionMap F p A a)) ≠ 0 :=
  not_iff_forall_not_of_iff_exists
    (rationalFunction_regularNorm_eq_zero_iff_exists_place F A a)

/-- A wrong generalized regular-eigenspace dimension in a number-field CSA persists everywhere. -/
theorem numberField_mulLeft_generalizedEigenKernel_finrank_ne_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (A : CSA.{u, w} K) (x : A.carrier)
    (c : K) (n d : ℕ) :
    Module.finrank K (LinearMap.ker
      ((LinearMap.mulLeft K x - c • LinearMap.id) ^ n)) ≠ d ↔
      ∀ p : NumberFieldPlace K,
        Module.finrank (completion K p) (LinearMap.ker
          ((LinearMap.mulLeft (completion K p)
            (numberFieldLocalScalarExtensionMap K p A x) -
            (algebraMap K (completion K p) c) • LinearMap.id) ^ n)) ≠ d :=
  not_iff_forall_not_of_iff_exists
    (numberFieldLocalScalarExtensionMap_mulLeft_generalizedEigenKernel_finrank_eq_iff_exists_place
      K A x c n d)

/-- A wrong generalized regular-eigenspace dimension in a function-field CSA persists. -/
theorem rationalFunction_mulLeft_generalizedEigenKernel_finrank_ne_iff_forall_place
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, w} (RatFunc F)) (x : A.carrier)
    (c : RatFunc F) (n d : ℕ) :
    Module.finrank (RatFunc F) (LinearMap.ker
      ((LinearMap.mulLeft (RatFunc F) x - c • LinearMap.id) ^ n)) ≠ d ↔
      ∀ p : RationalFunctionPlace F,
        Module.finrank (rationalFunctionCompletion F p) (LinearMap.ker
          ((LinearMap.mulLeft (rationalFunctionCompletion F p)
            (rationalFunctionLocalScalarExtensionMap F p A x) -
            (algebraMap (RatFunc F) (rationalFunctionCompletion F p) c) •
              LinearMap.id) ^ n)) ≠ d :=
  not_iff_forall_not_of_iff_exists
    (rationalFunctionLocalScalarExtensionMap_mulLeft_generalizedEigenKernel_finrank_eq_iff_exists_place
      F A x c n d)

/-- A wrong centralizer dimension in a number-field CSA persists everywhere. -/
theorem numberField_commutator_ker_finrank_ne_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (A : CSA.{u, w} K)
    (a : A.carrier) (d : ℕ) :
    Module.finrank K
      (LinearMap.ker (LinearMap.mulLeft K a - LinearMap.mulRight K a)) ≠ d ↔
      ∀ p : NumberFieldPlace K,
        Module.finrank (completion K p)
          (LinearMap.ker (LinearMap.mulLeft (completion K p)
            (numberFieldLocalScalarExtensionMap K p A a) -
            LinearMap.mulRight (completion K p)
              (numberFieldLocalScalarExtensionMap K p A a))) ≠ d :=
  not_iff_forall_not_of_iff_exists
    (numberFieldLocalScalarExtensionMap_commutator_ker_finrank_eq_iff_exists_place K A a d)

/-- A wrong centralizer dimension in a function-field CSA persists everywhere. -/
theorem rationalFunction_commutator_ker_finrank_ne_iff_forall_place
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, w} (RatFunc F))
    (a : A.carrier) (d : ℕ) :
    Module.finrank (RatFunc F)
      (LinearMap.ker (LinearMap.mulLeft (RatFunc F) a - LinearMap.mulRight (RatFunc F) a)) ≠ d ↔
      ∀ p : RationalFunctionPlace F,
        Module.finrank (rationalFunctionCompletion F p)
          (LinearMap.ker (LinearMap.mulLeft (rationalFunctionCompletion F p)
            (rationalFunctionLocalScalarExtensionMap F p A a) -
            LinearMap.mulRight (rationalFunctionCompletion F p)
              (rationalFunctionLocalScalarExtensionMap F p A a))) ≠ d :=
  not_iff_forall_not_of_iff_exists
    (rationalFunctionLocalScalarExtensionMap_commutator_ker_finrank_eq_iff_exists_place F A a d)

/-- Absence of a nonzero left annihilator in a number-field CSA persists everywhere. -/
theorem numberField_not_exists_nonzero_mulLeft_eq_zero_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (A : CSA.{u, w} K) (a : A.carrier) :
    (¬ ∃ x, x ≠ 0 ∧ a * x = 0) ↔ ∀ p : NumberFieldPlace K, ¬ ∃ z, z ≠ 0 ∧
      numberFieldLocalScalarExtensionMap K p A a * z = 0 :=
  not_iff_forall_not_of_iff_exists
    (numberField_exists_nonzero_mulLeft_eq_zero_iff_exists_place K A a)

/-- Absence of a nonzero right annihilator in a number-field CSA persists everywhere. -/
theorem numberField_not_exists_nonzero_mulRight_eq_zero_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (A : CSA.{u, w} K) (a : A.carrier) :
    (¬ ∃ x, x ≠ 0 ∧ x * a = 0) ↔ ∀ p : NumberFieldPlace K, ¬ ∃ z, z ≠ 0 ∧
      z * numberFieldLocalScalarExtensionMap K p A a = 0 :=
  not_iff_forall_not_of_iff_exists
    (numberField_exists_nonzero_mulRight_eq_zero_iff_exists_place K A a)

/-- Absence of a nonzero left annihilator in a function-field CSA persists everywhere. -/
theorem rationalFunction_not_exists_nonzero_mulLeft_eq_zero_iff_forall_place
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, w} (RatFunc F)) (a : A.carrier) :
    (¬ ∃ x, x ≠ 0 ∧ a * x = 0) ↔ ∀ p : RationalFunctionPlace F, ¬ ∃ z, z ≠ 0 ∧
      rationalFunctionLocalScalarExtensionMap F p A a * z = 0 :=
  not_iff_forall_not_of_iff_exists
    (rationalFunction_exists_nonzero_mulLeft_eq_zero_iff_exists_place F A a)

/-- Absence of a nonzero right annihilator in a function-field CSA persists everywhere. -/
theorem rationalFunction_not_exists_nonzero_mulRight_eq_zero_iff_forall_place
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, w} (RatFunc F)) (a : A.carrier) :
    (¬ ∃ x, x ≠ 0 ∧ x * a = 0) ↔ ∀ p : RationalFunctionPlace F, ¬ ∃ z, z ≠ 0 ∧
      z * rationalFunctionLocalScalarExtensionMap F p A a = 0 :=
  not_iff_forall_not_of_iff_exists
    (rationalFunction_exists_nonzero_mulRight_eq_zero_iff_exists_place F A a)

end GaloisForLFunctions.HTGeometry.ABHN
