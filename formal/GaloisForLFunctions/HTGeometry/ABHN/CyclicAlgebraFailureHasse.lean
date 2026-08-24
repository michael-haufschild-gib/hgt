import GaloisForLFunctions.HTGeometry.HassePredicate
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisAlgebraHasseElements
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisAlgebraHasseStructure
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisAlgebraHasseMorphisms
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisAlgebraHasseAzumaya

/-!
# Cyclic-algebra defects at every completion

Cyclic Galois algebras give explicit representatives of Brauer classes.  Faithful completion
reflects their element relations, centralizer equations, endomorphism properties, and Azumaya
structure.  Consequently failure of any such property is visible at every global-field place.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

/-- Nonidempotence of a cyclic-algebra element over a number field persists everywhere. -/
theorem numberField_cyclicGaloisAlgebra_not_isIdempotent_iff_forall_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (ha : a ≠ 0) (x : cyclicGaloisAlgebra K L a) :
    ¬ IsIdempotentElem x ↔ ∀ p : NumberFieldPlace K,
      ¬ IsIdempotentElem (numberFieldLocalScalarExtensionMap K p
        (cyclicGaloisAlgebraCSA K L a ha) x) :=
  not_iff_forall_not_of_iff_exists
    (numberField_cyclicGaloisAlgebra_isIdempotent_iff_exists_place K L a ha x)

/-- Nonidempotence of a cyclic-algebra element over a function field persists everywhere. -/
theorem rationalFunction_cyclicGaloisAlgebra_not_isIdempotent_iff_forall_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F) (ha : a ≠ 0) (x : cyclicGaloisAlgebra (RatFunc F) L a) :
    ¬ IsIdempotentElem x ↔ ∀ p : RationalFunctionPlace F,
      ¬ IsIdempotentElem (rationalFunctionLocalScalarExtensionMap F p
        (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x) :=
  not_iff_forall_not_of_iff_exists
    (rationalFunction_cyclicGaloisAlgebra_isIdempotent_iff_exists_place F L a ha x)

/-- Nonnilpotence of a cyclic-algebra element over a number field persists everywhere. -/
theorem numberField_cyclicGaloisAlgebra_not_isNilpotent_iff_forall_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (ha : a ≠ 0) (x : cyclicGaloisAlgebra K L a) :
    ¬ IsNilpotent x ↔ ∀ p : NumberFieldPlace K,
      ¬ IsNilpotent (numberFieldLocalScalarExtensionMap K p
        (cyclicGaloisAlgebraCSA K L a ha) x) :=
  not_iff_forall_not_of_iff_exists
    (numberField_cyclicGaloisAlgebra_isNilpotent_iff_exists_place K L a ha x)

/-- Nonnilpotence of a cyclic-algebra element over a function field persists everywhere. -/
theorem rationalFunction_cyclicGaloisAlgebra_not_isNilpotent_iff_forall_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F) (ha : a ≠ 0) (x : cyclicGaloisAlgebra (RatFunc F) L a) :
    ¬ IsNilpotent x ↔ ∀ p : RationalFunctionPlace F,
      ¬ IsNilpotent (rationalFunctionLocalScalarExtensionMap F p
        (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x) :=
  not_iff_forall_not_of_iff_exists
    (rationalFunction_cyclicGaloisAlgebra_isNilpotent_iff_exists_place F L a ha x)

/-- Failure of a polynomial relation in a cyclic algebra over a number field persists everywhere. -/
theorem numberField_cyclicGaloisAlgebra_polynomial_eval₂_ne_zero_iff_forall_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (ha : a ≠ 0) (q : Polynomial K) (x : cyclicGaloisAlgebra K L a) :
    q.eval₂ (algebraMap K (cyclicGaloisAlgebra K L a)) x ≠ 0 ↔
      ∀ v : NumberFieldPlace K,
        (q.map (algebraMap K (completion K v))).eval₂
          (algebraMap (completion K v)
            (completion K v ⊗[K] cyclicGaloisAlgebra K L a))
          (numberFieldLocalScalarExtensionMap K v
            (cyclicGaloisAlgebraCSA K L a ha) x) ≠ 0 :=
  not_iff_forall_not_of_iff_exists
    (numberField_cyclicGaloisAlgebra_polynomial_eval₂_eq_zero_iff_exists_place
      K L a ha q x)

/-- Failure of a polynomial relation in a function-field cyclic algebra persists everywhere. -/
theorem rationalFunction_cyclicGaloisAlgebra_polynomial_eval₂_ne_zero_iff_forall_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F) (ha : a ≠ 0) (q : Polynomial (RatFunc F))
    (x : cyclicGaloisAlgebra (RatFunc F) L a) :
    q.eval₂ (algebraMap (RatFunc F) (cyclicGaloisAlgebra (RatFunc F) L a)) x ≠ 0 ↔
      ∀ v : RationalFunctionPlace F,
        (q.map (algebraMap (RatFunc F) (rationalFunctionCompletion F v))).eval₂
          (algebraMap (rationalFunctionCompletion F v)
            (rationalFunctionCompletion F v ⊗[RatFunc F]
              cyclicGaloisAlgebra (RatFunc F) L a))
          (rationalFunctionLocalScalarExtensionMap F v
            (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x) ≠ 0 :=
  not_iff_forall_not_of_iff_exists
    (rationalFunction_cyclicGaloisAlgebra_polynomial_eval₂_eq_zero_iff_exists_place
      F L a ha q x)

/-- Noncentrality of a cyclic-algebra element over a number field persists everywhere. -/
theorem numberField_cyclicGaloisAlgebra_not_mem_center_iff_forall_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (ha : a ≠ 0) (x : cyclicGaloisAlgebra K L a) :
    x ∉ Subalgebra.center K (cyclicGaloisAlgebra K L a) ↔ ∀ p : NumberFieldPlace K,
      numberFieldLocalScalarExtensionMap K p (cyclicGaloisAlgebraCSA K L a ha) x ∉
        Subalgebra.center (completion K p)
          (completion K p ⊗[K] cyclicGaloisAlgebra K L a) :=
  not_iff_forall_not_of_iff_exists
    (numberField_cyclicGaloisAlgebra_mem_center_iff_exists_place K L a ha x)

/-- Noncentrality of a function-field cyclic-algebra element persists everywhere. -/
theorem rationalFunction_cyclicGaloisAlgebra_not_mem_center_iff_forall_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F) (ha : a ≠ 0) (x : cyclicGaloisAlgebra (RatFunc F) L a) :
    x ∉ Subalgebra.center (RatFunc F) (cyclicGaloisAlgebra (RatFunc F) L a) ↔
      ∀ p : RationalFunctionPlace F,
        rationalFunctionLocalScalarExtensionMap F p
            (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x ∉
          Subalgebra.center (rationalFunctionCompletion F p)
            (rationalFunctionCompletion F p ⊗[RatFunc F]
              cyclicGaloisAlgebra (RatFunc F) L a) :=
  not_iff_forall_not_of_iff_exists
    (rationalFunction_cyclicGaloisAlgebra_mem_center_iff_exists_place F L a ha x)

/-- Global failure of a commutator equation over a number field persists everywhere. -/
theorem numberField_cyclicGaloisAlgebra_not_exists_commutator_eq_iff_forall_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (ha : a ≠ 0) (x y : cyclicGaloisAlgebra K L a) :
    (¬ ∃ z, x * z - z * x = y) ↔ ∀ p : NumberFieldPlace K, ¬ ∃ z,
      numberFieldLocalScalarExtensionMap K p (cyclicGaloisAlgebraCSA K L a ha) x * z -
          z * numberFieldLocalScalarExtensionMap K p (cyclicGaloisAlgebraCSA K L a ha) x =
            numberFieldLocalScalarExtensionMap K p (cyclicGaloisAlgebraCSA K L a ha) y :=
  not_iff_forall_not_of_iff_exists
    (numberField_cyclicGaloisAlgebra_exists_commutator_eq_iff_exists_place K L a ha x y)

/-- Global failure of a commutator equation over a function field persists everywhere. -/
theorem rationalFunction_cyclicGaloisAlgebra_not_exists_commutator_eq_iff_forall_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F) (ha : a ≠ 0) (x y : cyclicGaloisAlgebra (RatFunc F) L a) :
    (¬ ∃ z, x * z - z * x = y) ↔ ∀ p : RationalFunctionPlace F, ¬ ∃ z,
      rationalFunctionLocalScalarExtensionMap F p
          (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x * z -
        z * rationalFunctionLocalScalarExtensionMap F p
          (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x =
          rationalFunctionLocalScalarExtensionMap F p
            (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) y :=
  not_iff_forall_not_of_iff_exists
    (rationalFunction_cyclicGaloisAlgebra_exists_commutator_eq_iff_exists_place
      F L a ha x y)

/-- Failure of a prescribed centralizer dimension over a number field persists everywhere. -/
theorem numberField_cyclicGaloisAlgebra_centralizerFinrank_ne_iff_forall_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (ha : a ≠ 0) (x : cyclicGaloisAlgebra K L a) (d : ℕ) :
    Module.finrank K (LinearMap.ker (LinearMap.mulLeft K x - LinearMap.mulRight K x)) ≠ d ↔
      ∀ p : NumberFieldPlace K,
        Module.finrank (completion K p)
          (LinearMap.ker
            (LinearMap.mulLeft (completion K p)
              (numberFieldLocalScalarExtensionMap K p (cyclicGaloisAlgebraCSA K L a ha) x) -
              LinearMap.mulRight (completion K p)
                (numberFieldLocalScalarExtensionMap K p
                  (cyclicGaloisAlgebraCSA K L a ha) x))) ≠ d :=
  not_iff_forall_not_of_iff_exists
    (numberField_cyclicGaloisAlgebra_centralizerFinrank_eq_iff_exists_place K L a ha x d)

/-- Failure of a prescribed centralizer dimension over a function field persists everywhere. -/
theorem rationalFunction_cyclicGaloisAlgebra_centralizerFinrank_ne_iff_forall_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F) (ha : a ≠ 0) (x : cyclicGaloisAlgebra (RatFunc F) L a) (d : ℕ) :
    Module.finrank (RatFunc F)
      (LinearMap.ker (LinearMap.mulLeft (RatFunc F) x - LinearMap.mulRight (RatFunc F) x)) ≠ d ↔
      ∀ p : RationalFunctionPlace F,
        Module.finrank (rationalFunctionCompletion F p)
          (LinearMap.ker
            (LinearMap.mulLeft (rationalFunctionCompletion F p)
              (rationalFunctionLocalScalarExtensionMap F p
                (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x) -
              LinearMap.mulRight (rationalFunctionCompletion F p)
                (rationalFunctionLocalScalarExtensionMap F p
                  (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x))) ≠ d :=
  not_iff_forall_not_of_iff_exists
    (rationalFunction_cyclicGaloisAlgebra_centralizerFinrank_eq_iff_exists_place
      F L a ha x d)

/-- Noninjectivity of a cyclic-algebra endomorphism over a number field persists everywhere. -/
theorem numberField_cyclicGaloisAlgebra_algHom_not_injective_iff_forall_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (f : cyclicGaloisAlgebra K L a →ₐ[K] cyclicGaloisAlgebra K L a) :
    ¬ Function.Injective f ↔ ∀ p : NumberFieldPlace K,
      ¬ Function.Injective (algHomBaseChange (L := completion K p) f) :=
  not_iff_forall_not_of_iff_exists
    (numberField_cyclicGaloisAlgebra_algHom_injective_iff_exists_place K L a f)

/-- Noninjectivity of a function-field cyclic-algebra endomorphism persists everywhere. -/
theorem rationalFunction_cyclicGaloisAlgebra_algHom_not_injective_iff_forall_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F)
    (f : cyclicGaloisAlgebra (RatFunc F) L a →ₐ[RatFunc F]
      cyclicGaloisAlgebra (RatFunc F) L a) :
    ¬ Function.Injective f ↔ ∀ p : RationalFunctionPlace F,
      ¬ Function.Injective (algHomBaseChange (L := rationalFunctionCompletion F p) f) :=
  not_iff_forall_not_of_iff_exists
    (rationalFunction_cyclicGaloisAlgebra_algHom_injective_iff_exists_place F L a f)

/-- Nonsurjectivity of a cyclic-algebra endomorphism over a number field persists everywhere. -/
theorem numberField_cyclicGaloisAlgebra_algHom_not_surjective_iff_forall_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (f : cyclicGaloisAlgebra K L a →ₐ[K] cyclicGaloisAlgebra K L a) :
    ¬ Function.Surjective f ↔ ∀ p : NumberFieldPlace K,
      ¬ Function.Surjective (algHomBaseChange (L := completion K p) f) :=
  not_iff_forall_not_of_iff_exists
    (numberField_cyclicGaloisAlgebra_algHom_surjective_iff_exists_place K L a f)

/-- Nonsurjectivity of a function-field cyclic-algebra endomorphism persists everywhere. -/
theorem rationalFunction_cyclicGaloisAlgebra_algHom_not_surjective_iff_forall_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F)
    (f : cyclicGaloisAlgebra (RatFunc F) L a →ₐ[RatFunc F]
      cyclicGaloisAlgebra (RatFunc F) L a) :
    ¬ Function.Surjective f ↔ ∀ p : RationalFunctionPlace F,
      ¬ Function.Surjective (algHomBaseChange (L := rationalFunctionCompletion F p) f) :=
  not_iff_forall_not_of_iff_exists
    (rationalFunction_cyclicGaloisAlgebra_algHom_surjective_iff_exists_place F L a f)

/-- Nonbijectivity of a cyclic-algebra endomorphism over a number field persists everywhere. -/
theorem numberField_cyclicGaloisAlgebra_algHom_not_bijective_iff_forall_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (f : cyclicGaloisAlgebra K L a →ₐ[K] cyclicGaloisAlgebra K L a) :
    ¬ Function.Bijective f ↔ ∀ p : NumberFieldPlace K,
      ¬ Function.Bijective (algHomBaseChange (L := completion K p) f) :=
  not_iff_forall_not_of_iff_exists
    (numberField_cyclicGaloisAlgebra_algHom_bijective_iff_exists_place K L a f)

/-- Nonbijectivity of a function-field cyclic-algebra endomorphism persists everywhere. -/
theorem rationalFunction_cyclicGaloisAlgebra_algHom_not_bijective_iff_forall_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F)
    (f : cyclicGaloisAlgebra (RatFunc F) L a →ₐ[RatFunc F]
      cyclicGaloisAlgebra (RatFunc F) L a) :
    ¬ Function.Bijective f ↔ ∀ p : RationalFunctionPlace F,
      ¬ Function.Bijective (algHomBaseChange (L := rationalFunctionCompletion F p) f) :=
  not_iff_forall_not_of_iff_exists
    (rationalFunction_cyclicGaloisAlgebra_algHom_bijective_iff_exists_place F L a f)

/-- Failure of the Azumaya property for a cyclic algebra over a number field persists everywhere. -/
theorem numberField_cyclicGaloisAlgebra_not_isAzumaya_iff_forall_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L] (a : K) :
    ¬ IsAzumaya K (cyclicGaloisAlgebra K L a) ↔ ∀ p : NumberFieldPlace K,
      ¬ IsAzumaya (completion K p) (completion K p ⊗[K] cyclicGaloisAlgebra K L a) :=
  not_iff_forall_not_of_iff_exists
    (numberField_cyclicGaloisAlgebra_isAzumaya_iff_exists_place K L a)

/-- Failure of the Azumaya property for a function-field cyclic algebra persists everywhere. -/
theorem rationalFunction_cyclicGaloisAlgebra_not_isAzumaya_iff_forall_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F) :
    ¬ IsAzumaya (RatFunc F) (cyclicGaloisAlgebra (RatFunc F) L a) ↔
      ∀ p : RationalFunctionPlace F,
        ¬ IsAzumaya (rationalFunctionCompletion F p)
          (rationalFunctionCompletion F p ⊗[RatFunc F]
            cyclicGaloisAlgebra (RatFunc F) L a) :=
  not_iff_forall_not_of_iff_exists
    (rationalFunction_cyclicGaloisAlgebra_isAzumaya_iff_exists_place F L a)

end GaloisForLFunctions.HTGeometry.ABHN
