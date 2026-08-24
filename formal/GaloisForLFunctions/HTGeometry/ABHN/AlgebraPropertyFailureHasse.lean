import GaloisForLFunctions.HTGeometry.HassePredicate
import GaloisForLFunctions.HTGeometry.ABHN.HasseFormalUnramified
import GaloisForLFunctions.HTGeometry.ABHN.HasseAzumaya
import GaloisForLFunctions.HTGeometry.ABHN.HasseCentralSimple
import GaloisForLFunctions.HTGeometry.ABHN.HassePolynomialCoprime
import GaloisForLFunctions.HTGeometry.ABHN.HassePolynomialSeparable
import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraTraceForm

/-!
# Structural algebra failures at every completion

This module records all-place persistence for failures of formal unramifiedness, Azumaya-ness,
centrality, simplicity, polynomial coprimality and separability, and trace-pairing nondegeneracy.
These rigid Hasse laws expose local witnesses for defects in the algebraic objects used to build
Brauer classes and finite étale or spectral models.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

universe u w

/-- Failure of formal unramifiedness over a number field persists at every completion. -/
theorem numberField_algebra_not_formallyUnramified_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    {A : Type w} [CommRing A] [Algebra K A] :
    ¬ Algebra.FormallyUnramified K A ↔ ∀ p : NumberFieldPlace K,
      ¬ Algebra.FormallyUnramified (completion K p) (completion K p ⊗[K] A) :=
  not_iff_forall_not_of_iff_exists
    (numberField_algebra_formallyUnramified_iff_exists_place K)

/-- Failure of formal unramifiedness over `F(t)` persists at every completion. -/
theorem rationalFunction_algebra_not_formallyUnramified_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    {A : Type w} [CommRing A] [Algebra (RatFunc F) A] :
    ¬ Algebra.FormallyUnramified (RatFunc F) A ↔ ∀ p : RationalFunctionPlace F,
      ¬ Algebra.FormallyUnramified (rationalFunctionCompletion F p)
        (rationalFunctionCompletion F p ⊗[RatFunc F] A) :=
  not_iff_forall_not_of_iff_exists
    (rationalFunction_algebra_formallyUnramified_iff_exists_place F)

/-- Failure of the Azumaya property over a number field persists at every completion. -/
theorem numberField_algebra_not_isAzumaya_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    {A : Type w} [Ring A] [Algebra K A] [Module.Finite K A] :
    ¬ IsAzumaya K A ↔ ∀ p : NumberFieldPlace K,
      ¬ IsAzumaya (completion K p) (completion K p ⊗[K] A) :=
  not_iff_forall_not_of_iff_exists (numberField_isAzumaya_iff_exists_place K)

/-- Failure of the Azumaya property over `F(t)` persists at every completion. -/
theorem rationalFunction_algebra_not_isAzumaya_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    {A : Type w} [Ring A] [Algebra (RatFunc F) A] [Module.Finite (RatFunc F) A] :
    ¬ IsAzumaya (RatFunc F) A ↔ ∀ p : RationalFunctionPlace F,
      ¬ IsAzumaya (rationalFunctionCompletion F p)
        (rationalFunctionCompletion F p ⊗[RatFunc F] A) :=
  not_iff_forall_not_of_iff_exists (rationalFunction_isAzumaya_iff_exists_place F)

/-- Noncentrality of a finite-dimensional number-field algebra persists at every completion. -/
theorem numberField_algebra_not_isCentral_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    {A : Type w} [Ring A] [Algebra K A] [Module.Finite K A] :
    ¬ Algebra.IsCentral K A ↔ ∀ p : NumberFieldPlace K,
      ¬ Algebra.IsCentral (completion K p) (completion K p ⊗[K] A) :=
  not_iff_forall_not_of_iff_exists (numberField_isCentral_iff_exists_place K)

/-- Noncentrality of a finite-dimensional function-field algebra persists at every completion. -/
theorem rationalFunction_algebra_not_isCentral_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    {A : Type w} [Ring A] [Algebra (RatFunc F) A] [Module.Finite (RatFunc F) A] :
    ¬ Algebra.IsCentral (RatFunc F) A ↔ ∀ p : RationalFunctionPlace F,
      ¬ Algebra.IsCentral (rationalFunctionCompletion F p)
        (rationalFunctionCompletion F p ⊗[RatFunc F] A) :=
  not_iff_forall_not_of_iff_exists (rationalFunction_isCentral_iff_exists_place F)

/-- Nonsimplicity of a central number-field algebra persists at every completion. -/
theorem numberField_algebra_not_isSimpleRing_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    {A : Type w} [Ring A] [Algebra K A] [Algebra.IsCentral K A] [Module.Finite K A] :
    ¬ IsSimpleRing A ↔ ∀ p : NumberFieldPlace K,
      ¬ IsSimpleRing (completion K p ⊗[K] A) :=
  not_iff_forall_not_of_iff_exists (numberField_isSimpleRing_iff_exists_place K)

/-- Nonsimplicity of a central function-field algebra persists at every completion. -/
theorem rationalFunction_algebra_not_isSimpleRing_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    {A : Type w} [Ring A] [Algebra (RatFunc F) A]
    [Algebra.IsCentral (RatFunc F) A] [Module.Finite (RatFunc F) A] :
    ¬ IsSimpleRing A ↔ ∀ p : RationalFunctionPlace F,
      ¬ IsSimpleRing (rationalFunctionCompletion F p ⊗[RatFunc F] A) :=
  not_iff_forall_not_of_iff_exists (rationalFunction_isSimpleRing_iff_exists_place F)

/-- Failure of central simplicity over a number field persists at every completion. -/
theorem numberField_algebra_not_centralSimple_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    {A : Type w} [Ring A] [Algebra K A] [Module.Finite K A] :
    ¬ (Algebra.IsCentral K A ∧ IsSimpleRing A) ↔ ∀ p : NumberFieldPlace K,
      ¬ (Algebra.IsCentral (completion K p) (completion K p ⊗[K] A) ∧
        IsSimpleRing (completion K p ⊗[K] A)) :=
  not_iff_forall_not_of_iff_exists (numberField_isCentral_and_isSimpleRing_iff_exists_place K)

/-- Failure of central simplicity over `F(t)` persists at every completion. -/
theorem rationalFunction_algebra_not_centralSimple_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    {A : Type w} [Ring A] [Algebra (RatFunc F) A] [Module.Finite (RatFunc F) A] :
    ¬ (Algebra.IsCentral (RatFunc F) A ∧ IsSimpleRing A) ↔
      ∀ p : RationalFunctionPlace F,
        ¬ (Algebra.IsCentral (rationalFunctionCompletion F p)
          (rationalFunctionCompletion F p ⊗[RatFunc F] A) ∧
            IsSimpleRing (rationalFunctionCompletion F p ⊗[RatFunc F] A)) :=
  not_iff_forall_not_of_iff_exists
    (rationalFunction_isCentral_and_isSimpleRing_iff_exists_place F)

/-- Noncoprimality of number-field polynomials persists at every completion. -/
theorem numberFieldPolynomial_not_isCoprime_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (p q : Polynomial K) :
    ¬ IsCoprime p q ↔ ∀ v : NumberFieldPlace K,
      ¬ IsCoprime (p.map (algebraMap K (completion K v)))
        (q.map (algebraMap K (completion K v))) :=
  not_iff_forall_not_of_iff_exists (numberFieldPolynomial_isCoprime_iff_exists_place K p q)

/-- Noncoprimality of function-field polynomials persists at every completion. -/
theorem rationalFunctionPolynomial_not_isCoprime_iff_forall_place
    (F : Type u) [Field F] [Finite F] (p q : Polynomial (RatFunc F)) :
    ¬ IsCoprime p q ↔ ∀ v : RationalFunctionPlace F,
      ¬ IsCoprime (p.map (algebraMap (RatFunc F) (rationalFunctionCompletion F v)))
        (q.map (algebraMap (RatFunc F) (rationalFunctionCompletion F v))) :=
  not_iff_forall_not_of_iff_exists
    (rationalFunctionPolynomial_isCoprime_iff_exists_place F p q)

/-- Inseparability of a number-field polynomial persists at every completion. -/
theorem numberFieldPolynomial_not_separable_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (p : Polynomial K) :
    ¬ p.Separable ↔ ∀ v : NumberFieldPlace K,
      ¬ (p.map (algebraMap K (completion K v))).Separable :=
  not_iff_forall_not_of_iff_exists (numberFieldPolynomial_separable_iff_exists_place K p)

/-- Inseparability of a function-field polynomial persists at every completion. -/
theorem rationalFunctionPolynomial_not_separable_iff_forall_place
    (F : Type u) [Field F] [Finite F] (p : Polynomial (RatFunc F)) :
    ¬ p.Separable ↔ ∀ v : RationalFunctionPlace F,
      ¬ (p.map (algebraMap (RatFunc F) (rationalFunctionCompletion F v))).Separable :=
  not_iff_forall_not_of_iff_exists
    (rationalFunctionPolynomial_separable_iff_exists_place F p)

/-- Degeneracy of a number-field trace pairing persists at every completion. -/
theorem numberField_algebra_traceForm_degenerate_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    {B : Type w} [CommRing B] [Algebra K B] [Module.Free K B] [Module.Finite K B]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (e : Module.Basis ι K B) :
    ¬ (Algebra.traceForm K B).Nondegenerate ↔ ∀ p : NumberFieldPlace K,
      ¬ (Algebra.traceForm (completion K p) (completion K p ⊗[K] B)).Nondegenerate :=
  not_iff_forall_not_of_iff_exists
    (numberField_algebra_traceForm_nondegenerate_iff_exists_place K e)

/-- Degeneracy of a function-field trace pairing persists at every completion. -/
theorem rationalFunction_algebra_traceForm_degenerate_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    {B : Type w} [CommRing B] [Algebra (RatFunc F) B]
    [Module.Free (RatFunc F) B] [Module.Finite (RatFunc F) B]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (e : Module.Basis ι (RatFunc F) B) :
    ¬ (Algebra.traceForm (RatFunc F) B).Nondegenerate ↔ ∀ p : RationalFunctionPlace F,
      ¬ (Algebra.traceForm (rationalFunctionCompletion F p)
        (rationalFunctionCompletion F p ⊗[RatFunc F] B)).Nondegenerate :=
  not_iff_forall_not_of_iff_exists
    (rationalFunction_algebra_traceForm_nondegenerate_iff_exists_place F e)

end GaloisForLFunctions.HTGeometry.ABHN
