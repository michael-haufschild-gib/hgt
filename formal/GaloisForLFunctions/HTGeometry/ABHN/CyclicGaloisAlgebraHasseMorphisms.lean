/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisAlgebraCompanionRepresentation
import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraHomEquality

/-!
# Hasse tests for cyclic Galois algebra morphisms

Equality, diagram commutation, and injectivity/surjectivity of algebra endomorphisms of a cyclic
Galois algebra are reflected by scalar extension to global-field completions.  These statements
need only the cyclic algebra's algebra structure, so they apply even at parameter zero; the
central-simple Brauer interface is not needed here.

They compare specified global morphisms and their scalar extensions.  They do not descend a
separately chosen family of local morphisms.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

/-- Two endomorphisms of a cyclic Galois algebra over a number field are equal exactly when all
their completed scalar extensions are equal. -/
theorem numberField_cyclicGaloisAlgebra_algHom_eq_iff_forall_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (f g : cyclicGaloisAlgebra K L a →ₐ[K] cyclicGaloisAlgebra K L a) :
    f = g ↔ ∀ p : NumberFieldPlace K,
      algHomBaseChange (L := completion K p) f = algHomBaseChange (L := completion K p) g :=
  numberField_algHom_eq_iff_forall_place K f g

/-- Two endomorphisms of a cyclic Galois algebra over a global function field are equal exactly
when all their completed scalar extensions are equal. -/
theorem rationalFunction_cyclicGaloisAlgebra_algHom_eq_iff_forall_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F)
    (f g : cyclicGaloisAlgebra (RatFunc F) L a →ₐ[RatFunc F]
      cyclicGaloisAlgebra (RatFunc F) L a) :
    f = g ↔ ∀ p : RationalFunctionPlace F,
      algHomBaseChange (L := rationalFunctionCompletion F p) f =
        algHomBaseChange (L := rationalFunctionCompletion F p) g :=
  rationalFunction_algHom_eq_iff_forall_place F f g

/-- A specified endomorphism diagram of a cyclic Galois algebra over a number field commutes
exactly when its scalar extensions commute at every completion. -/
theorem numberField_cyclicGaloisAlgebra_algHom_comp_eq_iff_forall_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (f g h : cyclicGaloisAlgebra K L a →ₐ[K] cyclicGaloisAlgebra K L a) :
    g.comp f = h ↔ ∀ p : NumberFieldPlace K,
      (algHomBaseChange (L := completion K p) g).comp
          (algHomBaseChange (L := completion K p) f) =
        algHomBaseChange (L := completion K p) h :=
  numberField_algHom_comp_eq_iff_forall_place K f g h

/-- A specified endomorphism diagram of a cyclic Galois algebra over a global function field
commutes exactly when its scalar extensions commute at every completion. -/
theorem rationalFunction_cyclicGaloisAlgebra_algHom_comp_eq_iff_forall_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F)
    (f g h : cyclicGaloisAlgebra (RatFunc F) L a →ₐ[RatFunc F]
      cyclicGaloisAlgebra (RatFunc F) L a) :
    g.comp f = h ↔ ∀ p : RationalFunctionPlace F,
      (algHomBaseChange (L := rationalFunctionCompletion F p) g).comp
          (algHomBaseChange (L := rationalFunctionCompletion F p) f) =
        algHomBaseChange (L := rationalFunctionCompletion F p) h :=
  rationalFunction_algHom_comp_eq_iff_forall_place F f g h

/-- Two cyclic Galois algebra automorphisms over a number field are equal exactly when their
completed scalar extensions are equal. -/
theorem numberField_cyclicGaloisAlgebra_algEquiv_eq_iff_forall_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (e f : cyclicGaloisAlgebra K L a ≃ₐ[K] cyclicGaloisAlgebra K L a) :
    e = f ↔ ∀ p : NumberFieldPlace K,
      algEquivBaseChange (L := completion K p) e = algEquivBaseChange (L := completion K p) f :=
  numberField_algEquiv_eq_iff_forall_place K e f

/-- Two cyclic Galois algebra automorphisms over a global function field are equal exactly when
their completed scalar extensions are equal. -/
theorem rationalFunction_cyclicGaloisAlgebra_algEquiv_eq_iff_forall_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F)
    (e f : cyclicGaloisAlgebra (RatFunc F) L a ≃ₐ[RatFunc F]
      cyclicGaloisAlgebra (RatFunc F) L a) :
    e = f ↔ ∀ p : RationalFunctionPlace F,
      algEquivBaseChange (L := rationalFunctionCompletion F p) e =
        algEquivBaseChange (L := rationalFunctionCompletion F p) f :=
  rationalFunction_algEquiv_eq_iff_forall_place F e f

/-- Injectivity of a cyclic Galois algebra endomorphism over a number field is detected at every
completion. -/
theorem numberField_cyclicGaloisAlgebra_algHom_injective_iff_forall_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (f : cyclicGaloisAlgebra K L a →ₐ[K] cyclicGaloisAlgebra K L a) :
    Function.Injective f ↔ ∀ p : NumberFieldPlace K,
      Function.Injective (algHomBaseChange (L := completion K p) f) :=
  numberField_algHom_injective_iff_forall_place K f

/-- Injectivity of a cyclic Galois algebra endomorphism over a global function field is detected
at every completion. -/
theorem rationalFunction_cyclicGaloisAlgebra_algHom_injective_iff_forall_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F)
    (f : cyclicGaloisAlgebra (RatFunc F) L a →ₐ[RatFunc F]
      cyclicGaloisAlgebra (RatFunc F) L a) :
    Function.Injective f ↔ ∀ p : RationalFunctionPlace F,
      Function.Injective (algHomBaseChange (L := rationalFunctionCompletion F p) f) :=
  rationalFunction_algHom_injective_iff_forall_place F f

/-- Surjectivity of a cyclic Galois algebra endomorphism over a number field is detected at every
completion. -/
theorem numberField_cyclicGaloisAlgebra_algHom_surjective_iff_forall_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (f : cyclicGaloisAlgebra K L a →ₐ[K] cyclicGaloisAlgebra K L a) :
    Function.Surjective f ↔ ∀ p : NumberFieldPlace K,
      Function.Surjective (algHomBaseChange (L := completion K p) f) :=
  numberField_algHom_surjective_iff_forall_place K f

/-- Surjectivity of a cyclic Galois algebra endomorphism over a global function field is detected
at every completion. -/
theorem rationalFunction_cyclicGaloisAlgebra_algHom_surjective_iff_forall_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F)
    (f : cyclicGaloisAlgebra (RatFunc F) L a →ₐ[RatFunc F]
      cyclicGaloisAlgebra (RatFunc F) L a) :
    Function.Surjective f ↔ ∀ p : RationalFunctionPlace F,
      Function.Surjective (algHomBaseChange (L := rationalFunctionCompletion F p) f) :=
  rationalFunction_algHom_surjective_iff_forall_place F f

/-- Bijectivity of a cyclic Galois algebra endomorphism over a number field is detected at every
completion. -/
theorem numberField_cyclicGaloisAlgebra_algHom_bijective_iff_forall_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (f : cyclicGaloisAlgebra K L a →ₐ[K] cyclicGaloisAlgebra K L a) :
    Function.Bijective f ↔ ∀ p : NumberFieldPlace K,
      Function.Bijective (algHomBaseChange (L := completion K p) f) :=
  numberField_algHom_bijective_iff_forall_place K f

/-- Bijectivity of a cyclic Galois algebra endomorphism over a global function field is detected
at every completion. -/
theorem rationalFunction_cyclicGaloisAlgebra_algHom_bijective_iff_forall_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F)
    (f : cyclicGaloisAlgebra (RatFunc F) L a →ₐ[RatFunc F]
      cyclicGaloisAlgebra (RatFunc F) L a) :
    Function.Bijective f ↔ ∀ p : RationalFunctionPlace F,
      Function.Bijective (algHomBaseChange (L := rationalFunctionCompletion F p) f) :=
  rationalFunction_algHom_bijective_iff_forall_place F f

/-- Injectivity of a cyclic Galois algebra endomorphism over a number field can be certified at
one completion. -/
theorem numberField_cyclicGaloisAlgebra_algHom_injective_iff_exists_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (f : cyclicGaloisAlgebra K L a →ₐ[K] cyclicGaloisAlgebra K L a) :
    Function.Injective f ↔ ∃ p : NumberFieldPlace K,
      Function.Injective (algHomBaseChange (L := completion K p) f) :=
  numberField_algHom_injective_iff_exists_place K f

/-- Injectivity of a cyclic Galois algebra endomorphism over a global function field can be
certified at one completion. -/
theorem rationalFunction_cyclicGaloisAlgebra_algHom_injective_iff_exists_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F)
    (f : cyclicGaloisAlgebra (RatFunc F) L a →ₐ[RatFunc F]
      cyclicGaloisAlgebra (RatFunc F) L a) :
    Function.Injective f ↔ ∃ p : RationalFunctionPlace F,
      Function.Injective (algHomBaseChange (L := rationalFunctionCompletion F p) f) :=
  rationalFunction_algHom_injective_iff_exists_place F f

/-- Surjectivity of a cyclic Galois algebra endomorphism over a number field can be certified at
one completion. -/
theorem numberField_cyclicGaloisAlgebra_algHom_surjective_iff_exists_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (f : cyclicGaloisAlgebra K L a →ₐ[K] cyclicGaloisAlgebra K L a) :
    Function.Surjective f ↔ ∃ p : NumberFieldPlace K,
      Function.Surjective (algHomBaseChange (L := completion K p) f) :=
  numberField_algHom_surjective_iff_exists_place K f

/-- Surjectivity of a cyclic Galois algebra endomorphism over a global function field can be
certified at one completion. -/
theorem rationalFunction_cyclicGaloisAlgebra_algHom_surjective_iff_exists_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F)
    (f : cyclicGaloisAlgebra (RatFunc F) L a →ₐ[RatFunc F]
      cyclicGaloisAlgebra (RatFunc F) L a) :
    Function.Surjective f ↔ ∃ p : RationalFunctionPlace F,
      Function.Surjective (algHomBaseChange (L := rationalFunctionCompletion F p) f) :=
  rationalFunction_algHom_surjective_iff_exists_place F f

/-- Bijectivity of a cyclic Galois algebra endomorphism over a number field can be certified at
one completion. -/
theorem numberField_cyclicGaloisAlgebra_algHom_bijective_iff_exists_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (f : cyclicGaloisAlgebra K L a →ₐ[K] cyclicGaloisAlgebra K L a) :
    Function.Bijective f ↔ ∃ p : NumberFieldPlace K,
      Function.Bijective (algHomBaseChange (L := completion K p) f) :=
  numberField_algHom_bijective_iff_exists_place K f

/-- Bijectivity of a cyclic Galois algebra endomorphism over a global function field can be
certified at one completion. -/
theorem rationalFunction_cyclicGaloisAlgebra_algHom_bijective_iff_exists_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F)
    (f : cyclicGaloisAlgebra (RatFunc F) L a →ₐ[RatFunc F]
      cyclicGaloisAlgebra (RatFunc F) L a) :
    Function.Bijective f ↔ ∃ p : RationalFunctionPlace F,
      Function.Bijective (algHomBaseChange (L := rationalFunctionCompletion F p) f) :=
  rationalFunction_algHom_bijective_iff_exists_place F f

end GaloisForLFunctions.HTGeometry.ABHN
