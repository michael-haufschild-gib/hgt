/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.HasseCentralSimple

/-!
# Selected-place Hasse detection for finite-dimensional algebras

Every completion of either supported global-field model is faithfully flat.  Thus Azumaya-ness,
centrality, simplicity, and central simplicity of a finite-dimensional algebra are reflected at
each specified completion, not only by an all-place or existential test.  These are structural
local--global equivalences; they do not identify local Brauer classes or prove ABHN.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

universe u v w

/-- Azumaya-ness of a finite-dimensional number-field algebra is reflected at every specified
completion. -/
theorem numberField_isAzumaya_iff_at_place (K : Type u)
    [Field K] [NumberField K] {A : Type w} [Ring A] [Algebra K A] [Module.Finite K A]
    (p : NumberFieldPlace K) :
    IsAzumaya K A ↔ IsAzumaya (completion K p) (completion K p ⊗[K] A) := by
  exact isAzumaya_iff_tensorProduct_isAzumaya (L := completion K p)

/-- Azumaya-ness of a finite-dimensional algebra over `F(t)` is reflected at every specified
finite or infinite completion. -/
theorem rationalFunction_isAzumaya_iff_at_place (F : Type u)
    [Field F] [Finite F] {A : Type w} [Ring A] [Algebra (RatFunc F) A]
    [Module.Finite (RatFunc F) A] (p : RationalFunctionPlace F) :
    IsAzumaya (RatFunc F) A ↔
      IsAzumaya (rationalFunctionCompletion F p)
        (rationalFunctionCompletion F p ⊗[RatFunc F] A) := by
  exact isAzumaya_iff_tensorProduct_isAzumaya
    (L := rationalFunctionCompletion F p)

/-- Centrality of a finite-dimensional number-field algebra is reflected at every specified
completion. -/
theorem numberField_isCentral_iff_at_place (K : Type u) [Field K] [NumberField K]
    {A : Type w} [Ring A] [Algebra K A] [Module.Finite K A]
    (p : NumberFieldPlace K) :
    Algebra.IsCentral K A ↔ Algebra.IsCentral (completion K p) (completion K p ⊗[K] A) := by
  exact isCentral_iff_tensorProduct_isCentral (L := completion K p)

/-- Centrality of a finite-dimensional algebra over `F(t)` is reflected at every specified
finite or infinite completion. -/
theorem rationalFunction_isCentral_iff_at_place (F : Type u) [Field F] [Finite F]
    {A : Type w} [Ring A] [Algebra (RatFunc F) A] [Module.Finite (RatFunc F) A]
    (p : RationalFunctionPlace F) :
    Algebra.IsCentral (RatFunc F) A ↔
      Algebra.IsCentral (rationalFunctionCompletion F p)
        (rationalFunctionCompletion F p ⊗[RatFunc F] A) := by
  exact isCentral_iff_tensorProduct_isCentral (L := rationalFunctionCompletion F p)

/-- Simplicity of a finite-dimensional central number-field algebra is reflected at every
specified completion. -/
theorem numberField_isSimpleRing_iff_at_place (K : Type u) [Field K] [NumberField K]
    {A : Type w} [Ring A] [Algebra K A] [Algebra.IsCentral K A] [Module.Finite K A]
    (p : NumberFieldPlace K) :
    IsSimpleRing A ↔ IsSimpleRing (completion K p ⊗[K] A) := by
  exact isSimpleRing_iff_tensorProduct_isSimpleRing (L := completion K p)

/-- Simplicity of a finite-dimensional central algebra over `F(t)` is reflected at every
specified finite or infinite completion. -/
theorem rationalFunction_isSimpleRing_iff_at_place (F : Type u) [Field F] [Finite F]
    {A : Type w} [Ring A] [Algebra (RatFunc F) A] [Algebra.IsCentral (RatFunc F) A]
    [Module.Finite (RatFunc F) A] (p : RationalFunctionPlace F) :
    IsSimpleRing A ↔ IsSimpleRing (rationalFunctionCompletion F p ⊗[RatFunc F] A) := by
  exact isSimpleRing_iff_tensorProduct_isSimpleRing
    (L := rationalFunctionCompletion F p)

/-- Central simplicity of a finite-dimensional number-field algebra is reflected at every
specified completion. -/
theorem numberField_isCentral_and_isSimpleRing_iff_at_place
    (K : Type u) [Field K] [NumberField K] {A : Type w} [Ring A] [Algebra K A]
    [Module.Finite K A] (p : NumberFieldPlace K) :
    (Algebra.IsCentral K A ∧ IsSimpleRing A) ↔
      Algebra.IsCentral (completion K p) (completion K p ⊗[K] A) ∧
        IsSimpleRing (completion K p ⊗[K] A) := by
  exact isCentral_and_isSimpleRing_iff_tensorProduct (L := completion K p)

/-- Central simplicity of a finite-dimensional algebra over `F(t)` is reflected at every
specified finite or infinite completion. -/
theorem rationalFunction_isCentral_and_isSimpleRing_iff_at_place
    (F : Type u) [Field F] [Finite F] {A : Type w} [Ring A] [Algebra (RatFunc F) A]
    [Module.Finite (RatFunc F) A] (p : RationalFunctionPlace F) :
    (Algebra.IsCentral (RatFunc F) A ∧ IsSimpleRing A) ↔
      Algebra.IsCentral (rationalFunctionCompletion F p)
          (rationalFunctionCompletion F p ⊗[RatFunc F] A) ∧
        IsSimpleRing (rationalFunctionCompletion F p ⊗[RatFunc F] A) := by
  exact isCentral_and_isSimpleRing_iff_tensorProduct
    (L := rationalFunctionCompletion F p)

end GaloisForLFunctions.HTGeometry.ABHN
