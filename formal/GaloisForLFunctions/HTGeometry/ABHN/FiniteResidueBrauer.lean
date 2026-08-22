/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.LaurentSeriesFiniteLocalField
import GaloisForLFunctions.HTGeometry.ABHN.LocalFieldResidueBrauer
import GaloisForLFunctions.HTGeometry.ABHN.NumberFieldFiniteLocalField
import GaloisForLFunctions.HTGeometry.ABHN.RationalFunctionFiniteLocalField
import GaloisForLFunctions.HTGeometry.ABHN.RationalFunctionInfinityCompletion

/-!
# Trivial residue Brauer groups at concrete ABHN places

The residue fields of the existing nonarchimedean models are finite.  Their Brauer groups are
therefore trivial.  These are residue-field statements, not assertions that the Brauer groups of
the local fields themselves vanish.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open IsDedekindDomain
open scoped LaurentSeries Polynomial ValuativeRel

universe u v

/-- The residue Brauer group at every finite number-field completion is trivial. -/
theorem numberFieldFinitePlace_residueBrauerGroup_subsingleton
    (K : Type u) [Field K] [NumberField K] (v : NumberField.FinitePlace K) :
    Subsingleton (BrauerGroup.{u, u} 𝓀[completion K (.finite v)]) :=
  nonarchimedeanLocalField_residueBrauerGroup_subsingleton _

/-- Every additive observable of the residue Brauer group at a finite number-field place is
zero.  Thus this residue term alone cannot carry a nonzero local source contribution. -/
theorem numberFieldFinitePlace_residueBrauerAddHom_eq_zero
    (K : Type u) [Field K] [NumberField K] (v : NumberField.FinitePlace K)
    (A : Type v) [AddCommMonoid A]
    (f : BrauerGroup.{u, u} 𝓀[completion K (.finite v)] →+ A) :
    f = 0 :=
  nonarchimedeanLocalField_residueBrauerAddHom_eq_zero
    (completion K (.finite v)) A f

/-- The residue Brauer group at every finite rational completion is trivial. -/
theorem rationalFinitePlace_residueBrauerGroup_subsingleton (v : NumberField.FinitePlace ℚ) :
    Subsingleton (BrauerGroup.{0, 0} 𝓀[completion ℚ (.finite v)]) :=
  nonarchimedeanLocalField_residueBrauerGroup_subsingleton _

/-- Every additive observable of the residue Brauer group at a finite rational place is zero. -/
theorem rationalFinitePlace_residueBrauerAddHom_eq_zero
    (v : NumberField.FinitePlace ℚ) (A : Type u) [AddCommMonoid A]
    (f : BrauerGroup.{0, 0} 𝓀[completion ℚ (.finite v)] →+ A) :
    f = 0 :=
  nonarchimedeanLocalField_residueBrauerAddHom_eq_zero
    (completion ℚ (.finite v)) A f

/-- The residue Brauer group of a finite-coefficient Laurent-series field is trivial. -/
theorem laurentSeries_residueBrauerGroup_subsingleton (F : Type u) [Field F] [Finite F] :
    Subsingleton (BrauerGroup.{u, u} 𝓀[F⸨X⸩]) :=
  nonarchimedeanLocalField_residueBrauerGroup_subsingleton _

/-- Every additive observable of a finite-coefficient Laurent-series residue Brauer group is
zero. -/
theorem laurentSeries_residueBrauerAddHom_eq_zero
    (F : Type u) [Field F] [Finite F] (A : Type v) [AddCommMonoid A]
    (f : BrauerGroup.{u, u} 𝓀[F⸨X⸩] →+ A) :
    f = 0 :=
  nonarchimedeanLocalField_residueBrauerAddHom_eq_zero F⸨X⸩ A f

/-- The residue Brauer group at every finite completion of `F(t)` is trivial. -/
theorem rationalFunctionFinitePlace_residueBrauerGroup_subsingleton (F : Type u) [Field F]
    [Finite F] (v : HeightOneSpectrum F[X]) :
    Subsingleton (BrauerGroup.{u, u} 𝓀[rationalFunctionCompletion F (.finite v)]) :=
  nonarchimedeanLocalField_residueBrauerGroup_subsingleton _

/-- Every additive observable of the residue Brauer group at a finite place of `F(t)` is zero. -/
theorem rationalFunctionFinitePlace_residueBrauerAddHom_eq_zero
    (F : Type u) [Field F] [Finite F] (v : HeightOneSpectrum F[X])
    (A : Type v) [AddCommMonoid A]
    (f : BrauerGroup.{u, u} 𝓀[rationalFunctionCompletion F (.finite v)] →+ A) :
    f = 0 :=
  nonarchimedeanLocalField_residueBrauerAddHom_eq_zero
    (rationalFunctionCompletion F (.finite v)) A f

/-- The residue Brauer group at the infinite completion of `F(t)` is trivial. -/
theorem rationalFunctionInfinitePlace_residueBrauerGroup_subsingleton (F : Type u) [Field F]
    [Finite F] :
    Subsingleton (BrauerGroup.{u, u} 𝓀[rationalFunctionCompletion F .infinite]) :=
  nonarchimedeanLocalField_residueBrauerGroup_subsingleton _

/-- Every additive observable of the residue Brauer group at the infinite place of `F(t)` is
zero. -/
theorem rationalFunctionInfinitePlace_residueBrauerAddHom_eq_zero
    (F : Type u) [Field F] [Finite F] (A : Type v) [AddCommMonoid A]
    (f : BrauerGroup.{u, u} 𝓀[rationalFunctionCompletion F .infinite] →+ A) :
    f = 0 :=
  nonarchimedeanLocalField_residueBrauerAddHom_eq_zero
    (rationalFunctionCompletion F .infinite) A f

/-- The residue Brauer group at every finite number-field completion has its canonical zero-valued
invariant. It concerns the residue field, not the Brauer group of the completion itself. -/
noncomputable def numberFieldFinitePlace_residueBrauerInvariantAddEquivBot
    (K : Type u) [Field K] [NumberField K] (v : NumberField.FinitePlace K) :
    BrauerGroup.{u, u} 𝓀[completion K (.finite v)] ≃+ (⊥ : AddSubgroup RatModInt) :=
  nonarchimedeanLocalField_residueBrauerInvariantAddEquivBot _

/-- The residue Brauer group at every finite rational completion has its canonical zero-valued
invariant.  It concerns the residue field, not the Brauer group of the completion itself. -/
noncomputable def rationalFinitePlace_residueBrauerInvariantAddEquivBot
    (v : NumberField.FinitePlace ℚ) :
    BrauerGroup.{0, 0} 𝓀[completion ℚ (.finite v)] ≃+ (⊥ : AddSubgroup RatModInt) :=
  nonarchimedeanLocalField_residueBrauerInvariantAddEquivBot _

/-- The residue Brauer group of a Laurent-series field over a finite field has its canonical
zero-valued invariant. -/
noncomputable def laurentSeries_residueBrauerInvariantAddEquivBot
    (F : Type u) [Field F] [Finite F] :
    BrauerGroup.{u, u} 𝓀[F⸨X⸩] ≃+ (⊥ : AddSubgroup RatModInt) :=
  nonarchimedeanLocalField_residueBrauerInvariantAddEquivBot _

/-- The residue Brauer group at every finite completion of `F(t)` has its canonical zero-valued
invariant. -/
noncomputable def rationalFunctionFinitePlace_residueBrauerInvariantAddEquivBot
    (F : Type u) [Field F] [Finite F] (v : HeightOneSpectrum F[X]) :
    BrauerGroup.{u, u} 𝓀[rationalFunctionCompletion F (.finite v)] ≃+
      (⊥ : AddSubgroup RatModInt) :=
  nonarchimedeanLocalField_residueBrauerInvariantAddEquivBot _

/-- The residue Brauer group at the infinite completion of `F(t)` has its canonical zero-valued
invariant. -/
noncomputable def rationalFunctionInfinitePlace_residueBrauerInvariantAddEquivBot
    (F : Type u) [Field F] [Finite F] :
    BrauerGroup.{u, u} 𝓀[rationalFunctionCompletion F .infinite] ≃+
      (⊥ : AddSubgroup RatModInt) :=
  nonarchimedeanLocalField_residueBrauerInvariantAddEquivBot _

end GaloisForLFunctions.HTGeometry.ABHN
