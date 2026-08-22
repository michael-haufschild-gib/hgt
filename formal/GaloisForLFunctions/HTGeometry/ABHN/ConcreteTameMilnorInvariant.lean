/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.ConcreteLocalMilnorResidue
import GaloisForLFunctions.HTGeometry.ABHN.RationalFunctionInfinityCompletion
import GaloisForLFunctions.HTGeometry.ABHN.TameMilnorInvariant

/-!
# Tame Milnor invariants at concrete ABHN local models

The generic nonarchimedean tame invariant supplies an exact sequence for finite completions used
by the number-field and global-function-field interfaces, for the packaged infinite completion
of `F(t)`, and for the Laurent-series model.  These are closed `K₂` local-invariant sequences.
They are not claims about local Brauer groups: the Milnor--Brauer comparison remains a separate
bridge.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open IsDedekindDomain
open scoped LaurentSeries Polynomial ValuativeRel

universe u

/-- At a finite number-field place, the raw tame invariant has exactly the tame-residue kernel. -/
theorem numberFieldFinitePlace_tameMilnorInvariantRaw_ker
    (K : Type u) [Field K] [NumberField K] (v : NumberField.FinitePlace K) :
    (nonarchimedeanLocalFieldTameMilnorInvariantRaw (completion K (.finite v))).ker =
      (nonarchimedeanLocalFieldTameMilnorResidue (completion K (.finite v))).ker :=
  nonarchimedeanLocalFieldTameMilnorInvariantRaw_ker (completion K (.finite v))

/-- At a finite number-field place, inclusion of the tame kernel followed by the raw tame
invariant is exact. -/
theorem numberFieldFinitePlace_tameMilnorInvariantRaw_exact
    (K : Type u) [Field K] [NumberField K] (v : NumberField.FinitePlace K) :
    Function.Exact
      ((nonarchimedeanLocalFieldTameMilnorResidue (completion K (.finite v))).ker).subtype
      (nonarchimedeanLocalFieldTameMilnorInvariantRaw (completion K (.finite v))) :=
  nonarchimedeanLocalFieldTameMilnorInvariantRaw_exact (completion K (.finite v))

/-- At a finite place of `F(t)`, the raw tame invariant has exactly the tame-residue kernel. -/
theorem rationalFunctionFinitePlace_tameMilnorInvariantRaw_ker
    (F : Type u) [Field F] [Finite F] (v : HeightOneSpectrum F[X]) :
    (nonarchimedeanLocalFieldTameMilnorInvariantRaw
      (rationalFunctionCompletion F (.finite v))).ker =
      (nonarchimedeanLocalFieldTameMilnorResidue
        (rationalFunctionCompletion F (.finite v))).ker :=
  nonarchimedeanLocalFieldTameMilnorInvariantRaw_ker
    (rationalFunctionCompletion F (.finite v))

/-- At a finite place of `F(t)`, inclusion of the tame kernel followed by the raw tame
invariant is exact. -/
theorem rationalFunctionFinitePlace_tameMilnorInvariantRaw_exact
    (F : Type u) [Field F] [Finite F] (v : HeightOneSpectrum F[X]) :
    Function.Exact
      ((nonarchimedeanLocalFieldTameMilnorResidue
        (rationalFunctionCompletion F (.finite v))).ker).subtype
      (nonarchimedeanLocalFieldTameMilnorInvariantRaw
        (rationalFunctionCompletion F (.finite v))) :=
  nonarchimedeanLocalFieldTameMilnorInvariantRaw_exact
    (rationalFunctionCompletion F (.finite v))

/-- At the infinite place of `F(t)`, the raw tame invariant has exactly the tame-residue kernel. -/
theorem rationalFunctionInfinitePlace_tameMilnorInvariantRaw_ker
    (F : Type u) [Field F] [Finite F] :
    (nonarchimedeanLocalFieldTameMilnorInvariantRaw
      (rationalFunctionCompletion F .infinite)).ker =
      (nonarchimedeanLocalFieldTameMilnorResidue
        (rationalFunctionCompletion F .infinite)).ker :=
  nonarchimedeanLocalFieldTameMilnorInvariantRaw_ker
    (rationalFunctionCompletion F .infinite)

/-- At the infinite place of `F(t)`, inclusion of the tame kernel followed by the raw tame
invariant is exact. -/
theorem rationalFunctionInfinitePlace_tameMilnorInvariantRaw_exact
    (F : Type u) [Field F] [Finite F] :
    Function.Exact
      ((nonarchimedeanLocalFieldTameMilnorResidue
        (rationalFunctionCompletion F .infinite)).ker).subtype
      (nonarchimedeanLocalFieldTameMilnorInvariantRaw
        (rationalFunctionCompletion F .infinite)) :=
  nonarchimedeanLocalFieldTameMilnorInvariantRaw_exact
    (rationalFunctionCompletion F .infinite)

/-- In the Laurent-series local model, the raw tame invariant has exactly the tame-residue
kernel. -/
theorem laurentSeries_tameMilnorInvariantRaw_ker
    (F : Type u) [Field F] [Finite F] :
    (nonarchimedeanLocalFieldTameMilnorInvariantRaw F⸨X⸩).ker =
      (nonarchimedeanLocalFieldTameMilnorResidue F⸨X⸩).ker :=
  nonarchimedeanLocalFieldTameMilnorInvariantRaw_ker F⸨X⸩

/-- In the Laurent-series local model, inclusion of the tame kernel followed by the raw tame
invariant is exact. -/
theorem laurentSeries_tameMilnorInvariantRaw_exact
    (F : Type u) [Field F] [Finite F] :
    Function.Exact
      ((nonarchimedeanLocalFieldTameMilnorResidue F⸨X⸩).ker).subtype
      (nonarchimedeanLocalFieldTameMilnorInvariantRaw F⸨X⸩) :=
  nonarchimedeanLocalFieldTameMilnorInvariantRaw_exact F⸨X⸩

end GaloisForLFunctions.HTGeometry.ABHN
