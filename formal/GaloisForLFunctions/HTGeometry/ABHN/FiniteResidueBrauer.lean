/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.FiniteFieldBrauer
import GaloisForLFunctions.HTGeometry.ABHN.LaurentSeriesFiniteLocalField
import GaloisForLFunctions.HTGeometry.ABHN.RationalFunctionFiniteLocalField

/-!
# Trivial residue Brauer groups at concrete ABHN places

The residue fields of the existing nonarchimedean models are finite.  Their Brauer groups are
therefore trivial.  These are residue-field statements, not assertions that the Brauer groups of
the local fields themselves vanish.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open IsDedekindDomain
open scoped LaurentSeries Polynomial ValuativeRel

universe u

/-- The residue Brauer group at every finite rational completion is trivial. -/
theorem rationalFinitePlace_residueBrauerGroup_subsingleton (v : NumberField.FinitePlace ℚ) :
    Subsingleton (BrauerGroup.{0, 0} 𝓀[completion ℚ (.finite v)]) :=
  finiteField_brauerGroup_subsingleton _

/-- The residue Brauer group of a finite-coefficient Laurent-series field is trivial. -/
theorem laurentSeries_residueBrauerGroup_subsingleton (F : Type u) [Field F] [Finite F] :
    Subsingleton (BrauerGroup.{u, u} 𝓀[F⸨X⸩]) :=
  finiteField_brauerGroup_subsingleton _

/-- The residue Brauer group at every finite completion of `F(t)` is trivial. -/
theorem rationalFunctionFinitePlace_residueBrauerGroup_subsingleton (F : Type u) [Field F]
    [Finite F] (v : HeightOneSpectrum F[X]) :
    Subsingleton (BrauerGroup.{u, u} 𝓀[rationalFunctionCompletion F (.finite v)]) :=
  finiteField_brauerGroup_subsingleton _

end GaloisForLFunctions.HTGeometry.ABHN
