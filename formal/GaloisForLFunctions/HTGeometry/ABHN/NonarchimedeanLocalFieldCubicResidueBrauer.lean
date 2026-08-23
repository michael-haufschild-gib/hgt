/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.NonarchimedeanLocalFieldValuationSequence
import GaloisForLFunctions.HTGeometry.ABHN.FiniteFieldCubicCyclicBrauer

/-!
# Cubic cyclic residue classes of unramified local lifts

A finite unramified root lift of a nonarchimedean local field has a finite cyclic Galois residue
extension. Thus every cubic cyclic degree-two class has split selected residue Brauer class. This
remains a residue-field result; comparison with the local fraction-field Brauer group is separate
local class field theory.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open CategoryTheory groupCohomology Rep Rep.FiniteCyclicGroup
open scoped ValuativeRel

attribute [local instance] IsCyclic.commGroup

/-- Every cubic cyclic degree-two residue class of a finite unramified root lift selects the
split residue Brauer class. -/
theorem nonarchimedeanLocalFieldAdjoinRootResidueField_cubicCyclicGaloisH2BrauerMap_eq_split
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
    letI : Finite (IsLocalRing.ResidueField (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRootResidueField_finite K f hf g hgmonic hfg hg
    letI : Module.Finite 𝓀[K] (IsLocalRing.ResidueField (AdjoinRoot f)) :=
      Module.Finite.of_finite
    letI : IsGalois 𝓀[K] (IsLocalRing.ResidueField (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRootResidueField_isGalois K f hf g hgmonic hfg hg
    letI : IsCyclic Gal(IsLocalRing.ResidueField (AdjoinRoot f) / 𝓀[K]) :=
      nonarchimedeanLocalFieldAdjoinRootResidueField_isCyclic K f hf g hgmonic hfg hg
    ∀ (hdeg : Module.finrank 𝓀[K] (IsLocalRing.ResidueField (AdjoinRoot f)) = 3)
      (z : cyclicGaloisH2 𝓀[K] (IsLocalRing.ResidueField (AdjoinRoot f))),
      cubicCyclicGaloisH2BrauerMap 𝓀[K] (IsLocalRing.ResidueField (AdjoinRoot f)) hdeg z =
        brauerSplitClass 𝓀[K] := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  letI : Finite (IsLocalRing.ResidueField (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRootResidueField_finite K f hf g hgmonic hfg hg
  letI : Module.Finite 𝓀[K] (IsLocalRing.ResidueField (AdjoinRoot f)) :=
    Module.Finite.of_finite
  letI : IsGalois 𝓀[K] (IsLocalRing.ResidueField (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRootResidueField_isGalois K f hf g hgmonic hfg hg
  letI : IsCyclic Gal(IsLocalRing.ResidueField (AdjoinRoot f) / 𝓀[K]) :=
    nonarchimedeanLocalFieldAdjoinRootResidueField_isCyclic K f hf g hgmonic hfg hg
  intro hdeg z
  exact finiteField_cubicCyclicGaloisH2BrauerMap_eq_split
    𝓀[K] (IsLocalRing.ResidueField (AdjoinRoot f)) hdeg z

end GaloisForLFunctions.HTGeometry.ABHN
