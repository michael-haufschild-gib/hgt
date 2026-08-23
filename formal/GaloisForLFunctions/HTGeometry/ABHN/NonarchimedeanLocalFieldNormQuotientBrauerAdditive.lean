/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.NonarchimedeanLocalFieldNormQuotientBrauer
import GaloisForLFunctions.HTGeometry.ABHN.QuadraticCyclicGaloisH2BrauerAdditive
import GaloisForLFunctions.HTGeometry.ABHN.RatModIntTorsion

/-!
# Additivity of quadratic unramified local Brauer parameters

For an unramified quadratic root lift of a nonarchimedean local field, the valuation norm
quotient identifies the parameter group with `ℤ/2ℤ`.  The resulting selected Brauer parameter
map is therefore a closed additive map.  This is a finite-level local Brauer construction; it
does not identify the full local Brauer group with `ℚ/ℤ`.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped ValuativeRel WithZero WithZeroMulInt

/-- The concrete quadratic unramified local norm-quotient Brauer parameter map preserves
addition. -/
theorem nonarchimedeanLocalFieldAdjoinRootFractionField_quadraticNormQuotientBrauerMap_add
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g)
    (hdegree : f.natDegree = 2) (x y : ZMod 2) :
    nonarchimedeanLocalFieldAdjoinRootFractionField_quadraticNormQuotientBrauerMap
      K f hf g hgmonic hfg hg hdegree (x + y) =
      nonarchimedeanLocalFieldAdjoinRootFractionField_quadraticNormQuotientBrauerMap
        K f hf g hgmonic hfg hg hdegree x +
      nonarchimedeanLocalFieldAdjoinRootFractionField_quadraticNormQuotientBrauerMap
        K f hf g hgmonic hfg hg hdegree y := by
  unfold nonarchimedeanLocalFieldAdjoinRootFractionField_quadraticNormQuotientBrauerMap
  rw [quadraticCyclicNormQuotientBrauerMap_eq_addHom,
    quadraticCyclicNormQuotientBrauerMap_eq_addHom,
    quadraticCyclicNormQuotientBrauerMap_eq_addHom]
  apply AddMonoidHom.map_add

/-- The additive refinement of the concrete quadratic unramified local norm-quotient Brauer
parameter map. -/
noncomputable def nonarchimedeanLocalFieldAdjoinRootFractionField_quadraticNormQuotientBrauerAddHom
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g)
    (hdegree : f.natDegree = 2) :
    ZMod 2 →+ BrauerGroup (FractionRing 𝒪[K]) where
  toFun := nonarchimedeanLocalFieldAdjoinRootFractionField_quadraticNormQuotientBrauerMap
    K f hf g hgmonic hfg hg hdegree
  map_zero' := by
    change nonarchimedeanLocalFieldAdjoinRootFractionField_quadraticNormQuotientBrauerMap
      K f hf g hgmonic hfg hg hdegree 0 = brauerSplitClass (FractionRing 𝒪[K])
    unfold nonarchimedeanLocalFieldAdjoinRootFractionField_quadraticNormQuotientBrauerMap
    rw [quadraticCyclicNormQuotientBrauerMap_eq_addHom]
    exact AddMonoidHom.map_zero _
  map_add' := by
    intro x y
    exact nonarchimedeanLocalFieldAdjoinRootFractionField_quadraticNormQuotientBrauerMap_add
      K f hf g hgmonic hfg hg hdegree x y

/-- The quadratic unramified local Brauer slice is either trivial or faithfully parameterized by
`ℤ/2ℤ`.  Thus non-splitting of its single nonzero parameter is exactly the remaining issue before
this finite local slice becomes a `ℤ/2ℤ` Brauer subgroup. -/
theorem nonarchimedeanLocalFieldAdjoinRootFractionField_quadraticNormQuotientBrauerAddHom_injective_or_eq_zero
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g)
    (hdegree : f.natDegree = 2) :
    Function.Injective
      (nonarchimedeanLocalFieldAdjoinRootFractionField_quadraticNormQuotientBrauerAddHom
        K f hf g hgmonic hfg hg hdegree) ∨
      nonarchimedeanLocalFieldAdjoinRootFractionField_quadraticNormQuotientBrauerAddHom
        K f hf g hgmonic hfg hg hdegree = 0 := by
  classical
  let F := nonarchimedeanLocalFieldAdjoinRootFractionField_quadraticNormQuotientBrauerAddHom
    K f hf g hgmonic hfg hg hdegree
  by_cases h : F 1 = 0
  · right
    ext z
    rcases zmod_two_eq_zero_or_eq_one z with rfl | rfl
    · exact F.map_zero
    · exact h
  · left
    intro x y hxy
    rcases zmod_two_eq_zero_or_eq_one x with rfl | rfl
    · rcases zmod_two_eq_zero_or_eq_one y with rfl | rfl
      · rfl
      · exfalso
        apply h
        simpa using hxy.symm
    · rcases zmod_two_eq_zero_or_eq_one y with rfl | rfl
      · exfalso
        apply h
        simpa using hxy
      · rfl

/-- The unramified quadratic local Brauer parameter map indexed by the two-torsion subgroup of
`ℚ/ℤ`.  It has the same source format as the real quaternionic local slice. -/
noncomputable def nonarchimedeanLocalFieldAdjoinRootFractionField_quadraticNormQuotientBrauerRatModIntTwoTorsionAddHom
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g)
    (hdegree : f.natDegree = 2) :
    ratModIntNTorsion 2 →+ BrauerGroup (FractionRing 𝒪[K]) :=
  (nonarchimedeanLocalFieldAdjoinRootFractionField_quadraticNormQuotientBrauerAddHom
    K f hf g hgmonic hfg hg hdegree).comp
    (zmodRatModIntAddEquivNTorsion 2 (by norm_num)).symm.toAddMonoidHom

/-- The torsion parameter corresponding to one half maps to the nonzero `ZMod 2` parameter of
the quadratic unramified local Brauer map. -/
theorem nonarchimedeanLocalFieldAdjoinRootFractionField_quadraticNormQuotientBrauerRatModIntTwoTorsionAddHom_apply_generator
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g)
    (hdegree : f.natDegree = 2) :
    nonarchimedeanLocalFieldAdjoinRootFractionField_quadraticNormQuotientBrauerRatModIntTwoTorsionAddHom
      K f hf g hgmonic hfg hg hdegree
      (zmodRatModIntAddEquivNTorsion 2 (by norm_num) (1 : ZMod 2)) =
    nonarchimedeanLocalFieldAdjoinRootFractionField_quadraticNormQuotientBrauerMap
      K f hf g hgmonic hfg hg hdegree 1 := by
  let htwo : 2 ≠ 0 := by norm_num
  change nonarchimedeanLocalFieldAdjoinRootFractionField_quadraticNormQuotientBrauerAddHom
      K f hf g hgmonic hfg hg hdegree
      ((zmodRatModIntAddEquivNTorsion 2 htwo).symm
        (zmodRatModIntAddEquivNTorsion 2 htwo (1 : ZMod 2))) =
    nonarchimedeanLocalFieldAdjoinRootFractionField_quadraticNormQuotientBrauerMap
      K f hf g hgmonic hfg hg hdegree 1
  rw [AddEquiv.symm_apply_apply]
  rfl

/-- The original concrete quadratic unramified local parameter function is evaluation of its
additive refinement. -/
theorem nonarchimedeanLocalFieldAdjoinRootFractionField_quadraticNormQuotientBrauerMap_eq_addHom
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g)
    (hdegree : f.natDegree = 2) (z : ZMod 2) :
    nonarchimedeanLocalFieldAdjoinRootFractionField_quadraticNormQuotientBrauerMap
      K f hf g hgmonic hfg hg hdegree z =
      nonarchimedeanLocalFieldAdjoinRootFractionField_quadraticNormQuotientBrauerAddHom
        K f hf g hgmonic hfg hg hdegree z := rfl

end GaloisForLFunctions.HTGeometry.ABHN
