/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.PrimeCyclicGeneratorHasse
import GaloisForLFunctions.HTGeometry.ABHN.NonarchimedeanLocalFieldNormQuotientBrauerAdditive

/-!
# Generator Hasse tests for the quadratic local Brauer slice

The unramified quadratic norm-quotient Brauer map is controlled by its single nonzero parameter.
Its generator is split exactly when the whole map is zero, and nonsplit exactly when the whole
map is injective.  The same dichotomy is transported to the two-torsion subgroup of `ℚ/ℤ`, the
coordinate system used by local ABHN invariants.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped ValuativeRel WithZero WithZeroMulInt

/-- The quadratic unramified local Brauer map vanishes exactly when its generator is split. -/
theorem nonarchimedeanLocalFieldAdjoinRootFractionField_quadraticNormQuotientBrauerAddHom_eq_zero_iff_generator_eq_split
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g)
    (hdegree : f.natDegree = 2) :
    nonarchimedeanLocalFieldAdjoinRootFractionField_quadraticNormQuotientBrauerAddHom
      K f hf g hgmonic hfg hg hdegree = 0 ↔
    nonarchimedeanLocalFieldAdjoinRootFractionField_quadraticNormQuotientBrauerMap
      K f hf g hgmonic hfg hg hdegree 1 = brauerSplitClass (FractionRing 𝒪[K]) := by
  change nonarchimedeanLocalFieldAdjoinRootFractionField_quadraticNormQuotientBrauerAddHom
      K f hf g hgmonic hfg hg hdegree = 0 ↔
    nonarchimedeanLocalFieldAdjoinRootFractionField_quadraticNormQuotientBrauerAddHom
      K f hf g hgmonic hfg hg hdegree 1 = 0
  exact zmodPrime_addMonoidHom_eq_zero_iff_apply_one_eq_zero
    ⟨2, Nat.prime_two⟩
    (nonarchimedeanLocalFieldAdjoinRootFractionField_quadraticNormQuotientBrauerAddHom
      K f hf g hgmonic hfg hg hdegree)

/-- The quadratic unramified local Brauer map is injective exactly when its generator is
nonsplit. -/
theorem nonarchimedeanLocalFieldAdjoinRootFractionField_quadraticNormQuotientBrauerAddHom_injective_iff_generator_ne_split
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g)
    (hdegree : f.natDegree = 2) :
    Function.Injective
      (nonarchimedeanLocalFieldAdjoinRootFractionField_quadraticNormQuotientBrauerAddHom
        K f hf g hgmonic hfg hg hdegree) ↔
    nonarchimedeanLocalFieldAdjoinRootFractionField_quadraticNormQuotientBrauerMap
      K f hf g hgmonic hfg hg hdegree 1 ≠ brauerSplitClass (FractionRing 𝒪[K]) := by
  change Function.Injective
      (nonarchimedeanLocalFieldAdjoinRootFractionField_quadraticNormQuotientBrauerAddHom
        K f hf g hgmonic hfg hg hdegree) ↔
    nonarchimedeanLocalFieldAdjoinRootFractionField_quadraticNormQuotientBrauerAddHom
      K f hf g hgmonic hfg hg hdegree 1 ≠ 0
  exact zmodPrime_addMonoidHom_injective_iff_apply_one_ne_zero
    ⟨2, Nat.prime_two⟩
    (nonarchimedeanLocalFieldAdjoinRootFractionField_quadraticNormQuotientBrauerAddHom
      K f hf g hgmonic hfg hg hdegree)

/-- Closed quadratic local Hasse dichotomy: the selected slice is either wholly split or a
faithful copy of `ℤ/2ℤ`, with no intermediate behavior. -/
theorem nonarchimedeanLocalFieldAdjoinRootFractionField_quadraticNormQuotientBrauerAddHom_trivial_or_faithful_hasse
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g)
    (hdegree : f.natDegree = 2) :
    (nonarchimedeanLocalFieldAdjoinRootFractionField_quadraticNormQuotientBrauerAddHom
        K f hf g hgmonic hfg hg hdegree = 0 ∧
      nonarchimedeanLocalFieldAdjoinRootFractionField_quadraticNormQuotientBrauerMap
        K f hf g hgmonic hfg hg hdegree 1 = brauerSplitClass (FractionRing 𝒪[K])) ∨
    (Function.Injective
        (nonarchimedeanLocalFieldAdjoinRootFractionField_quadraticNormQuotientBrauerAddHom
          K f hf g hgmonic hfg hg hdegree) ∧
      nonarchimedeanLocalFieldAdjoinRootFractionField_quadraticNormQuotientBrauerMap
        K f hf g hgmonic hfg hg hdegree 1 ≠ brauerSplitClass (FractionRing 𝒪[K])) := by
  change
    (nonarchimedeanLocalFieldAdjoinRootFractionField_quadraticNormQuotientBrauerAddHom
        K f hf g hgmonic hfg hg hdegree = 0 ∧
      nonarchimedeanLocalFieldAdjoinRootFractionField_quadraticNormQuotientBrauerAddHom
        K f hf g hgmonic hfg hg hdegree 1 = 0) ∨
    (Function.Injective
        (nonarchimedeanLocalFieldAdjoinRootFractionField_quadraticNormQuotientBrauerAddHom
          K f hf g hgmonic hfg hg hdegree) ∧
      nonarchimedeanLocalFieldAdjoinRootFractionField_quadraticNormQuotientBrauerAddHom
        K f hf g hgmonic hfg hg hdegree 1 ≠ 0)
  exact zmodPrime_addMonoidHom_trivial_or_faithful_hasse
    ⟨2, Nat.prime_two⟩
    (nonarchimedeanLocalFieldAdjoinRootFractionField_quadraticNormQuotientBrauerAddHom
      K f hf g hgmonic hfg hg hdegree)

/-- In `ℚ/ℤ[2]` coordinates, the quadratic local Brauer map vanishes exactly when its half-class
generator is split. -/
theorem nonarchimedeanLocalFieldAdjoinRootFractionField_quadraticNormQuotientBrauerRatModIntTwoTorsionAddHom_eq_zero_iff_generator_eq_split
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g)
    (hdegree : f.natDegree = 2) :
    nonarchimedeanLocalFieldAdjoinRootFractionField_quadraticNormQuotientBrauerRatModIntTwoTorsionAddHom
      K f hf g hgmonic hfg hg hdegree = 0 ↔
    nonarchimedeanLocalFieldAdjoinRootFractionField_quadraticNormQuotientBrauerMap
      K f hf g hgmonic hfg hg hdegree 1 = brauerSplitClass (FractionRing 𝒪[K]) := by
  rw [←
    nonarchimedeanLocalFieldAdjoinRootFractionField_quadraticNormQuotientBrauerRatModIntTwoTorsionAddHom_apply_generator]
  change nonarchimedeanLocalFieldAdjoinRootFractionField_quadraticNormQuotientBrauerRatModIntTwoTorsionAddHom
      K f hf g hgmonic hfg hg hdegree = 0 ↔
    nonarchimedeanLocalFieldAdjoinRootFractionField_quadraticNormQuotientBrauerRatModIntTwoTorsionAddHom
      K f hf g hgmonic hfg hg hdegree
      (zmodRatModIntAddEquivNTorsion 2 (by norm_num) (1 : ZMod 2)) = 0
  exact primeCyclic_addMonoidHom_eq_zero_iff_apply_generator
    ⟨2, Nat.prime_two⟩ (zmodRatModIntAddEquivNTorsion 2 (by norm_num))
    (nonarchimedeanLocalFieldAdjoinRootFractionField_quadraticNormQuotientBrauerRatModIntTwoTorsionAddHom
      K f hf g hgmonic hfg hg hdegree)

/-- In `ℚ/ℤ[2]` coordinates, the quadratic local Brauer map is injective exactly when its
half-class generator is nonsplit. -/
theorem nonarchimedeanLocalFieldAdjoinRootFractionField_quadraticNormQuotientBrauerRatModIntTwoTorsionAddHom_injective_iff_generator_ne_split
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g)
    (hdegree : f.natDegree = 2) :
    Function.Injective
      (nonarchimedeanLocalFieldAdjoinRootFractionField_quadraticNormQuotientBrauerRatModIntTwoTorsionAddHom
        K f hf g hgmonic hfg hg hdegree) ↔
    nonarchimedeanLocalFieldAdjoinRootFractionField_quadraticNormQuotientBrauerMap
      K f hf g hgmonic hfg hg hdegree 1 ≠ brauerSplitClass (FractionRing 𝒪[K]) := by
  rw [←
    nonarchimedeanLocalFieldAdjoinRootFractionField_quadraticNormQuotientBrauerRatModIntTwoTorsionAddHom_apply_generator]
  change Function.Injective
      (nonarchimedeanLocalFieldAdjoinRootFractionField_quadraticNormQuotientBrauerRatModIntTwoTorsionAddHom
        K f hf g hgmonic hfg hg hdegree) ↔
    nonarchimedeanLocalFieldAdjoinRootFractionField_quadraticNormQuotientBrauerRatModIntTwoTorsionAddHom
      K f hf g hgmonic hfg hg hdegree
      (zmodRatModIntAddEquivNTorsion 2 (by norm_num) (1 : ZMod 2)) ≠ 0
  exact primeCyclic_addMonoidHom_injective_iff_apply_generator_ne_zero
    ⟨2, Nat.prime_two⟩ (zmodRatModIntAddEquivNTorsion 2 (by norm_num))
    (nonarchimedeanLocalFieldAdjoinRootFractionField_quadraticNormQuotientBrauerRatModIntTwoTorsionAddHom
      K f hf g hgmonic hfg hg hdegree)

/-- Closed ABHN-coordinate dichotomy: the quadratic `ℚ/ℤ[2]` slice is either wholly split or a
faithful two-torsion local-invariant slice. -/
theorem nonarchimedeanLocalFieldAdjoinRootFractionField_quadraticNormQuotientBrauerRatModIntTwoTorsionAddHom_trivial_or_faithful_hasse
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g)
    (hdegree : f.natDegree = 2) :
    (nonarchimedeanLocalFieldAdjoinRootFractionField_quadraticNormQuotientBrauerRatModIntTwoTorsionAddHom
        K f hf g hgmonic hfg hg hdegree = 0 ∧
      nonarchimedeanLocalFieldAdjoinRootFractionField_quadraticNormQuotientBrauerMap
        K f hf g hgmonic hfg hg hdegree 1 = brauerSplitClass (FractionRing 𝒪[K])) ∨
    (Function.Injective
        (nonarchimedeanLocalFieldAdjoinRootFractionField_quadraticNormQuotientBrauerRatModIntTwoTorsionAddHom
          K f hf g hgmonic hfg hg hdegree) ∧
      nonarchimedeanLocalFieldAdjoinRootFractionField_quadraticNormQuotientBrauerMap
        K f hf g hgmonic hfg hg hdegree 1 ≠ brauerSplitClass (FractionRing 𝒪[K])) := by
  rw [←
    nonarchimedeanLocalFieldAdjoinRootFractionField_quadraticNormQuotientBrauerRatModIntTwoTorsionAddHom_apply_generator]
  change
    (nonarchimedeanLocalFieldAdjoinRootFractionField_quadraticNormQuotientBrauerRatModIntTwoTorsionAddHom
        K f hf g hgmonic hfg hg hdegree = 0 ∧
      nonarchimedeanLocalFieldAdjoinRootFractionField_quadraticNormQuotientBrauerRatModIntTwoTorsionAddHom
        K f hf g hgmonic hfg hg hdegree
        (zmodRatModIntAddEquivNTorsion 2 (by norm_num) (1 : ZMod 2)) = 0) ∨
    (Function.Injective
        (nonarchimedeanLocalFieldAdjoinRootFractionField_quadraticNormQuotientBrauerRatModIntTwoTorsionAddHom
          K f hf g hgmonic hfg hg hdegree) ∧
      nonarchimedeanLocalFieldAdjoinRootFractionField_quadraticNormQuotientBrauerRatModIntTwoTorsionAddHom
        K f hf g hgmonic hfg hg hdegree
        (zmodRatModIntAddEquivNTorsion 2 (by norm_num) (1 : ZMod 2)) ≠ 0)
  exact primeCyclic_addMonoidHom_trivial_or_faithful_hasse
    ⟨2, Nat.prime_two⟩ (zmodRatModIntAddEquivNTorsion 2 (by norm_num))
    (nonarchimedeanLocalFieldAdjoinRootFractionField_quadraticNormQuotientBrauerRatModIntTwoTorsionAddHom
      K f hf g hgmonic hfg hg hdegree)

end GaloisForLFunctions.HTGeometry.ABHN
