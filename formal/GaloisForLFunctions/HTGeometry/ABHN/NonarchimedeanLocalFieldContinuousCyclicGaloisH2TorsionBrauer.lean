/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.NonarchimedeanLocalFieldContinuousCyclicGaloisH2TorsionInvariant
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisH2TorsionBrauerPresentation

/-!
# Finite unramified local torsion Brauer representatives

For every finite unramified root lift of a nonarchimedean local field, its finite cohomological
invariant group `ℚ/ℤ[n]` indexes cyclic Brauer representatives.  They give a surjective free
additive presentation of the cyclic Brauer subgroup split by that lift.  This remains finite
cyclic data; it does not identify the whole local Brauer group with `ℚ/ℤ`.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped ValuativeRel WithZero WithZeroMulInt

/-- The finite cohomological invariant values of a concrete unramified root lift index cyclic
Brauer representatives over its base fraction field. -/
noncomputable def nonarchimedeanLocalFieldAdjoinRootFractionField_continuousGaloisH2NTorsionBrauerMap
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) := nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
    letI : IsDiscreteValuationRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
    letI : FaithfulSMul 𝒪[K] (AdjoinRoot f) := by
      refine (faithfulSMul_iff_algebraMap_injective 𝒪[K] (AdjoinRoot f)).mpr ?_
      change Function.Injective <| AdjoinRoot.of f
      exact AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg)
    letI : FaithfulSMul 𝒪[K] (FractionRing (AdjoinRoot f)) := by
      refine (faithfulSMul_iff_algebraMap_injective 𝒪[K]
        (FractionRing (AdjoinRoot f))).mpr ?_
      change Function.Injective <|
        (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
      exact (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
        (AdjoinRoot.of.injective_of_degree_ne_zero
          (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
    letI : Algebra (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) :=
      FractionRing.liftAlgebra 𝒪[K] (FractionRing (AdjoinRoot f))
    letI : FiniteDimensional (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRootFractionField_finiteDimensional K f hf g hfg hg
    ratModIntNTorsion f.natDegree → BrauerGroup (FractionRing 𝒪[K]) := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  letI : IsDiscreteValuationRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
  letI : FaithfulSMul 𝒪[K] (AdjoinRoot f) := by
    refine (faithfulSMul_iff_algebraMap_injective 𝒪[K] (AdjoinRoot f)).mpr ?_
    change Function.Injective <| AdjoinRoot.of f
    exact AdjoinRoot.of.injective_of_degree_ne_zero
      (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg)
  letI : FaithfulSMul 𝒪[K] (FractionRing (AdjoinRoot f)) := by
    refine (faithfulSMul_iff_algebraMap_injective 𝒪[K]
      (FractionRing (AdjoinRoot f))).mpr ?_
    change Function.Injective <|
      (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
    exact (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
      (AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
  letI : Algebra (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) :=
    FractionRing.liftAlgebra 𝒪[K] (FractionRing (AdjoinRoot f))
  letI : FiniteDimensional (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_finiteDimensional K f hf g hfg hg
  letI : IsGalois (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_isGaloisOverFractionRing
      K f hf g hgmonic hfg hg
  letI : IsCyclic Gal(FractionRing (AdjoinRoot f) / FractionRing 𝒪[K]) :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_gal_isCyclic K f hf g hgmonic hfg hg
  exact finiteGaloisContinuousCyclicH2TorsionInvariantBrauerMap
    (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) f.natDegree
    (nonarchimedeanLocalFieldAdjoinRootFractionField_continuousGaloisH2NTorsionInvariant
      K f hf g hgmonic hfg hg)

/-- The same local torsion values, now with a certificate that every representative becomes
split over the defining unramified fraction-field extension. -/
noncomputable def nonarchimedeanLocalFieldAdjoinRootFractionField_continuousGaloisH2NTorsionRelativeBrauerMap
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) := nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
    letI : IsDiscreteValuationRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
    letI : FaithfulSMul 𝒪[K] (AdjoinRoot f) := by
      refine (faithfulSMul_iff_algebraMap_injective 𝒪[K] (AdjoinRoot f)).mpr ?_
      change Function.Injective <| AdjoinRoot.of f
      exact AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg)
    letI : FaithfulSMul 𝒪[K] (FractionRing (AdjoinRoot f)) := by
      refine (faithfulSMul_iff_algebraMap_injective 𝒪[K]
        (FractionRing (AdjoinRoot f))).mpr ?_
      change Function.Injective <|
        (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
      exact (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
        (AdjoinRoot.of.injective_of_degree_ne_zero
          (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
    letI : Algebra (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) :=
      FractionRing.liftAlgebra 𝒪[K] (FractionRing (AdjoinRoot f))
    letI : FiniteDimensional (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRootFractionField_finiteDimensional K f hf g hfg hg
    ratModIntNTorsion f.natDegree →
      scalarExtensionBrauerKernel (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  letI : IsDiscreteValuationRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
  letI : FaithfulSMul 𝒪[K] (AdjoinRoot f) := by
    refine (faithfulSMul_iff_algebraMap_injective 𝒪[K] (AdjoinRoot f)).mpr ?_
    change Function.Injective <| AdjoinRoot.of f
    exact AdjoinRoot.of.injective_of_degree_ne_zero
      (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg)
  letI : FaithfulSMul 𝒪[K] (FractionRing (AdjoinRoot f)) := by
    refine (faithfulSMul_iff_algebraMap_injective 𝒪[K]
      (FractionRing (AdjoinRoot f))).mpr ?_
    change Function.Injective <|
      (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
    exact (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
      (AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
  letI : Algebra (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) :=
    FractionRing.liftAlgebra 𝒪[K] (FractionRing (AdjoinRoot f))
  letI : FiniteDimensional (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_finiteDimensional K f hf g hfg hg
  letI : IsGalois (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_isGaloisOverFractionRing
      K f hf g hgmonic hfg hg
  letI : IsCyclic Gal(FractionRing (AdjoinRoot f) / FractionRing 𝒪[K]) :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_gal_isCyclic K f hf g hgmonic hfg hg
  have hdegree : f.degree ≠ 0 :=
    nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg
  have hnatDegree : f.natDegree ≠ 0 := by
    intro hzero
    apply hdegree
    rw [Polynomial.degree_eq_natDegree hf.ne_zero, hzero]
    rfl
  have hfinrank : Module.finrank (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) =
      f.natDegree - 1 + 1 :=
    (nonarchimedeanLocalFieldAdjoinRootFractionField_finrank K f hf g hfg hg).trans
      (Nat.sub_add_cancel (Nat.pos_of_ne_zero hnatDegree)).symm
  exact finiteGaloisContinuousCyclicH2TorsionInvariantRelativeBrauerMap
    (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) f.natDegree
    (nonarchimedeanLocalFieldAdjoinRootFractionField_continuousGaloisH2NTorsionInvariant
      K f hf g hgmonic hfg hg)
    (f.natDegree - 1) hfinrank

end GaloisForLFunctions.HTGeometry.ABHN
