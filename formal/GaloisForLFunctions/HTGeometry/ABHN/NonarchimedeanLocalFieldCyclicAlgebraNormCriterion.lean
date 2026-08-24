/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisAlgebraNormCriterion
import GaloisForLFunctions.HTGeometry.ABHN.NonarchimedeanLocalFieldNormQuotient

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped ValuativeRel WithZero WithZeroMulInt

theorem nonarchimedeanLocalFieldAdjoinRootFractionField_cyclicClass_split_iff_eq_zero
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g)
    (z : ZMod f.natDegree) :
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
      nonarchimedeanLocalFieldAdjoinRootFractionField_gal_isCyclic
        K f hf g hgmonic hfg hg
    Nonempty
      (cyclicGaloisH2ClassCyclicAlgebra (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f))
          (cyclicGaloisH2BaseNormQuotientEquiv (FractionRing 𝒪[K])
            (FractionRing (AdjoinRoot f))
            ((nonarchimedeanLocalFieldAdjoinRootFractionField_normQuotientValuationEquiv
              K f hf g hgmonic hfg hg).symm z)) ≃ₐ[FractionRing 𝒪[K]]
        Module.End (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f))) ↔ z = 0 := by
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
    nonarchimedeanLocalFieldAdjoinRootFractionField_gal_isCyclic
      K f hf g hgmonic hfg hg
  exact cyclicGaloisNormQuotientClassCyclicAlgebra_split_iff_eq_zero
    (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) f.natDegree
    (nonarchimedeanLocalFieldAdjoinRootFractionField_normQuotientValuationEquiv
      K f hf g hgmonic hfg hg) z

end GaloisForLFunctions.HTGeometry.ABHN

