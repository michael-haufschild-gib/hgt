import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisH2BrauerFaithful
import GaloisForLFunctions.HTGeometry.ABHN.NonarchimedeanLocalFieldCyclicGaloisH2Invariant

/-!
# Finite unramified local cyclic Brauer invariants

For each unramified root-lift extension, valuation coordinates and faithfulness of the cyclic
crossed-product map identify `ZMod n` with the actual cyclic relative Brauer subgroup.  This is a
closed finite-level local invariant isomorphism; passage to all local Brauer classes remains a
separate exhaustion theorem.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped ValuativeRel WithZero WithZeroMulInt

/-- The cyclic relative Brauer subgroup of an unramified root-lift extension is canonically
`ZMod` its residue degree. -/
noncomputable def nonarchimedeanLocalFieldAdjoinRootFractionField_cyclicBrauerInvariant
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
    ZMod f.natDegree ≃+
      cyclicGaloisBrauerSubgroup (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) := by
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
  exact cyclicGaloisInvariantBrauerSubgroupAddEquiv
    (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) f.natDegree
    (nonarchimedeanLocalFieldAdjoinRootFractionField_cyclicGaloisH2Invariant
      K f hf g hgmonic hfg hg)

end GaloisForLFunctions.HTGeometry.ABHN
