/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.NonarchimedeanLocalFieldCubicNormQuotientBrauer
import GaloisForLFunctions.HTGeometry.ABHN.ContinuousCubicGaloisH2Brauer

/-!
# Continuous cubic local cyclic Galois `H²` Brauer classes

For an explicit degree-three unramified root lift, every continuous cyclic degree-two cohomology
class has a Brauer representative that becomes split over the lift's fraction field.  This gives a
finite-level local relative-kernel theorem; it does not yet identify the local Brauer group with
`ℚ/ℤ`.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped ValuativeRel WithZero WithZeroMulInt

/-- The defining fraction field splits every continuous cubic cyclic degree-two class of an
explicit unramified root lift. -/
theorem scalarExtensionBrauerMap_nonarchimedeanLocalFieldAdjoinRootFractionField_continuousCubicCyclicGaloisH2BrauerMap_eq_split
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g)
    (hdegree : f.natDegree = 3) :
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
    let g₀ : 𝒪[K] →+* FractionRing (AdjoinRoot f) :=
      (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
    let hg₀ : Function.Injective g₀ :=
      (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
        (AdjoinRoot.of.injective_of_degree_ne_zero
          (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
    letI : Algebra K (FractionRing (AdjoinRoot f)) := RingHom.toAlgebra (IsFractionRing.lift hg₀)
    letI : IsGalois (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRootFractionField_isGaloisOverFractionRing
        K f hf g hgmonic hfg hg
    letI : IsCyclic Gal(FractionRing (AdjoinRoot f) / FractionRing 𝒪[K]) :=
      nonarchimedeanLocalFieldAdjoinRootFractionField_gal_isCyclic K f hf g hgmonic hfg hg
    ∀ z : continuousGaloisUnitCohomology 2 (FractionRing 𝒪[K])
        (FractionRing (AdjoinRoot f)),
      scalarExtensionBrauerMap (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f))
        (finiteGaloisContinuousCubicCyclicGaloisH2BrauerMap
          (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f))
          ((nonarchimedeanLocalFieldAdjoinRootFractionField_finrank K f hf g hfg hg).trans hdegree) z) =
        brauerSplitClass (FractionRing (AdjoinRoot f)) := by
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
  let g₀ : 𝒪[K] →+* FractionRing (AdjoinRoot f) :=
    (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
  have hg₀ : Function.Injective g₀ :=
    (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
      (AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
  letI : Algebra K (FractionRing (AdjoinRoot f)) := RingHom.toAlgebra (IsFractionRing.lift hg₀)
  letI : IsGalois (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_isGaloisOverFractionRing
      K f hf g hgmonic hfg hg
  letI : IsCyclic Gal(FractionRing (AdjoinRoot f) / FractionRing 𝒪[K]) :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_gal_isCyclic K f hf g hgmonic hfg hg
  let hfinrank : Module.finrank (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) = 3 :=
    (nonarchimedeanLocalFieldAdjoinRootFractionField_finrank K f hf g hfg hg).trans hdegree
  change ∀ z : continuousGaloisUnitCohomology 2 (FractionRing 𝒪[K])
      (FractionRing (AdjoinRoot f)),
    scalarExtensionBrauerMap (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f))
      (finiteGaloisContinuousCubicCyclicGaloisH2BrauerMap
        (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) hfinrank z) =
      brauerSplitClass (FractionRing (AdjoinRoot f))
  intro z
  exact scalarExtensionBrauerMap_finiteGaloisContinuousCubicCyclicGaloisH2BrauerMap_eq_split
    (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) hfinrank z

end GaloisForLFunctions.HTGeometry.ABHN
