/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisH2AlgEquiv
import GaloisForLFunctions.HTGeometry.ABHN.NonarchimedeanLocalFieldCyclicGaloisH2Invariant
import GaloisForLFunctions.HTGeometry.ABHN.CentralDivisionUnramifiedMaximalSubfieldGalois

/-!
# Native-base unramified cyclic `H²` invariant

The concrete unramified invariant was first established over the fraction field of the valuation
ring. The canonical fraction-field equivalence and norm-quotient transport identify that base with
the original local field, producing the finite invariant directly over the local field itself.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped ValuativeRel WithZero WithZeroMulInt

/-- The cyclic degree-two cohomology of a finite unramified root lift over the original
nonarchimedean local field is canonically `ZMod` the lifted degree. -/
noncomputable def
    nonarchimedeanLocalFieldAdjoinRootFractionField_cyclicGaloisH2InvariantOverBase
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) := nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
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
    letI : Algebra K (FractionRing (AdjoinRoot f)) := by
      let g₀ : 𝒪[K] →+* FractionRing (AdjoinRoot f) :=
        (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
      have hg₀ : Function.Injective g₀ :=
        (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
          (AdjoinRoot.of.injective_of_degree_ne_zero
            (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
      exact RingHom.toAlgebra (IsFractionRing.lift hg₀)
    letI : FiniteDimensional K (FractionRing (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRootFractionField_finiteDimensionalOverBase
        K f hf g hfg hg
    cyclicGaloisH2 K (FractionRing (AdjoinRoot f)) ≃+ ZMod f.natDegree := by
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
  let g₀ : 𝒪[K] →+* FractionRing (AdjoinRoot f) :=
    (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
  have hg₀ : Function.Injective g₀ :=
    (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
      (AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
  letI : Algebra K (FractionRing (AdjoinRoot f)) := RingHom.toAlgebra (IsFractionRing.lift hg₀)
  letI : FiniteDimensional (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_finiteDimensional K f hf g hfg hg
  letI : FiniteDimensional K (FractionRing (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_finiteDimensionalOverBase
      K f hf g hfg hg
  letI : IsGalois (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_isGaloisOverFractionRing
      K f hf g hgmonic hfg hg
  letI : IsCyclic Gal(FractionRing (AdjoinRoot f) / FractionRing 𝒪[K]) :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_gal_isCyclic
      K f hf g hgmonic hfg hg
  letI : IsGalois K (FractionRing (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_isGalois
      K f hf g hgmonic hfg hg
  letI : IsCyclic Gal(FractionRing (AdjoinRoot f) / K) :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_gal_isCyclic_over_base
      K f hf g hgmonic hfg hg
  let eK := FractionRing.algEquiv 𝒪[K] K
  have hcompat :
      (algebraMap K (FractionRing (AdjoinRoot f))).comp eK.toRingEquiv.toRingHom =
        (RingEquiv.refl (FractionRing (AdjoinRoot f))).toRingHom.comp
          (algebraMap (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f))) := by
    apply IsFractionRing.ringHom_ext (A := 𝒪[K])
    intro r
    simp only [RingHom.comp_apply]
    change (algebraMap K (FractionRing (AdjoinRoot f)))
      (eK (algebraMap 𝒪[K] (FractionRing 𝒪[K]) r)) = _
    rw [eK.commutes]
    change IsFractionRing.lift hg₀ (algebraMap 𝒪[K] K r) =
      IsFractionRing.lift hg₀ (algebraMap 𝒪[K] (FractionRing 𝒪[K]) r)
    rw [IsFractionRing.lift_algebraMap]
    rw [IsFractionRing.lift_algebraMap]
  exact (cyclicGaloisH2AddEquivOfEquivEquiv
      (FractionRing 𝒪[K]) K (FractionRing (AdjoinRoot f))
        (FractionRing (AdjoinRoot f)) eK.toRingEquiv
        (RingEquiv.refl (FractionRing (AdjoinRoot f))) hcompat).symm.trans
    (nonarchimedeanLocalFieldAdjoinRootFractionField_cyclicGaloisH2Invariant
      K f hf g hgmonic hfg hg)

end GaloisForLFunctions.HTGeometry.ABHN
