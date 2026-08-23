/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.NonarchimedeanLocalFieldIntegralNorm

/-!
# Finite unramified local norm quotients

For a finite unramified root lift of a nonarchimedean local field, its field-unit norm quotient
is the cyclic group `ℤ/nℤ`, where `n` is the residue degree.  This is the finite-level local
invariant calculation for cyclic `H²` parameters.  It does not identify the quotient with a
Brauer group or construct the full local invariant `Br(K) ≃ ℚ/ℤ`.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped ValuativeRel WithZero WithZeroMulInt

universe u

/-- The finite unramified cyclic norm quotient is canonically the valuation group modulo the
residue degree.  This is a norm-quotient local invariant isomorphism, before the separate
cyclic-algebra and Brauer-group comparison. -/
noncomputable def nonarchimedeanLocalFieldAdjoinRootFractionField_normQuotientValuationEquiv
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
    Additive (FractionRing 𝒪[K])ˣ ⧸
      cyclicGaloisH2BaseNormImage (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) ≃+
        ZMod f.natDegree := by
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
  let π : 𝒪[K] := (IsDiscreteValuationRing.exists_irreducible 𝒪[K]).choose
  have hπ : Irreducible π :=
    (IsDiscreteValuationRing.exists_irreducible 𝒪[K]).choose_spec
  have hπF : algebraMap 𝒪[K] (FractionRing 𝒪[K]) π ≠ 0 := by
    intro h
    apply hπ.ne_zero
    apply (IsFractionRing.injective 𝒪[K] (FractionRing 𝒪[K]))
    simpa using h
  let u : (FractionRing 𝒪[K])ˣ := Units.mk0
    (algebraMap 𝒪[K] (FractionRing 𝒪[K]) π) hπF
  apply cyclicGaloisH2BaseNormQuotientSplitValuationEquiv
    (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f))
    ((IsDiscreteValuationRing.maximalIdeal 𝒪[K]).valuation (FractionRing 𝒪[K]))
    ((IsDiscreteValuationRing.maximalIdeal (AdjoinRoot f)).valuation
      (FractionRing (AdjoinRoot f))) f.natDegree u
  · change Multiplicative.toAdd
      (tameValHom ((IsDiscreteValuationRing.maximalIdeal 𝒪[K]).valuation
        (FractionRing 𝒪[K]))
        (Units.mk0 (algebraMap 𝒪[K] (FractionRing 𝒪[K]) π) hπF)) = 1
    exact discreteValuationRingFractionField_irreducible_tameVal
      𝒪[K] (FractionRing 𝒪[K]) hπ
  · exact nonarchimedeanLocalFieldAdjoinRootFractionField_finrank K f hf g hfg hg
  · exact nonarchimedeanLocalFieldAdjoinRootFractionField_tameValHom_norm
      K f hf g hgmonic hfg hg
  · intro a ha
    have ha' : a ∈ (tameValHom ((IsDiscreteValuationRing.maximalIdeal 𝒪[K]).valuation
        (FractionRing 𝒪[K]))).ker := by
      simpa only [MonoidHom.mem_ker] using ha
    obtain ⟨b, hb⟩ :=
      nonarchimedeanLocalFieldAdjoinRoot_fractionField_norm_surjective_on_tameValKer
        K f hf g hgmonic hfg hg a ha'
    refine ⟨Units.map (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))) b, ?_⟩
    apply Units.ext
    change Algebra.norm (FractionRing 𝒪[K])
      (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f)) (b : AdjoinRoot f)) =
        (a : FractionRing 𝒪[K])
    exact hb

end GaloisForLFunctions.HTGeometry.ABHN
