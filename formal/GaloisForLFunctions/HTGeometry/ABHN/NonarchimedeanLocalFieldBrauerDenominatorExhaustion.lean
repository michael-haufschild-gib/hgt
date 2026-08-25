/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.NonarchimedeanLocalFieldCyclicBrauerInvariant
import GaloisForLFunctions.HTGeometry.ABHN.BrauerFieldEquiv

/-!
# Finite-denominator exhaustion inside a nonarchimedean local Brauer group

Every positive degree occurs as a concrete finite unramified extension of a nonarchimedean local
field.  Its cyclic Brauer subgroup is additively equivalent to `ZMod n`.  Transporting from the
fraction field of the valuation ring back to the original local field therefore embeds `ZMod n`
in the actual Brauer group for every positive `n`.

Consequently every positive finite additive order occurs in the local Brauer group, and the local
Brauer group is infinite.  This proves the finite-denominator lower bound in the local invariant
theorem.  The converse assertion that every Brauer class belongs to one of these unramified cyclic
subgroups remains the division-algebra exhaustion step.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped ValuativeRel WithZero WithZeroMulInt

noncomputable section

/-- For every positive `n`, the Brauer group of a nonarchimedean local field contains an embedded
copy of `ZMod n`, constructed from a degree-`n` finite unramified cyclic extension. -/
theorem nonarchimedeanLocalField_exists_zmod_brauerEmbedding
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℕ) [NeZero n] :
    ∃ φ : ZMod n →+ BrauerGroup.{0, 0} K, Function.Injective φ := by
  obtain ⟨f, g, hf, hgmonic, hg, hfg, hdegree, _⟩ :=
    nonarchimedeanLocalField_exists_finiteUnramifiedDVRLift_of_natDegree K n
  subst n
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
  let eCyclic :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_cyclicBrauerInvariant
      K f hf g hgmonic hfg hg
  let cyclicSubtype :
      cyclicGaloisBrauerSubgroup (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) →+
        BrauerGroup.{0, 0} (FractionRing 𝒪[K]) :=
    (cyclicGaloisBrauerSubgroup
      (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f))).subtype
  let toFractionBrauer :
      ZMod f.natDegree →+ BrauerGroup.{0, 0} (FractionRing 𝒪[K]) :=
    cyclicSubtype.comp eCyclic.toAddMonoidHom
  let baseEquiv : FractionRing 𝒪[K] ≃+* K :=
    (FractionRing.algEquiv (A := 𝒪[K]) K).toRingEquiv
  let φ : ZMod f.natDegree →+ BrauerGroup.{0, 0} K :=
    (brauerGroupAddEquivOfRingEquiv baseEquiv).toAddMonoidHom.comp toFractionBrauer
  refine ⟨φ, ?_⟩
  intro x y hxy
  apply eCyclic.injective
  apply Subtype.ext
  apply (brauerGroupAddEquivOfRingEquiv baseEquiv).injective
  exact hxy

/-- Every positive finite additive order occurs in the Brauer group of a nonarchimedean local
field.  The witness is the image of `1 : ZMod n` under an unramified cyclic Brauer embedding. -/
theorem nonarchimedeanLocalField_brauerGroup_exists_addOrderOf
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℕ) [NeZero n] :
    ∃ β : BrauerGroup.{0, 0} K, addOrderOf β = n := by
  obtain ⟨φ, hφ⟩ := nonarchimedeanLocalField_exists_zmod_brauerEmbedding K n
  refine ⟨φ 1, ?_⟩
  rw [addOrderOf_injective φ hφ, ZMod.addOrderOf_one]

/-- The Brauer group of every nonarchimedean local field is infinite. -/
theorem nonarchimedeanLocalField_brauerGroup_infinite
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : Infinite (BrauerGroup.{0, 0} K) := by
  refine not_finite_iff_infinite.mp fun hfinite ↦ ?_
  haveI := hfinite
  let n := Nat.card (BrauerGroup.{0, 0} K) + 1
  letI : NeZero n := ⟨Nat.succ_ne_zero _⟩
  obtain ⟨β, hβ⟩ := nonarchimedeanLocalField_brauerGroup_exists_addOrderOf K n
  have hle : addOrderOf β ≤ Nat.card (BrauerGroup.{0, 0} K) := addOrderOf_le_card
  omega

end

end GaloisForLFunctions.HTGeometry.ABHN
