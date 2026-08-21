import GaloisForLFunctions.HTGeometry.ABHN.NonarchimedeanLocalFieldValuationSequence
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.RingTheory.Smooth.Fiber

namespace GaloisForLFunctions.HTGeometry.ABHN

open Polynomial
open scoped ValuativeRel

attribute [local instance] Ideal.Quotient.field

universe u

#check Ideal.Quotient.maximal_of_isField
#check IsLocalRing.of_unique_max_ideal
#check Ideal.IsMaximal.eq_of_le
#check Ideal.isMaximal_comap_of_isIntegral_of_isMaximal
#check Algebra.IsIntegral.of_finite
#check Ideal.map_le_iff_le_comap
#print IsLocalRing.ResidueField

noncomputable def testReductionEquivOfMapEq
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (g : Polynomial 𝓀[K])
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) :
    (AdjoinRoot f ⧸ Ideal.map (AdjoinRoot.of f) 𝓂[K]) ≃ₐ[𝒪[K]] AdjoinRoot g := by
  let e₁ : (AdjoinRoot f ⧸ Ideal.map (AdjoinRoot.of f) 𝓂[K]) ≃ₐ[𝒪[K]]
      AdjoinRoot (f.map (Ideal.Quotient.mk 𝓂[K])) :=
    AdjoinRoot.quotEquivQuotMap f 𝓂[K]
  let e₂ : AdjoinRoot (f.map (Ideal.Quotient.mk 𝓂[K])) ≃ₐ[𝒪[K]] AdjoinRoot g :=
    AdjoinRoot.algEquivOfEq 𝒪[K] _ g hfg
  exact e₁.trans e₂

theorem test_adjoinRoot_map_maximalIdeal_isMaximal
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (g : Polynomial 𝓀[K])
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g) :
    (Ideal.map (AdjoinRoot.of f) 𝓂[K]).IsMaximal := by
  apply Ideal.Quotient.maximal_of_isField
  letI : Fact (Irreducible g) := ⟨hg⟩
  exact (testReductionEquivOfMapEq K f g hfg).toMulEquiv.isField
    (Field.toIsField _)

theorem test_adjoinRoot_isLocalRing
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g)
    (hg : Irreducible g) : IsLocalRing (AdjoinRoot f) := by
  letI : Module.Finite 𝒪[K] (AdjoinRoot f) := hf.finite_adjoinRoot
  letI : Algebra.IsIntegral 𝒪[K] (AdjoinRoot f) := Algebra.IsIntegral.of_finite 𝒪[K] (AdjoinRoot f)
  let m : Ideal (AdjoinRoot f) := Ideal.map (AdjoinRoot.of f) 𝓂[K]
  have hm : m.IsMaximal := test_adjoinRoot_map_maximalIdeal_isMaximal K f g hfg hg
  refine IsLocalRing.of_unique_max_ideal ⟨m, hm, ?_⟩
  intro P hP
  letI : P.IsMaximal := hP
  have hunder : (P.comap (algebraMap 𝒪[K] (AdjoinRoot f))).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P
  have hunder_eq : P.comap (algebraMap 𝒪[K] (AdjoinRoot f)) = 𝓂[K] :=
    IsLocalRing.eq_maximalIdeal hunder
  apply (hm.eq_of_le hP.ne_top ?_).symm
  change Ideal.map (algebraMap 𝒪[K] (AdjoinRoot f)) 𝓂[K] ≤ P
  rw [Ideal.map_le_iff_le_comap, ← hunder_eq]

noncomputable def test_adjoinRoot_residueFieldEquiv
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g)
    (hg : Irreducible g) :
    letI : IsLocalRing (AdjoinRoot f) := test_adjoinRoot_isLocalRing K f hf g hfg hg
    IsLocalRing.ResidueField (AdjoinRoot f) ≃ₐ[𝒪[K]] AdjoinRoot g := by
  letI : IsLocalRing (AdjoinRoot f) := test_adjoinRoot_isLocalRing K f hf g hfg hg
  let hm : (Ideal.map (AdjoinRoot.of f) 𝓂[K]).IsMaximal :=
    test_adjoinRoot_map_maximalIdeal_isMaximal K f g hfg hg
  change (AdjoinRoot f ⧸ IsLocalRing.maximalIdeal (AdjoinRoot f)) ≃ₐ[𝒪[K]] AdjoinRoot g
  rw [← IsLocalRing.eq_maximalIdeal hm]
  exact testReductionEquivOfMapEq K f g hfg

theorem test_adjoinRoot_etale
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g) :
    Algebra.Etale 𝒪[K] (AdjoinRoot f) := by
  letI : Module.Free 𝒪[K] (AdjoinRoot f) := hf.free_adjoinRoot
  letI : Module.Finite 𝒪[K] (AdjoinRoot f) := hf.finite_adjoinRoot
  letI : IsLocalRing (AdjoinRoot f) := test_adjoinRoot_isLocalRing K f hf g hfg hg
  have hmap : (IsLocalRing.maximalIdeal 𝒪[K]).map (algebraMap 𝒪[K] (AdjoinRoot f)) =
      IsLocalRing.maximalIdeal (AdjoinRoot f) := by
    change (Ideal.map (AdjoinRoot.of f) 𝓂[K]) = IsLocalRing.maximalIdeal (AdjoinRoot f)
    exact IsLocalRing.eq_maximalIdeal (test_adjoinRoot_map_maximalIdeal_isMaximal K f g hfg hg)
  letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
    ((IsLocalRing.local_hom_TFAE (algebraMap 𝒪[K] (AdjoinRoot f))).out 2 0).mp (le_of_eq hmap)
  letI : Fact (Irreducible g) := ⟨hg⟩
  letI : Module.Finite 𝓀[K] (AdjoinRoot g) := hgmonic.finite_adjoinRoot
  letI : Finite (AdjoinRoot g) := Module.finite_of_finite 𝓀[K]
  let e := test_adjoinRoot_residueFieldEquiv K f hf g hfg hg
  letI : Finite (IsLocalRing.ResidueField (AdjoinRoot f)) :=
    Finite.of_surjective e.symm e.symm.surjective
  letI : Module.Finite 𝓀[K] (IsLocalRing.ResidueField (AdjoinRoot f)) :=
    Module.Finite.of_finite
  letI : Algebra.IsAlgebraic 𝓀[K] (IsLocalRing.ResidueField (AdjoinRoot f)) :=
    Algebra.IsAlgebraic.of_finite 𝓀[K] _
  letI : Algebra.IsSeparable 𝓀[K] (IsLocalRing.ResidueField (AdjoinRoot f)) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  letI : Algebra.FormallyUnramified 𝒪[K] (AdjoinRoot f) :=
    Algebra.FormallyUnramified.of_map_maximalIdeal hmap
  exact Algebra.Etale.of_formallyUnramified_of_flat

end GaloisForLFunctions.HTGeometry.ABHN
