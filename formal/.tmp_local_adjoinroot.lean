import GaloisForLFunctions.HTGeometry.ABHN.NonarchimedeanLocalFieldValuationSequence
import Mathlib.RingTheory.Ideal.GoingUp

namespace GaloisForLFunctions.HTGeometry.ABHN

open Polynomial
open scoped ValuativeRel

attribute [local instance] Ideal.Quotient.field

universe u

#check Ideal.Quotient.maximal_of_isField
#check IsLocalRing.of_unique_max_ideal
#check Ideal.IsMaximal.eq_of_le
#check isMaximal_comap_of_isIntegral_of_isMaximal
#check Algebra.IsIntegral.of_finite
#check Ideal.map_le_iff_le_comap

theorem test_adjoinRoot_map_maximalIdeal_isMaximal
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (g : Polynomial 𝓀[K])
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : g.Irreducible) :
    (Ideal.map (AdjoinRoot.of f) 𝓂[K]).IsMaximal := by
  apply Ideal.Quotient.maximal_of_isField
  letI : Fact (Irreducible g) := ⟨hg⟩
  exact (nonarchimedeanLocalFieldAdjoinRootReductionEquivOfMapEq K f g hfg).toMulEquiv.isField
    (Field.toIsField _)

theorem test_adjoinRoot_isLocalRing
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g)
    (hg : g.Irreducible) : IsLocalRing (AdjoinRoot f) := by
  letI : Module.Finite 𝒪[K] (AdjoinRoot f) := hf.finite_adjoinRoot
  letI : Algebra.IsIntegral 𝒪[K] (AdjoinRoot f) := Algebra.IsIntegral.of_finite 𝒪[K] (AdjoinRoot f)
  let m : Ideal (AdjoinRoot f) := Ideal.map (AdjoinRoot.of f) 𝓂[K]
  have hm : m.IsMaximal := test_adjoinRoot_map_maximalIdeal_isMaximal K f g hfg hg
  refine IsLocalRing.of_unique_max_ideal ⟨m, hm, ?_⟩
  intro P hP
  letI : P.IsMaximal := hP
  have hunder : (P.comap (algebraMap 𝒪[K] (AdjoinRoot f))).IsMaximal :=
    isMaximal_comap_of_isIntegral_of_isMaximal P
  have hunder_eq : P.comap (algebraMap 𝒪[K] (AdjoinRoot f)) = 𝓂[K] :=
    IsLocalRing.eq_maximalIdeal hunder
  apply (hm.eq_of_le hP.ne_top ?_).symm
  rw [Ideal.map_le_iff_le_comap, ← hunder_eq]

end GaloisForLFunctions.HTGeometry.ABHN
