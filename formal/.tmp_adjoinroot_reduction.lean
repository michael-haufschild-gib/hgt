import GaloisForLFunctions.HTGeometry.ABHN.NonarchimedeanLocalFieldValuationSequence
import Mathlib.RingTheory.AdjoinRoot

namespace GaloisForLFunctions.HTGeometry.ABHN

open Polynomial

attribute [local instance] Ideal.Quotient.field

universe u

#check AdjoinRoot.quotEquivQuotMap
#check Polynomial.Monic.free_adjoinRoot
#check Polynomial.Monic.finite_adjoinRoot

noncomputable def testReductionEquiv
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) :
    (AdjoinRoot f ⧸ Ideal.map (AdjoinRoot.of f) 𝓂[K]) ≃ₐ[𝒪[K]]
      AdjoinRoot (f.map (Ideal.Quotient.mk 𝓂[K])) :=
  AdjoinRoot.quotEquivQuotMap f 𝓂[K]

noncomputable def testReductionEquivOfMapEq
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (g : Polynomial 𝓀[K])
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) :
    (AdjoinRoot f ⧸ Ideal.map (AdjoinRoot.of f) 𝓂[K]) ≃ₐ[𝒪[K]] AdjoinRoot g :=
  (AdjoinRoot.quotEquivQuotMap f 𝓂[K]).trans
    (AdjoinRoot.algEquivOfEq 𝒪[K] _ g hfg)

theorem test_exists_finite_free_lift
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (g : Polynomial 𝓀[K]) (hg : g.Monic) :
    ∃ f : Polynomial 𝒪[K], f.Monic ∧ f.map (Ideal.Quotient.mk 𝓂[K]) = g ∧
      f.natDegree = g.natDegree ∧ Module.Free 𝒪[K] (AdjoinRoot f) ∧
      Module.Finite 𝒪[K] (AdjoinRoot f) ∧
      (AdjoinRoot f ⧸ Ideal.map (AdjoinRoot.of f) 𝓂[K]) ≃ₐ[𝒪[K]] AdjoinRoot g := by
  obtain ⟨f, hf, hmap, hdegree⟩ :=
    nonarchimedeanLocalField_exists_monic_residuePolynomial_lift K g hg
  exact ⟨f, hf, hmap, hdegree, hf.free_adjoinRoot, hf.finite_adjoinRoot,
    testReductionEquivOfMapEq K f g hmap⟩

end GaloisForLFunctions.HTGeometry.ABHN
