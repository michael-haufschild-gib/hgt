import GaloisForLFunctions.HTGeometry.ABHN.LocalValuationSequence
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Henselian

namespace GaloisForLFunctions.HTGeometry.ABHN

open Polynomial
open scoped ValuativeRel

attribute [local instance] Ideal.Quotient.field

universe u

noncomputable example
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) :
    (AdjoinRoot f ⧸ Ideal.map (AdjoinRoot.of f) 𝓂[K]) ≃ₐ[𝒪[K]]
      AdjoinRoot (f.map (Ideal.Quotient.mk 𝓂[K])) :=
  AdjoinRoot.quotEquivQuotMap f 𝓂[K]

noncomputable example
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

end GaloisForLFunctions.HTGeometry.ABHN
