import GaloisForLFunctions.HTGeometry.CylinderDifferentialCharacter
import GaloisForLFunctions.HTGeometry.SourceLogarithmicBoundary

/-!
# Hypertranscendence of a source with a cotangent cylinder increment

This is the reduction step of the double-sine translation-annihilator theorem, assembled from two
already proved pieces.

The arbitrary-family differential Ostrowski criterion of `SourceLogarithmicBoundary` says that an
additive primitive `Ψ` for a compatible automorphism family with common fixed field `ℂ` is
differentially transcendental over the base exactly when no nonzero finite constant differential
character of its increment family is a simultaneous base coboundary.

`CylinderDifferentialCharacter` proves that in the two-cylinder field `ℂ(u₁)(u₂)` no such character
of the cotangent model `c(u₂+1)/(u₂-1)` is a coboundary for a non-torsion dilation of `u₂`.

Combining them gives `hypertranscendentalOver_of_cotangentCylinderIncrement`: only one of the two
translation directions has to be examined, and its increment only has to be the cotangent model
with the cylinder differential jets.  The other directions enter solely through the common
fixed-field hypothesis, which is where the two incommensurate periods are used.
-/

open Polynomial
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A finite sum over `Unit × ℕ` reindexes to a sum over `ℕ`. -/
theorem sum_unitProd {M : Type*} [AddCommMonoid M] (s : Finset (Unit × ℕ)) (f : Unit × ℕ → M) :
    ∑ p ∈ s, f p = ∑ n ∈ s.image Prod.snd, f ((), n) := by
  classical
  refine Finset.sum_nbij' (i := fun p => p.2) (j := fun n => ((), n)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
  · intro n hn
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hn
    have : p = ((), p.2) := by
      cases p with | mk a bb => cases a; rfl
    rwa [← this]
  · intro p _
    cases p with | mk a bb => cases a; rfl
  · intro n _
    rfl
  · intro p _
    cases p with | mk a bb => cases a; rfl

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- **Hypertranscendence from a cotangent cylinder increment.**  Let a family of compatible
differential automorphisms of `L` have common fixed field `ℂ`, and let `Ψ` be an additive primitive
whose increments lie in the two-cylinder field `ℂ(u₁)(u₂)`.  If one direction acts by a non-torsion
dilation of `u₂` and its increment is the cotangent model `c(u₂+1)/(u₂-1)` with the cylinder
differential jets, then `Ψ` is hypertranscendental over the two-cylinder field. -/
theorem hypertranscendentalOver_of_cotangentCylinderIncrement
    {I L : Type*} [Field L]
    [Differential (RatFunc (RatFunc ℂ))]
    [Algebra (RatFunc (RatFunc ℂ)) L] [Algebra ℂ L]
    [IsScalarTower ℂ (RatFunc (RatFunc ℂ)) L]
    [Differential L] [DifferentialAlgebra (RatFunc (RatFunc ℂ)) L]
    (tau : I → RatFunc (RatFunc ℂ) ≃+* RatFunc (RatFunc ℂ)) (sigma : I → L ≃+* L)
    (hcomp : ∀ i k, sigma i (algebraMap (RatFunc (RatFunc ℂ)) L k)
      = algebraMap (RatFunc (RatFunc ℂ)) L (tau i k))
    (hderivcomm : ∀ i (y : L), sigma i y′ = (sigma i y)′)
    (hCfixed : ∀ i (z : ℂ), sigma i (algebraMap ℂ L z) = algebraMap ℂ L z)
    (hfixed : ∀ z : L, (∀ i, sigma i z = z) → ∃ w : ℂ, algebraMap ℂ L w = z)
    (Ψ : L) (bb : I → RatFunc (RatFunc ℂ))
    (hshift : ∀ i, sigma i Ψ = Ψ + algebraMap (RatFunc (RatFunc ℂ)) L (bb i))
    (i₀ : I) (q lam c : ℂ) (hq : q ≠ 0) (hqtor : ∀ n : ℤ, n ≠ 0 → q ^ n ≠ 1)
    (hlam : lam ≠ 0) (hc : c ≠ 0)
    (htau : ∀ k, tau i₀ k
      = ratFuncScale (algebraMap ℂ (RatFunc ℂ) q) (by simpa using hq) k)
    (hjet : ∀ n : ℕ, differentialJet n (bb i₀)
      = (cylDeriv (algebraMap ℂ (RatFunc ℂ) lam))^[n]
          (cotModel (algebraMap ℂ (RatFunc ℂ) c))) :
    HypertranscendentalOver (RatFunc (RatFunc ℂ)) Ψ := by
  classical
  rw [hypertranscendentalOver_iff_differentialIndependent_singleton,
    automorphismFamily_differentialIndependent_iff_no_constant_simultaneous_jet_telescoping
      (I := I) (κ := Unit) (C := ℂ) (K := RatFunc (RatFunc ℂ)) (L := L)
      tau sigma hcomp hderivcomm hCfixed hfixed (fun _ : Unit => Ψ) (fun i _ => bb i)
      (fun i _ => hshift i)]
  intro γ hγ k
  refine ⟨i₀, ?_⟩
  set α : ℕ →₀ ℂ := Finsupp.equivMapDomain (Equiv.punitProd ℕ) γ with hα
  have hαapply : ∀ n : ℕ, α n = γ ((), n) := by
    intro n
    rw [hα, Finsupp.equivMapDomain_apply]
    rfl
  have hαsupp : α.support = γ.support.image Prod.snd := by
    ext n
    simp only [Finsupp.mem_support_iff, hαapply, Finset.mem_image]
    constructor
    · intro hn
      exact ⟨((), n), hn, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      have hpe : p = ((), p.2) := by
        cases p with | mk a bbb => cases a; rfl
      rw [← hpe]
      exact hp
  have hαne : α ≠ 0 := by
    intro hzero
    apply hγ
    have hemp : α.support = ∅ := by rw [hzero]; simp
    rw [hαsupp] at hemp
    refine Finsupp.support_eq_empty.mp (Finset.eq_empty_of_forall_notMem ?_)
    intro p hp
    have : p.2 ∈ γ.support.image Prod.snd := Finset.mem_image.mpr ⟨p, hp, rfl⟩
    rw [hemp] at this
    exact absurd this (Finset.notMem_empty _)
  have hmap : ∀ x : ℂ, algebraMap ℂ (RatFunc (RatFunc ℂ)) x
      = algebraMap (RatFunc ℂ) (RatFunc (RatFunc ℂ)) (algebraMap ℂ (RatFunc ℂ) x) :=
    fun x => IsScalarTower.algebraMap_apply ℂ (RatFunc ℂ) (RatFunc (RatFunc ℂ)) x
  rw [htau, Finsupp.linearCombination_apply, Finsupp.sum,
    Finsupp.support_mapRange_of_injective (map_zero (algebraMap ℂ (RatFunc (RatFunc ℂ)))) γ
      (algebraMap ℂ (RatFunc (RatFunc ℂ))).injective]
  simp only [Finsupp.mapRange_apply, smul_eq_mul]
  rw [sum_unitProd, ← hαsupp]
  simp only [← hαapply, hjet, hmap]
  exact no_constantCharacter_dilationTelescoping_twoCylinder q lam c hq hqtor hlam hc α hαne k

end

end GaloisForLFunctions.HTGeometry
