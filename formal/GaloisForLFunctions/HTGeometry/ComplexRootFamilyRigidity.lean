import GaloisForLFunctions.HTGeometry.SpectralRelationSpaceGalois
import GaloisForLFunctions.HTGeometry.SpectralExponentialIndependence

/-!
# Rigidity of a complex root family with symmetric Galois group

`SpectralRelationSpaceGalois` proves that the roots of a traceless monic irreducible rational
polynomial with full symmetric Galois group carry no rational relation other than the trace
relation, inside the polynomial's splitting field.  The spectral argument needs the same statement
for the roots as *complex numbers*, in whatever labelling the analysis produces them.

Both are labelled enumerations of the same root set, so they differ by a field embedding of the
splitting field into `ℂ` and a relabelling; the relation space is carried along both.  No
automorphism of `ℂ` is needed -- which is the point, since the Galois action does not extend to one
without choice-heavy machinery.

## Main results

* `ker_relationForm_eq_constLine_of_gal` — **the only rational relation among the complex roots is
  the trace relation.**
-/

open Polynomial
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **The only rational relation among the complex roots is the trace relation.** -/
theorem ker_relationForm_eq_constLine_of_gal {p : Polynomial ℚ}
    (hmonic : p.Monic) (hirr : Irreducible p) {D : ℕ} (hdeg : p.natDegree = D) (hD1 : 1 < D)
    (hcoeff : p.coeff (D - 1) = 0) (hgal : Nat.card p.Gal = D.factorial)
    {ι : Type} [Fintype ι] [DecidableEq ι] {E : ι → ℂ} (hEinj : Function.Injective E)
    (hEprod : p.map (algebraMap ℚ ℂ) = ∏ i, (X - C (E i))) :
    LinearMap.ker (SpectralExp.relationForm E) = PermSubspace.constLine (K := ℚ) (ι := ι) := by
  classical
  obtain ⟨γ, hγinj, hγ, hker⟩ := exists_rigid_root_family hmonic hirr hdeg hD1 hcoeff hgal
  haveI hsf : IsSplittingField ℚ p.SplittingField p :=
    Polynomial.IsSplittingField.splittingField p
  haveI : FiniteDimensional ℚ p.SplittingField :=
    Polynomial.IsSplittingField.finiteDimensional p.SplittingField p
  let ψ : p.SplittingField →ₐ[ℚ] ℂ := IsAlgClosed.lift
  have hψinj : Function.Injective ψ := (ψ : p.SplittingField →+* ℂ).injective
  -- the splitting transported to `ℂ`
  have hψγ : p.map (algebraMap ℚ ℂ) = ∏ j, (X - C (ψ (γ j))) := by
    have hmapmap : (p.map (algebraMap ℚ p.SplittingField)).map
        (ψ : p.SplittingField →+* ℂ) = p.map (algebraMap ℚ ℂ) := by
      rw [Polynomial.map_map]
      congr 1
      exact ψ.comp_algebraMap
    rw [← hmapmap, hγ, Polynomial.map_prod]
    exact Finset.prod_congr rfl fun j _ => by
      rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
      rfl
  have hψγinj : Function.Injective (fun j => ψ (γ j)) := hψinj.comp hγinj
  have hrangeE : p.rootSet ℂ = Set.range E := rootSet_eq_range_of_prod hEprod
  have hrangeG : p.rootSet ℂ = Set.range (fun j => ψ (γ j)) := rootSet_eq_range_of_prod hψγ
  -- the relabelling
  let ρ : ι ≃ Fin D :=
    (Equiv.ofInjective E hEinj).trans
      ((Equiv.setCongr (hrangeE.symm.trans hrangeG)).trans
        (Equiv.ofInjective (fun j => ψ (γ j)) hψγinj).symm)
  have hρ : ∀ i, ψ (γ (ρ i)) = E i := by
    intro i
    have hb := Equiv.apply_ofInjective_symm (f := fun j => ψ (γ j)) hψγinj
      ((Equiv.setCongr (hrangeE.symm.trans hrangeG)) (Equiv.ofInjective E hEinj i))
    exact hb
  set θ : ι → p.SplittingField := fun i => γ (ρ i) with hθ
  -- the relation form factors through the embedding
  have hval : ∀ a : ι → ℚ,
      SpectralExp.relationForm E a = ψ (ratRelationForm θ a) := by
    intro a
    rw [SpectralExp.relationForm_apply, ratRelationForm_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 : ψ (a i • θ i) = a i • ψ (θ i) := by
      rw [Algebra.smul_def, map_mul, AlgHom.commutes, ← Algebra.smul_def]
    rw [h1]
    exact congrArg (fun z : ℂ => a i • z) (hρ i).symm
  have hkerE : LinearMap.ker (SpectralExp.relationForm E)
      = LinearMap.ker (ratRelationForm θ) := by
    ext a
    rw [LinearMap.mem_ker, LinearMap.mem_ker, hval a]
    constructor
    · intro h
      exact hψinj (by rw [h, map_zero])
    · intro h
      rw [h, map_zero]
  have hsum : ∑ j, γ j = 0 := by
    have h1 : (fun _ => (1 : ℚ)) ∈ LinearMap.ker (ratRelationForm γ) := by
      rw [hker]
      exact PermSubspace.const_mem_constLine 1
    rw [LinearMap.mem_ker, ratRelationForm_apply] at h1
    simpa using h1
  rw [hkerE]
  ext a
  constructor
  · intro ha
    rw [LinearMap.mem_ker, ratRelationForm_apply] at ha
    have hb : (fun j => a (ρ.symm j)) ∈ LinearMap.ker (ratRelationForm γ) := by
      rw [LinearMap.mem_ker, ratRelationForm_apply, ← ha]
      refine (Fintype.sum_equiv ρ (fun i => a i • θ i)
        (fun j => a (ρ.symm j) • γ j) ?_).symm
      intro i
      simp [hθ]
    rw [hker] at hb
    obtain ⟨c, hc⟩ := PermSubspace.eq_const_of_mem_constLine hb
    have hac : a = fun _ => c := by
      funext i
      have hci := congrFun hc (ρ i)
      simpa using hci
    rw [hac]
    exact PermSubspace.const_mem_constLine c
  · intro ha
    obtain ⟨c, hc⟩ := PermSubspace.eq_const_of_mem_constLine ha
    rw [LinearMap.mem_ker, ratRelationForm_apply, hc]
    have hshift : ∑ i, c • θ i = ∑ j, c • γ j :=
      Fintype.sum_equiv ρ (fun i => c • θ i) (fun j => c • γ j) (fun i => rfl)
    show ∑ i, c • θ i = 0
    rw [hshift, ← Finset.smul_sum, hsum, smul_zero]

end

end GaloisForLFunctions.HTGeometry
