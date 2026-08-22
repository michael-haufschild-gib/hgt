import GaloisForLFunctions.HTGeometry.SpectralRelationSpaceGalois
import GaloisForLFunctions.HTGeometry.SpectralFormConjugateBound
import Mathlib.NumberTheory.NumberField.Basic

/-!
# The spectrum of an integer matrix as algebraic integers of a number field

Theorem A and Theorem B of the arithmetic hardness–recurrence card take their spectrum as a family
of algebraic integers in a number field together with a distinguished complex embedding.  For an
integer matrix the characteristic polynomial is monic integral, so its splitting field is a number
field and its roots are algebraic integers; and the rigidity of the root family (no rational
relation but the trace relation) is exactly the hypothesis `spectralForm E m ≠ 0` those theorems
consume.

## Main results

* `isIntegral_of_isRoot_charpoly` — a root of the characteristic polynomial is an algebraic integer.
* `spectralForm_ne_zero_of_ker_eq_constLine` — **rigidity gives the integer-relation hypothesis.**
-/

open Polynomial NumberField
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **A root of the characteristic polynomial of an integer matrix is an algebraic integer.** -/
theorem isIntegral_of_isRoot_charpoly {K : Type*} [Field K] [Algebra ℚ K]
    (Hz : Matrix ι ι ℤ) {x : K}
    (hx : ((Hz.charpoly.map (Int.castRingHom ℚ)).map (algebraMap ℚ K)).IsRoot x) :
    IsIntegral ℤ x := by
  refine ⟨Hz.charpoly, Hz.charpoly_monic, ?_⟩
  have hcomp : (algebraMap ℤ K) = (algebraMap ℚ K).comp (Int.castRingHom ℚ) := by
    refine RingHom.ext fun z => ?_
    simp
  rw [hcomp, ← Polynomial.eval₂_map, Polynomial.eval₂_eq_eval_map]
  exact hx

/-- **Rigidity of the root family gives the integer-relation hypothesis of Theorems A and B.** -/
theorem spectralForm_ne_zero_of_ker_eq_constLine {K : Type*} [Field K] [NumberField K] {d : ℕ}
    (E : Fin (d + 1) → 𝓞 K)
    (hker : LinearMap.ker (ratRelationForm (fun j => ((E j : 𝓞 K) : K)))
      = PermSubspace.constLine (K := ℚ) (ι := Fin (d + 1)))
    (m : Fin d → ℤ) (hm : m ≠ 0) : spectralForm E m ≠ 0 := by
  classical
  intro h0
  set γ : Fin (d + 1) → K := fun j => ((E j : 𝓞 K) : K) with hγ
  set a : Fin (d + 1) → ℚ := Fin.cons (-(∑ j, (m j : ℚ))) (fun j => ((m j : ℤ) : ℚ)) with ha
  have ha0 : a 0 = -(∑ j, (m j : ℚ)) := by rw [ha]; simp
  have hasucc : ∀ j : Fin d, a j.succ = ((m j : ℤ) : ℚ) := by
    intro j
    rw [ha]
    simp
  have hcast : ∑ j : Fin d, ((m j : ℤ) : ℚ) • (γ j.succ - γ 0) = 0 := by
    have hz : ((spectralForm E m : 𝓞 K) : K) = 0 := by
      rw [h0]
      simp
    rw [spectralForm] at hz
    push_cast at hz
    rw [← hz]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [zsmul_eq_mul, Rat.smul_def]
    push_cast
    ring
  have hexpand : ∑ j : Fin d, ((m j : ℤ) : ℚ) • (γ j.succ - γ 0)
      = (∑ j : Fin d, ((m j : ℤ) : ℚ) • γ j.succ)
        - (∑ j : Fin d, ((m j : ℤ) : ℚ)) • γ 0 := by
    rw [Finset.sum_smul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => smul_sub _ _ _
  rw [hexpand] at hcast
  have heq : (∑ j : Fin d, ((m j : ℤ) : ℚ) • γ j.succ)
      = (∑ j : Fin d, ((m j : ℤ) : ℚ)) • γ 0 := sub_eq_zero.mp hcast
  have hval : ratRelationForm γ a = 0 := by
    rw [ratRelationForm_apply, Fin.sum_univ_succ]
    have hstep : ∑ j : Fin d, (a j.succ) • γ j.succ
        = ∑ j : Fin d, ((m j : ℤ) : ℚ) • γ j.succ :=
      Finset.sum_congr rfl fun j _ => by rw [hasucc j]
    rw [hstep, ha0, neg_smul, heq, neg_add_cancel]
  have hmem : a ∈ LinearMap.ker (ratRelationForm γ) := by
    rw [LinearMap.mem_ker]
    exact hval
  rw [hker] at hmem
  obtain ⟨c, hc⟩ := PermSubspace.eq_const_of_mem_constLine hmem
  have hcj : ∀ j : Fin d, ((m j : ℤ) : ℚ) = c := by
    intro j
    have hj : a j.succ = c := by rw [hc]
    rw [← hasucc j]
    exact hj
  have hc0 : -(∑ j : Fin d, (m j : ℚ)) = c := by
    have hj : a 0 = c := by rw [hc]
    rw [← ha0]
    exact hj
  have hsum : (∑ j : Fin d, (m j : ℚ)) = (d : ℚ) * c := by
    rw [Finset.sum_congr rfl (fun j _ => hcj j), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  rw [hsum] at hc0
  have hczero : c = 0 := by
    have hlin : ((d : ℚ) + 1) * c = 0 := by linarith
    have hd1 : ((d : ℚ) + 1) ≠ 0 := by positivity
    exact (mul_eq_zero.mp hlin).resolve_left hd1
  refine hm (funext fun j => ?_)
  have hj := hcj j
  rw [hczero] at hj
  exact_mod_cast hj

/-! ### Complex embeddings of the root family -/

/-- Every complex embedding sends a root of a rational polynomial to a complex root of it. -/
theorem isRoot_embedding {K : Type*} [Field K] [Algebra ℚ K] (p : Polynomial ℚ)
    {x : K} (hx : (p.map (algebraMap ℚ K)).IsRoot x) (τ : K →+* ℂ) :
    (p.map (algebraMap ℚ ℂ)).IsRoot (τ x) := by
  have hcomp : τ.comp (algebraMap ℚ K) = algebraMap ℚ ℂ := RingHom.ext_rat _ _
  have hval := congrArg τ hx
  rw [map_zero, Polynomial.eval_map, Polynomial.hom_eval₂, hcomp] at hval
  rw [Polynomial.IsRoot, Polynomial.eval_map]
  exact hval

/-- **Every conjugate of a root is bounded by a bound for the complex roots.** -/
theorem norm_embedding_le {K : Type*} [Field K] [Algebra ℚ K] {J : Type*} [Fintype J]
    (p : Polynomial ℚ)
    {E : J → ℂ} (hp : p.map (algebraMap ℚ ℂ) = ∏ i, (X - C (E i)))
    {x : K} (hx : (p.map (algebraMap ℚ K)).IsRoot x) (τ : K →+* ℂ) {R : ℝ}
    (hR : ∀ i, ‖E i‖ ≤ R) : ‖τ x‖ ≤ R := by
  classical
  have hroot := isRoot_embedding p hx τ
  rw [Polynomial.IsRoot, hp, Polynomial.eval_prod] at hroot
  obtain ⟨i, -, hi⟩ := Finset.prod_eq_zero_iff.mp hroot
  rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at hi
  rw [hi]
  exact hR i

/-- **Two labelled enumerations of the same root set differ by an embedding and a relabelling.** -/
theorem exists_embedding_matching_roots {K : Type*} [Field K] [Algebra ℚ K]
    [FiniteDimensional ℚ K] {D : ℕ} {p : Polynomial ℚ} {γ : Fin D → K}
    (hγinj : Function.Injective γ)
    (hγ : p.map (algebraMap ℚ K) = ∏ j, (X - C (γ j)))
    {ι : Type} [Fintype ι] [DecidableEq ι] {E : ι → ℂ} (hEinj : Function.Injective E)
    (hE : p.map (algebraMap ℚ ℂ) = ∏ i, (X - C (E i))) :
    ∃ (σ₀ : K →+* ℂ) (ρ : ι ≃ Fin D), ∀ i, σ₀ (γ (ρ i)) = E i := by
  classical
  haveI : Algebra.IsAlgebraic ℚ K := Algebra.IsAlgebraic.of_finite ℚ K
  let ψ : K →ₐ[ℚ] ℂ := IsAlgClosed.lift
  have hψinj : Function.Injective ψ := (ψ : K →+* ℂ).injective
  have hψγ : p.map (algebraMap ℚ ℂ) = ∏ j, (X - C (ψ (γ j))) := by
    have hmapmap : (p.map (algebraMap ℚ K)).map (ψ : K →+* ℂ) = p.map (algebraMap ℚ ℂ) := by
      rw [Polynomial.map_map]
      congr 1
      exact ψ.comp_algebraMap
    rw [← hmapmap, hγ, Polynomial.map_prod]
    exact Finset.prod_congr rfl fun j _ => by
      rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
      rfl
  have hψγinj : Function.Injective (fun j => ψ (γ j)) := hψinj.comp hγinj
  have hrangeE : p.rootSet ℂ = Set.range E := rootSet_eq_range_of_prod hE
  have hrangeG : p.rootSet ℂ = Set.range (fun j => ψ (γ j)) := rootSet_eq_range_of_prod hψγ
  refine ⟨(ψ : K →+* ℂ),
    (Equiv.ofInjective E hEinj).trans
      ((Equiv.setCongr (hrangeE.symm.trans hrangeG)).trans
        (Equiv.ofInjective (fun j => ψ (γ j)) hψγinj).symm), fun i => ?_⟩
  exact Equiv.apply_ofInjective_symm (f := fun j => ψ (γ j)) hψγinj
    ((Equiv.setCongr (hrangeE.symm.trans hrangeG)) (Equiv.ofInjective E hEinj i))

end

end GaloisForLFunctions.HTGeometry
