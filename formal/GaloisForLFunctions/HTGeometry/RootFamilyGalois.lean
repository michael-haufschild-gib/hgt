import GaloisForLFunctions.HTGeometry.GalPermutationRealization

/-!
# The Galois group from a labelled root family

A splitting field is usually met with its roots already labelled by a combinatorial index — the
points of a hypercube, say — rather than as an abstract root set.  The permutations of that index
realized by base automorphisms form a subgroup, so realizing a generating set is enough, and the
Galois group is the full symmetric group on the index.

## Main results

* `realizedPermSubgroup` — the realized permutations of a labelled root family.
* `card_gal_eq_factorial_of_rootFamily` — the Galois group is symmetric once a generating set of
  index permutations is realized.
-/

open Polynomial
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {F E : Type*} [Field F] [Field E] [Algebra F E] {ι : Type*}

/-- Permutations of a labelled root family realized by base automorphisms. -/
def realizedPermSubgroup (θ : ι → E) : Subgroup (Equiv.Perm ι) where
  carrier := {π | ∃ σ : E ≃ₐ[F] E, ∀ i, σ (θ i) = θ (π i)}
  one_mem' := ⟨1, fun i => rfl⟩
  mul_mem' := by
    rintro π₁ π₂ ⟨σ₁, h₁⟩ ⟨σ₂, h₂⟩
    exact ⟨σ₂.trans σ₁, fun i => by
      show σ₁ (σ₂ (θ i)) = θ ((π₁ * π₂) i)
      rw [h₂ i, h₁ (π₂ i)]
      rfl⟩
  inv_mem' := by
    rintro π ⟨σ, h⟩
    refine ⟨σ.symm, fun i => ?_⟩
    have hi := h (π⁻¹ i)
    have hpi : π (π⁻¹ i) = i := by simp
    rw [hpi] at hi
    rw [← hi, AlgEquiv.symm_apply_apply]

theorem mem_realizedPermSubgroup {θ : ι → E} {π : Equiv.Perm ι} :
    π ∈ realizedPermSubgroup (F := F) θ ↔ ∃ σ : E ≃ₐ[F] E, ∀ i, σ (θ i) = θ (π i) := Iff.rfl

/-- **Every index permutation is realized** once a generating set is. -/
theorem realizedPermSubgroup_eq_top {θ : ι → E} {S : Set (Equiv.Perm ι)}
    (hS : Subgroup.closure S = ⊤)
    (hmem : ∀ π ∈ S, ∃ σ : E ≃ₐ[F] E, ∀ i, σ (θ i) = θ (π i)) :
    realizedPermSubgroup (F := F) θ = ⊤ := by
  refine eq_top_iff.mpr ?_
  rw [← hS]
  exact Subgroup.closure_le _ |>.mpr fun π hπ => hmem π hπ

variable [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- The root set of a polynomial split by a labelled family is the range of the family. -/
theorem rootSet_eq_range_of_prod {p : Polynomial F} {θ : ι → E}
    (hroots : p.map (algebraMap F E) = ∏ i, (Polynomial.X - Polynomial.C (θ i))) :
    p.rootSet E = Set.range θ := by
  classical
  have hne : p.map (algebraMap F E) ≠ 0 := by
    rw [hroots]
    refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
    exact Polynomial.X_sub_C_ne_zero (θ i)
  ext x
  rw [Polynomial.mem_rootSet']
  constructor
  · rintro ⟨-, hx⟩
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, hroots] at hx
    have := Polynomial.eval_prod (Finset.univ : Finset ι)
      (fun i => Polynomial.X - Polynomial.C (θ i)) x
    rw [hx] at this
    obtain ⟨i, -, hi⟩ := Finset.prod_eq_zero_iff.mp this.symm
    refine ⟨i, ?_⟩
    have : x - θ i = 0 := by simpa using hi
    exact (sub_eq_zero.mp this).symm
  · rintro ⟨i, rfl⟩
    refine ⟨hne, ?_⟩
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, hroots, Polynomial.eval_prod]
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    simp

omit [DecidableEq ι] in
/-- **The Galois group is the full symmetric group on the labels** once a generating set of index
permutations is realized by base automorphisms. -/
theorem card_gal_eq_factorial_of_rootFamily (p : Polynomial F)
    [Fact (p.map (algebraMap F E)).Splits]
    {θ : ι → E} (hinj : Function.Injective θ)
    (hroots : p.map (algebraMap F E) = ∏ i, (Polynomial.X - Polynomial.C (θ i)))
    {S : Set (Equiv.Perm ι)} (hS : Subgroup.closure S = ⊤)
    (hmem : ∀ π ∈ S, ∃ σ : E ≃ₐ[F] E, ∀ i, σ (θ i) = θ (π i)) :
    Nat.card p.Gal = (Fintype.card ι).factorial := by
  classical
  have hrange := rootSet_eq_range_of_prod (E := E) hroots
  have htop := realizedPermSubgroup_eq_top (F := F) (θ := θ) hS hmem
  have hmemRoot : ∀ i, θ i ∈ p.rootSet E := by
    intro i
    rw [hrange]
    exact ⟨i, rfl⟩
  set ε : ι → p.rootSet E := fun i => ⟨θ i, hmemRoot i⟩ with hε
  have hεinj : Function.Injective ε := by
    intro a b hab
    exact hinj (congrArg Subtype.val hab)
  have hεsurj : Function.Surjective ε := by
    rintro ⟨x, hx⟩
    rw [hrange] at hx
    obtain ⟨i, rfl⟩ := hx
    exact ⟨i, rfl⟩
  set e : ι ≃ p.rootSet E := Equiv.ofBijective ε ⟨hεinj, hεsurj⟩ with he
  haveI : Fintype (p.rootSet E) := Fintype.ofEquiv ι e
  have hcard : Fintype.card (p.rootSet E) = Fintype.card ι := (Fintype.card_congr e).symm
  have hsurj : Function.Surjective (Gal.galActionHom p E) := by
    intro τ
    set π : Equiv.Perm ι := (e.trans (τ.trans e.symm)) with hπ
    obtain ⟨σ, hσ⟩ := (htop ▸ Subgroup.mem_top π :
      π ∈ realizedPermSubgroup (F := F) θ)
    refine ⟨Gal.restrict p E σ, ?_⟩
    ext x
    obtain ⟨i, rfl⟩ := hεsurj x
    rw [Gal.galActionHom_restrict]
    have : σ ((ε i : E)) = ((ε (π i) : E)) := hσ i
    show σ ((ε i : E)) = ((τ (ε i) : E))
    rw [this]
    have : e (π i) = τ (e i) := by
      rw [hπ]
      simp
    have h2 : ε (π i) = τ (ε i) := this
    rw [h2]
  have hbij : Function.Bijective (Gal.galActionHom p E) :=
    ⟨Gal.galActionHom_injective p E, hsurj⟩
  rw [Nat.card_eq_of_bijective _ hbij, Nat.card_eq_fintype_card, Fintype.card_perm, hcard]

end

end GaloisForLFunctions.HTGeometry
