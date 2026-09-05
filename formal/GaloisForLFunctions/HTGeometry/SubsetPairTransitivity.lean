import GaloisForLFunctions.HTGeometry.JohnsonGraphConnected

/-!
# One transposition of subsets, plus the induced symmetric group, is everything

The symmetric group of a finite set is transitive on pairs of subsets with prescribed cardinalities
and prescribed intersection cardinality:

```text
exists_perm_mapsTo       a permutation carrying one finset into another of the same size
exists_perm_image_pair   ** and one carrying a pair onto a pair with the same intersection size **
```

The pair statement is proved in two moves: first carry the left members onto each other, then
correct the right members with `Equiv.Perm.subtypeCongr`, whose two halves act inside and outside
the common left member and are again instances of the one-set statement.

Conjugating a transposition by the induced action therefore reaches every transposition with the
same intersection size, and the connectivity of the fixed-intersection graph upgrades those to the
whole symmetric group on `m`-subsets:

```text
finsetPerm                                      the induced action on `m`-subsets
eq_top_of_induced_symmetric_and_johnson_swap    ** the induced symmetric group and one such
                                                   transposition generate everything **
```

This route needs no primitivity: transitivity on pairs replaces the block-system analysis, so a
monodromy group known to contain the ground-set symmetric group and a single transposition of two
subsets meeting in `j` points is the full symmetric group on the subsets.
-/

namespace GaloisForLFunctions.HTGeometry

open Finset

variable {β : Type*} [DecidableEq β] [Fintype β]

theorem exists_perm_mapsTo {U V : Finset β} (h : U.card = V.card) :
    ∃ σ : Equiv.Perm β, ∀ x ∈ U, σ x ∈ V := by
  classical
  have hc : Fintype.card {x // x ∈ U} = Fintype.card {x // x ∈ V} := by
    simpa using h
  exact ⟨(Fintype.equivOfCardEq hc).extendSubtype,
    fun x hx => Equiv.extendSubtype_mem _ x hx⟩

omit [Fintype β] in
theorem image_eq_of_mapsTo {U V : Finset β} (σ : Equiv.Perm β)
    (h : ∀ x ∈ U, σ x ∈ V) (hcard : U.card = V.card) : U.image σ = V := by
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact h x hx
  · rw [Finset.card_image_of_injective _ σ.injective, hcard]

/-- **A permutation carrying one pair of finsets onto another.**  Two pairs with the same two
cardinalities and the same intersection cardinality are in the same orbit of the symmetric group:
first move the left members onto each other, then correct inside and outside the common left member
with `Equiv.Perm.subtypeCongr`. -/
private theorem exists_perm_image_pair {S T S' T' : Finset β}
    (hS : S.card = S'.card) (hT : T.card = T'.card)
    (hI : (S ∩ T).card = (S' ∩ T').card) :
    ∃ σ : Equiv.Perm β, S.image σ = S' ∧ T.image σ = T' := by
  classical
  obtain ⟨σ₁, hσ₁⟩ := exists_perm_mapsTo hS
  have hS1 : S.image σ₁ = S' := image_eq_of_mapsTo σ₁ hσ₁ hS
  have hT1card : (T.image σ₁).card = T'.card := by
    rw [Finset.card_image_of_injective _ σ₁.injective, hT]
  have hint1 : (S' ∩ T.image σ₁).card = (S' ∩ T').card := by
    have hEq : S' ∩ T.image σ₁ = (S ∩ T).image σ₁ := by
      rw [Finset.image_inter _ _ σ₁.injective, hS1]
    rw [hEq, Finset.card_image_of_injective _ σ₁.injective, hI]
  have hinter : ((T.image σ₁) ∩ S').card = (T' ∩ S').card := by
    rw [Finset.inter_comm _ S', Finset.inter_comm T' S']
    exact hint1
  -- inside `S'`
  have hin : ((T.image σ₁).subtype (· ∈ S')).card = (T'.subtype (· ∈ S')).card := by
    rw [Finset.card_subtype, Finset.card_subtype, Finset.filter_mem_eq_inter,
      Finset.filter_mem_eq_inter]
    exact hinter
  obtain ⟨ep, hep⟩ := exists_perm_mapsTo hin
  -- outside `S'`
  have hout : ((T.image σ₁).subtype (· ∉ S')).card = (T'.subtype (· ∉ S')).card := by
    rw [Finset.card_subtype, Finset.card_subtype, ← Finset.sdiff_eq_filter, ← Finset.sdiff_eq_filter]
    have h1 := Finset.card_inter_add_card_sdiff (T.image σ₁) S'
    have h2 := Finset.card_inter_add_card_sdiff T' S'
    omega
  obtain ⟨en, hen⟩ := exists_perm_mapsTo hout
  refine ⟨(ep.subtypeCongr en) * σ₁, ?_, ?_⟩
  · rw [Equiv.Perm.coe_mul, ← Finset.image_image, hS1]
    refine image_eq_of_mapsTo _ (fun x hx => ?_) rfl
    rw [Equiv.Perm.subtypeCongr.left_apply _ _ hx]
    exact (ep ⟨x, hx⟩).2
  · rw [Equiv.Perm.coe_mul, ← Finset.image_image]
    refine image_eq_of_mapsTo _ (fun x hx => ?_) hT1card
    by_cases hxS : x ∈ S'
    · rw [Equiv.Perm.subtypeCongr.left_apply _ _ hxS]
      have hmem : (⟨x, hxS⟩ : {a // a ∈ S'}) ∈ (T.image σ₁).subtype (· ∈ S') := by
        rw [Finset.mem_subtype]
        exact hx
      have := hep _ hmem
      rw [Finset.mem_subtype] at this
      exact this
    · rw [Equiv.Perm.subtypeCongr.right_apply _ _ hxS]
      have hmem : (⟨x, hxS⟩ : {a // a ∉ S'}) ∈ (T.image σ₁).subtype (· ∉ S') := by
        rw [Finset.mem_subtype]
        exact hx
      have := hen _ hmem
      rw [Finset.mem_subtype] at this
      exact this

section Induced

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- The permutation of `m`-subsets induced by a permutation of the ground set. -/
def finsetPerm (m : ℕ) (σ : Equiv.Perm α) : Equiv.Perm {s : Finset α // s.card = m} where
  toFun S := ⟨S.1.image σ, by rw [Finset.card_image_of_injective _ σ.injective]; exact S.2⟩
  invFun S := ⟨S.1.image σ.symm, by
    rw [Finset.card_image_of_injective _ σ.symm.injective]; exact S.2⟩
  left_inv S := by
    refine Subtype.ext ?_
    show (S.1.image σ).image σ.symm = S.1
    rw [Finset.image_image]
    simp
  right_inv S := by
    refine Subtype.ext ?_
    show (S.1.image σ.symm).image σ = S.1
    rw [Finset.image_image]
    simp

omit [Fintype α] in
theorem finsetPerm_apply (m : ℕ) (σ : Equiv.Perm α) (S : {s : Finset α // s.card = m}) :
    (finsetPerm m σ S).1 = S.1.image σ := rfl

/-- **One transposition of `m`-subsets plus the induced symmetric group is everything.**  The
symmetric group of the ground set is transitive on pairs of `m`-subsets with a given intersection
size, so conjugating one such transposition produces all of them, and the connectivity of the
fixed-intersection graph turns those into the full symmetric group on `m`-subsets. -/
theorem eq_top_of_induced_symmetric_and_johnson_swap {m j : ℕ} (hj : j < m)
    (hbig : 2 * m ≤ Fintype.card α) (hne : j ≠ 0 ∨ 2 * m ≠ Fintype.card α)
    {G : Subgroup (Equiv.Perm {s : Finset α // s.card = m})}
    (hsym : ∀ σ : Equiv.Perm α, finsetPerm m σ ∈ G)
    {S₀ T₀ : {s : Finset α // s.card = m}} (hj0 : (S₀.1 ∩ T₀.1).card = j)
    (h0 : Equiv.swap S₀ T₀ ∈ G) :
    G = ⊤ := by
  classical
  refine eq_top_of_johnsonSwaps hj hbig hne (fun S T hST => ?_)
  obtain ⟨σ, h1, h2⟩ := exists_perm_image_pair (S := S₀.1) (T := T₀.1) (S' := S.1) (T' := T.1)
    (by rw [S₀.2, S.2]) (by rw [T₀.2, T.2]) (by rw [hj0, hST])
  have hmap : finsetPerm m σ S₀ = S := Subtype.ext h1
  have hmap2 : finsetPerm m σ T₀ = T := Subtype.ext h2
  have hconj := Equiv.swap_apply_apply (finsetPerm m σ) S₀ T₀
  rw [hmap, hmap2] at hconj
  rw [hconj]
  exact G.mul_mem (G.mul_mem (hsym σ) h0) (G.inv_mem (hsym σ))

end Induced

end GaloisForLFunctions.HTGeometry
