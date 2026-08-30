import Mathlib

/-!
# Connectivity of the fixed-intersection graph on `m`-subsets

Two `m`-subsets meeting in exactly `j` points are joined by an edge.  The resulting graph is
connected whenever `j < m` and there is room for one extra point outside a pair of subsets differing
by a single swap — that is, in every case except `j = 0` with the ambient set of size exactly `2m`,
where the graph is the perfect matching by complementation.
-/

namespace GaloisForLFunctions.HTGeometry

open Finset

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- One edge of the fixed-intersection graph on `m`-subsets. -/
def JohnsonStep (m j : ℕ) (S T : Finset α) : Prop :=
  S.card = m ∧ T.card = m ∧ (S ∩ T).card = j

omit [Fintype α] in
theorem johnsonStep_symm {m j : ℕ} {S T : Finset α} (h : JohnsonStep m j S T) :
    JohnsonStep m j T S := by
  obtain ⟨hS, hT, hST⟩ := h
  exact ⟨hT, hS, by rw [Finset.inter_comm]; exact hST⟩

omit [Fintype α] in
theorem eq_of_card_inter_eq {m : ℕ} {S T : Finset α} (hS : S.card = m) (hT : T.card = m)
    (hint : (S ∩ T).card = m) : S = T := by
  have h1 : S ∩ T = S := Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
  have h2 : S ⊆ T := by
    rw [← h1]
    exact Finset.inter_subset_right
  exact Finset.eq_of_subset_of_card_le h2 (by omega)

/-- **One swap is a path of length two.** -/
theorem reflTransGen_of_inter_card_pred {m j : ℕ} (hj : j < m)
    (hbig : 2 * m ≤ Fintype.card α) (hne : j ≠ 0 ∨ 2 * m ≠ Fintype.card α)
    {S S' : Finset α} (hS : S.card = m) (hS' : S'.card = m)
    (hint : (S ∩ S').card = m - 1) :
    Relation.ReflTransGen (JohnsonStep m j) S S' := by
  classical
  set A : Finset α := S ∩ S' with hA
  have hAS : A ⊆ S := Finset.inter_subset_left
  have hAS' : A ⊆ S' := Finset.inter_subset_right
  have hAcard : A.card = m - 1 := hint
  have hxcard : (S \ A).card = 1 := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.2 hAS, hS, hAcard]
    omega
  have hycard : (S' \ A).card = 1 := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.2 hAS', hS', hAcard]
    omega
  obtain ⟨x, hxdef⟩ := Finset.card_eq_one.1 hxcard
  obtain ⟨y, hydef⟩ := Finset.card_eq_one.1 hycard
  have hSx : S = A ∪ {x} := by
    rw [← hxdef, Finset.union_sdiff_of_subset hAS]
  have hSy : S' = A ∪ {y} := by
    rw [← hydef, Finset.union_sdiff_of_subset hAS']
  have hxA : x ∉ A := by
    intro hmem
    have : x ∈ S \ A := by rw [hxdef]; exact Finset.mem_singleton_self x
    exact (Finset.mem_sdiff.1 this).2 hmem
  have hyA : y ∉ A := by
    intro hmem
    have : y ∈ S' \ A := by rw [hydef]; exact Finset.mem_singleton_self y
    exact (Finset.mem_sdiff.1 this).2 hmem
  have hxy : x ≠ y := by
    intro h
    have hSS' : S = S' := by rw [hSx, hSy, h]
    have : A = S := by rw [hA, hSS', Finset.inter_self]
    rw [this, hS] at hAcard
    omega
  set E : Finset α := A ∪ {x, y} with hE
  have hEcard : E.card = m + 1 := by
    rw [hE, Finset.card_union_of_disjoint, Finset.card_insert_of_notMem (by simpa using hxy),
      Finset.card_singleton, hAcard]
    · omega
    · rw [Finset.disjoint_right]
      intro a ha
      rcases Finset.mem_insert.1 ha with rfl | ha'
      · exact hxA
      · rw [Finset.mem_singleton] at ha'
        subst ha'
        exact hyA
  have hroom : m - j ≤ (Finset.univ \ E).card := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.2 (Finset.subset_univ E), Finset.card_univ,
      hEcard]
    rcases hne with h | h
    · omega
    · omega
  obtain ⟨B, hBA, hBcard⟩ := Finset.exists_subset_card_eq (show j ≤ A.card by omega)
  obtain ⟨C, hCE, hCcard⟩ := Finset.exists_subset_card_eq hroom
  have hCdisj : ∀ a ∈ C, a ∉ E := by
    intro a ha
    exact (Finset.mem_sdiff.1 (hCE ha)).2
  set T : Finset α := B ∪ C with hT
  have hBCdisj : Disjoint B C := by
    rw [Finset.disjoint_right]
    intro a ha hb
    exact hCdisj a ha (Finset.mem_union_left _ (hBA hb))
  have hTcard : T.card = m := by
    rw [hT, Finset.card_union_of_disjoint hBCdisj, hBcard, hCcard]
    omega
  have hSE : S ⊆ E := by
    rw [hSx, hE]
    exact Finset.union_subset_union (subset_refl A)
      (Finset.singleton_subset_iff.2 (Finset.mem_insert_self x {y}))
  have hS'E : S' ⊆ E := by
    rw [hSy, hE]
    exact Finset.union_subset_union (subset_refl A)
      (Finset.singleton_subset_iff.2 (by simp))
  have hTS : (T ∩ S).card = j := by
    have hset : T ∩ S = B := by
      ext a
      simp only [hT, Finset.mem_inter, Finset.mem_union]
      constructor
      · rintro ⟨hB | hC, haS⟩
        · exact hB
        · exact absurd (hSE haS) (hCdisj a hC)
      · intro hb
        refine ⟨Or.inl hb, ?_⟩
        rw [hSx]
        exact Finset.mem_union_left _ (hBA hb)
    rw [hset, hBcard]
  have hTS' : (T ∩ S').card = j := by
    have hset : T ∩ S' = B := by
      ext a
      simp only [hT, Finset.mem_inter, Finset.mem_union]
      constructor
      · rintro ⟨hB | hC, haS⟩
        · exact hB
        · exact absurd (hS'E haS) (hCdisj a hC)
      · intro hb
        refine ⟨Or.inl hb, ?_⟩
        rw [hSy]
        exact Finset.mem_union_left _ (hBA hb)
    rw [hset, hBcard]
  refine Relation.ReflTransGen.head (b := T) ?_ (Relation.ReflTransGen.single ?_)
  · exact ⟨hS, hTcard, by rw [Finset.inter_comm]; exact hTS⟩
  · exact ⟨hTcard, hS', hTS'⟩


theorem reflTransGen_johnsonStep_aux {m j : ℕ} (hj : j < m) (hbig : 2 * m ≤ Fintype.card α)
    (hne : j ≠ 0 ∨ 2 * m ≠ Fintype.card α) :
    ∀ (k : ℕ) (S T : Finset α), S.card = m → T.card = m → m - (S ∩ T).card ≤ k →
      Relation.ReflTransGen (JohnsonStep m j) S T := by
  classical
  intro k
  induction k with
  | zero =>
      intro S T hS hT hle
      have h1 : (S ∩ T).card ≤ m := by
        rw [← hS]
        exact Finset.card_le_card Finset.inter_subset_left
      have hcard : (S ∩ T).card = m := by omega
      rw [eq_of_card_inter_eq hS hT hcard]
  | succ k ih =>
      intro S T hS hT hle
      by_cases hST : S = T
      · rw [hST]
      obtain ⟨x, hx⟩ : ∃ x, x ∈ S \ T := by
        by_contra hcon
        push Not at hcon
        have hsub : S ⊆ T := by
          intro a ha
          by_contra hb
          exact hcon a (Finset.mem_sdiff.2 ⟨ha, hb⟩)
        exact hST (Finset.eq_of_subset_of_card_le hsub (by omega))
      obtain ⟨y, hy⟩ : ∃ y, y ∈ T \ S := by
        by_contra hcon
        push Not at hcon
        have hsub : T ⊆ S := by
          intro a ha
          by_contra hb
          exact hcon a (Finset.mem_sdiff.2 ⟨ha, hb⟩)
        exact hST (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
      obtain ⟨hxS, hxT⟩ := Finset.mem_sdiff.1 hx
      obtain ⟨hyT, hyS⟩ := Finset.mem_sdiff.1 hy
      set S'' : Finset α := insert y (S.erase x) with hS''
      have hynot : y ∉ S.erase x := fun h => hyS (Finset.mem_of_mem_erase h)
      have hS''card : S''.card = m := by
        rw [hS'', Finset.card_insert_of_notMem hynot, Finset.card_erase_of_mem hxS, hS]
        omega
      have hinterS : S ∩ S'' = S.erase x := by
        ext a
        simp only [hS'', Finset.mem_inter, Finset.mem_insert, Finset.mem_erase]
        constructor
        · rintro ⟨haS, rfl | ha⟩
          · exact absurd haS hyS
          · exact ha
        · rintro ⟨hax, haS⟩
          exact ⟨haS, Or.inr ⟨hax, haS⟩⟩
      have hinterT : S'' ∩ T = insert y (S ∩ T) := by
        ext a
        simp only [hS'', Finset.mem_inter, Finset.mem_insert, Finset.mem_erase]
        constructor
        · rintro ⟨rfl | ⟨hax, haS⟩, haT⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨haS, haT⟩
        · rintro (rfl | ⟨haS, haT⟩)
          · exact ⟨Or.inl rfl, hyT⟩
          · exact ⟨Or.inr ⟨fun h => hxT (h ▸ haT), haS⟩, haT⟩
      have hynotinter : y ∉ S ∩ T := fun h => hyS (Finset.mem_inter.1 h).1
      have hcardT : (S'' ∩ T).card = (S ∩ T).card + 1 := by
        rw [hinterT, Finset.card_insert_of_notMem hynotinter]
      refine Relation.ReflTransGen.trans ?_ (ih S'' T hS''card hT (by omega))
      refine reflTransGen_of_inter_card_pred hj hbig hne hS hS''card ?_
      rw [hinterS, Finset.card_erase_of_mem hxS, hS]

/-- **The fixed-intersection graph on `m`-subsets is connected.** -/
theorem reflTransGen_johnsonStep {m j : ℕ} (hj : j < m) (hbig : 2 * m ≤ Fintype.card α)
    (hne : j ≠ 0 ∨ 2 * m ≠ Fintype.card α) {S T : Finset α}
    (hS : S.card = m) (hT : T.card = m) :
    Relation.ReflTransGen (JohnsonStep m j) S T :=
  reflTransGen_johnsonStep_aux hj hbig hne m S T hS hT (by omega)


omit [Fintype α] in
theorem reflTransGen_subtype_aux {m j : ℕ} :
    ∀ (u v : Finset α), Relation.ReflTransGen (JohnsonStep m j) u v →
      ∀ (hu : u.card = m) (hv : v.card = m),
        Relation.ReflTransGen (fun A B : {s : Finset α // s.card = m} => (A.1 ∩ B.1).card = j)
          ⟨u, hu⟩ ⟨v, hv⟩ := by
  intro u v h
  induction h with
  | refl => intro hu hv; exact Relation.ReflTransGen.refl
  | tail hab hbc ih =>
      rename_i b c
      intro hu hv
      exact Relation.ReflTransGen.tail (ih hu hbc.1) hbc.2.2

/-! ## From a connected swap graph to the full symmetric group -/

/-- Transpositions along a connected relation generate every transposition. -/
theorem swap_mem_of_reflTransGen {X : Type*} [DecidableEq X] {G : Subgroup (Equiv.Perm X)}
    {R : X → X → Prop} (hR : ∀ a b, R a b → Equiv.swap a b ∈ G) {a b : X}
    (h : Relation.ReflTransGen R a b) : Equiv.swap a b ∈ G := by
  induction h with
  | refl =>
      have h1 : Equiv.swap a a = (1 : Equiv.Perm X) := Equiv.swap_self a
      rw [h1]
      exact G.one_mem
  | tail hac hcb ih =>
      rename_i c d
      by_cases had : a = d
      · subst had
        have h1 : Equiv.swap a a = (1 : Equiv.Perm X) := Equiv.swap_self a
        rw [h1]
        exact G.one_mem
      by_cases hac' : a = c
      · subst hac'
        exact hR _ _ hcb
      have hfa : Equiv.swap c d a = a := Equiv.swap_apply_of_ne_of_ne hac' had
      have hfc : Equiv.swap c d c = d := Equiv.swap_apply_left c d
      have hswap : Equiv.swap a d
          = Equiv.swap c d * Equiv.swap a c * (Equiv.swap c d)⁻¹ := by
        rw [← Equiv.swap_apply_apply, hfa, hfc]
      rw [hswap]
      exact G.mul_mem (G.mul_mem (hR _ _ hcb) ih) (G.inv_mem (hR _ _ hcb))

/-- A subgroup containing every transposition is the whole symmetric group. -/
theorem eq_top_of_forall_swap_mem {X : Type*} [DecidableEq X] [Fintype X]
    {G : Subgroup (Equiv.Perm X)} (h : ∀ a b : X, Equiv.swap a b ∈ G) : G = ⊤ := by
  refine le_antisymm le_top ?_
  rw [← Equiv.Perm.closure_isSwap]
  refine (Subgroup.closure_le G).2 ?_
  rintro σ ⟨a, b, hab, rfl⟩
  exact h a b

/-- **A group containing every fixed-intersection transposition of `m`-subsets is the full
symmetric group on those subsets.** -/
theorem eq_top_of_johnsonSwaps {m j : ℕ} (hj : j < m) (hbig : 2 * m ≤ Fintype.card α)
    (hne : j ≠ 0 ∨ 2 * m ≠ Fintype.card α)
    {G : Subgroup (Equiv.Perm {s : Finset α // s.card = m})}
    (hswap : ∀ S T : {s : Finset α // s.card = m},
      (S.1 ∩ T.1).card = j → Equiv.swap S T ∈ G) :
    G = ⊤ := by
  classical
  refine eq_top_of_forall_swap_mem fun S T => ?_
  refine swap_mem_of_reflTransGen
    (R := fun S T : {s : Finset α // s.card = m} => (S.1 ∩ T.1).card = j)
    (fun a b hab => hswap a b hab) ?_
  exact reflTransGen_subtype_aux S.1 T.1
    (reflTransGen_johnsonStep (α := α) hj hbig hne S.2 T.2) S.2 T.2

end GaloisForLFunctions.HTGeometry
