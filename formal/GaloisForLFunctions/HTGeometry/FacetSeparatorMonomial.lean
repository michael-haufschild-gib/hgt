import GaloisForLFunctions.HTGeometry.StanleyReisnerFacetIdeal

/-!
# The separating monomial of a facet

For a facet `A` of an antichain of facets, pick for every other facet `B` a vertex of `A` outside
`B` and multiply the corresponding variables.  The resulting squarefree monomial `q A` is supported
inside `A`, so it is a face monomial and misses the Stanley--Reisner ideal; but multiplying it by
any variable outside `A` produces a nonface, because the extra vertex rules out `A` itself while the
separating vertices rule out every other facet.

This is the combinatorial half of the facet period-escape theorem: `q A` survives the annihilator,
`x_v q A` dies for `v ∉ A`, and `x_v q A` survives for `v ∈ A`.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

variable {α : Type*} [DecidableEq α] [Nonempty α]

/-- A vertex of `A` outside `B`, when one exists. -/
noncomputable def facetSepVertex (A B : Finset α) : α :=
  if h : (A \ B).Nonempty then h.choose else Classical.arbitrary α

theorem facetSepVertex_mem {A B : Finset α} (h : (A \ B).Nonempty) :
    facetSepVertex A B ∈ A ∧ facetSepVertex A B ∉ B := by
  rw [facetSepVertex, dif_pos h]
  have := h.choose_spec
  rw [Finset.mem_sdiff] at this
  exact this

/-- The separating monomial of a facet: one variable for every other facet, chosen inside `A`. -/
noncomputable def facetSepMonomial (facets : Finset (Finset α)) (A : Finset α) :
    MvPolynomial α ℂ :=
  ∏ B ∈ facets.erase A, X (facetSepVertex A B)

omit [DecidableEq α] [Nonempty α] in
/-- A finite product of variables is the monomial of the sum of the single exponents. -/
theorem prod_X_eq_monomial {ι : Type*} (s : Finset ι) (g : ι → α) :
    (∏ i ∈ s, (X (g i) : MvPolynomial α ℂ))
      = monomial (∑ i ∈ s, Finsupp.single (g i) 1) 1 := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, X, monomial_mul, one_mul]

omit [Nonempty α] in
theorem support_prod_X_subset {ι : Type*} (s : Finset ι) (g : ι → α) (T : Finset α)
    (hg : ∀ i ∈ s, g i ∈ T) :
    (∑ i ∈ s, Finsupp.single (g i) (1 : ℕ)).support ⊆ T := by
  classical
  intro v hv
  by_contra hvT
  refine (Finsupp.mem_support_iff.mp hv) ?_
  rw [Finset.sum_apply']
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [Finsupp.single_apply, if_neg]
  intro hgi
  exact hvT (hgi ▸ hg i hi)

theorem facetSepMonomial_support_subset {facets : Finset (Finset α)} {A : Finset α}
    (hsep : ∀ B ∈ facets.erase A, (A \ B).Nonempty) :
    ∀ e ∈ (facetSepMonomial facets A).support, e.support ⊆ A := by
  classical
  intro e he
  rw [facetSepMonomial, prod_X_eq_monomial, support_monomial, if_neg one_ne_zero] at he
  rw [Finset.mem_singleton] at he
  subst he
  exact support_prod_X_subset _ _ A fun B hB => (facetSepVertex_mem (hsep B hB)).1

theorem facetSepMonomial_support_mem {facets : Finset (Finset α)} {A B : Finset α}
    (_hsep : ∀ B ∈ facets.erase A, (A \ B).Nonempty) (hB : B ∈ facets.erase A) :
    ∀ e ∈ (facetSepMonomial facets A).support, facetSepVertex A B ∈ e.support := by
  classical
  intro e he
  rw [facetSepMonomial, prod_X_eq_monomial, support_monomial, if_neg one_ne_zero] at he
  rw [Finset.mem_singleton] at he
  subst he
  refine Finsupp.mem_support_iff.mpr ?_
  rw [Finset.sum_apply']
  have hle : (Finsupp.single (facetSepVertex A B) (1 : ℕ)) (facetSepVertex A B)
      ≤ ∑ C ∈ facets.erase A,
        (Finsupp.single (facetSepVertex A C) (1 : ℕ)) (facetSepVertex A B) :=
    Finset.single_le_sum (f := fun C =>
      (Finsupp.single (facetSepVertex A C) (1 : ℕ)) (facetSepVertex A B))
      (fun i _ => Nat.zero_le _) hB
  have hone : (Finsupp.single (facetSepVertex A B) (1 : ℕ)) (facetSepVertex A B) = 1 := by
    simp
  omega

/-! ## Stanley--Reisner membership -/

omit [Nonempty α] in
theorem sepNonempty_of_antichain {facets : Finset (Finset α)} {A : Finset α} (hA : A ∈ facets)
    (hanti : ∀ B ∈ facets, ∀ C ∈ facets, B ⊆ C → B = C) :
    ∀ B ∈ facets.erase A, (A \ B).Nonempty := by
  intro B hB
  rw [Finset.mem_erase] at hB
  rw [Finset.sdiff_nonempty]
  intro hsub
  exact hB.1 (hanti A hA B hB.2 hsub).symm

/-- The exponent of `X v` times the separating monomial. -/
theorem X_mul_facetSepMonomial_support (facets : Finset (Finset α)) (A : Finset α) (v : α) :
    ∀ e ∈ ((X v : MvPolynomial α ℂ) * facetSepMonomial facets A).support,
      e.support = insert v (∑ B ∈ facets.erase A, Finsupp.single (facetSepVertex A B) (1 : ℕ)).support
        ∧ (∑ B ∈ facets.erase A,
            Finsupp.single (facetSepVertex A B) (1 : ℕ)).support ⊆ e.support := by
  classical
  intro e he
  rw [facetSepMonomial, prod_X_eq_monomial, X, monomial_mul, one_mul, support_monomial,
    if_neg one_ne_zero, Finset.mem_singleton] at he
  subst he
  constructor
  · ext u
    simp only [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_apply,
      Finset.mem_insert]
    constructor
    · intro hu
      by_cases huv : v = u
      · exact Or.inl huv.symm
      · right
        rw [if_neg huv] at hu
        simpa using hu
    · intro hu
      rcases hu with rfl | hu
      · simp
      · have hu' : (∑ B ∈ facets.erase A,
            Finsupp.single (facetSepVertex A B) (1 : ℕ)) u ≠ 0 := hu
        by_cases huv : v = u
        · rw [if_pos huv]
          omega
        · rw [if_neg huv]
          omega
  · intro u hu
    have hu' : (∑ B ∈ facets.erase A,
        Finsupp.single (facetSepVertex A B) (1 : ℕ)) u ≠ 0 := Finsupp.mem_support_iff.mp hu
    refine Finsupp.mem_support_iff.mpr ?_
    simp only [Finsupp.add_apply, Finsupp.single_apply]
    split_ifs <;> omega

theorem facetSepMonomial_notMem_stanleyReisnerIdeal {facets : Finset (Finset α)} {A : Finset α}
    (hA : A ∈ facets) (hsep : ∀ B ∈ facets.erase A, (A \ B).Nonempty) :
    facetSepMonomial facets A ∉ stanleyReisnerIdeal ℂ facets := by
  classical
  rw [mem_stanleyReisnerIdeal_iff]
  intro hcon
  have hne : (facetSepMonomial facets A).support.Nonempty := by
    rw [facetSepMonomial, prod_X_eq_monomial, support_monomial, if_neg one_ne_zero]
    exact ⟨_, Finset.mem_singleton_self _⟩
  obtain ⟨e, he⟩ := hne
  exact hcon e he ⟨A, hA, facetSepMonomial_support_subset hsep e he⟩

theorem X_mul_facetSepMonomial_mem {facets : Finset (Finset α)} {A : Finset α}
    (hsep : ∀ B ∈ facets.erase A, (A \ B).Nonempty) {v : α} (hv : v ∉ A) :
    (X v : MvPolynomial α ℂ) * facetSepMonomial facets A ∈ stanleyReisnerIdeal ℂ facets := by
  classical
  rw [mem_stanleyReisnerIdeal_iff]
  intro e he
  rintro ⟨C, hC, hsub⟩
  obtain ⟨hins, hsupsub⟩ := X_mul_facetSepMonomial_support facets A v e he
  have hvC : v ∈ C := hsub (by rw [hins]; exact Finset.mem_insert_self _ _)
  have hCA : C ≠ A := by
    intro hCA
    exact hv (hCA ▸ hvC)
  have hCerase : C ∈ facets.erase A := Finset.mem_erase.mpr ⟨hCA, hC⟩
  have hmem : facetSepVertex A C ∈ e.support := by
    refine hsupsub ?_
    have hmono := facetSepMonomial_support_mem hsep hCerase
    have he' : ∀ f ∈ (facetSepMonomial facets A).support, facetSepVertex A C ∈ f.support := hmono
    rw [facetSepMonomial, prod_X_eq_monomial, support_monomial, if_neg one_ne_zero] at he'
    exact he' _ (Finset.mem_singleton_self _)
  exact (facetSepVertex_mem (hsep C hCerase)).2 (hsub hmem)

theorem X_mul_facetSepMonomial_notMem {facets : Finset (Finset α)} {A : Finset α}
    (hA : A ∈ facets) (hsep : ∀ B ∈ facets.erase A, (A \ B).Nonempty) {v : α} (hv : v ∈ A) :
    (X v : MvPolynomial α ℂ) * facetSepMonomial facets A ∉ stanleyReisnerIdeal ℂ facets := by
  classical
  rw [mem_stanleyReisnerIdeal_iff]
  intro hcon
  have hne : ((X v : MvPolynomial α ℂ) * facetSepMonomial facets A).support.Nonempty := by
    rw [facetSepMonomial, prod_X_eq_monomial, X, monomial_mul, one_mul, support_monomial,
      if_neg one_ne_zero]
    exact ⟨_, Finset.mem_singleton_self _⟩
  obtain ⟨e, he⟩ := hne
  obtain ⟨hins, -⟩ := X_mul_facetSepMonomial_support facets A v e he
  refine hcon e he ⟨A, hA, ?_⟩
  rw [hins]
  refine Finset.insert_subset hv ?_
  have hsub := facetSepMonomial_support_subset hsep
  have hmem : (∑ B ∈ facets.erase A, Finsupp.single (facetSepVertex A B) (1 : ℕ))
      ∈ (facetSepMonomial facets A).support := by
    rw [facetSepMonomial, prod_X_eq_monomial, support_monomial, if_neg one_ne_zero]
    exact Finset.mem_singleton_self _
  exact hsub _ hmem

end GaloisForLFunctions.HTGeometry
