import GaloisForLFunctions.HTGeometry.MvPolynomialInfiniteVanishing
import GaloisForLFunctions.HTGeometry.MonomialFrequencySeparation

/-!
# Symmetrised monomials of distinct exponent multisets are independent

Expanding a differential relation over the tuples that realise one multiset of frequencies produces,
for each monomial in the jets, the symmetrisation of a monomial in the frequency variables.  Two
monomials in the jets give the same symmetrisation exactly when their exponent multisets agree.

So the symmetrised monomials of pairwise distinct exponent multisets are linearly independent: the
coefficient of one sorted monomial sees only its own symmetrisation, with a positive multiplicity.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The symmetrisation of a monomial with exponents `k`. -/
def permSum {m : ℕ} (k : Fin m → ℕ) : MvPolynomial (Fin m) ℂ :=
  ∑ σ : Equiv.Perm (Fin m),
    MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm fun j => k (σ j)) 1

theorem coeff_permSum {m : ℕ} (k e : Fin m → ℕ) :
    MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm e) (permSum k)
      = (({σ : Equiv.Perm (Fin m) | (fun j => k (σ j)) = e} : Finset (Equiv.Perm (Fin m))).card :
        ℂ) := by
  classical
  rw [permSum, MvPolynomial.coeff_sum]
  rw [Finset.sum_congr rfl (fun σ _ => MvPolynomial.coeff_monomial _ _ _)]
  have hcond : ∀ σ : Equiv.Perm (Fin m),
      ((Finsupp.equivFunOnFinite.symm fun j => k (σ j))
          = Finsupp.equivFunOnFinite.symm e)
        ↔ ((fun j => k (σ j)) = e) := fun σ => Equiv.apply_eq_iff_eq _
  simp only [hcond]
  rw [Finset.sum_boole]

/-- Reindexing a tuple by a permutation does not change the multiset it uses. -/
theorem tupleCount_comp_perm {β : Type*} [Fintype β] [DecidableEq β] (k : β → ℕ)
    (σ : Equiv.Perm β) :
    tupleCount (fun j => k (σ j)) = tupleCount k := by
  classical
  rw [tupleCount, tupleCount]
  exact Fintype.sum_equiv σ _ _ fun j => rfl

/-- **Symmetrised monomials of pairwise distinct multisets are linearly independent.** -/
theorem eq_zero_of_permSum_combination {m : ℕ} {K : Finset (Fin m → ℕ)} (c : (Fin m → ℕ) → ℂ)
    (hdistinct : ∀ k ∈ K, ∀ k' ∈ K, tupleCount k = tupleCount k' → k = k')
    (h : ∑ k ∈ K, c k • permSum k = 0) : ∀ k ∈ K, c k = 0 := by
  classical
  intro k₀ hk₀
  have hcoeff := congrArg
    (MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm k₀)) h
  rw [MvPolynomial.coeff_sum, MvPolynomial.coeff_zero] at hcoeff
  have hterm : ∀ k ∈ K, MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm k₀) (c k • permSum k)
      = if k = k₀ then
          c k₀ * (({σ : Equiv.Perm (Fin m) | (fun j => k₀ (σ j)) = k₀} :
            Finset (Equiv.Perm (Fin m))).card : ℂ)
        else 0 := by
    intro k hk
    rw [MvPolynomial.coeff_smul, smul_eq_mul, coeff_permSum]
    by_cases hkk : k = k₀
    · subst hkk
      rw [if_pos rfl]
    · rw [if_neg hkk]
      have hempty : ({σ : Equiv.Perm (Fin m) | (fun j => k (σ j)) = k₀} :
          Finset (Equiv.Perm (Fin m))) = ∅ := by
        refine Finset.eq_empty_of_forall_notMem fun σ hσ => ?_
        rw [Finset.mem_filter] at hσ
        have hcount : tupleCount (fun j => k (σ j)) = tupleCount k₀ := by
          rw [hσ.2]
        rw [tupleCount_comp_perm] at hcount
        exact hkk (hdistinct k hk k₀ hk₀ hcount)
      rw [hempty]
      simp
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' K k₀, if_pos hk₀] at hcoeff
  have hpos : (0 : ℕ) < ({σ : Equiv.Perm (Fin m) | (fun j => k₀ (σ j)) = k₀} :
      Finset (Equiv.Perm (Fin m))).card := by
    refine Finset.card_pos.mpr ⟨Equiv.refl _, ?_⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, rfl⟩
  have hne : (({σ : Equiv.Perm (Fin m) | (fun j => k₀ (σ j)) = k₀} :
      Finset (Equiv.Perm (Fin m))).card : ℂ) ≠ 0 := by
    exact_mod_cast Nat.cast_ne_zero.mpr hpos.ne'
  exact (mul_eq_zero.mp hcoeff).resolve_right hne

/-! ## Fibres of the multiset map -/

theorem tupleCount_apply {ι : Type*} [DecidableEq ι] {m : ℕ} (n : Fin m → ι) (x : ι) :
    tupleCount n x = ({j : Fin m | n j = x} : Finset (Fin m)).card := by
  classical
  rw [tupleCount, Finset.sum_apply']
  simp only [Finsupp.single_apply]
  rw [Finset.sum_boole]
  rfl

/-- **Tuples with the same multiset as an injective tuple are its permutations.** -/
theorem exists_perm_of_tupleCount_eq {ι : Type*} [DecidableEq ι] {m : ℕ} {i n : Fin m → ι}
    (hi : Function.Injective i) (h : tupleCount n = tupleCount i) :
    ∃ σ : Equiv.Perm (Fin m), n = fun j => i (σ j) := by
  classical
  have hcard : ∀ x : ι, ({j : Fin m | n j = x} : Finset (Fin m)).card
      = ({j : Fin m | i j = x} : Finset (Fin m)).card := by
    intro x
    rw [← tupleCount_apply, ← tupleCount_apply, h]
  have hiFilter : ∀ l : Fin m, ({j : Fin m | i j = i l} : Finset (Fin m)) = {l} := by
    intro l
    refine Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩
    · rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, rfl⟩
    · intro j hj
      rw [Finset.mem_filter] at hj
      exact hi hj.2
  have hmem : ∀ j : Fin m, ∃ l : Fin m, i l = n j := by
    intro j
    have hpos : 0 < ({j' : Fin m | n j' = n j} : Finset (Fin m)).card := by
      refine Finset.card_pos.mpr ⟨j, ?_⟩
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, rfl⟩
    rw [hcard (n j)] at hpos
    obtain ⟨l, hl⟩ := Finset.card_pos.mp hpos
    rw [Finset.mem_filter] at hl
    exact ⟨l, hl.2⟩
  choose g hg using hmem
  have hninj : Function.Injective n := by
    intro j j' hjj
    have hone : ({j'' : Fin m | n j'' = n j} : Finset (Fin m)).card = 1 := by
      rw [hcard (n j), ← hg j, hiFilter (g j), Finset.card_singleton]
    have hsub : ({j, j'} : Finset (Fin m)) ⊆ ({j'' : Fin m | n j'' = n j} : Finset (Fin m)) := by
      intro b hb
      rw [Finset.mem_insert, Finset.mem_singleton] at hb
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rcases hb with rfl | rfl
      · rfl
      · exact hjj.symm
    have hle := Finset.card_le_card hsub
    rw [hone] at hle
    by_contra hne
    rw [Finset.card_pair hne] at hle
    omega
  have hginj : Function.Injective g := by
    intro j j' hjj
    refine hninj ?_
    rw [← hg j, ← hg j', hjj]
  have hgbij : Function.Bijective g := (Finite.injective_iff_bijective).mp hginj
  refine ⟨Equiv.ofBijective g hgbij, ?_⟩
  funext j
  exact (hg j).symm

end

end GaloisForLFunctions.HTGeometry
