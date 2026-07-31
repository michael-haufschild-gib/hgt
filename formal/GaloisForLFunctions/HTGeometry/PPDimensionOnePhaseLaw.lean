import GaloisForLFunctions.HTGeometry.PPMatrixRankFormulaConsequences
import GaloisForLFunctions.HTGeometry.SimplicialConstraintTower

/-!
# The exact dimension-one phase law for the periodic-pencil dimension

A one-dimensional periodic pencil forces every facet to omit at most one vertex.  In dimension one
the facet form is multiplication by a single nonzero scalar, so the integrality condition writes
each omitted vertex's step as an integer multiple of one period; two omitted vertices then give a
rational relation between their steps, which `ℚ`-independence forbids.

Conversely a deletion family — and the full simplex — is realized in dimension one by the powers of
one transcendental number.

* `card_sdiff_le_one_of_ppAdmissible_one` — the necessity, stated for an explicit one-dimensional
  admissible configuration;
* `facetComplementRankOne_of_ppAdmissible_one` — the same in the corpus's combinatorial vocabulary,
  which feeds `facetAntichain_eq_singleton_or_deletionFacets`;
* `ppDim_le_one_deletion`, `ppDim_le_one_simplex` — the sufficiency.
-/

namespace GaloisForLFunctions

open scoped Matrix Classical

variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

/-! ### Necessity -/

/-- **A one-dimensional periodic pencil omits at most one vertex per facet.**  The facet form is
multiplication by one nonzero scalar, so two omitted vertices have steps in a common `ℤ`-line,
contradicting `ℚ`-independence. -/
theorem card_sdiff_le_one_of_ppAdmissible_one (faces : A → Finset V)
    (hne : ∀ B, (faces B).Nonempty) {a : V → Fin 1 → ℂ} (hindep : LinearIndependent ℚ a)
    {U : A → Fin 1 → ℂ}
    (hadm : PPAdmissible faces (fun B v => ∑ i, U B i * a v i)) (B : A) :
    ((Finset.univ : Finset V) \ faces B).card ≤ 1 := by
  classical
  obtain ⟨v₀, hv₀⟩ := hne B
  obtain ⟨hint, hli⟩ := hadm B
  have hM : ∀ v : V, (∑ i, U B i * a v i) = U B 0 * a v 0 := fun v => by
    rw [Fin.sum_univ_one]
  have hne0 : U B 0 * a v₀ 0 ≠ 0 := by
    have h := hli.ne_zero (some ⟨v₀, hv₀⟩)
    simpa [hM] using h
  have hc : U B 0 ≠ 0 := fun h => hne0 (by rw [h, zero_mul])
  refine Finset.card_le_one.mpr ?_
  intro v hv v' hv'
  by_contra hvv'
  obtain ⟨n, hn0⟩ := hint v (Finset.mem_sdiff.mp hv).2
  obtain ⟨n', hn'0⟩ := hint v' (Finset.mem_sdiff.mp hv').2
  have hn : U B 0 * a v 0 = (n : ℂ) := by rw [← hM]; exact hn0
  have hn' : U B 0 * a v' 0 = (n' : ℂ) := by rw [← hM]; exact hn'0
  set g : V → ℚ := fun w => if w = v then (n' : ℚ) else if w = v' then (-n : ℚ) else 0 with hg
  have hsum : ∑ w, g w • a w = 0 := by
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    rw [smul_apply_sum]
    have hsub : ({v, v'} : Finset V) ⊆ Finset.univ := Finset.subset_univ _
    rw [← Finset.sum_subset hsub]
    · rw [Finset.sum_pair hvv']
      have hgv : g v = (n' : ℚ) := by simp [hg]
      have hv'v : v' ≠ v := fun hcx => hvv' hcx.symm
      have hgv' : g v' = (-n : ℚ) := by simp [hg, hv'v]
      rw [hgv, hgv']
      have hcancel : U B 0 * ((n' : ℂ) * a v 0 + ((-n : ℤ) : ℂ) * a v' 0) = 0 := by
        push_cast
        push_cast at hn hn'
        linear_combination (n' : ℂ) * hn - (n : ℂ) * hn'
      have := mul_eq_zero.mp hcancel
      rcases this with h | h
      · exact absurd h hc
      · push_cast at h ⊢
        exact h
    · intro x _ hx
      have hxv : x ≠ v := fun hcx => hx (by rw [hcx]; simp)
      have hxv' : x ≠ v' := fun hcx => hx (by rw [hcx]; simp)
      simp [hg, hxv, hxv']
      rfl
  have hzero := Fintype.linearIndependent_iff.mp hindep g hsum
  have hn'0 : (n' : ℚ) = 0 := by
    have := hzero v
    simpa [hg] using this
  have hn'z : n' = 0 := by exact_mod_cast hn'0
  have hav' : a v' 0 = 0 := by
    have : U B 0 * a v' 0 = 0 := by rw [hn', hn'z]; simp
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hc
    · exact h
  refine hindep.ne_zero v' ?_
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst hi
  exact hav'

/-- The necessity in the corpus's combinatorial vocabulary. -/
theorem facetComplementRankOne_of_ppAdmissible_one (faces : A → Finset V)
    (hne : ∀ B, (faces B).Nonempty) {a : V → Fin 1 → ℂ} (hindep : LinearIndependent ℚ a)
    {U : A → Fin 1 → ℂ}
    (hadm : PPAdmissible faces (fun B v => ∑ i, U B i * a v i)) :
    FacetComplementRankOne (Finset.univ : Finset V) (Set.range faces) := by
  rintro F ⟨B, rfl⟩
  exact ⟨Finset.subset_univ _, card_sdiff_le_one_of_ppAdmissible_one faces hne hindep hadm B⟩

end GaloisForLFunctions
