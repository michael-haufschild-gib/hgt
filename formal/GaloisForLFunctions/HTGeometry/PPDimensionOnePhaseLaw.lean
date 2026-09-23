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

omit [Fintype A] [DecidableEq A] in
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

omit [Fintype A] [DecidableEq A] in
/-- The necessity in the corpus's combinatorial vocabulary. -/
theorem facetComplementRankOne_of_ppAdmissible_one (faces : A → Finset V)
    (hne : ∀ B, (faces B).Nonempty) {a : V → Fin 1 → ℂ} (hindep : LinearIndependent ℚ a)
    {U : A → Fin 1 → ℂ}
    (hadm : PPAdmissible faces (fun B v => ∑ i, U B i * a v i)) :
    FacetComplementRankOne (Finset.univ : Finset V) (Set.range faces) := by
  rintro F ⟨B, rfl⟩
  exact ⟨Finset.subset_univ _, card_sdiff_le_one_of_ppAdmissible_one faces hne hindep hadm B⟩

/-! ### Sufficiency -/

/-- A positive injective exponent labelling of a finite vertex type. -/
noncomputable def vertexExponent (v : V) : ℕ := (Fintype.equivFin V v : ℕ) + 1

omit [DecidableEq V] in
theorem vertexExponent_injective : Function.Injective (vertexExponent (V := V)) := by
  intro x y hxy
  have h : (Fintype.equivFin V x : ℕ) = (Fintype.equivFin V y : ℕ) := by
    rw [vertexExponent, vertexExponent] at hxy
    omega
  exact (Fintype.equivFin V).injective (Fin.ext h)

omit [DecidableEq V] in
theorem vertexExponent_ne_zero (v : V) : vertexExponent v ≠ 0 := by
  rw [vertexExponent]
  omega

/-- The one-dimensional translation configuration built from a transcendental number. -/
noncomputable def onePencilVector (τ : ℂ) (v : V) : Fin 1 → ℂ := fun _ => τ ^ vertexExponent v

omit [DecidableEq V] [Fintype A] [DecidableEq A] in
theorem onePencilVector_linearIndependent {τ : ℂ} (hτ : Transcendental ℚ τ) :
    LinearIndependent ℚ (onePencilVector (V := V) τ) := by
  have hbase : LinearIndependent ℚ fun v : V => τ ^ vertexExponent v :=
    linearIndependent_of_mul_eq_transcendental_powers hτ vertexExponent
      vertexExponent_injective _ fun _ => one_mul _
  have hmap : LinearIndependent ℚ fun v : V =>
      (LinearEquiv.funUnique (Fin 1) ℚ ℂ).symm (τ ^ vertexExponent v) :=
    hbase.map' (LinearEquiv.funUnique (Fin 1) ℚ ℂ).symm.toLinearMap (LinearEquiv.ker _)
  exact hmap

omit [Fintype A] [DecidableEq A] in
/-- **The deletion family is realized in dimension one.** -/
theorem ppDim_le_one_deletion (faces : A → Finset V) (u : A → V)
    (hface : ∀ B, faces B = (Finset.univ : Finset V).erase (u B)) : ppDim faces ≤ 1 := by
  classical
  obtain ⟨τ, hτ⟩ := exists_transcendental_complex
  have hτ0 : τ ≠ 0 := fun h => hτ (by rw [h]; exact isAlgebraic_zero)
  refine Nat.sInf_le ⟨onePencilVector τ, onePencilVector_linearIndependent hτ,
    fun B _ => (τ ^ vertexExponent (u B))⁻¹, fun B => ⟨?_, ?_⟩⟩
  · intro v hv
    refine ⟨1, ?_⟩
    have hvu : v = u B := by
      rw [hface B] at hv
      by_contra hcon
      exact hv (Finset.mem_erase.mpr ⟨hcon, Finset.mem_univ v⟩)
    show ∑ i : Fin 1, (τ ^ vertexExponent (u B))⁻¹ * onePencilVector τ v i = ((1 : ℤ) : ℂ)
    rw [Fin.sum_univ_one]
    show (τ ^ vertexExponent (u B))⁻¹ * τ ^ vertexExponent v = ((1 : ℤ) : ℂ)
    rw [hvu, inv_mul_cancel₀ (pow_ne_zero _ hτ0)]
    norm_num
  · refine linearIndependent_of_mul_eq_transcendental_powers (c := τ ^ vertexExponent (u B)) hτ
      (fun i : Option (faces B) => i.elim (vertexExponent (u B)) fun v => vertexExponent (v : V))
      ?_ _ ?_
    · intro x y hxy
      rcases x with _ | ⟨x, hx⟩ <;> rcases y with _ | ⟨y, hy⟩
      · rfl
      · rw [hface B] at hy
        exact absurd (vertexExponent_injective hxy.symm)
          (Finset.ne_of_mem_erase hy)
      · rw [hface B] at hx
        exact absurd (vertexExponent_injective hxy) (Finset.ne_of_mem_erase hx)
      · have : x = y := vertexExponent_injective hxy
        subst this
        rfl
    · intro i
      rcases i with _ | ⟨v, hv⟩
      · show τ ^ vertexExponent (u B) * 1 = τ ^ vertexExponent (u B)
        rw [mul_one]
      · show τ ^ vertexExponent (u B)
          * ∑ j : Fin 1, (τ ^ vertexExponent (u B))⁻¹ * onePencilVector τ (v : V) j
          = τ ^ vertexExponent (v : V)
        rw [Fin.sum_univ_one]
        show τ ^ vertexExponent (u B)
          * ((τ ^ vertexExponent (u B))⁻¹ * τ ^ vertexExponent (v : V)) = _
        rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hτ0), one_mul]

omit [Fintype A] [DecidableEq V] [DecidableEq A] in
/-- **The full simplex is realized in dimension one.** -/
theorem ppDim_le_one_simplex (faces : A → Finset V)
    (hface : ∀ B, faces B = (Finset.univ : Finset V)) : ppDim faces ≤ 1 := by
  classical
  obtain ⟨τ, hτ⟩ := exists_transcendental_complex
  refine Nat.sInf_le ⟨onePencilVector τ, onePencilVector_linearIndependent hτ,
    fun _ _ => 1, fun B => ⟨?_, ?_⟩⟩
  · intro v hv
    rw [hface B] at hv
    exact absurd (Finset.mem_univ v) hv
  · refine linearIndependent_of_mul_eq_transcendental_powers (c := 1) hτ
      (fun i : Option (faces B) => i.elim 0 fun v => vertexExponent (v : V)) ?_ _ ?_
    · intro x y hxy
      rcases x with _ | ⟨x, hx⟩ <;> rcases y with _ | ⟨y, hy⟩
      · rfl
      · exact absurd hxy.symm (vertexExponent_ne_zero y)
      · exact absurd hxy (vertexExponent_ne_zero x)
      · have : x = y := vertexExponent_injective hxy
        subst this
        rfl
    · intro i
      rcases i with _ | ⟨v, hv⟩
      · show (1 : ℂ) * 1 = τ ^ (0 : ℕ)
        rw [mul_one, pow_zero]
      · show (1 : ℂ) * ∑ j : Fin 1, 1 * onePencilVector τ (v : V) j = τ ^ vertexExponent (v : V)
        rw [Fin.sum_univ_one]
        show (1 : ℂ) * (1 * τ ^ vertexExponent (v : V)) = _
        rw [one_mul, one_mul]

end GaloisForLFunctions
