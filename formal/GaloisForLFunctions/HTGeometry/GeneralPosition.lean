import Mathlib

/-!
# Points in prescribed open sets, in general position

A nonempty open subset of a finite-dimensional real vector space is never covered by finitely many
proper subspaces: removing one closed proper subspace leaves a nonempty open set, and the removal
can be iterated.

Consequently, given a sequence of nonempty open sets one can choose a point in each so that no
chosen point lies in the span of `r` earlier ones, as long as `r` is below the dimension.  A
positive combination of at most `r + 1` such points is then nonzero — the property needed when a
map is built from a partition of unity of order `r + 1` and must avoid the origin.
-/

namespace GaloisForLFunctions.HTGeometry

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **A nonempty open set escapes finitely many proper subspaces.** -/
theorem exists_mem_notMem_of_ne_top {ι : Type*} (V : ι → Submodule ℝ E) (t : Finset ι) :
    (∀ i ∈ t, V i ≠ ⊤) → ∀ {S : Set E}, IsOpen S → S.Nonempty →
      ∃ x ∈ S, ∀ i ∈ t, x ∉ V i := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      intro _ S _ hSne
      obtain ⟨x, hx⟩ := hSne
      exact ⟨x, hx, by simp⟩
  | insert a t ha ih =>
      intro hV S hS hSne
      have hVa : V a ≠ ⊤ := hV a (Finset.mem_insert_self a t)
      have hclosed : IsClosed ((V a : Set E)) := (V a).closed_of_finiteDimensional
      have hS' : IsOpen (S \ (V a : Set E)) := hS.sdiff hclosed
      have hS'ne : (S \ (V a : Set E)).Nonempty := by
        by_contra hcon
        rw [Set.not_nonempty_iff_eq_empty, Set.sdiff_eq_empty] at hcon
        exact hVa ((V a).eq_top_of_nonempty_interior'
          ⟨hSne.choose, mem_interior.mpr ⟨S, hcon, hS, hSne.choose_spec⟩⟩)
      obtain ⟨x, hx, hxt⟩ :=
        ih (fun i hi => hV i (Finset.mem_insert_of_mem hi)) hS' hS'ne
      refine ⟨x, hx.1, ?_⟩
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact hx.2
      · exact hxt i hi

/-- **General position.**  Points chosen in prescribed nonempty open sets so that none lies in the
span of `r` earlier ones. -/
theorem exists_generalPosition {r : ℕ} (hr : r < Module.finrank ℝ E) (S : ℕ → Set E)
    (hSo : ∀ j, IsOpen (S j)) (hSne : ∀ j, (S j).Nonempty) (N : ℕ) :
    ∃ w : ℕ → E, (∀ j < N, w j ∈ S j) ∧
      ∀ j < N, ∀ t : Finset ℕ, (∀ p ∈ t, p < j) → t.card ≤ r →
        w j ∉ Submodule.span ℝ (w '' ↑t) := by
  classical
  induction N with
  | zero =>
      exact ⟨fun _ => (hSne 0).choose, fun j hj => absurd hj (Nat.not_lt_zero j),
        fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  | succ N ih =>
      obtain ⟨w, hwS, hwgp⟩ := ih
      set fam : Finset (Finset ℕ) :=
        (Finset.range N).powerset.filter (fun t => t.card ≤ r) with hfam
      have hne : ∀ t ∈ fam, Submodule.span ℝ ((t.image w : Finset E) : Set E) ≠ ⊤ := by
        intro t ht htop
        have hcard : (t.image w).card ≤ r := by
          have h1 : (t.image w).card ≤ t.card := Finset.card_image_le
          have h2 : t.card ≤ r := (Finset.mem_filter.mp ht).2
          omega
        have hfr : Module.finrank ℝ E ≤ r := by
          have := finrank_span_finset_le_card (R := ℝ) (t.image w)
          rw [Set.finrank] at this
          rw [htop] at this
          rw [finrank_top] at this
          omega
        omega
      obtain ⟨x, hxS, hxV⟩ :=
        exists_mem_notMem_of_ne_top (fun t : Finset ℕ => Submodule.span ℝ ((t.image w : Finset E) : Set E))
          fam hne (hSo N) (hSne N)
      refine ⟨Function.update w N x, ?_, ?_⟩
      · intro j hj
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | rfl
        · rw [Function.update_of_ne (by omega)]
          exact hwS j hj'
        · rw [Function.update_self]
          exact hxS
      · intro j hj t htlt htcard
        have himg : (Function.update w N x) '' ↑t = w '' ↑t := by
          apply Set.image_congr
          intro p hp
          exact Function.update_of_ne (by have := htlt p hp; omega) _ _
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | rfl
        · rw [Function.update_of_ne (by omega), himg]
          exact hwgp j hj' t (fun p hp => htlt p hp) htcard
        · rw [Function.update_self, himg]
          have htmem : t ∈ fam := by
            rw [hfam, Finset.mem_filter, Finset.mem_powerset]
            exact ⟨fun p hp => Finset.mem_range.mpr (htlt p hp), htcard⟩
          have := hxV t htmem
          rwa [Finset.coe_image] at this

omit [FiniteDimensional ℝ E] in
/-- **A positive combination of at most `r + 1` points in general position is nonzero.** -/
theorem sum_smul_ne_zero_of_generalPosition {w : ℕ → E} {r N : ℕ}
    (hgp : ∀ j < N, ∀ t : Finset ℕ, (∀ p ∈ t, p < j) → t.card ≤ r →
      w j ∉ Submodule.span ℝ (w '' ↑t))
    {t : Finset ℕ} (ht : ∀ p ∈ t, p < N) (htc : t.card ≤ r + 1) (htne : t.Nonempty)
    {lam : ℕ → ℝ} (hlam : ∀ p ∈ t, 0 < lam p) :
    ∑ p ∈ t, lam p • w p ≠ 0 := by
  classical
  intro hsum
  set j := t.max' htne with hj
  have hjt : j ∈ t := t.max'_mem htne
  set t' := t.erase j with ht'
  have hlt : ∀ p ∈ t', p < j := by
    intro p hp
    have hpt : p ∈ t := Finset.mem_of_mem_erase hp
    have hpj : p ≠ j := Finset.ne_of_mem_erase hp
    have := t.le_max' p hpt
    omega
  have hcard : t'.card ≤ r := by
    have : t'.card + 1 = t.card := Finset.card_erase_add_one hjt
    omega
  have hsplit : ∑ p ∈ t, lam p • w p = lam j • w j + ∑ p ∈ t', lam p • w p :=
    (Finset.add_sum_erase t (fun p => lam p • w p) hjt).symm
  have hmem : ∑ p ∈ t', lam p • w p ∈ Submodule.span ℝ (w '' ↑t') := by
    refine Submodule.sum_mem _ fun p hp => ?_
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, hp, rfl⟩)
  have hjmem : lam j • w j ∈ Submodule.span ℝ (w '' ↑t') := by
    have : lam j • w j = -(∑ p ∈ t', lam p • w p) := by
      rw [hsplit] at hsum
      linear_combination (norm := module) hsum
    rw [this]
    exact Submodule.neg_mem _ hmem
  have hlamj : lam j ≠ 0 := ne_of_gt (hlam j hjt)
  have : w j ∈ Submodule.span ℝ (w '' ↑t') := by
    have := Submodule.smul_mem (Submodule.span ℝ (w '' ↑t')) (lam j)⁻¹ hjmem
    rwa [smul_smul, inv_mul_cancel₀ hlamj, one_smul] at this
  exact hgp j (ht j hjt) t' hlt hcard this

end GaloisForLFunctions.HTGeometry
