import GaloisForLFunctions.HTGeometry.DifferentialOperatorSubmoduleSplitting

/-!
# Submodules of a finite free module over the operator ring are free

The coordinate splitting of `DifferentialOperatorSubmoduleSplitting` produces generators; this file
upgrades them to a *basis*.  In the induction step the new generator `x` has a nonzero coordinate
`x i₀` while every generator of the previous stage has that coordinate zero, so the coordinate
projection separates the leading coefficient of any relation: the operator ring is a domain, so the
coefficient of `x` in a relation vanishes, and the remaining relation is one among the previous
basis.

Consequently `K[∂;δ]` behaves like a principal ideal domain for finite free modules: every
submodule of `K[∂;δ]^ι` with `ι` finite is free of rank at most `card ι`.

* `exists_basis_card_le` — the induction over the supporting coordinate set;
* `exists_basis_of_submodule` — the statement for a finite index type;
* `free_submodule` — the same, as `Module.Free`.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

namespace DiffOp

noncomputable section

variable {K : Type u} [Field K] [Differential K] {ι : Type*} [DecidableEq ι]

/-- **Submodules supported on a finite coordinate set are free of rank at most its size.** -/
theorem exists_basis_card_le (t : Finset ι) :
    ∀ N : Submodule (DiffOp K) (ι → DiffOp K), N ≤ coordSupport t →
      ∃ (n : ℕ) (v : Fin n → (ι → DiffOp K)), n ≤ t.card ∧
        LinearIndependent (DiffOp K) v ∧
        Submodule.span (DiffOp K) (Set.range v) = N := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      intro N hN
      refine ⟨0, Fin.elim0, by simp, linearIndependent_empty_type, ?_⟩
      rw [Set.range_eq_empty, Submodule.span_empty]
      refine (eq_bot_iff.mpr fun y hy => ?_).symm
      have hzero : y = 0 := by
        funext i
        exact (hN hy) i (by simp)
      rw [hzero]
      exact Submodule.zero_mem _
  | insert i₀ t hi₀ ih =>
      intro N hN
      obtain ⟨x, hxN, hsplit⟩ := exists_coord_generator i₀ N
      set N' : Submodule (DiffOp K) (ι → DiffOp K) := N ⊓ LinearMap.ker (projCoord i₀) with hN'def
      have hN'le : N' ≤ coordSupport t := by
        intro y hy i hi
        by_cases hii₀ : i = i₀
        · subst hii₀
          exact hy.2
        · exact (hN hy.1) i (by
            intro hmem
            rcases Finset.mem_insert.mp hmem with h | h
            · exact hii₀ h
            · exact hi h)
      obtain ⟨n, v, hcard, hindep, hspan⟩ := ih N' hN'le
      have hvcoord : ∀ i : Fin n, v i i₀ = 0 := by
        intro i
        have hmem : v i ∈ N' := by
          rw [← hspan]
          exact Submodule.subset_span ⟨i, rfl⟩
        exact hmem.2
      by_cases hx0 : x i₀ = 0
      · -- the chosen coordinate is identically zero on `N`, so `N = N'`
        have hNle : N ≤ LinearMap.ker (projCoord i₀) := by
          intro y hy
          obtain ⟨r, hcoord, _⟩ := hsplit y hy
          have hrx : (r • x) i₀ = 0 := by
            show r * x i₀ = 0
            rw [hx0, mul_zero]
          have : y i₀ - (r • x) i₀ = 0 := hcoord
          rw [hrx, sub_zero] at this
          exact this
        have hNN' : N' = N := le_antisymm inf_le_left (le_inf le_rfl hNle)
        refine ⟨n, v, ?_, hindep, ?_⟩
        · refine le_trans hcard ?_
          rw [Finset.card_insert_of_notMem hi₀]
          omega
        · rw [hspan, hNN']
      · set w : Fin (n + 1) → (ι → DiffOp K) := Fin.cons x v with hwdef
        have hw0 : w 0 = x := rfl
        have hwsucc : ∀ i : Fin n, w i.succ = v i := fun _ => rfl
        refine ⟨n + 1, w, ?_, ?_, ?_⟩
        · rw [Finset.card_insert_of_notMem hi₀]
          omega
        · rw [Fintype.linearIndependent_iff]
          intro g hg
          have hzero : ∀ i : Fin n, (g i.succ • w i.succ) i₀ = 0 := by
            intro i
            show g i.succ * (w i.succ) i₀ = 0
            rw [hwsucc i, hvcoord i, mul_zero]
          have hsum : (∑ i : Fin n, g i.succ • w i.succ) i₀ = 0 := by
            rw [Finset.sum_apply]
            exact Finset.sum_eq_zero fun i _ => hzero i
          have hsplitSum : ∑ i : Fin (n + 1), g i • w i
              = g 0 • w 0 + ∑ i : Fin n, g i.succ • w i.succ := Fin.sum_univ_succ _
          have hgcoord : (g 0 • w 0) i₀ + (∑ i : Fin n, g i.succ • w i.succ) i₀ = 0 := by
            have h := congrArg (fun y : ι → DiffOp K => y i₀) hg
            rw [hsplitSum] at h
            exact h
          rw [hsum, add_zero] at hgcoord
          have hg0 : g 0 * x i₀ = 0 := by
            rw [← hw0]
            exact hgcoord
          have hg0' : g 0 = 0 := (mul_eq_zero.mp hg0).resolve_right hx0
          have hrest : ∑ i : Fin n, g i.succ • v i = 0 := by
            have h : ∑ i : Fin n, g i.succ • w i.succ = 0 := by
              rw [hsplitSum, hg0', zero_smul, zero_add] at hg
              exact hg
            refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) h
            rw [hwsucc i]
          have hrest' : ∀ i : Fin n, g i.succ = 0 :=
            (Fintype.linearIndependent_iff.mp hindep) (fun i => g i.succ) hrest
          intro j
          refine Fin.cases ?_ ?_ j
          · exact hg0'
          · exact hrest'
        · refine le_antisymm ?_ ?_
          · refine Submodule.span_le.mpr ?_
            rintro z ⟨j, rfl⟩
            refine Fin.cases ?_ ?_ j
            · rw [hw0]
              exact hxN
            · intro i
              rw [hwsucc i]
              have hmem : v i ∈ N' := by
                rw [← hspan]
                exact Submodule.subset_span ⟨i, rfl⟩
              exact hmem.1
          · intro y hy
            obtain ⟨r, hcoord, hmem⟩ := hsplit y hy
            have hy' : y - r • x ∈ N' := ⟨hmem, hcoord⟩
            have hsub : y - r • x ∈ Submodule.span (DiffOp K) (Set.range w) := by
              rw [← hspan] at hy'
              refine Submodule.span_mono ?_ hy'
              rintro z ⟨i, rfl⟩
              exact ⟨i.succ, hwsucc i⟩
            have hxspan : x ∈ Submodule.span (DiffOp K) (Set.range w) :=
              Submodule.subset_span ⟨0, hw0⟩
            have hsum2 := Submodule.add_mem _ (Submodule.smul_mem _ r hxspan) hsub
            rwa [add_sub_cancel] at hsum2

variable [Fintype ι]

/-- **Every submodule of a finite free module over the operator ring is free of rank at most the
number of coordinates.** -/
theorem exists_basis_of_submodule (N : Submodule (DiffOp K) (ι → DiffOp K)) :
    ∃ (n : ℕ) (v : Fin n → (ι → DiffOp K)), n ≤ Fintype.card ι ∧
      LinearIndependent (DiffOp K) v ∧
      Submodule.span (DiffOp K) (Set.range v) = N := by
  have hle : N ≤ coordSupport (Finset.univ : Finset ι) := by
    intro y _ i hi
    exact absurd (Finset.mem_univ i) hi
  obtain ⟨n, v, hcard, hindep, hspan⟩ := exists_basis_card_le (Finset.univ : Finset ι) N hle
  exact ⟨n, v, by simpa [Finset.card_univ] using hcard, hindep, hspan⟩

/-- The same, as freeness. -/
theorem free_submodule (N : Submodule (DiffOp K) (ι → DiffOp K)) :
    Module.Free (DiffOp K) N := by
  classical
  obtain ⟨n, v, _, hindep, hspan⟩ := exists_basis_of_submodule N
  have hmem : ∀ i, v i ∈ N := by
    intro i
    rw [← hspan]
    exact Submodule.subset_span ⟨i, rfl⟩
  set v' : Fin n → N := fun i => ⟨v i, hmem i⟩ with hv'
  have hcomp : (N.subtype : N →ₗ[DiffOp K] (ι → DiffOp K)) ∘ v' = v := rfl
  have hindep' : LinearIndependent (DiffOp K) v' :=
    LinearIndependent.of_comp N.subtype (by rw [hcomp]; exact hindep)
  have hrange : (N.subtype : N → (ι → DiffOp K)) '' (Set.range v') = Set.range v := by
    rw [← Set.range_comp]
    rfl
  have hmapspan : Submodule.map N.subtype (Submodule.span (DiffOp K) (Set.range v'))
      = Submodule.map N.subtype (⊤ : Submodule (DiffOp K) N) := by
    rw [Submodule.map_span, hrange, hspan, Submodule.map_subtype_top]
  have hspan' : Submodule.span (DiffOp K) (Set.range v') = ⊤ :=
    Submodule.map_injective_of_injective N.injective_subtype hmapspan
  exact Module.Free.of_basis (Module.Basis.mk hindep' (le_of_eq hspan'.symm))

end

end DiffOp

end GaloisForLFunctions.HTGeometry
