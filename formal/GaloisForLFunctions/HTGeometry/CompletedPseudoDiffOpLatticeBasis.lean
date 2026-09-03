import GaloisForLFunctions.HTGeometry.CompletedPseudoDiffOpLatticeSplitting

/-!
# Bases of completed pseudodifferential valuation lattices

Coordinate splitting and finite-generation of each remainder give an induction on coordinate
support.  Every finitely generated valuation-ring submodule of a finite-dimensional completed
skew vector space therefore has a basis with no more vectors than ambient coordinates.

This is the free-module half of arbitrary-lattice Cartan reduction.  The full-span condition of a
lattice will force equality of ranks downstream.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

namespace DiffOp

noncomputable section

variable {K : Type u} [Field K] [Differential K]
variable {ι : Type*} [DecidableEq ι]

/-- Vectors supported on a finite set of completed-skew coordinates. -/
def completedPseudoDiffOpCoordSupport (t : Finset ι) :
    Submodule (CompletedPseudoDiffOpInteger (K := K)) (ι → CompletedPseudoDiffOp K) where
  carrier := {y | ∀ i ∉ t, y i = 0}
  add_mem' := by
    intro y z hy hz i hi
    show y i + z i = 0
    rw [hy i hi, hz i hi, add_zero]
  zero_mem' := by
    intro i _
    rfl
  smul_mem' := by
    intro r y hy i hi
    show (r : CompletedPseudoDiffOp K) * y i = 0
    rw [hy i hi, mul_zero]

omit [DecidableEq ι] in
theorem mem_completedPseudoDiffOpCoordSupport
    {t : Finset ι} {y : ι → CompletedPseudoDiffOp K} :
    y ∈ completedPseudoDiffOpCoordSupport (K := K) t ↔ ∀ i ∉ t, y i = 0 := Iff.rfl

/-- Finitely generated completed-skew submodules supported on `t` are free of rank at most
`t.card`. -/
theorem exists_completedPseudoDiffOp_basis_card_le (t : Finset ι) :
    ∀ N : Submodule (CompletedPseudoDiffOpInteger (K := K))
        (ι → CompletedPseudoDiffOp K),
      N.FG → N ≤ completedPseudoDiffOpCoordSupport (K := K) t →
      ∃ (n : ℕ) (v : Fin n → (ι → CompletedPseudoDiffOp K)), n ≤ t.card ∧
        LinearIndependent (CompletedPseudoDiffOpInteger (K := K)) v ∧
        Submodule.span (CompletedPseudoDiffOpInteger (K := K)) (Set.range v) = N := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      intro N hN hle
      refine ⟨0, Fin.elim0, by simp, linearIndependent_empty_type, ?_⟩
      rw [Set.range_eq_empty, Submodule.span_empty]
      refine (eq_bot_iff.mpr fun y hy => ?_).symm
      have hzero : y = 0 := by
        funext i
        exact (hle hy) i (by simp)
      rw [hzero]
      exact Submodule.zero_mem _
  | insert i₀ t hi₀ ih =>
      intro N hN hle
      obtain ⟨x, hxN, hsplit⟩ :=
        exists_completedPseudoDiffOp_coord_generator i₀ N hN
      set N' : Submodule (CompletedPseudoDiffOpInteger (K := K))
          (ι → CompletedPseudoDiffOp K) :=
        N ⊓ LinearMap.ker (completedPseudoDiffOpProjCoord (K := K) i₀) with hN'def
      have hN'fg : N'.FG := by
        rw [hN'def]
        exact fg_inf_ker_completedPseudoDiffOpProjCoord i₀ N hN
      have hN'le : N' ≤ completedPseudoDiffOpCoordSupport (K := K) t := by
        intro y hy i hi
        by_cases hii₀ : i = i₀
        · subst hii₀
          exact hy.2
        · exact (hle hy.1) i (by
            intro hmem
            rcases Finset.mem_insert.mp hmem with h | h
            · exact hii₀ h
            · exact hi h)
      obtain ⟨n, v, hcard, hindep, hspan⟩ := ih N' hN'fg hN'le
      have hvcoord : ∀ i : Fin n, v i i₀ = 0 := by
        intro i
        have hmem : v i ∈ N' := by
          rw [← hspan]
          exact Submodule.subset_span ⟨i, rfl⟩
        exact hmem.2
      by_cases hx0 : x i₀ = 0
      · have hNle : N ≤ LinearMap.ker (completedPseudoDiffOpProjCoord (K := K) i₀) := by
          intro y hy
          obtain ⟨r, hcoord, -⟩ := hsplit y hy
          have hrx : (r • x) i₀ = 0 := by
            change (r : CompletedPseudoDiffOp K) * x i₀ = 0
            rw [hx0, mul_zero]
          change y i₀ - (r • x) i₀ = 0 at hcoord
          rw [hrx, sub_zero] at hcoord
          exact hcoord
        have hNN' : N' = N := le_antisymm inf_le_left (le_inf le_rfl hNle)
        refine ⟨n, v, ?_, hindep, ?_⟩
        · refine le_trans hcard ?_
          rw [Finset.card_insert_of_notMem hi₀]
          omega
        · rw [hspan, hNN']
      · set w : Fin (n + 1) → (ι → CompletedPseudoDiffOp K) := Fin.cons x v with hwdef
        have hw0 : w 0 = x := rfl
        have hwsucc : ∀ i : Fin n, w i.succ = v i := fun _ => rfl
        refine ⟨n + 1, w, ?_, ?_, ?_⟩
        · rw [Finset.card_insert_of_notMem hi₀]
          omega
        · rw [Fintype.linearIndependent_iff]
          intro g hg
          have hzero : ∀ i : Fin n, (g i.succ • w i.succ) i₀ = 0 := by
            intro i
            show (g i.succ : CompletedPseudoDiffOp K) * (w i.succ) i₀ = 0
            rw [hwsucc i, hvcoord i, mul_zero]
          have hsum : (∑ i : Fin n, g i.succ • w i.succ) i₀ = 0 := by
            rw [Finset.sum_apply]
            exact Finset.sum_eq_zero fun i _ => hzero i
          have hsplitSum : ∑ i : Fin (n + 1), g i • w i =
              g 0 • w 0 + ∑ i : Fin n, g i.succ • w i.succ := Fin.sum_univ_succ _
          have hgcoord : (g 0 • w 0) i₀ +
              (∑ i : Fin n, g i.succ • w i.succ) i₀ = 0 := by
            have h := congrArg (fun y : ι → CompletedPseudoDiffOp K => y i₀) hg
            rw [hsplitSum] at h
            exact h
          rw [hsum, add_zero] at hgcoord
          have hg0D : (g 0 : CompletedPseudoDiffOp K) * x i₀ = 0 := by
            rw [← hw0]
            exact hgcoord
          have hg0D' : (g 0 : CompletedPseudoDiffOp K) = 0 :=
            (mul_eq_zero.mp hg0D).resolve_right hx0
          have hg0 : g 0 = 0 := Subtype.ext hg0D'
          have hrest : ∑ i : Fin n, g i.succ • v i = 0 := by
            have h : ∑ i : Fin n, g i.succ • w i.succ = 0 := by
              rw [hsplitSum, hg0, zero_smul, zero_add] at hg
              exact hg
            refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) h
            rw [hwsucc i]
          have hrest' : ∀ i : Fin n, g i.succ = 0 :=
            (Fintype.linearIndependent_iff.mp hindep) (fun i => g i.succ) hrest
          intro j
          refine Fin.cases hg0 hrest' j
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
            have hsub : y - r • x ∈
                Submodule.span (CompletedPseudoDiffOpInteger (K := K)) (Set.range w) := by
              rw [← hspan] at hy'
              refine Submodule.span_mono ?_ hy'
              rintro z ⟨i, rfl⟩
              exact ⟨i.succ, hwsucc i⟩
            have hxspan : x ∈
                Submodule.span (CompletedPseudoDiffOpInteger (K := K)) (Set.range w) :=
              Submodule.subset_span ⟨0, hw0⟩
            have hsum2 := Submodule.add_mem _ (Submodule.smul_mem _ r hxspan) hsub
            rwa [add_sub_cancel] at hsum2

variable [Fintype ι]

/-- Every finitely generated completed-skew valuation submodule of a finite coordinate space is
free of rank at most ambient rank. -/
theorem exists_completedPseudoDiffOp_basis_of_fg_submodule
    (N : Submodule (CompletedPseudoDiffOpInteger (K := K))
      (ι → CompletedPseudoDiffOp K)) (hN : N.FG) :
    ∃ (n : ℕ) (v : Fin n → (ι → CompletedPseudoDiffOp K)), n ≤ Fintype.card ι ∧
      LinearIndependent (CompletedPseudoDiffOpInteger (K := K)) v ∧
      Submodule.span (CompletedPseudoDiffOpInteger (K := K)) (Set.range v) = N := by
  have hle : N ≤ completedPseudoDiffOpCoordSupport (K := K) (Finset.univ : Finset ι) := by
    intro y _ i hi
    exact absurd (Finset.mem_univ i) hi
  obtain ⟨n, v, hcard, hindep, hspan⟩ :=
    exists_completedPseudoDiffOp_basis_card_le (Finset.univ : Finset ι) N hN hle
  exact ⟨n, v, by simpa [Finset.card_univ] using hcard, hindep, hspan⟩

/-- A finite family independent over the completed valuation ring remains independent after
extension to the completed skew field.  A coefficient of least valuation clears all denominators
in a putative skew-field relation. -/
theorem linearIndependent_completedPseudoDiffOp_of_integer
    {n : ℕ} {v : Fin n → (ι → CompletedPseudoDiffOp K)}
    (hv : LinearIndependent (CompletedPseudoDiffOpInteger (K := K)) v) :
    LinearIndependent (CompletedPseudoDiffOp K) v := by
  classical
  rw [Fintype.linearIndependent_iff] at hv ⊢
  intro g hg
  by_cases hzero : ∀ i, g i = 0
  · exact hzero
  · push Not at hzero
    let t : Finset (Fin n) := Finset.univ.filter (fun i => g i ≠ 0)
    have ht : t.Nonempty := by
      obtain ⟨i, hi⟩ := hzero
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
    obtain ⟨p, hpt, hmin⟩ := Finset.exists_min_image t
      (fun i => completedPseudoDiffOpAddValue (g i)) ht
    have hp0 : g p ≠ 0 := (Finset.mem_filter.mp hpt).2
    have hle : ∀ i, completedPseudoDiffOpAddValue (g p) ≤
        completedPseudoDiffOpAddValue (g i) := by
      intro i
      by_cases hi : g i = 0
      · rw [hi]
        unfold completedPseudoDiffOpAddValue
        rw [Valuation.map_zero]
        exact le_top
      · exact hmin i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)
    choose c hc using fun i => exists_completedPseudoDiffOpInteger_right_factor
      hp0 (hle i)
    have hscaled : (g p) • (∑ i, c i • v i) =
        ∑ i, g i • v i := by
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i _
      funext j
      change g p * ((c i : CompletedPseudoDiffOp K) * v i j) = g i * v i j
      rw [← mul_assoc, hc i]
    have hsum : ∑ i, c i • v i = 0 := by
      have hz : (g p) • (∑ i, c i • v i) = 0 := by
        rw [hscaled, hg]
      exact (smul_eq_zero.mp hz).resolve_left hp0
    have hc0 : ∀ i, c i = 0 := hv c hsum
    intro i
    rw [← hc i, hc0 i]
    simp

/-- Every completed pseudodifferential lattice has an integral basis of exactly the ambient rank.
The same vectors form a basis after extending scalars to the completed skew field. -/
theorem exists_completedPseudoDiffOpLattice_full_rank_basis
    (L : CompletedPseudoDiffOpLattice K ι) :
    ∃ v : Fin (Fintype.card ι) → (ι → CompletedPseudoDiffOp K),
      LinearIndependent (CompletedPseudoDiffOpInteger (K := K)) v ∧
      Submodule.span (CompletedPseudoDiffOpInteger (K := K)) (Set.range v) = L.carrier ∧
      LinearIndependent (CompletedPseudoDiffOp K) v ∧
      Submodule.span (CompletedPseudoDiffOp K) (Set.range v) = ⊤ := by
  classical
  obtain ⟨n, v, hcard, hindep, hspan⟩ :=
    exists_completedPseudoDiffOp_basis_of_fg_submodule L.carrier L.fg
  have hindepD : LinearIndependent (CompletedPseudoDiffOp K) v :=
    linearIndependent_completedPseudoDiffOp_of_integer hindep
  have hspanD : Submodule.span (CompletedPseudoDiffOp K) (Set.range v) = ⊤ := by
    rw [← L.full]
    apply le_antisymm
    · apply Submodule.span_mono
      rintro x ⟨i, rfl⟩
      rw [← hspan]
      exact Submodule.subset_span ⟨i, rfl⟩
    · apply Submodule.span_le.mpr
      intro x hx
      rw [← hspan] at hx
      exact Submodule.span_induction
        (p := fun y _ => y ∈ Submodule.span (CompletedPseudoDiffOp K) (Set.range v))
        (fun y hy => Submodule.subset_span hy)
        (Submodule.zero_mem _)
        (fun _ _ _ _ hy hz => Submodule.add_mem _ hy hz)
        (fun c y _ hy => by
          change (c : CompletedPseudoDiffOp K) • y ∈
            Submodule.span (CompletedPseudoDiffOp K) (Set.range v)
          exact Submodule.smul_mem _ (c : CompletedPseudoDiffOp K) hy)
        hx
  let b := Module.Basis.mk hindepD (le_of_eq hspanD.symm)
  have hn : Module.finrank (CompletedPseudoDiffOp K)
      (ι → CompletedPseudoDiffOp K) = n := by
    simpa [b] using Module.finrank_eq_card_basis b
  have hi : Module.finrank (CompletedPseudoDiffOp K)
      (ι → CompletedPseudoDiffOp K) = Fintype.card ι := by
    simpa using Module.finrank_eq_card_basis
      (Pi.basisFun (CompletedPseudoDiffOp K) ι)
  have hne : n = Fintype.card ι := hn.symm.trans hi
  cases hne
  exact ⟨v, hindep, hspan, hindepD, hspanD⟩

/-- Every completed pseudodifferential lattice carrier is a finite free valuation module of rank
at most its ambient coordinate rank.  The full-rank theorem above sharpens this bound to equality. -/
theorem exists_completedPseudoDiffOpLattice_basis
    (L : CompletedPseudoDiffOpLattice K ι) :
    ∃ (n : ℕ) (v : Fin n → (ι → CompletedPseudoDiffOp K)), n ≤ Fintype.card ι ∧
      LinearIndependent (CompletedPseudoDiffOpInteger (K := K)) v ∧
      Submodule.span (CompletedPseudoDiffOpInteger (K := K)) (Set.range v) = L.carrier :=
  exists_completedPseudoDiffOp_basis_of_fg_submodule L.carrier L.fg

end

end DiffOp

end GaloisForLFunctions.HTGeometry
