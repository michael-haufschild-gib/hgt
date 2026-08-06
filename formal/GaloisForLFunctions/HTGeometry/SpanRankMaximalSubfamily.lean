import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

/-!
# The rank of a span through a maximal independent subfamily

Over a commutative domain the rank of the span of a family is the size of any independent
subfamily over which every member of the family is torsion: the quotient of the span by the span
of the subfamily is a torsion module, hence of rank zero, and rank is additive along quotients.

A family indexed by a finite type always has such a subfamily — one of maximal cardinality — so
its span has rank the maximal size of an independent subfamily.
-/

open Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

variable {R M : Type u} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]

/-! ### Torsion over an independent core -/

/-- If every generator has a nonzero multiple inside a submodule, so does every element of the
span of the generators. -/
theorem exists_smul_mem_of_mem_span {κ : Type u} (v : κ → M) (N : Submodule R M)
    (htor : ∀ k : κ, ∃ c : R, c ≠ 0 ∧ c • v k ∈ N) :
    ∀ x ∈ Submodule.span R (Set.range v), ∃ c : R, c ≠ 0 ∧ c • x ∈ N := by
  intro x hx
  refine Submodule.span_induction (p := fun y _ => ∃ c : R, c ≠ 0 ∧ c • y ∈ N) ?_ ?_ ?_ ?_ hx
  · rintro - ⟨k, rfl⟩
    exact htor k
  · exact ⟨1, one_ne_zero, by rw [one_smul]; exact N.zero_mem⟩
  · rintro y z _ _ ⟨c, hc, hcy⟩ ⟨e, he, hez⟩
    refine ⟨c * e, mul_ne_zero hc he, ?_⟩
    have h1 : (c * e) • y = e • (c • y) := by rw [← mul_smul, mul_comm]
    have h2 : (c * e) • z = c • (e • z) := by rw [← mul_smul]
    rw [smul_add, h1, h2]
    exact N.add_mem (N.smul_mem e hcy) (N.smul_mem c hez)
  · rintro a y _ ⟨c, hc, hcy⟩
    refine ⟨c, hc, ?_⟩
    rw [smul_comm]
    exact N.smul_mem a hcy

/-- **The rank of a span through an independent core.**  If every generator has a nonzero multiple
in the span of an independent subset, the rank of the whole span is the size of that subset. -/
theorem rank_span_eq_mk_of_torsion_generators {κ : Type u} (v : κ → M) (s : Set M)
    (hs : LinearIndepOn R id s) (hsub : s ⊆ Set.range v)
    (htor : ∀ k : κ, ∃ c : R, c ≠ 0 ∧ c • v k ∈ Submodule.span R s) :
    Module.rank R (Submodule.span R (Set.range v)) = Cardinal.mk s := by
  classical
  set N : Submodule R M := Submodule.span R s with hNdef
  set W : Submodule R M := Submodule.span R (Set.range v) with hWdef
  have hNW : N ≤ W := Submodule.span_mono hsub
  set N' : Submodule R W := N.comap W.subtype with hN'def
  have hquot : Module.IsTorsion R (W ⧸ N') := by
    intro x
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective N' x
    obtain ⟨c, hc, hcy⟩ := exists_smul_mem_of_mem_span v N htor (y : M) y.2
    refine ⟨⟨c, mem_nonZeroDivisors_of_ne_zero hc⟩, ?_⟩
    show c • (Submodule.Quotient.mk y : W ⧸ N') = 0
    rw [← Submodule.Quotient.mk_smul]
    refine (Submodule.Quotient.mk_eq_zero N').2 ?_
    show ((c • y : W) : M) ∈ N
    rw [Submodule.coe_smul]
    exact hcy
  have hrank0 : Module.rank R (W ⧸ N') = 0 := rank_eq_zero_iff_isTorsion.2 hquot
  have hrankN' : Module.rank R N' = Cardinal.mk s := by
    have hequiv : N' ≃ₗ[R] N := Submodule.comapSubtypeEquivOfLe hNW
    rw [hequiv.rank_eq, hNdef, rank_span_set hs]
  have hadd := rank_quotient_add_rank_of_isDomain (R := R) (M := W) N'
  rw [hrank0, hrankN', zero_add] at hadd
  exact hadd.symm

/-! ### Maximal independent subfamilies of a finite family -/

/-- A family indexed by a finite type has an independent subfamily of maximal size, and every
member of the family has a nonzero multiple in its span. -/
theorem exists_maximal_linearIndepOn_finset {κ : Type u} [Fintype κ] [DecidableEq κ]
    (v : κ → M) :
    ∃ T : Finset κ, LinearIndepOn R v (T : Set κ) ∧
      (∀ k : κ, ∃ c : R, c ≠ 0 ∧ c • v k ∈ Submodule.span R (v '' (T : Set κ))) ∧
      ∀ k : κ, k ∉ T → ¬ LinearIndepOn R v ((insert k T : Finset κ) : Set κ) := by
  classical
  set S : Finset (Finset κ) :=
    Finset.univ.filter fun T : Finset κ => LinearIndepOn R v (T : Set κ) with hS
  have hSne : S.Nonempty := by
    refine ⟨∅, ?_⟩
    rw [hS, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    simp
  obtain ⟨T, hTS, hTmax⟩ := S.exists_max_image Finset.card hSne
  have hTind : LinearIndepOn R v (T : Set κ) := by
    have := hTS
    rw [hS, Finset.mem_filter] at this
    exact this.2
  have hdep : ∀ k : κ, k ∉ T → ¬ LinearIndepOn R v ((insert k T : Finset κ) : Set κ) := by
    intro k hk hcon
    have hmem : (insert k T : Finset κ) ∈ S := by
      rw [hS, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hcon⟩
    have hcard := hTmax _ hmem
    rw [Finset.card_insert_of_notMem hk] at hcard
    omega
  refine ⟨T, hTind, fun k => ?_, hdep⟩
  by_cases hk : k ∈ T
  · exact ⟨1, one_ne_zero, by
      rw [one_smul]
      exact Submodule.subset_span ⟨k, hk, rfl⟩⟩
  · have hins := hdep k hk
    rw [linearIndepOn_iff] at hins
    push Not at hins
    obtain ⟨l, hlsupp, hlzero, hlne⟩ := hins
    have hlk : l k ≠ 0 := by
      intro hlk0
      apply hlne
      refine (linearIndepOn_iff.1 hTind) l ?_ hlzero
      intro x hx
      have hx' := hlsupp hx
      rw [Finset.coe_insert, Set.mem_insert_iff] at hx'
      rcases hx' with rfl | hx'
      · exact absurd (Finsupp.mem_support_iff.1 hx) (by simpa using hlk0)
      · exact hx'
    refine ⟨l k, hlk, ?_⟩
    have hsplit : Finsupp.linearCombination R v l
        = l k • v k + ∑ t ∈ l.support.erase k, l t • v t := by
      rw [Finsupp.linearCombination_apply, Finsupp.sum]
      by_cases hks : k ∈ l.support
      · rw [← Finset.add_sum_erase _ _ hks]
      · rw [Finsupp.notMem_support_iff.1 hks, zero_smul, zero_add,
          Finset.erase_eq_of_notMem hks]
    have hval : l k • v k = -∑ t ∈ l.support.erase k, l t • v t := by
      have h0 : l k • v k + ∑ t ∈ l.support.erase k, l t • v t = 0 := by
        rw [← hsplit, hlzero]
      exact add_eq_zero_iff_eq_neg.1 h0
    rw [hval]
    refine Submodule.neg_mem _ (Submodule.sum_mem _ fun t ht => ?_)
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨t, ?_, rfl⟩)
    have hts := hlsupp (Finset.mem_of_mem_erase ht)
    rw [Finset.coe_insert, Set.mem_insert_iff] at hts
    rcases hts with rfl | hts
    · exact absurd rfl (Finset.ne_of_mem_erase ht)
    · exact hts

end

end GaloisForLFunctions.HTGeometry
