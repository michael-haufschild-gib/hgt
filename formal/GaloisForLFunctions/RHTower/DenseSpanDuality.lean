import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient

/-!
# Dense span from trivial continuous annihilator

This is the precise complex Hahn--Banach capstone used after the
Fourier--Borel argument: if the only continuous functional annihilating a
family is zero, its complex linear span is dense.
-/

noncomputable section

namespace RHTower

open Set Topology

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Complex dual-annihilator criterion for density. -/
theorem dense_span_of_forall_dual_eq_zero (v : ι → E)
    (hdual : ∀ L : E →L[ℂ] ℂ, (∀ i, L (v i) = 0) → L = 0) :
    Dense (Submodule.span ℂ (Set.range v) : Set E) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  let M : Submodule ℂ E := (Submodule.span ℂ (Set.range v)).topologicalClosure
  change M = ⊤
  by_contra hM
  obtain ⟨x, hx⟩ : ∃ x : E, x ∉ M := by
    simpa [Submodule.eq_top_iff'] using hM
  letI : IsClosed (M : Set E) := Submodule.isClosed_topologicalClosure _
  have hxq : (Submodule.Quotient.mk x : E ⧸ M) ≠ 0 := by
    simpa [Submodule.Quotient.mk_eq_zero] using hx
  obtain ⟨g, hg, hgx⟩ := exists_dual_vector ℂ (Submodule.Quotient.mk x : E ⧸ M)
    (norm_ne_zero_iff.mpr hxq)
  let L : E →L[ℂ] ℂ := g.comp M.mkQL
  have hLv : ∀ i, L (v i) = 0 := by
    intro i
    have hvi : v i ∈ M :=
      (Submodule.span ℂ (Set.range v)).le_topologicalClosure
        (Submodule.subset_span (Set.mem_range_self i))
    change g (M.mkQ (v i)) = 0
    rw [show M.mkQ (v i) = 0 by exact (Submodule.Quotient.mk_eq_zero M).mpr hvi]
    simp
  have hL0 := hdual L hLv
  have hxzero : L x = 0 := by rw [hL0]; simp
  change g (M.mkQ x) = 0 at hxzero
  have hxzero' : g (Submodule.Quotient.mk x) = 0 := by
    simpa [Submodule.mkQ_apply] using hxzero
  rw [hgx] at hxzero'
  have hnormzero : ‖(Submodule.Quotient.mk x : E ⧸ M)‖ = 0 := by
    have hre := congrArg Complex.re hxzero'
    simpa using hre
  exact (norm_pos_iff.mpr hxq).ne' hnormzero

/-- Pointwise complex Hahn--Banach criterion: a vector lies in the closed span
of a family if every continuous functional annihilating the family also
annihilates that vector. -/
theorem mem_topologicalClosure_span_of_forall_dual
    (v : ι → E) (x : E)
    (hdual : ∀ L : E →L[ℂ] ℂ, (∀ i, L (v i) = 0) → L x = 0) :
    x ∈ (Submodule.span ℂ (Set.range v)).topologicalClosure := by
  let M : Submodule ℂ E := (Submodule.span ℂ (Set.range v)).topologicalClosure
  by_contra hx
  letI : IsClosed (M : Set E) := Submodule.isClosed_topologicalClosure _
  have hxq : (Submodule.Quotient.mk x : E ⧸ M) ≠ 0 := by
    simpa [Submodule.Quotient.mk_eq_zero] using hx
  obtain ⟨g, hg, hgx⟩ := exists_dual_vector ℂ (Submodule.Quotient.mk x : E ⧸ M)
    (norm_ne_zero_iff.mpr hxq)
  let L : E →L[ℂ] ℂ := g.comp M.mkQL
  have hLv : ∀ i, L (v i) = 0 := by
    intro i
    have hvi : v i ∈ M :=
      (Submodule.span ℂ (Set.range v)).le_topologicalClosure
        (Submodule.subset_span (Set.mem_range_self i))
    change g (M.mkQ (v i)) = 0
    rw [show M.mkQ (v i) = 0 by exact (Submodule.Quotient.mk_eq_zero M).mpr hvi]
    simp
  have hxzero := hdual L hLv
  change g (M.mkQ x) = 0 at hxzero
  have hxzero' : g (Submodule.Quotient.mk x) = 0 := by
    simpa [Submodule.mkQ_apply] using hxzero
  rw [hgx] at hxzero'
  have hnormzero : ‖(Submodule.Quotient.mk x : E ⧸ M)‖ = 0 := by
    have hre := congrArg Complex.re hxzero'
    simpa using hre
  exact (norm_pos_iff.mpr hxq).ne' hnormzero

end RHTower
