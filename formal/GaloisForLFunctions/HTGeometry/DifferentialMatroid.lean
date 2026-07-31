import GaloisForLFunctions.HTGeometry.DifferentialMatroidClosure
import GaloisForLFunctions.HTGeometry.DifferentialAlgebraicFiniteTransitivity
import Mathlib.Combinatorics.Matroid.Closure

/-!
# The differential-transcendence matroid

This module completes `DifferentialMatroidFoundations`: in characteristic zero, differential
independence is the independence predicate of a genuine finitary mathlib `Matroid`.

The load-bearing augmentation proof is not assumed.  Starting from a nonmaximal independent set,
finitarity reduces dependence over a maximal independent set to finitely many generators.  The
set-valued Steinitz theorem `differentialClosure_exchange` and finite differential-algebraic
transitivity then force one of those generators to augment the original set.
-/

open scoped Classical Differential

namespace GaloisForLFunctions

open Set

noncomputable section

universe u

/-- If an element is differentially algebraic over an independent set, one finite subset already
witnesses that differential algebraicity. -/
theorem differentialClosure_exists_finite_subset_of_indep
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    {s : Set E} {x : E} (hs : DiffIndepOn F s)
    (hx : x ∈ differentialClosure F s) :
    ∃ t : Set E, t ⊆ s ∧ t.Finite ∧ x ∈ differentialClosure F t := by
  by_cases hxs : x ∈ s
  · exact ⟨{x}, by simpa, Set.finite_singleton x,
      subset_differentialClosure ({x} : Set E) (Set.mem_singleton x)⟩
  by_contra h
  push Not at h
  have hall : DiffIndepOn F (insert x s) := by
    apply diffIndepOn_of_forall_finite
    intro t ht htfin
    let u : Set E := t \ {x}
    have hufin : u.Finite := htfin.sdiff
    have hus : u ⊆ s := by
      intro z hz
      have hzt := ht hz.1
      rcases Set.mem_insert_iff.mp hzt with hzx | hzs
      · exact (hz.2 (by simp [hzx])).elim
      · exact hzs
    have hxu : x ∉ u := by simp [u]
    have hu : DiffIndepOn F u := hs.subset hus
    have hxnot : x ∉ differentialClosure F u := h u hus hufin
    have hi : DiffIndepOn F (insert x u) :=
      (diffIndepOn_insert_iff hxu).mpr ⟨hu, hxnot⟩
    exact hi.subset (by
      intro z hzt
      by_cases hzx : z = x
      · simp [hzx]
      · exact Set.mem_insert_of_mem x ⟨hzt, by simp [hzx]⟩)
  exact ((diffIndepOn_insert_iff hxs).mp hall).2 hx

set_option maxHeartbeats 600000 in
/-- Differential algebraicity is transitive across any nonempty finite family, independently of
the chosen finite indexing type. -/
theorem differentialAlgebraicOver_trans_finite_nonempty
    {F E ι : Type u} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    [Finite ι] [Nonempty ι]
    (x : ι → E) (hx : ∀ i, DifferentialAlgebraicOver F (x i)) (y : E)
    (hy : DifferentialAlgebraicOver (differentialAdjoin F (Set.range x)) y) :
    DifferentialAlgebraicOver F y := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  cases n with
  | zero =>
      exact False.elim (Fin.elim0 (e (Classical.choice (inferInstance : Nonempty ι))))
  | succ n =>
      let z : Fin (n + 1) → E := x ∘ e.symm
      have hz : ∀ i, DifferentialAlgebraicOver F (z i) := fun i => hx (e.symm i)
      have hrange : Set.range z = Set.range x := by
        ext a
        simp [z]
      exact HTGeometry.differentialAlgebraicOver_trans_fin_succ_narrow z hz y (by rwa [hrange])

private def differentialIndepMatroid
    (F E : Type u) [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E] :
    IndepMatroid E :=
  IndepMatroid.ofFinitary Set.univ (DiffIndepOn F)
    diffIndepOn_empty
    (fun _ _ hJ hIJ => hJ.subset hIJ)
    (by
      intro I B hI hImax hBmax
      obtain ⟨y, hyI, hyind⟩ :=
        Set.exists_insert_of_not_maximal (fun _ _ hJ hIJ => hJ.subset hIJ) hI hImax
      by_contra hno
      push Not at hno
      have hyB : y ∉ B := by
        intro hyB
        exact hno y ⟨hyB, hyI⟩ hyind
      have hydep : ¬ DiffIndepOn F (insert y B) :=
        hBmax.not_prop_of_ssuperset (ssubset_insert hyB)
      have hycl : y ∈ differentialClosure F B := by
        change DifferentialAlgebraicOver (differentialAdjoin F B) y
        by_contra hynda
        exact hydep ((diffIndepOn_insert_iff hyB).mpr ⟨hBmax.prop, hynda⟩)
      obtain ⟨J, hJB, hJfin, hyJ⟩ :=
        differentialClosure_exists_finite_subset_of_indep hBmax.prop hycl
      let Base := differentialAdjoin F I
      letI : DifferentialAlgebra Base E :=
        ⟨fun c => derivationClosedDifferential_apply Base
          (derivationClosed_differentialAdjoin F I) c⟩
      have hjI : ∀ j ∈ J, DifferentialAlgebraicOver Base j := by
        intro j hj
        by_cases hji : j ∈ I
        · exact subset_differentialClosure I hji
        · have hjdep : ¬ DiffIndepOn F (insert j I) := hno j ⟨hJB hj, hji⟩
          change DifferentialAlgebraicOver (differentialAdjoin F I) j
          by_contra hjnda
          exact hjdep ((diffIndepOn_insert_iff hji).mpr ⟨hI, hjnda⟩)
      have hyBase : DifferentialAlgebraicOver Base y := by
        by_cases hJempty : J = ∅
        · subst J
          apply HTGeometry.differentialAlgebraicOver_mono_differentialAdjoin_narrow
            (F := F) (E := E) (s := (∅ : Set E))
            (B := Base) (derivationClosed_differentialAdjoin F I)
          · simp
          · exact hyJ
        · letI : Fintype J := hJfin.fintype
          letI : Nonempty J := Set.nonempty_coe_sort.mpr (Set.nonempty_iff_ne_empty.mpr hJempty)
          let x : J → E := Subtype.val
          let T := differentialAdjoin Base J
          have hyT : DifferentialAlgebraicOver T y := by
            apply HTGeometry.differentialAlgebraicOver_mono_differentialAdjoin_narrow
              (F := F) (E := E) (s := J)
              (B := T.restrictScalars F)
              (derivationClosed_differentialAdjoin Base J)
            · intro z hz
              exact subset_differentialAdjoin Base J hz
            · exact hyJ
          apply differentialAlgebraicOver_trans_finite_nonempty x
            (fun i => hjI i i.2) y
          have hrange : Set.range x = J := Subtype.range_val
          rwa [hrange]
      exact ((diffIndepOn_insert_iff hyI).mp hyind).2 hyBase)
    (fun _ h => diffIndepOn_of_forall_finite h)
    (fun _ _ => Set.subset_univ _)

/-- The finitary differential-transcendence matroid of a characteristic-zero differential field
extension. -/
def differentialMatroid
    (F E : Type u) [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E] : Matroid E :=
  (differentialIndepMatroid F E).matroid

instance differentialMatroid_finitary
    (F E : Type u) [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E] :
    (differentialMatroid F E).Finitary := by
  unfold differentialMatroid differentialIndepMatroid
  infer_instance

@[simp]
theorem differentialMatroid_ground
    (F E : Type u) [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E] :
    (differentialMatroid F E).E = Set.univ := rfl

@[simp]
theorem differentialMatroid_indep_iff
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    {s : Set E} :
    (differentialMatroid F E).Indep s ↔ DiffIndepOn F s := Iff.rfl

/-- On an independent set, mathlib matroid closure is exactly differential-algebraic closure. -/
theorem differentialMatroid_mem_closure_iff_of_indep
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    {s : Set E} (hs : DiffIndepOn F s) (x : E) :
    x ∈ (differentialMatroid F E).closure s ↔ x ∈ differentialClosure F s := by
  by_cases hxs : x ∈ s
  · exact iff_of_true
      (((differentialMatroid F E).subset_closure s (by simp)) hxs)
      (subset_differentialClosure s hxs)
  have hMind : (differentialMatroid F E).Indep s :=
    differentialMatroid_indep_iff.mpr hs
  rw [hMind.mem_closure_iff_of_notMem hxs, Matroid.dep_iff]
  simp only [differentialMatroid_ground, Set.insert_subset_iff, Set.mem_univ, true_and,
    differentialMatroid_indep_iff]
  rw [diffIndepOn_insert_iff hxs]
  simp [hs, differentialClosure]

end

end GaloisForLFunctions
