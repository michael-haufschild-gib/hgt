import GaloisForLFunctions.HTGeometry.AnalyticDirichletObservableGrassmannCorrespondence
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Complete analytic Grassmann-field lattice embedding

The analytic Grassmann representation already preserves arbitrary joins and binary meets.  This
leaf proves the missing finite-character statement: a field element represented by an arbitrary
source subspace is represented by a finite-dimensional source subspace.  Finite-dimensional
descending-chain stabilization then upgrades the binary meet law to every nonempty intersection.

The empty intersection is deliberately excluded in the ambient field lattice: its value there is
the whole meromorphic field, while the represented top is only the field of the complete source
frame.  Equivalently, the result is a complete lattice embedding into the interval below that
represented top.
-/

namespace GaloisForLFunctions.HTGeometry

open Set

noncomputable section

universe u v w

set_option maxHeartbeats 800000

attribute [local instance]
  analyticObservableUpperEndAnalyticDomain
  analyticObservableUpperEndMeroComplexAlgebra
  analyticObservableUpperEndMeroDifferential

/-- Every element of a represented analytic Grassmann field already lies in the field of a
finite-dimensional source subspace.  The subspace can be chosen inside the original source
subspace. -/
theorem exists_finiteDimensional_source_of_mem_analyticObservableGrassmannField
    {V : Type u} {J : Type v} [TopologicalSpace V]
    (x : Nat.Primes → V) (K : Set V) (hx : CofiniteTailDenseOn x K)
    (f : J → V → ℂ) (hf : ∀ j, Continuous (f j))
    (hlinear : LinearIndependent ℂ (fun j ↦ fun z : K ↦ f j z.1))
    (M : J → ℝ) (hM : ∀ j p, ‖f j (x p)‖ ≤ M j)
    (a : ℂ) (W : Submodule ℂ (J →₀ ℂ)) (z : upperEndMeroField)
    (hz : z ∈ analyticObservableGrassmannField x f M hM a W) :
    ∃ U : Submodule ℂ (J →₀ ℂ),
      U ≤ W ∧ FiniteDimensional ℂ U ∧
        z ∈ analyticObservableGrassmannField x f M hM a U := by
  let line : W → Submodule ℂ (J →₀ ℂ) := fun w ↦ ℂ ∙ (w.1 : J →₀ ℂ)
  have hW : (⨆ w : W, line w) = W := by
    apply le_antisymm
    · apply iSup_le
      intro w
      rw [Submodule.span_singleton_le_iff_mem]
      exact w.2
    · intro c hc
      exact (le_iSup (fun w : W ↦ line w) ⟨c, hc⟩)
        (Submodule.subset_span (Set.mem_singleton c))
  have hfield :
      analyticObservableGrassmannField x f M hM a W =
        ⨆ w : W, analyticObservableGrassmannField x f M hM a (line w) := by
    calc
      analyticObservableGrassmannField x f M hM a W =
          analyticObservableGrassmannField x f M hM a (⨆ w : W, line w) :=
        congrArg (analyticObservableGrassmannField x f M hM a) hW.symm
      _ = ⨆ w : W, analyticObservableGrassmannField x f M hM a (line w) :=
        analyticObservableGrassmannField_iSup x f M hM a line
  rw [hfield] at hz
  obtain ⟨S, hzS⟩ := IntermediateField.exists_finset_of_mem_iSup hz
  let A : Set (J →₀ ℂ) := (fun w : W ↦ (w.1 : J →₀ ℂ)) '' (S : Set W)
  let U : Submodule ℂ (J →₀ ℂ) := Submodule.span ℂ A
  have hAfin : A.Finite := S.finite_toSet.image _
  have hUW : U ≤ W := by
    change Submodule.span ℂ A ≤ W
    rw [Submodule.span_le]
    rintro c ⟨w, hwS, rfl⟩
    exact w.2
  have hlineU : ∀ w ∈ S, line w ≤ U := by
    intro w hw
    rw [Submodule.span_singleton_le_iff_mem]
    apply Submodule.subset_span
    exact ⟨w, hw, rfl⟩
  have hfields :
      (⨆ w ∈ S, analyticObservableGrassmannField x f M hM a (line w)) ≤
        analyticObservableGrassmannField x f M hM a U := by
    apply iSup_le
    intro w
    apply iSup_le
    intro hw
    exact (cofiniteTailDenseOn_analyticObservableGrassmannField_le_iff
      x K hx f hf hlinear M hM a (line w) U).2 (hlineU w hw)
  refine ⟨U, hUW, ?_, hfields hzS⟩
  exact FiniteDimensional.span_of_finite ℂ hAfin

/-- Inside a finite-dimensional source space, an arbitrary family of subspace constraints is
already determined by finitely many members of the family. -/
theorem exists_finset_inf_eq_iInf_inside_finiteDimensional
    {E : Type u} {ι : Type w} [AddCommGroup E] [Module ℂ E]
    (U : Submodule ℂ E) [FiniteDimensional ℂ U]
    (W : ι → Submodule ℂ E) :
    ∃ S : Finset ι,
      U ⊓ (⨅ i, W i) = U ⊓ (⨅ i ∈ S, W i) := by
  classical
  let A : Finset ι → Submodule ℂ U := fun S ↦
    ⨅ i ∈ S, (W i).comap U.subtype
  have hex : ∃ n : ℕ, ∃ S : Finset ι, Module.finrank ℂ (A S) = n :=
    ⟨Module.finrank ℂ (A ∅), ∅, rfl⟩
  let n : ℕ := Nat.find hex
  obtain ⟨S, hS⟩ := Nat.find_spec hex
  have hmin : ∀ T : Finset ι, n ≤ Module.finrank ℂ (A T) := by
    intro T
    exact Nat.find_min' hex ⟨T, rfl⟩
  have hinsert : ∀ i, A (insert i S) = A S := by
    intro i
    apply Submodule.eq_of_le_of_finrank_le
    · intro q hq
      simp only [A, Submodule.mem_iInf] at hq ⊢
      intro j hj
      exact hq j (Finset.mem_insert_of_mem hj)
    · rw [hS]
      exact hmin (insert i S)
  have hAiInf : A S = ⨅ i, (W i).comap U.subtype := by
    apply le_antisymm
    · apply le_iInf
      intro i
      rw [← hinsert i]
      intro q hq
      simp only [A, Submodule.mem_iInf] at hq
      exact hq i (Finset.mem_insert_self i S)
    · intro q hq
      simp only [A, Submodule.mem_iInf] at hq ⊢
      intro i hi
      exact hq i
  refine ⟨S, ?_⟩
  ext y
  constructor
  · rintro ⟨hyU, hyW⟩
    refine ⟨hyU, ?_⟩
    apply (Submodule.mem_iInf _).2
    intro i
    apply (Submodule.mem_iInf _).2
    intro hi
    have hyWall : ∀ i, y ∈ W i := (Submodule.mem_iInf W).1 hyW
    exact hyWall i
  · rintro ⟨hyU, hyW⟩
    refine ⟨hyU, ?_⟩
    have hyAS : (⟨y, hyU⟩ : U) ∈ A S := by
      apply (Submodule.mem_iInf _).2
      intro i
      apply (Submodule.mem_iInf _).2
      intro hi
      have hyWi : y ∈ W i :=
        (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hyW i) hi
      exact hyWi
    rw [hAiInf] at hyAS
    apply (Submodule.mem_iInf W).2
    intro i
    exact (Submodule.mem_iInf _).1 hyAS i

/-- Finite source intersections are transported to finite intersections of represented fields. -/
theorem cofiniteTailDenseOn_analyticObservableGrassmannField_finset_inf
    {V : Type u} {J : Type v} {ι : Type w} [TopologicalSpace V]
    (x : Nat.Primes → V) (K : Set V) (hx : CofiniteTailDenseOn x K)
    (f : J → V → ℂ) (hf : ∀ j, Continuous (f j))
    (hlinear : LinearIndependent ℂ (fun j ↦ fun z : K ↦ f j z.1))
    (M : J → ℝ) (hM : ∀ j p, ‖f j (x p)‖ ≤ M j)
    (a : ℂ) (U : Submodule ℂ (J →₀ ℂ))
    (W : ι → Submodule ℂ (J →₀ ℂ)) (S : Finset ι) :
    analyticObservableGrassmannField x f M hM a
        (U ⊓ (⨅ i ∈ S, W i)) =
      analyticObservableGrassmannField x f M hM a U ⊓
        (⨅ i ∈ S, analyticObservableGrassmannField x f M hM a (W i)) := by
  classical
  induction S using Finset.induction_on generalizing U with
  | empty => simp
  | @insert i S hi ih =>
      rw [Finset.iInf_insert, Finset.iInf_insert, ← inf_assoc, ih,
        ← cofiniteTailDenseOn_analyticObservableGrassmannField_inf
          x K hx f hf hlinear M hM a U (W i), inf_assoc]

/-- **Complete analytic Grassmann meet law.**  Every nonempty intersection of represented
Dirichlet differential fields is exactly the field represented by the intersection of their
source subspaces.  Thus no hidden hypertranscendental sector can survive an infinite descending
intersection after all of its source directions have disappeared. -/
theorem cofiniteTailDenseOn_analyticObservableGrassmannField_iInf
    {V : Type u} {J : Type v} {ι : Type w} [TopologicalSpace V] [Nonempty ι]
    (x : Nat.Primes → V) (K : Set V) (hx : CofiniteTailDenseOn x K)
    (f : J → V → ℂ) (hf : ∀ j, Continuous (f j))
    (hlinear : LinearIndependent ℂ (fun j ↦ fun z : K ↦ f j z.1))
    (M : J → ℝ) (hM : ∀ j p, ‖f j (x p)‖ ≤ M j)
    (a : ℂ) (W : ι → Submodule ℂ (J →₀ ℂ)) :
    (⨅ i, analyticObservableGrassmannField x f M hM a (W i)) =
      analyticObservableGrassmannField x f M hM a (⨅ i, W i) := by
  apply le_antisymm
  · intro z hz
    let i0 : ι := Classical.choice inferInstance
    have hzall : ∀ i, z ∈ analyticObservableGrassmannField x f M hM a (W i) := by
      intro i
      exact (iInf_le (fun i ↦
        analyticObservableGrassmannField x f M hM a (W i)) i) hz
    have hzi0 : z ∈ analyticObservableGrassmannField x f M hM a (W i0) :=
      hzall i0
    obtain ⟨U, hUW, hUfin, hzU⟩ :=
      exists_finiteDimensional_source_of_mem_analyticObservableGrassmannField
        x K hx f hf hlinear M hM a (W i0) z hzi0
    letI : FiniteDimensional ℂ U := hUfin
    obtain ⟨S, hS⟩ :=
      exists_finset_inf_eq_iInf_inside_finiteDimensional U W
    have hzFiniteFields : z ∈
        analyticObservableGrassmannField x f M hM a U ⊓
          (⨅ i ∈ S, analyticObservableGrassmannField x f M hM a (W i)) := by
      refine ⟨hzU, ?_⟩
      apply IntermediateField.mem_sInf.mpr
      rintro F ⟨i, rfl⟩
      apply IntermediateField.mem_sInf.mpr
      rintro F ⟨hi, rfl⟩
      exact hzall i
    rw [← cofiniteTailDenseOn_analyticObservableGrassmannField_finset_inf
      x K hx f hf hlinear M hM a U W S] at hzFiniteFields
    rw [← hS] at hzFiniteFields
    apply (cofiniteTailDenseOn_analyticObservableGrassmannField_le_iff
      x K hx f hf hlinear M hM a
      (U ⊓ ⨅ i, W i) (⨅ i, W i)).2 inf_le_right
    exact hzFiniteFields
  · apply le_iInf
    intro i
    exact (cofiniteTailDenseOn_analyticObservableGrassmannField_le_iff
      x K hx f hf hlinear M hM a (⨅ j, W j) (W i)).2 (iInf_le W i)

end

end GaloisForLFunctions.HTGeometry
