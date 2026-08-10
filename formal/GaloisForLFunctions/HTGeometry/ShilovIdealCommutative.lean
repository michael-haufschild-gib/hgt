import GaloisForLFunctions.HTGeometry.ChoquetBoundaryFunctionSystem
import Mathlib.Topology.ContinuousMap.Ideals

/-!
# The Shilov ideal of a function system

The Shilov boundary of a function system `S ⊆ C(X, ℂ)` carries a distinguished ideal: the
functions vanishing on it.  This module identifies it as the **largest closed boundary ideal**.

Two halves, with different hypotheses:

* maximality is unconditional — every closed ideal of `C(X, ℂ)` is the vanishing ideal of a closed
  set (mathlib's `idealOfSet_ofIdeal_isClosed`), a boundary ideal exactly when that set is a
  boundary, and the Shilov boundary is contained in every closed boundary;
* that the Shilov ideal *is* a boundary ideal needs the Shilov boundary to be a boundary, which is
  the function-system statement proved in `ChoquetBoundaryFunctionSystem`.

This is the commutative model of the Shilov ideal that the C*-envelope is built from.
-/

namespace GaloisForLFunctions.HTGeometry

namespace ShilovLocal

open Set ContinuousMap

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-- The Shilov ideal: the functions vanishing on the Shilov boundary. -/
noncomputable def shilovIdeal (S : Submodule ℂ C(X, ℂ)) : Ideal C(X, ℂ) :=
  ContinuousMap.idealOfSet ℂ (shilovBoundary S)ᶜ

omit [T2Space X] in
@[simp]
theorem mem_shilovIdeal {S : Submodule ℂ C(X, ℂ)} {f : C(X, ℂ)} :
    f ∈ shilovIdeal S ↔ ∀ x ∈ shilovBoundary S, f x = 0 := by
  rw [shilovIdeal, ContinuousMap.mem_idealOfSet, compl_compl]

omit [T2Space X] in
theorem shilovIdeal_eq_vanishingIdeal (S : Submodule ℂ C(X, ℂ)) {f : C(X, ℂ)} :
    f ∈ shilovIdeal S ↔ f ∈ vanishingIdeal (shilovBoundary S) := by
  rw [mem_shilovIdeal, mem_vanishingIdeal]

omit [T2Space X] in
theorem isClosed_shilovIdeal (S : Submodule ℂ C(X, ℂ)) :
    IsClosed (shilovIdeal S : Set C(X, ℂ)) :=
  ContinuousMap.idealOfSet_closed ℂ _

/-- **Every closed ideal of `C(X, ℂ)` is the vanishing ideal of a closed set.** -/
theorem exists_isClosed_mem_iff_of_isClosed (I : Ideal C(X, ℂ))
    (hI : IsClosed (I : Set C(X, ℂ))) :
    ∃ F : Set X, IsClosed F ∧ ∀ f : C(X, ℂ), f ∈ I ↔ ∀ x ∈ F, f x = 0 := by
  refine ⟨(ContinuousMap.setOfIdeal I)ᶜ, (ContinuousMap.setOfIdeal_open I).isClosed_compl,
    fun f => ?_⟩
  constructor
  · intro hf x hx
    have hf' : f ∈ ContinuousMap.idealOfSet ℂ (ContinuousMap.setOfIdeal I) := by
      rwa [ContinuousMap.idealOfSet_ofIdeal_isClosed hI]
    exact ContinuousMap.mem_idealOfSet.mp hf' hx
  · intro hf
    have hf' : f ∈ ContinuousMap.idealOfSet ℂ (ContinuousMap.setOfIdeal I) :=
      ContinuousMap.mem_idealOfSet.mpr fun x hx => hf x hx
    rwa [ContinuousMap.idealOfSet_ofIdeal_isClosed hI] at hf'

/-- **Maximality of the Shilov ideal, unconditionally.**  Any closed ideal all of whose elements
leave the norms on `S` intact is contained in the Shilov ideal. -/
theorem le_shilovIdeal_of_isBoundaryIdeal (S : Submodule ℂ C(X, ℂ)) (I : Ideal C(X, ℂ))
    (hIc : IsClosed (I : Set C(X, ℂ))) (hIb : ∀ s ∈ S, ∀ f ∈ I, ‖s‖ ≤ ‖s - f‖) :
    ∀ f ∈ I, f ∈ shilovIdeal S := by
  obtain ⟨F, hFc, hFmem⟩ := exists_isClosed_mem_iff_of_isClosed I hIc
  have hbdry : IsBoundaryIdeal S (vanishingIdeal F) := by
    intro s hs j hj
    exact hIb s hs j ((hFmem j).mpr (fun x hx => hj x hx))
  have hFb : IsBoundarySet S F := (isBoundaryIdeal_vanishingIdeal_iff S hFc).mp hbdry
  have hsub : shilovBoundary S ⊆ F := shilovBoundary_subset hFc hFb
  intro f hf
  rw [mem_shilovIdeal]
  intro x hx
  exact (hFmem f).mp hf x (hsub hx)

omit [T2Space X] in
/-- **The Shilov ideal is a boundary ideal.**  For a function system the Shilov boundary is itself
a boundary, so subtracting a function vanishing on it cannot shorten an element of `S`. -/
theorem isBoundaryIdeal_shilovIdeal (S : Submodule ℂ C(X, ℂ)) (hone : (1 : C(X, ℂ)) ∈ S)
    (hstar : ∀ s ∈ S, star s ∈ S)
    (hsep : ∀ x y : X, x ≠ y → ∃ s ∈ S, (s : C(X, ℂ)) x ≠ s y) :
    ∀ s ∈ S, ∀ f ∈ shilovIdeal S, ‖s‖ ≤ ‖s - f‖ := by
  intro s hs f hf
  have hb : IsBoundarySet S (shilovBoundary S) :=
    (isLeast_shilovBoundary_of_functionSystem S hone hstar hsep).1.2
  exact isBoundaryIdeal_of_isBoundarySet hb s hs f ((shilovIdeal_eq_vanishingIdeal S).mp hf)

/-- **The Shilov ideal is the greatest closed boundary ideal.** -/
theorem isGreatest_shilovIdeal (S : Submodule ℂ C(X, ℂ)) (hone : (1 : C(X, ℂ)) ∈ S)
    (hstar : ∀ s ∈ S, star s ∈ S)
    (hsep : ∀ x y : X, x ≠ y → ∃ s ∈ S, (s : C(X, ℂ)) x ≠ s y) :
    (IsClosed (shilovIdeal S : Set C(X, ℂ)) ∧ ∀ s ∈ S, ∀ f ∈ shilovIdeal S, ‖s‖ ≤ ‖s - f‖) ∧
      ∀ I : Ideal C(X, ℂ), IsClosed (I : Set C(X, ℂ)) → (∀ s ∈ S, ∀ f ∈ I, ‖s‖ ≤ ‖s - f‖) →
        ∀ f ∈ I, f ∈ shilovIdeal S :=
  ⟨⟨isClosed_shilovIdeal S, isBoundaryIdeal_shilovIdeal S hone hstar hsep⟩,
    fun I hIc hIb => le_shilovIdeal_of_isBoundaryIdeal S I hIc hIb⟩

end ShilovLocal

end GaloisForLFunctions.HTGeometry
