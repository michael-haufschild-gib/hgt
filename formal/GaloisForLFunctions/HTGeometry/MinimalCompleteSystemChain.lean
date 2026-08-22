import GaloisForLFunctions.HTGeometry.MinimalCompleteSystem
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Data.EReal.Basic

/-!
# The minimality and completeness indices of a decreasing chain of subspaces

Burnol, *Two complete and minimal systems associated with the zeros of the Riemann zeta function*
(arXiv:math/0203120), opens §7 with the following observation.  The Sonine spaces `K_a` form a
decreasing chain and the evaluators attached to a multiset `Z` in `K_a` project orthogonally onto
the evaluators in `K_b` for `b ≥ a`.  Consequently

* minimality of the system is a *downward closed* condition in `a`, and
* completeness of the system is an *upward closed* condition in `a`,

so that two indices `a₁(Z), a₂(Z) ∈ [0, +∞]` are well defined: the system is minimal for
`a < a₁(Z)` and not minimal for `a > a₁(Z)`, complete for `a > a₂(Z)` and not complete for
`a < a₂(Z)`.

This file proves that structure unconditionally, for an arbitrary antitone family of subspaces of
a Hilbert space with orthogonal projections and an arbitrary base system of vectors.  The two
transfer lemmas are exactly the arguments Burnol uses in the proofs of Prop. 6.4 (minimality of the
projected system forces minimality upstairs) and Prop. 6.6 (completeness is pushed down the chain).

## Main results

* `isCompleteSystemIn_starProjection` — completeness transfers along an orthogonal projection.
* `isMinimalSystem_starProjection_of_le`, `isCompleteSystemIn_starProjection_of_le` — the two
  monotonicity statements along the chain.
* `isLowerSet_minimalIndexSet`, `isUpperSet_completeIndexSet`.
* `mem_minimalIndexSet_of_lt_minimalIndex`, `notMem_minimalIndexSet_of_minimalIndex_lt`,
  `mem_completeIndexSet_of_completeIndex_lt`, `notMem_completeIndexSet_of_lt_completeIndex` —
  the defining properties of the two indices.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped InnerProductSpace

variable (𝕜 : Type*) {E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- A system of vectors is **complete in the subspace `S`** when its closed linear span is `S`. -/
def IsCompleteSystemIn (S : Submodule 𝕜 E) (u : ι → E) : Prop :=
  (Submodule.span 𝕜 (Set.range u)).topologicalClosure = S

variable {𝕜}

theorem isClosed_of_hasOrthogonalProjection (S : Submodule 𝕜 E) [S.HasOrthogonalProjection] :
    IsClosed (S : Set E) := by
  have h := Submodule.isClosed_orthogonal (K := (Sᗮ : Submodule 𝕜 E))
  rwa [Submodule.orthogonal_orthogonal] at h

/-- **Completeness transfers along an orthogonal projection** (Burnol, proof of Prop. 6.6).  If a
system is complete in `T` and `S ≤ T`, then its orthogonal projection onto `S` is complete in
`S`. -/
theorem isCompleteSystemIn_starProjection {S T : Submodule 𝕜 E} [S.HasOrthogonalProjection]
    (hST : S ≤ T) {u : ι → E} (h : IsCompleteSystemIn 𝕜 T u) :
    IsCompleteSystemIn 𝕜 S fun i => S.starProjection (u i) := by
  set W : Submodule 𝕜 E :=
    (Submodule.span 𝕜 (Set.range fun i => S.starProjection (u i))).topologicalClosure with hW
  have hWS : W ≤ S := by
    refine Submodule.topologicalClosure_minimal _ ?_ (isClosed_of_hasOrthogonalProjection S)
    rw [Submodule.span_le]
    rintro y ⟨i, rfl⟩
    exact S.starProjection_apply_mem _
  have hSW : S ≤ W := by
    have hcomap : T ≤ W.comap (S.starProjection : E →ₗ[𝕜] E) := by
      rw [← h]
      refine Submodule.topologicalClosure_minimal _ ?_ ?_
      · rw [Submodule.span_le]
        rintro y ⟨i, rfl⟩
        exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨i, rfl⟩)
      · exact (Submodule.isClosed_topologicalClosure _).preimage
          (Submodule.starProjection S).continuous
    intro x hx
    have hxT : x ∈ T := hST hx
    have hproj := hcomap hxT
    simp only [Submodule.mem_comap, ContinuousLinearMap.coe_coe,
      Submodule.starProjection_eq_self_iff.2 hx] at hproj
    exact hproj
  exact le_antisymm hWS hSW

/-- **Minimality of a projected system forces minimality upstairs** (Burnol, proof of
Prop. 6.4). -/
theorem IsMinimalSystem.of_starProjection (S : Submodule 𝕜 E) [S.HasOrthogonalProjection]
    {u : ι → E} (h : IsMinimalSystem 𝕜 fun i => S.starProjection (u i)) :
    IsMinimalSystem 𝕜 u :=
  IsMinimalSystem.of_continuousLinearMap (Submodule.starProjection S) h

/-- Minimality travels **up** the chain: minimality of the system projected to the smaller space
forces minimality of the system projected to the larger one. -/
theorem isMinimalSystem_starProjection_of_le {S T : Submodule 𝕜 E}
    [S.HasOrthogonalProjection] [T.HasOrthogonalProjection] (hST : S ≤ T) {u : ι → E}
    (h : IsMinimalSystem 𝕜 fun i => S.starProjection (u i)) :
    IsMinimalSystem 𝕜 fun i => T.starProjection (u i) := by
  refine IsMinimalSystem.of_starProjection S ?_
  have hcomp : ∀ x : E, S.starProjection (T.starProjection x) = S.starProjection x := fun x =>
    congrArg (fun L : E →L[𝕜] E => L x) (Submodule.starProjection_comp_starProjection_of_le hST)
  simpa [hcomp] using h

/-- Completeness travels **down** the chain: completeness of the system projected to the larger
space forces completeness of the system projected to the smaller one. -/
theorem isCompleteSystemIn_starProjection_of_le {S T : Submodule 𝕜 E}
    [S.HasOrthogonalProjection] [T.HasOrthogonalProjection] (hST : S ≤ T) {u : ι → E}
    (h : IsCompleteSystemIn 𝕜 T fun i => T.starProjection (u i)) :
    IsCompleteSystemIn 𝕜 S fun i => S.starProjection (u i) := by
  have hcomp : ∀ x : E, S.starProjection (T.starProjection x) = S.starProjection x := fun x =>
    congrArg (fun L : E →L[𝕜] E => L x) (Submodule.starProjection_comp_starProjection_of_le hST)
  have := isCompleteSystemIn_starProjection (S := S) (T := T) hST h
  simpa [hcomp] using this

/-! ### The two indices -/

variable (K : ℝ → Submodule 𝕜 E) (u : ι → E)

/-- The set of parameters at which the projected system is minimal. -/
def minimalIndexSet [∀ a, (K a).HasOrthogonalProjection] : Set ℝ :=
  {a : ℝ | IsMinimalSystem 𝕜 fun i => (K a).starProjection (u i)}

/-- The set of parameters at which the projected system is complete. -/
def completeIndexSet [∀ a, (K a).HasOrthogonalProjection] : Set ℝ :=
  {a : ℝ | IsCompleteSystemIn 𝕜 (K a) fun i => (K a).starProjection (u i)}

variable [∀ a, (K a).HasOrthogonalProjection]

/-- Minimality is a downward closed condition along a decreasing chain. -/
theorem isLowerSet_minimalIndexSet (hK : Antitone K) :
    IsLowerSet (minimalIndexSet K u) := by
  intro b a hab hb
  exact isMinimalSystem_starProjection_of_le (hK hab) hb

/-- Completeness is an upward closed condition along a decreasing chain. -/
theorem isUpperSet_completeIndexSet (hK : Antitone K) :
    IsUpperSet (completeIndexSet K u) := by
  intro a b hab ha
  exact isCompleteSystemIn_starProjection_of_le (hK hab) ha

/-- Burnol's index `a₁(Z)`: the supremum of the parameters at which the system is minimal. -/
noncomputable def minimalIndex : EReal :=
  sSup ((fun a : ℝ => (a : EReal)) '' minimalIndexSet K u)

/-- Burnol's index `a₂(Z)`: the infimum of the parameters at which the system is complete. -/
noncomputable def completeIndex : EReal :=
  sInf ((fun a : ℝ => (a : EReal)) '' completeIndexSet K u)

variable {K u}

theorem le_minimalIndex_of_mem {a : ℝ} (ha : a ∈ minimalIndexSet K u) :
    (a : EReal) ≤ minimalIndex K u :=
  le_sSup ⟨a, ha, rfl⟩

theorem completeIndex_le_of_mem {a : ℝ} (ha : a ∈ completeIndexSet K u) :
    completeIndex K u ≤ (a : EReal) :=
  sInf_le ⟨a, ha, rfl⟩

/-- Below the index `a₁(Z)` the system is minimal. -/
theorem mem_minimalIndexSet_of_lt_minimalIndex (hK : Antitone K) {a : ℝ}
    (ha : (a : EReal) < minimalIndex K u) : a ∈ minimalIndexSet K u := by
  obtain ⟨y, hy, hay⟩ := lt_sSup_iff.1 ha
  obtain ⟨b, hb, rfl⟩ := hy
  exact isLowerSet_minimalIndexSet K u hK (le_of_lt (EReal.coe_lt_coe_iff.1 hay)) hb

/-- Above the index `a₁(Z)` the system is not minimal. -/
theorem notMem_minimalIndexSet_of_minimalIndex_lt {a : ℝ}
    (ha : minimalIndex K u < (a : EReal)) : a ∉ minimalIndexSet K u := fun h =>
  absurd (le_minimalIndex_of_mem h) (not_le.2 ha)

/-- Above the index `a₂(Z)` the system is complete. -/
theorem mem_completeIndexSet_of_completeIndex_lt (hK : Antitone K) {a : ℝ}
    (ha : completeIndex K u < (a : EReal)) : a ∈ completeIndexSet K u := by
  obtain ⟨y, hy, hya⟩ := sInf_lt_iff.1 ha
  obtain ⟨b, hb, rfl⟩ := hy
  exact isUpperSet_completeIndexSet K u hK (le_of_lt (EReal.coe_lt_coe_iff.1 hya)) hb

/-- Below the index `a₂(Z)` the system is not complete. -/
theorem notMem_completeIndexSet_of_lt_completeIndex {a : ℝ}
    (ha : (a : EReal) < completeIndex K u) : a ∉ completeIndexSet K u := fun h =>
  absurd (completeIndex_le_of_mem h) (not_le.2 ha)

end GaloisForLFunctions.HTGeometry
