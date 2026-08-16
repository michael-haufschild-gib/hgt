import GaloisForLFunctions.HTGeometry.FixedEdgeSingletDefect

/-!
# The fixed-edge Hall expansion on the singlet sector

Because the edge images of a singlet are pairwise orthogonal, the sum of all edge commutators has
the same kernel as the whole family.  Rank–nullity for that single map is the Hall inequality: the
dimension of a subspace of the singlet sector is at most the dimension of the span of its edge
images plus the dimension of its intersection with the joint edge kernel.
-/

open Finset Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

variable {I R : Type*} [Fintype I] [DecidableEq I] [Fintype R] [DecidableEq R]

section Hall

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- The linear map of one edge of a labelled family. -/
def edgeMap (lf rf : E → I) (a1 a2 : E → Fin 3) (e : E) :
    EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R) →ₗ[ℂ]
      EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R) :=
  (fixedEdgeCommutatorMatrix I R (lf e) (rf e) (a1 e) (a2 e)).toEuclideanLin

/-- The sum of all edge maps. -/
def edgeSumMap (lf rf : E → I) (a1 a2 : E → Fin 3) :
    EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R) →ₗ[ℂ]
      EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R) :=
  ∑ e : E, edgeMap lf rf a1 a2 e

/-- **On the singlet sector the edge images of one vector are pairwise orthogonal.** -/
theorem inner_edgeMap_eq_zero (lf rf : E → I) (a1 a2 : E → Fin 3)
    (hne : ∀ e, lf e ≠ rf e)
    (hsep : ∀ e f : E, e ≠ f → ∃ v : I, (v = lf e ∨ v = rf e) ∧ v ≠ lf f ∧ v ≠ rf f)
    {x y : EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R)}
    (hx : x ∈ finiteAllReplicaCollectiveSingletSubspace I R)
    (hy : y ∈ finiteAllReplicaCollectiveSingletSubspace I R)
    {e f : E} (hef : e ≠ f) :
    @inner ℂ _ _ (edgeMap lf rf a1 a2 e x) (edgeMap lf rf a1 a2 f y) = 0 := by
  obtain ⟨v, hv, hvl, hvr⟩ := hsep e f hef
  exact inner_fixedEdge_eq_zero_of_separating hv hvl hvr (hne e) _ _ _ _ hx hy

/-- The sum map has the same kernel as the whole edge family. -/
theorem edgeSumMap_apply_eq_zero_iff (lf rf : E → I) (a1 a2 : E → Fin 3)
    (hne : ∀ e, lf e ≠ rf e)
    (hsep : ∀ e f : E, e ≠ f → ∃ v : I, (v = lf e ∨ v = rf e) ∧ v ≠ lf f ∧ v ≠ rf f)
    {x : EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R)}
    (hx : x ∈ finiteAllReplicaCollectiveSingletSubspace I R) :
    edgeSumMap lf rf a1 a2 x = 0 ↔ ∀ e : E, edgeMap lf rf a1 a2 e x = 0 := by
  classical
  constructor
  · intro hzero f
    have hsum : @inner ℂ _ _ (edgeMap lf rf a1 a2 f x) (edgeSumMap lf rf a1 a2 x) = 0 := by
      rw [hzero, inner_zero_right]
    rw [edgeSumMap, LinearMap.sum_apply, inner_sum] at hsum
    rw [Finset.sum_eq_single f (fun e _ hef =>
      inner_edgeMap_eq_zero lf rf a1 a2 hne hsep hx hx (Ne.symm hef))
      (fun hcon => absurd (Finset.mem_univ f) hcon)] at hsum
    exact inner_self_eq_zero.mp hsum
  · intro hall
    rw [edgeSumMap, LinearMap.sum_apply]
    exact Finset.sum_eq_zero fun e _ => hall e

/-- **The all-replica fixed-edge Hall expansion.**

For every subspace of the sitewise singlet sector, its dimension is at most the dimension of the
span of its edge images plus the dimension of its intersection with the joint edge kernel. -/
theorem finrank_le_edgeImages_add_kernel (lf rf : E → I) (a1 a2 : E → Fin 3)
    (hne : ∀ e, lf e ≠ rf e)
    (hsep : ∀ e f : E, e ≠ f → ∃ v : I, (v = lf e ∨ v = rf e) ∧ v ≠ lf f ∧ v ≠ rf f)
    (U : Submodule ℂ (EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R)))
    (hU : U ≤ finiteAllReplicaCollectiveSingletSubspace I R) :
    Module.finrank ℂ U ≤
      Module.finrank ℂ ↥(⨆ e : E, Submodule.map (edgeMap lf rf a1 a2 e) U) +
        Module.finrank ℂ ↥(U ⊓ ⨅ e : E, LinearMap.ker (edgeMap lf rf a1 a2 e)) := by
  classical
  set S : U →ₗ[ℂ] EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R) :=
    (edgeSumMap lf rf a1 a2).comp U.subtype with hS
  have hrn := LinearMap.finrank_range_add_finrank_ker S
  have hrange : LinearMap.range S ≤ ⨆ e : E, Submodule.map (edgeMap lf rf a1 a2 e) U := by
    rintro _ ⟨u, rfl⟩
    have hval : S u = ∑ e : E, edgeMap lf rf a1 a2 e (u : _) := by
      rw [hS, LinearMap.comp_apply, edgeSumMap, LinearMap.sum_apply]
      rfl
    rw [hval]
    refine Submodule.sum_mem _ fun e _ => ?_
    exact Submodule.mem_iSup_of_mem e ⟨u, u.2, rfl⟩
  have hker : LinearMap.ker S =
      (U ⊓ ⨅ e : E, LinearMap.ker (edgeMap lf rf a1 a2 e)).comap U.subtype := by
    ext u
    rw [LinearMap.mem_ker, Submodule.mem_comap, Submodule.mem_inf, Submodule.mem_iInf]
    constructor
    · intro h
      refine ⟨u.2, fun e => ?_⟩
      have := (edgeSumMap_apply_eq_zero_iff lf rf a1 a2 hne hsep (hU u.2)).mp h e
      exact this
    · rintro ⟨-, h⟩
      exact (edgeSumMap_apply_eq_zero_iff lf rf a1 a2 hne hsep (hU u.2)).mpr h
  have hkerrank : Module.finrank ℂ ↥(LinearMap.ker S) =
      Module.finrank ℂ ↥(U ⊓ ⨅ e : E, LinearMap.ker (edgeMap lf rf a1 a2 e)) := by
    rw [hker]
    refine LinearEquiv.finrank_eq ?_
    exact Submodule.comapSubtypeEquivOfLe (by exact inf_le_left)
  rw [← hrn, hkerrank]
  exact Nat.add_le_add_right (Submodule.finrank_mono hrange) _

end Hall

end GaloisForLFunctions.HTGeometry
