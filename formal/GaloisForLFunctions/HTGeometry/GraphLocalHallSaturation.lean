import GaloisForLFunctions.HTGeometry.GraphLocalHallAssembly
import GaloisForLFunctions.HTGeometry.FixedEdgeSingletStableRange

/-!
# One-step Hall saturation of the complete graph-local Pauli family

Adjoining the projector onto the simultaneous kernel turns the sharp Hall law of the graph-local
collective Pauli family into an ordinary Hall condition, and the canonical greatest obstruction of
the completed family has nonpositive deficiency by the mixed-layer assembly.  Hence every subspace
orthogonal to the simultaneous kernel expands in one step, and an arbitrary subspace expands after
paying exactly its intersection with that kernel.
-/

open Finset Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

/-- Rank–nullity in the form used for splitting off a projector image. -/
theorem finrank_inf_ker_add_finrank_map {K M : Type*} [DivisionRing K] [AddCommGroup M]
    [Module K M] [FiniteDimensional K M] (f : M →ₗ[K] M) (U : Submodule K M) :
    Module.finrank K ((U ⊓ LinearMap.ker f : Submodule K M)) +
      Module.finrank K (U.map f) = Module.finrank K U := by
  have hrn := LinearMap.finrank_range_add_finrank_ker (f.domRestrict U)
  rw [LinearMap.range_domRestrict] at hrn
  have hker : LinearMap.ker (f.domRestrict U) =
      Submodule.comap U.subtype (U ⊓ LinearMap.ker f) := by
    rw [Submodule.comap_inf, Submodule.comap_subtype_self, top_inf_eq]
    exact LinearMap.ker_comp U.subtype f
  have hequiv : Module.finrank K (LinearMap.ker (f.domRestrict U)) =
      Module.finrank K ((U ⊓ LinearMap.ker f : Submodule K M)) := by
    rw [hker]
    exact LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe inf_le_left)
  omega

variable (I R : Type*) [Fintype I] [DecidableEq I] [Fintype R] [DecidableEq R]

/-- The orthogonal projector onto the exact collective commutant, as a linear map. -/
def graphLocalKernelProjection (G : SimpleGraph I) :
    EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R) →ₗ[ℂ]
      EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R) :=
  (graphLocalCommonKernel I R G).starProjection

/-- The orthogonal projector onto the complement of the exact collective commutant. -/
def graphLocalComplementProjection (G : SimpleGraph I) :
    EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R) →ₗ[ℂ]
      EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R) :=
  (graphLocalCommonKernel I R G)ᗮ.starProjection

variable {I R}

theorem ker_graphLocalKernelProjection (G : SimpleGraph I) :
    LinearMap.ker (graphLocalKernelProjection I R G) = (graphLocalCommonKernel I R G)ᗮ := by
  ext x
  rw [LinearMap.mem_ker]
  exact Submodule.starProjection_apply_eq_zero_iff _

theorem ker_graphLocalComplementProjection (G : SimpleGraph I) :
    LinearMap.ker (graphLocalComplementProjection I R G) = graphLocalCommonKernel I R G := by
  ext x
  rw [LinearMap.mem_ker]
  rw [show graphLocalComplementProjection I R G x =
    (graphLocalCommonKernel I R G)ᗮ.starProjection x from rfl,
    Submodule.starProjection_apply_eq_zero_iff, Submodule.orthogonal_orthogonal]

theorem map_graphLocalKernelProjection_le (G : SimpleGraph I)
    (U : Submodule ℂ (EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R))) :
    U.map (graphLocalKernelProjection I R G) ≤ graphLocalCommonKernel I R G := by
  rintro _ ⟨x, -, rfl⟩
  exact (graphLocalCommonKernel I R G).starProjection_apply_mem x

theorem map_graphLocalComplementProjection_le (G : SimpleGraph I)
    (U : Submodule ℂ (EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R))) :
    U.map (graphLocalComplementProjection I R G) ≤ (graphLocalCommonKernel I R G)ᗮ := by
  rintro _ ⟨x, -, rfl⟩
  exact (graphLocalCommonKernel I R G)ᗮ.starProjection_apply_mem x

theorem linearFamilyShadow_completed_eq (G : SimpleGraph I)
    (U : Submodule ℂ (EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R))) :
    linearFamilyShadow (graphLocalCompleted I R G) U =
      linearFamilyShadow (graphLocalGenerator I R G) U ⊔
        U.map (graphLocalKernelProjection I R G) :=
  linearFamilyShadow_completed G U

set_option maxHeartbeats 1000000 in
/-- The canonical greatest obstruction of the completed family has nonpositive deficiency. -/
theorem graphLocalCompleted_defect_nonpos (G : SimpleGraph I) :
    linearFamilyDefect (graphLocalCompleted I R G)
      (linearFamilyGreatestMaximizer (graphLocalCompleted I R G)) ≤ 0 := by
  classical
  have hdisj : Disjoint
      (linearFamilyShadow (graphLocalGenerator I R G) (graphLocalObstruction I R G))
      ((graphLocalObstruction I R G).map (graphLocalKernelProjection I R G)) :=
    ((Submodule.orthogonal_disjoint (graphLocalCommonKernel I R G)).symm).mono
      (linearFamilyShadow_le_commonKernel_orthogonal G _)
      (map_graphLocalKernelProjection_le G _)
  have hsum : Module.finrank ℂ
      ((linearFamilyShadow (graphLocalGenerator I R G) (graphLocalObstruction I R G) ⊔
        (graphLocalObstruction I R G).map (graphLocalKernelProjection I R G) :
          Submodule ℂ (EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R)))) =
      Module.finrank ℂ
        (linearFamilyShadow (graphLocalGenerator I R G) (graphLocalObstruction I R G)) +
      Module.finrank ℂ ((graphLocalObstruction I R G).map
        (graphLocalKernelProjection I R G)) := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq
      (linearFamilyShadow (graphLocalGenerator I R G) (graphLocalObstruction I R G))
      ((graphLocalObstruction I R G).map (graphLocalKernelProjection I R G))
    rw [disjoint_iff.mp hdisj, finrank_bot] at h
    omega
  have hsplit : Module.finrank ℂ (graphLocalReducedObstruction I R G) +
      Module.finrank ℂ ((graphLocalObstruction I R G).map
        (graphLocalKernelProjection I R G)) =
      Module.finrank ℂ (graphLocalObstruction I R G) := by
    have h := finrank_inf_ker_add_finrank_map (graphLocalKernelProjection I R G)
      (graphLocalObstruction I R G)
    rw [ker_graphLocalKernelProjection G] at h
    exact h
  have hred := graphLocalReducedObstruction_finrank_le (I := I) (R := R) G
  have hmono : Module.finrank ℂ (linearFamilyShadow (graphLocalGenerator I R G)
      (graphLocalReducedObstruction I R G)) ≤
      Module.finrank ℂ (linearFamilyShadow (graphLocalGenerator I R G)
        (graphLocalObstruction I R G)) :=
    Submodule.finrank_mono (linearFamilyShadow_mono _ inf_le_left)
  have hkey : Module.finrank ℂ (graphLocalObstruction I R G) ≤
      Module.finrank ℂ (linearFamilyShadow (graphLocalCompleted I R G)
        (graphLocalObstruction I R G)) := by
    rw [linearFamilyShadow_completed_eq, hsum]
    omega
  rw [linearFamilyDefect]
  rw [graphLocalObstruction] at hkey
  omega

/-- **The completed graph-local family satisfies the Hall condition.** -/
theorem graphLocalCompleted_hall (G : SimpleGraph I) :
    LinearFamilyHall (graphLocalCompleted I R G) := by
  rw [linearFamilyHall_iff_greatestMaximizer_defect_eq_zero]
  have hle := graphLocalCompleted_defect_nonpos (I := I) (R := R) G
  have hge : (0 : ℤ) ≤ linearFamilyDefect (graphLocalCompleted I R G)
      (linearFamilyGreatestMaximizer (graphLocalCompleted I R G)) := by
    have hbot := linearFamilyDefect_le_greatestMaximizer (graphLocalCompleted I R G) ⊥
    rwa [linearFamilyDefect_bot] at hbot
  omega

/-- **Equation (9): one step of the complete graph-local Pauli family expands every subspace
orthogonal to the exact collective commutant.** -/
theorem graphLocal_finrank_le_shadow_of_le_orthogonal (G : SimpleGraph I)
    (U : Submodule ℂ (EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R)))
    (hU : U ≤ (graphLocalCommonKernel I R G)ᗮ) :
    Module.finrank ℂ U ≤
      Module.finrank ℂ (linearFamilyShadow (graphLocalGenerator I R G) U) := by
  classical
  have h := graphLocalCompleted_hall G U
  rw [linearFamilyShadow_completed_eq] at h
  have hzero : U.map (graphLocalKernelProjection I R G) = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨x, hx, rfl⟩
    exact (Submodule.mem_bot ℂ).mpr
      ((Submodule.starProjection_apply_eq_zero_iff _).mpr (hU hx))
  rw [hzero, sup_bot_eq] at h
  exact h

set_option maxHeartbeats 1000000 in
/-- **Equation (8): the sharp one-step Hall law, paying exactly the intersection with the exact
collective commutant.** -/
theorem graphLocal_finrank_le_shadow_add_commonKernel (G : SimpleGraph I)
    (U : Submodule ℂ (EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R))) :
    Module.finrank ℂ U ≤
      Module.finrank ℂ (linearFamilyShadow (graphLocalGenerator I R G) U) +
        Module.finrank ℂ ((U ⊓ graphLocalCommonKernel I R G :
          Submodule ℂ (EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R)))) := by
  classical
  have happ : ∀ (j : GraphLocalIndex I G)
      (x : EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R)),
      graphLocalGenerator I R G j (graphLocalComplementProjection I R G x) =
        graphLocalGenerator I R G j x := by
    intro j x
    have hmem : x - graphLocalComplementProjection I R G x ∈ graphLocalCommonKernel I R G := by
      have h := Submodule.sub_starProjection_mem_orthogonal
        (K := (graphLocalCommonKernel I R G)ᗮ) x
      rwa [Submodule.orthogonal_orthogonal] at h
    have hzero : graphLocalGenerator I R G j
        (x - graphLocalComplementProjection I R G x) = 0 :=
      (mem_graphLocalCommonKernel G).mp hmem j
    rw [map_sub, sub_eq_zero] at hzero
    exact hzero.symm
  have hmapeq : ∀ j : GraphLocalIndex I G,
      (U.map (graphLocalComplementProjection I R G)).map (graphLocalGenerator I R G j) =
        U.map (graphLocalGenerator I R G j) := by
    intro j
    refine le_antisymm ?_ ?_
    · rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, (happ j x).symm⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact ⟨graphLocalComplementProjection I R G x, ⟨x, hx, rfl⟩, happ j x⟩
  have hshadoweq : linearFamilyShadow (graphLocalGenerator I R G)
      (U.map (graphLocalComplementProjection I R G)) =
      linearFamilyShadow (graphLocalGenerator I R G) U := by
    rw [linearFamilyShadow, linearFamilyShadow]
    exact iSup_congr hmapeq
  have hhall := graphLocal_finrank_le_shadow_of_le_orthogonal G
    (U.map (graphLocalComplementProjection I R G)) (map_graphLocalComplementProjection_le G U)
  rw [hshadoweq] at hhall
  have hsplit := finrank_inf_ker_add_finrank_map (graphLocalComplementProjection I R G) U
  rw [ker_graphLocalComplementProjection G] at hsplit
  omega

set_option maxHeartbeats 1000000 in
/-- **On a connected graph the simultaneous kernel is the exact global collective commutant.** -/
theorem graphLocalCommonKernel_eq_collectiveCommutant (G : SimpleGraph I) (hconn : G.Connected) :
    graphLocalCommonKernel I R G = collectiveCommutantSubspace I R := by
  classical
  refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
  · rw [mem_graphLocalCommonKernel] at hx
    have hs : x ∈ finiteAllReplicaCollectiveSingletSubspace I R := by
      refine mem_singlet_iff.mpr fun v a => ?_
      have h := hx (Sum.inl (v, a))
      rwa [graphLocalGenerator_inl] at h
    rw [mem_collectiveCommutantSubspace_iff]
    refine collectivePauliString_commutator_apply_eq_zero G hconn hs ?_
    intro i j hadj a b
    have hp : IsEdgeWord G (pairLabel i j a b) :=
      ⟨i, j, hadj, labelSupport_pairLabel hadj.ne a b⟩
    have h := hx (Sum.inr ⟨pairLabel i j a b, hp⟩)
    rw [graphLocalGenerator, graphLocalLabel_inr] at h
    rwa [fixedEdgeCommutatorMatrix, ← collectivePauliString_pairLabel hadj.ne]
  · rw [mem_graphLocalCommonKernel]
    rw [mem_collectiveCommutantSubspace_iff] at hx
    rintro (q | p)
    · rw [graphLocalGenerator, graphLocalLabel_inl]
      exact hx (siteLabel q.1 q.2)
    · rw [graphLocalGenerator, graphLocalLabel_inr]
      exact hx p.1

/-- **Equation (30): the stable-range form of the sharp Hall law.** -/
theorem graphLocal_finrank_le_shadow_add_factorial (G : SimpleGraph I) (hconn : G.Connected)
    (hrd : Fintype.card R ≤ Fintype.card (FiniteQubitConfiguration I))
    (U : Submodule ℂ (EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R))) :
    Module.finrank ℂ U ≤
      Module.finrank ℂ (linearFamilyShadow (graphLocalGenerator I R G) U) +
        Nat.factorial (Fintype.card R) := by
  have h := graphLocal_finrank_le_shadow_add_commonKernel G U
  have h2 : Module.finrank ℂ ((U ⊓ graphLocalCommonKernel I R G :
      Submodule ℂ (EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R)))) ≤
      Nat.factorial (Fintype.card R) := by
    rw [graphLocalCommonKernel_eq_collectiveCommutant G hconn]
    exact le_trans (Submodule.finrank_mono inf_le_right)
      (finrank_collectiveCommutantSubspace_le_factorial hrd)
  omega

end GaloisForLFunctions.HTGeometry
