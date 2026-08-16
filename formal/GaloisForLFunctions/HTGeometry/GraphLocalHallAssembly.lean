import GaloisForLFunctions.HTGeometry.GraphLocalPauliDetector
import GaloisForLFunctions.HTGeometry.HermitianFamilyCasimirSplit
import GaloisForLFunctions.HTGeometry.VisibleKernelRecoveryHallExpansion

/-!
# Mixed-layer assembly at the canonical obstruction

Inside the orthogonal complement of the simultaneous kernel the canonical greatest obstruction
splits along the sitewise singlet sector.  Its nonsinglet part reproduces itself under the
weight-one generators, its singlet part is detected by the aggregate edge map modulo that
nonsinglet part, and the edge Casimir recovers the hidden detector kernel back inside the singlet
layer.  The two output layers are independent, so one step of the complete local family already
expands the obstruction.
-/

open Finset Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

/-- Visible-rank Hall expansion with both independence conditions taken as hypotheses. -/
theorem visibleKernelRecovery_finrank_of_disjoint {K X Z : Type*} [Field K]
    [AddCommGroup X] [Module K X] [FiniteDimensional K X] [AddCommGroup Z] [Module K Z]
    (Uₛ U_w C Yout : Submodule K X) (F : Uₛ →ₗ[K] Z) (R : LinearMap.ker F →ₗ[K] X)
    (hinput : Disjoint Uₛ U_w)
    (houtput : Disjoint (U_w ⊔ C) (LinearMap.range R))
    (hRinj : Function.Injective R)
    (hvisible : Module.finrank K (LinearMap.range F) + Module.finrank K U_w ≤
      Module.finrank K ((U_w ⊔ C) : Submodule K X))
    (hout : (U_w ⊔ C) ⊔ LinearMap.range R ≤ Yout) :
    Module.finrank K ((Uₛ ⊔ U_w) : Submodule K X) ≤ Module.finrank K Yout := by
  have hin := Submodule.finrank_sup_add_finrank_inf_eq Uₛ U_w
  have hou := Submodule.finrank_sup_add_finrank_inf_eq (U_w ⊔ C) (LinearMap.range R)
  rw [disjoint_iff.mp hinput, finrank_bot] at hin
  rw [disjoint_iff.mp houtput, finrank_bot] at hou
  have hrecover : Module.finrank K (LinearMap.ker F) = Module.finrank K (LinearMap.range R) :=
    LinearEquiv.finrank_eq (LinearEquiv.ofInjective R hRinj)
  have hrankNullity := LinearMap.finrank_range_add_finrank_ker F
  have houtRank : Module.finrank K (((U_w ⊔ C) ⊔ LinearMap.range R) : Submodule K X) ≤
      Module.finrank K Yout := Submodule.finrank_mono hout
  omega

variable {I R : Type*} [Fintype I] [DecidableEq I] [Fintype R] [DecidableEq R]

/-- The weight-one part of the graph-local family. -/
def graphLocalSiteGenerator (I R : Type*) [Fintype I] [DecidableEq I] [Fintype R] [DecidableEq R]
    (G : SimpleGraph I) (q : I × Fin 3) :
    EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R) →ₗ[ℂ]
      EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R) :=
  graphLocalGenerator I R G (Sum.inl q)

/-- The edge part of the graph-local family, as matrices. -/
def graphLocalEdgeMatrix (I R : Type*) [Fintype I] [DecidableEq I] [Fintype R] [DecidableEq R]
    (G : SimpleGraph I) (p : {p : I → Option (Fin 3) // IsEdgeWord G p}) :
    Matrix (FiniteAllReplicaOperatorIndex I R) (FiniteAllReplicaOperatorIndex I R) ℂ :=
  matrixCommutatorRepresentation (collectivePauliString I R p.1)

theorem graphLocalEdgeMatrix_isHermitian (G : SimpleGraph I)
    (p : {p : I → Option (Fin 3) // IsEdgeWord G p}) :
    (graphLocalEdgeMatrix I R G p)ᴴ = graphLocalEdgeMatrix I R G p :=
  matrixCommutatorRepresentation_conjTranspose (collectivePauliString_isHermitian _)

theorem graphLocalGenerator_inr_eq (G : SimpleGraph I)
    (p : {p : I → Option (Fin 3) // IsEdgeWord G p}) :
    graphLocalGenerator I R G (Sum.inr p) = (graphLocalEdgeMatrix I R G p).toEuclideanLin := rfl

theorem graphLocalSiteGenerator_eq (G : SimpleGraph I) (q : I × Fin 3) :
    graphLocalSiteGenerator I R G q =
      (finiteAllReplicaCollectiveCommutatorMatrix I R q.1 q.2).toEuclideanLin :=
  graphLocalGenerator_inl G q.1 q.2

theorem singletSubspace_eq_familyCommonKernel (G : SimpleGraph I) :
    finiteAllReplicaCollectiveSingletSubspace I R =
      familyCommonKernel (graphLocalSiteGenerator I R G) := by
  rw [finiteAllReplicaCollectiveSingletSubspace, hermitianMatrixFamilyCommonKernel,
    familyCommonKernel]
  exact iInf_congr fun q => by rw [graphLocalSiteGenerator_eq]

theorem adjoint_graphLocalSiteGenerator (G : SimpleGraph I) (q : I × Fin 3) :
    LinearMap.adjoint (graphLocalSiteGenerator I R G q) = graphLocalSiteGenerator I R G q :=
  adjoint_graphLocalGenerator G (Sum.inl q)

/-- Every weight-one image is orthogonal to the singlet sector. -/
theorem graphLocalSiteGenerator_mem_singlet_orthogonal (G : SimpleGraph I) (q : I × Fin 3)
    (x : EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R)) :
    graphLocalSiteGenerator I R G q x ∈ (finiteAllReplicaCollectiveSingletSubspace I R)ᗮ := by
  rw [singletSubspace_eq_familyCommonKernel G]
  exact apply_mem_orthogonal_commonKernel (graphLocalSiteGenerator I R G)
    (adjoint_graphLocalSiteGenerator G) q x

/-- Every graph-local image is orthogonal to the simultaneous kernel. -/
theorem graphLocalGenerator_mem_commonKernel_orthogonal (G : SimpleGraph I)
    (j : GraphLocalIndex I G) (x : EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R)) :
    graphLocalGenerator I R G j x ∈ (graphLocalCommonKernel I R G)ᗮ :=
  apply_mem_orthogonal_commonKernel (graphLocalGenerator I R G)
    (adjoint_graphLocalGenerator G) j x

/-- Every weight-one collective commutator preserves the canonical greatest obstruction. -/
theorem graphLocalSiteGenerator_mem_obstruction (G : SimpleGraph I) (q : I × Fin 3)
    {x : EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R)}
    (hx : x ∈ graphLocalObstruction I R G) :
    graphLocalSiteGenerator I R G q x ∈ graphLocalObstruction I R G := by
  obtain ⟨X, rfl⟩ := (vecLinearEquiv (FiniteQubitConfiguration (I × R))).surjective x
  rw [graphLocalSiteGenerator, graphLocalGenerator_apply, graphLocalLabel_inl]
  exact ringCommutator_siteLabel_mem_obstruction G q.1 q.2 hx

/-- The reduced obstruction: the canonical greatest obstruction off the simultaneous kernel. -/
def graphLocalReducedObstruction (I R : Type*) [Fintype I] [DecidableEq I] [Fintype R]
    [DecidableEq R] (G : SimpleGraph I) :
    Submodule ℂ (EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R)) :=
  graphLocalObstruction I R G ⊓ (graphLocalCommonKernel I R G)ᗮ

theorem graphLocalSiteGenerator_mem_reducedObstruction (G : SimpleGraph I) (q : I × Fin 3)
    {x : EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R)}
    (hx : x ∈ graphLocalReducedObstruction I R G) :
    graphLocalSiteGenerator I R G q x ∈ graphLocalReducedObstruction I R G :=
  ⟨graphLocalSiteGenerator_mem_obstruction G q hx.1,
    graphLocalGenerator_mem_commonKernel_orthogonal G (Sum.inl q) x⟩


/-- The weight-one Casimir preserves the reduced obstruction. -/
theorem siteCasimir_mem_reducedObstruction (G : SimpleGraph I)
    {x : EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R)}
    (hx : x ∈ graphLocalReducedObstruction I R G) :
    hermitianFamilyCasimirOperator
        (fun q : I × Fin 3 => finiteAllReplicaCollectiveCommutatorMatrix I R q.1 q.2) x ∈
      graphLocalReducedObstruction I R G := by
  rw [hermitianFamilyCasimirOperator_apply]
  refine Submodule.sum_mem _ fun q _ => ?_
  rw [show ((finiteAllReplicaCollectiveCommutatorMatrix I R q.1 q.2).toEuclideanLin
      ((finiteAllReplicaCollectiveCommutatorMatrix I R q.1 q.2).toEuclideanLin x)) =
      graphLocalSiteGenerator I R G q (graphLocalSiteGenerator I R G q x) by
    rw [graphLocalSiteGenerator_eq]]
  exact graphLocalSiteGenerator_mem_reducedObstruction G q
    (graphLocalSiteGenerator_mem_reducedObstruction G q hx)

/-- **The reduced obstruction splits along the singlet sector.** -/
theorem graphLocalReducedObstruction_le_split (G : SimpleGraph I) :
    graphLocalReducedObstruction I R G ≤
      (graphLocalReducedObstruction I R G ⊓ finiteAllReplicaCollectiveSingletSubspace I R) ⊔
        (graphLocalReducedObstruction I R G ⊓
          (finiteAllReplicaCollectiveSingletSubspace I R)ᗮ) :=
  invariantSubspace_le_commonKernel_sup_orthogonal
    (fun q : I × Fin 3 => finiteAllReplicaCollectiveCommutatorMatrix I R q.1 q.2)
    (fun q => finiteAllReplicaCollectiveCommutatorMatrix_conjTranspose I R q.1 q.2)
    (graphLocalReducedObstruction I R G) (fun _ hx => siteCasimir_mem_reducedObstruction G hx)

theorem linearFamilySquare_siteGenerator_eq (G : SimpleGraph I) :
    linearFamilySquare (graphLocalSiteGenerator I R G) =
      hermitianFamilyCasimirOperator
        (fun q : I × Fin 3 => finiteAllReplicaCollectiveCommutatorMatrix I R q.1 q.2) := by
  rw [linearFamilySquare, hermitianFamilyCasimirOperator]
  exact Finset.sum_congr rfl fun q _ => by rw [graphLocalSiteGenerator_eq]

set_option maxHeartbeats 1000000 in
/-- **The nonsinglet layer of the reduced obstruction reproduces itself in one step.** -/
theorem graphLocalNonsinglet_le_shadow (G : SimpleGraph I) :
    (graphLocalReducedObstruction I R G ⊓ (finiteAllReplicaCollectiveSingletSubspace I R)ᗮ) ≤
      linearFamilyShadow (graphLocalGenerator I R G)
        (graphLocalReducedObstruction I R G ⊓
          (finiteAllReplicaCollectiveSingletSubspace I R)ᗮ) := by
  classical
  have hAU : ∀ q : I × Fin 3, ∀ x ∈ graphLocalReducedObstruction I R G ⊓
      (finiteAllReplicaCollectiveSingletSubspace I R)ᗮ,
      graphLocalSiteGenerator I R G q x ∈ graphLocalReducedObstruction I R G ⊓
        (finiteAllReplicaCollectiveSingletSubspace I R)ᗮ := fun q x hx =>
    ⟨graphLocalSiteGenerator_mem_reducedObstruction G q hx.1,
      graphLocalSiteGenerator_mem_singlet_orthogonal G q x⟩
  have hKinj : Function.Injective ((linearFamilySquare (graphLocalSiteGenerator I R G)).domRestrict
      (graphLocalReducedObstruction I R G ⊓
        (finiteAllReplicaCollectiveSingletSubspace I R)ᗮ)) := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro y hy
    rw [LinearMap.mem_ker, LinearMap.domRestrict_apply,
      linearFamilySquare_siteGenerator_eq] at hy
    have hmemS := (hermitianFamilyCasimir_eq_zero_iff
      (fun q : I × Fin 3 => finiteAllReplicaCollectiveCommutatorMatrix I R q.1 q.2)
      (fun q => finiteAllReplicaCollectiveCommutatorMatrix_conjTranspose I R q.1 q.2) _).mp hy
    have hmemS' : ((y : _) : EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R)) ∈
        finiteAllReplicaCollectiveSingletSubspace I R := hmemS
    have hzeroval : ((y : _) : EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R)) = 0 :=
      (Submodule.mem_bot ℂ).mp
        ((Submodule.orthogonal_disjoint (finiteAllReplicaCollectiveSingletSubspace I R)).le_bot
          ⟨hmemS', y.2.2⟩)
    exact (Submodule.mem_bot ℂ).mpr (Subtype.ext hzeroval)
  refine (invariantSubspace_le_shadow_of_linearFamilySquare_injective
    (graphLocalSiteGenerator I R G) _ hAU hKinj).trans ?_
  refine iSup_le fun q => ?_
  exact le_iSup (fun j => (graphLocalReducedObstruction I R G ⊓
    (finiteAllReplicaCollectiveSingletSubspace I R)ᗮ).map (graphLocalGenerator I R G j))
    (Sum.inl q)

theorem exists_ne_none_of_isEdgeWord {G : SimpleGraph I} {p : I → Option (Fin 3)}
    (hp : IsEdgeWord G p) : ∃ v, p v ≠ none := by
  classical
  obtain ⟨i, j, -, hsupp⟩ := hp
  refine ⟨i, mem_labelSupport.mp ?_⟩
  rw [hsupp]
  exact Finset.mem_insert_self i {j}

/-- Every edge image of a singlet is orthogonal to the singlet sector. -/
theorem graphLocalEdgeGenerator_mem_singlet_orthogonal (G : SimpleGraph I)
    (p : {p : I → Option (Fin 3) // IsEdgeWord G p})
    {x : EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R)}
    (hx : x ∈ finiteAllReplicaCollectiveSingletSubspace I R) :
    graphLocalGenerator I R G (Sum.inr p) x ∈
      (finiteAllReplicaCollectiveSingletSubspace I R)ᗮ := by
  obtain ⟨v, hv⟩ := exists_ne_none_of_isEdgeWord p.2
  rw [Submodule.mem_orthogonal]
  intro u hu
  exact inner_commutator_singlet_eq_zero hv hx hu

/-- The aggregate edge map. -/
def graphLocalEdgeSum (I R : Type*) [Fintype I] [DecidableEq I] [Fintype R] [DecidableEq R]
    (G : SimpleGraph I) :
    EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R) →ₗ[ℂ]
      EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R) :=
  ∑ p : {p : I → Option (Fin 3) // IsEdgeWord G p}, graphLocalGenerator I R G (Sum.inr p)

theorem graphLocalEdgeSum_apply (G : SimpleGraph I)
    (x : EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R)) :
    graphLocalEdgeSum I R G x =
      ∑ p : {p : I → Option (Fin 3) // IsEdgeWord G p},
        graphLocalGenerator I R G (Sum.inr p) x := by
  rw [graphLocalEdgeSum]
  simp

theorem siteConjEquiv_mem_reducedObstruction_inf (G : SimpleGraph I) (v : I) (c : Fin 3)
    {u : EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R)}
    (hu : u ∈ graphLocalReducedObstruction I R G ⊓
      (finiteAllReplicaCollectiveSingletSubspace I R)ᗮ) :
    siteConjEquiv I R v c u ∈ graphLocalReducedObstruction I R G ⊓
      (finiteAllReplicaCollectiveSingletSubspace I R)ᗮ :=
  ⟨⟨siteConjEquiv_mem_obstruction G v c hu.1.1,
      map_familyCommonKernel_orthogonal_le (graphLocalGenerator I R G)
        (adjoint_graphLocalGenerator G) _ (siteConjEquiv_forward G v c) ⟨u, hu.1.2, rfl⟩⟩,
    siteConjEquiv_mem_singlet_orthogonal v c hu.2⟩


theorem linearFamilyShadow_mono {K X Y J : Type*} [DivisionRing K] [AddCommGroup X] [Module K X]
    [AddCommGroup Y] [Module K Y] (A : J → X →ₗ[K] Y) {U V : Submodule K X} (h : U ≤ V) :
    linearFamilyShadow A U ≤ linearFamilyShadow A V :=
  iSup_le fun j => (Submodule.map_mono h).trans (le_iSup (fun k => V.map (A k)) j)

variable (I R)

/-- The singlet layer of the reduced obstruction. -/
def graphLocalSinglet (G : SimpleGraph I) :
    Submodule ℂ (EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R)) :=
  graphLocalReducedObstruction I R G ⊓ finiteAllReplicaCollectiveSingletSubspace I R

/-- The nonsinglet layer of the reduced obstruction. -/
def graphLocalNonsinglet (G : SimpleGraph I) :
    Submodule ℂ (EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R)) :=
  graphLocalReducedObstruction I R G ⊓ (finiteAllReplicaCollectiveSingletSubspace I R)ᗮ

/-- The visible edge output of the singlet layer. -/
def graphLocalVisible (G : SimpleGraph I) :
    Submodule ℂ (EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R)) :=
  ⨆ p : {p : I → Option (Fin 3) // IsEdgeWord G p},
    (graphLocalSinglet I R G).map (graphLocalGenerator I R G (Sum.inr p))

/-- The aggregate edge detector modulo the nonsinglet layer. -/
def graphLocalDetector (G : SimpleGraph I) :
    graphLocalSinglet I R G →ₗ[ℂ]
      (EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R) ⧸ graphLocalNonsinglet I R G) :=
  (((graphLocalNonsinglet I R G).mkQ).comp (graphLocalEdgeSum I R G)).comp
    (graphLocalSinglet I R G).subtype

/-- Quadratic edge recovery of the detector kernel. -/
def graphLocalRecovery (G : SimpleGraph I) :
    LinearMap.ker (graphLocalDetector I R G) →ₗ[ℂ]
      EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R) :=
  (hermitianFamilyCasimirOperator (graphLocalEdgeMatrix I R G)).comp
    ((graphLocalSinglet I R G).subtype.comp
      (LinearMap.ker (graphLocalDetector I R G)).subtype)

variable {I R}

theorem graphLocalDetector_apply (G : SimpleGraph I) (s : graphLocalSinglet I R G) :
    graphLocalDetector I R G s =
      (graphLocalNonsinglet I R G).mkQ (graphLocalEdgeSum I R G (s : _)) := rfl

theorem graphLocalRecovery_apply (G : SimpleGraph I)
    (y : LinearMap.ker (graphLocalDetector I R G)) :
    graphLocalRecovery I R G y =
      hermitianFamilyCasimirOperator (graphLocalEdgeMatrix I R G)
        (y.1.1 : EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R)) := rfl

theorem graphLocalSinglet_le_singlet (G : SimpleGraph I) :
    graphLocalSinglet I R G ≤ finiteAllReplicaCollectiveSingletSubspace I R := fun _ hx => hx.2

theorem graphLocalSinglet_le_reduced (G : SimpleGraph I) :
    graphLocalSinglet I R G ≤ graphLocalReducedObstruction I R G := fun _ hx => hx.1

theorem graphLocalNonsinglet_le_reduced (G : SimpleGraph I) :
    graphLocalNonsinglet I R G ≤ graphLocalReducedObstruction I R G := fun _ hx => hx.1

/-- Every detector-kernel direction sends each edge image into the nonsinglet layer. -/
theorem graphLocalDetector_ker_edge_mem (G : SimpleGraph I)
    (y : LinearMap.ker (graphLocalDetector I R G))
    (p : {p : I → Option (Fin 3) // IsEdgeWord G p}) :
    graphLocalGenerator I R G (Sum.inr p)
        (y.1.1 : EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R)) ∈
      graphLocalNonsinglet I R G := by
  classical
  have hker : graphLocalDetector I R G y.1 = 0 := LinearMap.mem_ker.mp y.2
  rw [graphLocalDetector_apply] at hker
  have hsum : graphLocalEdgeSum I R G
      (y.1.1 : EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R)) ∈
      graphLocalNonsinglet I R G := (Submodule.Quotient.mk_eq_zero _).mp hker
  rw [graphLocalEdgeSum_apply] at hsum
  exact edgeImage_mem_of_sum_mem G
    (fun v c u hu => siteConjEquiv_mem_reducedObstruction_inf G v c hu) y.1.2.2 hsum p

set_option maxHeartbeats 1000000 in
theorem graphLocalRecovery_range_le (G : SimpleGraph I) :
    LinearMap.range (graphLocalRecovery I R G) ≤
      linearFamilyShadow (graphLocalGenerator I R G) (graphLocalNonsinglet I R G) := by
  classical
  rintro _ ⟨y, rfl⟩
  rw [graphLocalRecovery_apply, hermitianFamilyCasimirOperator_apply]
  refine Submodule.sum_mem _ fun p _ => ?_
  exact le_iSup
    (fun j => (graphLocalNonsinglet I R G).map (graphLocalGenerator I R G j)) (Sum.inr p)
    ⟨_, graphLocalDetector_ker_edge_mem G y p, rfl⟩

set_option maxHeartbeats 1000000 in
theorem graphLocalRecovery_injective (G : SimpleGraph I) :
    Function.Injective (graphLocalRecovery I R G) := by
  classical
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro y hy
  have hzero : hermitianFamilyCasimirOperator (graphLocalEdgeMatrix I R G)
      (y.1.1 : EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R)) = 0 := by
    have := LinearMap.mem_ker.mp hy
    rwa [graphLocalRecovery_apply] at this
  have hedge := (hermitianFamilyCasimir_eq_zero_iff (graphLocalEdgeMatrix I R G)
    (graphLocalEdgeMatrix_isHermitian G) _).mp hzero
  rw [hermitianMatrixFamilyCommonKernel, Submodule.mem_iInf] at hedge
  have hsite : (y.1.1 : EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R)) ∈
      finiteAllReplicaCollectiveSingletSubspace I R := y.1.2.2
  rw [singletSubspace_eq_familyCommonKernel G, mem_familyCommonKernel] at hsite
  have hN : (y.1.1 : EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R)) ∈
      graphLocalCommonKernel I R G := by
    rw [graphLocalCommonKernel, mem_familyCommonKernel]
    rintro (q | p)
    · exact hsite q
    · exact LinearMap.mem_ker.mp (hedge p)
  have hzeroval : (y.1.1 : EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R)) = 0 :=
    (Submodule.mem_bot ℂ).mp
      ((Submodule.orthogonal_disjoint (graphLocalCommonKernel I R G)).le_bot
        ⟨hN, y.1.2.1.2⟩)
  exact (Submodule.mem_bot ℂ).mpr (Subtype.ext (Subtype.ext hzeroval))

theorem graphLocalVisible_le_singlet_orthogonal (G : SimpleGraph I) :
    graphLocalNonsinglet I R G ⊔ graphLocalVisible I R G ≤
      (finiteAllReplicaCollectiveSingletSubspace I R)ᗮ := by
  refine sup_le (fun _ hx => hx.2) (iSup_le fun p => ?_)
  rintro _ ⟨z, hz, rfl⟩
  exact graphLocalEdgeGenerator_mem_singlet_orthogonal G p hz.2

set_option maxHeartbeats 1000000 in
theorem graphLocalRecovery_disjoint (G : SimpleGraph I) :
    Disjoint (graphLocalNonsinglet I R G ⊔ graphLocalVisible I R G)
      (LinearMap.range (graphLocalRecovery I R G)) := by
  classical
  rw [disjoint_iff, eq_bot_iff]
  rintro w ⟨hw1, y, rfl⟩
  rw [graphLocalRecovery_apply] at hw1 ⊢
  have hzS : (y.1.1 : EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R)) ∈
      finiteAllReplicaCollectiveSingletSubspace I R := y.1.2.2
  have hinner : (inner ℂ (y.1.1 : EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R))
      (hermitianFamilyCasimirOperator (graphLocalEdgeMatrix I R G)
        (y.1.1 : EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R))) : ℂ) = 0 :=
    (Submodule.mem_orthogonal _ _).mp (graphLocalVisible_le_singlet_orthogonal G hw1) _ hzS
  have hker := mem_commonKernel_of_inner_hermitianFamilyCasimir_eq_zero
    (graphLocalEdgeMatrix I R G) (graphLocalEdgeMatrix_isHermitian G) _ hinner
  exact (Submodule.mem_bot ℂ).mpr
    ((hermitianFamilyCasimir_eq_zero_iff _ (graphLocalEdgeMatrix_isHermitian G) _).mpr hker)

theorem graphLocalLayers_disjoint (G : SimpleGraph I) :
    Disjoint (graphLocalSinglet I R G) (graphLocalNonsinglet I R G) := by
  rw [disjoint_iff, eq_bot_iff]
  rintro x ⟨hx1, hx2⟩
  exact (Submodule.orthogonal_disjoint
    (finiteAllReplicaCollectiveSingletSubspace I R)).le_bot ⟨hx1.2, hx2.2⟩

set_option maxHeartbeats 1000000 in
theorem graphLocalDetector_visible_finrank (G : SimpleGraph I) :
    Module.finrank ℂ (LinearMap.range (graphLocalDetector I R G)) +
        Module.finrank ℂ (graphLocalNonsinglet I R G) ≤
      Module.finrank ℂ ((graphLocalNonsinglet I R G ⊔ graphLocalVisible I R G :
        Submodule ℂ (EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R)))) := by
  classical
  refine visibleQuotientDetector_finrank (graphLocalSinglet I R G) (graphLocalNonsinglet I R G)
    (graphLocalVisible I R G) (graphLocalDetector I R G)
    (LinearMap.range (graphLocalDetector I R G)).subtype (Submodule.injective_subtype _) ?_
  rw [Submodule.range_subtype]
  rintro _ ⟨s, rfl⟩
  rw [graphLocalDetector_apply]
  refine ⟨graphLocalEdgeSum I R G ((s : _)), Submodule.mem_sup_right ?_, rfl⟩
  rw [graphLocalEdgeSum_apply]
  refine Submodule.sum_mem _ fun p _ => ?_
  exact le_iSup
    (fun p' => (graphLocalSinglet I R G).map (graphLocalGenerator I R G (Sum.inr p'))) p
    ⟨_, s.2, rfl⟩

set_option maxHeartbeats 1000000 in
/-- **One step of the complete graph-local family expands the reduced obstruction.** -/
theorem graphLocalReducedObstruction_finrank_le (G : SimpleGraph I) :
    Module.finrank ℂ (graphLocalReducedObstruction I R G) ≤
      Module.finrank ℂ (linearFamilyShadow (graphLocalGenerator I R G)
        (graphLocalReducedObstruction I R G)) := by
  classical
  have hout : (graphLocalNonsinglet I R G ⊔ graphLocalVisible I R G) ⊔
      LinearMap.range (graphLocalRecovery I R G) ≤
      linearFamilyShadow (graphLocalGenerator I R G) (graphLocalReducedObstruction I R G) := by
    refine sup_le (sup_le ?_ ?_) ?_
    · exact (graphLocalNonsinglet_le_shadow G).trans
        (linearFamilyShadow_mono _ (graphLocalNonsinglet_le_reduced G))
    · refine iSup_le fun p => ?_
      exact (Submodule.map_mono (graphLocalSinglet_le_reduced G)).trans
        (le_iSup (fun j => (graphLocalReducedObstruction I R G).map
          (graphLocalGenerator I R G j)) (Sum.inr p))
    · exact (graphLocalRecovery_range_le G).trans
        (linearFamilyShadow_mono _ (graphLocalNonsinglet_le_reduced G))
  have hfin := visibleKernelRecovery_finrank_of_disjoint (graphLocalSinglet I R G)
    (graphLocalNonsinglet I R G) (graphLocalVisible I R G)
    (linearFamilyShadow (graphLocalGenerator I R G) (graphLocalReducedObstruction I R G))
    (graphLocalDetector I R G) (graphLocalRecovery I R G) (graphLocalLayers_disjoint G)
    (graphLocalRecovery_disjoint G) (graphLocalRecovery_injective G)
    (graphLocalDetector_visible_finrank G) hout
  exact le_trans (Submodule.finrank_mono (graphLocalReducedObstruction_le_split G)) hfin

end GaloisForLFunctions.HTGeometry
