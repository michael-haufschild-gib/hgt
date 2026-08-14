import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.Algebra.ContinuousAffineMap
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.MetricSpace.Basic

/-!
# Asymptotic law cores

The asymptotic law core of a sequence is the intersection of the closed convex
hulls of all tails. This file proves compact-convex formation and exact
exchange with continuous affine maps.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Filter Topology

section Formation

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]

/-- Values of a history after stage `N`. -/
def lawTail (x : ℕ → E) (N : ℕ) : Set E := x '' Ici N

/-- Closed convex laws formable after stage `N`. -/
def lawTailHull (x : ℕ → E) (N : ℕ) : Set E :=
  closedConvexHull ℝ (lawTail x N)

/-- Laws formable after every finite prefix has been discarded. -/
def asymptoticLawCore (x : ℕ → E) : Set E :=
  ⋂ N, lawTailHull x N

omit [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [T2Space E] in
theorem lawTail_succ_subset (x : ℕ → E) (N : ℕ) :
    lawTail x (N + 1) ⊆ lawTail x N := by
  rintro y ⟨n, hn, rfl⟩
  exact ⟨n, le_trans (Nat.le_succ N) hn, rfl⟩

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E] in
theorem lawTailHull_succ_subset (x : ℕ → E) (N : ℕ) :
    lawTailHull x (N + 1) ⊆ lawTailHull x N :=
  (closedConvexHull ℝ).monotone (lawTail_succ_subset x N)

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E] in
theorem lawTailHull_nonempty (x : ℕ → E) (N : ℕ) :
    (lawTailHull x N).Nonempty := by
  refine ⟨x N, subset_closedConvexHull ?_⟩
  exact ⟨N, Set.mem_Ici.mpr le_rfl, rfl⟩

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E] in
theorem lawTailHull_subset_of_compactConvex {x : ℕ → E} {K : Set E}
    (hKconv : Convex ℝ K) (hKclosed : IsClosed K) (hx : ∀ n, x n ∈ K) (N : ℕ) :
    lawTailHull x N ⊆ K := by
  apply closedConvexHull_min _ hKconv hKclosed
  rintro y ⟨n, -, rfl⟩
  exact hx n

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
theorem asymptoticLawCore_nonempty {x : ℕ → E} {K : Set E}
    (hK : IsCompact K) (hKconv : Convex ℝ K) (hx : ∀ n, x n ∈ K) :
    (asymptoticLawCore x).Nonempty := by
  apply IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed (lawTailHull x)
  · exact lawTailHull_succ_subset x
  · exact lawTailHull_nonempty x
  · exact hK.of_isClosed_subset isClosed_closedConvexHull
      (lawTailHull_subset_of_compactConvex hKconv hK.isClosed hx 0)
  · intro N
    exact isClosed_closedConvexHull

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E] in
theorem asymptoticLawCore_convex (x : ℕ → E) :
    Convex ℝ (asymptoticLawCore x) :=
  convex_iInter fun _ ↦ convex_closedConvexHull

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E] in
theorem asymptoticLawCore_isClosed (x : ℕ → E) :
    IsClosed (asymptoticLawCore x) :=
  isClosed_iInter fun _ ↦ isClosed_closedConvexHull

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E] in
theorem asymptoticLawCore_subset_of_compactConvex {x : ℕ → E} {K : Set E}
    (hKconv : Convex ℝ K) (hKclosed : IsClosed K) (hx : ∀ n, x n ∈ K) :
    asymptoticLawCore x ⊆ K := by
  intro y hy
  exact lawTailHull_subset_of_compactConvex hKconv hKclosed hx 0
    (Set.mem_iInter.mp hy 0)

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
theorem asymptoticLawCore_isCompact {x : ℕ → E} {K : Set E}
    (hK : IsCompact K) (hKconv : Convex ℝ K) (hx : ∀ n, x n ∈ K) :
    IsCompact (asymptoticLawCore x) :=
  hK.of_isClosed_subset (asymptoticLawCore_isClosed x)
    (asymptoticLawCore_subset_of_compactConvex hKconv hK.isClosed hx)

end Formation

section Exchange

variable {E F : Type*}
  [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
  [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [T2Space F]

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] in
theorem continuousAffine_image_lawTailHull
    {x : ℕ → E} {K : Set E} (hK : IsCompact K) (hKconv : Convex ℝ K)
    (hx : ∀ n, x n ∈ K) (f : E →ᴬ[ℝ] F) (N : ℕ) :
    f '' lawTailHull x N = lawTailHull (f ∘ x) N := by
  apply Subset.antisymm
  · rintro y ⟨z, hz, rfl⟩
    have hpre : lawTail x N ⊆ f ⁻¹' lawTailHull (f ∘ x) N := by
      rintro u ⟨n, hn, rfl⟩
      exact subset_closedConvexHull ⟨n, hn, rfl⟩
    exact closedConvexHull_min hpre
      (convex_closedConvexHull.affine_preimage f.toAffineMap)
      (isClosed_closedConvexHull.preimage f.cont) hz
  · apply closedConvexHull_min
    · rintro y ⟨n, hn, rfl⟩
      exact ⟨x n, subset_closedConvexHull ⟨n, hn, rfl⟩, rfl⟩
    · exact convex_closedConvexHull.affine_image f.toAffineMap
    · exact (hK.of_isClosed_subset isClosed_closedConvexHull
        (lawTailHull_subset_of_compactConvex hKconv hK.isClosed hx N)).image f.cont |>.isClosed

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] in
theorem continuousAffine_image_asymptoticLawCore
    {x : ℕ → E} {K : Set E} (hK : IsCompact K) (hKconv : Convex ℝ K)
    (hx : ∀ n, x n ∈ K) (f : E →ᴬ[ℝ] F) :
    f '' asymptoticLawCore x = asymptoticLawCore (f ∘ x) := by
  rw [asymptoticLawCore, asymptoticLawCore]
  have htail (N : ℕ) : f '' lawTailHull x N = lawTailHull (f ∘ x) N :=
    continuousAffine_image_lawTailHull hK hKconv hx f N
  apply Subset.antisymm
  · rintro y ⟨z, hz, rfl⟩
    refine Set.mem_iInter.mpr ?_
    intro N
    rw [← htail N]
    exact ⟨z, Set.mem_iInter.mp hz N, rfl⟩
  · intro y hy
    let C : ℕ → Set E := fun N ↦ lawTailHull x N ∩ f ⁻¹' {y}
    have hC_nonempty (N : ℕ) : (C N).Nonempty := by
      have hyn := Set.mem_iInter.mp hy N
      rw [← htail N] at hyn
      rcases hyn with ⟨z, hz, hfz⟩
      exact ⟨z, hz, hfz⟩
    have hC_succ (N : ℕ) : C (N + 1) ⊆ C N := by
      intro z hz
      exact ⟨lawTailHull_succ_subset x N hz.1, hz.2⟩
    have hC_closed (N : ℕ) : IsClosed (C N) :=
      isClosed_closedConvexHull.inter (isClosed_singleton.preimage f.cont)
    have hC0_compact : IsCompact (C 0) :=
      (hK.of_isClosed_subset isClosed_closedConvexHull
        (lawTailHull_subset_of_compactConvex hKconv hK.isClosed hx 0)).of_isClosed_subset
          (hC_closed 0) inter_subset_left
    rcases IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed C
      hC_succ hC_nonempty hC0_compact hC_closed with ⟨z, hz⟩
    exact ⟨z, Set.mem_iInter.mpr (fun N ↦ (Set.mem_iInter.mp hz N).1),
      (Set.mem_iInter.mp hz 0).2⟩

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] in
/-- A common affine recovery is information-neutral after tail-law formation:
formation commutes with the encoder, and the decoder reconstructs the original
core exactly. -/
theorem commonRecovery_asymptoticLawCore
    {x : ℕ → E} {K : Set E} (hK : IsCompact K) (hKconv : Convex ℝ K)
    (hx : ∀ n, x n ∈ K) (R : E →ᴬ[ℝ] F) (Q : F →ᴬ[ℝ] E)
    (hQR : ∀ z, Q (R z) = z) :
    R '' asymptoticLawCore x = asymptoticLawCore (R ∘ x) ∧
      Q '' asymptoticLawCore (R ∘ x) = asymptoticLawCore x := by
  refine ⟨continuousAffine_image_asymptoticLawCore hK hKconv hx R, ?_⟩
  have hRK : IsCompact (R '' K) := hK.image R.cont
  have hRKconv : Convex ℝ (R '' K) := hKconv.affine_image R.toAffineMap
  have hxRK : ∀ n, (R ∘ x) n ∈ R '' K := fun n ↦ ⟨x n, hx n, rfl⟩
  have hcomp : (Q : F → E) ∘ (R : E → F) ∘ x = x := by
    funext n
    exact hQR (x n)
  simpa only [hcomp] using
    (continuousAffine_image_asymptoticLawCore hRK hRKconv hxRK Q)

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- A continuous affine involution acts exactly on formed law cores. The second
identity says that packet formation retains the full order-two action. -/
theorem continuousAffine_involution_asymptoticLawCore
    {x : ℕ → E} {K : Set E} (hK : IsCompact K) (hKconv : Convex ℝ K)
    (hx : ∀ n, x n ∈ K) (J : E →ᴬ[ℝ] E) (hJ : ∀ z, J (J z) = z) :
    J '' asymptoticLawCore x = asymptoticLawCore (J ∘ x) ∧
      J '' asymptoticLawCore (J ∘ x) = asymptoticLawCore x := by
  refine ⟨continuousAffine_image_asymptoticLawCore hK hKconv hx J, ?_⟩
  have hJK : IsCompact (J '' K) := hK.image J.cont
  have hJKconv : Convex ℝ (J '' K) := hKconv.affine_image J.toAffineMap
  have hxJK : ∀ n, (J ∘ x) n ∈ J '' K := fun n ↦ ⟨x n, hx n, rfl⟩
  have hcomp : (J : E → E) ∘ (J : E → E) ∘ x = x := by
    funext n
    exact hJ (x n)
  simpa only [hcomp] using
    (continuousAffine_image_asymptoticLawCore hJK hJKconv hxJK J)

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] in
/-- A lifted functional-equation action remains information-neutral through a
common affine recovery. Formation commutes with the lift, and decoding the
formed lifted packet gives exactly the source functional-equation packet. -/
theorem liftedFunctionalEquation_informationNeutral
    {x : ℕ → E} {K : Set E} (hK : IsCompact K) (hKconv : Convex ℝ K)
    (hx : ∀ n, x n ∈ K) (R : E →ᴬ[ℝ] F) (Q : F →ᴬ[ℝ] E)
    (hQR : ∀ z, Q (R z) = z) (J : E →ᴬ[ℝ] E) (Jhat : F →ᴬ[ℝ] F)
    (hJ : ∀ z, J (J z) = z) (hLift : ∀ z, Jhat (R z) = R (J z)) :
    Jhat '' asymptoticLawCore (R ∘ x) =
        asymptoticLawCore (R ∘ J ∘ x) ∧
      Q '' (Jhat '' asymptoticLawCore (R ∘ x)) =
        J '' asymptoticLawCore x ∧
      ∀ z, Q (Jhat (Jhat (R z))) = z := by
  have hRK : IsCompact (R '' K) := hK.image R.cont
  have hRKconv : Convex ℝ (R '' K) := hKconv.affine_image R.toAffineMap
  have hxRK : ∀ n, (R ∘ x) n ∈ R '' K := fun n ↦ ⟨x n, hx n, rfl⟩
  have hLiftHist :
      (Jhat : F → F) ∘ (R : E → F) ∘ x =
        (R : E → F) ∘ (J : E → E) ∘ x := by
    funext n
    exact hLift (x n)
  have hformed : Jhat '' asymptoticLawCore (R ∘ x) =
      asymptoticLawCore (R ∘ J ∘ x) := by
    simpa only [hLiftHist] using
      (continuousAffine_image_asymptoticLawCore hRK hRKconv hxRK Jhat)
  refine ⟨hformed, ?_, ?_⟩
  rw [hformed]
  have hJK : IsCompact (J '' K) := hK.image J.cont
  have hJKconv : Convex ℝ (J '' K) := hKconv.affine_image J.toAffineMap
  have hxJK : ∀ n, (J ∘ x) n ∈ J '' K := fun n ↦ ⟨x n, hx n, rfl⟩
  rw [(commonRecovery_asymptoticLawCore hJK hJKconv hxJK R Q hQR).2]
  exact (continuousAffine_image_asymptoticLawCore hK hKconv hx J).symm
  intro z
  rw [hLift z, hLift (J z), hQR, hJ]

end Exchange

section Exactification

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A convergent history has no asymptotic convex ambiguity. -/
theorem asymptoticLawCore_eq_singleton_of_tendsto
    {x : ℕ → E} {a : E} (hx : Tendsto x atTop (𝓝 a)) :
    asymptoticLawCore x = {a} := by
  ext y
  constructor
  · intro hy
    have hya : y = a := by
      by_contra hne
      have hd : 0 < dist y a := dist_pos.mpr hne
      obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hx (dist y a / 2) (half_pos hd)
      have htail : lawTail x N ⊆ Metric.closedBall a (dist y a / 2) := by
        rintro z ⟨n, hn, rfl⟩
        exact Metric.mem_closedBall.mpr (le_of_lt (hN n hn))
      have hyball : y ∈ Metric.closedBall a (dist y a / 2) :=
        closedConvexHull_min htail (convex_closedBall a _) Metric.isClosed_closedBall
          (Set.mem_iInter.mp hy N)
      have hle := Metric.mem_closedBall.mp hyball
      linarith
    simp [hya]
  · intro hy
    have hya : y = a := Set.mem_singleton_iff.mp hy
    subst y
    refine Set.mem_iInter.mpr ?_
    intro N
    apply closure_subset_closedConvexHull
    apply mem_closure_of_tendsto hx
    exact Filter.eventually_atTop.2 ⟨N, fun n hn ↦ ⟨n, hn, rfl⟩⟩

/-- Every asymptotically vanishing affine constraint vanishes on the complete
tail-law core. -/
theorem continuousAffine_vanishes_on_asymptoticLawCore
    {x : ℕ → E} {K : Set E} (hK : IsCompact K) (hKconv : Convex ℝ K)
    (hxK : ∀ n, x n ∈ K) (A : E →ᴬ[ℝ] F)
    (hAx : Tendsto (A ∘ x) atTop (𝓝 0)) {y : E}
    (hy : y ∈ asymptoticLawCore x) :
    A y = 0 := by
  have hAy : A y ∈ asymptoticLawCore (A ∘ x) := by
    rw [← continuousAffine_image_asymptoticLawCore hK hKconv hxK A]
    exact ⟨y, hy, rfl⟩
  rw [asymptoticLawCore_eq_singleton_of_tendsto hAx] at hAy
  exact Set.mem_singleton_iff.mp hAy

/-- Approximate affine fixed points become exact fixed points on the formed
tail-law core. -/
theorem continuousAffine_fixed_on_asymptoticLawCore
    {x : ℕ → E} {K : Set E} (hK : IsCompact K) (hKconv : Convex ℝ K)
    (hxK : ∀ n, x n ∈ K) (T : E →ᴬ[ℝ] E)
    (hTx : Tendsto (fun n ↦ T (x n) - x n) atTop (𝓝 0)) {y : E}
    (hy : y ∈ asymptoticLawCore x) :
    T y = y := by
  have hzero := continuousAffine_vanishes_on_asymptoticLawCore
    hK hKconv hxK (T - ContinuousAffineMap.id ℝ E) hTx hy
  have hsub : T y - y = 0 := by
    simpa only [ContinuousAffineMap.sub_apply, ContinuousAffineMap.coe_id,
      Function.id_def] using hzero
  exact sub_eq_zero.mp hsub

end Exactification

end GaloisForLFunctions.HTGeometry
