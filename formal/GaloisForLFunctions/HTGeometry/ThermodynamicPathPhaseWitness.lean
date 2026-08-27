import GaloisForLFunctions.HTGeometry.PathGraphTree
import GaloisForLFunctions.HTGeometry.PathCarrierSeparatingDirection
import GaloisForLFunctions.HTGeometry.ThermodynamicPathMobileReference
import GaloisForLFunctions.HTGeometry.TreePhaseTailCapacityLower

/-!
# Four-phase witness of the thermodynamic tail center

The diagonal `Z/ZZ` center is the Pauli expansion of a positive weighted `P11` path energy, up to
constant and one-site terms.  Four-corner differencing annihilates those lower-order terms exactly.
The tree orientation law can therefore expose the absolute crossing weight of every mobile cut.
-/

open scoped BigOperators Matrix Matrix.Norms.L2Operator
open Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open StaticLocalLaboratoryComplexityGrowthLaw

noncomputable local instance pathGraphEdgeSetFintype (n : ℕ) :
    Fintype (SimpleGraph.pathGraph (n + 1)).edgeSet :=
  Fintype.ofFinite _

theorem zSetSign_singleton_cutFour_mixed
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (A : Finset Q) (sigma : Q → Bool) (q : Q) :
    (if cutFourConfig A sigma false false q then (-1 : ℝ) else 1) +
      (if cutFourConfig A sigma true true q then (-1 : ℝ) else 1) -
      (if cutFourConfig A sigma false true q then (-1 : ℝ) else 1) -
      (if cutFourConfig A sigma true false q then (-1 : ℝ) else 1) = 0 := by
  by_cases hq : q ∈ A <;> cases hs : sigma q <;>
    simp [cutFourConfig, orientedBit, hq, hs]

theorem zSetSign_pair_cutFour_mixed_eq_four_mul_edgeP11
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (A : Finset Q) (sigma : Q → Bool) (u v : Q) :
    ((if cutFourConfig A sigma false false u then (-1 : ℝ) else 1) *
        (if cutFourConfig A sigma false false v then (-1 : ℝ) else 1) +
      (if cutFourConfig A sigma true true u then (-1 : ℝ) else 1) *
        (if cutFourConfig A sigma true true v then (-1 : ℝ) else 1) -
      (if cutFourConfig A sigma false true u then (-1 : ℝ) else 1) *
        (if cutFourConfig A sigma false true v then (-1 : ℝ) else 1) -
      (if cutFourConfig A sigma true false u then (-1 : ℝ) else 1) *
        (if cutFourConfig A sigma true false v then (-1 : ℝ) else 1)) =
      4 * (edgeP11Value (cutFourConfig A sigma false false) s(u, v) +
        edgeP11Value (cutFourConfig A sigma true true) s(u, v) -
        edgeP11Value (cutFourConfig A sigma false true) s(u, v) -
        edgeP11Value (cutFourConfig A sigma true false) s(u, v)) := by
  by_cases hu : u ∈ A <;> by_cases hv : v ∈ A <;>
    cases hsu : sigma u <;> cases hsv : sigma v <;>
    simp [cutFourConfig, orientedBit, edgeP11Value, hu, hv, hsu, hsv] <;> norm_num

/-- Physical path edge as an unordered vertex pair. -/
def pathEdgeSym (n : ℕ) (e : Fin n) : Sym2 (Fin (n + 1)) :=
  s(e.castSucc, e.succ)

theorem pathEdgeSym_injective (n : ℕ) : Function.Injective (pathEdgeSym n) := by
  intro e f hef
  exact SimpleGraph.pathGraphEdge_injective n (Subtype.ext hef)

/-- Tail phase coefficient on the physical path graph. -/
def pathTailPhaseWeight (k K : ℕ) (E : Sym2 (Fin (k + 3))) : ℝ :=
  ∑ e : Fin (k + 2),
    if pathEdgeSym (k + 2) e = E then
      if 4 * K ≤ e.val then nestedInfiniteEdgeWeight e.val else 0
    else 0

theorem pathTailPhaseWeight_pathEdge (k K : ℕ) (e : Fin (k + 2)) :
    pathTailPhaseWeight k K (pathEdgeSym (k + 2) e) =
      if 4 * K ≤ e.val then nestedInfiniteEdgeWeight e.val else 0 := by
  unfold pathTailPhaseWeight
  rw [Finset.sum_eq_single e]
  · simp
  · intro f hf hfe
    rw [if_neg]
    exact fun h => hfe (pathEdgeSym_injective (k + 2) h)
  · simp

theorem pathGraph_edgeFinset_eq_image_pathEdgeSym (n : ℕ) :
    (SimpleGraph.pathGraph (n + 1)).edgeFinset =
      Finset.univ.map ⟨pathEdgeSym n, pathEdgeSym_injective n⟩ := by
  apply Finset.ext
  intro E
  constructor
  · intro hE
    have hset : E ∈ (SimpleGraph.pathGraph (n + 1)).edgeSet := by
      simpa only [SimpleGraph.mem_edgeFinset] using hE
    obtain ⟨e, he⟩ := SimpleGraph.pathGraphEdge_surjective n ⟨E, hset⟩
    rw [Finset.mem_map]
    refine ⟨e, Finset.mem_univ e, ?_⟩
    exact congrArg Subtype.val he
  · intro hE
    rw [Finset.mem_map] at hE
    obtain ⟨e, he, rfl⟩ := hE
    simpa only [SimpleGraph.mem_edgeFinset, Function.Embedding.coeFn_mk,
      pathEdgeSym, SimpleGraph.pathGraphEdge] using
      (SimpleGraph.pathGraphEdge n e).property

theorem treePhaseEnergy_pathTail_expand
    (k K : ℕ) (x : FiniteQubitConfiguration (Fin (k + 3))) :
    treePhaseEnergy (SimpleGraph.pathGraph (k + 3)) (pathTailPhaseWeight k K) x =
      ∑ e : Fin (k + 2),
        (if 4 * K ≤ e.val then nestedInfiniteEdgeWeight e.val else 0) *
          edgeP11Value x (pathEdgeSym (k + 2) e) := by
  unfold treePhaseEnergy
  rw [pathGraph_edgeFinset_eq_image_pathEdgeSym (k + 2)]
  rw [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro e he
  change pathTailPhaseWeight k K (pathEdgeSym (k + 2) e) *
      edgeP11Value x (pathEdgeSym (k + 2) e) = _
  rw [pathTailPhaseWeight_pathEdge]

@[simp] theorem pathShellOnSites_mobileTail_nestedCenter_edge_zz
    (k K : ℕ) (e : Fin (k + 2)) :
    pathShellOnSites (mobileTailPathSites k K)
        (infinitePathPrefixShell k nestedInfinitePathCenter)
        (Sum.inr (e, ((2 : Fin 3), (2 : Fin 3)))) =
      if 4 * K ≤ e.val then nestedInfiniteEdgeWeight e.val / 4 else 0 := by
  unfold pathShellOnSites infinitePathPrefixShell
  change (if PathWordSupportedIn (mobileTailPathSites k K)
      (Sum.inr (e, ((2 : Fin 3), (2 : Fin 3)))) then
        nestedInfinitePathCenter
          (pathLabelToInfinite k (Sum.inr (e, ((2 : Fin 3), (2 : Fin 3)))))
      else 0) = _
  simp only [pathWordSupportedIn_mobileTail_edge_iff]
  by_cases he : 4 * K ≤ e.val
  · simp [he, pathLabelToInfinite, nestedInfinitePathCenter]
  · simp [he]

/-- Four-corner differencing of the physical diagonal tail energy is exactly the corresponding
positive `P11` tree phase.  Constant and onsite terms cancel; every retained `ZZ` coefficient
contributes its full physical edge weight. -/
theorem pathDiagEnergy_mobileTail_cut_mixed_eq_treePhaseEnergy
    (k K : ℕ) (A : Finset (Fin (k + 3))) (sigma : Fin (k + 3) → Bool) :
    let u := pathShellOnSites (mobileTailPathSites k K)
      (infinitePathPrefixShell k nestedInfinitePathCenter)
    pathDiagEnergy u (cutFourConfig A sigma false false) +
        pathDiagEnergy u (cutFourConfig A sigma true true) -
        pathDiagEnergy u (cutFourConfig A sigma false true) -
        pathDiagEnergy u (cutFourConfig A sigma true false) =
      treePhaseEnergy (SimpleGraph.pathGraph (k + 3)) (pathTailPhaseWeight k K)
          (cutFourConfig A sigma false false) +
        treePhaseEnergy (SimpleGraph.pathGraph (k + 3)) (pathTailPhaseWeight k K)
          (cutFourConfig A sigma true true) -
        treePhaseEnergy (SimpleGraph.pathGraph (k + 3)) (pathTailPhaseWeight k K)
          (cutFourConfig A sigma false true) -
        treePhaseEnergy (SimpleGraph.pathGraph (k + 3)) (pathTailPhaseWeight k K)
          (cutFourConfig A sigma true false) := by
  dsimp only
  unfold pathDiagEnergy
  have hOnsite :
      (∑ s : Fin (k + 3),
          pathShellOnSites (mobileTailPathSites k K)
              (infinitePathPrefixShell k nestedInfinitePathCenter) (Sum.inl (s, 2)) *
            zSetSign ({s} : Finset (Fin (k + 3)))
              (cutFourConfig A sigma false false)) +
        (∑ s : Fin (k + 3),
          pathShellOnSites (mobileTailPathSites k K)
              (infinitePathPrefixShell k nestedInfinitePathCenter) (Sum.inl (s, 2)) *
            zSetSign ({s} : Finset (Fin (k + 3)))
              (cutFourConfig A sigma true true)) -
        (∑ s : Fin (k + 3),
          pathShellOnSites (mobileTailPathSites k K)
              (infinitePathPrefixShell k nestedInfinitePathCenter) (Sum.inl (s, 2)) *
            zSetSign ({s} : Finset (Fin (k + 3)))
              (cutFourConfig A sigma false true)) -
        (∑ s : Fin (k + 3),
          pathShellOnSites (mobileTailPathSites k K)
              (infinitePathPrefixShell k nestedInfinitePathCenter) (Sum.inl (s, 2)) *
            zSetSign ({s} : Finset (Fin (k + 3)))
              (cutFourConfig A sigma true false)) = 0 := by
    simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_eq_zero
    intro s hs
    rw [show
      pathShellOnSites (mobileTailPathSites k K)
            (infinitePathPrefixShell k nestedInfinitePathCenter) (Sum.inl (s, 2)) *
          zSetSign {s} (cutFourConfig A sigma false false) +
        pathShellOnSites (mobileTailPathSites k K)
            (infinitePathPrefixShell k nestedInfinitePathCenter) (Sum.inl (s, 2)) *
          zSetSign {s} (cutFourConfig A sigma true true) -
        pathShellOnSites (mobileTailPathSites k K)
            (infinitePathPrefixShell k nestedInfinitePathCenter) (Sum.inl (s, 2)) *
          zSetSign {s} (cutFourConfig A sigma false true) -
        pathShellOnSites (mobileTailPathSites k K)
            (infinitePathPrefixShell k nestedInfinitePathCenter) (Sum.inl (s, 2)) *
          zSetSign {s} (cutFourConfig A sigma true false) =
        pathShellOnSites (mobileTailPathSites k K)
            (infinitePathPrefixShell k nestedInfinitePathCenter) (Sum.inl (s, 2)) *
          (zSetSign {s} (cutFourConfig A sigma false false) +
            zSetSign {s} (cutFourConfig A sigma true true) -
            zSetSign {s} (cutFourConfig A sigma false true) -
            zSetSign {s} (cutFourConfig A sigma true false)) by ring]
    rw [zSetSign_singleton, zSetSign_singleton, zSetSign_singleton,
      zSetSign_singleton, zSetSign_singleton_cutFour_mixed]
    ring
  rw [show
    ((∑ s : Fin (k + 3),
        pathShellOnSites (mobileTailPathSites k K)
            (infinitePathPrefixShell k nestedInfinitePathCenter) (Sum.inl (s, 2)) *
          zSetSign {s} (cutFourConfig A sigma false false)) +
      ∑ e : Fin (k + 2),
        pathShellOnSites (mobileTailPathSites k K)
            (infinitePathPrefixShell k nestedInfinitePathCenter) (Sum.inr (e, (2, 2))) *
          zSetSign {e.castSucc, e.succ} (cutFourConfig A sigma false false)) +
      ((∑ s : Fin (k + 3),
        pathShellOnSites (mobileTailPathSites k K)
            (infinitePathPrefixShell k nestedInfinitePathCenter) (Sum.inl (s, 2)) *
          zSetSign {s} (cutFourConfig A sigma true true)) +
      ∑ e : Fin (k + 2),
        pathShellOnSites (mobileTailPathSites k K)
            (infinitePathPrefixShell k nestedInfinitePathCenter) (Sum.inr (e, (2, 2))) *
          zSetSign {e.castSucc, e.succ} (cutFourConfig A sigma true true)) -
      ((∑ s : Fin (k + 3),
        pathShellOnSites (mobileTailPathSites k K)
            (infinitePathPrefixShell k nestedInfinitePathCenter) (Sum.inl (s, 2)) *
          zSetSign {s} (cutFourConfig A sigma false true)) +
      ∑ e : Fin (k + 2),
        pathShellOnSites (mobileTailPathSites k K)
            (infinitePathPrefixShell k nestedInfinitePathCenter) (Sum.inr (e, (2, 2))) *
          zSetSign {e.castSucc, e.succ} (cutFourConfig A sigma false true)) -
      ((∑ s : Fin (k + 3),
        pathShellOnSites (mobileTailPathSites k K)
            (infinitePathPrefixShell k nestedInfinitePathCenter) (Sum.inl (s, 2)) *
          zSetSign {s} (cutFourConfig A sigma true false)) +
      ∑ e : Fin (k + 2),
        pathShellOnSites (mobileTailPathSites k K)
            (infinitePathPrefixShell k nestedInfinitePathCenter) (Sum.inr (e, (2, 2))) *
          zSetSign {e.castSucc, e.succ} (cutFourConfig A sigma true false)) =
      ((∑ s : Fin (k + 3),
        pathShellOnSites (mobileTailPathSites k K)
            (infinitePathPrefixShell k nestedInfinitePathCenter) (Sum.inl (s, 2)) *
          zSetSign {s} (cutFourConfig A sigma false false)) +
      (∑ s : Fin (k + 3),
        pathShellOnSites (mobileTailPathSites k K)
            (infinitePathPrefixShell k nestedInfinitePathCenter) (Sum.inl (s, 2)) *
          zSetSign {s} (cutFourConfig A sigma true true)) -
      (∑ s : Fin (k + 3),
        pathShellOnSites (mobileTailPathSites k K)
            (infinitePathPrefixShell k nestedInfinitePathCenter) (Sum.inl (s, 2)) *
          zSetSign {s} (cutFourConfig A sigma false true)) -
      (∑ s : Fin (k + 3),
        pathShellOnSites (mobileTailPathSites k K)
            (infinitePathPrefixShell k nestedInfinitePathCenter) (Sum.inl (s, 2)) *
          zSetSign {s} (cutFourConfig A sigma true false))) +
      ((∑ e : Fin (k + 2),
        pathShellOnSites (mobileTailPathSites k K)
            (infinitePathPrefixShell k nestedInfinitePathCenter) (Sum.inr (e, (2, 2))) *
          zSetSign {e.castSucc, e.succ} (cutFourConfig A sigma false false)) +
      (∑ e : Fin (k + 2),
        pathShellOnSites (mobileTailPathSites k K)
            (infinitePathPrefixShell k nestedInfinitePathCenter) (Sum.inr (e, (2, 2))) *
          zSetSign {e.castSucc, e.succ} (cutFourConfig A sigma true true)) -
      (∑ e : Fin (k + 2),
        pathShellOnSites (mobileTailPathSites k K)
            (infinitePathPrefixShell k nestedInfinitePathCenter) (Sum.inr (e, (2, 2))) *
          zSetSign {e.castSucc, e.succ} (cutFourConfig A sigma false true)) -
      (∑ e : Fin (k + 2),
        pathShellOnSites (mobileTailPathSites k K)
            (infinitePathPrefixShell k nestedInfinitePathCenter) (Sum.inr (e, (2, 2))) *
          zSetSign {e.castSucc, e.succ} (cutFourConfig A sigma true false))) by ring,
    hOnsite, zero_add]
  rw [treePhaseEnergy_pathTail_expand, treePhaseEnergy_pathTail_expand,
    treePhaseEnergy_pathTail_expand, treePhaseEnergy_pathTail_expand]
  simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro e he
  rw [pathShellOnSites_mobileTail_nestedCenter_edge_zz]
  by_cases htail : 4 * K ≤ e.val
  · simp only [if_pos htail]
    rw [zSetSign_pair_eq, zSetSign_pair_eq, zSetSign_pair_eq, zSetSign_pair_eq]
    unfold siteSign
    rw [show
      nestedInfiniteEdgeWeight e.val / 4 *
            ((if cutFourConfig A sigma false false e.castSucc then (-1 : ℝ) else 1) *
              (if cutFourConfig A sigma false false e.succ then (-1 : ℝ) else 1)) +
          nestedInfiniteEdgeWeight e.val / 4 *
            ((if cutFourConfig A sigma true true e.castSucc then (-1 : ℝ) else 1) *
              (if cutFourConfig A sigma true true e.succ then (-1 : ℝ) else 1)) -
        nestedInfiniteEdgeWeight e.val / 4 *
          ((if cutFourConfig A sigma false true e.castSucc then (-1 : ℝ) else 1) *
            (if cutFourConfig A sigma false true e.succ then (-1 : ℝ) else 1)) -
        nestedInfiniteEdgeWeight e.val / 4 *
          ((if cutFourConfig A sigma true false e.castSucc then (-1 : ℝ) else 1) *
            (if cutFourConfig A sigma true false e.succ then (-1 : ℝ) else 1)) =
        nestedInfiniteEdgeWeight e.val / 4 *
          (((if cutFourConfig A sigma false false e.castSucc then (-1 : ℝ) else 1) *
              (if cutFourConfig A sigma false false e.succ then (-1 : ℝ) else 1)) +
            ((if cutFourConfig A sigma true true e.castSucc then (-1 : ℝ) else 1) *
              (if cutFourConfig A sigma true true e.succ then (-1 : ℝ) else 1)) -
            ((if cutFourConfig A sigma false true e.castSucc then (-1 : ℝ) else 1) *
              (if cutFourConfig A sigma false true e.succ then (-1 : ℝ) else 1)) -
            ((if cutFourConfig A sigma true false e.castSucc then (-1 : ℝ) else 1) *
              (if cutFourConfig A sigma true false e.succ then (-1 : ℝ) else 1))) by ring,
      zSetSign_pair_cutFour_mixed_eq_four_mul_edgeP11]
    simp only [pathEdgeSym]
    ring
  · simp [htail]

end

end GaloisForLFunctions.HTGeometry
