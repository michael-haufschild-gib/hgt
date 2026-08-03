import GaloisForLFunctions.HTGeometry.CayleyJetPacketSubmersion
import GaloisForLFunctions.HTGeometry.OuterJetSigmaChart

/-!
# The multi-node Cayley chart is a submersion

Applying the Cayley outer chart at every node of a packet is the product of the one-node charts, so
the branch inverses at the nodes assemble to a smooth right inverse of the whole chart.

Its derivative is therefore surjective at every packet whose zeroth entries avoid `-i`.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι : Type*} [Fintype ι]

/-- The restriction of a sigma-indexed packet to one node. -/
def nodeSlice (m : ι → ℕ) (i : ι) (y : (Σ i, Fin (m i + 1)) → ℂ) : Fin (m i + 1) → ℂ :=
  fun k => y ⟨i, k⟩

theorem contDiff_nodeSlice (m : ι → ℕ) (i : ι) :
    ContDiff ℝ (⊤ : ℕ∞) (nodeSlice m i) :=
  contDiff_pi.2 fun k => contDiff_apply ℝ ℂ (⟨i, k⟩ : Σ i, Fin (m i + 1))

/-- The branch inverses at the nodes, assembled. -/
def outerJetSigmaInv (m : ι → ℕ) (a : ι → ℂ) (w : (Σ i, Fin (m i + 1)) → ℂ) :
    (Σ i, Fin (m i + 1)) → ℂ :=
  fun t => chiJetInvPacket (m t.1) (a t.1) (nodeSlice m t.1 w) t.2

/-- The packets whose every node slice lies in the target of the branch inverse. -/
def outerJetSigmaTarget (m : ι → ℕ) (a : ι → ℂ) : Set ((Σ i, Fin (m i + 1)) → ℂ) :=
  {w | ∀ i, nodeSlice m i w ∈ chiChartTarget (m i) (a i)}

theorem isOpen_outerJetSigmaTarget (m : ι → ℕ) (a : ι → ℂ) :
    IsOpen (outerJetSigmaTarget m a) := by
  have hset : outerJetSigmaTarget m a
      = ⋂ i, (nodeSlice m i) ⁻¹' (chiChartTarget (m i) (a i)) := by
    ext w
    simp [outerJetSigmaTarget, Set.mem_iInter]
  rw [hset]
  refine isOpen_iInter_of_finite fun i => ?_
  exact (isOpen_chiChartTarget (m i) (a i)).preimage (contDiff_nodeSlice m i).continuous

theorem contDiffOn_outerJetSigmaInv (m : ι → ℕ) (a : ι → ℂ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (outerJetSigmaInv m a) (outerJetSigmaTarget m a) := by
  rw [contDiffOn_pi]
  intro t
  have hmaps : Set.MapsTo (nodeSlice m t.1) (outerJetSigmaTarget m a)
      (chiChartTarget (m t.1) (a t.1)) := fun w hw => hw t.1
  have hcomp : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun w => chiJetInvPacket (m t.1) (a t.1) (nodeSlice m t.1 w)) (outerJetSigmaTarget m a) :=
    (contDiffOn_chiJetInvPacket (m t.1) (a t.1)).comp (contDiff_nodeSlice m t.1).contDiffOn hmaps
  exact (contDiffOn_pi.mp hcomp) t.2

/-- The chart domain of the multi-node Cayley chart. -/
def outerJetSigmaDomain (m : ι → ℕ) : Set ((Σ i, Fin (m i + 1)) → ℂ) :=
  {y | ∀ i, y ⟨i, 0⟩ + Complex.I ≠ 0}

theorem isOpen_outerJetSigmaDomain (m : ι → ℕ) : IsOpen (outerJetSigmaDomain m) := by
  have hset : outerJetSigmaDomain m
      = ⋂ i, (fun y : (Σ i, Fin (m i + 1)) → ℂ => y ⟨i, 0⟩ + Complex.I) ⁻¹' {z : ℂ | z ≠ 0} := by
    ext y
    simp [outerJetSigmaDomain, Set.mem_iInter]
  rw [hset]
  refine isOpen_iInter_of_finite fun i => ?_
  exact isOpen_ne.preimage ((continuous_apply (⟨i, 0⟩ : Σ i, Fin (m i + 1))).add continuous_const)

theorem contDiffOn_outerJetSigma (m : ι → ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (outerJetSigma m) (outerJetSigmaDomain m) := by
  rw [contDiffOn_pi]
  intro t
  have hmaps : Set.MapsTo (nodeSlice m t.1) (outerJetSigmaDomain m)
      {v : Fin (m t.1 + 1) → ℂ | v 0 + Complex.I ≠ 0} := fun y hy => hy t.1
  have hcomp : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y => chiJetPacket (m t.1) (nodeSlice m t.1 y)) (outerJetSigmaDomain m) :=
    (contDiffOn_chiJetPacket (m t.1)).comp (contDiff_nodeSlice m t.1).contDiffOn hmaps
  exact (contDiffOn_pi.mp hcomp) t.2

omit [Fintype ι] in
/-- **The assembled branch inverses invert the multi-node chart.** -/
theorem outerJetSigma_outerJetSigmaInv {m : ι → ℕ} {a : ι → ℂ}
    {w : (Σ i, Fin (m i + 1)) → ℂ} (hw : w ∈ outerJetSigmaTarget m a) :
    outerJetSigma m (outerJetSigmaInv m a w) = w := by
  funext t
  have hslice : nodeSlice m t.1 (outerJetSigmaInv m a w)
      = chiJetInvPacket (m t.1) (a t.1) (nodeSlice m t.1 w) := rfl
  have hval : outerJetSigma m (outerJetSigmaInv m a w) t
      = chiJetPacket (m t.1) (nodeSlice m t.1 (outerJetSigmaInv m a w)) t.2 := rfl
  rw [hval, hslice,
    chiJetPacket_chiJetInvPacket (n := m t.1) (a := a t.1) ?_ (hw t.1).2]
  · rfl
  · intro hzero
    have hmem : nodeSlice m t.1 w 0 / Complex.exp (a t.1) ∈ Complex.slitPlane := (hw t.1).1
    rw [hzero, zero_div] at hmem
    simp [Complex.mem_slitPlane_iff] at hmem

/-- **The multi-node chart is a submersion.** -/
theorem surjective_fderiv_outerJetSigma {m : ι → ℕ} {y : (Σ i, Fin (m i + 1)) → ℂ}
    (hy : y ∈ outerJetSigmaDomain m) :
    Function.Surjective (fderiv ℝ (outerJetSigma m) y) := by
  set a : ι → ℂ := fun i => chiJetBase (jetExtend (m i) (nodeSlice m i y)) with ha
  set w : (Σ i, Fin (m i + 1)) → ℂ := outerJetSigma m y with hw
  have hslice : ∀ i, nodeSlice m i w = chiJetPacket (m i) (nodeSlice m i y) := by
    intro i
    funext k
    rfl
  have hwmem : w ∈ outerJetSigmaTarget m a := by
    intro i
    rw [hslice i]
    exact chiJetPacket_mem_chiChartTarget (hy i)
  have hPsiw : outerJetSigmaInv m a w = y := by
    funext t
    have hval : outerJetSigmaInv m a w t
        = chiJetInvPacket (m t.1) (a t.1) (nodeSlice m t.1 w) t.2 := rfl
    rw [hval, hslice t.1, chiJetInvPacket_chiJetPacket (hy t.1)]
    rfl
  have hPsiDiff : DifferentiableAt ℝ (outerJetSigmaInv m a) w :=
    ((contDiffOn_outerJetSigmaInv m a).differentiableOn (by simp)).differentiableAt
      ((isOpen_outerJetSigmaTarget m a).mem_nhds hwmem)
  have hPhiDiff : DifferentiableAt ℝ (outerJetSigma m) y :=
    ((contDiffOn_outerJetSigma m).differentiableOn (by simp)).differentiableAt
      ((isOpen_outerJetSigmaDomain m).mem_nhds hy)
  have hcomp : HasFDerivAt (outerJetSigma m ∘ outerJetSigmaInv m a)
      ((fderiv ℝ (outerJetSigma m) y).comp (fderiv ℝ (outerJetSigmaInv m a) w)) w := by
    have h1 : HasFDerivAt (outerJetSigma m) (fderiv ℝ (outerJetSigma m) y)
        (outerJetSigmaInv m a w) := by
      rw [hPsiw]
      exact hPhiDiff.hasFDerivAt
    exact HasFDerivAt.comp w h1 hPsiDiff.hasFDerivAt
  have hid : HasFDerivAt (outerJetSigma m ∘ outerJetSigmaInv m a)
      (ContinuousLinearMap.id ℝ ((Σ i, Fin (m i + 1)) → ℂ)) w := by
    refine (hasFDerivAt_id w).congr_of_eventuallyEq ?_
    refine Filter.eventuallyEq_of_mem ((isOpen_outerJetSigmaTarget m a).mem_nhds hwmem) ?_
    intro v hv
    exact outerJetSigma_outerJetSigmaInv hv
  have hker : (fderiv ℝ (outerJetSigma m) y).comp (fderiv ℝ (outerJetSigmaInv m a) w)
      = ContinuousLinearMap.id ℝ ((Σ i, Fin (m i + 1)) → ℂ) := hcomp.unique hid
  have hsurj : Function.Surjective
      ((fderiv ℝ (outerJetSigma m) y) ∘ (fderiv ℝ (outerJetSigmaInv m a) w)) := by
    intro v
    refine ⟨v, ?_⟩
    have hv := congrArg
      (fun L : ((Σ i, Fin (m i + 1)) → ℂ) →L[ℝ] ((Σ i, Fin (m i + 1)) → ℂ) => L v) hker
    simpa using hv
  exact hsurj.of_comp

end

end GaloisForLFunctions.HTGeometry
