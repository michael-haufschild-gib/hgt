/-
# The selected-pair slice of a local-extension chart

The common eigenbranch chart of a one-step local extension restricts to the two-parameter curve
that moves one pair of local shifts against each other and switches on the exchange coupling.  On
that curve the labelled branches keep their labels — by uniqueness of simple characteristic-root
germs — so the restricted family is exactly the split-spectrum slice that the rigidity theorems
consume, and the restriction is available on a whole neighbourhood of the base shift.

This module packages that slice *with* the chart point it came from, so that any identity holding
throughout the chart restricts to the slice.  The selected-pair relation witness already in the
corpus carries the linear relation as a field and therefore cannot serve a quadratic one.

Main results:
* `SelectedLayerSliceData` — the slice, stated against the chart point.
* `exists_selectedLayerSliceData` — every chart has one, for every selected pair.
-/
import GaloisForLFunctions.HTGeometry.LocalExtensionChartSelectedWitness

open Filter Topology
open scoped Matrix.Norms.Elementwise

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The selected-pair slice of a local-extension eigenbranch chart, phrased directly in terms of
the chart branches at the selected-pair curve points. -/
structure SelectedLayerSliceData
    {α ρ : Type*} [Fintype α] [Fintype ρ] [DecidableEq α] [DecidableEq ρ]
    (energy : α → ℝ) (shift₀ : ρ → ℂ) (transition : Matrix α α ℂ)
    (C : LocalExtensionEigenbranchChart (fun a => (energy a : ℂ)) shift₀ transition)
    (r s : ρ) where
  S : Set ℂ
  infinite : S.Infinite
  memChart : ∀ z ∈ S, ∀ᶠ g in 𝓝 (0 : ℂ), selectedPairChartPoint shift₀ r s z g ∈ C.U
  pairShift : ∀ z : ℂ,
    selectedPairShiftLine shift₀ r s z r - selectedPairShiftLine shift₀ r s z s = z
  simple : ∀ z ∈ S, Function.Injective
    (layeredEnergy (fun a => (energy a : ℂ)) (selectedPairShiftLine shift₀ r s z))
  analytic : ∀ z ∈ S, ∀ i,
    AnalyticAt ℂ (fun g => C.branch i (selectedPairChartPoint shift₀ r s z g)) 0
  base : ∀ z ∈ S, ∀ i,
    C.branch i (selectedPairChartPoint shift₀ r s z 0)
      = layeredEnergy (fun a => (energy a : ℂ)) (selectedPairShiftLine shift₀ r s z) i
  root : ∀ z ∈ S, ∀ i, ∀ᶠ g in 𝓝 (0 : ℂ),
    matrixCharpolyRelation
      (Matrix.diagonal
          (layeredEnergy (fun a => (energy a : ℂ)) (selectedPairShiftLine shift₀ r s z)) +
        g • selectedLayerCoupling transition r s,
        C.branch i (selectedPairChartPoint shift₀ r s z g)) = 0

/-- **Every local-extension chart has a selected-pair slice**, for every pair of distinct local
labels.  The labels of the branches survive the restriction by uniqueness of simple
characteristic-root germs. -/
theorem exists_selectedLayerSliceData
    {α ρ : Type*} [Fintype α] [Fintype ρ] [DecidableEq α] [DecidableEq ρ]
    [Nonempty α] (energy : α → ℝ) (shift₀ : ρ → ℂ) (transition : Matrix α α ℂ)
    (hsimple : Function.Injective (layeredEnergy (fun a => (energy a : ℂ)) shift₀))
    (C : LocalExtensionEigenbranchChart (fun a => (energy a : ℂ)) shift₀ transition)
    {r s : ρ} (hrs : r ≠ s) :
    Nonempty (SelectedLayerSliceData energy shift₀ transition C r s) := by
  classical
  set z₀ : ℂ := shift₀ r - shift₀ s with hz₀def
  set shift : ℂ → ρ → ℂ := selectedPairShiftLine shift₀ r s with hshiftdef
  set point : ℂ → ℂ → (ρ → ℂ) × Matrix ρ ρ ℂ := selectedPairChartPoint shift₀ r s with hpointdef
  set explicitEnergy : ℂ → α × ρ → ℂ :=
    fun z => layeredEnergy (fun a => (energy a : ℂ)) (shift z) with hexpdef
  have hpointAnalytic : AnalyticAt ℂ (fun z => point z 0) z₀ :=
    selectedPairChartPoint_analyticAt_shift shift₀ r s z₀
  have hpointBase : point z₀ 0 = (shift₀, 0) := selectedPairChartPoint_base shift₀ r s
  have hpointU : ∀ᶠ z in 𝓝 z₀, point z 0 ∈ C.U := by
    have hmem := C.isOpen_U.mem_nhds C.center_mem
    have htend : Tendsto (fun z => point z 0) (𝓝 z₀) (𝓝 (shift₀, 0)) := by
      have ht := hpointAnalytic.continuousAt
      change Tendsto (fun z => point z 0) (𝓝 z₀) (𝓝 (point z₀ 0)) at ht
      rw [hpointBase] at ht
      exact ht
    exact htend hmem
  have hshiftBase : shift z₀ = shift₀ := selectedPairShiftLine_base shift₀ r s
  have hbaseEq : explicitEnergy z₀ = layeredEnergy (fun a => (energy a : ℂ)) shift₀ := by
    show layeredEnergy (fun a => (energy a : ℂ)) (shift z₀) = _
    rw [hshiftBase]
  have hlabel : ∀ i, C.branch i (point z₀ 0) = explicitEnergy z₀ i := by
    intro i
    rw [hpointBase, C.base, hbaseEq]
  have hlabelGerm : ∀ i,
      (fun z => C.branch i (point z 0)) =ᶠ[𝓝 z₀] (fun z => explicitEnergy z i) := by
    intro i
    set H : ℂ → Matrix (α × ρ) (α × ρ) ℂ :=
      fun z => localExtensionMatrix (fun a => (energy a : ℂ)) (point z 0).1 transition
        (point z 0).2 with hHdef
    have hHan : AnalyticAt ℂ H z₀ :=
      (localExtensionMatrix_analyticAt (fun a => (energy a : ℂ)) transition
        (shift₀, 0)).fun_comp_of_eq hpointAnalytic hpointBase
    have hHz₀ : H z₀ = Matrix.diagonal (layeredEnergy (fun a => (energy a : ℂ)) shift₀) := by
      rw [hHdef]
      simp [hpointBase, localExtensionMatrix_zero]
    have hHt : Tendsto H (𝓝 z₀)
        (𝓝 (Matrix.diagonal (layeredEnergy (fun a => (energy a : ℂ)) shift₀))) := by
      have hcont := hHan.continuousAt
      change Tendsto H (𝓝 z₀) (𝓝 (H z₀)) at hcont
      rwa [hHz₀] at hcont
    have hbranchAn : AnalyticAt ℂ (fun z => C.branch i (point z 0)) z₀ :=
      (C.analyticOn_branch i (shift₀, 0) C.center_mem).fun_comp_of_eq hpointAnalytic hpointBase
    have hbranchT : Tendsto (fun z => C.branch i (point z 0)) (𝓝 z₀)
        (𝓝 (layeredEnergy (fun a => (energy a : ℂ)) shift₀ i)) := by
      have hcont := hbranchAn.continuousAt
      change Tendsto (fun z => C.branch i (point z 0)) (𝓝 z₀)
        (𝓝 (C.branch i (point z₀ 0))) at hcont
      rw [hlabel i, hbaseEq] at hcont
      exact hcont
    have hexplicitAn : AnalyticAt ℂ (fun z => explicitEnergy z i) z₀ :=
      analyticAt_const.add
        (analyticAt_pi_iff.mp (selectedPairShiftLine_analyticAt shift₀ r s z₀) i.2)
    have hexplicitT : Tendsto (fun z => explicitEnergy z i) (𝓝 z₀)
        (𝓝 (layeredEnergy (fun a => (energy a : ℂ)) shift₀ i)) := by
      have hcont := hexplicitAn.continuousAt
      change Tendsto (fun z => explicitEnergy z i) (𝓝 z₀) (𝓝 (explicitEnergy z₀ i)) at hcont
      rwa [hbaseEq] at hcont
    have hbranchRoot : ∀ᶠ z in 𝓝 z₀, matrixCharpolyRelation (H z, C.branch i (point z 0)) = 0 := by
      filter_upwards [hpointU] with z hz
      exact C.root (point z 0) hz i
    have hexplicitRoot : ∀ᶠ z in 𝓝 z₀,
        matrixCharpolyRelation (H z, explicitEnergy z i) = 0 := by
      filter_upwards [] with z
      simpa [hHdef, hpointdef, selectedPairChartPoint, localExtensionMatrix_zero, hexpdef,
        hshiftdef] using (matrixCharpolyRelation_diagonal_root (explicitEnergy z) i)
    exact simpleDiagonalMatrix_root_germs_unique
      (layeredEnergy (fun a => (energy a : ℂ)) shift₀) hsimple i hHt hbranchT hexplicitT
      hbranchRoot hexplicitRoot
  have hlabelAll : ∀ᶠ z in 𝓝 z₀, ∀ i, C.branch i (point z 0) = explicitEnergy z i := by
    rw [Filter.eventually_all]
    exact hlabelGerm
  have hsimpleGerm : ∀ᶠ z in 𝓝 z₀, Function.Injective (explicitEnergy z) := by
    have hpairs : ∀ i j : α × ρ, i ≠ j →
        ∀ᶠ z in 𝓝 z₀, explicitEnergy z i ≠ explicitEnergy z j := by
      intro i j hij
      have hdiffAn : AnalyticAt ℂ (fun z => explicitEnergy z i - explicitEnergy z j) z₀ :=
        (analyticAt_const.add
          (analyticAt_pi_iff.mp (selectedPairShiftLine_analyticAt shift₀ r s z₀) i.2)).sub
          (analyticAt_const.add
            (analyticAt_pi_iff.mp (selectedPairShiftLine_analyticAt shift₀ r s z₀) j.2))
      have hdiffNe : explicitEnergy z₀ i - explicitEnergy z₀ j ≠ 0 := by
        rw [sub_ne_zero]
        intro heq
        refine hij (hsimple ?_)
        rw [hbaseEq] at heq
        exact heq
      have hev := hdiffAn.continuousAt (isOpen_ne.mem_nhds hdiffNe)
      filter_upwards [hev] with z hz
      exact sub_ne_zero.mp hz
    have hall : ∀ᶠ z in 𝓝 z₀,
        ∀ i j : α × ρ, i ≠ j → explicitEnergy z i ≠ explicitEnergy z j := by
      rw [Filter.eventually_all]
      intro i
      rw [Filter.eventually_all]
      intro j
      by_cases hij : i = j
      · filter_upwards [] with z
        exact fun h => (h hij).elim
      · filter_upwards [hpairs i j hij] with z hz
        exact fun _ => hz
    filter_upwards [hall] with z hz
    rw [Function.injective_iff_pairwise_ne]
    exact hz
  set T : Set ℂ :=
    {z | point z 0 ∈ C.U ∧ Function.Injective (explicitEnergy z) ∧
      ∀ i, C.branch i (point z 0) = explicitEnergy z i} with hTdef
  have hTnhds : T ∈ 𝓝 z₀ := by
    filter_upwards [hpointU, hsimpleGerm, hlabelAll] with z hzU hzsimple hzlabel
    exact ⟨hzU, hzsimple, hzlabel⟩
  have hTinfinite : T.Infinite := infinite_of_mem_nhds z₀ hTnhds
  have hcurveU : ∀ z ∈ T, ∀ᶠ g in 𝓝 (0 : ℂ), point z g ∈ C.U := by
    intro z hz
    have hpointCurve := selectedPairChartPoint_analyticAt_coupling shift₀ r s z 0
    exact hpointCurve.continuousAt (C.isOpen_U.mem_nhds hz.1)
  refine ⟨{
    S := T
    infinite := hTinfinite
    memChart := hcurveU
    pairShift := fun z => selectedPairShiftLine_pairDifference shift₀ hrs z
    simple := fun z hz => hz.2.1
    analytic := ?_
    base := ?_
    root := ?_ }⟩
  · intro z hz i
    exact (C.analyticOn_branch i (point z 0) hz.1).fun_comp_of_eq
      (selectedPairChartPoint_analyticAt_coupling shift₀ r s z 0) rfl
  · intro z hz i
    exact hz.2.2 i
  · intro z hz i
    filter_upwards [hcurveU z hz] with g hg
    have hroot := C.root (point z g) hg i
    simpa [hpointdef, selectedPairChartPoint, localExtensionMatrix_selectedLayer] using hroot

end

end GaloisForLFunctions.HTGeometry
