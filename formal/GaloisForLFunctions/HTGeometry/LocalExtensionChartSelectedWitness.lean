import GaloisForLFunctions.HTGeometry.LocalExtensionMatrixChart
import GaloisForLFunctions.HTGeometry.LocalInteractionSpectralRelationEscape

/-!
# Selected-layer witnesses from the concrete local-extension chart

The common eigenbranch chart restricts to every selected local-label
exchange line.  Spectral labels remain fixed on a whole neighbourhood of
the base shift by uniqueness of simple characteristic-root germs.  That
neighbourhood is infinite, providing the exact witness required by the
interaction-lift relation theorem.
-/

open Filter Topology
open scoped Matrix.Norms.Elementwise

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Two-parameter selected-pair curve inside the concrete local-extension
parameter space. -/
def selectedPairChartPoint
    {ρ : Type*} [DecidableEq ρ]
    (shift₀ : ρ → ℂ) (r s : ρ) (z g : ℂ) :
    (ρ → ℂ) × Matrix ρ ρ ℂ :=
  (selectedPairShiftLine shift₀ r s z,
    g • selectedLayerExchangeMatrix r s)

@[simp] theorem selectedPairChartPoint_base
    {ρ : Type*} [DecidableEq ρ]
    (shift₀ : ρ → ℂ) (r s : ρ) :
    selectedPairChartPoint shift₀ r s
        (shift₀ r - shift₀ s) 0 =
      (shift₀, 0) := by
  simp [selectedPairChartPoint, selectedPairShiftLine_base]

theorem selectedPairChartPoint_analyticAt_shift
    {ρ : Type*} [Fintype ρ] [DecidableEq ρ]
    (shift₀ : ρ → ℂ) (r s : ρ) (z₀ : ℂ) :
    AnalyticAt ℂ
      (fun z => selectedPairChartPoint shift₀ r s z 0) z₀ := by
  exact
    (selectedPairShiftLine_analyticAt shift₀ r s z₀).prod
      analyticAt_const

theorem selectedPairChartPoint_analyticAt_coupling
    {ρ : Type*} [Fintype ρ] [DecidableEq ρ]
    (shift₀ : ρ → ℂ) (r s : ρ) (z g₀ : ℂ) :
    AnalyticAt ℂ
      (selectedPairChartPoint shift₀ r s z) g₀ := by
  exact analyticAt_const.prod
    (analyticAt_id.smul analyticAt_const)

/-- A relation holding throughout the common concrete chart automatically
supplies the selected-layer analytic witness for every chosen local pair. -/
noncomputable def LocalExtensionEigenbranchChart.selectedLayerWitness
    {α ρ : Type*} [Fintype α] [Fintype ρ]
    [DecidableEq α] [DecidableEq ρ]
    [Nonempty α]
    (energy : α → ℝ) (shift₀ : ρ → ℂ)
    (transition : Matrix α α ℂ)
    (hsimple :
      Function.Injective
        (layeredEnergy (fun a => (energy a : ℂ)) shift₀))
    (C :
      LocalExtensionEigenbranchChart
        (fun a => (energy a : ℂ)) shift₀ transition)
    (coefficient : α × ρ → ℂ)
    (hrelation :
      ∀ p ∈ C.U,
        ∑ i, coefficient i * C.branch i p = 0)
    {r s : ρ} (hrs : r ≠ s) :
    SelectedLayerAnalyticRelationWitness
      energy transition coefficient r s := by
  let z₀ : ℂ := shift₀ r - shift₀ s
  let shift : ℂ → ρ → ℂ :=
    selectedPairShiftLine shift₀ r s
  let point : ℂ → ℂ →
      (ρ → ℂ) × Matrix ρ ρ ℂ :=
    selectedPairChartPoint shift₀ r s
  let explicitEnergy : ℂ → α × ρ → ℂ :=
    fun z => layeredEnergy
      (fun a => (energy a : ℂ)) (shift z)
  let restrictedBranch : ℂ → α × ρ → ℂ → ℂ :=
    fun z i g => C.branch i (point z g)
  have hpointAnalytic :
      AnalyticAt ℂ (fun z => point z 0) z₀ := by
    exact selectedPairChartPoint_analyticAt_shift
      shift₀ r s z₀
  have hpointBase : point z₀ 0 = (shift₀, 0) := by
    exact selectedPairChartPoint_base shift₀ r s
  have hpointU :
      ∀ᶠ z in 𝓝 z₀, point z 0 ∈ C.U := by
    have hmem := C.isOpen_U.mem_nhds C.center_mem
    have htend :
        Tendsto (fun z => point z 0) (𝓝 z₀) (𝓝 (shift₀, 0)) := by
      have ht := hpointAnalytic.continuousAt
      change Tendsto (fun z => point z 0) (𝓝 z₀)
        (𝓝 (point z₀ 0)) at ht
      rw [hpointBase] at ht
      exact ht
    exact htend hmem
  have hlabel :
      ∀ i, restrictedBranch z₀ i 0 =
        explicitEnergy z₀ i := by
    intro i
    change C.branch i (point z₀ 0) =
      layeredEnergy (fun a => (energy a : ℂ)) (shift z₀) i
    rw [hpointBase, C.base]
    congr 2
    exact (selectedPairShiftLine_base shift₀ r s).symm
  have hlabelGerm :
      ∀ i,
        (fun z => restrictedBranch z i 0) =ᶠ[𝓝 z₀]
          (fun z => explicitEnergy z i) := by
    intro i
    let H : ℂ → Matrix (α × ρ) (α × ρ) ℂ :=
      fun z =>
        localExtensionMatrix
          (fun a => (energy a : ℂ))
          (point z 0).1 transition (point z 0).2
    have hHan : AnalyticAt ℂ H z₀ := by
      exact
        (localExtensionMatrix_analyticAt
          (fun a => (energy a : ℂ)) transition
          (shift₀, 0)).fun_comp_of_eq
          hpointAnalytic hpointBase
    have hHt :
        Tendsto H (𝓝 z₀)
          (𝓝 (Matrix.diagonal
            (layeredEnergy
              (fun a => (energy a : ℂ)) shift₀))) := by
      have hcont := hHan.continuousAt
      change Tendsto H (𝓝 z₀) (𝓝 (H z₀)) at hcont
      have hHz₀ :
          H z₀ =
            Matrix.diagonal
              (layeredEnergy
                (fun a => (energy a : ℂ)) shift₀) := by
        simp [H, hpointBase, localExtensionMatrix_zero]
      rw [hHz₀] at hcont
      exact hcont
    have hbranchAn :
        AnalyticAt ℂ
          (fun z => restrictedBranch z i 0) z₀ := by
      apply
        (C.analyticOn_branch i
          (shift₀, 0) C.center_mem).fun_comp_of_eq
      · exact hpointAnalytic
      · exact hpointBase
    have hbranchT :
        Tendsto (fun z => restrictedBranch z i 0)
          (𝓝 z₀)
          (𝓝 (layeredEnergy
            (fun a => (energy a : ℂ)) shift₀ i)) := by
      have hcont := hbranchAn.continuousAt
      change Tendsto (fun z => restrictedBranch z i 0)
        (𝓝 z₀) (𝓝 (restrictedBranch z₀ i 0)) at hcont
      have heq :
          explicitEnergy z₀ i =
            layeredEnergy
              (fun a => (energy a : ℂ)) shift₀ i := by
        simp [explicitEnergy, shift, z₀,
          selectedPairShiftLine_base]
      rw [hlabel i, heq] at hcont
      exact hcont
    have hexplicitAn :
        AnalyticAt ℂ (fun z => explicitEnergy z i) z₀ := by
      exact analyticAt_const.add
        (analyticAt_pi_iff.mp
          (selectedPairShiftLine_analyticAt
            shift₀ r s z₀) i.2)
    have hexplicitT :
        Tendsto (fun z => explicitEnergy z i)
          (𝓝 z₀)
          (𝓝 (layeredEnergy
              (fun a => (energy a : ℂ)) shift₀ i)) := by
      have hcont := hexplicitAn.continuousAt
      change Tendsto (fun z => explicitEnergy z i)
        (𝓝 z₀) (𝓝 (explicitEnergy z₀ i)) at hcont
      have heq :
          explicitEnergy z₀ i =
            layeredEnergy
              (fun a => (energy a : ℂ)) shift₀ i := by
        simp [explicitEnergy, shift, z₀,
          selectedPairShiftLine_base]
      rw [heq] at hcont
      exact hcont
    have hbranchRoot :
        ∀ᶠ z in 𝓝 z₀,
          matrixCharpolyRelation
            (H z, restrictedBranch z i 0) = 0 := by
      filter_upwards [hpointU] with z hz
      exact C.root (point z 0) hz i
    have hexplicitRoot :
        ∀ᶠ z in 𝓝 z₀,
          matrixCharpolyRelation
            (H z, explicitEnergy z i) = 0 := by
      filter_upwards [] with z
      simpa [H, point, selectedPairChartPoint,
        localExtensionMatrix_zero, explicitEnergy,
        shift] using
          (matrixCharpolyRelation_diagonal_root
            (explicitEnergy z) i)
    exact simpleDiagonalMatrix_root_germs_unique
      (layeredEnergy (fun a => (energy a : ℂ)) shift₀)
      hsimple i hHt hbranchT hexplicitT
      hbranchRoot hexplicitRoot
  have hlabelAll :
      ∀ᶠ z in 𝓝 z₀,
        ∀ i, restrictedBranch z i 0 =
          explicitEnergy z i := by
    rw [Filter.eventually_all]
    exact hlabelGerm
  have hsimpleGerm :
      ∀ᶠ z in 𝓝 z₀,
        Function.Injective (explicitEnergy z) := by
    have hpairs :
        ∀ i j : α × ρ, i ≠ j →
          ∀ᶠ z in 𝓝 z₀,
            explicitEnergy z i ≠
              explicitEnergy z j := by
      intro i j hij
      have hdiffAn :
          AnalyticAt ℂ
            (fun z =>
              explicitEnergy z i -
                explicitEnergy z j) z₀ := by
        exact
          (analyticAt_const.add
            (analyticAt_pi_iff.mp
              (selectedPairShiftLine_analyticAt
                shift₀ r s z₀) i.2)).sub
          (analyticAt_const.add
            (analyticAt_pi_iff.mp
              (selectedPairShiftLine_analyticAt
                shift₀ r s z₀) j.2))
      have hdiffNe :
          explicitEnergy z₀ i -
              explicitEnergy z₀ j ≠ 0 := by
        rw [sub_ne_zero]
        intro heq
        apply hij
        apply hsimple
        simpa [explicitEnergy, shift, z₀,
          selectedPairShiftLine_base] using heq
      have hev :=
        hdiffAn.continuousAt
          (isOpen_ne.mem_nhds hdiffNe)
      filter_upwards [hev] with z hz
      exact sub_ne_zero.mp hz
    have hall :
        ∀ᶠ z in 𝓝 z₀,
          ∀ i j : α × ρ, i ≠ j →
            explicitEnergy z i ≠
              explicitEnergy z j := by
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
  let S : Set ℂ :=
    {z |
      point z 0 ∈ C.U ∧
      Function.Injective (explicitEnergy z) ∧
      ∀ i, restrictedBranch z i 0 =
        explicitEnergy z i}
  have hSnhds : S ∈ 𝓝 z₀ := by
    filter_upwards [hpointU, hsimpleGerm, hlabelAll]
      with z hzU hzsimple hzlabel
    exact ⟨hzU, hzsimple, hzlabel⟩
  have hSinfinite : S.Infinite :=
    infinite_of_mem_nhds z₀ hSnhds
  refine {
    S := S
    infinite := hSinfinite
    shift := shift
    pairShift := ?_
    simple := ?_
    branch := restrictedBranch
    analytic := ?_
    base := ?_
    root := ?_
    relation := ?_
  }
  · intro z hz
    exact selectedPairShiftLine_pairDifference
      shift₀ hrs z
  · intro z hz
    exact hz.2.1
  · intro z hz i
    have hpointCurve :=
      selectedPairChartPoint_analyticAt_coupling
        shift₀ r s z 0
    apply
      (C.analyticOn_branch i (point z 0) hz.1).fun_comp_of_eq
    · exact hpointCurve
    · rfl
  · intro z hz i
    exact hz.2.2 i
  · intro z hz i
    have hpointCurve :=
      selectedPairChartPoint_analyticAt_coupling
        shift₀ r s z 0
    have hpointEventually :
        ∀ᶠ g in 𝓝 0, point z g ∈ C.U :=
      hpointCurve.continuousAt
        (C.isOpen_U.mem_nhds hz.1)
    filter_upwards [hpointEventually] with g hg
    have hroot := C.root (point z g) hg i
    simpa [point, shift, restrictedBranch,
      selectedPairChartPoint,
      localExtensionMatrix_selectedLayer] using hroot
  · intro z hz
    have hpointCurve :=
      selectedPairChartPoint_analyticAt_coupling
        shift₀ r s z 0
    have hpointEventually :
        ∀ᶠ g in 𝓝 0, point z g ∈ C.U :=
      hpointCurve.continuousAt
        (C.isOpen_U.mem_nhds hz.1)
    filter_upwards [hpointEventually] with g hg
    exact hrelation (point z g) hg

/-- **Concrete one-step local relation erasure.** If the old energy packet
is maximally projective and one transition channel has connected
interaction lift on the new local alphabet, then every nonzero balanced
integer relation has a tensor-local product-spectrum extension with simple
spectrum on which its unordered coefficient obstruction is nonzero. -/
theorem exists_localExtension_simpleRootPacket_coefficientObstruction_ne_zero
    {α ρ : Type*} [Fintype α] [Fintype ρ]
    [DecidableEq α] [DecidableEq ρ]
    [Nonempty α] [Nonempty ρ]
    (energy : α → ℝ) (hmax : MaximallyProjectiveEnergy energy)
    (shift₀ : ρ → ℂ)
    (transition : Matrix α α ℂ)
    (hsimple :
      Function.Injective
        (layeredEnergy (fun a => (energy a : ℂ)) shift₀))
    (hlift :
      (crossLayerLiftGraph
        (transitionSupportGraph transition) ρ).Preconnected)
    (k : α × ρ → ℤ)
    (hbalanced : SpectralCharacterBalanced k) (hk : k ≠ 0) :
    ∃ p : (ρ → ℂ) × Matrix ρ ρ ℂ,
      ∃ extendedEnergy : α × ρ → ℂ,
        Function.Injective extendedEnergy ∧
        (∀ i,
          matrixCharpolyRelation
            (localExtensionMatrix
                (fun a => (energy a : ℂ))
                p.1 transition p.2,
              extendedEnergy i) = 0) ∧
        MvPolynomial.eval₂ (Rat.castHom ℂ)
            (fun i : Fin (Fintype.card (α × ρ)) =>
              MvPolynomial.eval₂ (Rat.castHom ℂ)
                extendedEnergy
                (MvPolynomial.esymm (α × ρ) ℚ (i + 1)))
            (spectralRelationCoefficientPolynomial k) ≠ 0 := by
  let C :
      LocalExtensionEigenbranchChart
        (fun a => (energy a : ℂ)) shift₀ transition :=
    Classical.choice
      (exists_localExtensionEigenbranchChart
        (fun a => (energy a : ℂ)) shift₀ transition hsimple)
  obtain ⟨p, hpU, hpObstruction⟩ :=
    exists_localInteraction_coefficientObstruction_eval_ne_zero
      energy hmax transition k hbalanced hk
      C.branch C.U C.isOpen_U C.isPreconnected_U
      ⟨(shift₀, 0), C.center_mem⟩
      C.analyticOn_branch
      (fun σ hrelation r s hrs =>
        C.selectedLayerWitness
          energy shift₀ transition hsimple
          (permutedSpectralCoefficient k σ)
          hrelation hrs)
      hlift
  refine ⟨p, fun i => C.branch i p,
    C.simple p hpU, ?_, hpObstruction⟩
  intro i
  exact C.root p hpU i

end

end GaloisForLFunctions.HTGeometry
