import GaloisForLFunctions.HTGeometry.HermitianLocalExtensionChart
import GaloisForLFunctions.HTGeometry.LocalExtensionChartSelectedWitness
import GaloisForLFunctions.HTGeometry.RealFiniteAnalyticEscape
import GaloisForLFunctions.HTGeometry.HermitianLocalSpectralObserverLaw
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# Relation escape on the Hermitian local-extension slice

Vanishing along a real selected exchange line forces vanishing of its
one-complex-variable analytic continuation.  Therefore the interaction
lift rigidity mechanism remains available after restricting the local
extension chart to physical Hermitian Hamiltonians.
-/

open Filter Topology
open scoped Matrix.Norms.Elementwise

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Eventual vanishing on the real axis forces a one-variable complex
analytic germ to vanish. -/
theorem AnalyticAt.eventuallyEq_zero_of_eventually_ofReal_eq_zero
    {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0)
    (hreal : ∀ᶠ x : ℝ in 𝓝 0, f x = 0) :
    ∀ᶠ z : ℂ in 𝓝 0, f z = 0 := by
  apply hf.frequently_zero_iff_eventually_zero.mp
  rw [Filter.frequently_iff]
  intro U hU
  have ht :
      Tendsto Complex.ofReal
        (𝓝[≠] (0 : ℝ)) (𝓝[≠] (0 : ℂ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      Complex.ofReal
    · convert
        (tendsto_nhdsWithin_of_tendsto_nhds
          Complex.continuous_ofReal.continuousAt.tendsto) using 1
      all_goals simp
    · filter_upwards [self_mem_nhdsWithin] with x hx
      simpa [Complex.ofReal_ne_zero] using hx
  have hpreU :
      {x : ℝ | (x : ℂ) ∈ U} ∈ 𝓝[≠] (0 : ℝ) :=
    ht hU
  have hreal' :
      {x : ℝ | f x = 0} ∈ 𝓝[≠] (0 : ℝ) :=
    (show 𝓝[≠] (0 : ℝ) ≤ 𝓝 0 from inf_le_left) hreal
  have hboth :
      {x : ℝ | (x : ℂ) ∈ U ∧ f x = 0} ∈
        𝓝[≠] (0 : ℝ) := by
    exact inter_mem hpreU hreal'
  have hbothEventually :
      ∀ᶠ x : ℝ in 𝓝[≠] 0,
        (x : ℂ) ∈ U ∧ f x = 0 :=
    hboth
  obtain ⟨x, hxU, hxf⟩ := hbothEventually.exists
  exact ⟨(x : ℂ), hxU, hxf⟩

/-- Real selected-pair shift line. -/
def realSelectedPairShiftLine
    {ρ : Type*} [DecidableEq ρ]
    (shift₀ : ρ → ℝ) (r s : ρ) (z : ℝ) : ρ → ℝ :=
  fun u =>
    let z₀ := shift₀ r - shift₀ s
    if u = r then shift₀ r + (z - z₀) / 2
    else if u = s then shift₀ s - (z - z₀) / 2
    else shift₀ u

/-- Real exchange matrix on one unordered local-label pair. -/
def realSelectedLayerExchangeMatrix
    {ρ : Type*} [DecidableEq ρ] (r s : ρ) :
    Matrix ρ ρ ℝ :=
  fun u v =>
    if (u = r ∧ v = s) ∨ (u = s ∧ v = r)
    then 1 else 0

/-- Real two-parameter selected-pair curve. -/
def realSelectedPairChartPoint
    {ρ : Type*} [DecidableEq ρ]
    (shift₀ : ρ → ℝ) (r s : ρ) (z g : ℝ) :
    (ρ → ℝ) × Matrix ρ ρ ℝ :=
  (realSelectedPairShiftLine shift₀ r s z,
    g • realSelectedLayerExchangeMatrix r s)

theorem realSelectedPairShiftLine_complexification
    {ρ : Type*} [DecidableEq ρ]
    (shift₀ : ρ → ℝ) (r s : ρ) (z : ℝ) :
    (fun u => ((realSelectedPairShiftLine shift₀ r s z u : ℝ) : ℂ)) =
      selectedPairShiftLine (fun u => (shift₀ u : ℂ))
        r s (z : ℂ) := by
  ext u
  by_cases hur : u = r
  · subst u
    simp [realSelectedPairShiftLine, selectedPairShiftLine]
  · by_cases hus : u = s
    · subst u
      simp [realSelectedPairShiftLine,
        selectedPairShiftLine, hur]
    · simp [realSelectedPairShiftLine,
        selectedPairShiftLine, hur, hus]

theorem realSelectedPairChartPoint_complexification
    {ρ : Type*} [DecidableEq ρ]
    (shift₀ : ρ → ℝ) (r s : ρ) (z g : ℝ) :
    realLocalExtensionParameter
        (realSelectedPairChartPoint shift₀ r s z g) =
      selectedPairChartPoint
        (fun u => (shift₀ u : ℂ)) r s (z : ℂ) (g : ℂ) := by
  apply Prod.ext
  · exact realSelectedPairShiftLine_complexification
      shift₀ r s z
  · exact realSymmetricEdge_selectedLayerExchange r s g

@[simp] theorem realSelectedPairChartPoint_base
    {ρ : Type*} [DecidableEq ρ]
    (shift₀ : ρ → ℝ) (r s : ρ) :
    realSelectedPairChartPoint shift₀ r s
        (shift₀ r - shift₀ s) 0 =
      (shift₀, 0) := by
  apply Prod.ext
  · funext u
    by_cases hur : u = r
    · subst u
      simp [realSelectedPairChartPoint,
        realSelectedPairShiftLine]
    · by_cases hus : u = s
      · subst u
        simp [realSelectedPairChartPoint,
          realSelectedPairShiftLine, hur]
      · simp [realSelectedPairChartPoint,
          realSelectedPairShiftLine, hur, hus]
  · ext u v
    simp [realSelectedPairChartPoint]

theorem realSelectedPairChartPoint_continuous
    {ρ : Type*} [Fintype ρ] [DecidableEq ρ]
    (shift₀ : ρ → ℝ) (r s : ρ) :
    Continuous
      (fun p : ℝ × ℝ =>
        realSelectedPairChartPoint
          shift₀ r s p.1 p.2) := by
  apply Continuous.prodMk
  · change Continuous
      (fun p : ℝ × ℝ =>
        realSelectedPairShiftLine shift₀ r s p.1)
    apply continuous_pi
    intro u
    simp only [realSelectedPairShiftLine]
    split_ifs <;> fun_prop
  · change Continuous
      (fun p : ℝ × ℝ =>
        p.2 • realSelectedLayerExchangeMatrix r s)
    fun_prop

/-- A spectral relation holding on a real open neighbourhood of the
uncoupled physical slice supplies every complex selected-layer witness
needed by interaction-lift rigidity. -/
noncomputable def
    LocalExtensionEigenbranchChart.realSelectedLayerWitness
    {α ρ : Type*} [Fintype α] [Fintype ρ]
    [DecidableEq α] [DecidableEq ρ]
    [Nonempty α]
    (energy : α → ℝ) (shift₀ : ρ → ℝ)
    (transition : Matrix α α ℂ)
    (hsimple :
      Function.Injective
        (layeredEnergy
          (fun a => (energy a : ℂ))
          (fun r => (shift₀ r : ℂ))))
    (C :
      LocalExtensionEigenbranchChart
        (fun a => (energy a : ℂ))
        (fun r => (shift₀ r : ℂ)) transition)
    (V : Set ((ρ → ℝ) × Matrix ρ ρ ℝ))
    (hVopen : IsOpen V)
    (hVcenter : (shift₀, 0) ∈ V)
    (hVU :
      ∀ p ∈ V,
        realLocalExtensionParameter p ∈ C.U)
    (coefficient : α × ρ → ℂ)
    (hrelation :
      ∀ p ∈ V,
        ∑ i, coefficient i *
          C.branch i (realLocalExtensionParameter p) = 0)
    {r s : ρ} (hrs : r ≠ s) :
    SelectedLayerAnalyticRelationWitness
      energy transition coefficient r s := by
  let z₀R : ℝ := shift₀ r - shift₀ s
  let z₀ : ℂ := (z₀R : ℂ)
  let shiftC : ℂ → ρ → ℂ :=
    selectedPairShiftLine
      (fun u => (shift₀ u : ℂ)) r s
  let pointC : ℂ → ℂ →
      (ρ → ℂ) × Matrix ρ ρ ℂ :=
    selectedPairChartPoint
      (fun u => (shift₀ u : ℂ)) r s
  let pointR : ℝ → ℝ →
      (ρ → ℝ) × Matrix ρ ρ ℝ :=
    realSelectedPairChartPoint shift₀ r s
  let explicitEnergy : ℂ → α × ρ → ℂ :=
    fun z => layeredEnergy
      (fun a => (energy a : ℂ)) (shiftC z)
  let restrictedBranch : ℂ → α × ρ → ℂ → ℂ :=
    fun z i g => C.branch i (pointC z g)
  have hpointAnalytic :
      AnalyticAt ℂ (fun z => pointC z 0) z₀ := by
    exact selectedPairChartPoint_analyticAt_shift
      (fun u => (shift₀ u : ℂ)) r s z₀
  have hpointBase :
      pointC z₀ 0 =
        ((fun u => (shift₀ u : ℂ)), 0) := by
    simp [pointC, z₀, z₀R]
  have hpointU :
      ∀ᶠ z in 𝓝 z₀, pointC z 0 ∈ C.U := by
    have hmem := C.isOpen_U.mem_nhds C.center_mem
    have htend :
        Tendsto (fun z => pointC z 0) (𝓝 z₀)
          (𝓝 ((fun u => (shift₀ u : ℂ)), 0)) := by
      have ht := hpointAnalytic.continuousAt
      change Tendsto (fun z => pointC z 0) (𝓝 z₀)
        (𝓝 (pointC z₀ 0)) at ht
      rw [hpointBase] at ht
      exact ht
    exact htend hmem
  have hlabel :
      ∀ i, restrictedBranch z₀ i 0 =
        explicitEnergy z₀ i := by
    intro i
    change C.branch i (pointC z₀ 0) =
      layeredEnergy
        (fun a => (energy a : ℂ)) (shiftC z₀) i
    rw [hpointBase, C.base]
    congr 2
    simpa [shiftC, z₀, z₀R] using
      (selectedPairShiftLine_base
        (fun u => (shift₀ u : ℂ)) r s).symm
  have hlabelGerm :
      ∀ i,
        (fun z => restrictedBranch z i 0) =ᶠ[𝓝 z₀]
          (fun z => explicitEnergy z i) := by
    intro i
    let H : ℂ → Matrix (α × ρ) (α × ρ) ℂ :=
      fun z =>
        localExtensionMatrix
          (fun a => (energy a : ℂ))
          (pointC z 0).1 transition (pointC z 0).2
    have hHan : AnalyticAt ℂ H z₀ := by
      exact
        (localExtensionMatrix_analyticAt
          (fun a => (energy a : ℂ)) transition
          ((fun u => (shift₀ u : ℂ)), 0)).fun_comp_of_eq
          hpointAnalytic hpointBase
    have hHt :
        Tendsto H (𝓝 z₀)
          (𝓝 (Matrix.diagonal
            (layeredEnergy
              (fun a => (energy a : ℂ))
              (fun u => (shift₀ u : ℂ))))) := by
      have hcont := hHan.continuousAt
      change Tendsto H (𝓝 z₀) (𝓝 (H z₀)) at hcont
      have hHz₀ :
          H z₀ =
            Matrix.diagonal
              (layeredEnergy
                (fun a => (energy a : ℂ))
                (fun u => (shift₀ u : ℂ))) := by
        simp [H, hpointBase, localExtensionMatrix_zero]
      rw [hHz₀] at hcont
      exact hcont
    have hbranchAn :
        AnalyticAt ℂ
          (fun z => restrictedBranch z i 0) z₀ := by
      apply
        (C.analyticOn_branch i
          ((fun u => (shift₀ u : ℂ)), 0)
          C.center_mem).fun_comp_of_eq
      · exact hpointAnalytic
      · exact hpointBase
    have hbranchT :
        Tendsto (fun z => restrictedBranch z i 0)
          (𝓝 z₀)
          (𝓝 (layeredEnergy
            (fun a => (energy a : ℂ))
            (fun u => (shift₀ u : ℂ)) i)) := by
      have hcont := hbranchAn.continuousAt
      change Tendsto (fun z => restrictedBranch z i 0)
        (𝓝 z₀) (𝓝 (restrictedBranch z₀ i 0)) at hcont
      have heq :
          explicitEnergy z₀ i =
            layeredEnergy
              (fun a => (energy a : ℂ))
              (fun u => (shift₀ u : ℂ)) i := by
        simp [explicitEnergy, shiftC, z₀, z₀R,
          selectedPairShiftLine_base]
      rw [hlabel i, heq] at hcont
      exact hcont
    have hexplicitAn :
        AnalyticAt ℂ
          (fun z => explicitEnergy z i) z₀ := by
      exact analyticAt_const.add
        (analyticAt_pi_iff.mp
          (selectedPairShiftLine_analyticAt
            (fun u => (shift₀ u : ℂ)) r s z₀) i.2)
    have hexplicitT :
        Tendsto (fun z => explicitEnergy z i)
          (𝓝 z₀)
          (𝓝 (layeredEnergy
            (fun a => (energy a : ℂ))
            (fun u => (shift₀ u : ℂ)) i)) := by
      have hcont := hexplicitAn.continuousAt
      change Tendsto (fun z => explicitEnergy z i)
        (𝓝 z₀) (𝓝 (explicitEnergy z₀ i)) at hcont
      have heq :
          explicitEnergy z₀ i =
            layeredEnergy
              (fun a => (energy a : ℂ))
              (fun u => (shift₀ u : ℂ)) i := by
        simp [explicitEnergy, shiftC, z₀, z₀R,
          selectedPairShiftLine_base]
      rw [heq] at hcont
      exact hcont
    have hbranchRoot :
        ∀ᶠ z in 𝓝 z₀,
          matrixCharpolyRelation
            (H z, restrictedBranch z i 0) = 0 := by
      filter_upwards [hpointU] with z hz
      exact C.root (pointC z 0) hz i
    have hexplicitRoot :
        ∀ᶠ z in 𝓝 z₀,
          matrixCharpolyRelation
            (H z, explicitEnergy z i) = 0 := by
      filter_upwards [] with z
      simpa [H, pointC, selectedPairChartPoint,
        localExtensionMatrix_zero, explicitEnergy,
        shiftC] using
          (matrixCharpolyRelation_diagonal_root
            (explicitEnergy z) i)
    exact simpleDiagonalMatrix_root_germs_unique
      (layeredEnergy
        (fun a => (energy a : ℂ))
        (fun u => (shift₀ u : ℂ)))
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
                (fun u => (shift₀ u : ℂ))
                r s z₀) i.2)).sub
          (analyticAt_const.add
            (analyticAt_pi_iff.mp
              (selectedPairShiftLine_analyticAt
                (fun u => (shift₀ u : ℂ))
                r s z₀) j.2))
      have hdiffNe :
          explicitEnergy z₀ i -
              explicitEnergy z₀ j ≠ 0 := by
        rw [sub_ne_zero]
        intro heq
        apply hij
        apply hsimple
        simpa [explicitEnergy, shiftC, z₀, z₀R,
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
  have hpointRContinuous :
      ContinuousAt (fun x => pointR x 0) z₀R := by
    have hpair :
        Continuous (fun x : ℝ => (x, (0 : ℝ))) :=
      continuous_id.prodMk continuous_const
    exact
      (realSelectedPairChartPoint_continuous
        shift₀ r s).continuousAt.comp hpair.continuousAt
  have hpointRBase :
      pointR z₀R 0 = (shift₀, 0) := by
    simp [pointR, z₀R]
  have hpointRV :
      ∀ᶠ x in 𝓝 z₀R, pointR x 0 ∈ V := by
    have hVn :
        V ∈ 𝓝 (pointR z₀R 0) := by
      rw [hpointRBase]
      exact hVopen.mem_nhds hVcenter
    exact hpointRContinuous hVn
  have hcomplexConditions :
      ∀ᶠ x : ℝ in 𝓝 z₀R,
        Function.Injective (explicitEnergy (x : ℂ)) ∧
        ∀ i,
          restrictedBranch (x : ℂ) i 0 =
            explicitEnergy (x : ℂ) i := by
    have ht :
        Tendsto (fun x : ℝ => (x : ℂ))
          (𝓝 z₀R) (𝓝 z₀) := by
      simpa [z₀] using
        Complex.continuous_ofReal.continuousAt.tendsto
    filter_upwards
      [ht.eventually hsimpleGerm,
       ht.eventually hlabelAll] with x hxs hxl
    exact ⟨hxs, hxl⟩
  let Sr : Set ℝ :=
    {x |
      pointR x 0 ∈ V ∧
      Function.Injective (explicitEnergy (x : ℂ)) ∧
      ∀ i,
        restrictedBranch (x : ℂ) i 0 =
          explicitEnergy (x : ℂ) i}
  have hSrnhds : Sr ∈ 𝓝 z₀R := by
    filter_upwards [hpointRV, hcomplexConditions]
      with x hxV hx
    exact ⟨hxV, hx⟩
  have hSrinfinite : Sr.Infinite :=
    infinite_of_mem_nhds z₀R hSrnhds
  let S : Set ℂ := Complex.ofReal '' Sr
  have hSinfinite : S.Infinite :=
    hSrinfinite.image Complex.ofReal_injective.injOn
  refine {
    S := S
    infinite := hSinfinite
    shift := shiftC
    pairShift := ?_
    simple := ?_
    branch := restrictedBranch
    analytic := ?_
    base := ?_
    root := ?_
    relation := ?_
  }
  · intro z hz
    obtain ⟨x, hx, rfl⟩ := hz
    exact selectedPairShiftLine_pairDifference
      (fun u => (shift₀ u : ℂ)) hrs (x : ℂ)
  · intro z hz
    obtain ⟨x, hx, rfl⟩ := hz
    exact hx.2.1
  · intro z hz i
    obtain ⟨x, hx, rfl⟩ := hz
    have hpointCU :
        pointC (x : ℂ) 0 ∈ C.U := by
      have heq :
          realLocalExtensionParameter (pointR x 0) =
            pointC (x : ℂ) 0 := by
        simpa [pointR, pointC] using
          (realSelectedPairChartPoint_complexification
            shift₀ r s x 0)
      rw [← heq]
      exact hVU (pointR x 0) hx.1
    have hpointCurve :=
      selectedPairChartPoint_analyticAt_coupling
        (fun u => (shift₀ u : ℂ)) r s (x : ℂ) 0
    apply
      (C.analyticOn_branch i
        (pointC (x : ℂ) 0) hpointCU).fun_comp_of_eq
    · exact hpointCurve
    · rfl
  · intro z hz i
    obtain ⟨x, hx, rfl⟩ := hz
    exact hx.2.2 i
  · intro z hz i
    obtain ⟨x, hx, rfl⟩ := hz
    have hpointCU :
        pointC (x : ℂ) 0 ∈ C.U := by
      have heq :
          realLocalExtensionParameter (pointR x 0) =
            pointC (x : ℂ) 0 := by
        simpa [pointR, pointC] using
          (realSelectedPairChartPoint_complexification
            shift₀ r s x 0)
      rw [← heq]
      exact hVU (pointR x 0) hx.1
    have hpointCurve :=
      selectedPairChartPoint_analyticAt_coupling
        (fun u => (shift₀ u : ℂ)) r s (x : ℂ) 0
    have hpointEventually :
        ∀ᶠ g in 𝓝 0, pointC (x : ℂ) g ∈ C.U :=
      hpointCurve.continuousAt
        (C.isOpen_U.mem_nhds hpointCU)
    filter_upwards [hpointEventually] with g hg
    have hroot := C.root (pointC (x : ℂ) g) hg i
    simpa [pointC, shiftC, restrictedBranch,
      selectedPairChartPoint,
      localExtensionMatrix_selectedLayer] using hroot
  · intro z hz
    obtain ⟨x, hx, rfl⟩ := hz
    let f : ℂ → ℂ :=
      fun g =>
        ∑ i, coefficient i *
          restrictedBranch (x : ℂ) i g
    have hpointCU :
        pointC (x : ℂ) 0 ∈ C.U := by
      have heq :
          realLocalExtensionParameter (pointR x 0) =
            pointC (x : ℂ) 0 := by
        simpa [pointR, pointC] using
          (realSelectedPairChartPoint_complexification
            shift₀ r s x 0)
      rw [← heq]
      exact hVU (pointR x 0) hx.1
    have hfAnalytic : AnalyticAt ℂ f 0 := by
      apply Finset.analyticAt_fun_sum
      intro i hi
      exact analyticAt_const.mul
        ((C.analyticOn_branch i
          (pointC (x : ℂ) 0) hpointCU).fun_comp_of_eq
          (selectedPairChartPoint_analyticAt_coupling
            (fun u => (shift₀ u : ℂ)) r s (x : ℂ) 0)
          rfl)
    have hrealCurve :
        ContinuousAt (fun g : ℝ => pointR x g) 0 := by
      have hpair :
          Continuous (fun g : ℝ => (x, g)) :=
        continuous_const.prodMk continuous_id
      exact
        (realSelectedPairChartPoint_continuous
          shift₀ r s).continuousAt.comp hpair.continuousAt
    have hrealV :
        ∀ᶠ g : ℝ in 𝓝 0, pointR x g ∈ V :=
      hrealCurve (hVopen.mem_nhds hx.1)
    have hfReal :
        ∀ᶠ g : ℝ in 𝓝 0, f g = 0 := by
      filter_upwards [hrealV] with g hg
      have hrel := hrelation (pointR x g) hg
      have heq :
          realLocalExtensionParameter (pointR x g) =
            pointC (x : ℂ) (g : ℂ) := by
        simpa [pointR, pointC] using
          (realSelectedPairChartPoint_complexification
            shift₀ r s x g)
      rw [heq] at hrel
      exact hrel
    exact
      AnalyticAt.eventuallyEq_zero_of_eventually_ofReal_eq_zero
        hfAnalytic hfReal

/-- **Physical one-step local relation erasure.** Under a Hermitian
transition channel with connected interaction lift, every nonzero balanced
integer spectral relation can be erased by real onsite shifts and a
real-symmetric tensor-local edge control.  The resulting Hermitian matrix
has a simple real characteristic-root packet whose unordered coefficient
obstruction is nonzero. -/
theorem
    exists_hermitianLocalExtension_simpleRealRootPacket_coefficientObstruction_ne_zero
    {α ρ : Type*} [Fintype α] [Fintype ρ]
    [DecidableEq α] [DecidableEq ρ]
    [Nonempty α] [Nonempty ρ]
    (energy : α → ℝ) (hmax : MaximallyProjectiveEnergy energy)
    (shift₀ : ρ → ℝ)
    (transition : Matrix α α ℂ)
    (htransition : transition.IsHermitian)
    (hsimple :
      Function.Injective
        (layeredEnergy
          (fun a => (energy a : ℂ))
          (fun r => (shift₀ r : ℂ))))
    (hlift :
      (crossLayerLiftGraph
        (transitionSupportGraph transition) ρ).Preconnected)
    (k : α × ρ → ℤ)
    (hbalanced : SpectralCharacterBalanced k) (hk : k ≠ 0) :
    ∃ p : (ρ → ℝ) × Matrix ρ ρ ℝ,
      ∃ extendedEnergy : α × ρ → ℝ,
        Function.Injective extendedEnergy ∧
        (∀ i,
          matrixCharpolyRelation
            (localExtensionMatrix
                (fun a => (energy a : ℂ))
                (realLocalExtensionParameter p).1
                transition
                (realLocalExtensionParameter p).2,
              (extendedEnergy i : ℂ)) = 0) ∧
        MvPolynomial.eval₂ (Rat.castHom ℝ)
            (fun i : Fin (Fintype.card (α × ρ)) =>
              MvPolynomial.eval₂ (Rat.castHom ℝ)
                extendedEnergy
                (MvPolynomial.esymm (α × ρ) ℚ (i + 1)))
            (spectralRelationCoefficientPolynomial k) ≠ 0 := by
  let complexShift₀ : ρ → ℂ :=
    fun r => (shift₀ r : ℂ)
  let center :
      (ρ → ℝ) × Matrix ρ ρ ℝ :=
    (shift₀, 0)
  let C :
      LocalExtensionEigenbranchChart
        (fun a => (energy a : ℂ))
        complexShift₀ transition :=
    Classical.choice
      (exists_localExtensionEigenbranchChart
        (fun a => (energy a : ℂ))
        complexShift₀ transition hsimple)
  have hcenterComplex :
      realLocalExtensionParameter center =
        (complexShift₀, 0) := by
    simp [center, complexShift₀]
  have hparameterContinuous :
      ContinuousAt
        (realLocalExtensionParameter :
          ((ρ → ℝ) × Matrix ρ ρ ℝ) →
            (ρ → ℂ) × Matrix ρ ρ ℂ)
        center :=
    (realLocalExtensionParameter_analyticAt center).continuousAt
  have hpreimageNhd :
      {p |
        realLocalExtensionParameter p ∈ C.U} ∈ 𝓝 center := by
    apply hparameterContinuous
    rw [hcenterComplex]
    exact C.isOpen_U.mem_nhds C.center_mem
  obtain ⟨ε, hε, hball⟩ :=
    Metric.mem_nhds_iff.mp hpreimageNhd
  let V :
      Set ((ρ → ℝ) × Matrix ρ ρ ℝ) :=
    Metric.ball center ε
  have hVopen : IsOpen V :=
    Metric.isOpen_ball
  have hVconnected : IsPreconnected V :=
    Metric.isPreconnected_ball
  have hVcenter : center ∈ V := by
    simpa [V] using hε
  have hVU :
      ∀ p ∈ V,
        realLocalExtensionParameter p ∈ C.U := by
    intro p hp
    exact hball hp
  let branchR :
      α × ρ →
        ((ρ → ℝ) × Matrix ρ ρ ℝ) → ℂ :=
    fun i p =>
      C.branch i (realLocalExtensionParameter p)
  have hbranchR :
      ∀ i, AnalyticOnNhd ℝ (branchR i) V := by
    intro i p hp
    apply
      ((C.analyticOn_branch i
        (realLocalExtensionParameter p)
        (hVU p hp)).restrictScalars).comp
    exact realLocalExtensionParameter_analyticAt p
  let relationR :
      Equiv.Perm (α × ρ) →
        ((ρ → ℝ) × Matrix ρ ρ ℝ) → ℂ :=
    fun σ =>
      permutedAnalyticSpectralRelation k branchR σ
  have hrelationR :
      ∀ σ, AnalyticOnNhd ℝ (relationR σ) V := by
    intro σ p hp
    apply Finset.analyticAt_fun_sum
    intro i hi
    exact analyticAt_const.mul
      (hbranchR (σ i) p hp)
  have hlabel :
      ∀ σ : Equiv.Perm (α × ρ),
        ∃ p ∈ V, relationR σ p ≠ 0 := by
    intro σ
    by_contra hnone
    push Not at hnone
    have hfixed :
        ∀ p ∈ V,
          ∑ i,
            permutedSpectralCoefficient k σ i *
              C.branch i
                (realLocalExtensionParameter p) = 0 := by
      intro p hp
      rw [sum_permutedSpectralCoefficient_eq_relation]
      exact hnone p hp
    have hconstant :
        ∀ x y,
          permutedSpectralCoefficient k σ x =
            permutedSpectralCoefficient k σ y :=
      selectedLayerAnalyticRelation_constant_of_preconnected
        energy hmax transition
        (permutedSpectralCoefficient k σ)
        (fun r s hrs =>
          C.realSelectedLayerWitness
            energy shift₀ transition hsimple
            V hVopen
            (by simpa [center] using hVcenter)
            hVU
            (permutedSpectralCoefficient k σ)
            hfixed hrs)
        hlift
    exact
      (permutedSpectralCoefficient_not_constant
        hbalanced hk σ) hconstant
  obtain ⟨p, hpV, hpAll⟩ :=
    exists_forall_neZero_of_finite_analyticOnNhd_real_local
      relationR V hVopen hVconnected
      ⟨center, hVcenter⟩ hrelationR hlabel
  have hpU :
      realLocalExtensionParameter p ∈ C.U :=
    hVU p hpV
  let complexEnergy : α × ρ → ℂ :=
    fun i => C.branch i (realLocalExtensionParameter p)
  have hroot :
      ∀ i,
        matrixCharpolyRelation
          (localExtensionMatrix
              (fun a => (energy a : ℂ))
              (realLocalExtensionParameter p).1
              transition
              (realLocalExtensionParameter p).2,
            complexEnergy i) = 0 :=
    C.root (realLocalExtensionParameter p) hpU
  have hmatrixHermitian :
      (localExtensionMatrix
        (fun a => (energy a : ℂ))
        (realLocalExtensionParameter p).1
        transition
        (realLocalExtensionParameter p).2).IsHermitian :=
    localExtensionMatrix_realParameter_isHermitian
      energy transition htransition p
  have him : ∀ i, (complexEnergy i).im = 0 := by
    intro i
    exact
      matrixCharpolyRelation_im_eq_zero_of_isHermitian
        _ hmatrixHermitian _ (hroot i)
  let extendedEnergy : α × ρ → ℝ :=
    fun i => (complexEnergy i).re
  have hcomplexEnergy :
      ∀ i, complexEnergy i = (extendedEnergy i : ℂ) := by
    intro i
    apply Complex.ext
    · rfl
    · simpa [extendedEnergy] using him i
  have hextendedInjective :
      Function.Injective extendedEnergy := by
    intro i j hij
    apply (C.simple (realLocalExtensionParameter p) hpU)
    change complexEnergy i = complexEnergy j
    rw [hcomplexEnergy i, hcomplexEnergy j, hij]
  have hrealLabel :
      ∀ σ : Equiv.Perm (α × ρ),
        ∑ i, (k i : ℝ) * extendedEnergy (σ i) ≠ 0 := by
    intro σ hzero
    have hcomplexZero :
        relationR σ p = 0 := by
      unfold relationR
      unfold permutedAnalyticSpectralRelation
      rw [show branchR =
          fun i p =>
            C.branch i (realLocalExtensionParameter p) by rfl]
      change
        (∑ i, (k i : ℂ) *
          complexEnergy (σ i)) = 0
      simp_rw [hcomplexEnergy]
      exact_mod_cast hzero
    exact hpAll σ hcomplexZero
  have hcoefficient :
      MvPolynomial.eval₂ (Rat.castHom ℝ)
          (fun i : Fin (Fintype.card (α × ρ)) =>
            MvPolynomial.eval₂ (Rat.castHom ℝ)
              extendedEnergy
              (MvPolynomial.esymm (α × ρ) ℚ (i + 1)))
          (spectralRelationCoefficientPolynomial k) ≠ 0 := by
    rw [eval₂_spectralRelationCoefficientPolynomial_real_esymm,
      eval₂_spectralRelationOrbitPolynomial_real]
    exact
      (spectralRelationOrbitValue_ne_zero_iff
        k extendedEnergy).mpr hrealLabel
  refine ⟨p, extendedEnergy,
    hextendedInjective, ?_, hcoefficient⟩
  intro i
  rw [← hcomplexEnergy i]
  exact hroot i

/-- Countable index of all nonzero projective spectral characters. -/
def BalancedNonzeroSpectralCharacter
    (I : Type*) [Fintype I] :=
  {k : I → ℤ //
    SpectralCharacterBalanced k ∧ k ≠ 0}

/-- **Simultaneous physical local rank explosion.** One Hermitian
tensor-local extension erases every nonzero balanced integer spectral
relation at once. -/
theorem
    exists_hermitianLocalExtension_maximallyProjectiveRealRootPacket
    {α ρ : Type*} [Fintype α] [Fintype ρ]
    [DecidableEq α] [DecidableEq ρ]
    [Nonempty α] [Nonempty ρ]
    (energy : α → ℝ) (hmax : MaximallyProjectiveEnergy energy)
    (shift₀ : ρ → ℝ)
    (transition : Matrix α α ℂ)
    (htransition : transition.IsHermitian)
    (hsimple :
      Function.Injective
        (layeredEnergy
          (fun a => (energy a : ℂ))
          (fun r => (shift₀ r : ℂ))))
    (hlift :
      (crossLayerLiftGraph
        (transitionSupportGraph transition) ρ).Preconnected) :
    ∃ p : (ρ → ℝ) × Matrix ρ ρ ℝ,
      ∃ extendedEnergy : α × ρ → ℝ,
        MaximallyProjectiveEnergy extendedEnergy ∧
        Function.Injective extendedEnergy ∧
        ∀ i,
          matrixCharpolyRelation
            (localExtensionMatrix
                (fun a => (energy a : ℂ))
                (realLocalExtensionParameter p).1
                transition
                (realLocalExtensionParameter p).2,
              (extendedEnergy i : ℂ)) = 0 := by
  let complexShift₀ : ρ → ℂ :=
    fun r => (shift₀ r : ℂ)
  let center :
      (ρ → ℝ) × Matrix ρ ρ ℝ :=
    (shift₀, 0)
  let C :
      LocalExtensionEigenbranchChart
        (fun a => (energy a : ℂ))
        complexShift₀ transition :=
    Classical.choice
      (exists_localExtensionEigenbranchChart
        (fun a => (energy a : ℂ))
        complexShift₀ transition hsimple)
  have hcenterComplex :
      realLocalExtensionParameter center =
        (complexShift₀, 0) := by
    simp [center, complexShift₀]
  have hpreimageNhd :
      {p |
        realLocalExtensionParameter p ∈ C.U} ∈
          𝓝 center := by
    have hcont :=
      (realLocalExtensionParameter_analyticAt
        center).continuousAt
    apply hcont
    rw [hcenterComplex]
    exact C.isOpen_U.mem_nhds C.center_mem
  obtain ⟨ε, hε, hball⟩ :=
    Metric.mem_nhds_iff.mp hpreimageNhd
  let V :
      Set ((ρ → ℝ) × Matrix ρ ρ ℝ) :=
    Metric.ball center ε
  have hVopen : IsOpen V :=
    Metric.isOpen_ball
  have hVconnected : IsPreconnected V :=
    Metric.isPreconnected_ball
  have hVcenter : center ∈ V := by
    simpa [V] using hε
  have hVU :
      ∀ p ∈ V,
        realLocalExtensionParameter p ∈ C.U :=
    fun p hp => hball hp
  let branchR :
      α × ρ →
        ((ρ → ℝ) × Matrix ρ ρ ℝ) → ℂ :=
    fun i p =>
      C.branch i (realLocalExtensionParameter p)
  have hbranchR :
      ∀ i, AnalyticOnNhd ℝ (branchR i) V := by
    intro i p hp
    apply
      ((C.analyticOn_branch i
        (realLocalExtensionParameter p)
        (hVU p hp)).restrictScalars).comp
    exact realLocalExtensionParameter_analyticAt p
  let J :=
    BalancedNonzeroSpectralCharacter (α × ρ) ×
      Equiv.Perm (α × ρ)
  let relationAll :
      J → ((ρ → ℝ) × Matrix ρ ρ ℝ) → ℂ :=
    fun j =>
      permutedAnalyticSpectralRelation
        j.1.1 branchR j.2
  have hrelationAll :
      ∀ j, AnalyticOnNhd ℝ (relationAll j) V := by
    intro j p hp
    apply Finset.analyticAt_fun_sum
    intro i hi
    exact analyticAt_const.mul
      (hbranchR (j.2 i) p hp)
  have hlabel :
      ∀ j : J,
        ∃ p ∈ V, relationAll j p ≠ 0 := by
    intro j
    by_contra hnone
    push Not at hnone
    have hfixed :
        ∀ p ∈ V,
          ∑ i,
            permutedSpectralCoefficient j.1.1 j.2 i *
              C.branch i
                (realLocalExtensionParameter p) = 0 := by
      intro p hp
      rw [sum_permutedSpectralCoefficient_eq_relation]
      exact hnone p hp
    have hconstant :
        ∀ x y,
          permutedSpectralCoefficient j.1.1 j.2 x =
            permutedSpectralCoefficient j.1.1 j.2 y :=
      selectedLayerAnalyticRelation_constant_of_preconnected
        energy hmax transition
        (permutedSpectralCoefficient j.1.1 j.2)
        (fun r s hrs =>
          C.realSelectedLayerWitness
            energy shift₀ transition hsimple
            V hVopen
            (by simpa [center] using hVcenter)
            hVU
            (permutedSpectralCoefficient j.1.1 j.2)
            hfixed hrs)
        hlift
    exact
      (permutedSpectralCoefficient_not_constant
        j.1.2.1 j.1.2.2 j.2) hconstant
  letI : Countable J := by
    dsimp [J, BalancedNonzeroSpectralCharacter]
    infer_instance
  obtain ⟨p, hpV, hpAll⟩ :=
    exists_forall_neZero_of_countable_analyticOnNhd_real_local
      relationAll V hVopen hVconnected
      ⟨center, hVcenter⟩ hrelationAll hlabel
  have hpU :
      realLocalExtensionParameter p ∈ C.U :=
    hVU p hpV
  let complexEnergy : α × ρ → ℂ :=
    fun i =>
      C.branch i (realLocalExtensionParameter p)
  have hroot :
      ∀ i,
        matrixCharpolyRelation
          (localExtensionMatrix
              (fun a => (energy a : ℂ))
              (realLocalExtensionParameter p).1
              transition
              (realLocalExtensionParameter p).2,
            complexEnergy i) = 0 :=
    C.root (realLocalExtensionParameter p) hpU
  have hmatrixHermitian :
      (localExtensionMatrix
        (fun a => (energy a : ℂ))
        (realLocalExtensionParameter p).1
        transition
        (realLocalExtensionParameter p).2).IsHermitian :=
    localExtensionMatrix_realParameter_isHermitian
      energy transition htransition p
  have him : ∀ i, (complexEnergy i).im = 0 := by
    intro i
    exact
      matrixCharpolyRelation_im_eq_zero_of_isHermitian
        _ hmatrixHermitian _ (hroot i)
  let extendedEnergy : α × ρ → ℝ :=
    fun i => (complexEnergy i).re
  have hcomplexEnergy :
      ∀ i, complexEnergy i = (extendedEnergy i : ℂ) := by
    intro i
    apply Complex.ext
    · rfl
    · simpa [extendedEnergy] using him i
  have hextendedMax :
      MaximallyProjectiveEnergy extendedEnergy := by
    intro k hkbalanced hksum
    by_contra hk
    let j : J :=
      (⟨k, hkbalanced, hk⟩, Equiv.refl (α × ρ))
    apply hpAll j
    unfold relationAll
    unfold permutedAnalyticSpectralRelation
    change
      (∑ i, (k i : ℂ) *
        complexEnergy i) = 0
    simp_rw [hcomplexEnergy]
    exact_mod_cast hksum
  have hextendedInjective :
      Function.Injective extendedEnergy := by
    intro i j hij
    apply C.simple
      (realLocalExtensionParameter p) hpU
    change complexEnergy i = complexEnergy j
    rw [hcomplexEnergy i, hcomplexEnergy j, hij]
  refine ⟨p, extendedEnergy,
    hextendedMax, hextendedInjective, ?_⟩
  intro i
  rw [← hcomplexEnergy i]
  exact hroot i

end

end GaloisForLFunctions.HTGeometry
