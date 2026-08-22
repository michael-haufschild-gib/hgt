import GaloisForLFunctions.HTGeometry.CoupledAllVertexMaximalLeafExtension
import GaloisForLFunctions.HTGeometry.KleinbockMargulis.ProjectiveRatioAffineEscape

/-!
# Physical recurrence on an ordinary local-extension slice

The full real onsite-plus-edge coordinate slice of one time-independent
local extension carries a connected analytic simple-spectrum chart.  The
local interaction-lift rigidity theorem makes every nonconstant affine
spectral action escape on that physical chart.  Kleinbock--Margulis
extremality then gives the optimal continuous return exponent, including
the dimensional energy scale, for almost every Hamiltonian in the same
chart.
-/

open scoped BigOperators Matrix.Norms.Elementwise
open Set Topology MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Physical analytic local-extension chart with affine spectral
escape.**  The canonical real finite-coordinate slice contains an open
connected ball on which the complete labelled spectrum is simple and real
analytic.  Every nonconstant real spectral action escapes every prescribed
target inside that same ball. -/
theorem exists_localExtensionSliceRealAnalyticChart_affineEscape
    {α ρ : Type*} [Fintype α] [Fintype ρ]
    [DecidableEq α] [DecidableEq ρ]
    [Nonempty α] [Nonempty ρ]
    (baseEnergy : α → ℝ) (hmax : MaximallyProjectiveEnergy baseEnergy)
    (shift₀ : ρ → ℝ)
    (transition : Matrix α α ℂ)
    (htransition : transition.IsHermitian)
    (hsimple :
      Function.Injective
        (layeredEnergy
          (fun a => (baseEnergy a : ℂ))
          (fun r => (shift₀ r : ℂ))))
    (hlift :
      (crossLayerLiftGraph
        (transitionSupportGraph transition) ρ).Preconnected) :
    ∃ (U : Set (Fin (localExtensionSliceParameterCount ρ) → ℝ))
      (p₀ : Fin (localExtensionSliceParameterCount ρ) → ℝ)
      (energy : (α × ρ) →
        (Fin (localExtensionSliceParameterCount ρ) → ℝ) → ℝ),
      IsOpen U ∧ IsPreconnected U ∧ p₀ ∈ U ∧
      (∀ i, AnalyticOnNhd ℝ (energy i) U) ∧
      (∀ q ∈ U, Function.Injective fun i => energy i q) ∧
      (∀ c : α × ρ → ℝ,
        (¬ ∀ x y, c x = c y) → ∀ target : ℝ,
          ∃ q ∈ U, (∑ i, c i * energy i q) ≠ target) := by
  classical
  let C := Classical.choice
    (exists_localExtensionEigenbranchChart
      (fun a => (baseEnergy a : ℂ))
      (fun r => (shift₀ r : ℂ)) transition hsimple)
  let p₀R : (ρ → ℝ) × Matrix ρ ρ ℝ := (shift₀, 0)
  let p₀ : Fin (localExtensionSliceParameterCount ρ) → ℝ :=
    localExtensionSliceCoordinates p₀R
  let physicalParameter :
      (Fin (localExtensionSliceParameterCount ρ) → ℝ) →
        (ρ → ℂ) × Matrix ρ ρ ℂ :=
    realLocalExtensionParameter ∘ localExtensionSliceParameter
  have hp₀decode : localExtensionSliceParameter p₀ = p₀R := by
    exact localExtensionSliceParameter_coordinates p₀R
  have hp₀physical :
      physicalParameter p₀ =
        ((fun r => (shift₀ r : ℂ)), 0) := by
    simp only [physicalParameter, Function.comp_apply, hp₀decode, p₀R]
    exact realLocalExtensionParameter_center shift₀
  have hphysicalContinuous : Continuous physicalParameter := by
    exact (realLocalExtensionParameter_continuous (ρ := ρ)).comp
      (localExtensionSliceParameter_continuous (ρ := ρ))
  have hpreOpen : IsOpen (physicalParameter ⁻¹' C.U) :=
    C.isOpen_U.preimage hphysicalContinuous
  have hp₀pre : p₀ ∈ physicalParameter ⁻¹' C.U := by
    simpa only [Set.mem_preimage, hp₀physical] using C.center_mem
  obtain ⟨epsilon, hepsilon, hball⟩ := Metric.mem_nhds_iff.mp
    (hpreOpen.mem_nhds hp₀pre)
  let U : Set (Fin (localExtensionSliceParameterCount ρ) → ℝ) :=
    Metric.ball p₀ epsilon
  let energy : (α × ρ) →
      (Fin (localExtensionSliceParameterCount ρ) → ℝ) → ℝ :=
    fun i q => (C.branch i (physicalParameter q)).re
  have hUtoChart : ∀ q ∈ U, physicalParameter q ∈ C.U := by
    intro q hq
    exact hball hq
  have hphysicalAnalytic : ∀ q, AnalyticAt ℝ physicalParameter q := by
    intro q
    exact (realLocalExtensionParameter_analyticAt
      (localExtensionSliceParameter q)).comp
        (localExtensionSliceParameter_analyticAt q)
  have henergy : ∀ i, AnalyticOnNhd ℝ (energy i) U := by
    intro i q hq
    have hbranchR : AnalyticAt ℝ (C.branch i) (physicalParameter q) :=
      (C.analyticOn_branch i _ (hUtoChart q hq)).restrictScalars
    have hcomp : AnalyticAt ℝ
        (fun q => C.branch i (physicalParameter q)) q :=
      hbranchR.comp (hphysicalAnalytic q)
    exact (Complex.reCLM.analyticAt _).comp hcomp
  have hbranchReal : ∀ q ∈ U, ∀ i,
      C.branch i (physicalParameter q) = ((energy i q : ℝ) : ℂ) := by
    intro q hq i
    have hroot := C.root (physicalParameter q) (hUtoChart q hq) i
    have him : (C.branch i (physicalParameter q)).im = 0 := by
      apply matrixCharpolyRelation_im_eq_zero_of_isHermitian
        (localExtensionMatrix
          (fun a => (baseEnergy a : ℂ))
          (realLocalExtensionParameter (localExtensionSliceParameter q)).1
          transition
          (realLocalExtensionParameter (localExtensionSliceParameter q)).2)
      · exact localExtensionMatrix_realParameter_isHermitian
          baseEnergy transition htransition (localExtensionSliceParameter q)
      · simpa only [physicalParameter, Function.comp_apply] using hroot
    apply Complex.ext
    · rfl
    · simpa using him
  have henergyInj : ∀ q ∈ U,
      Function.Injective fun i => energy i q := by
    intro q hq i j hij
    apply C.simple (physicalParameter q) (hUtoChart q hq)
    change C.branch i (physicalParameter q) =
      C.branch j (physicalParameter q)
    rw [hbranchReal q hq i, hbranchReal q hq j]
    exact congrArg (fun x : ℝ => (x : ℂ)) hij
  have hescape : ∀ c : α × ρ → ℝ,
      (¬ ∀ x y, c x = c y) → ∀ target : ℝ,
        ∃ q ∈ U, (∑ i, c i * energy i q) ≠ target := by
    intro c hc target
    let V : Set ((ρ → ℝ) × Matrix ρ ρ ℝ) :=
      localExtensionSliceCoordinates ⁻¹' U
    have hVopen : IsOpen V :=
      Metric.isOpen_ball.preimage
        (localExtensionSliceCoordinates_continuous (ρ := ρ))
    have hp₀RV : p₀R ∈ V := by
      change localExtensionSliceCoordinates p₀R ∈ U
      exact Metric.mem_ball_self hepsilon
    have hVtoChart : ∀ p ∈ V,
        realLocalExtensionParameter p ∈ C.U := by
      intro p hp
      have hmem := hUtoChart (localExtensionSliceCoordinates p) hp
      simpa only [physicalParameter, Function.comp_apply,
        localExtensionSliceParameter_coordinates] using hmem
    have hcComplex : ¬ ∀ x y,
        (c x : ℂ) = (c y : ℂ) := by
      intro h
      apply hc
      intro x y
      exact_mod_cast h x y
    obtain ⟨p, hpV, hpne⟩ :=
      exists_hermitianLocalExtension_action_ne_target
        baseEnergy hmax shift₀ transition hsimple hlift C V hVopen
        hp₀RV hVtoChart (fun i => (c i : ℂ)) hcComplex (target : ℂ)
    let q := localExtensionSliceCoordinates p
    have hqU : q ∈ U := hpV
    refine ⟨q, hqU, ?_⟩
    intro heq
    apply hpne
    have hparam : physicalParameter q = realLocalExtensionParameter p := by
      simp only [physicalParameter, Function.comp_apply, q,
        localExtensionSliceParameter_coordinates]
    rw [← hparam]
    calc
      (∑ i, (c i : ℂ) * C.branch i (physicalParameter q)) =
          ∑ i, (c i : ℂ) * ((energy i q : ℝ) : ℂ) := by
            apply Finset.sum_congr rfl
            intro i _hi
            rw [hbranchReal q hqU i]
      _ = (((∑ i, c i * energy i q) : ℝ) : ℂ) := by
            push_cast
            rfl
      _ = (target : ℂ) := congrArg (fun x : ℝ => (x : ℂ)) heq
  exact ⟨U, p₀, energy, Metric.isOpen_ball,
    (convex_ball p₀ epsilon).isPreconnected, Metric.mem_ball_self hepsilon,
    henergy, henergyInj, hescape⟩

/-- **Optimal physical-time recurrence for an ordinary local extension.**
For every connected time-independent Hermitian local-extension family with
at least three levels, the parameters which fail the optimal projective or
physical continuous first-return lower exponent form a Lebesgue-null set
inside one open connected physical chart. -/
theorem exists_localExtensionSlice_optimalContinuousReturn_ae
    {α ρ : Type*} [Fintype α] [Fintype ρ]
    [DecidableEq α] [DecidableEq ρ]
    [Nonempty α] [Nonempty ρ]
    (baseEnergy : α → ℝ) (hmax : MaximallyProjectiveEnergy baseEnergy)
    (shift₀ : ρ → ℝ)
    (transition : Matrix α α ℂ)
    (htransition : transition.IsHermitian)
    (hsimple :
      Function.Injective
        (layeredEnergy
          (fun a => (baseEnergy a : ℂ))
          (fun r => (shift₀ r : ℂ))))
    (hlift :
      (crossLayerLiftGraph
        (transitionSupportGraph transition) ρ).Preconnected)
    (hr : 0 < Fintype.card (α × ρ) - 2) :
    ∃ (U : Set (Fin (localExtensionSliceParameterCount ρ) → ℝ))
      (p₀ : Fin (localExtensionSliceParameterCount ρ) → ℝ)
      (energy : Fin ((Fintype.card (α × ρ) - 2) + 2) →
        (Fin (localExtensionSliceParameterCount ρ) → ℝ) → ℝ),
      IsOpen U ∧ IsPreconnected U ∧ p₀ ∈ U ∧
      (∀ i, AnalyticOnNhd ℝ (energy i) U) ∧
      (∀ q ∈ U, Function.Injective fun i => energy i q) ∧
      volume {q ∈ U |
        ¬ KleinbockMargulis.HasOptimalContinuousReturnLower
          (fun j : Fin (Fintype.card (α × ρ) - 2) =>
            anchoredProjectiveRatio energy q j)} = 0 ∧
      volume {q ∈ U |
        ¬ HasOptimalPhysicalContinuousReturnLower energy q} = 0 := by
  classical
  letI : Nonempty (Sum ρ (ρ × ρ)) :=
    ⟨Sum.inl (Classical.choice (inferInstance : Nonempty ρ))⟩
  letI : NeZero (localExtensionSliceParameterCount ρ) :=
    ⟨Fintype.card_ne_zero⟩
  obtain ⟨U, p₀, rawEnergy, hUopen, hUconn, hp₀U, hrawA,
      hrawInj, hrawEscape⟩ :=
    exists_localExtensionSliceRealAnalyticChart_affineEscape
      baseEnergy hmax shift₀ transition htransition hsimple hlift
  have htwo : 2 ≤ Fintype.card (α × ρ) := by omega
  have hadd : (Fintype.card (α × ρ) - 2) + 2 =
      Fintype.card (α × ρ) := Nat.sub_add_cancel htwo
  let e : Fin ((Fintype.card (α × ρ) - 2) + 2) ≃ α × ρ :=
    (finCongr hadd).trans (Fintype.equivFin (α × ρ)).symm
  let energy : Fin ((Fintype.card (α × ρ) - 2) + 2) →
      (Fin (localExtensionSliceParameterCount ρ) → ℝ) → ℝ :=
    fun i q => rawEnergy (e i) q
  have henergyA : ∀ i, AnalyticOnNhd ℝ (energy i) U := by
    intro i
    exact hrawA (e i)
  have henergyInj : ∀ q ∈ U, Function.Injective fun i => energy i q := by
    intro q hq i j hij
    apply e.injective
    exact hrawInj q hq hij
  have hescape : ∀ c : Fin ((Fintype.card (α × ρ) - 2) + 2) → ℝ,
      (¬ ∀ x y, c x = c y) → ∀ target : ℝ,
        ∃ q ∈ U, (∑ i, c i * energy i q) ≠ target := by
    intro c hc target
    let c' : α × ρ → ℝ := fun x => c (e.symm x)
    have hc' : ¬ ∀ x y, c' x = c' y := by
      intro hconstant
      apply hc
      intro i j
      simpa [c'] using hconstant (e i) (e j)
    obtain ⟨q, hqU, hqne⟩ := hrawEscape c' hc' target
    refine ⟨q, hqU, ?_⟩
    have hsum : (∑ x, c' x * rawEnergy x q) =
        ∑ i, c i * energy i q := by
      exact Fintype.sum_equiv e.symm _ _ (fun x => by simp [c', energy])
    rwa [← hsum]
  have hden : ∀ q ∈ U, energy 1 q - energy 0 q ≠ 0 := by
    intro q hq
    rw [sub_ne_zero]
    intro heq
    have hindex : (1 : Fin ((Fintype.card (α × ρ) - 2) + 2)) = 0 :=
      henergyInj q hq heq
    exact Fin.zero_ne_one hindex.symm
  refine ⟨U, p₀, energy, hUopen, hUconn, hp₀U, henergyA,
    henergyInj, ?_, ?_⟩
  · exact volume_not_optimalReturn_anchoredProjectiveRatio_eq_zero_of_affineEscape
      hr hUopen hUconn energy henergyA p₀ hp₀U hden hescape
  · exact volume_not_optimalPhysicalReturn_eq_zero_of_affineEscape
      hr hUopen hUconn energy henergyA p₀ hp₀U hden hescape

end

end GaloisForLFunctions.HTGeometry
