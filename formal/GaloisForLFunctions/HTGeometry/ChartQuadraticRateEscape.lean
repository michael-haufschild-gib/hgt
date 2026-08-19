/-
# Quadratic-rate rigidity on a one-qubit extension chart

The rigidity theorem for a quadratic-rate identity is stated on the split-spectrum slice
`diag(layerSplitEnergy E z) + g·layerCrossPerturbation M`.  A one-qubit local-extension chart
restricts to exactly that slice: the new local alphabet is `Bool`, the base shift is the split
`±z₀/2`, the selected pair is `(false, true)`, and the selected-pair curve carries the base shift
to `±z/2` and the exchange matrix to the cross perturbation.

Consequently a chart-wide quadratic-rate identity -- with the rate the trace of the square of the
chart Hamiltonian, which is what `Q(H) = D^{-1} Tr(H²)` is -- forces the coefficient packet to
vanish.  The rate has no linear term along the slice, so it has the shape the rigidity theorem
consumes.

Main results:
* `boolShift`, `layeredEnergy_boolShift`, `selectedPairShiftLine_boolShift`,
  `selectedLayerCoupling_bool` — the identifications.
* `chart_quadraticRate_eq_zero` — chart-wide quadratic-rate rigidity.
* `exists_chart_quadraticRate_ne` — its contrapositive, the chart escape.
-/
import GaloisForLFunctions.HTGeometry.SelectedLayerSliceData
import GaloisForLFunctions.HTGeometry.LocalExtensionQuadraticRateFlatCollapse
import GaloisForLFunctions.HTGeometry.LayerSliceQuadraticTrace

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The split base shift `±z/2` of a one-qubit extension. -/
def boolShift (z : ℂ) : Bool → ℂ := fun b => if b then -(z / 2) else z / 2

variable {A : Type*} [Fintype A] [DecidableEq A]

omit [Fintype A] [DecidableEq A] in
theorem layeredEnergy_boolShift (E : A → ℂ) (z : ℂ) :
    layeredEnergy E (boolShift z) = layerSplitEnergy E z := by
  funext p
  rw [layeredEnergy, layerSplitEnergy, boolShift]

omit [Fintype A] [DecidableEq A] in
theorem selectedPairShiftLine_boolShift (z₀ z : ℂ) :
    selectedPairShiftLine (boolShift z₀) false true z = boolShift z := by
  funext u
  cases u <;> simp [selectedPairShiftLine, boolShift] <;> ring

omit [Fintype A] [DecidableEq A] in
theorem selectedLayerCoupling_bool (M : Matrix A A ℂ) :
    selectedLayerCoupling M false true = layerCrossPerturbation M := by
  ext x y
  rw [selectedLayerCoupling, layerCrossPerturbation]
  cases hx : x.2 <;> cases hy : y.2 <;> simp [hx, hy]

/-- **Quadratic-rate rigidity on a chart.**  A zero-sum coefficient packet satisfying the
quadratic-rate identity throughout a one-qubit local-extension chart vanishes. -/
theorem chart_quadraticRate_eq_zero [Nonempty A] (hcard : 3 ≤ Fintype.card A)
    {E : A → ℝ} (hE : Function.Injective fun a => (E a : ℂ))
    (hgap : ∀ α β γ δ : A, α ≠ β → γ ≠ δ →
      ((E β : ℂ) - (E α : ℂ)) = ((E δ : ℂ) - (E γ : ℂ)) → (α, β) = (γ, δ))
    {M : Matrix A A ℂ} (hMherm : M.IsHermitian) (hM : ∀ α β : A, α ≠ β → M α β * M β α ≠ 0)
    {z₀ : ℂ}
    (hbase : Function.Injective (layeredEnergy (fun a => (E a : ℂ)) (boolShift z₀)))
    (C : LocalExtensionEigenbranchChart (fun a => (E a : ℂ)) (boolShift z₀) M)
    (c : A × Bool → ℂ) (κ : ℂ)
    (hident : ∀ p ∈ C.U, (∑ i, c i * C.branch i p) ^ 2
      = κ * ((localExtensionMatrix (fun a => (E a : ℂ)) p.1 M p.2) ^ 2).trace)
    (hzero : ∑ i, c i = 0) : c = 0 := by
  classical
  obtain ⟨D⟩ := exists_selectedLayerSliceData E (boolShift z₀) M hbase C
    (by decide : (false : Bool) ≠ true)
  set V : Matrix (A × Bool) (A × Bool) ℂ := layerCrossPerturbation M with hV
  have hMne : M ≠ 0 := by
    obtain ⟨a, b, hab⟩ : ∃ a b : A, a ≠ b := by
      have : 1 < Fintype.card A := by omega
      exact Fintype.exists_pair_of_one_lt_card this
    intro h0
    exact hM a b hab (by rw [h0]; simp)
  have hQv : (V ^ 2).trace ≠ 0 := trace_sq_layerCrossPerturbation_ne_zero hMherm hMne
  set bad : Set ℂ := Set.range (fun p : A × A => (E p.2 : ℂ) - (E p.1 : ℂ)) with hbad
  set S' : Set ℂ := D.S \ bad with hS'
  have hS'inf : S'.Infinite := D.infinite.sdiff (Set.finite_range _)
  have hshiftline : ∀ z : ℂ, selectedPairShiftLine (boolShift z₀) false true z = boolShift z :=
    fun z => selectedPairShiftLine_boolShift z₀ z
  have havoid : ∀ z ∈ S', z ≠ 0 ∧ ∀ α β : A, α ≠ β → z ≠ (E β : ℂ) - (E α : ℂ) := by
    intro z hz
    refine ⟨?_, fun α β _ hEq => hz.2 ⟨(α, β), hEq.symm⟩⟩
    intro h0
    obtain ⟨a⟩ : Nonempty A := inferInstance
    exact hz.2 ⟨(a, a), by rw [h0]; ring⟩
  have hinj : ∀ z ∈ S', Function.Injective (layerSplitEnergy (fun a => (E a : ℂ)) z) := by
    intro z hz
    have := D.simple z hz.1
    rwa [hshiftline z, layeredEnergy_boolShift] at this
  have hbranchA : ∀ z ∈ S', ∀ i,
      AnalyticAt ℂ (fun g => C.branch i (selectedPairChartPoint (boolShift z₀) false true z g)) 0 :=
    fun z hz i => D.analytic z hz.1 i
  have hbranchBase : ∀ z ∈ S', ∀ i,
      C.branch i (selectedPairChartPoint (boolShift z₀) false true z 0)
        = layerSplitEnergy (fun a => (E a : ℂ)) z i := by
    intro z hz i
    have := D.base z hz.1 i
    rwa [hshiftline z, layeredEnergy_boolShift] at this
  have hslicemat : ∀ z g : ℂ,
      localExtensionMatrix (fun a => (E a : ℂ))
          (selectedPairChartPoint (boolShift z₀) false true z g).1 M
          (selectedPairChartPoint (boolShift z₀) false true z g).2
        = Matrix.diagonal (layerSplitEnergy (fun a => (E a : ℂ)) z) + g • V := by
    intro z g
    show localExtensionMatrix (fun a => (E a : ℂ)) (selectedPairShiftLine (boolShift z₀) false true z) M
        (g • selectedLayerExchangeMatrix false true) = _
    rw [localExtensionMatrix_selectedLayer, hshiftline z, layeredEnergy_boolShift,
      selectedLayerCoupling_bool]
  have hbranchRoot : ∀ z ∈ S', ∀ i, ∀ᶠ g in 𝓝 (0 : ℂ),
      matrixCharpolyRelation
        (Matrix.diagonal (layerSplitEnergy (fun a => (E a : ℂ)) z) + g • V,
          C.branch i (selectedPairChartPoint (boolShift z₀) false true z g)) = 0 := by
    intro z hz i
    have hr := D.root z hz.1 i
    filter_upwards [hr] with g hg
    rwa [hshiftline z, layeredEnergy_boolShift, selectedLayerCoupling_bool] at hg
  have hidentSlice : ∀ z ∈ S', ∀ᶠ g in 𝓝 (0 : ℂ),
      (∑ i, c i * C.branch i (selectedPairChartPoint (boolShift z₀) false true z g)) ^ 2
        = κ * ((∑ x, layerSplitEnergy (fun a => (E a : ℂ)) z x ^ 2) + g ^ 2 * (V ^ 2).trace) := by
    intro z hz
    filter_upwards [D.memChart z hz.1] with g hg
    have h := hident (selectedPairChartPoint (boolShift z₀) false true z g) hg
    rw [hslicemat z g, trace_sq_layerExtensionSlice] at h
    exact h
  exact localExtension_quadraticRate_eq_zero_unconditional hcard hE hgap hM c hQv hS'inf
    havoid hinj
    (fun z i g => C.branch i (selectedPairChartPoint (boolShift z₀) false true z g))
    hbranchA hbranchBase hbranchRoot hidentSlice hzero

/-- **The chart escape.**  A nonzero zero-sum coefficient packet fails the quadratic-rate identity
somewhere in the chart. -/
theorem exists_chart_quadraticRate_ne [Nonempty A] (hcard : 3 ≤ Fintype.card A)
    {E : A → ℝ} (hE : Function.Injective fun a => (E a : ℂ))
    (hgap : ∀ α β γ δ : A, α ≠ β → γ ≠ δ →
      ((E β : ℂ) - (E α : ℂ)) = ((E δ : ℂ) - (E γ : ℂ)) → (α, β) = (γ, δ))
    {M : Matrix A A ℂ} (hMherm : M.IsHermitian) (hM : ∀ α β : A, α ≠ β → M α β * M β α ≠ 0)
    {z₀ : ℂ}
    (hbase : Function.Injective (layeredEnergy (fun a => (E a : ℂ)) (boolShift z₀)))
    (C : LocalExtensionEigenbranchChart (fun a => (E a : ℂ)) (boolShift z₀) M)
    (c : A × Bool → ℂ) (κ : ℂ) (hzero : ∑ i, c i = 0) (hcne : c ≠ 0) :
    ∃ p ∈ C.U, (∑ i, c i * C.branch i p) ^ 2
      ≠ κ * ((localExtensionMatrix (fun a => (E a : ℂ)) p.1 M p.2) ^ 2).trace := by
  by_contra hcon
  push Not at hcon
  exact hcne (chart_quadraticRate_eq_zero hcard hE hgap hMherm hM hbase C c κ hcon hzero)

end

end GaloisForLFunctions.HTGeometry
