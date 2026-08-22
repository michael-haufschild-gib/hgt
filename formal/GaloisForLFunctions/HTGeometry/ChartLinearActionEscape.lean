import GaloisForLFunctions.HTGeometry.ChartQuadraticRateEscape

/-!
# Constant spectral actions escape a one-qubit local-extension chart

The second-order pole packet does not merely rule out a selected quadratic
rate identity.  Differentiating any locally constant linear spectral action
twice produces the same pole packet with constant multiplier one.  Its crown
graph is connected after at most one exceptional ordered gap, so every
coefficient must coincide.  Consequently every nonconstant spectral action
escapes every prescribed value inside the physical local-extension chart.
-/

open Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- **Linear-action rigidity on a one-qubit extension chart.**  If a
branchwise linear spectral action is constant throughout the chart, all of
its coefficients are equal. -/
theorem chart_constantAction_coefficients_constant [Nonempty A]
    (hcard : 3 ≤ Fintype.card A)
    {E : A → ℝ} (hE : Function.Injective fun a => (E a : ℂ))
    (hgap : ∀ alpha beta gamma delta : A, alpha ≠ beta → gamma ≠ delta →
      ((E beta : ℂ) - (E alpha : ℂ)) =
        ((E delta : ℂ) - (E gamma : ℂ)) →
      (alpha, beta) = (gamma, delta))
    {M : Matrix A A ℂ}
    (hM : ∀ alpha beta : A, alpha ≠ beta → M alpha beta * M beta alpha ≠ 0)
    {z₀ : ℂ}
    (hbase : Function.Injective
      (layeredEnergy (fun a => (E a : ℂ)) (boolShift z₀)))
    (C : LocalExtensionEigenbranchChart
      (fun a => (E a : ℂ)) (boolShift z₀) M)
    (c : A × Bool → ℂ) (target : ℂ)
    (hident : ∀ p ∈ C.U, ∑ i, c i * C.branch i p = target) :
    ∀ x y, c x = c y := by
  classical
  obtain ⟨D⟩ := exists_selectedLayerSliceData E (boolShift z₀) M hbase C
    (by decide : (false : Bool) ≠ true)
  set V : Matrix (A × Bool) (A × Bool) ℂ :=
    layerCrossPerturbation M with hV
  set bad : Set ℂ :=
    Set.range (fun p : A × A => (E p.2 : ℂ) - (E p.1 : ℂ)) with hbad
  set S' : Set ℂ := D.S \ bad with hS'
  have hS'inf : S'.Infinite := D.infinite.sdiff (Set.finite_range _)
  have hshiftline : ∀ z : ℂ,
      selectedPairShiftLine (boolShift z₀) false true z = boolShift z :=
    fun z => selectedPairShiftLine_boolShift z₀ z
  have havoid : ∀ z ∈ S', z ≠ 0 ∧
      ∀ alpha beta : A, alpha ≠ beta →
        z ≠ (E beta : ℂ) - (E alpha : ℂ) := by
    intro z hz
    refine ⟨?_, fun alpha beta _ hEq => hz.2 ⟨(alpha, beta), hEq.symm⟩⟩
    intro hzero
    obtain ⟨a⟩ : Nonempty A := inferInstance
    exact hz.2 ⟨(a, a), by rw [hzero]; ring⟩
  have hinj : ∀ z ∈ S',
      Function.Injective (layerSplitEnergy (fun a => (E a : ℂ)) z) := by
    intro z hz
    have h := D.simple z hz.1
    rwa [hshiftline z, layeredEnergy_boolShift] at h
  have hbranchA : ∀ z ∈ S', ∀ i,
      AnalyticAt ℂ
        (fun g => C.branch i
          (selectedPairChartPoint (boolShift z₀) false true z g)) 0 :=
    fun z hz i => D.analytic z hz.1 i
  have hbranchBase : ∀ z ∈ S', ∀ i,
      C.branch i (selectedPairChartPoint (boolShift z₀) false true z 0) =
        layerSplitEnergy (fun a => (E a : ℂ)) z i := by
    intro z hz i
    have h := D.base z hz.1 i
    rwa [hshiftline z, layeredEnergy_boolShift] at h
  have hbranchRoot : ∀ z ∈ S', ∀ i,
      ∀ᶠ g in nhds (0 : ℂ),
        matrixCharpolyRelation
          (Matrix.diagonal (layerSplitEnergy (fun a => (E a : ℂ)) z) + g • V,
            C.branch i
              (selectedPairChartPoint (boolShift z₀) false true z g)) = 0 := by
    intro z hz i
    have hroot := D.root z hz.1 i
    filter_upwards [hroot] with g hg
    rwa [hshiftline z, layeredEnergy_boolShift,
      selectedLayerCoupling_bool] at hg
  have hpacket : ∀ z ∈ S',
      (∑ alpha, ∑ beta,
        (c (alpha, false) - c (beta, true)) *
          (M alpha beta * M beta alpha) /
            (z + (E alpha : ℂ) - (E beta : ℂ))) = 0 := by
    intro z hz
    have hrelation : ∀ᶠ g in nhds (0 : ℂ),
        ∑ i, c i * C.branch i
          (selectedPairChartPoint (boolShift z₀) false true z g) = target := by
      filter_upwards [D.memChart z hz.1] with g hg
      exact hident _ hg
    have hsecond := affineEigenbranch_constant_action_secondOrder
      (layerSplitEnergy (fun a => (E a : ℂ)) z) (hinj z hz)
      V (layerCrossPerturbation_diagonal M) c
      (fun i g => C.branch i
        (selectedPairChartPoint (boolShift z₀) false true z g))
      (hbranchA z hz) (hbranchBase z hz) (hbranchRoot z hz) target hrelation
    rw [hV, layerCrossSecondOrder_weighted_sum] at hsecond
    exact hsecond
  have hidentity : ∀ z ∈ S',
      ((1 : ℂ) + 0 * z) *
        (∑ alpha, ∑ beta,
          (c (alpha, false) - c (beta, true)) *
            (M alpha beta * M beta alpha) /
              (z + (E alpha : ℂ) - (E beta : ℂ))) = 0 := by
    intro z hz
    rw [hpacket z hz]
    ring
  obtain ⟨hfalse, htrue, hcross⟩ :=
    extensionPacket_crossPair_constant hcard hE hgap
      (w := fun alpha beta => M alpha beta * M beta alpha) hM
      (fun alpha => c (alpha, false)) (fun beta => c (beta, true))
      (p := 1) (q := 0) (cst := 0) (Or.inl one_ne_zero)
      hS'inf havoid hidentity
  rintro ⟨x, bx⟩ ⟨y, b_y⟩
  cases bx <;> cases b_y
  · exact hfalse x y
  · exact hcross x y
  · exact (hcross y x).symm
  · exact htrue x y

/-- **Affine escape on a one-qubit local-extension chart.**  Every
nonconstant spectral action escapes every prescribed complex value inside
the same chart. -/
theorem exists_chart_linearAction_ne_const [Nonempty A]
    (hcard : 3 ≤ Fintype.card A)
    {E : A → ℝ} (hE : Function.Injective fun a => (E a : ℂ))
    (hgap : ∀ alpha beta gamma delta : A, alpha ≠ beta → gamma ≠ delta →
      ((E beta : ℂ) - (E alpha : ℂ)) =
        ((E delta : ℂ) - (E gamma : ℂ)) →
      (alpha, beta) = (gamma, delta))
    {M : Matrix A A ℂ}
    (hM : ∀ alpha beta : A, alpha ≠ beta → M alpha beta * M beta alpha ≠ 0)
    {z₀ : ℂ}
    (hbase : Function.Injective
      (layeredEnergy (fun a => (E a : ℂ)) (boolShift z₀)))
    (C : LocalExtensionEigenbranchChart
      (fun a => (E a : ℂ)) (boolShift z₀) M)
    (c : A × Bool → ℂ) (hc : ¬ ∀ x y, c x = c y)
    (target : ℂ) :
    ∃ p ∈ C.U, ∑ i, c i * C.branch i p ≠ target := by
  by_contra hcon
  push Not at hcon
  exact hc (chart_constantAction_coefficients_constant
    hcard hE hgap hM hbase C c target hcon)

end

end GaloisForLFunctions.HTGeometry
