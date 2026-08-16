import GaloisForLFunctions.HTGeometry.LayerExtensionEndpointCompleteness
import GaloisForLFunctions.HTGeometry.BlockExtensionSecondOrderResponse
import GaloisForLFunctions.HTGeometry.AffineEigenbranchGeneralSecondOrderLaw

/-!
# Endpoint completeness for the canonical eigenvector germs

The canonical adjugate-column eigenvector germs of the split family
`diagonal (layerSplitEnergy E z) + g • layerCrossPerturbation M` are supported at their own label
when the coupling vanishes, and their off-label first derivative is the corresponding matrix
element of the coupling divided by the level gap.

Feeding that into the first-order creation law shows: whenever the old endpoint coupling sees an
old pair, the attached qubit sees the corresponding split pair for all small nonzero coupling.
This is the induction step of endpoint completeness.
-/

open Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- The canonical eigenvector germ of the split family, as a real curve in the coupling. -/
def layerGerm (E : A → ℂ) (z : ℂ) (M : Matrix A A ℂ) (branch : ℂ → ℂ) (x : A × Bool)
    (t : ℝ) : A × Bool → ℂ :=
  fun y => affineEigenbranchAdjugateColumn (layerSplitEnergy E z) (layerCrossPerturbation M)
    branch x (t : ℂ) y

/-- The gap product of a split label. -/
def layerGapProduct (E : A → ℂ) (z : ℂ) (x : A × Bool) : ℂ :=
  ∏ j ∈ Finset.univ.erase x, (layerSplitEnergy E z x - layerSplitEnergy E z j)

theorem layerGapProduct_ne_zero {E : A → ℂ} {z : ℂ}
    (hinj : Function.Injective (layerSplitEnergy E z)) (x : A × Bool) :
    layerGapProduct E z x ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr fun j hj => ?_
  exact sub_ne_zero.mpr fun h => (Finset.mem_erase.mp hj).1 (hinj h).symm

theorem layerGerm_zero (E : A → ℂ) (z : ℂ) (M : Matrix A A ℂ) {branch : ℂ → ℂ} {x : A × Bool}
    (hbase : branch 0 = layerSplitEnergy E z x) (y : A × Bool) :
    layerGerm E z M branch x 0 y = if y = x then layerGapProduct E z x else 0 := by
  simpa [layerGerm, layerGapProduct] using
    affineEigenbranchAdjugateColumn_zero (layerSplitEnergy E z) (layerCrossPerturbation M)
      branch x y hbase

theorem hasDerivAt_layerGerm (E : A → ℂ) (z : ℂ) (M : Matrix A A ℂ) {branch : ℂ → ℂ}
    (x : A × Bool) (hbranch : AnalyticAt ℂ branch 0) (y : A × Bool) :
    HasDerivAt (fun t : ℝ => layerGerm E z M branch x t y)
      (deriv (fun g => affineEigenbranchAdjugateColumn (layerSplitEnergy E z)
        (layerCrossPerturbation M) branch x g y) 0) 0 := by
  have hana := analyticAt_affineEigenbranchAdjugateColumn (layerSplitEnergy E z)
    (layerCrossPerturbation M) branch x hbranch y
  have hcomplex : HasDerivAt
      (fun g => affineEigenbranchAdjugateColumn (layerSplitEnergy E z)
        (layerCrossPerturbation M) branch x g y)
      (deriv (fun g => affineEigenbranchAdjugateColumn (layerSplitEnergy E z)
        (layerCrossPerturbation M) branch x g y) 0) ((0 : ℝ) : ℂ) := by
    simpa using hana.differentiableAt.hasDerivAt
  simpa [layerGerm] using hcomplex.comp_ofReal

/-- **The off-label first derivative of the germ is the coupling element over the gap.** -/
theorem layerGerm_deriv_ne_zero {E : A → ℂ} {z : ℂ}
    (hinj : Function.Injective (layerSplitEnergy E z)) {M : Matrix A A ℂ}
    {branch : ℂ → ℂ} {x y : A × Bool} (hyx : y ≠ x)
    (hbranch : AnalyticAt ℂ branch 0) (hbase : branch 0 = layerSplitEnergy E z x)
    (hroot : ∀ᶠ g in 𝓝 (0 : ℂ), matrixCharpolyRelation
      (Matrix.diagonal (layerSplitEnergy E z) + g • layerCrossPerturbation M, branch g) = 0)
    (hV : layerCrossPerturbation M y x ≠ 0) :
    deriv (fun g => affineEigenbranchAdjugateColumn (layerSplitEnergy E z)
      (layerCrossPerturbation M) branch x g y) 0 ≠ 0 := by
  have hgap := affineEigenbranchAdjugateColumn_deriv_gap_mul_general (layerSplitEnergy E z) hinj
    (layerCrossPerturbation M) x y hyx branch hbranch hbase hroot
  intro hzero
  rw [hzero, mul_zero] at hgap
  exact (mul_ne_zero hV (layerGapProduct_ne_zero hinj x)) hgap.symm

/-- **The induction step of endpoint completeness.**  If the edge coupling sees an old pair, the
attached qubit sees the corresponding split pair for all small nonzero coupling. -/
theorem eventually_layerGerm_endpoint_ne_zero {E : A → ℂ} {z : ℂ}
    (hinj : Function.Injective (layerSplitEnergy E z)) {M : Matrix A A ℂ}
    {α₀ β₀ : A} {r₀ s₀ : Bool} (hM : M β₀ α₀ ≠ 0)
    {branchI branchI' : ℂ → ℂ}
    (hbI : AnalyticAt ℂ branchI 0) (hbaseI : branchI 0 = layerSplitEnergy E z (α₀, r₀))
    (hrootI : ∀ᶠ g in 𝓝 (0 : ℂ), matrixCharpolyRelation
      (Matrix.diagonal (layerSplitEnergy E z) + g • layerCrossPerturbation M, branchI g) = 0)
    (hbI' : AnalyticAt ℂ branchI' 0) (hbaseI' : branchI' 0 = layerSplitEnergy E z (β₀, s₀)) :
    ∀ᶠ t in 𝓝[≠] (0 : ℝ),
      layerReducedTransition (layerGerm E z M branchI (α₀, r₀) t)
        (layerGerm E z M branchI' (β₀, s₀) t) ≠ 0 := by
  have hflip : ((β₀, !r₀) : A × Bool) ≠ (α₀, r₀) := by
    intro hc
    exact (Bool.not_ne_self r₀) (congrArg Prod.snd hc)
  have hV : layerCrossPerturbation M (β₀, !r₀) (α₀, r₀) ≠ 0 := by
    rw [layerCrossPerturbation_apply_cross (x := ((β₀, !r₀) : A × Bool))
      (y := ((α₀, r₀) : A × Bool)) (by simp)]
    exact hM
  refine eventually_layerReducedTransition_ne_zero
    (Pi := layerGapProduct E z (α₀, r₀)) (Pi' := layerGapProduct E z (β₀, s₀))
    (layerGapProduct_ne_zero hinj (β₀, s₀))
    (layerGerm_zero E z M hbaseI) (layerGerm_zero E z M hbaseI')
    (fun y => hasDerivAt_layerGerm E z M (α₀, r₀) hbI y)
    (fun y => hasDerivAt_layerGerm E z M (β₀, s₀) hbI' y) ?_
  exact layerGerm_deriv_ne_zero hinj hflip hbI hbaseI hrootI hV

/-- The same-level version: at zero coupling the attached qubit already separates the two halves
of one old level. -/
theorem eventually_layerGerm_endpoint_ne_zero_sameLevel {E : A → ℂ} {z : ℂ}
    (hinj : Function.Injective (layerSplitEnergy E z)) {M : Matrix A A ℂ}
    {α₀ : A} {r₀ s₀ : Bool} {branchI branchI' : ℂ → ℂ}
    (hbI : AnalyticAt ℂ branchI 0) (hbaseI : branchI 0 = layerSplitEnergy E z (α₀, r₀))
    (hbI' : AnalyticAt ℂ branchI' 0) (hbaseI' : branchI' 0 = layerSplitEnergy E z (α₀, s₀)) :
    ∀ᶠ t in 𝓝 (0 : ℝ),
      layerReducedTransition (layerGerm E z M branchI (α₀, r₀) t)
        (layerGerm E z M branchI' (α₀, s₀) t) ≠ 0 :=
  eventually_layerReducedTransition_ne_zero_sameLevel
    (layerGapProduct_ne_zero hinj (α₀, r₀)) (layerGapProduct_ne_zero hinj (α₀, s₀))
    (layerGerm_zero E z M hbaseI) (layerGerm_zero E z M hbaseI')
    (fun y => (hasDerivAt_layerGerm E z M (α₀, r₀) hbI y).continuousAt)
    (fun y => (hasDerivAt_layerGerm E z M (α₀, s₀) hbI' y).continuousAt)

/-- **Endpoint completeness of the split system.**  If one edge coupling sees every ordered old
pair, then for all small nonzero coupling the attached qubit sees every ordered pair of split
labels. -/
theorem eventually_forall_layerGerm_endpoint_ne_zero {E : A → ℂ} {z : ℂ}
    (hinj : Function.Injective (layerSplitEnergy E z)) {M : Matrix A A ℂ}
    (hM : ∀ α β : A, α ≠ β → M β α ≠ 0) (branch : A × Bool → ℂ → ℂ)
    (hb : ∀ i, AnalyticAt ℂ (branch i) 0)
    (hbase : ∀ i, branch i 0 = layerSplitEnergy E z i)
    (hroot : ∀ i, ∀ᶠ g in 𝓝 (0 : ℂ), matrixCharpolyRelation
      (Matrix.diagonal (layerSplitEnergy E z) + g • layerCrossPerturbation M, branch i g) = 0) :
    ∀ᶠ t in 𝓝[≠] (0 : ℝ), ∀ p : (A × Bool) × (A × Bool), p.1 ≠ p.2 →
      layerReducedTransition (layerGerm E z M (branch p.1) p.1 t)
        (layerGerm E z M (branch p.2) p.2 t) ≠ 0 := by
  classical
  refine Filter.eventually_all.mpr fun p => ?_
  obtain ⟨⟨α, r⟩, ⟨β, s⟩⟩ := p
  by_cases hne : ((α, r) : A × Bool) = (β, s)
  · filter_upwards with t hcon
    exact absurd hne hcon
  by_cases hlevel : α = β
  · subst hlevel
    have hsame := eventually_layerGerm_endpoint_ne_zero_sameLevel (M := M) hinj
      (hb (α, r)) (hbase (α, r)) (hb (α, s)) (hbase (α, s))
    have hsame' : ∀ᶠ t in 𝓝[≠] (0 : ℝ),
        layerReducedTransition (layerGerm E z M (branch (α, r)) (α, r) t)
          (layerGerm E z M (branch (α, s)) (α, s) t) ≠ 0 :=
      hsame.filter_mono nhdsWithin_le_nhds
    filter_upwards [hsame'] with t ht _
    exact ht
  · have hcross := eventually_layerGerm_endpoint_ne_zero hinj (hM α β hlevel)
      (hb (α, r)) (hbase (α, r)) (hroot (α, r)) (hb (β, s)) (hbase (β, s))
    filter_upwards [hcross] with t ht _
    exact ht

end

end GaloisForLFunctions.HTGeometry
