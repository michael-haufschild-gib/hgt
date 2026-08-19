/-
# The chart eigenvectors on the anchor-star line are the split-family germs

The canonical adjugate-column eigenvectors of the full local-extension chart, restricted to the
anchor-star coupling line, are exactly the canonical eigenvector germs of the split family: both
are adjugate columns of the same characteristic matrix.  So endpoint completeness proved for the
germs -- the induction step of Lemma A1 -- is endpoint completeness of the chart eigenvectors,
which is where the openness and genericity arguments live.

Main results:
* `anchorStarLayerEdge_bool` — for one attached qubit the anchor star is the exchange matrix.
* `characteristicMatrix_anchorStar`, `adjugateColumn_anchorStar` — the identification.
* `eventually_forall_chartAdjugate_endpoint_ne_zero` — **endpoint completeness of the chart
  eigenvectors at all small nonzero coupling**.
-/
import GaloisForLFunctions.HTGeometry.AnchorStarLocalExtensionChart
import GaloisForLFunctions.HTGeometry.LocalExtensionChartProbeContinuity
import GaloisForLFunctions.HTGeometry.LayerGermEndpointCompleteness
import GaloisForLFunctions.HTGeometry.LayerSplitPhysicalRealization
import GaloisForLFunctions.HTGeometry.ChartQuadraticRateEscape

open Filter Topology
open scoped Matrix.Norms.Elementwise

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- For a single attached qubit the anchor star is the exchange matrix. -/
theorem anchorStarLayerEdge_bool :
    anchorStarLayerEdge (false : Bool) = layerExchange := by
  ext u v
  rw [anchorStarLayerEdge, layerExchange_apply]
  cases u <;> cases v <;> simp

variable {I ρ : Type*} [Fintype I] [Fintype ρ] [DecidableEq I] [DecidableEq ρ]

/-- On the anchor-star line the chart characteristic matrix is the affine one. -/
theorem characteristicMatrix_anchorStar (energy : I → ℂ) (shift : ρ → ℂ)
    (attachment : Matrix I I ℂ)
    (C : LocalExtensionEigenbranchChart energy shift attachment)
    (anchor : ρ) (x : I × ρ) (t : ℂ) :
    C.characteristicMatrix energy shift attachment x
        (shift, t • anchorStarLayerEdge anchor)
      = affineBranchCharacteristicMatrix (layeredEnergy energy shift)
          (layerMatrixCoupling attachment (anchorStarLayerEdge anchor))
          (C.anchorStarBranch energy shift attachment anchor x) t := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [LocalExtensionEigenbranchChart.characteristicMatrix,
      LocalExtensionEigenbranchChart.anchorStarBranch, affineBranchCharacteristicMatrix,
      localExtensionMatrix, Matrix.scalar_apply]
    ring
  · simp only [LocalExtensionEigenbranchChart.characteristicMatrix,
      LocalExtensionEigenbranchChart.anchorStarBranch, affineBranchCharacteristicMatrix,
      localExtensionMatrix, layerMatrixCoupling, Matrix.scalar_apply, Matrix.sub_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.diagonal_apply_ne _ hij]
    ring

/-- **The chart eigenvector on the anchor-star line is the split-family germ.** -/
theorem adjugateColumn_anchorStar (energy : I → ℂ) (shift : ρ → ℂ)
    (attachment : Matrix I I ℂ)
    (C : LocalExtensionEigenbranchChart energy shift attachment)
    (anchor : ρ) (x : I × ρ) (t : ℂ) :
    C.adjugateColumn energy shift attachment x (shift, t • anchorStarLayerEdge anchor)
      = affineEigenbranchAdjugateColumn (layeredEnergy energy shift)
          (layerMatrixCoupling attachment (anchorStarLayerEdge anchor))
          (C.anchorStarBranch energy shift attachment anchor x) x t := by
  funext i
  rw [LocalExtensionEigenbranchChart.adjugateColumn, affineEigenbranchAdjugateColumn,
    characteristicMatrix_anchorStar]

/-! ## Endpoint completeness of the chart eigenvectors -/

/-- **Endpoint completeness of the chart eigenvectors at all small nonzero coupling.**  The germ
statement of the induction step of Lemma A1, transported to the canonical eigenvectors of the full
chart. -/
theorem eventually_forall_chartAdjugate_endpoint_ne_zero
    {A : Type*} [Fintype A] [DecidableEq A] {E : A → ℂ} {z : ℂ}
    (hinj : Function.Injective (layerSplitEnergy E z))
    {M : Matrix A A ℂ} (hM : ∀ α β : A, α ≠ β → M β α ≠ 0)
    (C : LocalExtensionEigenbranchChart E (boolShift z) M) :
    ∀ᶠ t : ℝ in 𝓝[≠] (0 : ℝ), ∀ q : (A × Bool) × (A × Bool), q.1 ≠ q.2 →
      layerReducedTransition
        (C.adjugateColumn E (boolShift z) M q.1
          (boolShift z, ((t : ℝ) : ℂ) • anchorStarLayerEdge (false : Bool)))
        (C.adjugateColumn E (boolShift z) M q.2
          (boolShift z, ((t : ℝ) : ℂ) • anchorStarLayerEdge (false : Bool))) ≠ 0 := by
  have hsplit : layeredEnergy E (boolShift z) = layerSplitEnergy E z := layeredEnergy_boolShift E z
  have hcoup : layerMatrixCoupling M (anchorStarLayerEdge (false : Bool))
      = layerCrossPerturbation M := by
    rw [anchorStarLayerEdge_bool, ← layerCrossPerturbation_eq_coupling]
  set br : A × Bool → ℂ → ℂ := fun i => C.anchorStarBranch E (boolShift z) M false i with hbr
  have hb : ∀ i, AnalyticAt ℂ (br i) 0 := fun i =>
    C.anchorStarBranch_analyticAt E (boolShift z) M false i
  have hbase : ∀ i, br i 0 = layerSplitEnergy E z i := by
    intro i
    show C.anchorStarBranch E (boolShift z) M false i 0 = layerSplitEnergy E z i
    rw [C.anchorStarBranch_zero E (boolShift z) M false i, hsplit]
  have hroot : ∀ i, ∀ᶠ g : ℂ in 𝓝 0, matrixCharpolyRelation
      (Matrix.diagonal (layerSplitEnergy E z) + g • layerCrossPerturbation M, br i g) = 0 := by
    intro i
    have := C.anchorStarBranch_root E (boolShift z) M false i
    rw [hsplit, hcoup] at this
    exact this
  have hgerm := eventually_forall_layerGerm_endpoint_ne_zero hinj hM br hb hbase hroot
  filter_upwards [hgerm] with t ht q hq
  have hEq : ∀ x : A × Bool,
      C.adjugateColumn E (boolShift z) M x
          (boolShift z, ((t : ℝ) : ℂ) • anchorStarLayerEdge (false : Bool))
        = layerGerm E z M (br x) x t := by
    intro x
    rw [adjugateColumn_anchorStar, hsplit, hcoup]
    rfl
  rw [hEq q.1, hEq q.2]
  exact ht q hq

end

end GaloisForLFunctions.HTGeometry
