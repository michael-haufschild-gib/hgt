import GaloisForLFunctions.HTGeometry.AllVertexGoodLeafExtension
import GaloisForLFunctions.HTGeometry.ParityCompleteLocalExtensionRelationEscape

/-!
# Anchor-star restriction of the physical local-extension chart

The all-vertex perturbative witness and the full physical genericity theorem
must use the same labeled eigenbranches.  This module restricts the common
multi-parameter local-extension chart to the real-symmetric anchor-star
coupling line and records exact analyticity, base, root, and chart-membership
properties.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Filter Topology
open scoped Matrix.Norms.Elementwise

/-- Anchor-star one-parameter restriction of a local-extension eigenbranch
chart. -/
def LocalExtensionEigenbranchChart.anchorStarBranch
    {I ρ : Type*} [Fintype I] [Fintype ρ]
    [DecidableEq I] [DecidableEq ρ]
    (energy : I → ℂ) (shift : ρ → ℂ)
    (attachment : Matrix I I ℂ)
    (C : LocalExtensionEigenbranchChart energy shift attachment)
    (anchor : ρ) (x : I × ρ) (t : ℂ) : ℂ :=
  C.branch x (shift, t • anchorStarLayerEdge anchor)

/-- The anchor-star parameter line is complex analytic. -/
theorem analyticAt_anchorStarLocalExtensionParameter
    {ρ : Type*} [Fintype ρ] [DecidableEq ρ]
    (shift : ρ → ℂ) (anchor : ρ) :
    AnalyticAt ℂ
      (fun t : ℂ =>
        (shift, t • anchorStarLayerEdge anchor)) 0 := by
  exact analyticAt_const.prod
    (analyticAt_id.smul analyticAt_const)

/-- Every restricted chart branch is analytic at zero. -/
theorem LocalExtensionEigenbranchChart.anchorStarBranch_analyticAt
    {I ρ : Type*} [Fintype I] [Fintype ρ]
    [DecidableEq I] [DecidableEq ρ]
    (energy : I → ℂ) (shift : ρ → ℂ)
    (attachment : Matrix I I ℂ)
    (C : LocalExtensionEigenbranchChart energy shift attachment)
    (anchor : ρ) (x : I × ρ) :
    AnalyticAt ℂ
      (C.anchorStarBranch energy shift attachment anchor x) 0 := by
  apply
    (C.analyticOn_branch x (shift, 0) C.center_mem).fun_comp_of_eq
  · exact analyticAt_anchorStarLocalExtensionParameter shift anchor
  · simp

/-- At zero coupling, restricted chart branches equal the coded product
energies. -/
theorem LocalExtensionEigenbranchChart.anchorStarBranch_zero
    {I ρ : Type*} [Fintype I] [Fintype ρ]
    [DecidableEq I] [DecidableEq ρ]
    (energy : I → ℂ) (shift : ρ → ℂ)
    (attachment : Matrix I I ℂ)
    (C : LocalExtensionEigenbranchChart energy shift attachment)
    (anchor : ρ) (x : I × ρ) :
    C.anchorStarBranch energy shift attachment anchor x 0 =
      layeredEnergy energy shift x := by
  simpa [LocalExtensionEigenbranchChart.anchorStarBranch] using C.base x

/-- The anchor-star parameter line remains in the common branch chart near
zero. -/
theorem LocalExtensionEigenbranchChart.eventually_anchorStar_mem
    {I ρ : Type*} [Fintype I] [Fintype ρ]
    [DecidableEq I] [DecidableEq ρ]
    (energy : I → ℂ) (shift : ρ → ℂ)
    (attachment : Matrix I I ℂ)
    (C : LocalExtensionEigenbranchChart energy shift attachment)
    (anchor : ρ) :
    ∀ᶠ t : ℂ in 𝓝 0,
      (shift, t • anchorStarLayerEdge anchor) ∈ C.U := by
  have hcenter :
      (shift, (0 : ℂ) • anchorStarLayerEdge anchor) ∈ C.U := by
    simpa using C.center_mem
  exact
    (analyticAt_anchorStarLocalExtensionParameter
      shift anchor).continuousAt
      (C.isOpen_U.mem_nhds hcenter)

/-- Restricted chart branches are characteristic roots of the exact affine
anchor-star Hamiltonian family. -/
theorem LocalExtensionEigenbranchChart.anchorStarBranch_root
    {I ρ : Type*} [Fintype I] [Fintype ρ]
    [DecidableEq I] [DecidableEq ρ]
    (energy : I → ℂ) (shift : ρ → ℂ)
    (attachment : Matrix I I ℂ)
    (C : LocalExtensionEigenbranchChart energy shift attachment)
    (anchor : ρ) (x : I × ρ) :
    ∀ᶠ t : ℂ in 𝓝 0,
      matrixCharpolyRelation
        (Matrix.diagonal (layeredEnergy energy shift) +
            t • layerMatrixCoupling attachment
              (anchorStarLayerEdge anchor),
          C.anchorStarBranch
            energy shift attachment anchor x t) = 0 := by
  filter_upwards
    [C.eventually_anchorStar_mem energy shift attachment anchor]
      with t ht
  have hroot :=
    C.root
      (shift, t • anchorStarLayerEdge anchor) ht x
  simpa [LocalExtensionEigenbranchChart.anchorStarBranch,
    localExtensionMatrix, layerMatrixCoupling_smul] using hroot

/-- Any analytic labeled root branch through the same simple product level
is the same germ as the anchor-star restriction of the common physical
chart. -/
theorem
    affineEigenbranch_eventuallyEq_anchorStarBranch
    {I ρ : Type*} [Fintype I] [Fintype ρ]
    [DecidableEq I] [DecidableEq ρ]
    (energy : I → ℂ) (shift : ρ → ℂ)
    (attachment : Matrix I I ℂ)
    (C : LocalExtensionEigenbranchChart energy shift attachment)
    (anchor : ρ)
    (hinj : Function.Injective (layeredEnergy energy shift))
    (x : I × ρ) (branch : ℂ → ℂ)
    (hbranchAnalytic : AnalyticAt ℂ branch 0)
    (hbranchBase :
      branch 0 = layeredEnergy energy shift x)
    (hbranchRoot :
      ∀ᶠ t : ℂ in 𝓝 0,
        matrixCharpolyRelation
          (Matrix.diagonal (layeredEnergy energy shift) +
              t • layerMatrixCoupling attachment
                (anchorStarLayerEdge anchor),
            branch t) = 0) :
    branch =ᶠ[𝓝 0]
      C.anchorStarBranch
        energy shift attachment anchor x := by
  let H : ℂ → Matrix (I × ρ) (I × ρ) ℂ :=
    fun t =>
      Matrix.diagonal (layeredEnergy energy shift) +
        t • layerMatrixCoupling attachment
          (anchorStarLayerEdge anchor)
  have hHan : AnalyticAt ℂ H 0 := by
    have hparameter :=
      analyticAt_anchorStarLocalExtensionParameter shift anchor
    have hlocal :=
      (localExtensionMatrix_analyticAt
        energy attachment (shift, 0)).fun_comp_of_eq
        hparameter (by simp)
    simpa [H, localExtensionMatrix,
      layerMatrixCoupling_smul] using hlocal
  have hHt :
      Tendsto H (𝓝 0)
        (𝓝 (Matrix.diagonal (layeredEnergy energy shift))) := by
    have hcont := hHan.continuousAt
    change Tendsto H (𝓝 0) (𝓝 (H 0)) at hcont
    have hH0 :
        H 0 = Matrix.diagonal (layeredEnergy energy shift) := by
      simp [H]
    rw [hH0] at hcont
    exact hcont
  have hbranchT :
      Tendsto branch (𝓝 0)
        (𝓝 (layeredEnergy energy shift x)) := by
    have hcont := hbranchAnalytic.continuousAt
    change Tendsto branch (𝓝 0) (𝓝 (branch 0)) at hcont
    simpa [hbranchBase] using hcont
  have hchartT :
      Tendsto
        (C.anchorStarBranch
          energy shift attachment anchor x)
        (𝓝 0)
        (𝓝 (layeredEnergy energy shift x)) := by
    have hcont :=
      (C.anchorStarBranch_analyticAt
        energy shift attachment anchor x).continuousAt
    change Tendsto
      (C.anchorStarBranch
        energy shift attachment anchor x)
      (𝓝 0)
      (𝓝 (C.anchorStarBranch
        energy shift attachment anchor x 0)) at hcont
    simpa [C.anchorStarBranch_zero
      energy shift attachment anchor x] using hcont
  apply simpleDiagonalMatrix_root_germs_unique
    (layeredEnergy energy shift) hinj x hHt
    hbranchT hchartT
  · simpa [H] using hbranchRoot
  · simpa [H] using
      C.anchorStarBranch_root
        energy shift attachment anchor x

/-- All finitely many labeled branches agree with the common physical chart
on one neighborhood. -/
theorem
    eventually_all_affineEigenbranches_eq_anchorStarBranch
    {I ρ : Type*} [Fintype I] [Fintype ρ]
    [DecidableEq I] [DecidableEq ρ]
    (energy : I → ℂ) (shift : ρ → ℂ)
    (attachment : Matrix I I ℂ)
    (C : LocalExtensionEigenbranchChart energy shift attachment)
    (anchor : ρ)
    (hinj : Function.Injective (layeredEnergy energy shift))
    (branch : I × ρ → ℂ → ℂ)
    (hbranchAnalytic : ∀ x, AnalyticAt ℂ (branch x) 0)
    (hbranchBase :
      ∀ x, branch x 0 = layeredEnergy energy shift x)
    (hbranchRoot :
      ∀ x,
        ∀ᶠ t : ℂ in 𝓝 0,
          matrixCharpolyRelation
            (Matrix.diagonal (layeredEnergy energy shift) +
                t • layerMatrixCoupling attachment
                  (anchorStarLayerEdge anchor),
              branch x t) = 0) :
    ∀ᶠ t : ℂ in 𝓝 0, ∀ x,
      branch x t =
        C.anchorStarBranch
          energy shift attachment anchor x t := by
  exact Filter.eventually_all.mpr fun x =>
    affineEigenbranch_eventuallyEq_anchorStarBranch
      energy shift attachment C anchor hinj x (branch x)
      (hbranchAnalytic x) (hbranchBase x) (hbranchRoot x)

end

end GaloisForLFunctions.HTGeometry
