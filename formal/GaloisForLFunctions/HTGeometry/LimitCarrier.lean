import GaloisForLFunctions.HTGeometry.CarriedConclusion
import GaloisForLFunctions.HTGeometry.GaussMomentLimit

/-!
# The weak limit inherits a carrying set

The portmanteau open-set inequality bounds the limit's mass on an open set by the liminf of the
approximants'.  If every approximant gives that open set no mass, neither does the limit.

Applied to the complement of a closed interval, this says a weak limit of measures carried by the
interval is carried by it too — the ingredient needed to turn bounded Gauss nodes into a compactly
supported representing measure.
-/

open scoped BigOperators
open MeasureTheory Filter

namespace HTGeometry

/-- **A weak limit gives no mass to an open set the approximants avoid.** -/
theorem measure_eq_zero_of_isOpen_le_liminf {mu : Measure ℝ} {mus : ℕ → Measure ℝ}
    (h_opens : ∀ G, IsOpen G → mu G ≤ atTop.liminf fun i => mus i G)
    {U : Set ℝ} (hU : IsOpen U) (hzero : ∀ i, mus i U = 0) : mu U = 0 := by
  refine nonpos_iff_eq_zero.mp ?_
  refine le_trans (h_opens U hU) ?_
  have hcongr : (fun i => mus i U) = fun _ : ℕ => (0 : ENNReal) := by
    funext i
    exact hzero i
  rw [hcongr, liminf_const]

/-- The Gauss measures give no mass to any open set avoiding their nodes. -/
theorem gaussMeasure_eq_zero_of_disjoint_nodes {s : ℕ → ℝ} (n : ℕ) {U : Set ℝ}
    (hU : MeasurableSet U) (hdisj : ∀ xi ∈ gaussNodes s n, xi ∉ U) :
    gaussMeasure s n U = 0 := by
  classical
  rw [gaussMeasure, finsetWeightedDirac_apply _ _ hU]
  refine Finset.sum_eq_zero fun xi hxi => ?_
  rw [Set.indicator_of_notMem (hdisj xi hxi), mul_zero]

/-- The normalised Gauss measure likewise gives no mass to a set avoiding its nodes. -/
theorem gaussProb_eq_zero_of_disjoint_nodes {s : ℕ → ℝ} (n : ℕ) {U : Set ℝ}
    (hU : MeasurableSet U) (hdisj : ∀ xi ∈ gaussNodes s n, xi ∉ U) :
    gaussProb s n U = 0 := by
  rw [gaussProb, Measure.smul_apply, gaussMeasure_eq_zero_of_disjoint_nodes n hU hdisj,
    smul_eq_mul, mul_zero]

/-- If all nodes of every level lie in a fixed interval, every Gauss measure vanishes off it. -/
theorem gaussProb_compl_eq_zero_of_nodes_mem {s : ℕ → ℝ} {B : ℝ}
    (hbdd : ∀ n : ℕ, ∀ xi ∈ gaussNodes s n, xi ∈ Set.Icc (-B) B) (n : ℕ) :
    gaussProb s n (Set.Icc (-B) B)ᶜ = 0 := by
  refine gaussProb_eq_zero_of_disjoint_nodes n measurableSet_Icc.compl fun xi hxi => ?_
  simp only [Set.mem_compl_iff, not_not]
  exact hbdd n xi hxi

end HTGeometry
