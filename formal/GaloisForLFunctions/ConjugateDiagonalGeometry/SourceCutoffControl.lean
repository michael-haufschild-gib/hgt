import GaloisForLFunctions.ConjugateDiagonalGeometry.XiPositiveSourceMetric
import Mathlib.Topology.ContinuousMap.BoundedCompactlySupported

/-!
# Explicit control of the source exhaustion

The first directional derivatives and the Laplacian of the fixed cutoff are
bounded continuous functions. Their norms give one source-independent control
constant. Differentiation also preserves the cutoff disc exactly.
-/

open Complex MeasureTheory Set Metric Laplacian InnerProductSpace
open scoped Laplacian
noncomputable section
namespace GaloisForLFunctions.ConjugateDiagonalGeometry

/-- The directional derivative of the fixed cutoff, with its actual supremum norm. -/
def sourceCutoffDerivative (n : ℕ) (v : ℂ) : BoundedContinuousFunction ℂ ℝ := by
  have hc : ContDiff ℝ 2 (sourceCutoff n : ℂ → ℝ) := (sourceCutoff n).contDiff
  exact ofCompactSupport (fun z => fderiv ℝ (sourceCutoff n) z v)
    ((hc.continuous_fderiv (by norm_num)).clm_apply continuous_const)
    ((sourceCutoff n).hasCompactSupport.fderiv_apply ℝ v)

/-- The cutoff Laplacian, with its actual supremum norm. -/
def sourceCutoffLaplacian (n : ℕ) : BoundedContinuousFunction ℂ ℝ := by
  have hc : ContDiff ℝ 2 (sourceCutoff n : ℂ → ℝ) := (sourceCutoff n).contDiff
  exact ofCompactSupport (Δ (sourceCutoff n : ℂ → ℝ))
    (continuous_test_laplacian hc)
    (compact_test_laplacian hc (sourceCutoff n).hasCompactSupport)

/-- One positive constant controls every term in the cutoff product Laplacian. -/
def sourceCutoffControl (n : ℕ) : ℝ :=
  1 + ‖sourceCutoffDerivative n 1‖ + ‖sourceCutoffDerivative n Complex.I‖ +
    ‖sourceCutoffLaplacian n‖

theorem sourceCutoffControl_pos (n : ℕ) : 0 < sourceCutoffControl n := by
  unfold sourceCutoffControl
  positivity

theorem abs_sourceCutoffDerivative_le (n : ℕ) (v z : ℂ) :
    |fderiv ℝ (sourceCutoff n) z v| ≤ ‖sourceCutoffDerivative n v‖ := by
  have h := (sourceCutoffDerivative n v).norm_coe_le_norm z
  change ‖fderiv ℝ (sourceCutoff n) z v‖ ≤ _ at h
  simpa only [Real.norm_eq_abs] using h

theorem abs_sourceCutoffLaplacian_le (n : ℕ) (z : ℂ) :
    |Δ (sourceCutoff n : ℂ → ℝ) z| ≤ ‖sourceCutoffLaplacian n‖ := by
  have h := (sourceCutoffLaplacian n).norm_coe_le_norm z
  change ‖Δ (sourceCutoff n : ℂ → ℝ) z‖ ≤ _ at h
  simpa only [Real.norm_eq_abs] using h

/-- The planar Laplacian cannot enlarge the support of a C² test. -/
theorem tsupport_test_laplacian_subset {φ : ℂ → ℝ} (hp : ContDiff ℝ 2 φ) :
    tsupport (Δ φ) ⊆ tsupport φ := by
  have he : Δ φ = fun z => Bottcher.dderiv φ 1 z + Bottcher.dderiv φ Complex.I z :=
    funext (Bottcher.laplacian_eq_dderiv φ hp)
  have hd (v : ℂ) : tsupport (Bottcher.dderiv φ v) ⊆ tsupport φ :=
    (tsupport_fderiv_apply_subset ℝ v).trans (tsupport_fderiv_apply_subset ℝ v)
  rw [he]
  exact (tsupport_add _ _).trans (union_subset (hd 1) (hd Complex.I))

/-- Every cutoff source test has its full Laplacian supported in the specified source disc. -/
theorem sourceCutoff_laplacian_eq_zero_outside (n : ℕ) (φ : ℂ → ℝ)
    (hp : ContDiff ℝ 2 φ) (z : ℂ)
    (hz : z ∉ closedBall (0 : ℂ) |(n : ℝ) + 2|) :
    Δ (fun w => sourceCutoff n w * φ w) z = 0 := by
  have hs : tsupport (Δ (fun w => sourceCutoff n w * φ w)) ⊆
      closedBall (0 : ℂ) |(n : ℝ) + 2| := by
    have h := (tsupport_test_laplacian_subset ((sourceCutoff n).contDiff.mul hp)).trans
      tsupport_mul_subset_left
    rw [(sourceCutoff n).tsupport_eq] at h
    change tsupport (Δ (fun w => sourceCutoff n w * φ w)) ⊆
      closedBall (0 : ℂ) ((n : ℝ) + 2) at h
    simpa only [abs_of_pos (by positivity : 0 < (n : ℝ) + 2)] using h
  by_contra hne
  exact hz (hs (subset_tsupport _ hne))

end GaloisForLFunctions.ConjugateDiagonalGeometry
