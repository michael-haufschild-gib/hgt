import GaloisForLFunctions.HTGeometry.CoordinateMetricVolumeTrace
import GaloisForLFunctions.HTGeometry.CoordinateEinsteinActionCurrent

set_option autoImplicit false
namespace GaloisForLFunctions.HTGeometry.EinsteinActionBoundary
open CoordinateMetricTwoJet CoordinateMetricTwoJet.Linearization MetricPathDensity
noncomputable section
variable {d : ℕ}
local notation "Mat" => Matrix (Fin d) (Fin d) ℂ
local notation "Jet" => CoordinateMetricTwoJet d ℂ

private theorem raised_contraction_metric (G H : Mat) (hG : G.det ≠ 0)
    (hs : G.transpose = G) :
    (∑ i, ∑ j, (G⁻¹ * H * (G⁻¹).transpose) i j * G i j) = (G⁻¹ * H).trace := by
  have ht : (G⁻¹).transpose = G⁻¹ := by rw [Matrix.transpose_nonsing_inv, hs]
  have he : (∑ i, ∑ j, (G⁻¹ * H * (G⁻¹).transpose) i j * G i j) =
      ((G⁻¹ * H * (G⁻¹).transpose) * G.transpose).trace := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply]
  rw [he, ht, hs, Matrix.mul_assoc (G⁻¹ * H),
    Matrix.nonsing_inv_mul G (isUnit_iff_ne_zero.mpr hG), Matrix.mul_one]

/-- Relative Einstein--Hilbert density with the same volume branch as the weighted source. -/
def densityPath (J H : Jet) (Λ : ℂ) (t : ℂ) : ℂ :=
  volumeRatio J.metric H.metric 0 0 t * ((affine J H t).scalar - 2 * Λ)

/-- First variation of the actual density, retaining the complete scalar-curvature derivative. -/
theorem densityPath_hasDerivAt (J H : Jet) (Λ : ℂ) (hJ : J.metric.det ≠ 0) :
    HasDerivAt (densityPath J H Λ)
      ((J.metric⁻¹ * H.metric).trace / 2 * (J.scalar - 2 * Λ) + Linearization.scalar J H) 0 := by
  have hd := (volumeRatio_hasDerivAt_trace J.metric H.metric 0 0 hJ).mul
    ((scalar_hasDerivAt J H hJ).sub_const (2 * Λ))
  convert! hd using 1
  simp only [affine_zero, volumeRatio_zero _ _ _ _ hJ, one_mul]

/-- Actual Einstein--Hilbert first variation splits into its full Einstein residual and the
connection-variation divergence. The cosmological volume term fixes the bulk sign. -/
theorem densityPath_first_variation (J H : Jet) (Λ : ℂ) (hJ : J.metric.det ≠ 0)
    (hs : J.metric.transpose = J.metric)
    (hf : ∀ k i j, J.first k i j = J.first k j i) :
    deriv (densityPath J H Λ) 0 =
      -(∑ i, ∑ j, (J.metric⁻¹ * H.metric * (J.metric⁻¹).transpose) i j *
        (J.einstein i j + Λ * J.metric i j)) + divergence J H := by
  rw [(densityPath_hasDerivAt J H Λ hJ).deriv]
  have ht : (J.metric⁻¹).transpose = J.metric⁻¹ := by rw [Matrix.transpose_nonsing_inv, hs]
  have hc := raised_contraction_metric J.metric H.metric hJ hs
  have hd := contracted_ricci_eq_divergence J H hJ hs hf
  unfold Linearization.scalar
  simp only [Finset.sum_add_distrib]
  rw [hd]
  simp only [CoordinateMetricTwoJet.einstein, mul_add, mul_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  have hn : (∑ i, ∑ j, inverse J H i j * J.ricci i j) =
      -(∑ i, ∑ j, (J.metric⁻¹ * H.metric * (J.metric⁻¹).transpose) i j * J.ricci i j) := by
    simp only [inverse, ht, Matrix.neg_apply, neg_mul, Finset.sum_neg_distrib]
  rw [hn]
  have hp (c : ℂ) : (∑ i, ∑ j,
      (J.metric⁻¹ * H.metric * (J.metric⁻¹).transpose) i j * (c * J.metric i j)) =
      c * (J.metric⁻¹ * H.metric).trace := by
    rw [← hc, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hp ((1 / 2 : ℂ) * J.scalar), hp Λ]
  ring

end
end GaloisForLFunctions.HTGeometry.EinsteinActionBoundary
