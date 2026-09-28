import GaloisForLFunctions.HTGeometry.RegularizedMonomialCharge
import GaloisForLFunctions.Bottcher.AnnulusRoot
import DifferentialGeometry.Analysis.Elliptic.ComplexPlane.Disk.GreenIdentity

/-!
# Regularized divisor mass and monomial winding

The proved planar Green identity evaluates the disk Laplacian mass of the smooth
regularized logarithm. At every positive radius that mass converges to `2πm` as
the regularizer vanishes through nonzero values. The limit agrees with the
imaginary part of the existing logarithmic-derivative winding integral of `z^m`.
The actual Laplacian integral over every annulus with positive inner radius tends to zero.
The singular logarithm has zero classical Laplacian almost everywhere, but its
distributional Laplacian retains the point charge, as tested against compactly
supported twice continuously differentiable functions.
-/

noncomputable section
open MeasureTheory Filter Set InnerProductSpace
open scoped Topology ContDiff
namespace HTGeometry.RegularizedMonomialCharge
open DifferentialGeometry.Analysis

theorem radial_boundary_flux (m : ℕ) {ε R : ℝ} (hε : ε ≠ 0) (hR : 0 < R) (θ : ℝ) :
    R * fderiv ℝ (logFactor m ε) (Complex.polarCoord.symm (R, θ))
      (Complex.polarCoord.symm (1, θ)) = charge m ε R := by
  have hp : R • Complex.polarCoord.symm (1, θ) = Complex.polarCoord.symm (R, θ) := by
    exact (polar_point_eq_smul_unit R θ).symm
  have hn : ‖Complex.polarCoord.symm (R, θ)‖ = R := by simp [hR.le]
  rw [← smul_eq_mul, ← map_smul, hp, fderiv_logFactor_radial m hε, hn]
  rfl

def laplacianMass (m : ℕ) (ε R : ℝ) : ℝ :=
  ∫ z in Metric.closedBall (0 : ℂ) R, Laplacian.laplacian (logFactor m ε) z

theorem laplacianMass_eq (m : ℕ) {ε R : ℝ} (hε : ε ≠ 0) (hR : 0 < R) :
    laplacianMass m ε R = 2 * Real.pi * charge m ε R := by
  unfold laplacianMass
  rw [integral_laplacian_closedBall ((contDiff_logFactor m hε).of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) hR]
  simp_rw [radial_boundary_flux m hε hR]
  rw [intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

theorem tendsto_laplacianMass (m : ℕ) {R : ℝ} (hR : 0 < R) :
    Tendsto (fun ε : ℝ => laplacianMass m ε R) (𝓝[≠] 0) (𝓝 (2 * Real.pi * (m : ℝ))) := by
  apply ((tendsto_const_nhds.mul (tendsto_charge m hR)).mono_left inf_le_left).congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (laplacianMass_eq m hε hR).symm

theorem tendsto_laplacianMass_winding (m : ℕ) {R : ℝ} (hR : 0 < R) :
    Tendsto (fun ε : ℝ => laplacianMass m ε R) (𝓝[≠] 0)
      (𝓝 ((∫ θ in (0 : ℝ)..(2 * Real.pi),
        logDeriv (fun z : ℂ => z ^ (m : ℤ)) (circleMap 0 R θ) *
          (circleMap 0 R θ * Complex.I)).im)) := by
  rw [Bottcher.winding_zpow_circle hR]
  convert tendsto_laplacianMass m hR using 1 <;> simp <;> ring

theorem annular_laplacianMass_eq (m : ℕ) {ε r R : ℝ} (hε : ε ≠ 0)
    (hr : 0 < r) (hrR : r ≤ R) :
    (∫ z in Metric.closedBall (0 : ℂ) R \ Metric.closedBall 0 r,
      Laplacian.laplacian (logFactor m ε) z) =
        2 * Real.pi * (charge m ε R - charge m ε r) := by
  have hc := continuous_laplacian_complex ((contDiff_logFactor m hε).of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
  rw [setIntegral_sdiff (Metric.isClosed_closedBall.measurableSet)
    (hc.continuousOn.integrableOn_compact (isCompact_closedBall (0 : ℂ) R))
    (Metric.closedBall_subset_closedBall hrR)]
  change laplacianMass m ε R - laplacianMass m ε r = _
  rw [laplacianMass_eq m hε (lt_of_lt_of_le hr hrR), laplacianMass_eq m hε hr]
  ring

theorem tendsto_annular_laplacianMass (m : ℕ) {r R : ℝ}
    (hr : 0 < r) (hrR : r ≤ R) :
    Tendsto (fun ε : ℝ => ∫ z in Metric.closedBall (0 : ℂ) R \ Metric.closedBall 0 r,
      Laplacian.laplacian (logFactor m ε) z) (𝓝[≠] 0) (𝓝 0) := by
  have ht := ((tendsto_const_nhds (x := 2 * Real.pi)).mul
    ((tendsto_charge m (lt_of_lt_of_le hr hrR)).sub (tendsto_charge m hr))).mono_left
      (show 𝓝[≠] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)
  simp only [sub_self, mul_zero] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (annular_laplacianMass_eq m hε hr hrR).symm

theorem logFactor_zero (m : ℕ) (z : ℂ) : logFactor m 0 z = (m : ℝ) * Real.log ‖z‖ := by
  simp [logFactor, Real.log_pow]; ring

theorem laplacian_logFactor_zero_ae (m : ℕ) :
    Laplacian.laplacian (logFactor m 0) =ᵐ[volume] (fun _ : ℂ => 0) := by
  filter_upwards [volume.ae_ne (0 : ℂ)] with z hz
  have hh : HarmonicAt (fun z : ℂ => (m : ℝ) • Real.log ‖z‖) z :=
    (harmonicAt_log_norm_complex hz).const_smul
  have he : logFactor m 0 = fun z : ℂ => (m : ℝ) • Real.log ‖z‖ := by
    funext z
    simpa only [smul_eq_mul] using logFactor_zero m z
  rw [he]
  exact hh.2.self_of_nhds

theorem laplacianMass_zero_parameter (m : ℕ) (R : ℝ) : laplacianMass m 0 R = 0 := by
  unfold laplacianMass
  calc
    _ = ∫ z in Metric.closedBall (0 : ℂ) R, (0 : ℝ) :=
      integral_congr_ae (ae_restrict_of_ae (laplacian_logFactor_zero_ae m))
    _ = 0 := by simp

theorem tendsto_classical_laplacian_defect (m : ℕ) {R : ℝ} (hR : 0 < R) :
    Tendsto (fun ε : ℝ => laplacianMass m ε R - laplacianMass m 0 R)
      (𝓝[≠] 0) (𝓝 (2 * Real.pi * (m : ℝ))) := by
  simpa only [laplacianMass_zero_parameter, sub_zero] using tendsto_laplacianMass m hR

theorem integral_logFactor_zero_mul_laplacian (m : ℕ) {φ : ℂ → ℝ}
    (hc : HasCompactSupport φ) (hf : ContDiff ℝ 2 φ) :
    (∫ z : ℂ, logFactor m 0 z * Laplacian.laplacian φ z) =
      (2 * Real.pi * (m : ℝ)) * φ 0 := by
  simp_rw [logFactor_zero, mul_assoc]
  rw [integral_const_mul, integral_log_norm_mul_laplacian hc hf]
  ring

end HTGeometry.RegularizedMonomialCharge
