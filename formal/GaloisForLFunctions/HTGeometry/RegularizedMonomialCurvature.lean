import GaloisForLFunctions.HTGeometry.RegularizedMonomialWinding
import DifferentialGeometry.Geometry.Curvature.ConformalGaussBonnet

/-!
# Curvature and boundary charge of regularized monomials

For nonzero ε, the conformal metric is `(‖z‖^(2m) + ε²) |dz|²`.
Its curvature integral over a radius-R disk equals `-2π * charge m ε R`;
the unit-circle geodesic-curvature integral equals `2π * (1 + charge m ε 1)`.
Along any nonzero regularization family tending to zero, these converge to
`-2πm` and `2π(1+m)`. The boundary contribution retains the compensating charge.
These formulas use the actual Riemannian curvature and area/arclength densities.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff
namespace HTGeometry.RegularizedMonomialCharge
open DifferentialGeometry.Analysis DifferentialGeometry.Geometry

theorem disk_curvature_integral (m : ℕ) {ε R : ℝ} (hε : ε ≠ 0) (hR : 0 < R) :
    (∫ z in Metric.closedBall (0 : ℂ) R,
      planeGaussianCurvature (conformalEuclideanMetric (logFactor m ε)
          (contDiff_logFactor m hε)) z *
        tangentTwoJacobian (conformalEuclideanMetric (logFactor m ε)
          (contDiff_logFactor m hε)) (x := z) (1 : ℂ) Complex.I) =
      -(2 * Real.pi * charge m ε R) := by
  simp only [planeGaussianCurvature_mul_areaDensity (contDiff_logFactor m hε)]
  rw [integral_neg]
  exact congrArg Neg.neg (laplacianMass_eq m hε hR)

theorem unitDisk_curvature_integral (m : ℕ) {ε : ℝ} (hε : ε ≠ 0) :
    (∫ z in Metric.closedBall (0 : ℂ) 1,
      planeGaussianCurvature (conformalEuclideanMetric (logFactor m ε)
          (contDiff_logFactor m hε)) z *
        tangentTwoJacobian (conformalEuclideanMetric (logFactor m ε)
          (contDiff_logFactor m hε)) (x := z) (1 : ℂ) Complex.I) =
      -(2 * Real.pi * charge m ε 1) :=
  disk_curvature_integral m hε (by norm_num)

theorem unitCircle_boundary_integral (m : ℕ) {ε : ℝ} (hε : ε ≠ 0) :
    (∫ θ in -Real.pi..Real.pi,
      let z := Complex.polarCoord.symm (1, θ)
      conformalCircleGeodesicCurvature (logFactor m ε) (contDiff_logFactor m hε) z *
        Real.sqrt ((conformalEuclideanMetric (logFactor m ε) (contDiff_logFactor m hε)).inner
          z (Complex.I * z) (Complex.I * z))) =
      2 * Real.pi * (1 + charge m ε 1) := by
  have hz (θ : ℝ) : ‖Complex.polarCoord.symm (1, θ)‖ = 1 := by simp
  simp only [conformalCircleGeodesicCurvature_mul_arclength (contDiff_logFactor m hε) (hz _),
    fderiv_logFactor_unit m hε (hz _)]
  rw [intervalIntegral.integral_const]
  simp only [charge, one_pow, mul_one, smul_eq_mul]
  ring

/-- Curvature retains the negative divisor charge along any nonzero regularization
family tending to zero. -/
theorem tendsto_disk_curvature_integral {α : Type*} {l : Filter α}
    (m : ℕ) {ε : α → ℝ} (hε : ∀ a, ε a ≠ 0)
    (ht : Tendsto ε l (𝓝 0)) {R : ℝ} (hR : 0 < R) :
    Tendsto (fun a => ∫ z in Metric.closedBall (0 : ℂ) R,
      planeGaussianCurvature (conformalEuclideanMetric (logFactor m (ε a))
          (contDiff_logFactor m (hε a))) z *
        tangentTwoJacobian (conformalEuclideanMetric (logFactor m (ε a))
          (contDiff_logFactor m (hε a))) (x := z) (1 : ℂ) Complex.I)
      l (𝓝 (-(2 * Real.pi * (m : ℝ)))) := by
  simp only [disk_curvature_integral m (hε _) hR]
  exact (tendsto_const_nhds.mul ((tendsto_charge m hR).comp ht)).neg

/-- The boundary term retains the compensating charge in the singular limit. -/
theorem tendsto_unitCircle_boundary_integral {α : Type*} {l : Filter α}
    (m : ℕ) {ε : α → ℝ} (hε : ∀ a, ε a ≠ 0)
    (ht : Tendsto ε l (𝓝 0)) :
    Tendsto (fun a => ∫ θ in -Real.pi..Real.pi,
      let z := Complex.polarCoord.symm (1, θ)
      conformalCircleGeodesicCurvature (logFactor m (ε a))
          (contDiff_logFactor m (hε a)) z *
        Real.sqrt ((conformalEuclideanMetric (logFactor m (ε a))
          (contDiff_logFactor m (hε a))).inner z (Complex.I * z) (Complex.I * z)))
      l (𝓝 (2 * Real.pi * (1 + (m : ℝ)))) := by
  simp only [unitCircle_boundary_integral m (hε _)]
  exact tendsto_const_nhds.mul
    (tendsto_const_nhds.add ((tendsto_charge m (by norm_num)).comp ht))

end HTGeometry.RegularizedMonomialCharge
