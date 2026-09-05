import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaSquaredCurvatureDynamics
import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaJacobiQuartic
import Mathlib.Tactic

/-!
# Dimensionless squared-curvature dynamics

This module performs the exact physical-to-dimensionless transport behind paper equation (62).
Keeping arclength `s` explicit exposes the Jacobian factor `k₀²/(4q₀)`; the paper's variable
`v = k₀s/(2√q₀)` removes precisely that factor.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

/-- Algebraic transport from the physical cubic (60) to the dimensionless cubic (62). -/
theorem squaredCurvatureCubic_to_dimensionless
    (k₀ q₀ : ℝˣ) (γ ν q : ℝ) :
    4 * (q₀ : ℝ) ^ 3 / (k₀ : ℝ) ^ 6 *
        squaredCurvatureCubic (k₀ : ℝ) γ ν
          ((k₀ : ℝ) ^ 2 * q / (q₀ : ℝ)) =
      dimensionlessCurvatureRHS (q₀ : ℝ) γ ν q := by
  rw [squaredCurvatureCubic, dimensionlessCurvatureRHS]
  field_simp [k₀.ne_zero, q₀.ne_zero]
  ring

/-- Paper's dimensionless squared curvature `q = q₀κ²/k₀²`, kept as a function of arclength. -/
noncomputable def dimensionlessSquaredCurvature
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (E : CenteredElasticaNormalization V) (q₀ : ℝˣ) (s : ℝ) : ℝ :=
  (q₀ : ℝ) / E.frame.geometry.curvature 0 ^ 2 *
    E.frame.geometry.curvature s ^ 2

/-- Arclength derivative of the dimensionless squared curvature. -/
noncomputable def dimensionlessSquaredCurvatureVelocity
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (E : CenteredElasticaNormalization V) (q₀ : ℝˣ) (s : ℝ) : ℝ :=
  (q₀ : ℝ) / E.frame.geometry.curvature 0 ^ 2 * squaredCurvatureVelocity E s

theorem dimensionlessSquaredCurvature_hasDerivAt
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (E : CenteredElasticaNormalization V) (q₀ : ℝˣ) (s : ℝ) :
    HasDerivAt (dimensionlessSquaredCurvature E q₀)
      (dimensionlessSquaredCurvatureVelocity E q₀ s) s := by
  have h := (stationaryElastica_curvatureSq_hasDerivAt E s).const_mul
    ((q₀ : ℝ) / E.frame.geometry.curvature 0 ^ 2)
  change HasDerivAt
    (fun y => (q₀ : ℝ) / E.frame.geometry.curvature 0 ^ 2 *
      E.frame.geometry.curvature y ^ 2)
    (dimensionlessSquaredCurvatureVelocity E q₀ s) s
  simpa only [dimensionlessSquaredCurvatureVelocity] using! h

theorem dimensionlessSquaredCurvature_zero
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (E : CenteredElasticaNormalization V) (q₀ : ℝˣ) :
    dimensionlessSquaredCurvature E q₀ 0 = (q₀ : ℝ) := by
  rw [dimensionlessSquaredCurvature]
  field_simp [ne_of_gt (E.frame.geometry.curvature_pos 0)]

theorem dimensionlessSquaredCurvatureVelocity_zero
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (E : CenteredElasticaNormalization V) (q₀ : ℝˣ) :
    dimensionlessSquaredCurvatureVelocity E q₀ 0 = 0 := by
  rw [dimensionlessSquaredCurvatureVelocity, squaredCurvatureVelocity_zero, mul_zero]

/-- Equation (62) before the paper's final change from arclength `s` to `v`. -/
theorem dimensionlessSquaredCurvature_arclength_equation
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (E : CenteredElasticaNormalization V) (q₀ : ℝˣ) (s : ℝ) :
    dimensionlessSquaredCurvatureVelocity E q₀ s ^ 2 =
      E.frame.geometry.curvature 0 ^ 2 / (4 * (q₀ : ℝ)) *
        dimensionlessCurvatureRHS (q₀ : ℝ) E.gamma E.nu
          (dimensionlessSquaredCurvature E q₀ s) := by
  have hcubic := stationaryElastica_squaredCurvature_cubic E s
  have hk₀ : E.frame.geometry.curvature 0 ≠ 0 :=
    ne_of_gt (E.frame.geometry.curvature_pos 0)
  have hq₀ : (q₀ : ℝ) ≠ 0 := q₀.ne_zero
  rw [dimensionlessSquaredCurvatureVelocity, dimensionlessSquaredCurvature]
  calc
    ((q₀ : ℝ) / E.frame.geometry.curvature 0 ^ 2 *
        squaredCurvatureVelocity E s) ^ 2 =
      (q₀ : ℝ) ^ 2 / E.frame.geometry.curvature 0 ^ 4 *
        squaredCurvatureVelocity E s ^ 2 := by ring
    _ = (q₀ : ℝ) ^ 2 / E.frame.geometry.curvature 0 ^ 4 *
        squaredCurvatureCubic (E.frame.geometry.curvature 0) E.gamma E.nu
          (E.frame.geometry.curvature s ^ 2) := by rw [hcubic]
    _ = E.frame.geometry.curvature 0 ^ 2 / (4 * (q₀ : ℝ)) *
        dimensionlessCurvatureRHS (q₀ : ℝ) E.gamma E.nu
          ((q₀ : ℝ) / E.frame.geometry.curvature 0 ^ 2 *
            E.frame.geometry.curvature s ^ 2) := by
      rw [squaredCurvatureCubic, dimensionlessCurvatureRHS]
      field_simp [hk₀, hq₀]
      ring

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
