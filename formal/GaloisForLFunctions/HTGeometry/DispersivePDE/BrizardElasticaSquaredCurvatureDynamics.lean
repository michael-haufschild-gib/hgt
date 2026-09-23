import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaCurvatureEnergyDerived
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic

/-!
# Squared-curvature dynamics of a stationary elastica

This file turns the derived curvature energy into the paper's cubic equation (60), including its
physical-scale factorization.  The endpoint `κ²=k₀²` is an algebraic root independently of all
parameter signs.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

/-- Velocity of squared curvature, `(κ²)' = 2κκ'`. -/
noncomputable def squaredCurvatureVelocity
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (E : CenteredElasticaNormalization V) (s : ℝ) : ℝ :=
  2 * E.frame.geometry.curvature s * E.frame.geometry.curvature₁ s

theorem stationaryElastica_curvatureSq_hasDerivAt
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (E : CenteredElasticaNormalization V) (s : ℝ) :
    HasDerivAt (fun x => E.frame.geometry.curvature x ^ (2 : ℕ))
      (squaredCurvatureVelocity E s) s := by
  have h := (E.frame.geometry.curvature_deriv s).fun_pow 2
  norm_num at h
  simpa only [squaredCurvatureVelocity] using! h

/-- Physical-scale factorization of the cubic in paper equation (60). -/
theorem squaredCurvatureCubic_factor (k₀ γ ν q : ℝ) :
    squaredCurvatureCubic k₀ γ ν q =
      (k₀ ^ (2 : ℕ) - q) *
        (q ^ (2 : ℕ) + k₀ ^ (2 : ℕ) * (1 + γ ^ (2 : ℕ)) * q - k₀ ^ (4 : ℕ) * ν ^ (2 : ℕ)) := by
  rw [squaredCurvatureCubic]
  ring

theorem squaredCurvatureCubic_initial_root (k₀ γ ν : ℝ) :
    squaredCurvatureCubic k₀ γ ν (k₀ ^ (2 : ℕ)) = 0 := by
  rw [squaredCurvatureCubic_factor, sub_self, zero_mul]

/-- Paper equation (60) for every packaged centered stationary elastica. -/
theorem stationaryElastica_squaredCurvature_cubic
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (E : CenteredElasticaNormalization V) (s : ℝ) :
    squaredCurvatureVelocity E s ^ (2 : ℕ) =
      squaredCurvatureCubic (E.frame.geometry.curvature 0) E.gamma E.nu
        (E.frame.geometry.curvature s ^ (2 : ℕ)) := by
  rw [squaredCurvatureVelocity]
  calc
    (2 * E.frame.geometry.curvature s * E.frame.geometry.curvature₁ s) ^ (2 : ℕ) =
        4 * E.frame.geometry.curvature s ^ (2 : ℕ) *
          E.frame.geometry.curvature₁ s ^ (2 : ℕ) := by ring
    _ = 4 * E.frame.geometry.curvature s ^ (2 : ℕ) *
        curvatureEnergy (E.frame.geometry.curvature 0) E.gamma E.nu
          (E.curvatureUnitAt s) := by
      rw [stationaryElastica_curvature₁_sq_eq_energy]
    _ = squaredCurvatureCubic (E.frame.geometry.curvature 0) E.gamma E.nu
        (E.frame.geometry.curvature s ^ (2 : ℕ)) := by
      exact curvatureEnergy_to_squaredCubic
        (E.frame.geometry.curvature 0) E.gamma E.nu (E.curvatureUnitAt s)

/-- Factorized form of the actual squared-curvature equation. -/
theorem stationaryElastica_squaredCurvature_factorized
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (E : CenteredElasticaNormalization V) (s : ℝ) :
    squaredCurvatureVelocity E s ^ (2 : ℕ) =
      (E.frame.geometry.curvature 0 ^ (2 : ℕ) - E.frame.geometry.curvature s ^ (2 : ℕ)) *
        (E.frame.geometry.curvature s ^ (4 : ℕ) +
          E.frame.geometry.curvature 0 ^ (2 : ℕ) * (1 + E.gamma ^ (2 : ℕ)) *
            E.frame.geometry.curvature s ^ (2 : ℕ) -
          E.frame.geometry.curvature 0 ^ (4 : ℕ) * E.nu ^ (2 : ℕ)) := by
  rw [stationaryElastica_squaredCurvature_cubic, squaredCurvatureCubic_factor]
  ring

theorem squaredCurvatureVelocity_zero
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (E : CenteredElasticaNormalization V) :
    squaredCurvatureVelocity E 0 = 0 := by
  rw [squaredCurvatureVelocity, E.curvature₁_zero, mul_zero]

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
