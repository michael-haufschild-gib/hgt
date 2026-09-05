import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaForceCoordinates
import Mathlib.Tactic

/-!
# Deriving the elastica first integral from conserved force

The paper obtains equation (59) by integrating the scalar curvature ODE.  Here it follows instead
from the constant norm of the variational force.  This closes the gap between actual stationary
elastica data and the earlier algebraic `spatialAcoefSq`, `spatialBcoefSq`, `spatialCcoefSq` model.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

/-- Curvature at an arbitrary point, packaged as a nonzero real unit. -/
noncomputable def CenteredElasticaNormalization.curvatureUnitAt
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (E : CenteredElasticaNormalization V) (s : ℝ) : ℝˣ :=
  Units.mk0 (E.frame.geometry.curvature s)
    (ne_of_gt (E.frame.geometry.curvature_pos s))

/-- Paper equation (59), derived from the conserved force rather than assumed as a first integral. -/
theorem stationaryElastica_curvature₁_sq_eq_energy
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (E : CenteredElasticaNormalization V) (s : ℝ) :
    E.frame.geometry.curvature₁ s ^ 2 =
      curvatureEnergy (E.frame.geometry.curvature 0) E.gamma E.nu
        (E.curvatureUnitAt s) := by
  have hs := elasticaForce_norm_sq E.frame s
  have hconst := congrArg (fun x : V => ‖x‖ ^ 2)
    (stationaryElasticaForce_constant E.frame.geometry s)
  have hzero := centered_elasticaForce_norm_sq E
  have hmag :
      E.frame.geometry.curvature₁ s ^ 2 +
          (E.frame.geometry.curvature s * E.frame.geometry.torsion s) ^ 2 +
          (E.frame.geometry.curvature s ^ 2 + E.frame.geometry.lagrange s) ^ 2 =
        E.frame.geometry.curvature 0 ^ 4 / 4 *
          ((1 + E.gamma ^ 2 / 2) ^ 2 + E.nu ^ 2) := by
    calc
      _ = ‖elasticaForce E.frame.geometry.toFrenetElasticaData s‖ ^ 2 := hs.symm
      _ = ‖elasticaForce E.frame.geometry.toFrenetElasticaData 0‖ ^ 2 := hconst
      _ = _ := hzero
  have hlagrange := stationaryElastica_lagrange_eq E.frame.geometry s
  rw [E.multiplier_selected] at hlagrange
  have htorsion := stationaryElastica_torsion_eq E.frame.geometry s
  rw [hlagrange, htorsion, E.torsion_selected] at hmag
  rw [curvatureEnergy]
  change E.frame.geometry.curvature₁ s ^ 2 =
    (E.frame.geometry.curvature 0 ^ 4 - E.frame.geometry.curvature s ^ 4) / 4 +
      (E.frame.geometry.curvature 0 ^ 2 * E.gamma ^ 2 / 4) *
        (E.frame.geometry.curvature 0 ^ 2 - E.frame.geometry.curvature s ^ 2) +
      (E.frame.geometry.curvature 0 ^ 4 * E.nu ^ 2 / 4) *
        (1 - E.frame.geometry.curvature 0 ^ 2 /
          E.frame.geometry.curvature s ^ 2)
  rw [E.torsion_selected]
  have hk : E.frame.geometry.curvature s ≠ 0 :=
    ne_of_gt (E.frame.geometry.curvature_pos s)
  have hk₀ : E.frame.geometry.curvature 0 ≠ 0 :=
    ne_of_gt (E.frame.geometry.curvature_pos 0)
  field_simp [hk, hk₀] at hmag ⊢
  nlinarith [hmag]

/-- The reciprocal force magnitude squared is exactly the symbolic `ℛ⁴`. -/
theorem normalizedForceScale_sq
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (E : CenteredElasticaNormalization V) :
    normalizedForceScale E ^ 2 =
      spatialRadiusFourth E.curvatureUnit E.gamma E.nu := by
  have h := spatialRadiusFourth_mul_force_norm_sq E
  have hn := centered_elasticaForce_norm_pos E
  rw [normalizedForceScale]
  field_simp [ne_of_gt hn] at h ⊢
  exact h.symm

/-- Actual tangent coefficient squared equals the paper's algebraic `A²`. -/
theorem verticalTangentCoefficient_sq_eq_spatialA
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (E : CenteredElasticaNormalization V) (s : ℝ) :
    verticalTangentCoefficient E s ^ 2 =
      spatialAcoefSq E.curvatureUnit E.gamma E.nu (E.curvatureUnitAt s) := by
  rw [verticalTangentCoefficient_eq, spatialAcoefSq]
  calc
    _ = normalizedForceScale E ^ 2 *
        (E.frame.geometry.curvature s ^ 2 +
          E.gamma ^ 2 * E.frame.geometry.curvature 0 ^ 2 / 2) ^ 2 / 4 := by
      ring
    _ = spatialRadiusFourth E.curvatureUnit E.gamma E.nu *
        (E.frame.geometry.curvature s ^ 2 +
          E.gamma ^ 2 * E.frame.geometry.curvature 0 ^ 2 / 2) ^ 2 / 4 := by
      rw [normalizedForceScale_sq]
    _ = _ := by rfl

/-- Actual normal coefficient squared equals the paper's algebraic `B²`. -/
theorem verticalNormalCoefficient_sq_eq_spatialB
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (E : CenteredElasticaNormalization V) (s : ℝ) :
    verticalNormalCoefficient E s ^ 2 =
      spatialBcoefSq E.curvatureUnit E.gamma E.nu (E.curvatureUnitAt s) := by
  rw [verticalNormalCoefficient, spatialBcoefSq]
  calc
    _ = normalizedForceScale E ^ 2 * E.frame.geometry.curvature₁ s ^ 2 := by ring
    _ = spatialRadiusFourth E.curvatureUnit E.gamma E.nu *
        curvatureEnergy (E.frame.geometry.curvature 0) E.gamma E.nu
          (E.curvatureUnitAt s) := by
      rw [normalizedForceScale_sq, stationaryElastica_curvature₁_sq_eq_energy]
    _ = _ := by rfl

/-- Actual binormal coefficient squared equals the paper's algebraic `C²`. -/
theorem verticalBinormalCoefficient_sq_eq_spatialC
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (E : CenteredElasticaNormalization V) (s : ℝ) :
    verticalBinormalCoefficient E s ^ 2 =
      spatialCcoefSq E.curvatureUnit E.gamma E.nu (E.curvatureUnitAt s) := by
  rw [verticalBinormalCoefficient_eq, spatialCcoefSq]
  calc
    _ = normalizedForceScale E ^ 2 *
        (E.frame.geometry.curvature 0 ^ 2 * E.frame.geometry.torsion 0 /
          E.frame.geometry.curvature s) ^ 2 := by ring
    _ = spatialRadiusFourth E.curvatureUnit E.gamma E.nu *
        (E.frame.geometry.curvature 0 ^ 2 * E.frame.geometry.torsion 0 /
          E.frame.geometry.curvature s) ^ 2 := by
      rw [normalizedForceScale_sq]
    _ = _ := by
      change spatialRadiusFourth E.curvatureUnit E.gamma E.nu *
          (E.frame.geometry.curvature 0 ^ 2 * E.frame.geometry.torsion 0 /
            E.frame.geometry.curvature s) ^ 2 =
        spatialRadiusFourth E.curvatureUnit E.gamma E.nu *
          E.frame.geometry.curvature 0 ^ 6 *
            E.nu ^ 2 /
          (4 * E.frame.geometry.curvature s ^ 2)
      rw [E.torsion_selected]
      have hk₀ : E.frame.geometry.curvature 0 ≠ 0 :=
        ne_of_gt (E.frame.geometry.curvature_pos 0)
      have hk : E.frame.geometry.curvature s ≠ 0 :=
        ne_of_gt (E.frame.geometry.curvature_pos s)
      field_simp [hk₀, hk]
      ring

theorem verticalNormalCoefficient_zero
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (E : CenteredElasticaNormalization V) :
    verticalNormalCoefficient E 0 = 0 := by
  rw [verticalNormalCoefficient, E.curvature₁_zero, mul_zero]

/-- At centered initial data, the binormal weight is exactly `Ω²`. -/
theorem verticalBinormalCoefficient_sq_zero
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (E : CenteredElasticaNormalization V) :
    verticalBinormalCoefficient E 0 ^ 2 = spatialOmegaSq E.gamma E.nu := by
  rw [verticalBinormalCoefficient_sq_eq_spatialC]
  have hunit : E.curvatureUnitAt 0 = E.curvatureUnit := by
    apply Units.ext
    rfl
  rw [hunit, spatialCcoefSq_initial]

/-- At centered initial data, the tangent weight is exactly `1-Ω²`. -/
theorem verticalTangentCoefficient_sq_zero
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (E : CenteredElasticaNormalization V) :
    verticalTangentCoefficient E 0 ^ 2 = 1 - spatialOmegaSq E.gamma E.nu := by
  rw [verticalTangentCoefficient_sq_eq_spatialA]
  have hunit : E.curvatureUnitAt 0 = E.curvatureUnit := by
    apply Units.ext
    rfl
  rw [hunit, spatialAcoefSq_initial]

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
