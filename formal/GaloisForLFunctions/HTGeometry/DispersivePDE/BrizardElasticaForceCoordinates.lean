import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaForceMagnitude
import Mathlib.Tactic

/-!
# Frenet coordinates of the intrinsic elastica axis

The conserved variational force selects the paper's vertical unit vector.  This file identifies
its three Frenet coefficients, proves the displayed closed formulas, and derives the unit-sphere
constraint `A² + B² + C² = 1` without choosing ambient coordinates.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

/-- The reciprocal force magnitude, equal to the paper's squared spatial radius `ℛ²`. -/
noncomputable def normalizedForceScale
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (E : CenteredElasticaNormalization V) : ℝ :=
  ‖elasticaForce E.frame.geometry.toFrenetElasticaData 0‖⁻¹

/-- Tangent coefficient `A` of the normalized variational force. -/
noncomputable def verticalTangentCoefficient
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (E : CenteredElasticaNormalization V) (s : ℝ) : ℝ :=
  normalizedForceScale E *
    (-(E.frame.geometry.curvature s ^ (2 : ℕ) + E.frame.geometry.lagrange s))

/-- Normal coefficient `B` of the normalized variational force. -/
noncomputable def verticalNormalCoefficient
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (E : CenteredElasticaNormalization V) (s : ℝ) : ℝ :=
  normalizedForceScale E * E.frame.geometry.curvature₁ s

/-- Binormal coefficient `C` of the normalized variational force. -/
noncomputable def verticalBinormalCoefficient
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (E : CenteredElasticaNormalization V) (s : ℝ) : ℝ :=
  normalizedForceScale E *
    (E.frame.geometry.curvature s * E.frame.geometry.torsion s)

/-- Paper equation (75): `A = ℛ²(κ² + γ²k₀²/2)/2`. -/
theorem verticalTangentCoefficient_eq
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (E : CenteredElasticaNormalization V) (s : ℝ) :
    verticalTangentCoefficient E s =
      normalizedForceScale E *
        (E.frame.geometry.curvature s ^ (2 : ℕ) +
          E.gamma ^ (2 : ℕ) * E.frame.geometry.curvature 0 ^ (2 : ℕ) / 2) / 2 := by
  rw [verticalTangentCoefficient,
    stationaryElastica_lagrange_eq E.frame.geometry s, E.multiplier_selected]
  ring

/-- Paper equation (76): `B = ℛ²κ'`. -/
theorem verticalNormalCoefficient_eq
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (E : CenteredElasticaNormalization V) (s : ℝ) :
    verticalNormalCoefficient E s =
      normalizedForceScale E * E.frame.geometry.curvature₁ s := by
  rfl

/-- Paper equation (77): `C = ℛ²k₀²τ₀/κ`. -/
theorem verticalBinormalCoefficient_eq
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (E : CenteredElasticaNormalization V) (s : ℝ) :
    verticalBinormalCoefficient E s =
      normalizedForceScale E *
        (E.frame.geometry.curvature 0 ^ (2 : ℕ) * E.frame.geometry.torsion 0 /
          E.frame.geometry.curvature s) := by
  rw [verticalBinormalCoefficient,
    stationaryElastica_torsion_eq E.frame.geometry s]
  have hk : E.frame.geometry.curvature s ≠ 0 :=
    ne_of_gt (E.frame.geometry.curvature_pos s)
  field_simp [hk]

/-- Paper equation (74), now as an equality in any real inner-product space. -/
theorem elasticaVerticalAxis_eq_frenetExpansion
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (E : CenteredElasticaNormalization V) (s : ℝ) :
    elasticaVerticalAxis E s =
      verticalTangentCoefficient E s • E.frame.geometry.tangent s +
        verticalNormalCoefficient E s • E.frame.geometry.normal s +
        verticalBinormalCoefficient E s • E.frame.geometry.binormal s := by
  change normalizedForceScale E •
      (E.frame.geometry.curvature₁ s • E.frame.geometry.normal s +
        (E.frame.geometry.curvature s * E.frame.geometry.torsion s) •
          E.frame.geometry.binormal s -
        (E.frame.geometry.curvature s ^ (2 : ℕ) + E.frame.geometry.lagrange s) •
          E.frame.geometry.tangent s) = _
  rw [verticalTangentCoefficient, verticalNormalCoefficient,
    verticalBinormalCoefficient]
  simp only [smul_add, smul_sub, smul_smul]
  module

theorem inner_verticalAxis_tangent
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (E : CenteredElasticaNormalization V) (s : ℝ) :
    inner ℝ (elasticaVerticalAxis E s) (E.frame.geometry.tangent s) =
      verticalTangentCoefficient E s := by
  rw [elasticaVerticalAxis_eq_frenetExpansion]
  simp only [inner_add_left, real_inner_smul_left]
  rw [E.frame.tangent_self,
    show inner ℝ (E.frame.geometry.normal s) (E.frame.geometry.tangent s) = 0 by
      rw [real_inner_comm, E.frame.tangent_normal],
    show inner ℝ (E.frame.geometry.binormal s) (E.frame.geometry.tangent s) = 0 by
      rw [real_inner_comm, E.frame.tangent_binormal]]
  ring

theorem inner_verticalAxis_normal
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (E : CenteredElasticaNormalization V) (s : ℝ) :
    inner ℝ (elasticaVerticalAxis E s) (E.frame.geometry.normal s) =
      verticalNormalCoefficient E s := by
  rw [elasticaVerticalAxis_eq_frenetExpansion]
  simp only [inner_add_left, real_inner_smul_left]
  rw [E.frame.tangent_normal, E.frame.normal_self,
    show inner ℝ (E.frame.geometry.binormal s) (E.frame.geometry.normal s) = 0 by
      rw [real_inner_comm, E.frame.normal_binormal]]
  ring

theorem inner_verticalAxis_binormal
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (E : CenteredElasticaNormalization V) (s : ℝ) :
    inner ℝ (elasticaVerticalAxis E s) (E.frame.geometry.binormal s) =
      verticalBinormalCoefficient E s := by
  rw [elasticaVerticalAxis_eq_frenetExpansion]
  simp only [inner_add_left, real_inner_smul_left]
  rw [E.frame.tangent_binormal, E.frame.normal_binormal, E.frame.binormal_self]
  ring

/-- The three paper coefficients lie exactly on the unit sphere. -/
theorem verticalCoefficients_unitSphere
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (E : CenteredElasticaNormalization V) (s : ℝ) :
    verticalTangentCoefficient E s ^ (2 : ℕ) +
        verticalNormalCoefficient E s ^ (2 : ℕ) +
        verticalBinormalCoefficient E s ^ (2 : ℕ) = 1 := by
  have hsq := elasticaForce_norm_sq E.frame s
  have hconst := congrArg norm
    (stationaryElasticaForce_constant E.frame.geometry s)
  have hpos := centered_elasticaForce_norm_pos E
  rw [verticalTangentCoefficient, verticalNormalCoefficient,
    verticalBinormalCoefficient, normalizedForceScale]
  calc
    _ = ‖elasticaForce E.frame.geometry.toFrenetElasticaData 0‖⁻¹ ^ (2 : ℕ) *
        (E.frame.geometry.curvature₁ s ^ (2 : ℕ) +
          (E.frame.geometry.curvature s * E.frame.geometry.torsion s) ^ (2 : ℕ) +
          (E.frame.geometry.curvature s ^ (2 : ℕ) + E.frame.geometry.lagrange s) ^ (2 : ℕ)) := by
      ring
    _ = ‖elasticaForce E.frame.geometry.toFrenetElasticaData 0‖⁻¹ ^ (2 : ℕ) *
        ‖elasticaForce E.frame.geometry.toFrenetElasticaData s‖ ^ (2 : ℕ) := by
      rw [hsq]
    _ = ‖elasticaForce E.frame.geometry.toFrenetElasticaData 0‖⁻¹ ^ (2 : ℕ) *
        ‖elasticaForce E.frame.geometry.toFrenetElasticaData 0‖ ^ (2 : ℕ) := by
      rw [hconst]
    _ = 1 := by
      field_simp [ne_of_gt hpos]

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
