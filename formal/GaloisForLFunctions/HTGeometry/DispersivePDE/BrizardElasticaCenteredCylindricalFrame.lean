import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaCylindricalFrame
import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaCurvatureEnergyDerived
import Mathlib.Tactic

/-!
# Centered elastica in the cylindrical chart

The abstract cylindrical-frame construction is instantiated with the actual conserved-force
coefficients at the centered point.  There the normal coefficient vanishes, so the radial axis
is exactly minus the Frenet normal and the remaining two axes form a planar rotation.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

theorem normalizedForceScale_pos
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (E : CenteredElasticaNormalization V) :
    0 < normalizedForceScale E := by
  rw [normalizedForceScale]
  exact inv_pos.2 (centered_elasticaForce_norm_pos E)

theorem verticalTangentCoefficient_zero_pos
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (E : CenteredElasticaNormalization V) :
    0 < verticalTangentCoefficient E 0 := by
  rw [verticalTangentCoefficient_eq]
  have hk : 0 < E.frame.geometry.curvature 0 ^ 2 :=
    sq_pos_of_pos (E.frame.geometry.curvature_pos 0)
  have hg : 0 ≤ E.gamma ^ 2 := sq_nonneg E.gamma
  have hs := normalizedForceScale_pos E
  positivity

noncomputable def centeredVerticalCoefficients
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (E : CenteredElasticaNormalization V) : RegularVerticalCoefficients where
  A := verticalTangentCoefficient E 0
  B := verticalNormalCoefficient E 0
  C := verticalBinormalCoefficient E 0
  unitSphere := verticalCoefficients_unitSphere E 0
  cylindricalRegular := by
    rw [verticalBinormalCoefficient_sq_zero]
    exact spatialOmegaSq_lt_one E.gamma E.nu

theorem centeredCylindricalDenominator_eq_tangent
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (E : CenteredElasticaNormalization V) :
    cylindricalDenominator (centeredVerticalCoefficients E) =
      verticalTangentCoefficient E 0 := by
  have hden := cylindricalDenominator_sq (centeredVerticalCoefficients E)
  have hA := verticalTangentCoefficient_sq_zero E
  have hC := verticalBinormalCoefficient_sq_zero E
  have hden_pos := cylindricalDenominator_pos (centeredVerticalCoefficients E)
  have hA_pos := verticalTangentCoefficient_zero_pos E
  change cylindricalDenominator (centeredVerticalCoefficients E) ^ 2 =
    1 - verticalBinormalCoefficient E 0 ^ 2 at hden
  rw [hC, ← hA] at hden
  nlinarith

/-- At the centered point the cylindrical radial axis is exactly `-normal`. -/
theorem centeredRadialInFrenet_eq
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (E : CenteredElasticaNormalization V) :
    radialInFrenet (centeredVerticalCoefficients E) = ⟨0, -1, 0⟩ := by
  ext
  · simp [radialInFrenet, centeredVerticalCoefficients,
      verticalNormalCoefficient_zero E]
  · change -verticalTangentCoefficient E 0 /
        cylindricalDenominator (centeredVerticalCoefficients E) = -1
    rw [centeredCylindricalDenominator_eq_tangent E]
    field_simp [ne_of_gt (verticalTangentCoefficient_zero_pos E)]
  · rfl

/-- Centered azimuthal axis is the complementary rotation in the tangent--binormal plane. -/
theorem centeredAzimuthalInFrenet_eq
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (E : CenteredElasticaNormalization V) :
    azimuthalInFrenet (centeredVerticalCoefficients E) =
      ⟨verticalBinormalCoefficient E 0, 0,
        -verticalTangentCoefficient E 0⟩ := by
  rw [azimuthalInFrenet_eq]
  ext
  · change verticalBinormalCoefficient E 0 * verticalTangentCoefficient E 0 /
        cylindricalDenominator (centeredVerticalCoefficients E) =
      verticalBinormalCoefficient E 0
    rw [centeredCylindricalDenominator_eq_tangent E]
    field_simp [ne_of_gt (verticalTangentCoefficient_zero_pos E)]
  · simp [centeredVerticalCoefficients, verticalNormalCoefficient_zero E]
  · change -cylindricalDenominator (centeredVerticalCoefficients E) =
      -verticalTangentCoefficient E 0
    rw [centeredCylindricalDenominator_eq_tangent E]

theorem centeredVerticalInFrenet_eq
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (E : CenteredElasticaNormalization V) :
    verticalInFrenet (centeredVerticalCoefficients E) =
      ⟨verticalTangentCoefficient E 0, 0,
        verticalBinormalCoefficient E 0⟩ := by
  ext <;> simp [verticalInFrenet, centeredVerticalCoefficients,
    verticalNormalCoefficient_zero E]

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
