import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaForceCoordinates
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic

/-!
# Intrinsic vertical position of a stationary elastica

Once the conserved force selects the vertical axis, projection of any arclength-parametrized
position curve onto that axis has derivative exactly equal to the paper's coefficient `A`.
This is the coordinate-free content of equation (90).
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

/-- A centered stationary elastica together with an ambient position curve whose derivative is its
unit tangent. -/
structure PositionedCenteredElastica
    (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] where
  normalization : CenteredElasticaNormalization V
  position : ℝ → V
  position_deriv : ∀ s, HasDerivAt position (normalization.frame.geometry.tangent s) s

/-- Vertical coordinate obtained by projection onto the intrinsic conserved-force axis. -/
noncomputable def intrinsicVerticalPosition
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (P : PositionedCenteredElastica V) (s : ℝ) : ℝ :=
  inner ℝ (elasticaVerticalAxis P.normalization 0) (P.position s)

/-- Paper equation (90): `z' = A`, with no ambient coordinate choice. -/
theorem intrinsicVerticalPosition_hasDerivAt
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (P : PositionedCenteredElastica V) (s : ℝ) :
    HasDerivAt (intrinsicVerticalPosition P)
      (verticalTangentCoefficient P.normalization s) s := by
  have h := (hasDerivAt_const s (elasticaVerticalAxis P.normalization 0)).inner ℝ
    (P.position_deriv s)
  have hproj :
      inner ℝ (elasticaVerticalAxis P.normalization 0)
          (P.normalization.frame.geometry.tangent s) =
        verticalTangentCoefficient P.normalization s := by
    rw [← elasticaVerticalAxis_constant P.normalization s]
    exact inner_verticalAxis_tangent P.normalization s
  change HasDerivAt
    (fun x => inner ℝ (elasticaVerticalAxis P.normalization 0) (P.position x))
    (verticalTangentCoefficient P.normalization s) s
  simpa only [inner_zero_left, add_zero, hproj] using h

/-- Closed version of `z' = A` in the paper's `(γ,k₀)` normalization. -/
theorem intrinsicVerticalPosition_hasDerivAt_closedFormula
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (P : PositionedCenteredElastica V) (s : ℝ) :
    HasDerivAt (intrinsicVerticalPosition P)
      (normalizedForceScale P.normalization *
        (P.normalization.frame.geometry.curvature s ^ 2 +
          P.normalization.gamma ^ 2 *
            P.normalization.frame.geometry.curvature 0 ^ 2 / 2) / 2) s := by
  convert intrinsicVerticalPosition_hasDerivAt P s using 1
  exact (verticalTangentCoefficient_eq P.normalization s).symm

/-- Choosing the position origin on the curve makes the intrinsic vertical coordinate vanish
there. -/
theorem intrinsicVerticalPosition_zero
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (P : PositionedCenteredElastica V) (hP : P.position 0 = 0) :
    intrinsicVerticalPosition P 0 = 0 := by
  rw [intrinsicVerticalPosition, hP, inner_zero_right]

/-- Central inversion symmetry of the ambient curve descends to oddness of vertical position. -/
theorem intrinsicVerticalPosition_neg
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (P : PositionedCenteredElastica V)
    (hP : ∀ s, P.position (-s) = -P.position s) (s : ℝ) :
    intrinsicVerticalPosition P (-s) = -intrinsicVerticalPosition P s := by
  rw [intrinsicVerticalPosition, intrinsicVerticalPosition, hP, inner_neg_right]

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
