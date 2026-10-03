import GaloisForLFunctions.RHTower.ThetaTailSmallNodeCoordinate
import GaloisForLFunctions.RHTower.ThetaTailCenterSourceConvexity

/-! A uniform triangular region of positive actual center Schur residuals. -/

noncomputable section
namespace RHTower.ThetaJoint
open ThetaConfluent ThetaCoordinate

local notation "k" => thetaCuspFullSource
local notation "H" => thetaTailFirstMomentKernel
local notation "J" => thetaTailFirstMomentKernel 0 0
local notation "D" => ThetaSturm.determinant

def normalizedProjection (z y : ℝ) : ℝ :=
  k z/k y*(J*H z y-H 0 z*H 0 y)/D 0 z

theorem coordinateResidual_eq_projection (z y : ℝ) :
    coordinateResidual z y = k y*(y-z*normalizedProjection z y) := by
  unfold coordinateResidual normalizedProjection
  field_simp [(thetaCuspFullSource_pos_all y).ne']

/-- The source residual retains the same actual inverse-Gram projection coefficient. -/
theorem sourceResidual_eq_projection {z : ℝ} (hz : 0 < z) (y : ℝ) :
    sourceResidual z y = k y*(sourceDeficit y-normalizedProjection z y*sourceDeficit z) := by
  have hD : D 0 z ≠ 0 := (ThetaTailTwoPoint.kernel_two_point_det_pos hz.ne).ne'
  unfold sourceResidual sourceDeficit normalizedProjection ThetaSturm.representerLeft
    ThetaSturm.representerRight
  field_simp [(thetaCuspFullSource_pos_all z).ne', (thetaCuspFullSource_pos_all y).ne',
    centerMass_pos.ne', hD]
  unfold ThetaSturm.determinant
  ring

/-- Both literal inverse-Gram residuals are strictly positive throughout one triangular
neighborhood, including pairs approaching the diagonal at arbitrary relative speeds. -/
theorem exists_actual_ports_pos_triangle :
    ∃ e > 0, ∀ z y : ℝ, 0 < z → z < y → y < e →
      0 < sourceResidual z y ∧ 0 < coordinateResidual z y := by
  obtain ⟨e₁,he₁,hcoord⟩ := exists_coordinateResidual_pos_triangle
  obtain ⟨e₂,he₂,hsource⟩ := exists_sourceDeficit_chord
  refine ⟨min e₁ e₂,lt_min he₁ he₂,?_⟩
  intro z y hz hzy hye
  have hc := hcoord z y hz hzy (lt_of_lt_of_le hye (min_le_left _ _))
  obtain ⟨hg,hchord⟩ := hsource z y hz hzy (lt_of_lt_of_le hye (min_le_right _ _))
  refine ⟨?_,hc⟩
  have hgap : 0 < y-z*normalizedProjection z y := by
    rw [coordinateResidual_eq_projection] at hc
    nlinarith only [hc, thetaCuspFullSource_pos_all y]
  have hprod := mul_pos hgap hg
  have hscaled : 0 < z*(sourceDeficit y-normalizedProjection z y*sourceDeficit z) := by
    nlinarith only [hprod, hchord]
  have hres : 0 < sourceDeficit y-normalizedProjection z y*sourceDeficit z := by
    nlinarith only [hscaled, hz]
  rw [sourceResidual_eq_projection hz]
  exact mul_pos (thetaCuspFullSource_pos_all y) hres

end RHTower.ThetaJoint
