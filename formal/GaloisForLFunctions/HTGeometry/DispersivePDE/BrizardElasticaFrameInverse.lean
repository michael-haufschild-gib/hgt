import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaFrameRotation
import Mathlib.Tactic

/-!
# Inverse Frenet--cylindrical frame rotation

The paper prints the Frenet frame in cylindrical coordinates.  These identities prove the inverse
rotation explicitly: each cylindrical axis is reconstructed as a Frenet-frame linear combination.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

def frameLinearCombination
    (a : ℝ) (u : FrameCoordinates) (b : ℝ) (v : FrameCoordinates)
    (c : ℝ) (w : FrameCoordinates) : FrameCoordinates where
  radial := a * u.radial + b * v.radial + c * w.radial
  azimuthal := a * u.azimuthal + b * v.azimuthal + c * w.azimuthal
  vertical := a * u.vertical + b * v.vertical + c * w.vertical

/-- Inverse radial-axis row of the paper's rotation matrix. -/
theorem radialAxis_frenetExpansion (α β : ℝ) :
    radialAxis = frameLinearCombination
      (Real.sin α) (tangentCoordinates α β)
      (-Real.cos α) (normalCoordinates α β)
      0 (binormalCoordinates β) := by
  ext
  · simp [radialAxis, frameLinearCombination, tangentCoordinates,
      normalCoordinates, binormalCoordinates]
    nlinarith [Real.sin_sq_add_cos_sq α]
  · simp [radialAxis, frameLinearCombination, tangentCoordinates,
      normalCoordinates, binormalCoordinates]
    ring
  · simp [radialAxis, frameLinearCombination, tangentCoordinates,
      normalCoordinates, binormalCoordinates]
    ring

/-- Inverse azimuthal-axis row of the paper's rotation matrix. -/
theorem azimuthalAxis_frenetExpansion (α β : ℝ) :
    azimuthalAxis = frameLinearCombination
      (Real.cos α * Real.sin β) (tangentCoordinates α β)
      (Real.sin α * Real.sin β) (normalCoordinates α β)
      (-Real.cos β) (binormalCoordinates β) := by
  ext
  · simp [azimuthalAxis, frameLinearCombination, tangentCoordinates,
      normalCoordinates, binormalCoordinates]
    ring
  · simp [azimuthalAxis, frameLinearCombination, tangentCoordinates,
      normalCoordinates, binormalCoordinates]
    calc
      1 = Real.sin β ^ 2 *
            (Real.sin α ^ 2 + Real.cos α ^ 2) + Real.cos β ^ 2 := by
              rw [Real.sin_sq_add_cos_sq α]
              nlinarith [Real.sin_sq_add_cos_sq β]
      _ = _ := by ring
  · simp [azimuthalAxis, frameLinearCombination, tangentCoordinates,
      normalCoordinates, binormalCoordinates]
    symm
    calc
      _ = Real.sin β * Real.cos β *
          (Real.cos α ^ 2 + Real.sin α ^ 2 - 1) := by ring
      _ = 0 := by
        rw [show Real.cos α ^ 2 + Real.sin α ^ 2 = 1 by
          nlinarith [Real.sin_sq_add_cos_sq α]]
        ring

/-- Equation (74), expressed through the angular coordinates of equations (83)--(85). -/
theorem verticalAxis_frenetExpansion (α β : ℝ) :
    verticalAxis = frameLinearCombination
      (Real.cos α * Real.cos β) (tangentCoordinates α β)
      (Real.sin α * Real.cos β) (normalCoordinates α β)
      (Real.sin β) (binormalCoordinates β) := by
  ext
  · simp [verticalAxis, frameLinearCombination, tangentCoordinates,
      normalCoordinates, binormalCoordinates]
    ring
  · simp [verticalAxis, frameLinearCombination, tangentCoordinates,
      normalCoordinates, binormalCoordinates]
    symm
    calc
      _ = Real.cos β * Real.sin β *
          (Real.cos α ^ 2 + Real.sin α ^ 2 - 1) := by ring
      _ = 0 := by
        rw [show Real.cos α ^ 2 + Real.sin α ^ 2 = 1 by
          nlinarith [Real.sin_sq_add_cos_sq α]]
        ring
  · simp [verticalAxis, frameLinearCombination, tangentCoordinates,
      normalCoordinates, binormalCoordinates]
    calc
      1 = Real.cos β ^ 2 *
            (Real.sin α ^ 2 + Real.cos α ^ 2) + Real.sin β ^ 2 := by
              rw [Real.sin_sq_add_cos_sq α]
              nlinarith [Real.sin_sq_add_cos_sq β]
      _ = _ := by ring

theorem frameLinearCombination_dot
    (a : ℝ) (u : FrameCoordinates) (b : ℝ) (v : FrameCoordinates)
    (c : ℝ) (w x : FrameCoordinates) :
    frameDot (frameLinearCombination a u b v c w) x =
      a * frameDot u x + b * frameDot v x + c * frameDot w x := by
  simp [frameDot, frameLinearCombination]
  ring

/-- Orthogonal projection recovers the tangent coefficient of the vertical axis expansion. -/
theorem verticalAxis_tangentProjection (α β : ℝ) :
    frameDot verticalAxis (tangentCoordinates α β) =
      Real.cos α * Real.cos β := by
  simp [frameDot, verticalAxis, tangentCoordinates]

/-- Orthogonal projection recovers the normal coefficient of the vertical axis expansion. -/
theorem verticalAxis_normalProjection (α β : ℝ) :
    frameDot verticalAxis (normalCoordinates α β) =
      Real.sin α * Real.cos β := by
  simp [frameDot, verticalAxis, normalCoordinates]

/-- Orthogonal projection recovers the binormal coefficient of the vertical axis expansion. -/
theorem verticalAxis_binormalProjection (β : ℝ) :
    frameDot verticalAxis (binormalCoordinates β) = Real.sin β := by
  simp [frameDot, verticalAxis, binormalCoordinates]

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
