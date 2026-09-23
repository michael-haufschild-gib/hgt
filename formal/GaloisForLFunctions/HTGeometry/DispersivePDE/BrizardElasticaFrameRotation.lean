import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaSpatialFrame
import Mathlib.Tactic

/-!
# Frenet--cylindrical frame rotation

Equations (83)--(85) of arXiv:2607.21750 give the Frenet frame in cylindrical coordinates using
two angles.  This module realizes those displayed coordinate triples and proves that they form a
positively oriented orthonormal frame for every pair of real angles.  The angle formula therefore
extends smoothly even where the paper's preceding division by `sqrt (1-C²)` degenerates.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

@[ext]
structure FrameCoordinates where
  radial : ℝ
  azimuthal : ℝ
  vertical : ℝ

def frameDot (u v : FrameCoordinates) : ℝ :=
  u.radial * v.radial + u.azimuthal * v.azimuthal + u.vertical * v.vertical

def frameCross (u v : FrameCoordinates) : FrameCoordinates where
  radial := u.azimuthal * v.vertical - u.vertical * v.azimuthal
  azimuthal := u.vertical * v.radial - u.radial * v.vertical
  vertical := u.radial * v.azimuthal - u.azimuthal * v.radial

/-- Equation (83): tangent coordinates in the cylindrical frame. -/
noncomputable def tangentCoordinates (α β : ℝ) : FrameCoordinates where
  radial := Real.sin α
  azimuthal := Real.cos α * Real.sin β
  vertical := Real.cos α * Real.cos β

/-- Equation (84): normal coordinates in the cylindrical frame. -/
noncomputable def normalCoordinates (α β : ℝ) : FrameCoordinates where
  radial := -Real.cos α
  azimuthal := Real.sin α * Real.sin β
  vertical := Real.sin α * Real.cos β

/-- Equation (85): binormal coordinates in the cylindrical frame. -/
noncomputable def binormalCoordinates (β : ℝ) : FrameCoordinates where
  radial := 0
  azimuthal := -Real.cos β
  vertical := Real.sin β

def radialAxis : FrameCoordinates := ⟨1, 0, 0⟩
def azimuthalAxis : FrameCoordinates := ⟨0, 1, 0⟩
def verticalAxis : FrameCoordinates := ⟨0, 0, 1⟩

theorem tangentCoordinates_unit (α β : ℝ) :
    frameDot (tangentCoordinates α β) (tangentCoordinates α β) = 1 := by
  simp only [frameDot, tangentCoordinates]
  nlinarith [Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq β]

theorem normalCoordinates_unit (α β : ℝ) :
    frameDot (normalCoordinates α β) (normalCoordinates α β) = 1 := by
  simp only [frameDot, normalCoordinates]
  nlinarith [Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq β]

theorem binormalCoordinates_unit (β : ℝ) :
    frameDot (binormalCoordinates β) (binormalCoordinates β) = 1 := by
  simp only [frameDot, binormalCoordinates]
  nlinarith [Real.sin_sq_add_cos_sq β]

theorem tangent_dot_normal (α β : ℝ) :
    frameDot (tangentCoordinates α β) (normalCoordinates α β) = 0 := by
  simp only [frameDot, tangentCoordinates, normalCoordinates]
  calc
    _ = Real.sin α * Real.cos α *
        (-1 + (Real.sin β) ^ (2 : ℕ) + (Real.cos β) ^ (2 : ℕ)) := by ring
    _ = 0 := by
      have h : -1 + (Real.sin β) ^ (2 : ℕ) + (Real.cos β) ^ (2 : ℕ) = 0 := by
        nlinarith [Real.sin_sq_add_cos_sq β]
      rw [h, mul_zero]

theorem tangent_dot_binormal (α β : ℝ) :
    frameDot (tangentCoordinates α β) (binormalCoordinates β) = 0 := by
  simp only [frameDot, tangentCoordinates, binormalCoordinates]
  ring

theorem normal_dot_binormal (α β : ℝ) :
    frameDot (normalCoordinates α β) (binormalCoordinates β) = 0 := by
  simp only [frameDot, normalCoordinates, binormalCoordinates]
  ring

/-- Right-handed orientation: the displayed tangent cross normal is the displayed binormal. -/
theorem tangent_cross_normal (α β : ℝ) :
    frameCross (tangentCoordinates α β) (normalCoordinates α β) =
      binormalCoordinates β := by
  ext
  · simp only [frameCross, tangentCoordinates, normalCoordinates, binormalCoordinates]
    ring
  · simp only [frameCross, tangentCoordinates, normalCoordinates, binormalCoordinates]
    calc
      _ = -((Real.sin α) ^ (2 : ℕ) + (Real.cos α) ^ (2 : ℕ)) * Real.cos β := by ring
      _ = -Real.cos β := by rw [Real.sin_sq_add_cos_sq]; ring
  · simp only [frameCross, tangentCoordinates, normalCoordinates, binormalCoordinates]
    calc
      _ = ((Real.sin α) ^ (2 : ℕ) + (Real.cos α) ^ (2 : ℕ)) * Real.sin β := by ring
      _ = Real.sin β := by rw [Real.sin_sq_add_cos_sq]; ring

theorem normal_cross_binormal (α β : ℝ) :
    frameCross (normalCoordinates α β) (binormalCoordinates β) =
      tangentCoordinates α β := by
  ext
  · simp only [frameCross, tangentCoordinates, normalCoordinates, binormalCoordinates]
    calc
      _ = Real.sin α * ((Real.sin β) ^ (2 : ℕ) + (Real.cos β) ^ (2 : ℕ)) := by ring
      _ = Real.sin α := by rw [Real.sin_sq_add_cos_sq]; ring
  · simp only [frameCross, tangentCoordinates, normalCoordinates, binormalCoordinates]
    ring
  · simp only [frameCross, tangentCoordinates, normalCoordinates, binormalCoordinates]
    ring

theorem binormal_cross_tangent (α β : ℝ) :
    frameCross (binormalCoordinates β) (tangentCoordinates α β) =
      normalCoordinates α β := by
  ext
  · simp only [frameCross, tangentCoordinates, normalCoordinates, binormalCoordinates]
    calc
      _ = -Real.cos α * ((Real.sin β) ^ (2 : ℕ) + (Real.cos β) ^ (2 : ℕ)) := by ring
      _ = -Real.cos α := by rw [Real.sin_sq_add_cos_sq]; ring
  · simp only [frameCross, tangentCoordinates, normalCoordinates, binormalCoordinates]
    ring
  · simp only [frameCross, tangentCoordinates, normalCoordinates, binormalCoordinates]
    ring

/-- The paper's angle parameterization recovers `A=cos α cos β`. -/
theorem tangent_vertical_component (α β : ℝ) :
    frameDot (tangentCoordinates α β) verticalAxis = Real.cos α * Real.cos β := by
  simp [frameDot, tangentCoordinates, verticalAxis]

/-- The paper's angle parameterization recovers `B=sin α cos β`. -/
theorem normal_vertical_component (α β : ℝ) :
    frameDot (normalCoordinates α β) verticalAxis = Real.sin α * Real.cos β := by
  simp [frameDot, normalCoordinates, verticalAxis]

/-- The paper's angle parameterization recovers `C=sin β`. -/
theorem binormal_vertical_component (β : ℝ) :
    frameDot (binormalCoordinates β) verticalAxis = Real.sin β := by
  simp [frameDot, binormalCoordinates, verticalAxis]

/-- The coordinate rotation has determinant one. -/
theorem frenetCylindrical_orientation (α β : ℝ) :
    frameDot
        (frameCross (tangentCoordinates α β) (normalCoordinates α β))
        (binormalCoordinates β) = 1 := by
  rw [tangent_cross_normal, binormalCoordinates_unit]

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
