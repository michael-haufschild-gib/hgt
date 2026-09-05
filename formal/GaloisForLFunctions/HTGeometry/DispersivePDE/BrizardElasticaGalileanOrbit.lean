import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaNLS
import Mathlib.Tactic

/-!
# Galilean orbits of Brizard's explicit NLS families

Equation (26) of arXiv:2607.21750 gives the Galilean gauge symmetry.  In the wave-number
parameterization used by the formalized solitons, a gauge `v` shifts space by `2Dvt` and carries
phase `vx-Dv²t`.  This module proves the field-level group law, norm transport, exact momentum
translation of every plane wave, and exact velocity translation of every envelope soliton.  The
stationary optical soliton is therefore the zero-velocity representative of the full orbit.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

open GaloisForLFunctions.HTGeometry.FDNLS

theorem linearPhase_add (ω₁ ω₂ k₁ k₂ t x : ℝ) :
    linearPhase ω₁ k₁ t x * linearPhase ω₂ k₂ t x =
      linearPhase (ω₁ + ω₂) (k₁ + k₂) t x := by
  simp only [linearPhase, staggerPhase, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem linearPhase_shift (ω k c t x : ℝ) :
    linearPhase ω k t (x - c * t) = linearPhase (ω - k * c) k t x := by
  simp only [linearPhase, staggerPhase, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Field-level Galilean gauge with wave-number parameter `v`. -/
noncomputable def galileanField (D v : ℝ) (u : ℝ → ℝ → ℂ) (t x : ℝ) : ℂ :=
  u t (x - 2 * D * v * t) * linearPhase (-D * v ^ 2) v t x

theorem norm_galileanField (D v : ℝ) (u : ℝ → ℝ → ℂ) (t x : ℝ) :
    ‖galileanField D v u t x‖ = ‖u t (x - 2 * D * v * t)‖ := by
  rw [galileanField, norm_mul, norm_linearPhase, mul_one]

theorem galileanField_zero (D : ℝ) (u : ℝ → ℝ → ℂ) (t x : ℝ) :
    galileanField D 0 u t x = u t x := by
  simp [galileanField, linearPhase, staggerPhase]

/-- Consecutive Galilean gauges compose by addition of wave-number parameters. -/
theorem galileanField_add (D v w : ℝ) (u : ℝ → ℝ → ℂ) (t x : ℝ) :
    galileanField D v (galileanField D w u) t x =
      galileanField D (v + w) u t x := by
  rw [galileanField, galileanField, galileanField]
  have hx : x - 2 * D * v * t - 2 * D * w * t = x - 2 * D * (v + w) * t := by
    ring
  rw [hx, linearPhase_shift, mul_assoc, linearPhase_add]
  congr 2 <;> ring

/-- Galilean gauge translates paper equation (27)'s spatial wave number. -/
theorem galileanField_planeWave (D a k v t x : ℝ) :
    galileanField D v (planeWave D a k) t x = planeWave D a (k + v) t x := by
  rw [galileanField, planeWave, planeWave]
  rw [linearPhase_shift, mul_assoc, linearPhase_add]
  congr 2 <;> ring

/-- Every moving envelope lies in one additive Galilean orbit. -/
theorem galileanField_envelopeSoliton (D k v w t x : ℝ) :
    galileanField D v (envelopeSoliton D k w) t x =
      envelopeSoliton D k (v + w) t x := by
  rw [galileanField, envelopeSoliton, envelopeSoliton]
  have henv : envelope D k w t (x - 2 * D * v * t) =
      envelope D k (v + w) t x := by
    rw [envelope, envelope, envelopeCoordinate, envelopeCoordinate]
    congr 2
    ring
  rw [henv, linearPhase_shift, mul_assoc, linearPhase_add]
  congr 2 <;> ring

/-- Paper's optical soliton generates the complete moving envelope family. -/
theorem galileanField_opticalSoliton (D k v t x : ℝ) :
    galileanField D v (opticalSoliton D k) t x = envelopeSoliton D k v t x := by
  change galileanField D v (envelopeSoliton D k 0) t x = envelopeSoliton D k v t x
  simpa using galileanField_envelopeSoliton D k v 0 t x

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
