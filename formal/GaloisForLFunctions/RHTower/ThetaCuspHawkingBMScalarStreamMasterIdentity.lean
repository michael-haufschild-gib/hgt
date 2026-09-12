import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMScalarStreamEinstein
import GaloisForLFunctions.HTGeometry.InversePowerCancellation

/-!
# The sourced Kodama–Ishibashi master identity for the harmonic scalar stream

For the Kodama–Ishibashi-gauge scalar-stream jet with a harmonic angular profile (`ΔY = μY`) at
time rate `2s`, the ten components of the linearized cosmological Einstein operator reduce to seven
coefficient functions of the radial jets (`harmonicTT`, …, `harmonicL`). The master combination
`masterVar = r(−(r²−1)F1/s + F0/(r²−1) − (r²−1)F2 + 4H)` equals `(2−μ)Φ` on the vacuum
reconstruction, where `Φ` solves `Φ'' + (2r/(r²−1))Φ' + (μ/(r²(r²−1)) − 4s²/(r²−1)²)Φ = 0`, the
tortoise wave equation with potential `μ(r²−1)/r²`. The main theorem is the identity, valid for every
jet, expressing the master operator on `masterVar` as a combination of the Einstein coefficients and
formal derivatives of the mixed and trace-free coefficients; on-shell it is the sourced master
equation. This is row 35 (ii) of route HB at the level of one angular harmonic.
-/

set_option linter.unusedVariables false

namespace RHTower.D4BMScalarStream
open GaloisForLFunctions.HTGeometry CoordinateMetricTwoJet
noncomputable section

/-- Orbit `(t,t)` coefficient (of `Y`) of the cosmological Einstein operator on the harmonic scalar stream. -/
def harmonicTT (s r μ F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 : ℂ) : ℂ :=
  ((((-1 : ℂ) + (-1 / 2 : ℂ) * μ + (7 : ℂ) * r ^ 2 + (1 : ℂ) * r ^ 2 * μ + (-11 : ℂ) * r ^ 4 + (-1 / 2 : ℂ) * r ^ 4 * μ + (5 : ℂ) * r ^ 6) / (r ^ 2)) * F2 + (((-1 : ℂ) + (3 : ℂ) * r ^ 2 + (-3 : ℂ) * r ^ 4 + (1 : ℂ) * r ^ 6) / (r)) * F21 + (((-2 : ℂ) + (1 : ℂ) * μ + (2 : ℂ) * r ^ 2 + (-1 : ℂ) * r ^ 2 * μ) / (r ^ 2)) * H + (((-6 : ℂ) + (14 : ℂ) * r ^ 2 + (-8 : ℂ) * r ^ 4) / (r)) * H1 + ((-2 : ℂ) + (4 : ℂ) * r ^ 2 + (-2 : ℂ) * r ^ 4) * H2)


/-- Orbit `(t,r)` coefficient. -/
def harmonicTR (s r μ F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 : ℂ) : ℂ :=
  ((((-1 / 2 : ℂ) * μ) / (r ^ 2)) * F1 + (((-2 : ℂ) * s + (2 : ℂ) * s * r ^ 2) / (r)) * F2 + (((4 : ℂ) * s) / (r * (r ^ 2 - 1))) * H + ((-4 : ℂ) * s) * H1)


/-- Orbit `(r,r)` coefficient. -/
def harmonicRR (s r μ F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 : ℂ) : ℂ :=
  ((((-1 / 2 : ℂ) * μ + (2 : ℂ) * r ^ 2) / (r ^ 2 * (r ^ 2 - 1) * (1 + r) * (1 - r) * ((-1 : ℂ)))) * F0 + (((-1 : ℂ)) / (r * (r ^ 2 - 1))) * F01 + (((4 : ℂ) * s) / (r * (r ^ 2 - 1))) * F1 + (((1 : ℂ) + (-3 : ℂ) * r ^ 2) / (r ^ 2)) * F2 + (((2 : ℂ) + (-1 : ℂ) * μ + (-2 : ℂ) * r ^ 2 + (1 : ℂ) * r ^ 2 * μ + (-8 : ℂ) * s ^ 2 * r ^ 2) / (r ^ 2 * (r ^ 2 - 1) * (1 + r) * (1 - r) * ((-1 : ℂ)))) * H + (((-2 : ℂ) + (4 : ℂ) * r ^ 2) / (r * (r ^ 2 - 1))) * H1)


/-- Mixed `(t,i)` coefficient (of `∂_i Y`). -/
def harmonicT (s r μ F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 : ℂ) : ℂ :=
  (((1 : ℂ) * r) * F1 + ((-1 / 2 : ℂ) + (1 / 2 : ℂ) * r ^ 2) * F11 + ((1 : ℂ) * s + (-1 : ℂ) * s * r ^ 2) * F2 + ((-2 : ℂ) * s) * H)


/-- Mixed `(r,i)` coefficient (of `∂_i Y`). -/
def harmonicR (s r μ F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 : ℂ) : ℂ :=
  ((((1 / 2 : ℂ) + (-1 : ℂ) * r ^ 2) / (r * (r ^ 2 - 1) * (1 + r) * (1 - r) * ((-1 : ℂ)))) * F0 + (((1 / 2 : ℂ)) / ((r ^ 2 - 1))) * F01 + (((-1 : ℂ) * s) / ((r ^ 2 - 1))) * F1 + (((-1 / 2 : ℂ) + (1 : ℂ) * r ^ 2) / (r)) * F2 + ((-1 : ℂ)) * H1)


/-- Trace-free angular coefficient (of the covariant Hessian of `Y`). -/
def harmonicTF (s r μ F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 : ℂ) : ℂ :=
  ((((1 / 2 : ℂ)) / ((r ^ 2 - 1))) * F0 + ((1 / 2 : ℂ) + (-1 / 2 : ℂ) * r ^ 2) * F2)


/-- Angular trace coefficient (of `Y γ_ij`). -/
def harmonicL (s r μ F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 : ℂ) : ℂ :=
  ((((1 / 4 : ℂ) * μ + (-2 : ℂ) * r ^ 2 + (-1 / 4 : ℂ) * r ^ 2 * μ + (1 : ℂ) * r ^ 4) / ((r ^ 2 - 1) * (1 + r) * (1 - r) * ((-1 : ℂ)))) * F0 + (((1 / 2 : ℂ) * r) / ((r ^ 2 - 1))) * F01 + ((-1 / 2 : ℂ) * r ^ 2) * F02 + (((-2 : ℂ) * s * r + (4 : ℂ) * s * r ^ 3) / ((r ^ 2 - 1))) * F1 + ((2 : ℂ) * s * r ^ 2) * F11 + ((-1 / 4 : ℂ) * μ + (4 : ℂ) * r ^ 2 + (1 / 4 : ℂ) * r ^ 2 * μ + (-5 : ℂ) * r ^ 4 + (-2 : ℂ) * s ^ 2 * r ^ 2) * F2 + ((-1 / 2 : ℂ) * r + (3 / 2 : ℂ) * r ^ 3 + (-1 : ℂ) * r ^ 5) * F21 + (((-4 : ℂ) * s ^ 2 * r ^ 2) / ((r ^ 2 - 1))) * H + ((-2 : ℂ) * r + (4 : ℂ) * r ^ 3) * H1 + ((-1 : ℂ) * r ^ 2 + (1 : ℂ) * r ^ 4) * H2)


/-- Formal radial derivative of the mixed `(t,i)` coefficient. -/
def harmonicT1 (s r μ F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 : ℂ) : ℂ :=
  (((1 : ℂ)) * F1 + ((2 : ℂ) * r) * F11 + ((-1 / 2 : ℂ) + (1 / 2 : ℂ) * r ^ 2) * F12 + ((-2 : ℂ) * s * r) * F2 + ((1 : ℂ) * s + (-1 : ℂ) * s * r ^ 2) * F21 + ((-2 : ℂ) * s) * H1)


/-- Formal radial derivative of the trace-free coefficient. -/
def harmonicTF1 (s r μ F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 : ℂ) : ℂ :=
  ((((-1 : ℂ) * r) / ((r ^ 2 - 1) * (1 + r) * (1 - r) * ((-1 : ℂ)))) * F0 + (((1 / 2 : ℂ)) / ((r ^ 2 - 1))) * F01 + ((-1 : ℂ) * r) * F2 + ((1 / 2 : ℂ) + (-1 / 2 : ℂ) * r ^ 2) * F21)


/-- Formal second radial derivative of the trace-free coefficient. -/
def harmonicTF2 (s r μ F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 : ℂ) : ℂ :=
  ((((1 : ℂ) + (3 : ℂ) * r ^ 2) / ((r ^ 2 - 1) ^ 2 * (1 + r) * (1 - r) * ((-1 : ℂ)))) * F0 + (((-2 : ℂ) * r) / ((r ^ 2 - 1) * (1 + r) * (1 - r) * ((-1 : ℂ)))) * F01 + (((1 / 2 : ℂ)) / ((r ^ 2 - 1))) * F02 + ((-1 : ℂ)) * F2 + ((-2 : ℂ) * r) * F21 + ((1 / 2 : ℂ) + (-1 / 2 : ℂ) * r ^ 2) * F22)


/-- The master combination `r(−(r²−1)F1/s + F0/(r²−1) − (r²−1)F2 + 4H)`, equal to `(2−μ)Φ` on the vacuum reconstruction. -/
def masterVar (s r μ F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 : ℂ) : ℂ :=
  ((((1 : ℂ) * r) / ((r ^ 2 - 1))) * F0 + (((1 : ℂ) + (-1 : ℂ) * r ^ 2) / (s)) * F1 + ((1 : ℂ) * r + (-1 : ℂ) * r ^ 3) * F2 + ((4 : ℂ) * r) * H)


/-- Its formal radial derivative. -/
def masterVar1 (s r μ F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 : ℂ) : ℂ :=
  ((((-1 : ℂ) + (-1 : ℂ) * r ^ 2) / ((r ^ 2 - 1) * (1 + r) * (1 - r) * ((-1 : ℂ)))) * F0 + (((1 : ℂ) * r) / ((r ^ 2 - 1))) * F01 + (((-2 : ℂ) * r) / (s)) * F1 + (((1 : ℂ) + (-1 : ℂ) * r ^ 2) / (s)) * F11 + ((1 : ℂ) + (-3 : ℂ) * r ^ 2) * F2 + ((1 : ℂ) * r + (-1 : ℂ) * r ^ 3) * F21 + ((4 : ℂ)) * H + ((4 : ℂ) * r) * H1)


/-- Its formal second radial derivative. -/
def masterVar2 (s r μ F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 : ℂ) : ℂ :=
  ((((6 : ℂ) * r + (2 : ℂ) * r ^ 3) / ((r ^ 2 - 1) ^ 2 * (1 + r) * (1 - r) * ((-1 : ℂ)))) * F0 + (((-2 : ℂ) + (-2 : ℂ) * r ^ 2) / ((r ^ 2 - 1) * (1 + r) * (1 - r) * ((-1 : ℂ)))) * F01 + (((1 : ℂ) * r) / ((r ^ 2 - 1))) * F02 + (((-2 : ℂ)) / (s)) * F1 + (((-4 : ℂ) * r) / (s)) * F11 + (((1 : ℂ) + (-1 : ℂ) * r ^ 2) / (s)) * F12 + ((-6 : ℂ) * r) * F2 + ((2 : ℂ) + (-6 : ℂ) * r ^ 2) * F21 + ((1 : ℂ) * r + (-1 : ℂ) * r ^ 3) * F22 + ((8 : ℂ)) * H1 + ((4 : ℂ) * r) * H2)


private theorem coef_F0 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    (((6 : ℂ) * r + (2 : ℂ) * r ^ 3) / ((r ^ 2 - 1) ^ 2 * (1 + r) * (1 - r) * ((-1 : ℂ)))) + (((2 : ℂ) * r) / ((r ^ 2 - 1))) * (((-1 : ℂ) + (-1 : ℂ) * r ^ 2) / ((r ^ 2 - 1) * (1 + r) * (1 - r) * ((-1 : ℂ)))) + (((-1 : ℂ) * μ + (1 : ℂ) * r ^ 2 * μ + (-4 : ℂ) * s ^ 2 * r ^ 2) / (r ^ 2 * (r ^ 2 - 1) * (1 + r) * (1 - r) * ((-1 : ℂ)))) * (((1 : ℂ) * r) / ((r ^ 2 - 1))) =
      (((-2 : ℂ) * r) / ((r ^ 2 - 1) * (1 + r) * (1 - r) * ((-1 : ℂ)))) * (0 : ℂ) + (((2 : ℂ)) / (s)) * (0 : ℂ) + ((2 : ℂ) * r) * (((-1 / 2 : ℂ) * μ + (2 : ℂ) * r ^ 2) / (r ^ 2 * (r ^ 2 - 1) * (1 + r) * (1 - r) * ((-1 : ℂ)))) + (((-4 : ℂ) * r) / (s * (r ^ 2 - 1))) * (0 : ℂ) + ((4 : ℂ)) * (((1 / 2 : ℂ) + (-1 : ℂ) * r ^ 2) / (r * (r ^ 2 - 1) * (1 + r) * (1 - r) * ((-1 : ℂ)))) + (((4 : ℂ) + (-4 : ℂ) * μ + (-8 : ℂ) * r ^ 2 + (4 : ℂ) * r ^ 2 * μ + (4 : ℂ) * r ^ 4 + (-8 : ℂ) * s ^ 2 * r ^ 2) / (r * (r ^ 2 - 1) * (1 + r) * (1 - r) * ((-1 : ℂ)))) * (((1 / 2 : ℂ)) / ((r ^ 2 - 1))) + (((-2 : ℂ)) / (s)) * (0 : ℂ) + (((-4 : ℂ) + (8 : ℂ) * r ^ 2) / ((r ^ 2 - 1))) * (((-1 : ℂ) * r) / ((r ^ 2 - 1) * (1 + r) * (1 - r) * ((-1 : ℂ)))) + ((2 : ℂ) * r) * (((1 : ℂ) + (3 : ℂ) * r ^ 2) / ((r ^ 2 - 1) ^ 2 * (1 + r) * (1 - r) * ((-1 : ℂ)))) := by
  have hf' : (1 : ℂ) - r ^ 2 ≠ 0 := by rwa [show (1 : ℂ) - r ^ 2 = -(r ^ 2 - 1) by ring, neg_ne_zero]
  have hf2 : (r ^ 2 - 1) ^ 2 ≠ 0 := pow_ne_zero 2 hf
  field_simp
  ring

private theorem coef_F01 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    (((-2 : ℂ) + (-2 : ℂ) * r ^ 2) / ((r ^ 2 - 1) * (1 + r) * (1 - r) * ((-1 : ℂ)))) + (((2 : ℂ) * r) / ((r ^ 2 - 1))) * (((1 : ℂ) * r) / ((r ^ 2 - 1))) + (((-1 : ℂ) * μ + (1 : ℂ) * r ^ 2 * μ + (-4 : ℂ) * s ^ 2 * r ^ 2) / (r ^ 2 * (r ^ 2 - 1) * (1 + r) * (1 - r) * ((-1 : ℂ)))) * (0 : ℂ) =
      (((-2 : ℂ) * r) / ((r ^ 2 - 1) * (1 + r) * (1 - r) * ((-1 : ℂ)))) * (0 : ℂ) + (((2 : ℂ)) / (s)) * (0 : ℂ) + ((2 : ℂ) * r) * (((-1 : ℂ)) / (r * (r ^ 2 - 1))) + (((-4 : ℂ) * r) / (s * (r ^ 2 - 1))) * (0 : ℂ) + ((4 : ℂ)) * (((1 / 2 : ℂ)) / ((r ^ 2 - 1))) + (((4 : ℂ) + (-4 : ℂ) * μ + (-8 : ℂ) * r ^ 2 + (4 : ℂ) * r ^ 2 * μ + (4 : ℂ) * r ^ 4 + (-8 : ℂ) * s ^ 2 * r ^ 2) / (r * (r ^ 2 - 1) * (1 + r) * (1 - r) * ((-1 : ℂ)))) * (0 : ℂ) + (((-2 : ℂ)) / (s)) * (0 : ℂ) + (((-4 : ℂ) + (8 : ℂ) * r ^ 2) / ((r ^ 2 - 1))) * (((1 / 2 : ℂ)) / ((r ^ 2 - 1))) + ((2 : ℂ) * r) * (((-2 : ℂ) * r) / ((r ^ 2 - 1) * (1 + r) * (1 - r) * ((-1 : ℂ)))) := by
  have hf' : (1 : ℂ) - r ^ 2 ≠ 0 := by rwa [show (1 : ℂ) - r ^ 2 = -(r ^ 2 - 1) by ring, neg_ne_zero]
  have hf2 : (r ^ 2 - 1) ^ 2 ≠ 0 := pow_ne_zero 2 hf
  field_simp
  ring

private theorem coef_F02 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    (((1 : ℂ) * r) / ((r ^ 2 - 1))) + (((2 : ℂ) * r) / ((r ^ 2 - 1))) * (0 : ℂ) + (((-1 : ℂ) * μ + (1 : ℂ) * r ^ 2 * μ + (-4 : ℂ) * s ^ 2 * r ^ 2) / (r ^ 2 * (r ^ 2 - 1) * (1 + r) * (1 - r) * ((-1 : ℂ)))) * (0 : ℂ) =
      (((-2 : ℂ) * r) / ((r ^ 2 - 1) * (1 + r) * (1 - r) * ((-1 : ℂ)))) * (0 : ℂ) + (((2 : ℂ)) / (s)) * (0 : ℂ) + ((2 : ℂ) * r) * (0 : ℂ) + (((-4 : ℂ) * r) / (s * (r ^ 2 - 1))) * (0 : ℂ) + ((4 : ℂ)) * (0 : ℂ) + (((4 : ℂ) + (-4 : ℂ) * μ + (-8 : ℂ) * r ^ 2 + (4 : ℂ) * r ^ 2 * μ + (4 : ℂ) * r ^ 4 + (-8 : ℂ) * s ^ 2 * r ^ 2) / (r * (r ^ 2 - 1) * (1 + r) * (1 - r) * ((-1 : ℂ)))) * (0 : ℂ) + (((-2 : ℂ)) / (s)) * (0 : ℂ) + (((-4 : ℂ) + (8 : ℂ) * r ^ 2) / ((r ^ 2 - 1))) * (0 : ℂ) + ((2 : ℂ) * r) * (((1 / 2 : ℂ)) / ((r ^ 2 - 1))) := by
  have hf' : (1 : ℂ) - r ^ 2 ≠ 0 := by rwa [show (1 : ℂ) - r ^ 2 = -(r ^ 2 - 1) by ring, neg_ne_zero]
  have hf2 : (r ^ 2 - 1) ^ 2 ≠ 0 := pow_ne_zero 2 hf
  field_simp
  ring

private theorem coef_F1 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    (((-2 : ℂ)) / (s)) + (((2 : ℂ) * r) / ((r ^ 2 - 1))) * (((-2 : ℂ) * r) / (s)) + (((-1 : ℂ) * μ + (1 : ℂ) * r ^ 2 * μ + (-4 : ℂ) * s ^ 2 * r ^ 2) / (r ^ 2 * (r ^ 2 - 1) * (1 + r) * (1 - r) * ((-1 : ℂ)))) * (((1 : ℂ) + (-1 : ℂ) * r ^ 2) / (s)) =
      (((-2 : ℂ) * r) / ((r ^ 2 - 1) * (1 + r) * (1 - r) * ((-1 : ℂ)))) * (0 : ℂ) + (((2 : ℂ)) / (s)) * (((-1 / 2 : ℂ) * μ) / (r ^ 2)) + ((2 : ℂ) * r) * (((4 : ℂ) * s) / (r * (r ^ 2 - 1))) + (((-4 : ℂ) * r) / (s * (r ^ 2 - 1))) * ((1 : ℂ) * r) + ((4 : ℂ)) * (((-1 : ℂ) * s) / ((r ^ 2 - 1))) + (((4 : ℂ) + (-4 : ℂ) * μ + (-8 : ℂ) * r ^ 2 + (4 : ℂ) * r ^ 2 * μ + (4 : ℂ) * r ^ 4 + (-8 : ℂ) * s ^ 2 * r ^ 2) / (r * (r ^ 2 - 1) * (1 + r) * (1 - r) * ((-1 : ℂ)))) * (0 : ℂ) + (((-2 : ℂ)) / (s)) * ((1 : ℂ)) + (((-4 : ℂ) + (8 : ℂ) * r ^ 2) / ((r ^ 2 - 1))) * (0 : ℂ) + ((2 : ℂ) * r) * (0 : ℂ) := by
  have hf' : (1 : ℂ) - r ^ 2 ≠ 0 := by rwa [show (1 : ℂ) - r ^ 2 = -(r ^ 2 - 1) by ring, neg_ne_zero]
  have hf2 : (r ^ 2 - 1) ^ 2 ≠ 0 := pow_ne_zero 2 hf
  field_simp
  ring

private theorem coef_F11 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    (((-4 : ℂ) * r) / (s)) + (((2 : ℂ) * r) / ((r ^ 2 - 1))) * (((1 : ℂ) + (-1 : ℂ) * r ^ 2) / (s)) + (((-1 : ℂ) * μ + (1 : ℂ) * r ^ 2 * μ + (-4 : ℂ) * s ^ 2 * r ^ 2) / (r ^ 2 * (r ^ 2 - 1) * (1 + r) * (1 - r) * ((-1 : ℂ)))) * (0 : ℂ) =
      (((-2 : ℂ) * r) / ((r ^ 2 - 1) * (1 + r) * (1 - r) * ((-1 : ℂ)))) * (0 : ℂ) + (((2 : ℂ)) / (s)) * (0 : ℂ) + ((2 : ℂ) * r) * (0 : ℂ) + (((-4 : ℂ) * r) / (s * (r ^ 2 - 1))) * ((-1 / 2 : ℂ) + (1 / 2 : ℂ) * r ^ 2) + ((4 : ℂ)) * (0 : ℂ) + (((4 : ℂ) + (-4 : ℂ) * μ + (-8 : ℂ) * r ^ 2 + (4 : ℂ) * r ^ 2 * μ + (4 : ℂ) * r ^ 4 + (-8 : ℂ) * s ^ 2 * r ^ 2) / (r * (r ^ 2 - 1) * (1 + r) * (1 - r) * ((-1 : ℂ)))) * (0 : ℂ) + (((-2 : ℂ)) / (s)) * ((2 : ℂ) * r) + (((-4 : ℂ) + (8 : ℂ) * r ^ 2) / ((r ^ 2 - 1))) * (0 : ℂ) + ((2 : ℂ) * r) * (0 : ℂ) := by
  have hf' : (1 : ℂ) - r ^ 2 ≠ 0 := by rwa [show (1 : ℂ) - r ^ 2 = -(r ^ 2 - 1) by ring, neg_ne_zero]
  have hf2 : (r ^ 2 - 1) ^ 2 ≠ 0 := pow_ne_zero 2 hf
  field_simp
  ring

private theorem coef_F12 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    (((1 : ℂ) + (-1 : ℂ) * r ^ 2) / (s)) + (((2 : ℂ) * r) / ((r ^ 2 - 1))) * (0 : ℂ) + (((-1 : ℂ) * μ + (1 : ℂ) * r ^ 2 * μ + (-4 : ℂ) * s ^ 2 * r ^ 2) / (r ^ 2 * (r ^ 2 - 1) * (1 + r) * (1 - r) * ((-1 : ℂ)))) * (0 : ℂ) =
      (((-2 : ℂ) * r) / ((r ^ 2 - 1) * (1 + r) * (1 - r) * ((-1 : ℂ)))) * (0 : ℂ) + (((2 : ℂ)) / (s)) * (0 : ℂ) + ((2 : ℂ) * r) * (0 : ℂ) + (((-4 : ℂ) * r) / (s * (r ^ 2 - 1))) * (0 : ℂ) + ((4 : ℂ)) * (0 : ℂ) + (((4 : ℂ) + (-4 : ℂ) * μ + (-8 : ℂ) * r ^ 2 + (4 : ℂ) * r ^ 2 * μ + (4 : ℂ) * r ^ 4 + (-8 : ℂ) * s ^ 2 * r ^ 2) / (r * (r ^ 2 - 1) * (1 + r) * (1 - r) * ((-1 : ℂ)))) * (0 : ℂ) + (((-2 : ℂ)) / (s)) * ((-1 / 2 : ℂ) + (1 / 2 : ℂ) * r ^ 2) + (((-4 : ℂ) + (8 : ℂ) * r ^ 2) / ((r ^ 2 - 1))) * (0 : ℂ) + ((2 : ℂ) * r) * (0 : ℂ) := by
  have hf' : (1 : ℂ) - r ^ 2 ≠ 0 := by rwa [show (1 : ℂ) - r ^ 2 = -(r ^ 2 - 1) by ring, neg_ne_zero]
  have hf2 : (r ^ 2 - 1) ^ 2 ≠ 0 := pow_ne_zero 2 hf
  field_simp
  ring

private theorem coef_F2 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    ((-6 : ℂ) * r) + (((2 : ℂ) * r) / ((r ^ 2 - 1))) * ((1 : ℂ) + (-3 : ℂ) * r ^ 2) + (((-1 : ℂ) * μ + (1 : ℂ) * r ^ 2 * μ + (-4 : ℂ) * s ^ 2 * r ^ 2) / (r ^ 2 * (r ^ 2 - 1) * (1 + r) * (1 - r) * ((-1 : ℂ)))) * ((1 : ℂ) * r + (-1 : ℂ) * r ^ 3) =
      (((-2 : ℂ) * r) / ((r ^ 2 - 1) * (1 + r) * (1 - r) * ((-1 : ℂ)))) * (((-1 : ℂ) + (-1 / 2 : ℂ) * μ + (7 : ℂ) * r ^ 2 + (1 : ℂ) * r ^ 2 * μ + (-11 : ℂ) * r ^ 4 + (-1 / 2 : ℂ) * r ^ 4 * μ + (5 : ℂ) * r ^ 6) / (r ^ 2)) + (((2 : ℂ)) / (s)) * (((-2 : ℂ) * s + (2 : ℂ) * s * r ^ 2) / (r)) + ((2 : ℂ) * r) * (((1 : ℂ) + (-3 : ℂ) * r ^ 2) / (r ^ 2)) + (((-4 : ℂ) * r) / (s * (r ^ 2 - 1))) * ((1 : ℂ) * s + (-1 : ℂ) * s * r ^ 2) + ((4 : ℂ)) * (((-1 / 2 : ℂ) + (1 : ℂ) * r ^ 2) / (r)) + (((4 : ℂ) + (-4 : ℂ) * μ + (-8 : ℂ) * r ^ 2 + (4 : ℂ) * r ^ 2 * μ + (4 : ℂ) * r ^ 4 + (-8 : ℂ) * s ^ 2 * r ^ 2) / (r * (r ^ 2 - 1) * (1 + r) * (1 - r) * ((-1 : ℂ)))) * ((1 / 2 : ℂ) + (-1 / 2 : ℂ) * r ^ 2) + (((-2 : ℂ)) / (s)) * ((-2 : ℂ) * s * r) + (((-4 : ℂ) + (8 : ℂ) * r ^ 2) / ((r ^ 2 - 1))) * ((-1 : ℂ) * r) + ((2 : ℂ) * r) * ((-1 : ℂ)) := by
  have hf' : (1 : ℂ) - r ^ 2 ≠ 0 := by rwa [show (1 : ℂ) - r ^ 2 = -(r ^ 2 - 1) by ring, neg_ne_zero]
  have hf2 : (r ^ 2 - 1) ^ 2 ≠ 0 := pow_ne_zero 2 hf
  field_simp
  ring

private theorem coef_F21 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    ((2 : ℂ) + (-6 : ℂ) * r ^ 2) + (((2 : ℂ) * r) / ((r ^ 2 - 1))) * ((1 : ℂ) * r + (-1 : ℂ) * r ^ 3) + (((-1 : ℂ) * μ + (1 : ℂ) * r ^ 2 * μ + (-4 : ℂ) * s ^ 2 * r ^ 2) / (r ^ 2 * (r ^ 2 - 1) * (1 + r) * (1 - r) * ((-1 : ℂ)))) * (0 : ℂ) =
      (((-2 : ℂ) * r) / ((r ^ 2 - 1) * (1 + r) * (1 - r) * ((-1 : ℂ)))) * (((-1 : ℂ) + (3 : ℂ) * r ^ 2 + (-3 : ℂ) * r ^ 4 + (1 : ℂ) * r ^ 6) / (r)) + (((2 : ℂ)) / (s)) * (0 : ℂ) + ((2 : ℂ) * r) * (0 : ℂ) + (((-4 : ℂ) * r) / (s * (r ^ 2 - 1))) * (0 : ℂ) + ((4 : ℂ)) * (0 : ℂ) + (((4 : ℂ) + (-4 : ℂ) * μ + (-8 : ℂ) * r ^ 2 + (4 : ℂ) * r ^ 2 * μ + (4 : ℂ) * r ^ 4 + (-8 : ℂ) * s ^ 2 * r ^ 2) / (r * (r ^ 2 - 1) * (1 + r) * (1 - r) * ((-1 : ℂ)))) * (0 : ℂ) + (((-2 : ℂ)) / (s)) * ((1 : ℂ) * s + (-1 : ℂ) * s * r ^ 2) + (((-4 : ℂ) + (8 : ℂ) * r ^ 2) / ((r ^ 2 - 1))) * ((1 / 2 : ℂ) + (-1 / 2 : ℂ) * r ^ 2) + ((2 : ℂ) * r) * ((-2 : ℂ) * r) := by
  have hf' : (1 : ℂ) - r ^ 2 ≠ 0 := by rwa [show (1 : ℂ) - r ^ 2 = -(r ^ 2 - 1) by ring, neg_ne_zero]
  have hf2 : (r ^ 2 - 1) ^ 2 ≠ 0 := pow_ne_zero 2 hf
  field_simp
  ring

private theorem coef_F22 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    ((1 : ℂ) * r + (-1 : ℂ) * r ^ 3) + (((2 : ℂ) * r) / ((r ^ 2 - 1))) * (0 : ℂ) + (((-1 : ℂ) * μ + (1 : ℂ) * r ^ 2 * μ + (-4 : ℂ) * s ^ 2 * r ^ 2) / (r ^ 2 * (r ^ 2 - 1) * (1 + r) * (1 - r) * ((-1 : ℂ)))) * (0 : ℂ) =
      (((-2 : ℂ) * r) / ((r ^ 2 - 1) * (1 + r) * (1 - r) * ((-1 : ℂ)))) * (0 : ℂ) + (((2 : ℂ)) / (s)) * (0 : ℂ) + ((2 : ℂ) * r) * (0 : ℂ) + (((-4 : ℂ) * r) / (s * (r ^ 2 - 1))) * (0 : ℂ) + ((4 : ℂ)) * (0 : ℂ) + (((4 : ℂ) + (-4 : ℂ) * μ + (-8 : ℂ) * r ^ 2 + (4 : ℂ) * r ^ 2 * μ + (4 : ℂ) * r ^ 4 + (-8 : ℂ) * s ^ 2 * r ^ 2) / (r * (r ^ 2 - 1) * (1 + r) * (1 - r) * ((-1 : ℂ)))) * (0 : ℂ) + (((-2 : ℂ)) / (s)) * (0 : ℂ) + (((-4 : ℂ) + (8 : ℂ) * r ^ 2) / ((r ^ 2 - 1))) * (0 : ℂ) + ((2 : ℂ) * r) * ((1 / 2 : ℂ) + (-1 / 2 : ℂ) * r ^ 2) := by
  have hf' : (1 : ℂ) - r ^ 2 ≠ 0 := by rwa [show (1 : ℂ) - r ^ 2 = -(r ^ 2 - 1) by ring, neg_ne_zero]
  have hf2 : (r ^ 2 - 1) ^ 2 ≠ 0 := pow_ne_zero 2 hf
  field_simp
  ring

private theorem coef_H (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    (0 : ℂ) + (((2 : ℂ) * r) / ((r ^ 2 - 1))) * ((4 : ℂ)) + (((-1 : ℂ) * μ + (1 : ℂ) * r ^ 2 * μ + (-4 : ℂ) * s ^ 2 * r ^ 2) / (r ^ 2 * (r ^ 2 - 1) * (1 + r) * (1 - r) * ((-1 : ℂ)))) * ((4 : ℂ) * r) =
      (((-2 : ℂ) * r) / ((r ^ 2 - 1) * (1 + r) * (1 - r) * ((-1 : ℂ)))) * (((-2 : ℂ) + (1 : ℂ) * μ + (2 : ℂ) * r ^ 2 + (-1 : ℂ) * r ^ 2 * μ) / (r ^ 2)) + (((2 : ℂ)) / (s)) * (((4 : ℂ) * s) / (r * (r ^ 2 - 1))) + ((2 : ℂ) * r) * (((2 : ℂ) + (-1 : ℂ) * μ + (-2 : ℂ) * r ^ 2 + (1 : ℂ) * r ^ 2 * μ + (-8 : ℂ) * s ^ 2 * r ^ 2) / (r ^ 2 * (r ^ 2 - 1) * (1 + r) * (1 - r) * ((-1 : ℂ)))) + (((-4 : ℂ) * r) / (s * (r ^ 2 - 1))) * ((-2 : ℂ) * s) + ((4 : ℂ)) * (0 : ℂ) + (((4 : ℂ) + (-4 : ℂ) * μ + (-8 : ℂ) * r ^ 2 + (4 : ℂ) * r ^ 2 * μ + (4 : ℂ) * r ^ 4 + (-8 : ℂ) * s ^ 2 * r ^ 2) / (r * (r ^ 2 - 1) * (1 + r) * (1 - r) * ((-1 : ℂ)))) * (0 : ℂ) + (((-2 : ℂ)) / (s)) * (0 : ℂ) + (((-4 : ℂ) + (8 : ℂ) * r ^ 2) / ((r ^ 2 - 1))) * (0 : ℂ) + ((2 : ℂ) * r) * (0 : ℂ) := by
  have hf' : (1 : ℂ) - r ^ 2 ≠ 0 := by rwa [show (1 : ℂ) - r ^ 2 = -(r ^ 2 - 1) by ring, neg_ne_zero]
  have hf2 : (r ^ 2 - 1) ^ 2 ≠ 0 := pow_ne_zero 2 hf
  field_simp
  ring

private theorem coef_H1 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    ((8 : ℂ)) + (((2 : ℂ) * r) / ((r ^ 2 - 1))) * ((4 : ℂ) * r) + (((-1 : ℂ) * μ + (1 : ℂ) * r ^ 2 * μ + (-4 : ℂ) * s ^ 2 * r ^ 2) / (r ^ 2 * (r ^ 2 - 1) * (1 + r) * (1 - r) * ((-1 : ℂ)))) * (0 : ℂ) =
      (((-2 : ℂ) * r) / ((r ^ 2 - 1) * (1 + r) * (1 - r) * ((-1 : ℂ)))) * (((-6 : ℂ) + (14 : ℂ) * r ^ 2 + (-8 : ℂ) * r ^ 4) / (r)) + (((2 : ℂ)) / (s)) * ((-4 : ℂ) * s) + ((2 : ℂ) * r) * (((-2 : ℂ) + (4 : ℂ) * r ^ 2) / (r * (r ^ 2 - 1))) + (((-4 : ℂ) * r) / (s * (r ^ 2 - 1))) * (0 : ℂ) + ((4 : ℂ)) * ((-1 : ℂ)) + (((4 : ℂ) + (-4 : ℂ) * μ + (-8 : ℂ) * r ^ 2 + (4 : ℂ) * r ^ 2 * μ + (4 : ℂ) * r ^ 4 + (-8 : ℂ) * s ^ 2 * r ^ 2) / (r * (r ^ 2 - 1) * (1 + r) * (1 - r) * ((-1 : ℂ)))) * (0 : ℂ) + (((-2 : ℂ)) / (s)) * ((-2 : ℂ) * s) + (((-4 : ℂ) + (8 : ℂ) * r ^ 2) / ((r ^ 2 - 1))) * (0 : ℂ) + ((2 : ℂ) * r) * (0 : ℂ) := by
  have hf' : (1 : ℂ) - r ^ 2 ≠ 0 := by rwa [show (1 : ℂ) - r ^ 2 = -(r ^ 2 - 1) by ring, neg_ne_zero]
  have hf2 : (r ^ 2 - 1) ^ 2 ≠ 0 := pow_ne_zero 2 hf
  field_simp
  ring

private theorem coef_H2 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    ((4 : ℂ) * r) + (((2 : ℂ) * r) / ((r ^ 2 - 1))) * (0 : ℂ) + (((-1 : ℂ) * μ + (1 : ℂ) * r ^ 2 * μ + (-4 : ℂ) * s ^ 2 * r ^ 2) / (r ^ 2 * (r ^ 2 - 1) * (1 + r) * (1 - r) * ((-1 : ℂ)))) * (0 : ℂ) =
      (((-2 : ℂ) * r) / ((r ^ 2 - 1) * (1 + r) * (1 - r) * ((-1 : ℂ)))) * ((-2 : ℂ) + (4 : ℂ) * r ^ 2 + (-2 : ℂ) * r ^ 4) + (((2 : ℂ)) / (s)) * (0 : ℂ) + ((2 : ℂ) * r) * (0 : ℂ) + (((-4 : ℂ) * r) / (s * (r ^ 2 - 1))) * (0 : ℂ) + ((4 : ℂ)) * (0 : ℂ) + (((4 : ℂ) + (-4 : ℂ) * μ + (-8 : ℂ) * r ^ 2 + (4 : ℂ) * r ^ 2 * μ + (4 : ℂ) * r ^ 4 + (-8 : ℂ) * s ^ 2 * r ^ 2) / (r * (r ^ 2 - 1) * (1 + r) * (1 - r) * ((-1 : ℂ)))) * (0 : ℂ) + (((-2 : ℂ)) / (s)) * (0 : ℂ) + (((-4 : ℂ) + (8 : ℂ) * r ^ 2) / ((r ^ 2 - 1))) * (0 : ℂ) + ((2 : ℂ) * r) * (0 : ℂ) := by
  have hf' : (1 : ℂ) - r ^ 2 ≠ 0 := by rwa [show (1 : ℂ) - r ^ 2 = -(r ^ 2 - 1) by ring, neg_ne_zero]
  have hf2 : (r ^ 2 - 1) ^ 2 ≠ 0 := pow_ne_zero 2 hf
  field_simp
  ring

/-- The master operator `Φ'' + (2r/(r²−1))Φ' + (μ/(r²(r²−1)) − 4s²/(r²−1)²)Φ` on the master
combination. -/
def masterOp (s r μ F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 : ℂ) : ℂ :=
  masterVar2 s r μ F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 + (2 * r / (r ^ 2 - 1)) * masterVar1 s r μ F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 +
    (μ / (r ^ 2 * (r ^ 2 - 1)) - 4 * s ^ 2 / (r ^ 2 - 1) ^ 2) * masterVar s r μ F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2

/-- **Sourced Kodama–Ishibashi master identity on the Birmingham–Mokhtari background.** For every
jet of the harmonic scalar stream (rate `2s`, angular eigenvalue `μ`), the master operator applied
to the master combination equals an explicit combination of the seven Einstein coefficients and the
formal derivatives of the mixed and trace-free ones. On a solution of the sourced equations
`E_A = −τ_A` this is the sourced master equation, with master source
`Σ b_A τ_A − (2/s) τ_t' + ((8r²−4)/(r²−1)) τ_T' + 2r τ_T''`. -/
theorem master_identity (s r μ F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    masterOp s r μ F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 =
      (((-2 : ℂ) * r) / ((r ^ 2 - 1) * (1 + r) * (1 - r) * ((-1 : ℂ)))) * harmonicTT s r μ F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 +
      (((2 : ℂ)) / (s)) * harmonicTR s r μ F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 +
      ((2 : ℂ) * r) * harmonicRR s r μ F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 +
      (((-4 : ℂ) * r) / (s * (r ^ 2 - 1))) * harmonicT s r μ F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 +
      ((4 : ℂ)) * harmonicR s r μ F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 +
      (((4 : ℂ) + (-4 : ℂ) * μ + (-8 : ℂ) * r ^ 2 + (4 : ℂ) * r ^ 2 * μ + (4 : ℂ) * r ^ 4 + (-8 : ℂ) * s ^ 2 * r ^ 2) / (r * (r ^ 2 - 1) * (1 + r) * (1 - r) * ((-1 : ℂ)))) * harmonicTF s r μ F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 +
      (((-2 : ℂ)) / (s)) * harmonicT1 s r μ F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 +
      (((-4 : ℂ) + (8 : ℂ) * r ^ 2) / ((r ^ 2 - 1))) * harmonicTF1 s r μ F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 +
      ((2 : ℂ) * r) * harmonicTF2 s r μ F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 := by
  unfold masterOp masterVar masterVar1 masterVar2 harmonicTT harmonicTR harmonicRR harmonicT
    harmonicR harmonicTF harmonicT1 harmonicTF1 harmonicTF2
  linear_combination F0 * coef_F0 s r μ hs hr hf + F01 * coef_F01 s r μ hs hr hf + F02 * coef_F02 s r μ hs hr hf + F1 * coef_F1 s r μ hs hr hf + F11 * coef_F11 s r μ hs hr hf + F12 * coef_F12 s r μ hs hr hf + F2 * coef_F2 s r μ hs hr hf + F21 * coef_F21 s r μ hs hr hf + F22 * coef_F22 s r μ hs hr hf + H * coef_H s r μ hs hr hf + H1 * coef_H1 s r μ hs hr hf + H2 * coef_H2 s r μ hs hr hf

end
end RHTower.D4BMScalarStream
