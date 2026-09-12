import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMScalarStreamReconstructionJet

/-!
# Harmonic coefficients of the scalar–scalar quadratic source and their Bianchi identities

The scalar–scalar quadratic Einstein source of the fundamental mode (time rate `s`, envelope `B`
with `B' = sB/(r(r²−1))`, angular eigenvalue `λ = (s+1)(s+2)`), projected on one angular harmonic
`ΔY = μY`, has the seven harmonic coefficients `ssSourceTT, …, ssSourceL` (per `B²`): the images
`S² ↦ Y`, `|∇S|² ↦ (μ/2 − λ)Y`, `S∂S ↦ ½∂Y`, `[∇∇S² − ∇S⊗∇S]^{tf} ↦ (1 − λ/(μ−2))·tfHess Y`.
The envelope makes the radial derivative of a coefficient the twisted derivative
`D = ∂_r + 2s/(r(r²−1))`; the first twisted derivatives needed below are given explicitly. The
three theorems `ssSource_bianchiT/R/Ang` are the harmonic contracted Bianchi identities of the
source (its conservation), and `ssSource_masterSource` identifies the master source of the sourced
Kodama–Ishibashi master equation. Everything is a closed rational identity.
-/

set_option linter.unusedVariables false

namespace RHTower.D4BMScalarStream
open GaloisForLFunctions.HTGeometry CoordinateMetricTwoJet
noncomputable section

/-- Harmonic `tt` coefficient of the scalar–scalar source (per `B²`). -/
def ssSourceTT (s r μ : ℂ) : ℂ :=
  (((-1 / 4 : ℂ) * r ^ 4 * μ + (1 / 4 : ℂ) * r ^ 6 * μ + (-1 / 2 : ℂ) * s * r ^ 2 + (-1 / 4 : ℂ) * s * r ^ 2 * μ + (-1 : ℂ) * s * r ^ 4 + (1 / 4 : ℂ) * s * r ^ 4 * μ + (3 / 2 : ℂ) * s * r ^ 6 + (9 / 8 : ℂ) * s ^ 2 + (-3 / 32 : ℂ) * s ^ 2 * μ + (-31 / 8 : ℂ) * s ^ 2 * r ^ 2 + (-1 / 32 : ℂ) * s ^ 2 * r ^ 2 * μ + (5 : ℂ) * s ^ 2 * r ^ 4 + (1 / 8 : ℂ) * s ^ 2 * r ^ 4 * μ + (-1 / 4 : ℂ) * s ^ 2 * r ^ 6 + (57 / 16 : ℂ) * s ^ 3 + (-3 / 16 : ℂ) * s ^ 3 * μ + (-113 / 16 : ℂ) * s ^ 3 * r ^ 2 + (3 / 16 : ℂ) * s ^ 3 * r ^ 2 * μ + (1 / 4 : ℂ) * s ^ 3 * r ^ 4 + (33 / 8 : ℂ) * s ^ 4 + (-3 / 32 : ℂ) * s ^ 4 * μ + (-17 / 4 : ℂ) * s ^ 4 * r ^ 2 + (3 / 32 : ℂ) * s ^ 4 * r ^ 2 * μ + (1 / 2 : ℂ) * s ^ 4 * r ^ 4 + (33 / 16 : ℂ) * s ^ 5 + (-25 / 16 : ℂ) * s ^ 5 * r ^ 2 + (3 / 8 : ℂ) * s ^ 6) / (r ^ 6))

/-- Harmonic `tr` coefficient of the scalar–scalar source (per `B²`). -/
def ssSourceTR (s r μ : ℂ) : ℂ :=
  (((-1 : ℂ) * s ^ 2 * r ^ 2 + (3 : ℂ) * s ^ 2 * r ^ 4 + (3 / 4 : ℂ) * s ^ 3 + (-7 / 2 : ℂ) * s ^ 3 * r ^ 2 + (-1 / 2 : ℂ) * s ^ 3 * r ^ 4 + (15 / 8 : ℂ) * s ^ 4 + (-3 / 2 : ℂ) * s ^ 4 * r ^ 2 + (3 / 2 : ℂ) * s ^ 5 + (-1 : ℂ) * s ^ 5 * r ^ 2 + (3 / 8 : ℂ) * s ^ 6) / (r ^ 5 * (r ^ 2 - 1)))

/-- Harmonic `rr` coefficient of the scalar–scalar source (per `B²`). -/
def ssSourceRR (s r μ : ℂ) : ℂ :=
  (((1 / 4 : ℂ) * r ^ 4 * μ + (-1 / 4 : ℂ) * r ^ 6 * μ + (1 / 2 : ℂ) * s * r ^ 2 + (1 / 4 : ℂ) * s * r ^ 2 * μ + (1 : ℂ) * s * r ^ 4 + (-1 / 4 : ℂ) * s * r ^ 4 * μ + (-3 / 2 : ℂ) * s * r ^ 6 + (7 / 8 : ℂ) * s ^ 2 + (3 / 32 : ℂ) * s ^ 2 * μ + (-21 / 8 : ℂ) * s ^ 2 * r ^ 2 + (1 / 32 : ℂ) * s ^ 2 * r ^ 2 * μ + (2 : ℂ) * s ^ 2 * r ^ 4 + (-1 / 8 : ℂ) * s ^ 2 * r ^ 4 * μ + (7 / 4 : ℂ) * s ^ 2 * r ^ 6 + (35 / 16 : ℂ) * s ^ 3 + (3 / 16 : ℂ) * s ^ 3 * μ + (-83 / 16 : ℂ) * s ^ 3 * r ^ 2 + (-3 / 16 : ℂ) * s ^ 3 * r ^ 2 * μ + (-1 / 4 : ℂ) * s ^ 3 * r ^ 4 + (7 / 4 : ℂ) * s ^ 4 + (3 / 32 : ℂ) * s ^ 4 * μ + (-27 / 8 : ℂ) * s ^ 4 * r ^ 2 + (-3 / 32 : ℂ) * s ^ 4 * r ^ 2 * μ + (2 : ℂ) * s ^ 4 * r ^ 4 + (7 / 16 : ℂ) * s ^ 5 + (1 / 16 : ℂ) * s ^ 5 * r ^ 2 + (3 / 8 : ℂ) * s ^ 6 * r ^ 2) / (r ^ 6 * (r ^ 2 - 1) ^ 2))

/-- Harmonic `t` coefficient of the scalar–scalar source (per `B²`). -/
def ssSourceT (s r μ : ℂ) : ℂ :=
  (((1 / 2 : ℂ) * s * r ^ 4 + (1 / 2 : ℂ) * s ^ 2 * r ^ 2 + (3 / 16 : ℂ) * s ^ 3 + (1 / 4 : ℂ) * s ^ 3 * r ^ 2 + (3 / 8 : ℂ) * s ^ 4 + (3 / 16 : ℂ) * s ^ 5) / (r ^ 4))

/-- Harmonic `r` coefficient of the scalar–scalar source (per `B²`). -/
def ssSourceR (s r μ : ℂ) : ℂ :=
  (((1 / 2 : ℂ) * s * r ^ 2 + (1 / 2 : ℂ) * s ^ 2 + (-1 / 4 : ℂ) * s ^ 2 * r ^ 2 + (1 / 4 : ℂ) * s ^ 2 * r ^ 4 + (19 / 16 : ℂ) * s ^ 3 + (-3 / 4 : ℂ) * s ^ 3 * r ^ 2 + (7 / 8 : ℂ) * s ^ 4 + (-1 / 2 : ℂ) * s ^ 4 * r ^ 2 + (3 / 16 : ℂ) * s ^ 5) / (r ^ 5 * (r ^ 2 - 1)))

/-- Harmonic `T` coefficient of the scalar–scalar source (per `B²`). -/
def ssSourceTF (s r μ : ℂ) : ℂ :=
  (((1 / 2 : ℂ) * s ^ 2 + (-1 / 8 : ℂ) * s ^ 2 * μ + (-2 : ℂ) * s ^ 2 * r ^ 2 + (1 / 2 : ℂ) * s ^ 2 * r ^ 2 * μ + (11 / 8 : ℂ) * s ^ 3 + (-1 / 4 : ℂ) * s ^ 3 * μ + (-3 / 2 : ℂ) * s ^ 3 * r ^ 2 + (11 / 8 : ℂ) * s ^ 4 + (-1 / 8 : ℂ) * s ^ 4 * μ + (-1 / 2 : ℂ) * s ^ 4 * r ^ 2 + (5 / 8 : ℂ) * s ^ 5 + (1 / 8 : ℂ) * s ^ 6) / (r ^ 4 * (2 - μ)))

/-- Harmonic `L` coefficient of the scalar–scalar source (per `B²`). -/
def ssSourceL (s r μ : ℂ) : ℂ :=
  (((1 / 2 : ℂ) * s * r ^ 2 + (7 / 4 : ℂ) * s ^ 2 + (-1 / 16 : ℂ) * s ^ 2 * μ + (-1 / 4 : ℂ) * s ^ 2 * r ^ 2 + (1 / 4 : ℂ) * s ^ 2 * r ^ 2 * μ + (3 / 4 : ℂ) * s ^ 2 * r ^ 4 + (21 / 4 : ℂ) * s ^ 3 + (-1 / 8 : ℂ) * s ^ 3 * μ + (-1 : ℂ) * s ^ 3 * r ^ 2 + (91 / 16 : ℂ) * s ^ 4 + (-1 / 16 : ℂ) * s ^ 4 * μ + (-1 / 4 : ℂ) * s ^ 4 * r ^ 2 + (21 / 8 : ℂ) * s ^ 5 + (7 / 16 : ℂ) * s ^ 6) / (r ^ 4))

/-- Twisted radial derivative `D = ∂_r + 2s/(r(r²−1))` of `ssSourceTR`. -/
def ssSourceTR1 (s r μ : ℂ) : ℂ :=
  (((-3 : ℂ) * s ^ 2 * r ^ 2 + (8 : ℂ) * s ^ 2 * r ^ 4 + (-9 : ℂ) * s ^ 2 * r ^ 6 + (15 / 4 : ℂ) * s ^ 3 + (-71 / 4 : ℂ) * s ^ 3 * r ^ 2 + (23 : ℂ) * s ^ 3 * r ^ 4 + (3 / 2 : ℂ) * s ^ 3 * r ^ 6 + (87 / 8 : ℂ) * s ^ 4 + (-197 / 8 : ℂ) * s ^ 4 * r ^ 2 + (13 / 2 : ℂ) * s ^ 4 * r ^ 4 + (45 / 4 : ℂ) * s ^ 5 + (-33 / 2 : ℂ) * s ^ 5 * r ^ 2 + (5 : ℂ) * s ^ 5 * r ^ 4 + (39 / 8 : ℂ) * s ^ 6 + (-37 / 8 : ℂ) * s ^ 6 * r ^ 2 + (3 / 4 : ℂ) * s ^ 7) / (r ^ 6 * (r ^ 2 - 1) ^ 2))

/-- Twisted radial derivative `D = ∂_r + 2s/(r(r²−1))` of `ssSourceRR`. -/
def ssSourceRR1 (s r μ : ℂ) : ℂ :=
  (((1 / 2 : ℂ) * r ^ 4 * μ + (-3 / 2 : ℂ) * r ^ 6 * μ + (1 : ℂ) * r ^ 8 * μ + (2 : ℂ) * s * r ^ 2 + (1 : ℂ) * s * r ^ 2 * μ + (-2 : ℂ) * s * r ^ 4 + (-2 : ℂ) * s * r ^ 4 * μ + (-6 : ℂ) * s * r ^ 6 + (1 : ℂ) * s * r ^ 6 * μ + (6 : ℂ) * s * r ^ 8 + (21 / 4 : ℂ) * s ^ 2 + (9 / 16 : ℂ) * s ^ 2 * μ + (-73 / 4 : ℂ) * s ^ 2 * r ^ 2 + (-5 / 16 : ℂ) * s ^ 2 * r ^ 2 * μ + (27 : ℂ) * s ^ 2 * r ^ 4 + (-1 : ℂ) * s ^ 2 * r ^ 4 * μ + (-15 : ℂ) * s ^ 2 * r ^ 6 + (3 / 4 : ℂ) * s ^ 2 * r ^ 6 * μ + (-7 : ℂ) * s ^ 2 * r ^ 8 + (119 / 8 : ℂ) * s ^ 3 + (21 / 16 : ℂ) * s ^ 3 * μ + (-383 / 8 : ℂ) * s ^ 3 * r ^ 2 + (-41 / 16 : ℂ) * s ^ 3 * r ^ 2 * μ + (45 : ℂ) * s ^ 3 * r ^ 4 + (5 / 4 : ℂ) * s ^ 3 * r ^ 4 * μ + (5 : ℂ) * s ^ 3 * r ^ 6 + (119 / 8 : ℂ) * s ^ 4 + (15 / 16 : ℂ) * s ^ 4 * μ + (-331 / 8 : ℂ) * s ^ 4 * r ^ 2 + (-27 / 16 : ℂ) * s ^ 4 * r ^ 2 * μ + (61 / 2 : ℂ) * s ^ 4 * r ^ 4 + (3 / 4 : ℂ) * s ^ 4 * r ^ 4 * μ + (-12 : ℂ) * s ^ 4 * r ^ 6 + (49 / 8 : ℂ) * s ^ 5 + (3 / 16 : ℂ) * s ^ 5 * μ + (-87 / 8 : ℂ) * s ^ 5 * r ^ 2 + (-3 / 16 : ℂ) * s ^ 5 * r ^ 2 * μ + (7 / 2 : ℂ) * s ^ 5 * r ^ 4 + (7 / 8 : ℂ) * s ^ 6 + (13 / 8 : ℂ) * s ^ 6 * r ^ 2 + (-3 : ℂ) * s ^ 6 * r ^ 4 + (3 / 4 : ℂ) * s ^ 7 * r ^ 2) / (r ^ 7 * (r ^ 2 - 1) ^ 3))

/-- Twisted radial derivative `D = ∂_r + 2s/(r(r²−1))` of `ssSourceR`. -/
def ssSourceR1 (s r μ : ℂ) : ℂ :=
  (((3 / 2 : ℂ) * s * r ^ 2 + (-5 / 2 : ℂ) * s * r ^ 4 + (5 / 2 : ℂ) * s ^ 2 + (-13 / 4 : ℂ) * s ^ 2 * r ^ 2 + (3 / 2 : ℂ) * s ^ 2 * r ^ 4 + (-3 / 4 : ℂ) * s ^ 2 * r ^ 6 + (111 / 16 : ℂ) * s ^ 3 + (-177 / 16 : ℂ) * s ^ 3 * r ^ 2 + (17 / 4 : ℂ) * s ^ 3 * r ^ 4 + (27 / 4 : ℂ) * s ^ 4 + (-73 / 8 : ℂ) * s ^ 4 * r ^ 2 + (5 / 2 : ℂ) * s ^ 4 * r ^ 4 + (43 / 16 : ℂ) * s ^ 5 + (-37 / 16 : ℂ) * s ^ 5 * r ^ 2 + (3 / 8 : ℂ) * s ^ 6) / (r ^ 6 * (r ^ 2 - 1) ^ 2))

/-- Twisted radial derivative `D = ∂_r + 2s/(r(r²−1))` of `ssSourceT`. -/
def ssSourceT1 (s r μ : ℂ) : ℂ :=
  (((1 : ℂ) * s ^ 2 * r ^ 2 + (3 / 4 : ℂ) * s ^ 3 + (3 / 4 : ℂ) * s ^ 3 * r ^ 2 + (-1 / 2 : ℂ) * s ^ 3 * r ^ 4 + (15 / 8 : ℂ) * s ^ 4 + (-1 : ℂ) * s ^ 4 * r ^ 2 + (3 / 2 : ℂ) * s ^ 5 + (-3 / 4 : ℂ) * s ^ 5 * r ^ 2 + (3 / 8 : ℂ) * s ^ 6) / (r ^ 5 * (r ^ 2 - 1)))

/-- Twisted radial derivative `D = ∂_r + 2s/(r(r²−1))` of `ssSourceTF`. -/
def ssSourceTF1 (s r μ : ℂ) : ℂ :=
  (((2 : ℂ) * s ^ 2 + (-1 / 2 : ℂ) * s ^ 2 * μ + (-6 : ℂ) * s ^ 2 * r ^ 2 + (3 / 2 : ℂ) * s ^ 2 * r ^ 2 * μ + (4 : ℂ) * s ^ 2 * r ^ 4 + (-1 : ℂ) * s ^ 2 * r ^ 4 * μ + (13 / 2 : ℂ) * s ^ 3 + (-5 / 4 : ℂ) * s ^ 3 * μ + (-25 / 2 : ℂ) * s ^ 3 * r ^ 2 + (2 : ℂ) * s ^ 3 * r ^ 2 * μ + (3 : ℂ) * s ^ 3 * r ^ 4 + (33 / 4 : ℂ) * s ^ 4 + (-1 : ℂ) * s ^ 4 * μ + (-19 / 2 : ℂ) * s ^ 4 * r ^ 2 + (1 / 2 : ℂ) * s ^ 4 * r ^ 2 * μ + (1 : ℂ) * s ^ 4 * r ^ 4 + (21 / 4 : ℂ) * s ^ 5 + (-1 / 4 : ℂ) * s ^ 5 * μ + (-7 / 2 : ℂ) * s ^ 5 * r ^ 2 + (7 / 4 : ℂ) * s ^ 6 + (-1 / 2 : ℂ) * s ^ 6 * r ^ 2 + (1 / 4 : ℂ) * s ^ 7) / (r ^ 5 * (r ^ 2 - 1) * (2 - μ)))

/-- Second twisted radial derivative of `ssSourceTF`. -/
def ssSourceTF2 (s r μ : ℂ) : ℂ :=
  (((10 : ℂ) * s ^ 2 + (-5 / 2 : ℂ) * s ^ 2 * μ + (-32 : ℂ) * s ^ 2 * r ^ 2 + (8 : ℂ) * s ^ 2 * r ^ 2 * μ + (34 : ℂ) * s ^ 2 * r ^ 4 + (-17 / 2 : ℂ) * s ^ 2 * r ^ 4 * μ + (-12 : ℂ) * s ^ 2 * r ^ 6 + (3 : ℂ) * s ^ 2 * r ^ 6 * μ + (73 / 2 : ℂ) * s ^ 3 + (-29 / 4 : ℂ) * s ^ 3 * μ + (-95 : ℂ) * s ^ 3 * r ^ 2 + (71 / 4 : ℂ) * s ^ 3 * r ^ 2 * μ + (147 / 2 : ℂ) * s ^ 3 * r ^ 4 + (-12 : ℂ) * s ^ 3 * r ^ 4 * μ + (-9 : ℂ) * s ^ 3 * r ^ 6 + (217 / 4 : ℂ) * s ^ 4 + (-15 / 2 : ℂ) * s ^ 4 * μ + (-445 / 4 : ℂ) * s ^ 4 * r ^ 2 + (25 / 2 : ℂ) * s ^ 4 * r ^ 2 * μ + (109 / 2 : ℂ) * s ^ 4 * r ^ 4 + (-5 / 2 : ℂ) * s ^ 4 * r ^ 4 * μ + (-3 : ℂ) * s ^ 4 * r ^ 6 + (171 / 4 : ℂ) * s ^ 5 + (-13 / 4 : ℂ) * s ^ 5 * μ + (-265 / 4 : ℂ) * s ^ 5 * r ^ 2 + (11 / 4 : ℂ) * s ^ 5 * r ^ 2 * μ + (39 / 2 : ℂ) * s ^ 5 * r ^ 4 + (77 / 4 : ℂ) * s ^ 6 + (-1 / 2 : ℂ) * s ^ 6 * μ + (-83 / 4 : ℂ) * s ^ 6 * r ^ 2 + (5 / 2 : ℂ) * s ^ 6 * r ^ 4 + (19 / 4 : ℂ) * s ^ 7 + (-11 / 4 : ℂ) * s ^ 7 * r ^ 2 + (1 / 2 : ℂ) * s ^ 8) / (r ^ 6 * (r ^ 2 - 1) ^ 2 * (2 - μ)))

/-- The master source of the sourced master equation, per `B²`. -/
def ssMasterSource (s r μ : ℂ) : ℂ :=
  (((-2 : ℂ) * r ^ 4 * μ + (1 : ℂ) * r ^ 4 * μ ^ 2 + (-4 : ℂ) * r ^ 6 + (2 : ℂ) * r ^ 6 * μ + (-8 : ℂ) * s * r ^ 2 + (2 : ℂ) * s * r ^ 2 * μ + (1 : ℂ) * s * r ^ 2 * μ ^ 2 + (-4 : ℂ) * s * r ^ 4 + (2 : ℂ) * s * r ^ 4 * μ + (-9 : ℂ) * s ^ 2 + (9 / 4 : ℂ) * s ^ 2 * μ + (-1 / 8 : ℂ) * s ^ 2 * μ ^ 2 + (-5 / 2 : ℂ) * s ^ 2 * r ^ 2 + (-9 / 4 : ℂ) * s ^ 2 * r ^ 2 * μ + (5 / 2 : ℂ) * s ^ 2 * r ^ 2 * μ ^ 2 + (8 : ℂ) * s ^ 2 * r ^ 4 + (-4 : ℂ) * s ^ 2 * r ^ 4 * μ + (-75 / 2 : ℂ) * s ^ 3 + (7 : ℂ) * s ^ 3 * μ + (-1 / 4 : ℂ) * s ^ 3 * μ ^ 2 + (79 / 2 : ℂ) * s ^ 3 * r ^ 2 + (-17 / 2 : ℂ) * s ^ 3 * r ^ 2 * μ + (-129 / 2 : ℂ) * s ^ 4 + (8 : ℂ) * s ^ 4 * μ + (-1 / 8 : ℂ) * s ^ 4 * μ ^ 2 + (54 : ℂ) * s ^ 4 * r ^ 2 + (-29 / 4 : ℂ) * s ^ 4 * r ^ 2 * μ + (-59 : ℂ) * s ^ 5 + (4 : ℂ) * s ^ 5 * μ + (51 / 2 : ℂ) * s ^ 5 * r ^ 2 + (-61 / 2 : ℂ) * s ^ 6 + (3 / 4 : ℂ) * s ^ 6 * μ + (11 / 2 : ℂ) * s ^ 6 * r ^ 2 + (-17 / 2 : ℂ) * s ^ 7 + (-1 : ℂ) * s ^ 8) / (r ^ 5 * (r ^ 2 - 1) * (2 - μ)))

/-- Harmonic time Bianchi identity of the source: `−(2s/f)τ_tt + (2r + 2f/r)τ_tr + f·Dτ_tr + (μ/r²)τ_t = 0`. -/
theorem ssSource_bianchiT (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    -(2 * s / (r ^ 2 - 1)) * ssSourceTT s r μ + (2 * r + 2 * (r ^ 2 - 1) / r) * ssSourceTR s r μ +
      (r ^ 2 - 1) * ssSourceTR1 s r μ + μ / r ^ 2 * ssSourceT s r μ = 0 := by
  unfold ssSourceTT ssSourceTR ssSourceTR1 ssSourceT
  field_simp
  ring

/-- Harmonic radial Bianchi identity of the source. -/
theorem ssSource_bianchiR (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    r / (r ^ 2 - 1) ^ 2 * ssSourceTT s r μ - 2 * s / (r ^ 2 - 1) * ssSourceTR s r μ +
      (r ^ 2 - 1) * ssSourceRR1 s r μ + (3 * r + 2 * (r ^ 2 - 1) / r) * ssSourceRR s r μ +
      μ / r ^ 2 * ssSourceR s r μ - 2 / r ^ 3 * ssSourceL s r μ = 0 := by
  unfold ssSourceTT ssSourceTR ssSourceRR1 ssSourceRR ssSourceR ssSourceL
  field_simp
  ring

/-- Harmonic angular Bianchi identity of the source. -/
theorem ssSource_bianchiAng (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    -(2 * s / (r ^ 2 - 1)) * ssSourceT s r μ + (r ^ 2 - 1) * ssSourceR1 s r μ +
      (2 * r + 2 * (r ^ 2 - 1) / r) * ssSourceR s r μ + (μ - 2) / (2 * r ^ 2) * ssSourceTF s r μ +
      1 / r ^ 2 * ssSourceL s r μ = 0 := by
  unfold ssSourceT ssSourceR1 ssSourceR ssSourceTF ssSourceL
  field_simp
  ring

/-- The master identity applied to the source coefficients gives the master source. -/
theorem ssSource_masterSource (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    -(2 * r) / (r ^ 2 - 1) ^ 2 * ssSourceTT s r μ + 2 / s * ssSourceTR s r μ + 2 * r * ssSourceRR s r μ +
      -(4 * r) / (s * (r ^ 2 - 1)) * ssSourceT s r μ + 4 * ssSourceR s r μ +
      (4 / r + 4 * μ / (r * (r ^ 2 - 1)) - 8 * s ^ 2 * r / (r ^ 2 - 1) ^ 2) * ssSourceTF s r μ +
      -(2 / s) * ssSourceT1 s r μ + (8 * r ^ 2 - 4) / (r ^ 2 - 1) * ssSourceTF1 s r μ +
      2 * r * ssSourceTF2 s r μ = ssMasterSource s r μ := by
  unfold ssSourceTT ssSourceTR ssSourceRR ssSourceT ssSourceR ssSourceTF ssSourceT1 ssSourceTF1 ssSourceTF2
    ssMasterSource
  field_simp
  ring

end
end RHTower.D4BMScalarStream
