import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMScalarStreamReconstructionJet

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
  (((-1 / 4 : ℂ) * r ^ (4 : ℕ) * μ + (1 / 4 : ℂ) * r ^ (6 : ℕ) * μ + (-1 / 2 : ℂ) * s * r ^ (2 : ℕ) + (-1 / 4 : ℂ) * s * r ^ (2 : ℕ) * μ + (-1 : ℂ) * s * r ^ (4 : ℕ) + (1 / 4 : ℂ) * s * r ^ (4 : ℕ) * μ + (3 / 2 : ℂ) * s * r ^ (6 : ℕ) + (9 / 8 : ℂ) * s ^ (2 : ℕ) + (-3 / 32 : ℂ) * s ^ (2 : ℕ) * μ + (-31 / 8 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-1 / 32 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) * μ + (5 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (1 / 8 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) * μ + (-1 / 4 : ℂ) * s ^ (2 : ℕ) * r ^ (6 : ℕ) + (57 / 16 : ℂ) * s ^ (3 : ℕ) + (-3 / 16 : ℂ) * s ^ (3 : ℕ) * μ + (-113 / 16 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (3 / 16 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) * μ + (1 / 4 : ℂ) * s ^ (3 : ℕ) * r ^ (4 : ℕ) + (33 / 8 : ℂ) * s ^ (4 : ℕ) + (-3 / 32 : ℂ) * s ^ (4 : ℕ) * μ + (-17 / 4 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (3 / 32 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) * μ + (1 / 2 : ℂ) * s ^ (4 : ℕ) * r ^ (4 : ℕ) + (33 / 16 : ℂ) * s ^ (5 : ℕ) + (-25 / 16 : ℂ) * s ^ (5 : ℕ) * r ^ (2 : ℕ) + (3 / 8 : ℂ) * s ^ (6 : ℕ)) / (r ^ (6 : ℕ)))

/-- Harmonic `tr` coefficient of the scalar–scalar source (per `B²`). -/
def ssSourceTR (s r μ : ℂ) : ℂ :=
  (((-1 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (3 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (3 / 4 : ℂ) * s ^ (3 : ℕ) + (-7 / 2 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-1 / 2 : ℂ) * s ^ (3 : ℕ) * r ^ (4 : ℕ) + (15 / 8 : ℂ) * s ^ (4 : ℕ) + (-3 / 2 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (3 / 2 : ℂ) * s ^ (5 : ℕ) + (-1 : ℂ) * s ^ (5 : ℕ) * r ^ (2 : ℕ) + (3 / 8 : ℂ) * s ^ (6 : ℕ)) / (r ^ (5 : ℕ) * (r ^ (2 : ℕ) - 1)))

/-- Harmonic `rr` coefficient of the scalar–scalar source (per `B²`). -/
def ssSourceRR (s r μ : ℂ) : ℂ :=
  (((1 / 4 : ℂ) * r ^ (4 : ℕ) * μ + (-1 / 4 : ℂ) * r ^ (6 : ℕ) * μ + (1 / 2 : ℂ) * s * r ^ (2 : ℕ) + (1 / 4 : ℂ) * s * r ^ (2 : ℕ) * μ + (1 : ℂ) * s * r ^ (4 : ℕ) + (-1 / 4 : ℂ) * s * r ^ (4 : ℕ) * μ + (-3 / 2 : ℂ) * s * r ^ (6 : ℕ) + (7 / 8 : ℂ) * s ^ (2 : ℕ) + (3 / 32 : ℂ) * s ^ (2 : ℕ) * μ + (-21 / 8 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (1 / 32 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) * μ + (2 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (-1 / 8 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) * μ + (7 / 4 : ℂ) * s ^ (2 : ℕ) * r ^ (6 : ℕ) + (35 / 16 : ℂ) * s ^ (3 : ℕ) + (3 / 16 : ℂ) * s ^ (3 : ℕ) * μ + (-83 / 16 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-3 / 16 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) * μ + (-1 / 4 : ℂ) * s ^ (3 : ℕ) * r ^ (4 : ℕ) + (7 / 4 : ℂ) * s ^ (4 : ℕ) + (3 / 32 : ℂ) * s ^ (4 : ℕ) * μ + (-27 / 8 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (-3 / 32 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) * μ + (2 : ℂ) * s ^ (4 : ℕ) * r ^ (4 : ℕ) + (7 / 16 : ℂ) * s ^ (5 : ℕ) + (1 / 16 : ℂ) * s ^ (5 : ℕ) * r ^ (2 : ℕ) + (3 / 8 : ℂ) * s ^ (6 : ℕ) * r ^ (2 : ℕ)) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)))

/-- Harmonic `t` coefficient of the scalar–scalar source (per `B²`). -/
def ssSourceT (s r μ : ℂ) : ℂ :=
  (((1 / 2 : ℂ) * s * r ^ (4 : ℕ) + (1 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (3 / 16 : ℂ) * s ^ (3 : ℕ) + (1 / 4 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (3 / 8 : ℂ) * s ^ (4 : ℕ) + (3 / 16 : ℂ) * s ^ (5 : ℕ)) / (r ^ (4 : ℕ)))

/-- Harmonic `r` coefficient of the scalar–scalar source (per `B²`). -/
def ssSourceR (s r μ : ℂ) : ℂ :=
  (((1 / 2 : ℂ) * s * r ^ (2 : ℕ) + (1 / 2 : ℂ) * s ^ (2 : ℕ) + (-1 / 4 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (1 / 4 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (19 / 16 : ℂ) * s ^ (3 : ℕ) + (-3 / 4 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (7 / 8 : ℂ) * s ^ (4 : ℕ) + (-1 / 2 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (3 / 16 : ℂ) * s ^ (5 : ℕ)) / (r ^ (5 : ℕ) * (r ^ (2 : ℕ) - 1)))

/-- Harmonic `T` coefficient of the scalar–scalar source (per `B²`). -/
def ssSourceTF (s r μ : ℂ) : ℂ :=
  (((1 / 2 : ℂ) * s ^ (2 : ℕ) + (-1 / 8 : ℂ) * s ^ (2 : ℕ) * μ + (-2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (1 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) * μ + (11 / 8 : ℂ) * s ^ (3 : ℕ) + (-1 / 4 : ℂ) * s ^ (3 : ℕ) * μ + (-3 / 2 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (11 / 8 : ℂ) * s ^ (4 : ℕ) + (-1 / 8 : ℂ) * s ^ (4 : ℕ) * μ + (-1 / 2 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (5 / 8 : ℂ) * s ^ (5 : ℕ) + (1 / 8 : ℂ) * s ^ (6 : ℕ)) / (r ^ (4 : ℕ) * (2 - μ)))

/-- Harmonic `L` coefficient of the scalar–scalar source (per `B²`). -/
def ssSourceL (s r μ : ℂ) : ℂ :=
  (((1 / 2 : ℂ) * s * r ^ (2 : ℕ) + (7 / 4 : ℂ) * s ^ (2 : ℕ) + (-1 / 16 : ℂ) * s ^ (2 : ℕ) * μ + (-1 / 4 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (1 / 4 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) * μ + (3 / 4 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (21 / 4 : ℂ) * s ^ (3 : ℕ) + (-1 / 8 : ℂ) * s ^ (3 : ℕ) * μ + (-1 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (91 / 16 : ℂ) * s ^ (4 : ℕ) + (-1 / 16 : ℂ) * s ^ (4 : ℕ) * μ + (-1 / 4 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (21 / 8 : ℂ) * s ^ (5 : ℕ) + (7 / 16 : ℂ) * s ^ (6 : ℕ)) / (r ^ (4 : ℕ)))

/-- Twisted radial derivative `D = ∂_r + 2s/(r(r²−1))` of `ssSourceTR`. -/
def ssSourceTR1 (s r μ : ℂ) : ℂ :=
  (((-3 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (8 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (-9 : ℂ) * s ^ (2 : ℕ) * r ^ (6 : ℕ) + (15 / 4 : ℂ) * s ^ (3 : ℕ) + (-71 / 4 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (23 : ℂ) * s ^ (3 : ℕ) * r ^ (4 : ℕ) + (3 / 2 : ℂ) * s ^ (3 : ℕ) * r ^ (6 : ℕ) + (87 / 8 : ℂ) * s ^ (4 : ℕ) + (-197 / 8 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (13 / 2 : ℂ) * s ^ (4 : ℕ) * r ^ (4 : ℕ) + (45 / 4 : ℂ) * s ^ (5 : ℕ) + (-33 / 2 : ℂ) * s ^ (5 : ℕ) * r ^ (2 : ℕ) + (5 : ℂ) * s ^ (5 : ℕ) * r ^ (4 : ℕ) + (39 / 8 : ℂ) * s ^ (6 : ℕ) + (-37 / 8 : ℂ) * s ^ (6 : ℕ) * r ^ (2 : ℕ) + (3 / 4 : ℂ) * s ^ (7 : ℕ)) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)))

/-- Twisted radial derivative `D = ∂_r + 2s/(r(r²−1))` of `ssSourceRR`. -/
def ssSourceRR1 (s r μ : ℂ) : ℂ :=
  (((1 / 2 : ℂ) * r ^ (4 : ℕ) * μ + (-3 / 2 : ℂ) * r ^ (6 : ℕ) * μ + (1 : ℂ) * r ^ (8 : ℕ) * μ + (2 : ℂ) * s * r ^ (2 : ℕ) + (1 : ℂ) * s * r ^ (2 : ℕ) * μ + (-2 : ℂ) * s * r ^ (4 : ℕ) + (-2 : ℂ) * s * r ^ (4 : ℕ) * μ + (-6 : ℂ) * s * r ^ (6 : ℕ) + (1 : ℂ) * s * r ^ (6 : ℕ) * μ + (6 : ℂ) * s * r ^ (8 : ℕ) + (21 / 4 : ℂ) * s ^ (2 : ℕ) + (9 / 16 : ℂ) * s ^ (2 : ℕ) * μ + (-73 / 4 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-5 / 16 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) * μ + (27 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (-1 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) * μ + (-15 : ℂ) * s ^ (2 : ℕ) * r ^ (6 : ℕ) + (3 / 4 : ℂ) * s ^ (2 : ℕ) * r ^ (6 : ℕ) * μ + (-7 : ℂ) * s ^ (2 : ℕ) * r ^ (8 : ℕ) + (119 / 8 : ℂ) * s ^ (3 : ℕ) + (21 / 16 : ℂ) * s ^ (3 : ℕ) * μ + (-383 / 8 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-41 / 16 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) * μ + (45 : ℂ) * s ^ (3 : ℕ) * r ^ (4 : ℕ) + (5 / 4 : ℂ) * s ^ (3 : ℕ) * r ^ (4 : ℕ) * μ + (5 : ℂ) * s ^ (3 : ℕ) * r ^ (6 : ℕ) + (119 / 8 : ℂ) * s ^ (4 : ℕ) + (15 / 16 : ℂ) * s ^ (4 : ℕ) * μ + (-331 / 8 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (-27 / 16 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) * μ + (61 / 2 : ℂ) * s ^ (4 : ℕ) * r ^ (4 : ℕ) + (3 / 4 : ℂ) * s ^ (4 : ℕ) * r ^ (4 : ℕ) * μ + (-12 : ℂ) * s ^ (4 : ℕ) * r ^ (6 : ℕ) + (49 / 8 : ℂ) * s ^ (5 : ℕ) + (3 / 16 : ℂ) * s ^ (5 : ℕ) * μ + (-87 / 8 : ℂ) * s ^ (5 : ℕ) * r ^ (2 : ℕ) + (-3 / 16 : ℂ) * s ^ (5 : ℕ) * r ^ (2 : ℕ) * μ + (7 / 2 : ℂ) * s ^ (5 : ℕ) * r ^ (4 : ℕ) + (7 / 8 : ℂ) * s ^ (6 : ℕ) + (13 / 8 : ℂ) * s ^ (6 : ℕ) * r ^ (2 : ℕ) + (-3 : ℂ) * s ^ (6 : ℕ) * r ^ (4 : ℕ) + (3 / 4 : ℂ) * s ^ (7 : ℕ) * r ^ (2 : ℕ)) / (r ^ (7 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ)))

/-- Twisted radial derivative `D = ∂_r + 2s/(r(r²−1))` of `ssSourceR`. -/
def ssSourceR1 (s r μ : ℂ) : ℂ :=
  (((3 / 2 : ℂ) * s * r ^ (2 : ℕ) + (-5 / 2 : ℂ) * s * r ^ (4 : ℕ) + (5 / 2 : ℂ) * s ^ (2 : ℕ) + (-13 / 4 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (3 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (-3 / 4 : ℂ) * s ^ (2 : ℕ) * r ^ (6 : ℕ) + (111 / 16 : ℂ) * s ^ (3 : ℕ) + (-177 / 16 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (17 / 4 : ℂ) * s ^ (3 : ℕ) * r ^ (4 : ℕ) + (27 / 4 : ℂ) * s ^ (4 : ℕ) + (-73 / 8 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (5 / 2 : ℂ) * s ^ (4 : ℕ) * r ^ (4 : ℕ) + (43 / 16 : ℂ) * s ^ (5 : ℕ) + (-37 / 16 : ℂ) * s ^ (5 : ℕ) * r ^ (2 : ℕ) + (3 / 8 : ℂ) * s ^ (6 : ℕ)) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)))

/-- Twisted radial derivative `D = ∂_r + 2s/(r(r²−1))` of `ssSourceT`. -/
def ssSourceT1 (s r μ : ℂ) : ℂ :=
  (((1 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (3 / 4 : ℂ) * s ^ (3 : ℕ) + (3 / 4 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-1 / 2 : ℂ) * s ^ (3 : ℕ) * r ^ (4 : ℕ) + (15 / 8 : ℂ) * s ^ (4 : ℕ) + (-1 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (3 / 2 : ℂ) * s ^ (5 : ℕ) + (-3 / 4 : ℂ) * s ^ (5 : ℕ) * r ^ (2 : ℕ) + (3 / 8 : ℂ) * s ^ (6 : ℕ)) / (r ^ (5 : ℕ) * (r ^ (2 : ℕ) - 1)))

/-- Twisted radial derivative `D = ∂_r + 2s/(r(r²−1))` of `ssSourceTF`. -/
def ssSourceTF1 (s r μ : ℂ) : ℂ :=
  (((2 : ℂ) * s ^ (2 : ℕ) + (-1 / 2 : ℂ) * s ^ (2 : ℕ) * μ + (-6 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (3 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) * μ + (4 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (-1 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) * μ + (13 / 2 : ℂ) * s ^ (3 : ℕ) + (-5 / 4 : ℂ) * s ^ (3 : ℕ) * μ + (-25 / 2 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (2 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) * μ + (3 : ℂ) * s ^ (3 : ℕ) * r ^ (4 : ℕ) + (33 / 4 : ℂ) * s ^ (4 : ℕ) + (-1 : ℂ) * s ^ (4 : ℕ) * μ + (-19 / 2 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (1 / 2 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) * μ + (1 : ℂ) * s ^ (4 : ℕ) * r ^ (4 : ℕ) + (21 / 4 : ℂ) * s ^ (5 : ℕ) + (-1 / 4 : ℂ) * s ^ (5 : ℕ) * μ + (-7 / 2 : ℂ) * s ^ (5 : ℕ) * r ^ (2 : ℕ) + (7 / 4 : ℂ) * s ^ (6 : ℕ) + (-1 / 2 : ℂ) * s ^ (6 : ℕ) * r ^ (2 : ℕ) + (1 / 4 : ℂ) * s ^ (7 : ℕ)) / (r ^ (5 : ℕ) * (r ^ (2 : ℕ) - 1) * (2 - μ)))

/-- Second twisted radial derivative of `ssSourceTF`. -/
def ssSourceTF2 (s r μ : ℂ) : ℂ :=
  (((10 : ℂ) * s ^ (2 : ℕ) + (-5 / 2 : ℂ) * s ^ (2 : ℕ) * μ + (-32 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (8 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) * μ + (34 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (-17 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) * μ + (-12 : ℂ) * s ^ (2 : ℕ) * r ^ (6 : ℕ) + (3 : ℂ) * s ^ (2 : ℕ) * r ^ (6 : ℕ) * μ + (73 / 2 : ℂ) * s ^ (3 : ℕ) + (-29 / 4 : ℂ) * s ^ (3 : ℕ) * μ + (-95 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (71 / 4 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) * μ + (147 / 2 : ℂ) * s ^ (3 : ℕ) * r ^ (4 : ℕ) + (-12 : ℂ) * s ^ (3 : ℕ) * r ^ (4 : ℕ) * μ + (-9 : ℂ) * s ^ (3 : ℕ) * r ^ (6 : ℕ) + (217 / 4 : ℂ) * s ^ (4 : ℕ) + (-15 / 2 : ℂ) * s ^ (4 : ℕ) * μ + (-445 / 4 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (25 / 2 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) * μ + (109 / 2 : ℂ) * s ^ (4 : ℕ) * r ^ (4 : ℕ) + (-5 / 2 : ℂ) * s ^ (4 : ℕ) * r ^ (4 : ℕ) * μ + (-3 : ℂ) * s ^ (4 : ℕ) * r ^ (6 : ℕ) + (171 / 4 : ℂ) * s ^ (5 : ℕ) + (-13 / 4 : ℂ) * s ^ (5 : ℕ) * μ + (-265 / 4 : ℂ) * s ^ (5 : ℕ) * r ^ (2 : ℕ) + (11 / 4 : ℂ) * s ^ (5 : ℕ) * r ^ (2 : ℕ) * μ + (39 / 2 : ℂ) * s ^ (5 : ℕ) * r ^ (4 : ℕ) + (77 / 4 : ℂ) * s ^ (6 : ℕ) + (-1 / 2 : ℂ) * s ^ (6 : ℕ) * μ + (-83 / 4 : ℂ) * s ^ (6 : ℕ) * r ^ (2 : ℕ) + (5 / 2 : ℂ) * s ^ (6 : ℕ) * r ^ (4 : ℕ) + (19 / 4 : ℂ) * s ^ (7 : ℕ) + (-11 / 4 : ℂ) * s ^ (7 : ℕ) * r ^ (2 : ℕ) + (1 / 2 : ℂ) * s ^ (8 : ℕ)) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ) * (2 - μ)))

/-- The master source of the sourced master equation, per `B²`. -/
def ssMasterSource (s r μ : ℂ) : ℂ :=
  (((-2 : ℂ) * r ^ (4 : ℕ) * μ + (1 : ℂ) * r ^ (4 : ℕ) * μ ^ (2 : ℕ) + (-4 : ℂ) * r ^ (6 : ℕ) + (2 : ℂ) * r ^ (6 : ℕ) * μ + (-8 : ℂ) * s * r ^ (2 : ℕ) + (2 : ℂ) * s * r ^ (2 : ℕ) * μ + (1 : ℂ) * s * r ^ (2 : ℕ) * μ ^ (2 : ℕ) + (-4 : ℂ) * s * r ^ (4 : ℕ) + (2 : ℂ) * s * r ^ (4 : ℕ) * μ + (-9 : ℂ) * s ^ (2 : ℕ) + (9 / 4 : ℂ) * s ^ (2 : ℕ) * μ + (-1 / 8 : ℂ) * s ^ (2 : ℕ) * μ ^ (2 : ℕ) + (-5 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-9 / 4 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) * μ + (5 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) * μ ^ (2 : ℕ) + (8 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (-4 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) * μ + (-75 / 2 : ℂ) * s ^ (3 : ℕ) + (7 : ℂ) * s ^ (3 : ℕ) * μ + (-1 / 4 : ℂ) * s ^ (3 : ℕ) * μ ^ (2 : ℕ) + (79 / 2 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-17 / 2 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) * μ + (-129 / 2 : ℂ) * s ^ (4 : ℕ) + (8 : ℂ) * s ^ (4 : ℕ) * μ + (-1 / 8 : ℂ) * s ^ (4 : ℕ) * μ ^ (2 : ℕ) + (54 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (-29 / 4 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) * μ + (-59 : ℂ) * s ^ (5 : ℕ) + (4 : ℂ) * s ^ (5 : ℕ) * μ + (51 / 2 : ℂ) * s ^ (5 : ℕ) * r ^ (2 : ℕ) + (-61 / 2 : ℂ) * s ^ (6 : ℕ) + (3 / 4 : ℂ) * s ^ (6 : ℕ) * μ + (11 / 2 : ℂ) * s ^ (6 : ℕ) * r ^ (2 : ℕ) + (-17 / 2 : ℂ) * s ^ (7 : ℕ) + (-1 : ℂ) * s ^ (8 : ℕ)) / (r ^ (5 : ℕ) * (r ^ (2 : ℕ) - 1) * (2 - μ)))

/-- Harmonic time Bianchi identity of the source: `−(2s/f)τ_tt + (2r + 2f/r)τ_tr + f·Dτ_tr + (μ/r²)τ_t = 0`. -/
theorem ssSource_bianchiT (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    -(2 * s / (r ^ (2 : ℕ) - 1)) * ssSourceTT s r μ + (2 * r + 2 * (r ^ (2 : ℕ) - 1) / r) * ssSourceTR s r μ +
      (r ^ (2 : ℕ) - 1) * ssSourceTR1 s r μ + μ / r ^ (2 : ℕ) * ssSourceT s r μ = 0 := by
  unfold ssSourceTT ssSourceTR ssSourceTR1 ssSourceT
  field_simp
  ring

/-- Harmonic radial Bianchi identity of the source. -/
theorem ssSource_bianchiR (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    r / (r ^ (2 : ℕ) - 1) ^ (2 : ℕ) * ssSourceTT s r μ - 2 * s / (r ^ (2 : ℕ) - 1) * ssSourceTR s r μ +
      (r ^ (2 : ℕ) - 1) * ssSourceRR1 s r μ + (3 * r + 2 * (r ^ (2 : ℕ) - 1) / r) * ssSourceRR s r μ +
      μ / r ^ (2 : ℕ) * ssSourceR s r μ - 2 / r ^ (3 : ℕ) * ssSourceL s r μ = 0 := by
  unfold ssSourceTT ssSourceTR ssSourceRR1 ssSourceRR ssSourceR ssSourceL
  field_simp
  ring

/-- Harmonic angular Bianchi identity of the source. -/
theorem ssSource_bianchiAng (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    -(2 * s / (r ^ (2 : ℕ) - 1)) * ssSourceT s r μ + (r ^ (2 : ℕ) - 1) * ssSourceR1 s r μ +
      (2 * r + 2 * (r ^ (2 : ℕ) - 1) / r) * ssSourceR s r μ + (μ - 2) / (2 * r ^ (2 : ℕ)) * ssSourceTF s r μ +
      1 / r ^ (2 : ℕ) * ssSourceL s r μ = 0 := by
  unfold ssSourceT ssSourceR1 ssSourceR ssSourceTF ssSourceL
  field_simp
  ring

/-- The master identity applied to the source coefficients gives the master source. -/
theorem ssSource_masterSource (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    -(2 * r) / (r ^ (2 : ℕ) - 1) ^ (2 : ℕ) * ssSourceTT s r μ + 2 / s * ssSourceTR s r μ + 2 * r * ssSourceRR s r μ +
      -(4 * r) / (s * (r ^ (2 : ℕ) - 1)) * ssSourceT s r μ + 4 * ssSourceR s r μ +
      (4 / r + 4 * μ / (r * (r ^ (2 : ℕ) - 1)) - 8 * s ^ (2 : ℕ) * r / (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * ssSourceTF s r μ +
      -(2 / s) * ssSourceT1 s r μ + (8 * r ^ (2 : ℕ) - 4) / (r ^ (2 : ℕ) - 1) * ssSourceTF1 s r μ +
      2 * r * ssSourceTF2 s r μ = ssMasterSource s r μ := by
  unfold ssSourceTT ssSourceTR ssSourceRR ssSourceT ssSourceR ssSourceTF ssSourceT1 ssSourceTF1 ssSourceTF2
    ssMasterSource
  field_simp
  ring

end
end RHTower.D4BMScalarStream
