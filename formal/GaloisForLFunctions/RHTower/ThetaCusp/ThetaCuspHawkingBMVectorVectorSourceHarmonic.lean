import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMScalarStreamSourceHarmonic

/-!
# Harmonic coefficients of the vector–vector quadratic source and their Bianchi identities

The vector–vector quadratic Einstein source of the fundamental coexact vector mode (time rate `s`,
envelope `B` with `B' = sB/(r(r²−1))`, angular eigenvalue `λ = (s+1)(s+2)` of the generating
scalar `S`), projected on one angular harmonic `ΔY = μY`, has the seven harmonic coefficients
`vvSourceTT, …, vvSourceL` (per `B²`). The source decomposes into the invariants `S²`, `|∇S|²`,
`|∇∇S|²`, the gradients of `S²` and `|∇S|²`, and the trace-free tensors `(∇S⊗∇S)^{tf}`,
`tfHess(S²)`; their harmonic images are `S² ↦ Y`, `|∇S|² ↦ (μ/2 − λ)Y`,
`|∇∇S|² ↦ (μ²/4 − (λ − ½)μ + λ(λ−1))Y` (Bochner on the hyperbolic plane), `∇φ ↦ φ̂·∇Y`,
`(∇S⊗∇S)^{tf} ↦ (λ/(μ−2))·tfHess Y`, `tfHess(S²) ↦ tfHess Y`.
The envelope makes the radial derivative of a coefficient the twisted derivative
`D = ∂_r + 2s/(r(r²−1))`; the first twisted derivatives needed below are given explicitly. The
three theorems `vvSource_bianchiT/R/Ang` are the harmonic contracted Bianchi identities of the
source (its conservation), and `vvSource_masterSource` identifies the master source of the sourced
Kodama–Ishibashi master equation. Everything is a closed rational identity.
-/

set_option linter.unusedVariables false

namespace RHTower.D4BMScalarStream
open GaloisForLFunctions.HTGeometry CoordinateMetricTwoJet
noncomputable section

/-- Harmonic `tt` coefficient of the vector–vector source (per `B²`). -/
def vvSourceTT (s r μ : ℂ) : ℂ :=
  (((-9 / 2 : ℂ) * s ^ (2 : ℕ) + (15 / 8 : ℂ) * s ^ (2 : ℕ) * μ + (-1 / 8 : ℂ) * s ^ (2 : ℕ) * μ ^ (2 : ℕ) + (13 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-15 / 8 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) * μ + (1 / 8 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) * μ ^ (2 : ℕ) + (-2 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (1 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) * μ + (-45 / 4 : ℂ) * s ^ (3 : ℕ) + (9 / 4 : ℂ) * s ^ (3 : ℕ) * μ + (61 / 4 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-7 / 4 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) * μ + (-3 : ℂ) * s ^ (3 : ℕ) * r ^ (4 : ℕ) + (-10 : ℂ) * s ^ (4 : ℕ) + (5 / 8 : ℂ) * s ^ (4 : ℕ) * μ + (23 / 2 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (-1 / 8 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) * μ + (-1 : ℂ) * s ^ (4 : ℕ) * r ^ (4 : ℕ) + (-15 / 4 : ℂ) * s ^ (5 : ℕ) + (11 / 4 : ℂ) * s ^ (5 : ℕ) * r ^ (2 : ℕ) + (-1 / 2 : ℂ) * s ^ (6 : ℕ)) / (r ^ (6 : ℕ)))

/-- Harmonic `tr` coefficient of the vector–vector source (per `B²`). -/
def vvSourceTR (s r μ : ℂ) : ℂ :=
  (((1 / 2 : ℂ) * s ^ (2 : ℕ) * μ + (-3 : ℂ) * s ^ (3 : ℕ) + (3 / 2 : ℂ) * s ^ (3 : ℕ) * μ + (4 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-1 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) * μ + (-11 / 2 : ℂ) * s ^ (4 : ℕ) + (1 / 2 : ℂ) * s ^ (4 : ℕ) * μ + (6 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (-3 : ℂ) * s ^ (5 : ℕ) + (2 : ℂ) * s ^ (5 : ℕ) * r ^ (2 : ℕ) + (-1 / 2 : ℂ) * s ^ (6 : ℕ)) / (r ^ (5 : ℕ) * (r ^ (2 : ℕ) - 1)))

/-- Harmonic `rr` coefficient of the vector–vector source (per `B²`). -/
def vvSourceRR (s r μ : ℂ) : ℂ :=
  (((-7 / 2 : ℂ) * s ^ (2 : ℕ) + (5 / 8 : ℂ) * s ^ (2 : ℕ) * μ + (1 / 8 : ℂ) * s ^ (2 : ℕ) * μ ^ (2 : ℕ) + (19 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-13 / 8 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) * μ + (-1 / 8 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) * μ ^ (2 : ℕ) + (-6 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (3 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) * μ + (-31 / 4 : ℂ) * s ^ (3 : ℕ) + (1 / 4 : ℂ) * s ^ (3 : ℕ) * μ + (71 / 4 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (1 / 4 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) * μ + (-9 : ℂ) * s ^ (3 : ℕ) * r ^ (4 : ℕ) + (-11 / 2 : ℂ) * s ^ (4 : ℕ) + (-1 / 8 : ℂ) * s ^ (4 : ℕ) * μ + (9 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (5 / 8 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) * μ + (-3 : ℂ) * s ^ (4 : ℕ) * r ^ (4 : ℕ) + (-5 / 4 : ℂ) * s ^ (5 : ℕ) + (1 / 4 : ℂ) * s ^ (5 : ℕ) * r ^ (2 : ℕ) + (-1 / 2 : ℂ) * s ^ (6 : ℕ) * r ^ (2 : ℕ)) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)))

/-- Harmonic `t` coefficient of the vector–vector source (per `B²`). -/
def vvSourceT (s r μ : ℂ) : ℂ :=
  (((3 / 2 : ℂ) * s ^ (2 : ℕ) + (7 / 4 : ℂ) * s ^ (3 : ℕ) + (1 / 4 : ℂ) * s ^ (3 : ℕ) * μ + (-1 / 4 : ℂ) * s ^ (5 : ℕ)) / (r ^ (4 : ℕ)))

/-- Harmonic `r` coefficient of the vector–vector source (per `B²`). -/
def vvSourceR (s r μ : ℂ) : ℂ :=
  (((-1 / 2 : ℂ) * s ^ (2 : ℕ) + (1 / 2 : ℂ) * s ^ (2 : ℕ) * μ + (2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-1 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) * μ + (-5 / 4 : ℂ) * s ^ (3 : ℕ) + (1 / 4 : ℂ) * s ^ (3 : ℕ) * μ + (3 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-1 : ℂ) * s ^ (4 : ℕ) + (1 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (-1 / 4 : ℂ) * s ^ (5 : ℕ)) / (r ^ (5 : ℕ) * (r ^ (2 : ℕ) - 1)))

/-- Harmonic `T` coefficient of the vector–vector source (per `B²`). -/
def vvSourceTF (s r μ : ℂ) : ℂ :=
  (((-11 : ℂ) * s ^ (2 : ℕ) + (-57 / 2 : ℂ) * s ^ (3 : ℕ) + (-53 / 2 : ℂ) * s ^ (4 : ℕ) + (-21 / 2 : ℂ) * s ^ (5 : ℕ) + (-3 / 2 : ℂ) * s ^ (6 : ℕ)) / (r ^ (4 : ℕ) * (2 - μ)))

/-- Harmonic `L` coefficient of the vector–vector source (per `B²`). -/
def vvSourceL (s r μ : ℂ) : ℂ :=
  (((-7 : ℂ) * s ^ (2 : ℕ) + (3 / 2 : ℂ) * s ^ (2 : ℕ) * μ + (2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-1 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) * μ + (-19 : ℂ) * s ^ (3 : ℕ) + (7 / 4 : ℂ) * s ^ (3 : ℕ) * μ + (3 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-75 / 4 : ℂ) * s ^ (4 : ℕ) + (1 / 2 : ℂ) * s ^ (4 : ℕ) * μ + (1 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (-8 : ℂ) * s ^ (5 : ℕ) + (-5 / 4 : ℂ) * s ^ (6 : ℕ)) / (r ^ (4 : ℕ)))

/-- Twisted radial derivative `D = ∂_r + 2s/(r(r²−1))` of `vvSourceTR`. -/
def vvSourceTR1 (s r μ : ℂ) : ℂ :=
  (((5 / 2 : ℂ) * s ^ (2 : ℕ) * μ + (-7 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) * μ + (-15 : ℂ) * s ^ (3 : ℕ) + (17 / 2 : ℂ) * s ^ (3 : ℕ) * μ + (33 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-27 / 2 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) * μ + (-20 : ℂ) * s ^ (3 : ℕ) * r ^ (4 : ℕ) + (5 : ℂ) * s ^ (3 : ℕ) * r ^ (4 : ℕ) * μ + (-67 / 2 : ℂ) * s ^ (4 : ℕ) + (11 / 2 : ℂ) * s ^ (4 : ℕ) * μ + (129 / 2 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (-11 / 2 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) * μ + (-30 : ℂ) * s ^ (4 : ℕ) * r ^ (4 : ℕ) + (-26 : ℂ) * s ^ (5 : ℕ) + (1 : ℂ) * s ^ (5 : ℕ) * μ + (39 : ℂ) * s ^ (5 : ℕ) * r ^ (2 : ℕ) + (-10 : ℂ) * s ^ (5 : ℕ) * r ^ (4 : ℕ) + (-17 / 2 : ℂ) * s ^ (6 : ℕ) + (15 / 2 : ℂ) * s ^ (6 : ℕ) * r ^ (2 : ℕ) + (-1 : ℂ) * s ^ (7 : ℕ)) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)))

/-- Twisted radial derivative `D = ∂_r + 2s/(r(r²−1))` of `vvSourceRR`. -/
def vvSourceRR1 (s r μ : ℂ) : ℂ :=
  (((-21 : ℂ) * s ^ (2 : ℕ) + (15 / 4 : ℂ) * s ^ (2 : ℕ) * μ + (3 / 4 : ℂ) * s ^ (2 : ℕ) * μ ^ (2 : ℕ) + (73 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-51 / 4 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) * μ + (-7 / 4 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) * μ ^ (2 : ℕ) + (-88 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (16 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) * μ + (1 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) * μ ^ (2 : ℕ) + (36 : ℂ) * s ^ (2 : ℕ) * r ^ (6 : ℕ) + (-9 : ℂ) * s ^ (2 : ℕ) * r ^ (6 : ℕ) * μ + (-107 / 2 : ℂ) * s ^ (3 : ℕ) + (11 / 4 : ℂ) * s ^ (3 : ℕ) * μ + (1 / 4 : ℂ) * s ^ (3 : ℕ) * μ ^ (2 : ℕ) + (335 / 2 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-19 / 4 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) * μ + (-1 / 4 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) * μ ^ (2 : ℕ) + (-172 : ℂ) * s ^ (3 : ℕ) * r ^ (4 : ℕ) + (1 : ℂ) * s ^ (3 : ℕ) * r ^ (4 : ℕ) * μ + (54 : ℂ) * s ^ (3 : ℕ) * r ^ (6 : ℕ) + (-97 / 2 : ℂ) * s ^ (4 : ℕ) + (-1 / 4 : ℂ) * s ^ (4 : ℕ) * μ + (253 / 2 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (17 / 4 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) * μ + (-96 : ℂ) * s ^ (4 : ℕ) * r ^ (4 : ℕ) + (-5 : ℂ) * s ^ (4 : ℕ) * r ^ (4 : ℕ) * μ + (18 : ℂ) * s ^ (4 : ℕ) * r ^ (6 : ℕ) + (-37 / 2 : ℂ) * s ^ (5 : ℕ) + (-1 / 4 : ℂ) * s ^ (5 : ℕ) * μ + (63 / 2 : ℂ) * s ^ (5 : ℕ) * r ^ (2 : ℕ) + (5 / 4 : ℂ) * s ^ (5 : ℕ) * r ^ (2 : ℕ) * μ + (-8 : ℂ) * s ^ (5 : ℕ) * r ^ (4 : ℕ) + (-5 / 2 : ℂ) * s ^ (6 : ℕ) + (-3 / 2 : ℂ) * s ^ (6 : ℕ) * r ^ (2 : ℕ) + (4 : ℂ) * s ^ (6 : ℕ) * r ^ (4 : ℕ) + (-1 : ℂ) * s ^ (7 : ℕ) * r ^ (2 : ℕ)) / (r ^ (7 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ)))

/-- Twisted radial derivative `D = ∂_r + 2s/(r(r²−1))` of `vvSourceR`. -/
def vvSourceR1 (s r μ : ℂ) : ℂ :=
  (((-5 / 2 : ℂ) * s ^ (2 : ℕ) + (5 / 2 : ℂ) * s ^ (2 : ℕ) * μ + (19 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-5 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) * μ + (-10 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (5 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) * μ + (-29 / 4 : ℂ) * s ^ (3 : ℕ) + (9 / 4 : ℂ) * s ^ (3 : ℕ) * μ + (87 / 4 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-11 / 4 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) * μ + (-15 : ℂ) * s ^ (3 : ℕ) * r ^ (4 : ℕ) + (-15 / 2 : ℂ) * s ^ (4 : ℕ) + (1 / 2 : ℂ) * s ^ (4 : ℕ) * μ + (16 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (-5 : ℂ) * s ^ (4 : ℕ) * r ^ (4 : ℕ) + (-13 / 4 : ℂ) * s ^ (5 : ℕ) + (15 / 4 : ℂ) * s ^ (5 : ℕ) * r ^ (2 : ℕ) + (-1 / 2 : ℂ) * s ^ (6 : ℕ)) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)))

/-- Twisted radial derivative `D = ∂_r + 2s/(r(r²−1))` of `vvSourceT`. -/
def vvSourceT1 (s r μ : ℂ) : ℂ :=
  (((6 : ℂ) * s ^ (2 : ℕ) + (-6 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (10 : ℂ) * s ^ (3 : ℕ) + (1 : ℂ) * s ^ (3 : ℕ) * μ + (-7 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-1 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) * μ + (7 / 2 : ℂ) * s ^ (4 : ℕ) + (1 / 2 : ℂ) * s ^ (4 : ℕ) * μ + (-1 : ℂ) * s ^ (5 : ℕ) + (1 : ℂ) * s ^ (5 : ℕ) * r ^ (2 : ℕ) + (-1 / 2 : ℂ) * s ^ (6 : ℕ)) / (r ^ (5 : ℕ) * (r ^ (2 : ℕ) - 1)))

/-- Twisted radial derivative `D = ∂_r + 2s/(r(r²−1))` of `vvSourceTF`. -/
def vvSourceTF1 (s r μ : ℂ) : ℂ :=
  (((-44 : ℂ) * s ^ (2 : ℕ) + (44 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-136 : ℂ) * s ^ (3 : ℕ) + (114 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-163 : ℂ) * s ^ (4 : ℕ) + (106 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (-95 : ℂ) * s ^ (5 : ℕ) + (42 : ℂ) * s ^ (5 : ℕ) * r ^ (2 : ℕ) + (-27 : ℂ) * s ^ (6 : ℕ) + (6 : ℂ) * s ^ (6 : ℕ) * r ^ (2 : ℕ) + (-3 : ℂ) * s ^ (7 : ℕ)) / (r ^ (5 : ℕ) * (r ^ (2 : ℕ) - 1) * (2 - μ)))

/-- Second twisted radial derivative of `vvSourceTF`. -/
def vvSourceTF2 (s r μ : ℂ) : ℂ :=
  (((-220 : ℂ) * s ^ (2 : ℕ) + (440 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-220 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (-768 : ℂ) * s ^ (3 : ℕ) + (1382 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-570 : ℂ) * s ^ (3 : ℕ) * r ^ (4 : ℕ) + (-1087 : ℂ) * s ^ (4 : ℕ) + (1687 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (-530 : ℂ) * s ^ (4 : ℕ) * r ^ (4 : ℕ) + (-801 : ℂ) * s ^ (5 : ℕ) + (1003 : ℂ) * s ^ (5 : ℕ) * r ^ (2 : ℕ) + (-210 : ℂ) * s ^ (5 : ℕ) * r ^ (4 : ℕ) + (-325 : ℂ) * s ^ (6 : ℕ) + (291 : ℂ) * s ^ (6 : ℕ) * r ^ (2 : ℕ) + (-30 : ℂ) * s ^ (6 : ℕ) * r ^ (4 : ℕ) + (-69 : ℂ) * s ^ (7 : ℕ) + (33 : ℂ) * s ^ (7 : ℕ) * r ^ (2 : ℕ) + (-6 : ℂ) * s ^ (8 : ℕ)) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ) * (2 - μ)))

/-- The master source of the sourced master equation, per `B²`. -/
def vvMasterSource (s r μ : ℂ) : ℂ :=
  (((-24 : ℂ) * s + (14 : ℂ) * s * μ + (-1 : ℂ) * s * μ ^ (2 : ℕ) + (12 : ℂ) * s * r ^ (2 : ℕ) + (-6 : ℂ) * s * r ^ (2 : ℕ) * μ + (248 : ℂ) * s ^ (2 : ℕ) + (-3 : ℂ) * s ^ (2 : ℕ) * μ + (-13 / 2 : ℂ) * s ^ (2 : ℕ) * μ ^ (2 : ℕ) + (1 / 2 : ℂ) * s ^ (2 : ℕ) * μ ^ (3 : ℕ) + (-102 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-17 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) * μ + (1 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) * μ ^ (2 : ℕ) + (1046 : ℂ) * s ^ (3 : ℕ) + (-74 : ℂ) * s ^ (3 : ℕ) * μ + (-5 : ℂ) * s ^ (3 : ℕ) * μ ^ (2 : ℕ) + (-318 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-12 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) * μ + (1594 : ℂ) * s ^ (4 : ℕ) + (-86 : ℂ) * s ^ (4 : ℕ) * μ + (-3 / 2 : ℂ) * s ^ (4 : ℕ) * μ ^ (2 : ℕ) + (-312 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (-3 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) * μ + (1252 : ℂ) * s ^ (5 : ℕ) + (-36 : ℂ) * s ^ (5 : ℕ) * μ + (-126 : ℂ) * s ^ (5 : ℕ) * r ^ (2 : ℕ) + (546 : ℂ) * s ^ (6 : ℕ) + (-5 : ℂ) * s ^ (6 : ℕ) * μ + (-18 : ℂ) * s ^ (6 : ℕ) * r ^ (2 : ℕ) + (126 : ℂ) * s ^ (7 : ℕ) + (12 : ℂ) * s ^ (8 : ℕ)) / (r ^ (5 : ℕ) * (r ^ (2 : ℕ) - 1) * (2 - μ)))

/-- Harmonic time Bianchi identity of the source: `−(2s/f)τ_tt + (2r + 2f/r)τ_tr + f·Dτ_tr + (μ/r²)τ_t = 0`. -/
theorem vvSource_bianchiT (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    -(2 * s / (r ^ (2 : ℕ) - 1)) * vvSourceTT s r μ + (2 * r + 2 * (r ^ (2 : ℕ) - 1) / r) * vvSourceTR s r μ +
      (r ^ (2 : ℕ) - 1) * vvSourceTR1 s r μ + μ / r ^ (2 : ℕ) * vvSourceT s r μ = 0 := by
  unfold vvSourceTT vvSourceTR vvSourceTR1 vvSourceT
  field_simp
  ring

/-- Harmonic radial Bianchi identity of the source. -/
theorem vvSource_bianchiR (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    r / (r ^ (2 : ℕ) - 1) ^ (2 : ℕ) * vvSourceTT s r μ - 2 * s / (r ^ (2 : ℕ) - 1) * vvSourceTR s r μ +
      (r ^ (2 : ℕ) - 1) * vvSourceRR1 s r μ + (3 * r + 2 * (r ^ (2 : ℕ) - 1) / r) * vvSourceRR s r μ +
      μ / r ^ (2 : ℕ) * vvSourceR s r μ - 2 / r ^ (3 : ℕ) * vvSourceL s r μ = 0 := by
  unfold vvSourceTT vvSourceTR vvSourceRR1 vvSourceRR vvSourceR vvSourceL
  field_simp
  ring

/-- Harmonic angular Bianchi identity of the source. -/
theorem vvSource_bianchiAng (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    -(2 * s / (r ^ (2 : ℕ) - 1)) * vvSourceT s r μ + (r ^ (2 : ℕ) - 1) * vvSourceR1 s r μ +
      (2 * r + 2 * (r ^ (2 : ℕ) - 1) / r) * vvSourceR s r μ + (μ - 2) / (2 * r ^ (2 : ℕ)) * vvSourceTF s r μ +
      1 / r ^ (2 : ℕ) * vvSourceL s r μ = 0 := by
  unfold vvSourceT vvSourceR1 vvSourceR vvSourceTF vvSourceL
  field_simp
  ring

/-- The master identity applied to the source coefficients gives the master source. -/
theorem vvSource_masterSource (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    -(2 * r) / (r ^ (2 : ℕ) - 1) ^ (2 : ℕ) * vvSourceTT s r μ + 2 / s * vvSourceTR s r μ + 2 * r * vvSourceRR s r μ +
      -(4 * r) / (s * (r ^ (2 : ℕ) - 1)) * vvSourceT s r μ + 4 * vvSourceR s r μ +
      (4 / r + 4 * μ / (r * (r ^ (2 : ℕ) - 1)) - 8 * s ^ (2 : ℕ) * r / (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * vvSourceTF s r μ +
      -(2 / s) * vvSourceT1 s r μ + (8 * r ^ (2 : ℕ) - 4) / (r ^ (2 : ℕ) - 1) * vvSourceTF1 s r μ +
      2 * r * vvSourceTF2 s r μ = vvMasterSource s r μ := by
  unfold vvSourceTT vvSourceTR vvSourceRR vvSourceT vvSourceR vvSourceTF vvSourceT1 vvSourceTF1 vvSourceTF2
    vvMasterSource
  field_simp
  ring

end
end RHTower.D4BMScalarStream
