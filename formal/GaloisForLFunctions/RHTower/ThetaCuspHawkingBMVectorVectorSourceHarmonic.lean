import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMScalarStreamSourceHarmonic

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
  (((-9 / 2 : ℂ) * s ^ 2 + (15 / 8 : ℂ) * s ^ 2 * μ + (-1 / 8 : ℂ) * s ^ 2 * μ ^ 2 + (13 / 2 : ℂ) * s ^ 2 * r ^ 2 + (-15 / 8 : ℂ) * s ^ 2 * r ^ 2 * μ + (1 / 8 : ℂ) * s ^ 2 * r ^ 2 * μ ^ 2 + (-2 : ℂ) * s ^ 2 * r ^ 4 + (1 / 2 : ℂ) * s ^ 2 * r ^ 4 * μ + (-45 / 4 : ℂ) * s ^ 3 + (9 / 4 : ℂ) * s ^ 3 * μ + (61 / 4 : ℂ) * s ^ 3 * r ^ 2 + (-7 / 4 : ℂ) * s ^ 3 * r ^ 2 * μ + (-3 : ℂ) * s ^ 3 * r ^ 4 + (-10 : ℂ) * s ^ 4 + (5 / 8 : ℂ) * s ^ 4 * μ + (23 / 2 : ℂ) * s ^ 4 * r ^ 2 + (-1 / 8 : ℂ) * s ^ 4 * r ^ 2 * μ + (-1 : ℂ) * s ^ 4 * r ^ 4 + (-15 / 4 : ℂ) * s ^ 5 + (11 / 4 : ℂ) * s ^ 5 * r ^ 2 + (-1 / 2 : ℂ) * s ^ 6) / (r ^ 6))

/-- Harmonic `tr` coefficient of the vector–vector source (per `B²`). -/
def vvSourceTR (s r μ : ℂ) : ℂ :=
  (((1 / 2 : ℂ) * s ^ 2 * μ + (-3 : ℂ) * s ^ 3 + (3 / 2 : ℂ) * s ^ 3 * μ + (4 : ℂ) * s ^ 3 * r ^ 2 + (-1 : ℂ) * s ^ 3 * r ^ 2 * μ + (-11 / 2 : ℂ) * s ^ 4 + (1 / 2 : ℂ) * s ^ 4 * μ + (6 : ℂ) * s ^ 4 * r ^ 2 + (-3 : ℂ) * s ^ 5 + (2 : ℂ) * s ^ 5 * r ^ 2 + (-1 / 2 : ℂ) * s ^ 6) / (r ^ 5 * (r ^ 2 - 1)))

/-- Harmonic `rr` coefficient of the vector–vector source (per `B²`). -/
def vvSourceRR (s r μ : ℂ) : ℂ :=
  (((-7 / 2 : ℂ) * s ^ 2 + (5 / 8 : ℂ) * s ^ 2 * μ + (1 / 8 : ℂ) * s ^ 2 * μ ^ 2 + (19 / 2 : ℂ) * s ^ 2 * r ^ 2 + (-13 / 8 : ℂ) * s ^ 2 * r ^ 2 * μ + (-1 / 8 : ℂ) * s ^ 2 * r ^ 2 * μ ^ 2 + (-6 : ℂ) * s ^ 2 * r ^ 4 + (3 / 2 : ℂ) * s ^ 2 * r ^ 4 * μ + (-31 / 4 : ℂ) * s ^ 3 + (1 / 4 : ℂ) * s ^ 3 * μ + (71 / 4 : ℂ) * s ^ 3 * r ^ 2 + (1 / 4 : ℂ) * s ^ 3 * r ^ 2 * μ + (-9 : ℂ) * s ^ 3 * r ^ 4 + (-11 / 2 : ℂ) * s ^ 4 + (-1 / 8 : ℂ) * s ^ 4 * μ + (9 : ℂ) * s ^ 4 * r ^ 2 + (5 / 8 : ℂ) * s ^ 4 * r ^ 2 * μ + (-3 : ℂ) * s ^ 4 * r ^ 4 + (-5 / 4 : ℂ) * s ^ 5 + (1 / 4 : ℂ) * s ^ 5 * r ^ 2 + (-1 / 2 : ℂ) * s ^ 6 * r ^ 2) / (r ^ 6 * (r ^ 2 - 1) ^ 2))

/-- Harmonic `t` coefficient of the vector–vector source (per `B²`). -/
def vvSourceT (s r μ : ℂ) : ℂ :=
  (((3 / 2 : ℂ) * s ^ 2 + (7 / 4 : ℂ) * s ^ 3 + (1 / 4 : ℂ) * s ^ 3 * μ + (-1 / 4 : ℂ) * s ^ 5) / (r ^ 4))

/-- Harmonic `r` coefficient of the vector–vector source (per `B²`). -/
def vvSourceR (s r μ : ℂ) : ℂ :=
  (((-1 / 2 : ℂ) * s ^ 2 + (1 / 2 : ℂ) * s ^ 2 * μ + (2 : ℂ) * s ^ 2 * r ^ 2 + (-1 / 2 : ℂ) * s ^ 2 * r ^ 2 * μ + (-5 / 4 : ℂ) * s ^ 3 + (1 / 4 : ℂ) * s ^ 3 * μ + (3 : ℂ) * s ^ 3 * r ^ 2 + (-1 : ℂ) * s ^ 4 + (1 : ℂ) * s ^ 4 * r ^ 2 + (-1 / 4 : ℂ) * s ^ 5) / (r ^ 5 * (r ^ 2 - 1)))

/-- Harmonic `T` coefficient of the vector–vector source (per `B²`). -/
def vvSourceTF (s r μ : ℂ) : ℂ :=
  (((-11 : ℂ) * s ^ 2 + (-57 / 2 : ℂ) * s ^ 3 + (-53 / 2 : ℂ) * s ^ 4 + (-21 / 2 : ℂ) * s ^ 5 + (-3 / 2 : ℂ) * s ^ 6) / (r ^ 4 * (2 - μ)))

/-- Harmonic `L` coefficient of the vector–vector source (per `B²`). -/
def vvSourceL (s r μ : ℂ) : ℂ :=
  (((-7 : ℂ) * s ^ 2 + (3 / 2 : ℂ) * s ^ 2 * μ + (2 : ℂ) * s ^ 2 * r ^ 2 + (-1 / 2 : ℂ) * s ^ 2 * r ^ 2 * μ + (-19 : ℂ) * s ^ 3 + (7 / 4 : ℂ) * s ^ 3 * μ + (3 : ℂ) * s ^ 3 * r ^ 2 + (-75 / 4 : ℂ) * s ^ 4 + (1 / 2 : ℂ) * s ^ 4 * μ + (1 : ℂ) * s ^ 4 * r ^ 2 + (-8 : ℂ) * s ^ 5 + (-5 / 4 : ℂ) * s ^ 6) / (r ^ 4))

/-- Twisted radial derivative `D = ∂_r + 2s/(r(r²−1))` of `vvSourceTR`. -/
def vvSourceTR1 (s r μ : ℂ) : ℂ :=
  (((5 / 2 : ℂ) * s ^ 2 * μ + (-7 / 2 : ℂ) * s ^ 2 * r ^ 2 * μ + (-15 : ℂ) * s ^ 3 + (17 / 2 : ℂ) * s ^ 3 * μ + (33 : ℂ) * s ^ 3 * r ^ 2 + (-27 / 2 : ℂ) * s ^ 3 * r ^ 2 * μ + (-20 : ℂ) * s ^ 3 * r ^ 4 + (5 : ℂ) * s ^ 3 * r ^ 4 * μ + (-67 / 2 : ℂ) * s ^ 4 + (11 / 2 : ℂ) * s ^ 4 * μ + (129 / 2 : ℂ) * s ^ 4 * r ^ 2 + (-11 / 2 : ℂ) * s ^ 4 * r ^ 2 * μ + (-30 : ℂ) * s ^ 4 * r ^ 4 + (-26 : ℂ) * s ^ 5 + (1 : ℂ) * s ^ 5 * μ + (39 : ℂ) * s ^ 5 * r ^ 2 + (-10 : ℂ) * s ^ 5 * r ^ 4 + (-17 / 2 : ℂ) * s ^ 6 + (15 / 2 : ℂ) * s ^ 6 * r ^ 2 + (-1 : ℂ) * s ^ 7) / (r ^ 6 * (r ^ 2 - 1) ^ 2))

/-- Twisted radial derivative `D = ∂_r + 2s/(r(r²−1))` of `vvSourceRR`. -/
def vvSourceRR1 (s r μ : ℂ) : ℂ :=
  (((-21 : ℂ) * s ^ 2 + (15 / 4 : ℂ) * s ^ 2 * μ + (3 / 4 : ℂ) * s ^ 2 * μ ^ 2 + (73 : ℂ) * s ^ 2 * r ^ 2 + (-51 / 4 : ℂ) * s ^ 2 * r ^ 2 * μ + (-7 / 4 : ℂ) * s ^ 2 * r ^ 2 * μ ^ 2 + (-88 : ℂ) * s ^ 2 * r ^ 4 + (16 : ℂ) * s ^ 2 * r ^ 4 * μ + (1 : ℂ) * s ^ 2 * r ^ 4 * μ ^ 2 + (36 : ℂ) * s ^ 2 * r ^ 6 + (-9 : ℂ) * s ^ 2 * r ^ 6 * μ + (-107 / 2 : ℂ) * s ^ 3 + (11 / 4 : ℂ) * s ^ 3 * μ + (1 / 4 : ℂ) * s ^ 3 * μ ^ 2 + (335 / 2 : ℂ) * s ^ 3 * r ^ 2 + (-19 / 4 : ℂ) * s ^ 3 * r ^ 2 * μ + (-1 / 4 : ℂ) * s ^ 3 * r ^ 2 * μ ^ 2 + (-172 : ℂ) * s ^ 3 * r ^ 4 + (1 : ℂ) * s ^ 3 * r ^ 4 * μ + (54 : ℂ) * s ^ 3 * r ^ 6 + (-97 / 2 : ℂ) * s ^ 4 + (-1 / 4 : ℂ) * s ^ 4 * μ + (253 / 2 : ℂ) * s ^ 4 * r ^ 2 + (17 / 4 : ℂ) * s ^ 4 * r ^ 2 * μ + (-96 : ℂ) * s ^ 4 * r ^ 4 + (-5 : ℂ) * s ^ 4 * r ^ 4 * μ + (18 : ℂ) * s ^ 4 * r ^ 6 + (-37 / 2 : ℂ) * s ^ 5 + (-1 / 4 : ℂ) * s ^ 5 * μ + (63 / 2 : ℂ) * s ^ 5 * r ^ 2 + (5 / 4 : ℂ) * s ^ 5 * r ^ 2 * μ + (-8 : ℂ) * s ^ 5 * r ^ 4 + (-5 / 2 : ℂ) * s ^ 6 + (-3 / 2 : ℂ) * s ^ 6 * r ^ 2 + (4 : ℂ) * s ^ 6 * r ^ 4 + (-1 : ℂ) * s ^ 7 * r ^ 2) / (r ^ 7 * (r ^ 2 - 1) ^ 3))

/-- Twisted radial derivative `D = ∂_r + 2s/(r(r²−1))` of `vvSourceR`. -/
def vvSourceR1 (s r μ : ℂ) : ℂ :=
  (((-5 / 2 : ℂ) * s ^ 2 + (5 / 2 : ℂ) * s ^ 2 * μ + (19 / 2 : ℂ) * s ^ 2 * r ^ 2 + (-5 : ℂ) * s ^ 2 * r ^ 2 * μ + (-10 : ℂ) * s ^ 2 * r ^ 4 + (5 / 2 : ℂ) * s ^ 2 * r ^ 4 * μ + (-29 / 4 : ℂ) * s ^ 3 + (9 / 4 : ℂ) * s ^ 3 * μ + (87 / 4 : ℂ) * s ^ 3 * r ^ 2 + (-11 / 4 : ℂ) * s ^ 3 * r ^ 2 * μ + (-15 : ℂ) * s ^ 3 * r ^ 4 + (-15 / 2 : ℂ) * s ^ 4 + (1 / 2 : ℂ) * s ^ 4 * μ + (16 : ℂ) * s ^ 4 * r ^ 2 + (-5 : ℂ) * s ^ 4 * r ^ 4 + (-13 / 4 : ℂ) * s ^ 5 + (15 / 4 : ℂ) * s ^ 5 * r ^ 2 + (-1 / 2 : ℂ) * s ^ 6) / (r ^ 6 * (r ^ 2 - 1) ^ 2))

/-- Twisted radial derivative `D = ∂_r + 2s/(r(r²−1))` of `vvSourceT`. -/
def vvSourceT1 (s r μ : ℂ) : ℂ :=
  (((6 : ℂ) * s ^ 2 + (-6 : ℂ) * s ^ 2 * r ^ 2 + (10 : ℂ) * s ^ 3 + (1 : ℂ) * s ^ 3 * μ + (-7 : ℂ) * s ^ 3 * r ^ 2 + (-1 : ℂ) * s ^ 3 * r ^ 2 * μ + (7 / 2 : ℂ) * s ^ 4 + (1 / 2 : ℂ) * s ^ 4 * μ + (-1 : ℂ) * s ^ 5 + (1 : ℂ) * s ^ 5 * r ^ 2 + (-1 / 2 : ℂ) * s ^ 6) / (r ^ 5 * (r ^ 2 - 1)))

/-- Twisted radial derivative `D = ∂_r + 2s/(r(r²−1))` of `vvSourceTF`. -/
def vvSourceTF1 (s r μ : ℂ) : ℂ :=
  (((-44 : ℂ) * s ^ 2 + (44 : ℂ) * s ^ 2 * r ^ 2 + (-136 : ℂ) * s ^ 3 + (114 : ℂ) * s ^ 3 * r ^ 2 + (-163 : ℂ) * s ^ 4 + (106 : ℂ) * s ^ 4 * r ^ 2 + (-95 : ℂ) * s ^ 5 + (42 : ℂ) * s ^ 5 * r ^ 2 + (-27 : ℂ) * s ^ 6 + (6 : ℂ) * s ^ 6 * r ^ 2 + (-3 : ℂ) * s ^ 7) / (r ^ 5 * (r ^ 2 - 1) * (2 - μ)))

/-- Second twisted radial derivative of `vvSourceTF`. -/
def vvSourceTF2 (s r μ : ℂ) : ℂ :=
  (((-220 : ℂ) * s ^ 2 + (440 : ℂ) * s ^ 2 * r ^ 2 + (-220 : ℂ) * s ^ 2 * r ^ 4 + (-768 : ℂ) * s ^ 3 + (1382 : ℂ) * s ^ 3 * r ^ 2 + (-570 : ℂ) * s ^ 3 * r ^ 4 + (-1087 : ℂ) * s ^ 4 + (1687 : ℂ) * s ^ 4 * r ^ 2 + (-530 : ℂ) * s ^ 4 * r ^ 4 + (-801 : ℂ) * s ^ 5 + (1003 : ℂ) * s ^ 5 * r ^ 2 + (-210 : ℂ) * s ^ 5 * r ^ 4 + (-325 : ℂ) * s ^ 6 + (291 : ℂ) * s ^ 6 * r ^ 2 + (-30 : ℂ) * s ^ 6 * r ^ 4 + (-69 : ℂ) * s ^ 7 + (33 : ℂ) * s ^ 7 * r ^ 2 + (-6 : ℂ) * s ^ 8) / (r ^ 6 * (r ^ 2 - 1) ^ 2 * (2 - μ)))

/-- The master source of the sourced master equation, per `B²`. -/
def vvMasterSource (s r μ : ℂ) : ℂ :=
  (((-24 : ℂ) * s + (14 : ℂ) * s * μ + (-1 : ℂ) * s * μ ^ 2 + (12 : ℂ) * s * r ^ 2 + (-6 : ℂ) * s * r ^ 2 * μ + (248 : ℂ) * s ^ 2 + (-3 : ℂ) * s ^ 2 * μ + (-13 / 2 : ℂ) * s ^ 2 * μ ^ 2 + (1 / 2 : ℂ) * s ^ 2 * μ ^ 3 + (-102 : ℂ) * s ^ 2 * r ^ 2 + (-17 : ℂ) * s ^ 2 * r ^ 2 * μ + (1 : ℂ) * s ^ 2 * r ^ 2 * μ ^ 2 + (1046 : ℂ) * s ^ 3 + (-74 : ℂ) * s ^ 3 * μ + (-5 : ℂ) * s ^ 3 * μ ^ 2 + (-318 : ℂ) * s ^ 3 * r ^ 2 + (-12 : ℂ) * s ^ 3 * r ^ 2 * μ + (1594 : ℂ) * s ^ 4 + (-86 : ℂ) * s ^ 4 * μ + (-3 / 2 : ℂ) * s ^ 4 * μ ^ 2 + (-312 : ℂ) * s ^ 4 * r ^ 2 + (-3 : ℂ) * s ^ 4 * r ^ 2 * μ + (1252 : ℂ) * s ^ 5 + (-36 : ℂ) * s ^ 5 * μ + (-126 : ℂ) * s ^ 5 * r ^ 2 + (546 : ℂ) * s ^ 6 + (-5 : ℂ) * s ^ 6 * μ + (-18 : ℂ) * s ^ 6 * r ^ 2 + (126 : ℂ) * s ^ 7 + (12 : ℂ) * s ^ 8) / (r ^ 5 * (r ^ 2 - 1) * (2 - μ)))

/-- Harmonic time Bianchi identity of the source: `−(2s/f)τ_tt + (2r + 2f/r)τ_tr + f·Dτ_tr + (μ/r²)τ_t = 0`. -/
theorem vvSource_bianchiT (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    -(2 * s / (r ^ 2 - 1)) * vvSourceTT s r μ + (2 * r + 2 * (r ^ 2 - 1) / r) * vvSourceTR s r μ +
      (r ^ 2 - 1) * vvSourceTR1 s r μ + μ / r ^ 2 * vvSourceT s r μ = 0 := by
  unfold vvSourceTT vvSourceTR vvSourceTR1 vvSourceT
  field_simp
  ring

/-- Harmonic radial Bianchi identity of the source. -/
theorem vvSource_bianchiR (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    r / (r ^ 2 - 1) ^ 2 * vvSourceTT s r μ - 2 * s / (r ^ 2 - 1) * vvSourceTR s r μ +
      (r ^ 2 - 1) * vvSourceRR1 s r μ + (3 * r + 2 * (r ^ 2 - 1) / r) * vvSourceRR s r μ +
      μ / r ^ 2 * vvSourceR s r μ - 2 / r ^ 3 * vvSourceL s r μ = 0 := by
  unfold vvSourceTT vvSourceTR vvSourceRR1 vvSourceRR vvSourceR vvSourceL
  field_simp
  ring

/-- Harmonic angular Bianchi identity of the source. -/
theorem vvSource_bianchiAng (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    -(2 * s / (r ^ 2 - 1)) * vvSourceT s r μ + (r ^ 2 - 1) * vvSourceR1 s r μ +
      (2 * r + 2 * (r ^ 2 - 1) / r) * vvSourceR s r μ + (μ - 2) / (2 * r ^ 2) * vvSourceTF s r μ +
      1 / r ^ 2 * vvSourceL s r μ = 0 := by
  unfold vvSourceT vvSourceR1 vvSourceR vvSourceTF vvSourceL
  field_simp
  ring

/-- The master identity applied to the source coefficients gives the master source. -/
theorem vvSource_masterSource (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    -(2 * r) / (r ^ 2 - 1) ^ 2 * vvSourceTT s r μ + 2 / s * vvSourceTR s r μ + 2 * r * vvSourceRR s r μ +
      -(4 * r) / (s * (r ^ 2 - 1)) * vvSourceT s r μ + 4 * vvSourceR s r μ +
      (4 / r + 4 * μ / (r * (r ^ 2 - 1)) - 8 * s ^ 2 * r / (r ^ 2 - 1) ^ 2) * vvSourceTF s r μ +
      -(2 / s) * vvSourceT1 s r μ + (8 * r ^ 2 - 4) / (r ^ 2 - 1) * vvSourceTF1 s r μ +
      2 * r * vvSourceTF2 s r μ = vvMasterSource s r μ := by
  unfold vvSourceTT vvSourceTR vvSourceRR vvSourceT vvSourceR vvSourceTF vvSourceT1 vvSourceTF1 vvSourceTF2
    vvMasterSource
  field_simp
  ring

end
end RHTower.D4BMScalarStream
