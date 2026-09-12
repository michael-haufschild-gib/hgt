import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMScalarStreamMasterIdentity

/-!
# Sourced Kodama–Ishibashi reconstruction of the harmonic scalar stream (jet level)

For one angular harmonic (`ΔY = μY`) at time rate `2s`, let `τ_A` (`A ∈ {tt, tr, rr, t, r, T, L}`)
be the seven harmonic coefficients of a source tensor and `q{A}{k}` the symbols standing for its
`k`-th radial derivatives. Given a master jet `(P, P1, P2, P3, P4)`, the Kodama–Ishibashi radial
functions are reconstructed as explicit linear combinations `recF0, recF1, recF2, recH` (with
formal radial derivatives) of the master jet and the source jets, by solving the trace-free, mixed
`(t,i)` and orbit `(t,r)` equations exactly. The main theorems express every harmonic Einstein
coefficient of the reconstructed jet, plus its source, as an explicit combination of the sourced
master defect `masterDefect0 = P'' + (2r/(r²−1))P' + (μ/(r²(r²−1)) − 4s²/(r²−1)²)P + σ(τ)` and its
formal derivatives, and of the three Bianchi forms of the source (`bianchiT`, `bianchiR`,
`bianchiAng`) and their formal derivatives. For a conserved source on the sourced master shell all
seven sourced equations therefore hold. Every identity is a closed rational identity.
-/

set_option linter.unusedVariables false

namespace RHTower.D4BMScalarStream
open GaloisForLFunctions.HTGeometry CoordinateMetricTwoJet
noncomputable section

/-- Reconstructed `F0` from the master jet and the source jets. -/
def recF0 (s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4 : ℂ) : ℂ :=
  (((-1 / 2 : ℂ) * μ + (1 / 2 : ℂ) * r ^ 2 * μ) / (r * (2 - μ))) * P + (((1 : ℂ) + (-3 : ℂ) * r ^ 2 + (2 : ℂ) * r ^ 4) / ((2 - μ))) * P1 + (((1 : ℂ) * r + (-2 : ℂ) * r ^ 3 + (1 : ℂ) * r ^ 5) / ((2 - μ))) * P2 + (((-1 : ℂ) * r + (4 : ℂ) * r ^ 3 + (-3 : ℂ) * r ^ 5) / ((2 - μ) * s)) * qtr0 + (((-1 : ℂ) * r ^ 2 + (2 : ℂ) * r ^ 4 + (-1 : ℂ) * r ^ 6) / ((2 - μ) * s)) * qtr1 + (((-2 : ℂ) + (1 : ℂ) * μ + (6 : ℂ) * r ^ 2 + (-1 : ℂ) * r ^ 2 * μ + (-4 : ℂ) * r ^ 4) / ((2 - μ) * s)) * qt0 + (((-2 : ℂ) * r + (4 : ℂ) * r ^ 3 + (-2 : ℂ) * r ^ 5) / ((2 - μ) * s)) * qt1 + (((6 : ℂ) + (-3 : ℂ) * μ + (-10 : ℂ) * r ^ 2 + (3 : ℂ) * r ^ 2 * μ + (4 : ℂ) * r ^ 4) / ((2 - μ))) * qT0 + (((6 : ℂ) * r + (-14 : ℂ) * r ^ 3 + (8 : ℂ) * r ^ 5) / ((2 - μ))) * qT1 + (((2 : ℂ) * r ^ 2 + (-4 : ℂ) * r ^ 4 + (2 : ℂ) * r ^ 6) / ((2 - μ))) * qT2

/-- Reconstructed `F01` from the master jet and the source jets. -/
def recF01 (s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4 : ℂ) : ℂ :=
  (((1 / 2 : ℂ) * μ + (1 / 2 : ℂ) * r ^ 2 * μ) / (r ^ 2 * (2 - μ))) * P + (((-1 / 2 : ℂ) * μ + (-6 : ℂ) * r ^ 2 + (1 / 2 : ℂ) * r ^ 2 * μ + (8 : ℂ) * r ^ 4) / (r * (2 - μ))) * P1 + (((2 : ℂ) + (-9 : ℂ) * r ^ 2 + (7 : ℂ) * r ^ 4) / ((2 - μ))) * P2 + (((1 : ℂ) * r + (-2 : ℂ) * r ^ 3 + (1 : ℂ) * r ^ 5) / ((2 - μ))) * P3 + (((-1 : ℂ) + (12 : ℂ) * r ^ 2 + (-15 : ℂ) * r ^ 4) / ((2 - μ) * s)) * qtr0 + (((-3 : ℂ) * r + (12 : ℂ) * r ^ 3 + (-9 : ℂ) * r ^ 5) / ((2 - μ) * s)) * qtr1 + (((-1 : ℂ) * r ^ 2 + (2 : ℂ) * r ^ 4 + (-1 : ℂ) * r ^ 6) / ((2 - μ) * s)) * qtr2 + (((12 : ℂ) * r + (-2 : ℂ) * r * μ + (-16 : ℂ) * r ^ 3) / ((2 - μ) * s)) * qt0 + (((-4 : ℂ) + (1 : ℂ) * μ + (18 : ℂ) * r ^ 2 + (-1 : ℂ) * r ^ 2 * μ + (-14 : ℂ) * r ^ 4) / ((2 - μ) * s)) * qt1 + (((-2 : ℂ) * r + (4 : ℂ) * r ^ 3 + (-2 : ℂ) * r ^ 5) / ((2 - μ) * s)) * qt2 + (((-20 : ℂ) * r + (6 : ℂ) * r * μ + (16 : ℂ) * r ^ 3) / ((2 - μ))) * qT0 + (((12 : ℂ) + (-3 : ℂ) * μ + (-52 : ℂ) * r ^ 2 + (3 : ℂ) * r ^ 2 * μ + (44 : ℂ) * r ^ 4) / ((2 - μ))) * qT1 + (((10 : ℂ) * r + (-30 : ℂ) * r ^ 3 + (20 : ℂ) * r ^ 5) / ((2 - μ))) * qT2 + (((2 : ℂ) * r ^ 2 + (-4 : ℂ) * r ^ 4 + (2 : ℂ) * r ^ 6) / ((2 - μ))) * qT3

/-- Reconstructed `F02` from the master jet and the source jets. -/
def recF02 (s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4 : ℂ) : ℂ :=
  (((-1 : ℂ) * μ) / (r ^ 3 * (2 - μ))) * P + (((1 : ℂ) * μ + (-6 : ℂ) * r ^ 2 + (1 : ℂ) * r ^ 2 * μ + (24 : ℂ) * r ^ 4) / (r ^ 2 * (2 - μ))) * P1 + (((-1 / 2 : ℂ) * μ + (-24 : ℂ) * r ^ 2 + (1 / 2 : ℂ) * r ^ 2 * μ + (36 : ℂ) * r ^ 4) / (r * (2 - μ))) * P2 + (((3 : ℂ) + (-15 : ℂ) * r ^ 2 + (12 : ℂ) * r ^ 4) / ((2 - μ))) * P3 + (((1 : ℂ) * r + (-2 : ℂ) * r ^ 3 + (1 : ℂ) * r ^ 5) / ((2 - μ))) * P4 + (((24 : ℂ) * r + (-60 : ℂ) * r ^ 3) / ((2 - μ) * s)) * qtr0 + (((-4 : ℂ) + (48 : ℂ) * r ^ 2 + (-60 : ℂ) * r ^ 4) / ((2 - μ) * s)) * qtr1 + (((-5 : ℂ) * r + (20 : ℂ) * r ^ 3 + (-15 : ℂ) * r ^ 5) / ((2 - μ) * s)) * qtr2 + (((-1 : ℂ) * r ^ 2 + (2 : ℂ) * r ^ 4 + (-1 : ℂ) * r ^ 6) / ((2 - μ) * s)) * qtr3 + (((12 : ℂ) + (-2 : ℂ) * μ + (-48 : ℂ) * r ^ 2) / ((2 - μ) * s)) * qt0 + (((48 : ℂ) * r + (-4 : ℂ) * r * μ + (-72 : ℂ) * r ^ 3) / ((2 - μ) * s)) * qt1 + (((-6 : ℂ) + (1 : ℂ) * μ + (30 : ℂ) * r ^ 2 + (-1 : ℂ) * r ^ 2 * μ + (-24 : ℂ) * r ^ 4) / ((2 - μ) * s)) * qt2 + (((-2 : ℂ) * r + (4 : ℂ) * r ^ 3 + (-2 : ℂ) * r ^ 5) / ((2 - μ) * s)) * qt3 + (((-20 : ℂ) + (6 : ℂ) * μ + (48 : ℂ) * r ^ 2) / ((2 - μ))) * qT0 + (((-124 : ℂ) * r + (12 : ℂ) * r * μ + (192 : ℂ) * r ^ 3) / ((2 - μ))) * qT1 + (((22 : ℂ) + (-3 : ℂ) * μ + (-142 : ℂ) * r ^ 2 + (3 : ℂ) * r ^ 2 * μ + (144 : ℂ) * r ^ 4) / ((2 - μ))) * qT2 + (((14 : ℂ) * r + (-46 : ℂ) * r ^ 3 + (32 : ℂ) * r ^ 5) / ((2 - μ))) * qT3 + (((2 : ℂ) * r ^ 2 + (-4 : ℂ) * r ^ 4 + (2 : ℂ) * r ^ 6) / ((2 - μ))) * qT4

/-- Reconstructed `F1` from the master jet and the source jets. -/
def recF1 (s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4 : ℂ) : ℂ :=
  (((-2 : ℂ) * s) / ((r ^ 2 - 1) * (2 - μ))) * P + (((2 : ℂ) * s * r) / ((2 - μ))) * P1 + (((-2 : ℂ) * r ^ 2) / ((2 - μ))) * qtr0 + (((-4 : ℂ) * r) / ((2 - μ))) * qt0 + (((-8 : ℂ) * s * r + (4 : ℂ) * s * r ^ 3) / ((r ^ 2 - 1) * (2 - μ))) * qT0 + (((4 : ℂ) * s * r ^ 2) / ((2 - μ))) * qT1

/-- Reconstructed `F11` from the master jet and the source jets. -/
def recF11 (s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4 : ℂ) : ℂ :=
  (((4 : ℂ) * s * r) / ((r ^ 2 - 1) ^ 2 * (2 - μ))) * P + (((-4 : ℂ) * s + (2 : ℂ) * s * r ^ 2) / ((r ^ 2 - 1) * (2 - μ))) * P1 + (((2 : ℂ) * s * r) / ((2 - μ))) * P2 + (((-4 : ℂ) * r) / ((2 - μ))) * qtr0 + (((-2 : ℂ) * r ^ 2) / ((2 - μ))) * qtr1 + (((-4 : ℂ)) / ((2 - μ))) * qt0 + (((-4 : ℂ) * r) / ((2 - μ))) * qt1 + (((8 : ℂ) * s + (-4 : ℂ) * s * r ^ 2 + (4 : ℂ) * s * r ^ 4) / ((r ^ 2 - 1) ^ 2 * (2 - μ))) * qT0 + (((-16 : ℂ) * s * r + (12 : ℂ) * s * r ^ 3) / ((r ^ 2 - 1) * (2 - μ))) * qT1 + (((4 : ℂ) * s * r ^ 2) / ((2 - μ))) * qT2

/-- Reconstructed `F12` from the master jet and the source jets. -/
def recF12 (s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4 : ℂ) : ℂ :=
  (((-4 : ℂ) * s + (-12 : ℂ) * s * r ^ 2) / ((r ^ 2 - 1) ^ 3 * (2 - μ))) * P + (((8 : ℂ) * s * r) / ((r ^ 2 - 1) ^ 2 * (2 - μ))) * P1 + (((-6 : ℂ) * s + (4 : ℂ) * s * r ^ 2) / ((r ^ 2 - 1) * (2 - μ))) * P2 + (((2 : ℂ) * s * r) / ((2 - μ))) * P3 + (((-4 : ℂ)) / ((2 - μ))) * qtr0 + (((-8 : ℂ) * r) / ((2 - μ))) * qtr1 + (((-2 : ℂ) * r ^ 2) / ((2 - μ))) * qtr2 + (((-8 : ℂ)) / ((2 - μ))) * qt1 + (((-4 : ℂ) * r) / ((2 - μ))) * qt2 + (((-24 : ℂ) * s * r + (-8 : ℂ) * s * r ^ 3) / ((r ^ 2 - 1) ^ 3 * (2 - μ))) * qT0 + (((24 : ℂ) * s + (-24 : ℂ) * s * r ^ 2 + (16 : ℂ) * s * r ^ 4) / ((r ^ 2 - 1) ^ 2 * (2 - μ))) * qT1 + (((-24 : ℂ) * s * r + (20 : ℂ) * s * r ^ 3) / ((r ^ 2 - 1) * (2 - μ))) * qT2 + (((4 : ℂ) * s * r ^ 2) / ((2 - μ))) * qT3

/-- Reconstructed `F2` from the master jet and the source jets. -/
def recF2 (s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4 : ℂ) : ℂ :=
  (((1 / 2 : ℂ) * μ) / (r * (r ^ 2 - 1) * (2 - μ))) * P + (((-1 : ℂ) + (2 : ℂ) * r ^ 2) / ((r ^ 2 - 1) * (2 - μ))) * P1 + (((1 : ℂ) * r) / ((2 - μ))) * P2 + (((1 : ℂ) * r + (-3 : ℂ) * r ^ 3) / ((r ^ 2 - 1) * (2 - μ) * s)) * qtr0 + (((-1 : ℂ) * r ^ 2) / ((2 - μ) * s)) * qtr1 + (((2 : ℂ) + (-1 : ℂ) * μ + (-4 : ℂ) * r ^ 2) / ((r ^ 2 - 1) * (2 - μ) * s)) * qt0 + (((-2 : ℂ) * r) / ((2 - μ) * s)) * qt1 + (((-2 : ℂ) + (1 : ℂ) * μ + (4 : ℂ) * r ^ 2) / ((r ^ 2 - 1) * (2 - μ))) * qT0 + (((-6 : ℂ) * r + (8 : ℂ) * r ^ 3) / ((r ^ 2 - 1) * (2 - μ))) * qT1 + (((2 : ℂ) * r ^ 2) / ((2 - μ))) * qT2

/-- Reconstructed `F21` from the master jet and the source jets. -/
def recF21 (s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4 : ℂ) : ℂ :=
  (((1 / 2 : ℂ) * μ + (-3 / 2 : ℂ) * r ^ 2 * μ) / (r ^ 2 * (r ^ 2 - 1) ^ 2 * (2 - μ))) * P + (((-1 / 2 : ℂ) * μ + (-2 : ℂ) * r ^ 2 + (1 / 2 : ℂ) * r ^ 2 * μ) / (r * (r ^ 2 - 1) ^ 2 * (2 - μ))) * P1 + (((-2 : ℂ) + (3 : ℂ) * r ^ 2) / ((r ^ 2 - 1) * (2 - μ))) * P2 + (((1 : ℂ) * r) / ((2 - μ))) * P3 + (((-1 : ℂ) + (8 : ℂ) * r ^ 2 + (-3 : ℂ) * r ^ 4) / ((r ^ 2 - 1) ^ 2 * (2 - μ) * s)) * qtr0 + (((3 : ℂ) * r + (-5 : ℂ) * r ^ 3) / ((r ^ 2 - 1) * (2 - μ) * s)) * qtr1 + (((-1 : ℂ) * r ^ 2) / ((2 - μ) * s)) * qtr2 + (((4 : ℂ) * r + (2 : ℂ) * r * μ) / ((r ^ 2 - 1) ^ 2 * (2 - μ) * s)) * qt0 + (((4 : ℂ) + (-1 : ℂ) * μ + (-6 : ℂ) * r ^ 2) / ((r ^ 2 - 1) * (2 - μ) * s)) * qt1 + (((-2 : ℂ) * r) / ((2 - μ) * s)) * qt2 + (((-4 : ℂ) * r + (-2 : ℂ) * r * μ) / ((r ^ 2 - 1) ^ 2 * (2 - μ))) * qT0 + (((8 : ℂ) + (-1 : ℂ) * μ + (-24 : ℂ) * r ^ 2 + (1 : ℂ) * r ^ 2 * μ + (12 : ℂ) * r ^ 4) / ((r ^ 2 - 1) ^ 2 * (2 - μ))) * qT1 + (((-10 : ℂ) * r + (12 : ℂ) * r ^ 3) / ((r ^ 2 - 1) * (2 - μ))) * qT2 + (((2 : ℂ) * r ^ 2) / ((2 - μ))) * qT3

/-- Reconstructed `F22` from the master jet and the source jets. -/
def recF22 (s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4 : ℂ) : ℂ :=
  (((1 : ℂ) * μ + (-3 : ℂ) * r ^ 2 * μ + (6 : ℂ) * r ^ 4 * μ) / (r ^ 3 * (r ^ 2 - 1) ^ 3 * (2 - μ))) * P + (((-1 : ℂ) * μ + (2 : ℂ) * r ^ 2 + (4 : ℂ) * r ^ 2 * μ + (6 : ℂ) * r ^ 4 + (-3 : ℂ) * r ^ 4 * μ) / (r ^ 2 * (r ^ 2 - 1) ^ 3 * (2 - μ))) * P1 + (((-1 / 2 : ℂ) * μ + (-4 : ℂ) * r ^ 2 + (1 / 2 : ℂ) * r ^ 2 * μ) / (r * (r ^ 2 - 1) ^ 2 * (2 - μ))) * P2 + (((-3 : ℂ) + (4 : ℂ) * r ^ 2) / ((r ^ 2 - 1) * (2 - μ))) * P3 + (((1 : ℂ) * r) / ((2 - μ))) * P4 + (((-12 : ℂ) * r + (-4 : ℂ) * r ^ 3) / ((r ^ 2 - 1) ^ 3 * (2 - μ) * s)) * qtr0 + (((-4 : ℂ) + (20 : ℂ) * r ^ 2 + (-8 : ℂ) * r ^ 4) / ((r ^ 2 - 1) ^ 2 * (2 - μ) * s)) * qtr1 + (((5 : ℂ) * r + (-7 : ℂ) * r ^ 3) / ((r ^ 2 - 1) * (2 - μ) * s)) * qtr2 + (((-1 : ℂ) * r ^ 2) / ((2 - μ) * s)) * qtr3 + (((-4 : ℂ) + (-2 : ℂ) * μ + (-12 : ℂ) * r ^ 2 + (-6 : ℂ) * r ^ 2 * μ) / ((r ^ 2 - 1) ^ 3 * (2 - μ) * s)) * qt0 + (((8 : ℂ) * r + (4 : ℂ) * r * μ) / ((r ^ 2 - 1) ^ 2 * (2 - μ) * s)) * qt1 + (((6 : ℂ) + (-1 : ℂ) * μ + (-8 : ℂ) * r ^ 2) / ((r ^ 2 - 1) * (2 - μ) * s)) * qt2 + (((-2 : ℂ) * r) / ((2 - μ) * s)) * qt3 + (((4 : ℂ) + (2 : ℂ) * μ + (12 : ℂ) * r ^ 2 + (6 : ℂ) * r ^ 2 * μ) / ((r ^ 2 - 1) ^ 3 * (2 - μ))) * qT0 + (((20 : ℂ) * r + (4 : ℂ) * r * μ + (-4 : ℂ) * r ^ 3 + (-4 : ℂ) * r ^ 3 * μ) / ((r ^ 2 - 1) ^ 3 * (2 - μ))) * qT1 + (((18 : ℂ) + (-1 : ℂ) * μ + (-50 : ℂ) * r ^ 2 + (1 : ℂ) * r ^ 2 * μ + (24 : ℂ) * r ^ 4) / ((r ^ 2 - 1) ^ 2 * (2 - μ))) * qT2 + (((-14 : ℂ) * r + (16 : ℂ) * r ^ 3) / ((r ^ 2 - 1) * (2 - μ))) * qT3 + (((2 : ℂ) * r ^ 2) / ((2 - μ))) * qT4

/-- Reconstructed `H` from the master jet and the source jets. -/
def recH (s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4 : ℂ) : ℂ :=
  (((-1 / 4 : ℂ) * μ) / (r * (2 - μ))) * P + (((-1 / 2 : ℂ) + (1 / 2 : ℂ) * r ^ 2) / ((2 - μ))) * P1 + (((1 / 2 : ℂ) * r + (-1 / 2 : ℂ) * r ^ 3) / ((2 - μ) * s)) * qtr0 + (((1 : ℂ) + (-1 : ℂ) * r ^ 2) / ((2 - μ) * s)) * qt0 + (((-1 : ℂ) + (-1 / 2 : ℂ) * μ + (1 : ℂ) * r ^ 2) / ((2 - μ))) * qT0 + (((-1 : ℂ) * r + (1 : ℂ) * r ^ 3) / ((2 - μ))) * qT1

/-- Reconstructed `H1` from the master jet and the source jets. -/
def recH1 (s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4 : ℂ) : ℂ :=
  (((1 / 4 : ℂ) * μ) / (r ^ 2 * (2 - μ))) * P + (((-1 / 4 : ℂ) * μ + (1 : ℂ) * r ^ 2) / (r * (2 - μ))) * P1 + (((-1 / 2 : ℂ) + (1 / 2 : ℂ) * r ^ 2) / ((2 - μ))) * P2 + (((1 / 2 : ℂ) + (-3 / 2 : ℂ) * r ^ 2) / ((2 - μ) * s)) * qtr0 + (((1 / 2 : ℂ) * r + (-1 / 2 : ℂ) * r ^ 3) / ((2 - μ) * s)) * qtr1 + (((-2 : ℂ) * r) / ((2 - μ) * s)) * qt0 + (((1 : ℂ) + (-1 : ℂ) * r ^ 2) / ((2 - μ) * s)) * qt1 + (((2 : ℂ) * r) / ((2 - μ))) * qT0 + (((-2 : ℂ) + (-1 / 2 : ℂ) * μ + (4 : ℂ) * r ^ 2) / ((2 - μ))) * qT1 + (((-1 : ℂ) * r + (1 : ℂ) * r ^ 3) / ((2 - μ))) * qT2

/-- Reconstructed `H2` from the master jet and the source jets. -/
def recH2 (s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4 : ℂ) : ℂ :=
  (((-1 / 2 : ℂ) * μ) / (r ^ 3 * (2 - μ))) * P + (((1 / 2 : ℂ) * μ + (1 : ℂ) * r ^ 2) / (r ^ 2 * (2 - μ))) * P1 + (((-1 / 4 : ℂ) * μ + (2 : ℂ) * r ^ 2) / (r * (2 - μ))) * P2 + (((-1 / 2 : ℂ) + (1 / 2 : ℂ) * r ^ 2) / ((2 - μ))) * P3 + (((-3 : ℂ) * r) / ((2 - μ) * s)) * qtr0 + (((1 : ℂ) + (-3 : ℂ) * r ^ 2) / ((2 - μ) * s)) * qtr1 + (((1 / 2 : ℂ) * r + (-1 / 2 : ℂ) * r ^ 3) / ((2 - μ) * s)) * qtr2 + (((-2 : ℂ)) / ((2 - μ) * s)) * qt0 + (((-4 : ℂ) * r) / ((2 - μ) * s)) * qt1 + (((1 : ℂ) + (-1 : ℂ) * r ^ 2) / ((2 - μ) * s)) * qt2 + (((2 : ℂ)) / ((2 - μ))) * qT0 + (((10 : ℂ) * r) / ((2 - μ))) * qT1 + (((-3 : ℂ) + (-1 / 2 : ℂ) * μ + (7 : ℂ) * r ^ 2) / ((2 - μ))) * qT2 + (((-1 : ℂ) * r + (1 : ℂ) * r ^ 3) / ((2 - μ))) * qT3

/-- Sourced master defect, formal derivative order `0`. -/
def masterDefect0 (s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4 : ℂ) : ℂ :=
  (((-1 : ℂ) * μ + (1 : ℂ) * r ^ 2 * μ + (-4 : ℂ) * s ^ 2 * r ^ 2) / (r ^ 2 * (r ^ 2 - 1) ^ 2)) * P + (((2 : ℂ) * r) / ((r ^ 2 - 1))) * P1 + ((1 : ℂ)) * P2 + (((-2 : ℂ) * r) / ((r ^ 2 - 1) ^ 2)) * qtt0 + (((2 : ℂ)) / (s)) * qtr0 + ((2 : ℂ) * r) * qrr0 + (((-4 : ℂ) * r) / ((r ^ 2 - 1) * s)) * qt0 + (((-2 : ℂ)) / (s)) * qt1 + ((4 : ℂ)) * qr0 + (((4 : ℂ) + (-4 : ℂ) * μ + (-8 : ℂ) * r ^ 2 + (4 : ℂ) * r ^ 2 * μ + (4 : ℂ) * r ^ 4 + (-8 : ℂ) * s ^ 2 * r ^ 2) / (r * (r ^ 2 - 1) ^ 2)) * qT0 + (((-4 : ℂ) + (8 : ℂ) * r ^ 2) / ((r ^ 2 - 1))) * qT1 + ((2 : ℂ) * r) * qT2

/-- Sourced master defect, formal derivative order `1`. -/
def masterDefect1 (s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4 : ℂ) : ℂ :=
  (((-2 : ℂ) * μ + (6 : ℂ) * r ^ 2 * μ + (-4 : ℂ) * r ^ 4 * μ + (16 : ℂ) * s ^ 2 * r ^ 4) / (r ^ 3 * (r ^ 2 - 1) ^ 3)) * P + (((-1 : ℂ) * μ + (-2 : ℂ) * r ^ 2 + (1 : ℂ) * r ^ 2 * μ + (-2 : ℂ) * r ^ 4 + (-4 : ℂ) * s ^ 2 * r ^ 2) / (r ^ 2 * (r ^ 2 - 1) ^ 2)) * P1 + (((2 : ℂ) * r) / ((r ^ 2 - 1))) * P2 + ((1 : ℂ)) * P3 + (((2 : ℂ) + (6 : ℂ) * r ^ 2) / ((r ^ 2 - 1) ^ 3)) * qtt0 + (((-2 : ℂ) * r) / ((r ^ 2 - 1) ^ 2)) * qtt1 + (((2 : ℂ)) / (s)) * qtr1 + ((2 : ℂ)) * qrr0 + ((2 : ℂ) * r) * qrr1 + (((4 : ℂ) + (4 : ℂ) * r ^ 2) / ((r ^ 2 - 1) ^ 2 * s)) * qt0 + (((-4 : ℂ) * r) / ((r ^ 2 - 1) * s)) * qt1 + (((-2 : ℂ)) / (s)) * qt2 + ((4 : ℂ)) * qr1 + (((4 : ℂ) + (-4 : ℂ) * μ + (-12 : ℂ) * r ^ 2 + (16 : ℂ) * r ^ 2 * μ + (12 : ℂ) * r ^ 4 + (-12 : ℂ) * r ^ 4 * μ + (-4 : ℂ) * r ^ 6 + (8 : ℂ) * s ^ 2 * r ^ 2 + (24 : ℂ) * s ^ 2 * r ^ 4) / (r ^ 2 * (r ^ 2 - 1) ^ 3)) * qT0 + (((4 : ℂ) + (-4 : ℂ) * μ + (-16 : ℂ) * r ^ 2 + (4 : ℂ) * r ^ 2 * μ + (4 : ℂ) * r ^ 4 + (-8 : ℂ) * s ^ 2 * r ^ 2) / (r * (r ^ 2 - 1) ^ 2)) * qT1 + (((-6 : ℂ) + (10 : ℂ) * r ^ 2) / ((r ^ 2 - 1))) * qT2 + ((2 : ℂ) * r) * qT3

/-- Sourced master defect, formal derivative order `2`. -/
def masterDefect2 (s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4 : ℂ) : ℂ :=
  (((-6 : ℂ) * μ + (24 : ℂ) * r ^ 2 * μ + (-38 : ℂ) * r ^ 4 * μ + (20 : ℂ) * r ^ 6 * μ + (-16 : ℂ) * s ^ 2 * r ^ 4 + (-80 : ℂ) * s ^ 2 * r ^ 6) / (r ^ 4 * (r ^ 2 - 1) ^ 4)) * P + (((-4 : ℂ) * μ + (12 : ℂ) * r ^ 2 * μ + (12 : ℂ) * r ^ 4 + (-8 : ℂ) * r ^ 4 * μ + (4 : ℂ) * r ^ 6 + (32 : ℂ) * s ^ 2 * r ^ 4) / (r ^ 3 * (r ^ 2 - 1) ^ 3)) * P1 + (((-1 : ℂ) * μ + (-4 : ℂ) * r ^ 2 + (1 : ℂ) * r ^ 2 * μ + (-4 : ℂ) * r ^ 4 + (-4 : ℂ) * s ^ 2 * r ^ 2) / (r ^ 2 * (r ^ 2 - 1) ^ 2)) * P2 + (((2 : ℂ) * r) / ((r ^ 2 - 1))) * P3 + ((1 : ℂ)) * P4 + (((-24 : ℂ) * r + (-24 : ℂ) * r ^ 3) / ((r ^ 2 - 1) ^ 4)) * qtt0 + (((4 : ℂ) + (12 : ℂ) * r ^ 2) / ((r ^ 2 - 1) ^ 3)) * qtt1 + (((-2 : ℂ) * r) / ((r ^ 2 - 1) ^ 2)) * qtt2 + (((2 : ℂ)) / (s)) * qtr2 + ((4 : ℂ)) * qrr1 + ((2 : ℂ) * r) * qrr2 + (((-24 : ℂ) * r + (-8 : ℂ) * r ^ 3) / ((r ^ 2 - 1) ^ 3 * s)) * qt0 + (((8 : ℂ) + (8 : ℂ) * r ^ 2) / ((r ^ 2 - 1) ^ 2 * s)) * qt1 + (((-4 : ℂ) * r) / ((r ^ 2 - 1) * s)) * qt2 + (((-2 : ℂ)) / (s)) * qt3 + ((4 : ℂ)) * qr2 + (((8 : ℂ) + (-8 : ℂ) * μ + (-32 : ℂ) * r ^ 2 + (32 : ℂ) * r ^ 2 * μ + (48 : ℂ) * r ^ 4 + (-72 : ℂ) * r ^ 4 * μ + (-32 : ℂ) * r ^ 6 + (48 : ℂ) * r ^ 6 * μ + (8 : ℂ) * r ^ 8 + (-96 : ℂ) * s ^ 2 * r ^ 4 + (-96 : ℂ) * s ^ 2 * r ^ 6) / (r ^ 3 * (r ^ 2 - 1) ^ 4)) * qT0 + (((8 : ℂ) + (-8 : ℂ) * μ + (-16 : ℂ) * r ^ 2 + (32 : ℂ) * r ^ 2 * μ + (48 : ℂ) * r ^ 4 + (-24 : ℂ) * r ^ 4 * μ + (-8 : ℂ) * r ^ 6 + (16 : ℂ) * s ^ 2 * r ^ 2 + (48 : ℂ) * s ^ 2 * r ^ 4) / (r ^ 2 * (r ^ 2 - 1) ^ 3)) * qT1 + (((4 : ℂ) + (-4 : ℂ) * μ + (-24 : ℂ) * r ^ 2 + (4 : ℂ) * r ^ 2 * μ + (4 : ℂ) * r ^ 4 + (-8 : ℂ) * s ^ 2 * r ^ 2) / (r * (r ^ 2 - 1) ^ 2)) * qT2 + (((-8 : ℂ) + (12 : ℂ) * r ^ 2) / ((r ^ 2 - 1))) * qT3 + ((2 : ℂ) * r) * qT4

/-- Bianchi form `t` of the source jets, formal derivative order `0`. -/
def bianchiT0 (s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4 : ℂ) : ℂ :=
  (((-2 : ℂ) * s) / ((r ^ 2 - 1))) * qtt0 + (((-2 : ℂ) + (4 : ℂ) * r ^ 2) / (r)) * qtr0 + ((-1 : ℂ) + (1 : ℂ) * r ^ 2) * qtr1 + (((1 : ℂ) * μ) / (r ^ 2)) * qt0

/-- Bianchi form `t` of the source jets, formal derivative order `1`. -/
def bianchiT1 (s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4 : ℂ) : ℂ :=
  (((4 : ℂ) * s * r) / ((r ^ 2 - 1) ^ 2)) * qtt0 + (((-2 : ℂ) * s) / ((r ^ 2 - 1))) * qtt1 + (((2 : ℂ) + (4 : ℂ) * r ^ 2) / (r ^ 2)) * qtr0 + (((-2 : ℂ) + (6 : ℂ) * r ^ 2) / (r)) * qtr1 + ((-1 : ℂ) + (1 : ℂ) * r ^ 2) * qtr2 + (((-2 : ℂ) * μ) / (r ^ 3)) * qt0 + (((1 : ℂ) * μ) / (r ^ 2)) * qt1

/-- Bianchi form `t` of the source jets, formal derivative order `2`. -/
def bianchiT2 (s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4 : ℂ) : ℂ :=
  (((-4 : ℂ) * s + (-12 : ℂ) * s * r ^ 2) / ((r ^ 2 - 1) ^ 3)) * qtt0 + (((8 : ℂ) * s * r) / ((r ^ 2 - 1) ^ 2)) * qtt1 + (((-2 : ℂ) * s) / ((r ^ 2 - 1))) * qtt2 + (((-4 : ℂ)) / (r ^ 3)) * qtr0 + (((4 : ℂ) + (10 : ℂ) * r ^ 2) / (r ^ 2)) * qtr1 + (((-2 : ℂ) + (8 : ℂ) * r ^ 2) / (r)) * qtr2 + ((-1 : ℂ) + (1 : ℂ) * r ^ 2) * qtr3 + (((6 : ℂ) * μ) / (r ^ 4)) * qt0 + (((-4 : ℂ) * μ) / (r ^ 3)) * qt1 + (((1 : ℂ) * μ) / (r ^ 2)) * qt2

/-- Bianchi form `t` of the source jets, formal derivative order `3`. -/
def bianchiT3 (s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4 : ℂ) : ℂ :=
  (((48 : ℂ) * s * r + (48 : ℂ) * s * r ^ 3) / ((r ^ 2 - 1) ^ 4)) * qtt0 + (((-12 : ℂ) * s + (-36 : ℂ) * s * r ^ 2) / ((r ^ 2 - 1) ^ 3)) * qtt1 + (((12 : ℂ) * s * r) / ((r ^ 2 - 1) ^ 2)) * qtt2 + (((-2 : ℂ) * s) / ((r ^ 2 - 1))) * qtt3 + (((12 : ℂ)) / (r ^ 4)) * qtr0 + (((-12 : ℂ)) / (r ^ 3)) * qtr1 + (((6 : ℂ) + (18 : ℂ) * r ^ 2) / (r ^ 2)) * qtr2 + (((-2 : ℂ) + (10 : ℂ) * r ^ 2) / (r)) * qtr3 + ((-1 : ℂ) + (1 : ℂ) * r ^ 2) * qtr4 + (((-24 : ℂ) * μ) / (r ^ 5)) * qt0 + (((18 : ℂ) * μ) / (r ^ 4)) * qt1 + (((-6 : ℂ) * μ) / (r ^ 3)) * qt2 + (((1 : ℂ) * μ) / (r ^ 2)) * qt3

/-- Bianchi form `r` of the source jets, formal derivative order `0`. -/
def bianchiR0 (s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4 : ℂ) : ℂ :=
  (((1 : ℂ) * r) / ((r ^ 2 - 1) ^ 2)) * qtt0 + (((-2 : ℂ) * s) / ((r ^ 2 - 1))) * qtr0 + (((-2 : ℂ) + (5 : ℂ) * r ^ 2) / (r)) * qrr0 + ((-1 : ℂ) + (1 : ℂ) * r ^ 2) * qrr1 + (((1 : ℂ) * μ) / (r ^ 2)) * qr0 + (((-2 : ℂ)) / (r ^ 3)) * qL0

/-- Bianchi form `r` of the source jets, formal derivative order `1`. -/
def bianchiR1 (s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4 : ℂ) : ℂ :=
  (((-1 : ℂ) + (-3 : ℂ) * r ^ 2) / ((r ^ 2 - 1) ^ 3)) * qtt0 + (((1 : ℂ) * r) / ((r ^ 2 - 1) ^ 2)) * qtt1 + (((4 : ℂ) * s * r) / ((r ^ 2 - 1) ^ 2)) * qtr0 + (((-2 : ℂ) * s) / ((r ^ 2 - 1))) * qtr1 + (((2 : ℂ) + (5 : ℂ) * r ^ 2) / (r ^ 2)) * qrr0 + (((-2 : ℂ) + (7 : ℂ) * r ^ 2) / (r)) * qrr1 + ((-1 : ℂ) + (1 : ℂ) * r ^ 2) * qrr2 + (((-2 : ℂ) * μ) / (r ^ 3)) * qr0 + (((1 : ℂ) * μ) / (r ^ 2)) * qr1 + (((6 : ℂ)) / (r ^ 4)) * qL0 + (((-2 : ℂ)) / (r ^ 3)) * qL1

/-- Bianchi form `r` of the source jets, formal derivative order `2`. -/
def bianchiR2 (s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4 : ℂ) : ℂ :=
  (((12 : ℂ) * r + (12 : ℂ) * r ^ 3) / ((r ^ 2 - 1) ^ 4)) * qtt0 + (((-2 : ℂ) + (-6 : ℂ) * r ^ 2) / ((r ^ 2 - 1) ^ 3)) * qtt1 + (((1 : ℂ) * r) / ((r ^ 2 - 1) ^ 2)) * qtt2 + (((-4 : ℂ) * s + (-12 : ℂ) * s * r ^ 2) / ((r ^ 2 - 1) ^ 3)) * qtr0 + (((8 : ℂ) * s * r) / ((r ^ 2 - 1) ^ 2)) * qtr1 + (((-2 : ℂ) * s) / ((r ^ 2 - 1))) * qtr2 + (((-4 : ℂ)) / (r ^ 3)) * qrr0 + (((4 : ℂ) + (12 : ℂ) * r ^ 2) / (r ^ 2)) * qrr1 + (((-2 : ℂ) + (9 : ℂ) * r ^ 2) / (r)) * qrr2 + ((-1 : ℂ) + (1 : ℂ) * r ^ 2) * qrr3 + (((6 : ℂ) * μ) / (r ^ 4)) * qr0 + (((-4 : ℂ) * μ) / (r ^ 3)) * qr1 + (((1 : ℂ) * μ) / (r ^ 2)) * qr2 + (((-24 : ℂ)) / (r ^ 5)) * qL0 + (((12 : ℂ)) / (r ^ 4)) * qL1 + (((-2 : ℂ)) / (r ^ 3)) * qL2

/-- Bianchi form `r` of the source jets, formal derivative order `3`. -/
def bianchiR3 (s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4 : ℂ) : ℂ :=
  (((-12 : ℂ) + (-120 : ℂ) * r ^ 2 + (-60 : ℂ) * r ^ 4) / ((r ^ 2 - 1) ^ 5)) * qtt0 + (((36 : ℂ) * r + (36 : ℂ) * r ^ 3) / ((r ^ 2 - 1) ^ 4)) * qtt1 + (((-3 : ℂ) + (-9 : ℂ) * r ^ 2) / ((r ^ 2 - 1) ^ 3)) * qtt2 + (((1 : ℂ) * r) / ((r ^ 2 - 1) ^ 2)) * qtt3 + (((48 : ℂ) * s * r + (48 : ℂ) * s * r ^ 3) / ((r ^ 2 - 1) ^ 4)) * qtr0 + (((-12 : ℂ) * s + (-36 : ℂ) * s * r ^ 2) / ((r ^ 2 - 1) ^ 3)) * qtr1 + (((12 : ℂ) * s * r) / ((r ^ 2 - 1) ^ 2)) * qtr2 + (((-2 : ℂ) * s) / ((r ^ 2 - 1))) * qtr3 + (((12 : ℂ)) / (r ^ 4)) * qrr0 + (((-12 : ℂ)) / (r ^ 3)) * qrr1 + (((6 : ℂ) + (21 : ℂ) * r ^ 2) / (r ^ 2)) * qrr2 + (((-2 : ℂ) + (11 : ℂ) * r ^ 2) / (r)) * qrr3 + ((-1 : ℂ) + (1 : ℂ) * r ^ 2) * qrr4 + (((-24 : ℂ) * μ) / (r ^ 5)) * qr0 + (((18 : ℂ) * μ) / (r ^ 4)) * qr1 + (((-6 : ℂ) * μ) / (r ^ 3)) * qr2 + (((1 : ℂ) * μ) / (r ^ 2)) * qr3 + (((120 : ℂ)) / (r ^ 6)) * qL0 + (((-72 : ℂ)) / (r ^ 5)) * qL1 + (((18 : ℂ)) / (r ^ 4)) * qL2 + (((-2 : ℂ)) / (r ^ 3)) * qL3

/-- Bianchi form `ang` of the source jets, formal derivative order `0`. -/
def bianchiAng0 (s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4 : ℂ) : ℂ :=
  (((-2 : ℂ) * s) / ((r ^ 2 - 1))) * qt0 + (((-2 : ℂ) + (4 : ℂ) * r ^ 2) / (r)) * qr0 + ((-1 : ℂ) + (1 : ℂ) * r ^ 2) * qr1 + (((-1 : ℂ) + (1 / 2 : ℂ) * μ) / (r ^ 2)) * qT0 + (((1 : ℂ)) / (r ^ 2)) * qL0

/-- Bianchi form `ang` of the source jets, formal derivative order `1`. -/
def bianchiAng1 (s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4 : ℂ) : ℂ :=
  (((4 : ℂ) * s * r) / ((r ^ 2 - 1) ^ 2)) * qt0 + (((-2 : ℂ) * s) / ((r ^ 2 - 1))) * qt1 + (((2 : ℂ) + (4 : ℂ) * r ^ 2) / (r ^ 2)) * qr0 + (((-2 : ℂ) + (6 : ℂ) * r ^ 2) / (r)) * qr1 + ((-1 : ℂ) + (1 : ℂ) * r ^ 2) * qr2 + (((2 : ℂ) + (-1 : ℂ) * μ) / (r ^ 3)) * qT0 + (((-1 : ℂ) + (1 / 2 : ℂ) * μ) / (r ^ 2)) * qT1 + (((-2 : ℂ)) / (r ^ 3)) * qL0 + (((1 : ℂ)) / (r ^ 2)) * qL1

/-- Bianchi form `ang` of the source jets, formal derivative order `2`. -/
def bianchiAng2 (s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4 : ℂ) : ℂ :=
  (((-4 : ℂ) * s + (-12 : ℂ) * s * r ^ 2) / ((r ^ 2 - 1) ^ 3)) * qt0 + (((8 : ℂ) * s * r) / ((r ^ 2 - 1) ^ 2)) * qt1 + (((-2 : ℂ) * s) / ((r ^ 2 - 1))) * qt2 + (((-4 : ℂ)) / (r ^ 3)) * qr0 + (((4 : ℂ) + (10 : ℂ) * r ^ 2) / (r ^ 2)) * qr1 + (((-2 : ℂ) + (8 : ℂ) * r ^ 2) / (r)) * qr2 + ((-1 : ℂ) + (1 : ℂ) * r ^ 2) * qr3 + (((-6 : ℂ) + (3 : ℂ) * μ) / (r ^ 4)) * qT0 + (((4 : ℂ) + (-2 : ℂ) * μ) / (r ^ 3)) * qT1 + (((-1 : ℂ) + (1 / 2 : ℂ) * μ) / (r ^ 2)) * qT2 + (((6 : ℂ)) / (r ^ 4)) * qL0 + (((-4 : ℂ)) / (r ^ 3)) * qL1 + (((1 : ℂ)) / (r ^ 2)) * qL2

/-- Bianchi form `ang` of the source jets, formal derivative order `3`. -/
def bianchiAng3 (s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4 : ℂ) : ℂ :=
  (((48 : ℂ) * s * r + (48 : ℂ) * s * r ^ 3) / ((r ^ 2 - 1) ^ 4)) * qt0 + (((-12 : ℂ) * s + (-36 : ℂ) * s * r ^ 2) / ((r ^ 2 - 1) ^ 3)) * qt1 + (((12 : ℂ) * s * r) / ((r ^ 2 - 1) ^ 2)) * qt2 + (((-2 : ℂ) * s) / ((r ^ 2 - 1))) * qt3 + (((12 : ℂ)) / (r ^ 4)) * qr0 + (((-12 : ℂ)) / (r ^ 3)) * qr1 + (((6 : ℂ) + (18 : ℂ) * r ^ 2) / (r ^ 2)) * qr2 + (((-2 : ℂ) + (10 : ℂ) * r ^ 2) / (r)) * qr3 + ((-1 : ℂ) + (1 : ℂ) * r ^ 2) * qr4 + (((24 : ℂ) + (-12 : ℂ) * μ) / (r ^ 5)) * qT0 + (((-18 : ℂ) + (9 : ℂ) * μ) / (r ^ 4)) * qT1 + (((6 : ℂ) + (-3 : ℂ) * μ) / (r ^ 3)) * qT2 + (((-1 : ℂ) + (1 / 2 : ℂ) * μ) / (r ^ 2)) * qT3 + (((-24 : ℂ)) / (r ^ 5)) * qL0 + (((18 : ℂ)) / (r ^ 4)) * qL1 + (((-6 : ℂ)) / (r ^ 3)) * qL2 + (((1 : ℂ)) / (r ^ 2)) * qL3

private theorem rec_tt_P (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (((-1 : ℂ) + (-1 / 2 : ℂ) * μ + (7 : ℂ) * r ^ 2 + (1 : ℂ) * r ^ 2 * μ + (-11 : ℂ) * r ^ 4 + (-1 / 2 : ℂ) * r ^ 4 * μ + (5 : ℂ) * r ^ 6) / (r ^ 2)) * (((1 / 2 : ℂ) * μ) / (r * (r ^ 2 - 1) * (2 - μ))) + (((-1 : ℂ) + (3 : ℂ) * r ^ 2 + (-3 : ℂ) * r ^ 4 + (1 : ℂ) * r ^ 6) / (r)) * (((1 / 2 : ℂ) * μ + (-3 / 2 : ℂ) * r ^ 2 * μ) / (r ^ 2 * (r ^ 2 - 1) ^ 2 * (2 - μ))) + (((-2 : ℂ) + (1 : ℂ) * μ + (2 : ℂ) * r ^ 2 + (-1 : ℂ) * r ^ 2 * μ) / (r ^ 2)) * (((-1 / 4 : ℂ) * μ) / (r * (2 - μ))) + (((-6 : ℂ) + (14 : ℂ) * r ^ 2 + (-8 : ℂ) * r ^ 4) / (r)) * (((1 / 4 : ℂ) * μ) / (r ^ 2 * (2 - μ))) + ((-2 : ℂ) + (4 : ℂ) * r ^ 2 + (-2 : ℂ) * r ^ 4) * (((-1 / 2 : ℂ) * μ) / (r ^ 3 * (2 - μ))) = (0 : ℂ) := by
  field_simp
  ring

private theorem rec_tt_P1 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (((-1 : ℂ) + (-1 / 2 : ℂ) * μ + (7 : ℂ) * r ^ 2 + (1 : ℂ) * r ^ 2 * μ + (-11 : ℂ) * r ^ 4 + (-1 / 2 : ℂ) * r ^ 4 * μ + (5 : ℂ) * r ^ 6) / (r ^ 2)) * (((-1 : ℂ) + (2 : ℂ) * r ^ 2) / ((r ^ 2 - 1) * (2 - μ))) + (((-1 : ℂ) + (3 : ℂ) * r ^ 2 + (-3 : ℂ) * r ^ 4 + (1 : ℂ) * r ^ 6) / (r)) * (((-1 / 2 : ℂ) * μ + (-2 : ℂ) * r ^ 2 + (1 / 2 : ℂ) * r ^ 2 * μ) / (r * (r ^ 2 - 1) ^ 2 * (2 - μ))) + (((-2 : ℂ) + (1 : ℂ) * μ + (2 : ℂ) * r ^ 2 + (-1 : ℂ) * r ^ 2 * μ) / (r ^ 2)) * (((-1 / 2 : ℂ) + (1 / 2 : ℂ) * r ^ 2) / ((2 - μ))) + (((-6 : ℂ) + (14 : ℂ) * r ^ 2 + (-8 : ℂ) * r ^ 4) / (r)) * (((-1 / 4 : ℂ) * μ + (1 : ℂ) * r ^ 2) / (r * (2 - μ))) + ((-2 : ℂ) + (4 : ℂ) * r ^ 2 + (-2 : ℂ) * r ^ 4) * (((1 / 2 : ℂ) * μ + (1 : ℂ) * r ^ 2) / (r ^ 2 * (2 - μ))) = (0 : ℂ) := by
  field_simp
  ring

private theorem rec_tt_P2 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (((-1 : ℂ) + (-1 / 2 : ℂ) * μ + (7 : ℂ) * r ^ 2 + (1 : ℂ) * r ^ 2 * μ + (-11 : ℂ) * r ^ 4 + (-1 / 2 : ℂ) * r ^ 4 * μ + (5 : ℂ) * r ^ 6) / (r ^ 2)) * (((1 : ℂ) * r) / ((2 - μ))) + (((-1 : ℂ) + (3 : ℂ) * r ^ 2 + (-3 : ℂ) * r ^ 4 + (1 : ℂ) * r ^ 6) / (r)) * (((-2 : ℂ) + (3 : ℂ) * r ^ 2) / ((r ^ 2 - 1) * (2 - μ))) + (((-6 : ℂ) + (14 : ℂ) * r ^ 2 + (-8 : ℂ) * r ^ 4) / (r)) * (((-1 / 2 : ℂ) + (1 / 2 : ℂ) * r ^ 2) / ((2 - μ))) + ((-2 : ℂ) + (4 : ℂ) * r ^ 2 + (-2 : ℂ) * r ^ 4) * (((-1 / 4 : ℂ) * μ + (2 : ℂ) * r ^ 2) / (r * (2 - μ))) = (0 : ℂ) := by
  field_simp
  ring

private theorem rec_tt_P3 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (((-1 : ℂ) + (3 : ℂ) * r ^ 2 + (-3 : ℂ) * r ^ 4 + (1 : ℂ) * r ^ 6) / (r)) * (((1 : ℂ) * r) / ((2 - μ))) + ((-2 : ℂ) + (4 : ℂ) * r ^ 2 + (-2 : ℂ) * r ^ 4) * (((-1 / 2 : ℂ) + (1 / 2 : ℂ) * r ^ 2) / ((2 - μ))) = (0 : ℂ) := by
  field_simp
  ring

private theorem rec_tt_qtt0 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (1 : ℂ) = (((1 / 2 : ℂ) + (-1 / 2 : ℂ) * r ^ 2) / (s)) * (((-2 : ℂ) * s) / ((r ^ 2 - 1))) := by
  field_simp
  ring

private theorem rec_tt_qtr0 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (((-1 : ℂ) + (-1 / 2 : ℂ) * μ + (7 : ℂ) * r ^ 2 + (1 : ℂ) * r ^ 2 * μ + (-11 : ℂ) * r ^ 4 + (-1 / 2 : ℂ) * r ^ 4 * μ + (5 : ℂ) * r ^ 6) / (r ^ 2)) * (((1 : ℂ) * r + (-3 : ℂ) * r ^ 3) / ((r ^ 2 - 1) * (2 - μ) * s)) + (((-1 : ℂ) + (3 : ℂ) * r ^ 2 + (-3 : ℂ) * r ^ 4 + (1 : ℂ) * r ^ 6) / (r)) * (((-1 : ℂ) + (8 : ℂ) * r ^ 2 + (-3 : ℂ) * r ^ 4) / ((r ^ 2 - 1) ^ 2 * (2 - μ) * s)) + (((-2 : ℂ) + (1 : ℂ) * μ + (2 : ℂ) * r ^ 2 + (-1 : ℂ) * r ^ 2 * μ) / (r ^ 2)) * (((1 / 2 : ℂ) * r + (-1 / 2 : ℂ) * r ^ 3) / ((2 - μ) * s)) + (((-6 : ℂ) + (14 : ℂ) * r ^ 2 + (-8 : ℂ) * r ^ 4) / (r)) * (((1 / 2 : ℂ) + (-3 / 2 : ℂ) * r ^ 2) / ((2 - μ) * s)) + ((-2 : ℂ) + (4 : ℂ) * r ^ 2 + (-2 : ℂ) * r ^ 4) * (((-3 : ℂ) * r) / ((2 - μ) * s)) = (((1 / 2 : ℂ) + (-1 / 2 : ℂ) * r ^ 2) / (s)) * (((-2 : ℂ) + (4 : ℂ) * r ^ 2) / (r)) := by
  field_simp
  ring

private theorem rec_tt_qtr1 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (((-1 : ℂ) + (-1 / 2 : ℂ) * μ + (7 : ℂ) * r ^ 2 + (1 : ℂ) * r ^ 2 * μ + (-11 : ℂ) * r ^ 4 + (-1 / 2 : ℂ) * r ^ 4 * μ + (5 : ℂ) * r ^ 6) / (r ^ 2)) * (((-1 : ℂ) * r ^ 2) / ((2 - μ) * s)) + (((-1 : ℂ) + (3 : ℂ) * r ^ 2 + (-3 : ℂ) * r ^ 4 + (1 : ℂ) * r ^ 6) / (r)) * (((3 : ℂ) * r + (-5 : ℂ) * r ^ 3) / ((r ^ 2 - 1) * (2 - μ) * s)) + (((-6 : ℂ) + (14 : ℂ) * r ^ 2 + (-8 : ℂ) * r ^ 4) / (r)) * (((1 / 2 : ℂ) * r + (-1 / 2 : ℂ) * r ^ 3) / ((2 - μ) * s)) + ((-2 : ℂ) + (4 : ℂ) * r ^ 2 + (-2 : ℂ) * r ^ 4) * (((1 : ℂ) + (-3 : ℂ) * r ^ 2) / ((2 - μ) * s)) = (((1 / 2 : ℂ) + (-1 / 2 : ℂ) * r ^ 2) / (s)) * ((-1 : ℂ) + (1 : ℂ) * r ^ 2) := by
  field_simp
  ring

private theorem rec_tt_qtr2 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (((-1 : ℂ) + (3 : ℂ) * r ^ 2 + (-3 : ℂ) * r ^ 4 + (1 : ℂ) * r ^ 6) / (r)) * (((-1 : ℂ) * r ^ 2) / ((2 - μ) * s)) + ((-2 : ℂ) + (4 : ℂ) * r ^ 2 + (-2 : ℂ) * r ^ 4) * (((1 / 2 : ℂ) * r + (-1 / 2 : ℂ) * r ^ 3) / ((2 - μ) * s)) = (0 : ℂ) := by
  field_simp
  ring

private theorem rec_tt_qt0 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (((-1 : ℂ) + (-1 / 2 : ℂ) * μ + (7 : ℂ) * r ^ 2 + (1 : ℂ) * r ^ 2 * μ + (-11 : ℂ) * r ^ 4 + (-1 / 2 : ℂ) * r ^ 4 * μ + (5 : ℂ) * r ^ 6) / (r ^ 2)) * (((2 : ℂ) + (-1 : ℂ) * μ + (-4 : ℂ) * r ^ 2) / ((r ^ 2 - 1) * (2 - μ) * s)) + (((-1 : ℂ) + (3 : ℂ) * r ^ 2 + (-3 : ℂ) * r ^ 4 + (1 : ℂ) * r ^ 6) / (r)) * (((4 : ℂ) * r + (2 : ℂ) * r * μ) / ((r ^ 2 - 1) ^ 2 * (2 - μ) * s)) + (((-2 : ℂ) + (1 : ℂ) * μ + (2 : ℂ) * r ^ 2 + (-1 : ℂ) * r ^ 2 * μ) / (r ^ 2)) * (((1 : ℂ) + (-1 : ℂ) * r ^ 2) / ((2 - μ) * s)) + (((-6 : ℂ) + (14 : ℂ) * r ^ 2 + (-8 : ℂ) * r ^ 4) / (r)) * (((-2 : ℂ) * r) / ((2 - μ) * s)) + ((-2 : ℂ) + (4 : ℂ) * r ^ 2 + (-2 : ℂ) * r ^ 4) * (((-2 : ℂ)) / ((2 - μ) * s)) = (((1 / 2 : ℂ) + (-1 / 2 : ℂ) * r ^ 2) / (s)) * (((1 : ℂ) * μ) / (r ^ 2)) := by
  field_simp
  ring

private theorem rec_tt_qt1 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (((-1 : ℂ) + (-1 / 2 : ℂ) * μ + (7 : ℂ) * r ^ 2 + (1 : ℂ) * r ^ 2 * μ + (-11 : ℂ) * r ^ 4 + (-1 / 2 : ℂ) * r ^ 4 * μ + (5 : ℂ) * r ^ 6) / (r ^ 2)) * (((-2 : ℂ) * r) / ((2 - μ) * s)) + (((-1 : ℂ) + (3 : ℂ) * r ^ 2 + (-3 : ℂ) * r ^ 4 + (1 : ℂ) * r ^ 6) / (r)) * (((4 : ℂ) + (-1 : ℂ) * μ + (-6 : ℂ) * r ^ 2) / ((r ^ 2 - 1) * (2 - μ) * s)) + (((-6 : ℂ) + (14 : ℂ) * r ^ 2 + (-8 : ℂ) * r ^ 4) / (r)) * (((1 : ℂ) + (-1 : ℂ) * r ^ 2) / ((2 - μ) * s)) + ((-2 : ℂ) + (4 : ℂ) * r ^ 2 + (-2 : ℂ) * r ^ 4) * (((-4 : ℂ) * r) / ((2 - μ) * s)) = (0 : ℂ) := by
  field_simp
  ring

private theorem rec_tt_qt2 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (((-1 : ℂ) + (3 : ℂ) * r ^ 2 + (-3 : ℂ) * r ^ 4 + (1 : ℂ) * r ^ 6) / (r)) * (((-2 : ℂ) * r) / ((2 - μ) * s)) + ((-2 : ℂ) + (4 : ℂ) * r ^ 2 + (-2 : ℂ) * r ^ 4) * (((1 : ℂ) + (-1 : ℂ) * r ^ 2) / ((2 - μ) * s)) = (0 : ℂ) := by
  field_simp
  ring

private theorem rec_tt_qT0 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (((-1 : ℂ) + (-1 / 2 : ℂ) * μ + (7 : ℂ) * r ^ 2 + (1 : ℂ) * r ^ 2 * μ + (-11 : ℂ) * r ^ 4 + (-1 / 2 : ℂ) * r ^ 4 * μ + (5 : ℂ) * r ^ 6) / (r ^ 2)) * (((-2 : ℂ) + (1 : ℂ) * μ + (4 : ℂ) * r ^ 2) / ((r ^ 2 - 1) * (2 - μ))) + (((-1 : ℂ) + (3 : ℂ) * r ^ 2 + (-3 : ℂ) * r ^ 4 + (1 : ℂ) * r ^ 6) / (r)) * (((-4 : ℂ) * r + (-2 : ℂ) * r * μ) / ((r ^ 2 - 1) ^ 2 * (2 - μ))) + (((-2 : ℂ) + (1 : ℂ) * μ + (2 : ℂ) * r ^ 2 + (-1 : ℂ) * r ^ 2 * μ) / (r ^ 2)) * (((-1 : ℂ) + (-1 / 2 : ℂ) * μ + (1 : ℂ) * r ^ 2) / ((2 - μ))) + (((-6 : ℂ) + (14 : ℂ) * r ^ 2 + (-8 : ℂ) * r ^ 4) / (r)) * (((2 : ℂ) * r) / ((2 - μ))) + ((-2 : ℂ) + (4 : ℂ) * r ^ 2 + (-2 : ℂ) * r ^ 4) * (((2 : ℂ)) / ((2 - μ))) = (0 : ℂ) := by
  field_simp
  ring

private theorem rec_tt_qT1 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (((-1 : ℂ) + (-1 / 2 : ℂ) * μ + (7 : ℂ) * r ^ 2 + (1 : ℂ) * r ^ 2 * μ + (-11 : ℂ) * r ^ 4 + (-1 / 2 : ℂ) * r ^ 4 * μ + (5 : ℂ) * r ^ 6) / (r ^ 2)) * (((-6 : ℂ) * r + (8 : ℂ) * r ^ 3) / ((r ^ 2 - 1) * (2 - μ))) + (((-1 : ℂ) + (3 : ℂ) * r ^ 2 + (-3 : ℂ) * r ^ 4 + (1 : ℂ) * r ^ 6) / (r)) * (((8 : ℂ) + (-1 : ℂ) * μ + (-24 : ℂ) * r ^ 2 + (1 : ℂ) * r ^ 2 * μ + (12 : ℂ) * r ^ 4) / ((r ^ 2 - 1) ^ 2 * (2 - μ))) + (((-2 : ℂ) + (1 : ℂ) * μ + (2 : ℂ) * r ^ 2 + (-1 : ℂ) * r ^ 2 * μ) / (r ^ 2)) * (((-1 : ℂ) * r + (1 : ℂ) * r ^ 3) / ((2 - μ))) + (((-6 : ℂ) + (14 : ℂ) * r ^ 2 + (-8 : ℂ) * r ^ 4) / (r)) * (((-2 : ℂ) + (-1 / 2 : ℂ) * μ + (4 : ℂ) * r ^ 2) / ((2 - μ))) + ((-2 : ℂ) + (4 : ℂ) * r ^ 2 + (-2 : ℂ) * r ^ 4) * (((10 : ℂ) * r) / ((2 - μ))) = (0 : ℂ) := by
  field_simp
  ring

private theorem rec_tt_qT2 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (((-1 : ℂ) + (-1 / 2 : ℂ) * μ + (7 : ℂ) * r ^ 2 + (1 : ℂ) * r ^ 2 * μ + (-11 : ℂ) * r ^ 4 + (-1 / 2 : ℂ) * r ^ 4 * μ + (5 : ℂ) * r ^ 6) / (r ^ 2)) * (((2 : ℂ) * r ^ 2) / ((2 - μ))) + (((-1 : ℂ) + (3 : ℂ) * r ^ 2 + (-3 : ℂ) * r ^ 4 + (1 : ℂ) * r ^ 6) / (r)) * (((-10 : ℂ) * r + (12 : ℂ) * r ^ 3) / ((r ^ 2 - 1) * (2 - μ))) + (((-6 : ℂ) + (14 : ℂ) * r ^ 2 + (-8 : ℂ) * r ^ 4) / (r)) * (((-1 : ℂ) * r + (1 : ℂ) * r ^ 3) / ((2 - μ))) + ((-2 : ℂ) + (4 : ℂ) * r ^ 2 + (-2 : ℂ) * r ^ 4) * (((-3 : ℂ) + (-1 / 2 : ℂ) * μ + (7 : ℂ) * r ^ 2) / ((2 - μ))) = (0 : ℂ) := by
  field_simp
  ring

private theorem rec_tt_qT3 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (((-1 : ℂ) + (3 : ℂ) * r ^ 2 + (-3 : ℂ) * r ^ 4 + (1 : ℂ) * r ^ 6) / (r)) * (((2 : ℂ) * r ^ 2) / ((2 - μ))) + ((-2 : ℂ) + (4 : ℂ) * r ^ 2 + (-2 : ℂ) * r ^ 4) * (((-1 : ℂ) * r + (1 : ℂ) * r ^ 3) / ((2 - μ))) = (0 : ℂ) := by
  field_simp
  ring

/-- The reconstructed jet solves the sourced harmonic `tt` equation up to the master defect and the Bianchi forms of the source. -/
theorem reconstruction_TT (s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4 : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    harmonicTT s r μ (recF0 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4) (recF01 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4) (recF02 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4) (recF1 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4) (recF11 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4) (recF12 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4) (recF2 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4) (recF21 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4) (recF22 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4) (recH s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4) (recH1 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4) (recH2 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4) + qtt0 = (((1 / 2 : ℂ) + (-1 / 2 : ℂ) * r ^ 2) / (s)) * bianchiT0 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4 := by
  unfold harmonicTT recF2 recF21 recH recH1 recH2 bianchiT0
  linear_combination P * rec_tt_P s r μ hs hr hf hμ + P1 * rec_tt_P1 s r μ hs hr hf hμ + P2 * rec_tt_P2 s r μ hs hr hf hμ + P3 * rec_tt_P3 s r μ hs hr hf hμ + qtt0 * rec_tt_qtt0 s r μ hs hr hf hμ + qtr0 * rec_tt_qtr0 s r μ hs hr hf hμ + qtr1 * rec_tt_qtr1 s r μ hs hr hf hμ + qtr2 * rec_tt_qtr2 s r μ hs hr hf hμ + qt0 * rec_tt_qt0 s r μ hs hr hf hμ + qt1 * rec_tt_qt1 s r μ hs hr hf hμ + qt2 * rec_tt_qt2 s r μ hs hr hf hμ + qT0 * rec_tt_qT0 s r μ hs hr hf hμ + qT1 * rec_tt_qT1 s r μ hs hr hf hμ + qT2 * rec_tt_qT2 s r μ hs hr hf hμ + qT3 * rec_tt_qT3 s r μ hs hr hf hμ

private theorem rec_tr_P (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (((-1 / 2 : ℂ) * μ) / (r ^ 2)) * (((-2 : ℂ) * s) / ((r ^ 2 - 1) * (2 - μ))) + (((-2 : ℂ) * s + (2 : ℂ) * s * r ^ 2) / (r)) * (((1 / 2 : ℂ) * μ) / (r * (r ^ 2 - 1) * (2 - μ))) + (((4 : ℂ) * s) / (r * (r ^ 2 - 1))) * (((-1 / 4 : ℂ) * μ) / (r * (2 - μ))) + ((-4 : ℂ) * s) * (((1 / 4 : ℂ) * μ) / (r ^ 2 * (2 - μ))) = (0 : ℂ) := by
  field_simp
  ring

private theorem rec_tr_P1 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (((-1 / 2 : ℂ) * μ) / (r ^ 2)) * (((2 : ℂ) * s * r) / ((2 - μ))) + (((-2 : ℂ) * s + (2 : ℂ) * s * r ^ 2) / (r)) * (((-1 : ℂ) + (2 : ℂ) * r ^ 2) / ((r ^ 2 - 1) * (2 - μ))) + (((4 : ℂ) * s) / (r * (r ^ 2 - 1))) * (((-1 / 2 : ℂ) + (1 / 2 : ℂ) * r ^ 2) / ((2 - μ))) + ((-4 : ℂ) * s) * (((-1 / 4 : ℂ) * μ + (1 : ℂ) * r ^ 2) / (r * (2 - μ))) = (0 : ℂ) := by
  field_simp
  ring

private theorem rec_tr_P2 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (((-2 : ℂ) * s + (2 : ℂ) * s * r ^ 2) / (r)) * (((1 : ℂ) * r) / ((2 - μ))) + ((-4 : ℂ) * s) * (((-1 / 2 : ℂ) + (1 / 2 : ℂ) * r ^ 2) / ((2 - μ))) = (0 : ℂ) := by
  field_simp
  ring

private theorem rec_tr_qtr0 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (((-1 / 2 : ℂ) * μ) / (r ^ 2)) * (((-2 : ℂ) * r ^ 2) / ((2 - μ))) + (((-2 : ℂ) * s + (2 : ℂ) * s * r ^ 2) / (r)) * (((1 : ℂ) * r + (-3 : ℂ) * r ^ 3) / ((r ^ 2 - 1) * (2 - μ) * s)) + (((4 : ℂ) * s) / (r * (r ^ 2 - 1))) * (((1 / 2 : ℂ) * r + (-1 / 2 : ℂ) * r ^ 3) / ((2 - μ) * s)) + ((-4 : ℂ) * s) * (((1 / 2 : ℂ) + (-3 / 2 : ℂ) * r ^ 2) / ((2 - μ) * s)) + (1 : ℂ) = (0 : ℂ) := by
  field_simp
  ring

private theorem rec_tr_qtr1 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (((-2 : ℂ) * s + (2 : ℂ) * s * r ^ 2) / (r)) * (((-1 : ℂ) * r ^ 2) / ((2 - μ) * s)) + ((-4 : ℂ) * s) * (((1 / 2 : ℂ) * r + (-1 / 2 : ℂ) * r ^ 3) / ((2 - μ) * s)) = (0 : ℂ) := by
  field_simp
  ring

private theorem rec_tr_qt0 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (((-1 / 2 : ℂ) * μ) / (r ^ 2)) * (((-4 : ℂ) * r) / ((2 - μ))) + (((-2 : ℂ) * s + (2 : ℂ) * s * r ^ 2) / (r)) * (((2 : ℂ) + (-1 : ℂ) * μ + (-4 : ℂ) * r ^ 2) / ((r ^ 2 - 1) * (2 - μ) * s)) + (((4 : ℂ) * s) / (r * (r ^ 2 - 1))) * (((1 : ℂ) + (-1 : ℂ) * r ^ 2) / ((2 - μ) * s)) + ((-4 : ℂ) * s) * (((-2 : ℂ) * r) / ((2 - μ) * s)) = (0 : ℂ) := by
  field_simp
  ring

private theorem rec_tr_qt1 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (((-2 : ℂ) * s + (2 : ℂ) * s * r ^ 2) / (r)) * (((-2 : ℂ) * r) / ((2 - μ) * s)) + ((-4 : ℂ) * s) * (((1 : ℂ) + (-1 : ℂ) * r ^ 2) / ((2 - μ) * s)) = (0 : ℂ) := by
  field_simp
  ring

private theorem rec_tr_qT0 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (((-1 / 2 : ℂ) * μ) / (r ^ 2)) * (((-8 : ℂ) * s * r + (4 : ℂ) * s * r ^ 3) / ((r ^ 2 - 1) * (2 - μ))) + (((-2 : ℂ) * s + (2 : ℂ) * s * r ^ 2) / (r)) * (((-2 : ℂ) + (1 : ℂ) * μ + (4 : ℂ) * r ^ 2) / ((r ^ 2 - 1) * (2 - μ))) + (((4 : ℂ) * s) / (r * (r ^ 2 - 1))) * (((-1 : ℂ) + (-1 / 2 : ℂ) * μ + (1 : ℂ) * r ^ 2) / ((2 - μ))) + ((-4 : ℂ) * s) * (((2 : ℂ) * r) / ((2 - μ))) = (0 : ℂ) := by
  field_simp
  ring

private theorem rec_tr_qT1 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (((-1 / 2 : ℂ) * μ) / (r ^ 2)) * (((4 : ℂ) * s * r ^ 2) / ((2 - μ))) + (((-2 : ℂ) * s + (2 : ℂ) * s * r ^ 2) / (r)) * (((-6 : ℂ) * r + (8 : ℂ) * r ^ 3) / ((r ^ 2 - 1) * (2 - μ))) + (((4 : ℂ) * s) / (r * (r ^ 2 - 1))) * (((-1 : ℂ) * r + (1 : ℂ) * r ^ 3) / ((2 - μ))) + ((-4 : ℂ) * s) * (((-2 : ℂ) + (-1 / 2 : ℂ) * μ + (4 : ℂ) * r ^ 2) / ((2 - μ))) = (0 : ℂ) := by
  field_simp
  ring

private theorem rec_tr_qT2 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (((-2 : ℂ) * s + (2 : ℂ) * s * r ^ 2) / (r)) * (((2 : ℂ) * r ^ 2) / ((2 - μ))) + ((-4 : ℂ) * s) * (((-1 : ℂ) * r + (1 : ℂ) * r ^ 3) / ((2 - μ))) = (0 : ℂ) := by
  field_simp
  ring

/-- The reconstructed jet solves the sourced harmonic `tr` equation up to the master defect and the Bianchi forms of the source. -/
theorem reconstruction_TR (s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4 : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    harmonicTR s r μ (recF0 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4) (recF01 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4) (recF02 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4) (recF1 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4) (recF11 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4) (recF12 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4) (recF2 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4) (recF21 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4) (recF22 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4) (recH s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4) (recH1 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4) (recH2 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4) + qtr0 = (0 : ℂ) := by
  unfold harmonicTR recF1 recF2 recH recH1
  linear_combination P * rec_tr_P s r μ hs hr hf hμ + P1 * rec_tr_P1 s r μ hs hr hf hμ + P2 * rec_tr_P2 s r μ hs hr hf hμ + qtr0 * rec_tr_qtr0 s r μ hs hr hf hμ + qtr1 * rec_tr_qtr1 s r μ hs hr hf hμ + qt0 * rec_tr_qt0 s r μ hs hr hf hμ + qt1 * rec_tr_qt1 s r μ hs hr hf hμ + qT0 * rec_tr_qT0 s r μ hs hr hf hμ + qT1 * rec_tr_qT1 s r μ hs hr hf hμ + qT2 * rec_tr_qT2 s r μ hs hr hf hμ

private theorem rec_rr_P (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (((-1 / 2 : ℂ) * μ + (2 : ℂ) * r ^ 2) / (r ^ 2 * (r ^ 2 - 1) ^ 2)) * (((-1 / 2 : ℂ) * μ + (1 / 2 : ℂ) * r ^ 2 * μ) / (r * (2 - μ))) + (((-1 : ℂ)) / (r * (r ^ 2 - 1))) * (((1 / 2 : ℂ) * μ + (1 / 2 : ℂ) * r ^ 2 * μ) / (r ^ 2 * (2 - μ))) + (((4 : ℂ) * s) / (r * (r ^ 2 - 1))) * (((-2 : ℂ) * s) / ((r ^ 2 - 1) * (2 - μ))) + (((1 : ℂ) + (-3 : ℂ) * r ^ 2) / (r ^ 2)) * (((1 / 2 : ℂ) * μ) / (r * (r ^ 2 - 1) * (2 - μ))) + (((2 : ℂ) + (-1 : ℂ) * μ + (-2 : ℂ) * r ^ 2 + (1 : ℂ) * r ^ 2 * μ + (-8 : ℂ) * s ^ 2 * r ^ 2) / (r ^ 2 * (r ^ 2 - 1) ^ 2)) * (((-1 / 4 : ℂ) * μ) / (r * (2 - μ))) + (((-2 : ℂ) + (4 : ℂ) * r ^ 2) / (r * (r ^ 2 - 1))) * (((1 / 4 : ℂ) * μ) / (r ^ 2 * (2 - μ))) = (((2 : ℂ) + (-1 / 2 : ℂ) * μ + (-4 : ℂ) * r ^ 2) / (r * (2 - μ))) * (((-1 : ℂ) * μ + (1 : ℂ) * r ^ 2 * μ + (-4 : ℂ) * s ^ 2 * r ^ 2) / (r ^ 2 * (r ^ 2 - 1) ^ 2)) + (((1 : ℂ) + (-1 : ℂ) * r ^ 2) / ((2 - μ))) * (((-2 : ℂ) * μ + (6 : ℂ) * r ^ 2 * μ + (-4 : ℂ) * r ^ 4 * μ + (16 : ℂ) * s ^ 2 * r ^ 4) / (r ^ 3 * (r ^ 2 - 1) ^ 3)) := by
  field_simp
  ring

private theorem rec_rr_P1 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (((-1 / 2 : ℂ) * μ + (2 : ℂ) * r ^ 2) / (r ^ 2 * (r ^ 2 - 1) ^ 2)) * (((1 : ℂ) + (-3 : ℂ) * r ^ 2 + (2 : ℂ) * r ^ 4) / ((2 - μ))) + (((-1 : ℂ)) / (r * (r ^ 2 - 1))) * (((-1 / 2 : ℂ) * μ + (-6 : ℂ) * r ^ 2 + (1 / 2 : ℂ) * r ^ 2 * μ + (8 : ℂ) * r ^ 4) / (r * (2 - μ))) + (((4 : ℂ) * s) / (r * (r ^ 2 - 1))) * (((2 : ℂ) * s * r) / ((2 - μ))) + (((1 : ℂ) + (-3 : ℂ) * r ^ 2) / (r ^ 2)) * (((-1 : ℂ) + (2 : ℂ) * r ^ 2) / ((r ^ 2 - 1) * (2 - μ))) + (((2 : ℂ) + (-1 : ℂ) * μ + (-2 : ℂ) * r ^ 2 + (1 : ℂ) * r ^ 2 * μ + (-8 : ℂ) * s ^ 2 * r ^ 2) / (r ^ 2 * (r ^ 2 - 1) ^ 2)) * (((-1 / 2 : ℂ) + (1 / 2 : ℂ) * r ^ 2) / ((2 - μ))) + (((-2 : ℂ) + (4 : ℂ) * r ^ 2) / (r * (r ^ 2 - 1))) * (((-1 / 4 : ℂ) * μ + (1 : ℂ) * r ^ 2) / (r * (2 - μ))) = (((2 : ℂ) + (-1 / 2 : ℂ) * μ + (-4 : ℂ) * r ^ 2) / (r * (2 - μ))) * (((2 : ℂ) * r) / ((r ^ 2 - 1))) + (((1 : ℂ) + (-1 : ℂ) * r ^ 2) / ((2 - μ))) * (((-1 : ℂ) * μ + (-2 : ℂ) * r ^ 2 + (1 : ℂ) * r ^ 2 * μ + (-2 : ℂ) * r ^ 4 + (-4 : ℂ) * s ^ 2 * r ^ 2) / (r ^ 2 * (r ^ 2 - 1) ^ 2)) := by
  field_simp
  ring

private theorem rec_rr_P2 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (((-1 / 2 : ℂ) * μ + (2 : ℂ) * r ^ 2) / (r ^ 2 * (r ^ 2 - 1) ^ 2)) * (((1 : ℂ) * r + (-2 : ℂ) * r ^ 3 + (1 : ℂ) * r ^ 5) / ((2 - μ))) + (((-1 : ℂ)) / (r * (r ^ 2 - 1))) * (((2 : ℂ) + (-9 : ℂ) * r ^ 2 + (7 : ℂ) * r ^ 4) / ((2 - μ))) + (((1 : ℂ) + (-3 : ℂ) * r ^ 2) / (r ^ 2)) * (((1 : ℂ) * r) / ((2 - μ))) + (((-2 : ℂ) + (4 : ℂ) * r ^ 2) / (r * (r ^ 2 - 1))) * (((-1 / 2 : ℂ) + (1 / 2 : ℂ) * r ^ 2) / ((2 - μ))) = (((2 : ℂ) + (-1 / 2 : ℂ) * μ + (-4 : ℂ) * r ^ 2) / (r * (2 - μ))) * ((1 : ℂ)) + (((1 : ℂ) + (-1 : ℂ) * r ^ 2) / ((2 - μ))) * (((2 : ℂ) * r) / ((r ^ 2 - 1))) := by
  field_simp
  ring

private theorem rec_rr_P3 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (((-1 : ℂ)) / (r * (r ^ 2 - 1))) * (((1 : ℂ) * r + (-2 : ℂ) * r ^ 3 + (1 : ℂ) * r ^ 5) / ((2 - μ))) = (((1 : ℂ) + (-1 : ℂ) * r ^ 2) / ((2 - μ))) * ((1 : ℂ)) := by
  field_simp
  ring

private theorem rec_rr_qtt0 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (0 : ℂ) = (((2 : ℂ) + (-1 / 2 : ℂ) * μ + (-4 : ℂ) * r ^ 2) / (r * (2 - μ))) * (((-2 : ℂ) * r) / ((r ^ 2 - 1) ^ 2)) + (((1 : ℂ) + (-1 : ℂ) * r ^ 2) / ((2 - μ))) * (((2 : ℂ) + (6 : ℂ) * r ^ 2) / ((r ^ 2 - 1) ^ 3)) + (((-3 : ℂ) + (1 / 2 : ℂ) * μ + (4 : ℂ) * r ^ 2) / ((r ^ 2 - 1) * (2 - μ) * s)) * (((-2 : ℂ) * s) / ((r ^ 2 - 1))) + (((1 : ℂ) * r) / ((2 - μ) * s)) * (((4 : ℂ) * s * r) / ((r ^ 2 - 1) ^ 2)) + (((2 : ℂ) * r) / ((2 - μ))) * (((1 : ℂ) * r) / ((r ^ 2 - 1) ^ 2)) := by
  field_simp
  ring

private theorem rec_rr_qtt1 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (0 : ℂ) = (((1 : ℂ) + (-1 : ℂ) * r ^ 2) / ((2 - μ))) * (((-2 : ℂ) * r) / ((r ^ 2 - 1) ^ 2)) + (((1 : ℂ) * r) / ((2 - μ) * s)) * (((-2 : ℂ) * s) / ((r ^ 2 - 1))) := by
  field_simp
  ring

private theorem rec_rr_qtr0 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (((-1 / 2 : ℂ) * μ + (2 : ℂ) * r ^ 2) / (r ^ 2 * (r ^ 2 - 1) ^ 2)) * (((-1 : ℂ) * r + (4 : ℂ) * r ^ 3 + (-3 : ℂ) * r ^ 5) / ((2 - μ) * s)) + (((-1 : ℂ)) / (r * (r ^ 2 - 1))) * (((-1 : ℂ) + (12 : ℂ) * r ^ 2 + (-15 : ℂ) * r ^ 4) / ((2 - μ) * s)) + (((4 : ℂ) * s) / (r * (r ^ 2 - 1))) * (((-2 : ℂ) * r ^ 2) / ((2 - μ))) + (((1 : ℂ) + (-3 : ℂ) * r ^ 2) / (r ^ 2)) * (((1 : ℂ) * r + (-3 : ℂ) * r ^ 3) / ((r ^ 2 - 1) * (2 - μ) * s)) + (((2 : ℂ) + (-1 : ℂ) * μ + (-2 : ℂ) * r ^ 2 + (1 : ℂ) * r ^ 2 * μ + (-8 : ℂ) * s ^ 2 * r ^ 2) / (r ^ 2 * (r ^ 2 - 1) ^ 2)) * (((1 / 2 : ℂ) * r + (-1 / 2 : ℂ) * r ^ 3) / ((2 - μ) * s)) + (((-2 : ℂ) + (4 : ℂ) * r ^ 2) / (r * (r ^ 2 - 1))) * (((1 / 2 : ℂ) + (-3 / 2 : ℂ) * r ^ 2) / ((2 - μ) * s)) = (((2 : ℂ) + (-1 / 2 : ℂ) * μ + (-4 : ℂ) * r ^ 2) / (r * (2 - μ))) * (((2 : ℂ)) / (s)) + (((-3 : ℂ) + (1 / 2 : ℂ) * μ + (4 : ℂ) * r ^ 2) / ((r ^ 2 - 1) * (2 - μ) * s)) * (((-2 : ℂ) + (4 : ℂ) * r ^ 2) / (r)) + (((1 : ℂ) * r) / ((2 - μ) * s)) * (((2 : ℂ) + (4 : ℂ) * r ^ 2) / (r ^ 2)) + (((2 : ℂ) * r) / ((2 - μ))) * (((-2 : ℂ) * s) / ((r ^ 2 - 1))) := by
  field_simp
  ring

private theorem rec_rr_qtr1 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (((-1 / 2 : ℂ) * μ + (2 : ℂ) * r ^ 2) / (r ^ 2 * (r ^ 2 - 1) ^ 2)) * (((-1 : ℂ) * r ^ 2 + (2 : ℂ) * r ^ 4 + (-1 : ℂ) * r ^ 6) / ((2 - μ) * s)) + (((-1 : ℂ)) / (r * (r ^ 2 - 1))) * (((-3 : ℂ) * r + (12 : ℂ) * r ^ 3 + (-9 : ℂ) * r ^ 5) / ((2 - μ) * s)) + (((1 : ℂ) + (-3 : ℂ) * r ^ 2) / (r ^ 2)) * (((-1 : ℂ) * r ^ 2) / ((2 - μ) * s)) + (((-2 : ℂ) + (4 : ℂ) * r ^ 2) / (r * (r ^ 2 - 1))) * (((1 / 2 : ℂ) * r + (-1 / 2 : ℂ) * r ^ 3) / ((2 - μ) * s)) = (((1 : ℂ) + (-1 : ℂ) * r ^ 2) / ((2 - μ))) * (((2 : ℂ)) / (s)) + (((-3 : ℂ) + (1 / 2 : ℂ) * μ + (4 : ℂ) * r ^ 2) / ((r ^ 2 - 1) * (2 - μ) * s)) * ((-1 : ℂ) + (1 : ℂ) * r ^ 2) + (((1 : ℂ) * r) / ((2 - μ) * s)) * (((-2 : ℂ) + (6 : ℂ) * r ^ 2) / (r)) := by
  field_simp
  ring

private theorem rec_rr_qtr2 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (((-1 : ℂ)) / (r * (r ^ 2 - 1))) * (((-1 : ℂ) * r ^ 2 + (2 : ℂ) * r ^ 4 + (-1 : ℂ) * r ^ 6) / ((2 - μ) * s)) = (((1 : ℂ) * r) / ((2 - μ) * s)) * ((-1 : ℂ) + (1 : ℂ) * r ^ 2) := by
  field_simp
  ring

private theorem rec_rr_qrr0 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (1 : ℂ) = (((2 : ℂ) + (-1 / 2 : ℂ) * μ + (-4 : ℂ) * r ^ 2) / (r * (2 - μ))) * ((2 : ℂ) * r) + (((1 : ℂ) + (-1 : ℂ) * r ^ 2) / ((2 - μ))) * ((2 : ℂ)) + (((2 : ℂ) * r) / ((2 - μ))) * (((-2 : ℂ) + (5 : ℂ) * r ^ 2) / (r)) := by
  field_simp
  ring

private theorem rec_rr_qrr1 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (0 : ℂ) = (((1 : ℂ) + (-1 : ℂ) * r ^ 2) / ((2 - μ))) * ((2 : ℂ) * r) + (((2 : ℂ) * r) / ((2 - μ))) * ((-1 : ℂ) + (1 : ℂ) * r ^ 2) := by
  field_simp
  ring

private theorem rec_rr_qt0 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (((-1 / 2 : ℂ) * μ + (2 : ℂ) * r ^ 2) / (r ^ 2 * (r ^ 2 - 1) ^ 2)) * (((-2 : ℂ) + (1 : ℂ) * μ + (6 : ℂ) * r ^ 2 + (-1 : ℂ) * r ^ 2 * μ + (-4 : ℂ) * r ^ 4) / ((2 - μ) * s)) + (((-1 : ℂ)) / (r * (r ^ 2 - 1))) * (((12 : ℂ) * r + (-2 : ℂ) * r * μ + (-16 : ℂ) * r ^ 3) / ((2 - μ) * s)) + (((4 : ℂ) * s) / (r * (r ^ 2 - 1))) * (((-4 : ℂ) * r) / ((2 - μ))) + (((1 : ℂ) + (-3 : ℂ) * r ^ 2) / (r ^ 2)) * (((2 : ℂ) + (-1 : ℂ) * μ + (-4 : ℂ) * r ^ 2) / ((r ^ 2 - 1) * (2 - μ) * s)) + (((2 : ℂ) + (-1 : ℂ) * μ + (-2 : ℂ) * r ^ 2 + (1 : ℂ) * r ^ 2 * μ + (-8 : ℂ) * s ^ 2 * r ^ 2) / (r ^ 2 * (r ^ 2 - 1) ^ 2)) * (((1 : ℂ) + (-1 : ℂ) * r ^ 2) / ((2 - μ) * s)) + (((-2 : ℂ) + (4 : ℂ) * r ^ 2) / (r * (r ^ 2 - 1))) * (((-2 : ℂ) * r) / ((2 - μ) * s)) = (((2 : ℂ) + (-1 / 2 : ℂ) * μ + (-4 : ℂ) * r ^ 2) / (r * (2 - μ))) * (((-4 : ℂ) * r) / ((r ^ 2 - 1) * s)) + (((1 : ℂ) + (-1 : ℂ) * r ^ 2) / ((2 - μ))) * (((4 : ℂ) + (4 : ℂ) * r ^ 2) / ((r ^ 2 - 1) ^ 2 * s)) + (((-3 : ℂ) + (1 / 2 : ℂ) * μ + (4 : ℂ) * r ^ 2) / ((r ^ 2 - 1) * (2 - μ) * s)) * (((1 : ℂ) * μ) / (r ^ 2)) + (((1 : ℂ) * r) / ((2 - μ) * s)) * (((-2 : ℂ) * μ) / (r ^ 3)) + (((4 : ℂ)) / ((2 - μ))) * (((-2 : ℂ) * s) / ((r ^ 2 - 1))) := by
  field_simp
  ring

private theorem rec_rr_qt1 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (((-1 / 2 : ℂ) * μ + (2 : ℂ) * r ^ 2) / (r ^ 2 * (r ^ 2 - 1) ^ 2)) * (((-2 : ℂ) * r + (4 : ℂ) * r ^ 3 + (-2 : ℂ) * r ^ 5) / ((2 - μ) * s)) + (((-1 : ℂ)) / (r * (r ^ 2 - 1))) * (((-4 : ℂ) + (1 : ℂ) * μ + (18 : ℂ) * r ^ 2 + (-1 : ℂ) * r ^ 2 * μ + (-14 : ℂ) * r ^ 4) / ((2 - μ) * s)) + (((1 : ℂ) + (-3 : ℂ) * r ^ 2) / (r ^ 2)) * (((-2 : ℂ) * r) / ((2 - μ) * s)) + (((-2 : ℂ) + (4 : ℂ) * r ^ 2) / (r * (r ^ 2 - 1))) * (((1 : ℂ) + (-1 : ℂ) * r ^ 2) / ((2 - μ) * s)) = (((2 : ℂ) + (-1 / 2 : ℂ) * μ + (-4 : ℂ) * r ^ 2) / (r * (2 - μ))) * (((-2 : ℂ)) / (s)) + (((1 : ℂ) + (-1 : ℂ) * r ^ 2) / ((2 - μ))) * (((-4 : ℂ) * r) / ((r ^ 2 - 1) * s)) + (((1 : ℂ) * r) / ((2 - μ) * s)) * (((1 : ℂ) * μ) / (r ^ 2)) := by
  field_simp
  ring

private theorem rec_rr_qt2 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (((-1 : ℂ)) / (r * (r ^ 2 - 1))) * (((-2 : ℂ) * r + (4 : ℂ) * r ^ 3 + (-2 : ℂ) * r ^ 5) / ((2 - μ) * s)) = (((1 : ℂ) + (-1 : ℂ) * r ^ 2) / ((2 - μ))) * (((-2 : ℂ)) / (s)) := by
  field_simp
  ring

private theorem rec_rr_qr0 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (0 : ℂ) = (((2 : ℂ) + (-1 / 2 : ℂ) * μ + (-4 : ℂ) * r ^ 2) / (r * (2 - μ))) * ((4 : ℂ)) + (((2 : ℂ) * r) / ((2 - μ))) * (((1 : ℂ) * μ) / (r ^ 2)) + (((4 : ℂ)) / ((2 - μ))) * (((-2 : ℂ) + (4 : ℂ) * r ^ 2) / (r)) := by
  field_simp
  ring

private theorem rec_rr_qr1 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (0 : ℂ) = (((1 : ℂ) + (-1 : ℂ) * r ^ 2) / ((2 - μ))) * ((4 : ℂ)) + (((4 : ℂ)) / ((2 - μ))) * ((-1 : ℂ) + (1 : ℂ) * r ^ 2) := by
  field_simp
  ring

private theorem rec_rr_qT0 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (((-1 / 2 : ℂ) * μ + (2 : ℂ) * r ^ 2) / (r ^ 2 * (r ^ 2 - 1) ^ 2)) * (((6 : ℂ) + (-3 : ℂ) * μ + (-10 : ℂ) * r ^ 2 + (3 : ℂ) * r ^ 2 * μ + (4 : ℂ) * r ^ 4) / ((2 - μ))) + (((-1 : ℂ)) / (r * (r ^ 2 - 1))) * (((-20 : ℂ) * r + (6 : ℂ) * r * μ + (16 : ℂ) * r ^ 3) / ((2 - μ))) + (((4 : ℂ) * s) / (r * (r ^ 2 - 1))) * (((-8 : ℂ) * s * r + (4 : ℂ) * s * r ^ 3) / ((r ^ 2 - 1) * (2 - μ))) + (((1 : ℂ) + (-3 : ℂ) * r ^ 2) / (r ^ 2)) * (((-2 : ℂ) + (1 : ℂ) * μ + (4 : ℂ) * r ^ 2) / ((r ^ 2 - 1) * (2 - μ))) + (((2 : ℂ) + (-1 : ℂ) * μ + (-2 : ℂ) * r ^ 2 + (1 : ℂ) * r ^ 2 * μ + (-8 : ℂ) * s ^ 2 * r ^ 2) / (r ^ 2 * (r ^ 2 - 1) ^ 2)) * (((-1 : ℂ) + (-1 / 2 : ℂ) * μ + (1 : ℂ) * r ^ 2) / ((2 - μ))) + (((-2 : ℂ) + (4 : ℂ) * r ^ 2) / (r * (r ^ 2 - 1))) * (((2 : ℂ) * r) / ((2 - μ))) = (((2 : ℂ) + (-1 / 2 : ℂ) * μ + (-4 : ℂ) * r ^ 2) / (r * (2 - μ))) * (((4 : ℂ) + (-4 : ℂ) * μ + (-8 : ℂ) * r ^ 2 + (4 : ℂ) * r ^ 2 * μ + (4 : ℂ) * r ^ 4 + (-8 : ℂ) * s ^ 2 * r ^ 2) / (r * (r ^ 2 - 1) ^ 2)) + (((1 : ℂ) + (-1 : ℂ) * r ^ 2) / ((2 - μ))) * (((4 : ℂ) + (-4 : ℂ) * μ + (-12 : ℂ) * r ^ 2 + (16 : ℂ) * r ^ 2 * μ + (12 : ℂ) * r ^ 4 + (-12 : ℂ) * r ^ 4 * μ + (-4 : ℂ) * r ^ 6 + (8 : ℂ) * s ^ 2 * r ^ 2 + (24 : ℂ) * s ^ 2 * r ^ 4) / (r ^ 2 * (r ^ 2 - 1) ^ 3)) + (((4 : ℂ)) / ((2 - μ))) * (((-1 : ℂ) + (1 / 2 : ℂ) * μ) / (r ^ 2)) := by
  field_simp
  ring

private theorem rec_rr_qT1 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (((-1 / 2 : ℂ) * μ + (2 : ℂ) * r ^ 2) / (r ^ 2 * (r ^ 2 - 1) ^ 2)) * (((6 : ℂ) * r + (-14 : ℂ) * r ^ 3 + (8 : ℂ) * r ^ 5) / ((2 - μ))) + (((-1 : ℂ)) / (r * (r ^ 2 - 1))) * (((12 : ℂ) + (-3 : ℂ) * μ + (-52 : ℂ) * r ^ 2 + (3 : ℂ) * r ^ 2 * μ + (44 : ℂ) * r ^ 4) / ((2 - μ))) + (((4 : ℂ) * s) / (r * (r ^ 2 - 1))) * (((4 : ℂ) * s * r ^ 2) / ((2 - μ))) + (((1 : ℂ) + (-3 : ℂ) * r ^ 2) / (r ^ 2)) * (((-6 : ℂ) * r + (8 : ℂ) * r ^ 3) / ((r ^ 2 - 1) * (2 - μ))) + (((2 : ℂ) + (-1 : ℂ) * μ + (-2 : ℂ) * r ^ 2 + (1 : ℂ) * r ^ 2 * μ + (-8 : ℂ) * s ^ 2 * r ^ 2) / (r ^ 2 * (r ^ 2 - 1) ^ 2)) * (((-1 : ℂ) * r + (1 : ℂ) * r ^ 3) / ((2 - μ))) + (((-2 : ℂ) + (4 : ℂ) * r ^ 2) / (r * (r ^ 2 - 1))) * (((-2 : ℂ) + (-1 / 2 : ℂ) * μ + (4 : ℂ) * r ^ 2) / ((2 - μ))) = (((2 : ℂ) + (-1 / 2 : ℂ) * μ + (-4 : ℂ) * r ^ 2) / (r * (2 - μ))) * (((-4 : ℂ) + (8 : ℂ) * r ^ 2) / ((r ^ 2 - 1))) + (((1 : ℂ) + (-1 : ℂ) * r ^ 2) / ((2 - μ))) * (((4 : ℂ) + (-4 : ℂ) * μ + (-16 : ℂ) * r ^ 2 + (4 : ℂ) * r ^ 2 * μ + (4 : ℂ) * r ^ 4 + (-8 : ℂ) * s ^ 2 * r ^ 2) / (r * (r ^ 2 - 1) ^ 2)) := by
  field_simp
  ring

private theorem rec_rr_qT2 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (((-1 / 2 : ℂ) * μ + (2 : ℂ) * r ^ 2) / (r ^ 2 * (r ^ 2 - 1) ^ 2)) * (((2 : ℂ) * r ^ 2 + (-4 : ℂ) * r ^ 4 + (2 : ℂ) * r ^ 6) / ((2 - μ))) + (((-1 : ℂ)) / (r * (r ^ 2 - 1))) * (((10 : ℂ) * r + (-30 : ℂ) * r ^ 3 + (20 : ℂ) * r ^ 5) / ((2 - μ))) + (((1 : ℂ) + (-3 : ℂ) * r ^ 2) / (r ^ 2)) * (((2 : ℂ) * r ^ 2) / ((2 - μ))) + (((-2 : ℂ) + (4 : ℂ) * r ^ 2) / (r * (r ^ 2 - 1))) * (((-1 : ℂ) * r + (1 : ℂ) * r ^ 3) / ((2 - μ))) = (((2 : ℂ) + (-1 / 2 : ℂ) * μ + (-4 : ℂ) * r ^ 2) / (r * (2 - μ))) * ((2 : ℂ) * r) + (((1 : ℂ) + (-1 : ℂ) * r ^ 2) / ((2 - μ))) * (((-6 : ℂ) + (10 : ℂ) * r ^ 2) / ((r ^ 2 - 1))) := by
  field_simp
  ring

private theorem rec_rr_qT3 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (((-1 : ℂ)) / (r * (r ^ 2 - 1))) * (((2 : ℂ) * r ^ 2 + (-4 : ℂ) * r ^ 4 + (2 : ℂ) * r ^ 6) / ((2 - μ))) = (((1 : ℂ) + (-1 : ℂ) * r ^ 2) / ((2 - μ))) * ((2 : ℂ) * r) := by
  field_simp
  ring

private theorem rec_rr_qL0 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (0 : ℂ) = (((2 : ℂ) * r) / ((2 - μ))) * (((-2 : ℂ)) / (r ^ 3)) + (((4 : ℂ)) / ((2 - μ))) * (((1 : ℂ)) / (r ^ 2)) := by
  field_simp
  ring

/-- The reconstructed jet solves the sourced harmonic `rr` equation up to the master defect and the Bianchi forms of the source. -/
theorem reconstruction_RR (s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4 : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    harmonicRR s r μ (recF0 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4) (recF01 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4) (recF02 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4) (recF1 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4) (recF11 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4) (recF12 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4) (recF2 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4) (recF21 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4) (recF22 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4) (recH s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4) (recH1 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4) (recH2 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4) + qrr0 = (((2 : ℂ) + (-1 / 2 : ℂ) * μ + (-4 : ℂ) * r ^ 2) / (r * (2 - μ))) * masterDefect0 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4 + (((1 : ℂ) + (-1 : ℂ) * r ^ 2) / ((2 - μ))) * masterDefect1 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4 + (((-3 : ℂ) + (1 / 2 : ℂ) * μ + (4 : ℂ) * r ^ 2) / ((r ^ 2 - 1) * (2 - μ) * s)) * bianchiT0 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4 + (((1 : ℂ) * r) / ((2 - μ) * s)) * bianchiT1 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4 + (((2 : ℂ) * r) / ((2 - μ))) * bianchiR0 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4 + (((4 : ℂ)) / ((2 - μ))) * bianchiAng0 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4 := by
  unfold harmonicRR recF0 recF01 recF1 recF2 recH recH1 masterDefect0 masterDefect1 bianchiT0 bianchiT1 bianchiR0 bianchiAng0
  linear_combination P * rec_rr_P s r μ hs hr hf hμ + P1 * rec_rr_P1 s r μ hs hr hf hμ + P2 * rec_rr_P2 s r μ hs hr hf hμ + P3 * rec_rr_P3 s r μ hs hr hf hμ + qtt0 * rec_rr_qtt0 s r μ hs hr hf hμ + qtt1 * rec_rr_qtt1 s r μ hs hr hf hμ + qtr0 * rec_rr_qtr0 s r μ hs hr hf hμ + qtr1 * rec_rr_qtr1 s r μ hs hr hf hμ + qtr2 * rec_rr_qtr2 s r μ hs hr hf hμ + qrr0 * rec_rr_qrr0 s r μ hs hr hf hμ + qrr1 * rec_rr_qrr1 s r μ hs hr hf hμ + qt0 * rec_rr_qt0 s r μ hs hr hf hμ + qt1 * rec_rr_qt1 s r μ hs hr hf hμ + qt2 * rec_rr_qt2 s r μ hs hr hf hμ + qr0 * rec_rr_qr0 s r μ hs hr hf hμ + qr1 * rec_rr_qr1 s r μ hs hr hf hμ + qT0 * rec_rr_qT0 s r μ hs hr hf hμ + qT1 * rec_rr_qT1 s r μ hs hr hf hμ + qT2 * rec_rr_qT2 s r μ hs hr hf hμ + qT3 * rec_rr_qT3 s r μ hs hr hf hμ + qL0 * rec_rr_qL0 s r μ hs hr hf hμ

private theorem rec_t_P (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    ((1 : ℂ) * r) * (((-2 : ℂ) * s) / ((r ^ 2 - 1) * (2 - μ))) + ((-1 / 2 : ℂ) + (1 / 2 : ℂ) * r ^ 2) * (((4 : ℂ) * s * r) / ((r ^ 2 - 1) ^ 2 * (2 - μ))) + ((1 : ℂ) * s + (-1 : ℂ) * s * r ^ 2) * (((1 / 2 : ℂ) * μ) / (r * (r ^ 2 - 1) * (2 - μ))) + ((-2 : ℂ) * s) * (((-1 / 4 : ℂ) * μ) / (r * (2 - μ))) = (0 : ℂ) := by
  field_simp
  ring

private theorem rec_t_P1 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    ((1 : ℂ) * r) * (((2 : ℂ) * s * r) / ((2 - μ))) + ((-1 / 2 : ℂ) + (1 / 2 : ℂ) * r ^ 2) * (((-4 : ℂ) * s + (2 : ℂ) * s * r ^ 2) / ((r ^ 2 - 1) * (2 - μ))) + ((1 : ℂ) * s + (-1 : ℂ) * s * r ^ 2) * (((-1 : ℂ) + (2 : ℂ) * r ^ 2) / ((r ^ 2 - 1) * (2 - μ))) + ((-2 : ℂ) * s) * (((-1 / 2 : ℂ) + (1 / 2 : ℂ) * r ^ 2) / ((2 - μ))) = (0 : ℂ) := by
  field_simp
  ring

private theorem rec_t_P2 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    ((-1 / 2 : ℂ) + (1 / 2 : ℂ) * r ^ 2) * (((2 : ℂ) * s * r) / ((2 - μ))) + ((1 : ℂ) * s + (-1 : ℂ) * s * r ^ 2) * (((1 : ℂ) * r) / ((2 - μ))) = (0 : ℂ) := by
  field_simp
  ring

private theorem rec_t_qtr0 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    ((1 : ℂ) * r) * (((-2 : ℂ) * r ^ 2) / ((2 - μ))) + ((-1 / 2 : ℂ) + (1 / 2 : ℂ) * r ^ 2) * (((-4 : ℂ) * r) / ((2 - μ))) + ((1 : ℂ) * s + (-1 : ℂ) * s * r ^ 2) * (((1 : ℂ) * r + (-3 : ℂ) * r ^ 3) / ((r ^ 2 - 1) * (2 - μ) * s)) + ((-2 : ℂ) * s) * (((1 / 2 : ℂ) * r + (-1 / 2 : ℂ) * r ^ 3) / ((2 - μ) * s)) = (0 : ℂ) := by
  field_simp
  ring

private theorem rec_t_qtr1 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    ((-1 / 2 : ℂ) + (1 / 2 : ℂ) * r ^ 2) * (((-2 : ℂ) * r ^ 2) / ((2 - μ))) + ((1 : ℂ) * s + (-1 : ℂ) * s * r ^ 2) * (((-1 : ℂ) * r ^ 2) / ((2 - μ) * s)) = (0 : ℂ) := by
  field_simp
  ring

private theorem rec_t_qt0 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    ((1 : ℂ) * r) * (((-4 : ℂ) * r) / ((2 - μ))) + ((-1 / 2 : ℂ) + (1 / 2 : ℂ) * r ^ 2) * (((-4 : ℂ)) / ((2 - μ))) + ((1 : ℂ) * s + (-1 : ℂ) * s * r ^ 2) * (((2 : ℂ) + (-1 : ℂ) * μ + (-4 : ℂ) * r ^ 2) / ((r ^ 2 - 1) * (2 - μ) * s)) + ((-2 : ℂ) * s) * (((1 : ℂ) + (-1 : ℂ) * r ^ 2) / ((2 - μ) * s)) + (1 : ℂ) = (0 : ℂ) := by
  field_simp
  ring

private theorem rec_t_qt1 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    ((-1 / 2 : ℂ) + (1 / 2 : ℂ) * r ^ 2) * (((-4 : ℂ) * r) / ((2 - μ))) + ((1 : ℂ) * s + (-1 : ℂ) * s * r ^ 2) * (((-2 : ℂ) * r) / ((2 - μ) * s)) = (0 : ℂ) := by
  field_simp
  ring

private theorem rec_t_qT0 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    ((1 : ℂ) * r) * (((-8 : ℂ) * s * r + (4 : ℂ) * s * r ^ 3) / ((r ^ 2 - 1) * (2 - μ))) + ((-1 / 2 : ℂ) + (1 / 2 : ℂ) * r ^ 2) * (((8 : ℂ) * s + (-4 : ℂ) * s * r ^ 2 + (4 : ℂ) * s * r ^ 4) / ((r ^ 2 - 1) ^ 2 * (2 - μ))) + ((1 : ℂ) * s + (-1 : ℂ) * s * r ^ 2) * (((-2 : ℂ) + (1 : ℂ) * μ + (4 : ℂ) * r ^ 2) / ((r ^ 2 - 1) * (2 - μ))) + ((-2 : ℂ) * s) * (((-1 : ℂ) + (-1 / 2 : ℂ) * μ + (1 : ℂ) * r ^ 2) / ((2 - μ))) = (0 : ℂ) := by
  field_simp
  ring

private theorem rec_t_qT1 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    ((1 : ℂ) * r) * (((4 : ℂ) * s * r ^ 2) / ((2 - μ))) + ((-1 / 2 : ℂ) + (1 / 2 : ℂ) * r ^ 2) * (((-16 : ℂ) * s * r + (12 : ℂ) * s * r ^ 3) / ((r ^ 2 - 1) * (2 - μ))) + ((1 : ℂ) * s + (-1 : ℂ) * s * r ^ 2) * (((-6 : ℂ) * r + (8 : ℂ) * r ^ 3) / ((r ^ 2 - 1) * (2 - μ))) + ((-2 : ℂ) * s) * (((-1 : ℂ) * r + (1 : ℂ) * r ^ 3) / ((2 - μ))) = (0 : ℂ) := by
  field_simp
  ring

private theorem rec_t_qT2 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    ((-1 / 2 : ℂ) + (1 / 2 : ℂ) * r ^ 2) * (((4 : ℂ) * s * r ^ 2) / ((2 - μ))) + ((1 : ℂ) * s + (-1 : ℂ) * s * r ^ 2) * (((2 : ℂ) * r ^ 2) / ((2 - μ))) = (0 : ℂ) := by
  field_simp
  ring

/-- The reconstructed jet solves the sourced harmonic `t` equation up to the master defect and the Bianchi forms of the source. -/
theorem reconstruction_T (s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4 : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    harmonicT s r μ (recF0 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4) (recF01 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4) (recF02 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4) (recF1 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4) (recF11 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4) (recF12 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4) (recF2 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4) (recF21 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4) (recF22 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4) (recH s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4) (recH1 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4) (recH2 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4) + qt0 = (0 : ℂ) := by
  unfold harmonicT recF1 recF11 recF2 recH
  linear_combination P * rec_t_P s r μ hs hr hf hμ + P1 * rec_t_P1 s r μ hs hr hf hμ + P2 * rec_t_P2 s r μ hs hr hf hμ + qtr0 * rec_t_qtr0 s r μ hs hr hf hμ + qtr1 * rec_t_qtr1 s r μ hs hr hf hμ + qt0 * rec_t_qt0 s r μ hs hr hf hμ + qt1 * rec_t_qt1 s r μ hs hr hf hμ + qT0 * rec_t_qT0 s r μ hs hr hf hμ + qT1 * rec_t_qT1 s r μ hs hr hf hμ + qT2 * rec_t_qT2 s r μ hs hr hf hμ

private theorem rec_r_P (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (((1 / 2 : ℂ) + (-1 : ℂ) * r ^ 2) / (r * (r ^ 2 - 1) ^ 2)) * (((-1 / 2 : ℂ) * μ + (1 / 2 : ℂ) * r ^ 2 * μ) / (r * (2 - μ))) + (((1 / 2 : ℂ)) / ((r ^ 2 - 1))) * (((1 / 2 : ℂ) * μ + (1 / 2 : ℂ) * r ^ 2 * μ) / (r ^ 2 * (2 - μ))) + (((-1 : ℂ) * s) / ((r ^ 2 - 1))) * (((-2 : ℂ) * s) / ((r ^ 2 - 1) * (2 - μ))) + (((-1 / 2 : ℂ) + (1 : ℂ) * r ^ 2) / (r)) * (((1 / 2 : ℂ) * μ) / (r * (r ^ 2 - 1) * (2 - μ))) + ((-1 : ℂ)) * (((1 / 4 : ℂ) * μ) / (r ^ 2 * (2 - μ))) = (((-1 / 2 : ℂ) + (2 : ℂ) * r ^ 2) / ((2 - μ))) * (((-1 : ℂ) * μ + (1 : ℂ) * r ^ 2 * μ + (-4 : ℂ) * s ^ 2 * r ^ 2) / (r ^ 2 * (r ^ 2 - 1) ^ 2)) + (((-1 / 2 : ℂ) * r + (1 / 2 : ℂ) * r ^ 3) / ((2 - μ))) * (((-2 : ℂ) * μ + (6 : ℂ) * r ^ 2 * μ + (-4 : ℂ) * r ^ 4 * μ + (16 : ℂ) * s ^ 2 * r ^ 4) / (r ^ 3 * (r ^ 2 - 1) ^ 3)) := by
  field_simp
  ring

private theorem rec_r_P1 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (((1 / 2 : ℂ) + (-1 : ℂ) * r ^ 2) / (r * (r ^ 2 - 1) ^ 2)) * (((1 : ℂ) + (-3 : ℂ) * r ^ 2 + (2 : ℂ) * r ^ 4) / ((2 - μ))) + (((1 / 2 : ℂ)) / ((r ^ 2 - 1))) * (((-1 / 2 : ℂ) * μ + (-6 : ℂ) * r ^ 2 + (1 / 2 : ℂ) * r ^ 2 * μ + (8 : ℂ) * r ^ 4) / (r * (2 - μ))) + (((-1 : ℂ) * s) / ((r ^ 2 - 1))) * (((2 : ℂ) * s * r) / ((2 - μ))) + (((-1 / 2 : ℂ) + (1 : ℂ) * r ^ 2) / (r)) * (((-1 : ℂ) + (2 : ℂ) * r ^ 2) / ((r ^ 2 - 1) * (2 - μ))) + ((-1 : ℂ)) * (((-1 / 4 : ℂ) * μ + (1 : ℂ) * r ^ 2) / (r * (2 - μ))) = (((-1 / 2 : ℂ) + (2 : ℂ) * r ^ 2) / ((2 - μ))) * (((2 : ℂ) * r) / ((r ^ 2 - 1))) + (((-1 / 2 : ℂ) * r + (1 / 2 : ℂ) * r ^ 3) / ((2 - μ))) * (((-1 : ℂ) * μ + (-2 : ℂ) * r ^ 2 + (1 : ℂ) * r ^ 2 * μ + (-2 : ℂ) * r ^ 4 + (-4 : ℂ) * s ^ 2 * r ^ 2) / (r ^ 2 * (r ^ 2 - 1) ^ 2)) := by
  field_simp
  ring

private theorem rec_r_P2 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (((1 / 2 : ℂ) + (-1 : ℂ) * r ^ 2) / (r * (r ^ 2 - 1) ^ 2)) * (((1 : ℂ) * r + (-2 : ℂ) * r ^ 3 + (1 : ℂ) * r ^ 5) / ((2 - μ))) + (((1 / 2 : ℂ)) / ((r ^ 2 - 1))) * (((2 : ℂ) + (-9 : ℂ) * r ^ 2 + (7 : ℂ) * r ^ 4) / ((2 - μ))) + (((-1 / 2 : ℂ) + (1 : ℂ) * r ^ 2) / (r)) * (((1 : ℂ) * r) / ((2 - μ))) + ((-1 : ℂ)) * (((-1 / 2 : ℂ) + (1 / 2 : ℂ) * r ^ 2) / ((2 - μ))) = (((-1 / 2 : ℂ) + (2 : ℂ) * r ^ 2) / ((2 - μ))) * ((1 : ℂ)) + (((-1 / 2 : ℂ) * r + (1 / 2 : ℂ) * r ^ 3) / ((2 - μ))) * (((2 : ℂ) * r) / ((r ^ 2 - 1))) := by
  field_simp
  ring

private theorem rec_r_P3 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (((1 / 2 : ℂ)) / ((r ^ 2 - 1))) * (((1 : ℂ) * r + (-2 : ℂ) * r ^ 3 + (1 : ℂ) * r ^ 5) / ((2 - μ))) = (((-1 / 2 : ℂ) * r + (1 / 2 : ℂ) * r ^ 3) / ((2 - μ))) * ((1 : ℂ)) := by
  field_simp
  ring

private theorem rec_r_qtt0 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (0 : ℂ) = (((-1 / 2 : ℂ) + (2 : ℂ) * r ^ 2) / ((2 - μ))) * (((-2 : ℂ) * r) / ((r ^ 2 - 1) ^ 2)) + (((-1 / 2 : ℂ) * r + (1 / 2 : ℂ) * r ^ 3) / ((2 - μ))) * (((2 : ℂ) + (6 : ℂ) * r ^ 2) / ((r ^ 2 - 1) ^ 3)) + (((1 : ℂ) * r + (-2 : ℂ) * r ^ 3) / ((r ^ 2 - 1) * (2 - μ) * s)) * (((-2 : ℂ) * s) / ((r ^ 2 - 1))) + (((-1 / 2 : ℂ) * r ^ 2) / ((2 - μ) * s)) * (((4 : ℂ) * s * r) / ((r ^ 2 - 1) ^ 2)) + (((-1 : ℂ) * r ^ 2) / ((2 - μ))) * (((1 : ℂ) * r) / ((r ^ 2 - 1) ^ 2)) := by
  field_simp
  ring

private theorem rec_r_qtt1 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (0 : ℂ) = (((-1 / 2 : ℂ) * r + (1 / 2 : ℂ) * r ^ 3) / ((2 - μ))) * (((-2 : ℂ) * r) / ((r ^ 2 - 1) ^ 2)) + (((-1 / 2 : ℂ) * r ^ 2) / ((2 - μ) * s)) * (((-2 : ℂ) * s) / ((r ^ 2 - 1))) := by
  field_simp
  ring

private theorem rec_r_qtr0 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (((1 / 2 : ℂ) + (-1 : ℂ) * r ^ 2) / (r * (r ^ 2 - 1) ^ 2)) * (((-1 : ℂ) * r + (4 : ℂ) * r ^ 3 + (-3 : ℂ) * r ^ 5) / ((2 - μ) * s)) + (((1 / 2 : ℂ)) / ((r ^ 2 - 1))) * (((-1 : ℂ) + (12 : ℂ) * r ^ 2 + (-15 : ℂ) * r ^ 4) / ((2 - μ) * s)) + (((-1 : ℂ) * s) / ((r ^ 2 - 1))) * (((-2 : ℂ) * r ^ 2) / ((2 - μ))) + (((-1 / 2 : ℂ) + (1 : ℂ) * r ^ 2) / (r)) * (((1 : ℂ) * r + (-3 : ℂ) * r ^ 3) / ((r ^ 2 - 1) * (2 - μ) * s)) + ((-1 : ℂ)) * (((1 / 2 : ℂ) + (-3 / 2 : ℂ) * r ^ 2) / ((2 - μ) * s)) = (((-1 / 2 : ℂ) + (2 : ℂ) * r ^ 2) / ((2 - μ))) * (((2 : ℂ)) / (s)) + (((1 : ℂ) * r + (-2 : ℂ) * r ^ 3) / ((r ^ 2 - 1) * (2 - μ) * s)) * (((-2 : ℂ) + (4 : ℂ) * r ^ 2) / (r)) + (((-1 / 2 : ℂ) * r ^ 2) / ((2 - μ) * s)) * (((2 : ℂ) + (4 : ℂ) * r ^ 2) / (r ^ 2)) + (((-1 : ℂ) * r ^ 2) / ((2 - μ))) * (((-2 : ℂ) * s) / ((r ^ 2 - 1))) := by
  field_simp
  ring

private theorem rec_r_qtr1 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (((1 / 2 : ℂ) + (-1 : ℂ) * r ^ 2) / (r * (r ^ 2 - 1) ^ 2)) * (((-1 : ℂ) * r ^ 2 + (2 : ℂ) * r ^ 4 + (-1 : ℂ) * r ^ 6) / ((2 - μ) * s)) + (((1 / 2 : ℂ)) / ((r ^ 2 - 1))) * (((-3 : ℂ) * r + (12 : ℂ) * r ^ 3 + (-9 : ℂ) * r ^ 5) / ((2 - μ) * s)) + (((-1 / 2 : ℂ) + (1 : ℂ) * r ^ 2) / (r)) * (((-1 : ℂ) * r ^ 2) / ((2 - μ) * s)) + ((-1 : ℂ)) * (((1 / 2 : ℂ) * r + (-1 / 2 : ℂ) * r ^ 3) / ((2 - μ) * s)) = (((-1 / 2 : ℂ) * r + (1 / 2 : ℂ) * r ^ 3) / ((2 - μ))) * (((2 : ℂ)) / (s)) + (((1 : ℂ) * r + (-2 : ℂ) * r ^ 3) / ((r ^ 2 - 1) * (2 - μ) * s)) * ((-1 : ℂ) + (1 : ℂ) * r ^ 2) + (((-1 / 2 : ℂ) * r ^ 2) / ((2 - μ) * s)) * (((-2 : ℂ) + (6 : ℂ) * r ^ 2) / (r)) := by
  field_simp
  ring

private theorem rec_r_qtr2 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (((1 / 2 : ℂ)) / ((r ^ 2 - 1))) * (((-1 : ℂ) * r ^ 2 + (2 : ℂ) * r ^ 4 + (-1 : ℂ) * r ^ 6) / ((2 - μ) * s)) = (((-1 / 2 : ℂ) * r ^ 2) / ((2 - μ) * s)) * ((-1 : ℂ) + (1 : ℂ) * r ^ 2) := by
  field_simp
  ring

private theorem rec_r_qrr0 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (0 : ℂ) = (((-1 / 2 : ℂ) + (2 : ℂ) * r ^ 2) / ((2 - μ))) * ((2 : ℂ) * r) + (((-1 / 2 : ℂ) * r + (1 / 2 : ℂ) * r ^ 3) / ((2 - μ))) * ((2 : ℂ)) + (((-1 : ℂ) * r ^ 2) / ((2 - μ))) * (((-2 : ℂ) + (5 : ℂ) * r ^ 2) / (r)) := by
  field_simp
  ring

private theorem rec_r_qrr1 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (0 : ℂ) = (((-1 / 2 : ℂ) * r + (1 / 2 : ℂ) * r ^ 3) / ((2 - μ))) * ((2 : ℂ) * r) + (((-1 : ℂ) * r ^ 2) / ((2 - μ))) * ((-1 : ℂ) + (1 : ℂ) * r ^ 2) := by
  field_simp
  ring

private theorem rec_r_qt0 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (((1 / 2 : ℂ) + (-1 : ℂ) * r ^ 2) / (r * (r ^ 2 - 1) ^ 2)) * (((-2 : ℂ) + (1 : ℂ) * μ + (6 : ℂ) * r ^ 2 + (-1 : ℂ) * r ^ 2 * μ + (-4 : ℂ) * r ^ 4) / ((2 - μ) * s)) + (((1 / 2 : ℂ)) / ((r ^ 2 - 1))) * (((12 : ℂ) * r + (-2 : ℂ) * r * μ + (-16 : ℂ) * r ^ 3) / ((2 - μ) * s)) + (((-1 : ℂ) * s) / ((r ^ 2 - 1))) * (((-4 : ℂ) * r) / ((2 - μ))) + (((-1 / 2 : ℂ) + (1 : ℂ) * r ^ 2) / (r)) * (((2 : ℂ) + (-1 : ℂ) * μ + (-4 : ℂ) * r ^ 2) / ((r ^ 2 - 1) * (2 - μ) * s)) + ((-1 : ℂ)) * (((-2 : ℂ) * r) / ((2 - μ) * s)) = (((-1 / 2 : ℂ) + (2 : ℂ) * r ^ 2) / ((2 - μ))) * (((-4 : ℂ) * r) / ((r ^ 2 - 1) * s)) + (((-1 / 2 : ℂ) * r + (1 / 2 : ℂ) * r ^ 3) / ((2 - μ))) * (((4 : ℂ) + (4 : ℂ) * r ^ 2) / ((r ^ 2 - 1) ^ 2 * s)) + (((1 : ℂ) * r + (-2 : ℂ) * r ^ 3) / ((r ^ 2 - 1) * (2 - μ) * s)) * (((1 : ℂ) * μ) / (r ^ 2)) + (((-1 / 2 : ℂ) * r ^ 2) / ((2 - μ) * s)) * (((-2 : ℂ) * μ) / (r ^ 3)) + (((-2 : ℂ) * r) / ((2 - μ))) * (((-2 : ℂ) * s) / ((r ^ 2 - 1))) := by
  field_simp
  ring

private theorem rec_r_qt1 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (((1 / 2 : ℂ) + (-1 : ℂ) * r ^ 2) / (r * (r ^ 2 - 1) ^ 2)) * (((-2 : ℂ) * r + (4 : ℂ) * r ^ 3 + (-2 : ℂ) * r ^ 5) / ((2 - μ) * s)) + (((1 / 2 : ℂ)) / ((r ^ 2 - 1))) * (((-4 : ℂ) + (1 : ℂ) * μ + (18 : ℂ) * r ^ 2 + (-1 : ℂ) * r ^ 2 * μ + (-14 : ℂ) * r ^ 4) / ((2 - μ) * s)) + (((-1 / 2 : ℂ) + (1 : ℂ) * r ^ 2) / (r)) * (((-2 : ℂ) * r) / ((2 - μ) * s)) + ((-1 : ℂ)) * (((1 : ℂ) + (-1 : ℂ) * r ^ 2) / ((2 - μ) * s)) = (((-1 / 2 : ℂ) + (2 : ℂ) * r ^ 2) / ((2 - μ))) * (((-2 : ℂ)) / (s)) + (((-1 / 2 : ℂ) * r + (1 / 2 : ℂ) * r ^ 3) / ((2 - μ))) * (((-4 : ℂ) * r) / ((r ^ 2 - 1) * s)) + (((-1 / 2 : ℂ) * r ^ 2) / ((2 - μ) * s)) * (((1 : ℂ) * μ) / (r ^ 2)) := by
  field_simp
  ring

private theorem rec_r_qt2 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (((1 / 2 : ℂ)) / ((r ^ 2 - 1))) * (((-2 : ℂ) * r + (4 : ℂ) * r ^ 3 + (-2 : ℂ) * r ^ 5) / ((2 - μ) * s)) = (((-1 / 2 : ℂ) * r + (1 / 2 : ℂ) * r ^ 3) / ((2 - μ))) * (((-2 : ℂ)) / (s)) := by
  field_simp
  ring

private theorem rec_r_qr0 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (1 : ℂ) = (((-1 / 2 : ℂ) + (2 : ℂ) * r ^ 2) / ((2 - μ))) * ((4 : ℂ)) + (((-1 : ℂ) * r ^ 2) / ((2 - μ))) * (((1 : ℂ) * μ) / (r ^ 2)) + (((-2 : ℂ) * r) / ((2 - μ))) * (((-2 : ℂ) + (4 : ℂ) * r ^ 2) / (r)) := by
  field_simp
  ring

private theorem rec_r_qr1 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (0 : ℂ) = (((-1 / 2 : ℂ) * r + (1 / 2 : ℂ) * r ^ 3) / ((2 - μ))) * ((4 : ℂ)) + (((-2 : ℂ) * r) / ((2 - μ))) * ((-1 : ℂ) + (1 : ℂ) * r ^ 2) := by
  field_simp
  ring

private theorem rec_r_qT0 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (((1 / 2 : ℂ) + (-1 : ℂ) * r ^ 2) / (r * (r ^ 2 - 1) ^ 2)) * (((6 : ℂ) + (-3 : ℂ) * μ + (-10 : ℂ) * r ^ 2 + (3 : ℂ) * r ^ 2 * μ + (4 : ℂ) * r ^ 4) / ((2 - μ))) + (((1 / 2 : ℂ)) / ((r ^ 2 - 1))) * (((-20 : ℂ) * r + (6 : ℂ) * r * μ + (16 : ℂ) * r ^ 3) / ((2 - μ))) + (((-1 : ℂ) * s) / ((r ^ 2 - 1))) * (((-8 : ℂ) * s * r + (4 : ℂ) * s * r ^ 3) / ((r ^ 2 - 1) * (2 - μ))) + (((-1 / 2 : ℂ) + (1 : ℂ) * r ^ 2) / (r)) * (((-2 : ℂ) + (1 : ℂ) * μ + (4 : ℂ) * r ^ 2) / ((r ^ 2 - 1) * (2 - μ))) + ((-1 : ℂ)) * (((2 : ℂ) * r) / ((2 - μ))) = (((-1 / 2 : ℂ) + (2 : ℂ) * r ^ 2) / ((2 - μ))) * (((4 : ℂ) + (-4 : ℂ) * μ + (-8 : ℂ) * r ^ 2 + (4 : ℂ) * r ^ 2 * μ + (4 : ℂ) * r ^ 4 + (-8 : ℂ) * s ^ 2 * r ^ 2) / (r * (r ^ 2 - 1) ^ 2)) + (((-1 / 2 : ℂ) * r + (1 / 2 : ℂ) * r ^ 3) / ((2 - μ))) * (((4 : ℂ) + (-4 : ℂ) * μ + (-12 : ℂ) * r ^ 2 + (16 : ℂ) * r ^ 2 * μ + (12 : ℂ) * r ^ 4 + (-12 : ℂ) * r ^ 4 * μ + (-4 : ℂ) * r ^ 6 + (8 : ℂ) * s ^ 2 * r ^ 2 + (24 : ℂ) * s ^ 2 * r ^ 4) / (r ^ 2 * (r ^ 2 - 1) ^ 3)) + (((-2 : ℂ) * r) / ((2 - μ))) * (((-1 : ℂ) + (1 / 2 : ℂ) * μ) / (r ^ 2)) := by
  field_simp
  ring

private theorem rec_r_qT1 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (((1 / 2 : ℂ) + (-1 : ℂ) * r ^ 2) / (r * (r ^ 2 - 1) ^ 2)) * (((6 : ℂ) * r + (-14 : ℂ) * r ^ 3 + (8 : ℂ) * r ^ 5) / ((2 - μ))) + (((1 / 2 : ℂ)) / ((r ^ 2 - 1))) * (((12 : ℂ) + (-3 : ℂ) * μ + (-52 : ℂ) * r ^ 2 + (3 : ℂ) * r ^ 2 * μ + (44 : ℂ) * r ^ 4) / ((2 - μ))) + (((-1 : ℂ) * s) / ((r ^ 2 - 1))) * (((4 : ℂ) * s * r ^ 2) / ((2 - μ))) + (((-1 / 2 : ℂ) + (1 : ℂ) * r ^ 2) / (r)) * (((-6 : ℂ) * r + (8 : ℂ) * r ^ 3) / ((r ^ 2 - 1) * (2 - μ))) + ((-1 : ℂ)) * (((-2 : ℂ) + (-1 / 2 : ℂ) * μ + (4 : ℂ) * r ^ 2) / ((2 - μ))) = (((-1 / 2 : ℂ) + (2 : ℂ) * r ^ 2) / ((2 - μ))) * (((-4 : ℂ) + (8 : ℂ) * r ^ 2) / ((r ^ 2 - 1))) + (((-1 / 2 : ℂ) * r + (1 / 2 : ℂ) * r ^ 3) / ((2 - μ))) * (((4 : ℂ) + (-4 : ℂ) * μ + (-16 : ℂ) * r ^ 2 + (4 : ℂ) * r ^ 2 * μ + (4 : ℂ) * r ^ 4 + (-8 : ℂ) * s ^ 2 * r ^ 2) / (r * (r ^ 2 - 1) ^ 2)) := by
  field_simp
  ring

private theorem rec_r_qT2 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (((1 / 2 : ℂ) + (-1 : ℂ) * r ^ 2) / (r * (r ^ 2 - 1) ^ 2)) * (((2 : ℂ) * r ^ 2 + (-4 : ℂ) * r ^ 4 + (2 : ℂ) * r ^ 6) / ((2 - μ))) + (((1 / 2 : ℂ)) / ((r ^ 2 - 1))) * (((10 : ℂ) * r + (-30 : ℂ) * r ^ 3 + (20 : ℂ) * r ^ 5) / ((2 - μ))) + (((-1 / 2 : ℂ) + (1 : ℂ) * r ^ 2) / (r)) * (((2 : ℂ) * r ^ 2) / ((2 - μ))) + ((-1 : ℂ)) * (((-1 : ℂ) * r + (1 : ℂ) * r ^ 3) / ((2 - μ))) = (((-1 / 2 : ℂ) + (2 : ℂ) * r ^ 2) / ((2 - μ))) * ((2 : ℂ) * r) + (((-1 / 2 : ℂ) * r + (1 / 2 : ℂ) * r ^ 3) / ((2 - μ))) * (((-6 : ℂ) + (10 : ℂ) * r ^ 2) / ((r ^ 2 - 1))) := by
  field_simp
  ring

private theorem rec_r_qT3 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (((1 / 2 : ℂ)) / ((r ^ 2 - 1))) * (((2 : ℂ) * r ^ 2 + (-4 : ℂ) * r ^ 4 + (2 : ℂ) * r ^ 6) / ((2 - μ))) = (((-1 / 2 : ℂ) * r + (1 / 2 : ℂ) * r ^ 3) / ((2 - μ))) * ((2 : ℂ) * r) := by
  field_simp
  ring

private theorem rec_r_qL0 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (0 : ℂ) = (((-1 : ℂ) * r ^ 2) / ((2 - μ))) * (((-2 : ℂ)) / (r ^ 3)) + (((-2 : ℂ) * r) / ((2 - μ))) * (((1 : ℂ)) / (r ^ 2)) := by
  field_simp
  ring

/-- The reconstructed jet solves the sourced harmonic `r` equation up to the master defect and the Bianchi forms of the source. -/
theorem reconstruction_R (s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4 : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    harmonicR s r μ (recF0 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4) (recF01 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4) (recF02 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4) (recF1 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4) (recF11 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4) (recF12 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4) (recF2 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4) (recF21 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4) (recF22 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4) (recH s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4) (recH1 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4) (recH2 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4) + qr0 = (((-1 / 2 : ℂ) + (2 : ℂ) * r ^ 2) / ((2 - μ))) * masterDefect0 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4 + (((-1 / 2 : ℂ) * r + (1 / 2 : ℂ) * r ^ 3) / ((2 - μ))) * masterDefect1 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4 + (((1 : ℂ) * r + (-2 : ℂ) * r ^ 3) / ((r ^ 2 - 1) * (2 - μ) * s)) * bianchiT0 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4 + (((-1 / 2 : ℂ) * r ^ 2) / ((2 - μ) * s)) * bianchiT1 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4 + (((-1 : ℂ) * r ^ 2) / ((2 - μ))) * bianchiR0 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4 + (((-2 : ℂ) * r) / ((2 - μ))) * bianchiAng0 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4 := by
  unfold harmonicR recF0 recF01 recF1 recF2 recH1 masterDefect0 masterDefect1 bianchiT0 bianchiT1 bianchiR0 bianchiAng0
  linear_combination P * rec_r_P s r μ hs hr hf hμ + P1 * rec_r_P1 s r μ hs hr hf hμ + P2 * rec_r_P2 s r μ hs hr hf hμ + P3 * rec_r_P3 s r μ hs hr hf hμ + qtt0 * rec_r_qtt0 s r μ hs hr hf hμ + qtt1 * rec_r_qtt1 s r μ hs hr hf hμ + qtr0 * rec_r_qtr0 s r μ hs hr hf hμ + qtr1 * rec_r_qtr1 s r μ hs hr hf hμ + qtr2 * rec_r_qtr2 s r μ hs hr hf hμ + qrr0 * rec_r_qrr0 s r μ hs hr hf hμ + qrr1 * rec_r_qrr1 s r μ hs hr hf hμ + qt0 * rec_r_qt0 s r μ hs hr hf hμ + qt1 * rec_r_qt1 s r μ hs hr hf hμ + qt2 * rec_r_qt2 s r μ hs hr hf hμ + qr0 * rec_r_qr0 s r μ hs hr hf hμ + qr1 * rec_r_qr1 s r μ hs hr hf hμ + qT0 * rec_r_qT0 s r μ hs hr hf hμ + qT1 * rec_r_qT1 s r μ hs hr hf hμ + qT2 * rec_r_qT2 s r μ hs hr hf hμ + qT3 * rec_r_qT3 s r μ hs hr hf hμ + qL0 * rec_r_qL0 s r μ hs hr hf hμ

private theorem rec_T_P (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (((1 / 2 : ℂ)) / ((r ^ 2 - 1))) * (((-1 / 2 : ℂ) * μ + (1 / 2 : ℂ) * r ^ 2 * μ) / (r * (2 - μ))) + ((1 / 2 : ℂ) + (-1 / 2 : ℂ) * r ^ 2) * (((1 / 2 : ℂ) * μ) / (r * (r ^ 2 - 1) * (2 - μ))) = (0 : ℂ) := by
  field_simp
  ring

private theorem rec_T_P1 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (((1 / 2 : ℂ)) / ((r ^ 2 - 1))) * (((1 : ℂ) + (-3 : ℂ) * r ^ 2 + (2 : ℂ) * r ^ 4) / ((2 - μ))) + ((1 / 2 : ℂ) + (-1 / 2 : ℂ) * r ^ 2) * (((-1 : ℂ) + (2 : ℂ) * r ^ 2) / ((r ^ 2 - 1) * (2 - μ))) = (0 : ℂ) := by
  field_simp
  ring

private theorem rec_T_P2 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (((1 / 2 : ℂ)) / ((r ^ 2 - 1))) * (((1 : ℂ) * r + (-2 : ℂ) * r ^ 3 + (1 : ℂ) * r ^ 5) / ((2 - μ))) + ((1 / 2 : ℂ) + (-1 / 2 : ℂ) * r ^ 2) * (((1 : ℂ) * r) / ((2 - μ))) = (0 : ℂ) := by
  field_simp
  ring

private theorem rec_T_qtr0 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (((1 / 2 : ℂ)) / ((r ^ 2 - 1))) * (((-1 : ℂ) * r + (4 : ℂ) * r ^ 3 + (-3 : ℂ) * r ^ 5) / ((2 - μ) * s)) + ((1 / 2 : ℂ) + (-1 / 2 : ℂ) * r ^ 2) * (((1 : ℂ) * r + (-3 : ℂ) * r ^ 3) / ((r ^ 2 - 1) * (2 - μ) * s)) = (0 : ℂ) := by
  field_simp
  ring

private theorem rec_T_qtr1 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (((1 / 2 : ℂ)) / ((r ^ 2 - 1))) * (((-1 : ℂ) * r ^ 2 + (2 : ℂ) * r ^ 4 + (-1 : ℂ) * r ^ 6) / ((2 - μ) * s)) + ((1 / 2 : ℂ) + (-1 / 2 : ℂ) * r ^ 2) * (((-1 : ℂ) * r ^ 2) / ((2 - μ) * s)) = (0 : ℂ) := by
  field_simp
  ring

private theorem rec_T_qt0 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (((1 / 2 : ℂ)) / ((r ^ 2 - 1))) * (((-2 : ℂ) + (1 : ℂ) * μ + (6 : ℂ) * r ^ 2 + (-1 : ℂ) * r ^ 2 * μ + (-4 : ℂ) * r ^ 4) / ((2 - μ) * s)) + ((1 / 2 : ℂ) + (-1 / 2 : ℂ) * r ^ 2) * (((2 : ℂ) + (-1 : ℂ) * μ + (-4 : ℂ) * r ^ 2) / ((r ^ 2 - 1) * (2 - μ) * s)) = (0 : ℂ) := by
  field_simp
  ring

private theorem rec_T_qt1 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (((1 / 2 : ℂ)) / ((r ^ 2 - 1))) * (((-2 : ℂ) * r + (4 : ℂ) * r ^ 3 + (-2 : ℂ) * r ^ 5) / ((2 - μ) * s)) + ((1 / 2 : ℂ) + (-1 / 2 : ℂ) * r ^ 2) * (((-2 : ℂ) * r) / ((2 - μ) * s)) = (0 : ℂ) := by
  field_simp
  ring

private theorem rec_T_qT0 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (((1 / 2 : ℂ)) / ((r ^ 2 - 1))) * (((6 : ℂ) + (-3 : ℂ) * μ + (-10 : ℂ) * r ^ 2 + (3 : ℂ) * r ^ 2 * μ + (4 : ℂ) * r ^ 4) / ((2 - μ))) + ((1 / 2 : ℂ) + (-1 / 2 : ℂ) * r ^ 2) * (((-2 : ℂ) + (1 : ℂ) * μ + (4 : ℂ) * r ^ 2) / ((r ^ 2 - 1) * (2 - μ))) + (1 : ℂ) = (0 : ℂ) := by
  field_simp
  ring

private theorem rec_T_qT1 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (((1 / 2 : ℂ)) / ((r ^ 2 - 1))) * (((6 : ℂ) * r + (-14 : ℂ) * r ^ 3 + (8 : ℂ) * r ^ 5) / ((2 - μ))) + ((1 / 2 : ℂ) + (-1 / 2 : ℂ) * r ^ 2) * (((-6 : ℂ) * r + (8 : ℂ) * r ^ 3) / ((r ^ 2 - 1) * (2 - μ))) = (0 : ℂ) := by
  field_simp
  ring

private theorem rec_T_qT2 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (((1 / 2 : ℂ)) / ((r ^ 2 - 1))) * (((2 : ℂ) * r ^ 2 + (-4 : ℂ) * r ^ 4 + (2 : ℂ) * r ^ 6) / ((2 - μ))) + ((1 / 2 : ℂ) + (-1 / 2 : ℂ) * r ^ 2) * (((2 : ℂ) * r ^ 2) / ((2 - μ))) = (0 : ℂ) := by
  field_simp
  ring

/-- The reconstructed jet solves the sourced harmonic `T` equation up to the master defect and the Bianchi forms of the source. -/
theorem reconstruction_TF (s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4 : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    harmonicTF s r μ (recF0 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4) (recF01 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4) (recF02 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4) (recF1 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4) (recF11 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4) (recF12 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4) (recF2 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4) (recF21 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4) (recF22 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4) (recH s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4) (recH1 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4) (recH2 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4) + qT0 = (0 : ℂ) := by
  unfold harmonicTF recF0 recF2
  linear_combination P * rec_T_P s r μ hs hr hf hμ + P1 * rec_T_P1 s r μ hs hr hf hμ + P2 * rec_T_P2 s r μ hs hr hf hμ + qtr0 * rec_T_qtr0 s r μ hs hr hf hμ + qtr1 * rec_T_qtr1 s r μ hs hr hf hμ + qt0 * rec_T_qt0 s r μ hs hr hf hμ + qt1 * rec_T_qt1 s r μ hs hr hf hμ + qT0 * rec_T_qT0 s r μ hs hr hf hμ + qT1 * rec_T_qT1 s r μ hs hr hf hμ + qT2 * rec_T_qT2 s r μ hs hr hf hμ

private theorem rec_L_P (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (((1 / 4 : ℂ) * μ + (-2 : ℂ) * r ^ 2 + (-1 / 4 : ℂ) * r ^ 2 * μ + (1 : ℂ) * r ^ 4) / ((r ^ 2 - 1) ^ 2)) * (((-1 / 2 : ℂ) * μ + (1 / 2 : ℂ) * r ^ 2 * μ) / (r * (2 - μ))) + (((1 / 2 : ℂ) * r) / ((r ^ 2 - 1))) * (((1 / 2 : ℂ) * μ + (1 / 2 : ℂ) * r ^ 2 * μ) / (r ^ 2 * (2 - μ))) + ((-1 / 2 : ℂ) * r ^ 2) * (((-1 : ℂ) * μ) / (r ^ 3 * (2 - μ))) + (((-2 : ℂ) * s * r + (4 : ℂ) * s * r ^ 3) / ((r ^ 2 - 1))) * (((-2 : ℂ) * s) / ((r ^ 2 - 1) * (2 - μ))) + ((2 : ℂ) * s * r ^ 2) * (((4 : ℂ) * s * r) / ((r ^ 2 - 1) ^ 2 * (2 - μ))) + ((-1 / 4 : ℂ) * μ + (4 : ℂ) * r ^ 2 + (1 / 4 : ℂ) * r ^ 2 * μ + (-5 : ℂ) * r ^ 4 + (-2 : ℂ) * s ^ 2 * r ^ 2) * (((1 / 2 : ℂ) * μ) / (r * (r ^ 2 - 1) * (2 - μ))) + ((-1 / 2 : ℂ) * r + (3 / 2 : ℂ) * r ^ 3 + (-1 : ℂ) * r ^ 5) * (((1 / 2 : ℂ) * μ + (-3 / 2 : ℂ) * r ^ 2 * μ) / (r ^ 2 * (r ^ 2 - 1) ^ 2 * (2 - μ))) + (((-4 : ℂ) * s ^ 2 * r ^ 2) / ((r ^ 2 - 1))) * (((-1 / 4 : ℂ) * μ) / (r * (2 - μ))) + ((-2 : ℂ) * r + (4 : ℂ) * r ^ 3) * (((1 / 4 : ℂ) * μ) / (r ^ 2 * (2 - μ))) + ((-1 : ℂ) * r ^ 2 + (1 : ℂ) * r ^ 4) * (((-1 / 2 : ℂ) * μ) / (r ^ 3 * (2 - μ))) = (((-1 : ℂ) * r + (10 : ℂ) * r ^ 3 + (-12 : ℂ) * r ^ 5) / ((2 - μ))) * (((-1 : ℂ) * μ + (1 : ℂ) * r ^ 2 * μ + (-4 : ℂ) * s ^ 2 * r ^ 2) / (r ^ 2 * (r ^ 2 - 1) ^ 2)) + (((-2 : ℂ) * r ^ 2 + (15 / 2 : ℂ) * r ^ 4 + (-11 / 2 : ℂ) * r ^ 6) / ((2 - μ))) * (((-2 : ℂ) * μ + (6 : ℂ) * r ^ 2 * μ + (-4 : ℂ) * r ^ 4 * μ + (16 : ℂ) * s ^ 2 * r ^ 4) / (r ^ 3 * (r ^ 2 - 1) ^ 3)) + (((-1 / 2 : ℂ) * r ^ 3 + (1 : ℂ) * r ^ 5 + (-1 / 2 : ℂ) * r ^ 7) / ((2 - μ))) * (((-6 : ℂ) * μ + (24 : ℂ) * r ^ 2 * μ + (-38 : ℂ) * r ^ 4 * μ + (20 : ℂ) * r ^ 6 * μ + (-16 : ℂ) * s ^ 2 * r ^ 4 + (-80 : ℂ) * s ^ 2 * r ^ 6) / (r ^ 4 * (r ^ 2 - 1) ^ 4)) := by
  field_simp
  ring

private theorem rec_L_P1 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (((1 / 4 : ℂ) * μ + (-2 : ℂ) * r ^ 2 + (-1 / 4 : ℂ) * r ^ 2 * μ + (1 : ℂ) * r ^ 4) / ((r ^ 2 - 1) ^ 2)) * (((1 : ℂ) + (-3 : ℂ) * r ^ 2 + (2 : ℂ) * r ^ 4) / ((2 - μ))) + (((1 / 2 : ℂ) * r) / ((r ^ 2 - 1))) * (((-1 / 2 : ℂ) * μ + (-6 : ℂ) * r ^ 2 + (1 / 2 : ℂ) * r ^ 2 * μ + (8 : ℂ) * r ^ 4) / (r * (2 - μ))) + ((-1 / 2 : ℂ) * r ^ 2) * (((1 : ℂ) * μ + (-6 : ℂ) * r ^ 2 + (1 : ℂ) * r ^ 2 * μ + (24 : ℂ) * r ^ 4) / (r ^ 2 * (2 - μ))) + (((-2 : ℂ) * s * r + (4 : ℂ) * s * r ^ 3) / ((r ^ 2 - 1))) * (((2 : ℂ) * s * r) / ((2 - μ))) + ((2 : ℂ) * s * r ^ 2) * (((-4 : ℂ) * s + (2 : ℂ) * s * r ^ 2) / ((r ^ 2 - 1) * (2 - μ))) + ((-1 / 4 : ℂ) * μ + (4 : ℂ) * r ^ 2 + (1 / 4 : ℂ) * r ^ 2 * μ + (-5 : ℂ) * r ^ 4 + (-2 : ℂ) * s ^ 2 * r ^ 2) * (((-1 : ℂ) + (2 : ℂ) * r ^ 2) / ((r ^ 2 - 1) * (2 - μ))) + ((-1 / 2 : ℂ) * r + (3 / 2 : ℂ) * r ^ 3 + (-1 : ℂ) * r ^ 5) * (((-1 / 2 : ℂ) * μ + (-2 : ℂ) * r ^ 2 + (1 / 2 : ℂ) * r ^ 2 * μ) / (r * (r ^ 2 - 1) ^ 2 * (2 - μ))) + (((-4 : ℂ) * s ^ 2 * r ^ 2) / ((r ^ 2 - 1))) * (((-1 / 2 : ℂ) + (1 / 2 : ℂ) * r ^ 2) / ((2 - μ))) + ((-2 : ℂ) * r + (4 : ℂ) * r ^ 3) * (((-1 / 4 : ℂ) * μ + (1 : ℂ) * r ^ 2) / (r * (2 - μ))) + ((-1 : ℂ) * r ^ 2 + (1 : ℂ) * r ^ 4) * (((1 / 2 : ℂ) * μ + (1 : ℂ) * r ^ 2) / (r ^ 2 * (2 - μ))) = (((-1 : ℂ) * r + (10 : ℂ) * r ^ 3 + (-12 : ℂ) * r ^ 5) / ((2 - μ))) * (((2 : ℂ) * r) / ((r ^ 2 - 1))) + (((-2 : ℂ) * r ^ 2 + (15 / 2 : ℂ) * r ^ 4 + (-11 / 2 : ℂ) * r ^ 6) / ((2 - μ))) * (((-1 : ℂ) * μ + (-2 : ℂ) * r ^ 2 + (1 : ℂ) * r ^ 2 * μ + (-2 : ℂ) * r ^ 4 + (-4 : ℂ) * s ^ 2 * r ^ 2) / (r ^ 2 * (r ^ 2 - 1) ^ 2)) + (((-1 / 2 : ℂ) * r ^ 3 + (1 : ℂ) * r ^ 5 + (-1 / 2 : ℂ) * r ^ 7) / ((2 - μ))) * (((-4 : ℂ) * μ + (12 : ℂ) * r ^ 2 * μ + (12 : ℂ) * r ^ 4 + (-8 : ℂ) * r ^ 4 * μ + (4 : ℂ) * r ^ 6 + (32 : ℂ) * s ^ 2 * r ^ 4) / (r ^ 3 * (r ^ 2 - 1) ^ 3)) := by
  field_simp
  ring

private theorem rec_L_P2 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (((1 / 4 : ℂ) * μ + (-2 : ℂ) * r ^ 2 + (-1 / 4 : ℂ) * r ^ 2 * μ + (1 : ℂ) * r ^ 4) / ((r ^ 2 - 1) ^ 2)) * (((1 : ℂ) * r + (-2 : ℂ) * r ^ 3 + (1 : ℂ) * r ^ 5) / ((2 - μ))) + (((1 / 2 : ℂ) * r) / ((r ^ 2 - 1))) * (((2 : ℂ) + (-9 : ℂ) * r ^ 2 + (7 : ℂ) * r ^ 4) / ((2 - μ))) + ((-1 / 2 : ℂ) * r ^ 2) * (((-1 / 2 : ℂ) * μ + (-24 : ℂ) * r ^ 2 + (1 / 2 : ℂ) * r ^ 2 * μ + (36 : ℂ) * r ^ 4) / (r * (2 - μ))) + ((2 : ℂ) * s * r ^ 2) * (((2 : ℂ) * s * r) / ((2 - μ))) + ((-1 / 4 : ℂ) * μ + (4 : ℂ) * r ^ 2 + (1 / 4 : ℂ) * r ^ 2 * μ + (-5 : ℂ) * r ^ 4 + (-2 : ℂ) * s ^ 2 * r ^ 2) * (((1 : ℂ) * r) / ((2 - μ))) + ((-1 / 2 : ℂ) * r + (3 / 2 : ℂ) * r ^ 3 + (-1 : ℂ) * r ^ 5) * (((-2 : ℂ) + (3 : ℂ) * r ^ 2) / ((r ^ 2 - 1) * (2 - μ))) + ((-2 : ℂ) * r + (4 : ℂ) * r ^ 3) * (((-1 / 2 : ℂ) + (1 / 2 : ℂ) * r ^ 2) / ((2 - μ))) + ((-1 : ℂ) * r ^ 2 + (1 : ℂ) * r ^ 4) * (((-1 / 4 : ℂ) * μ + (2 : ℂ) * r ^ 2) / (r * (2 - μ))) = (((-1 : ℂ) * r + (10 : ℂ) * r ^ 3 + (-12 : ℂ) * r ^ 5) / ((2 - μ))) * ((1 : ℂ)) + (((-2 : ℂ) * r ^ 2 + (15 / 2 : ℂ) * r ^ 4 + (-11 / 2 : ℂ) * r ^ 6) / ((2 - μ))) * (((2 : ℂ) * r) / ((r ^ 2 - 1))) + (((-1 / 2 : ℂ) * r ^ 3 + (1 : ℂ) * r ^ 5 + (-1 / 2 : ℂ) * r ^ 7) / ((2 - μ))) * (((-1 : ℂ) * μ + (-4 : ℂ) * r ^ 2 + (1 : ℂ) * r ^ 2 * μ + (-4 : ℂ) * r ^ 4 + (-4 : ℂ) * s ^ 2 * r ^ 2) / (r ^ 2 * (r ^ 2 - 1) ^ 2)) := by
  field_simp
  ring

private theorem rec_L_P3 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (((1 / 2 : ℂ) * r) / ((r ^ 2 - 1))) * (((1 : ℂ) * r + (-2 : ℂ) * r ^ 3 + (1 : ℂ) * r ^ 5) / ((2 - μ))) + ((-1 / 2 : ℂ) * r ^ 2) * (((3 : ℂ) + (-15 : ℂ) * r ^ 2 + (12 : ℂ) * r ^ 4) / ((2 - μ))) + ((-1 / 2 : ℂ) * r + (3 / 2 : ℂ) * r ^ 3 + (-1 : ℂ) * r ^ 5) * (((1 : ℂ) * r) / ((2 - μ))) + ((-1 : ℂ) * r ^ 2 + (1 : ℂ) * r ^ 4) * (((-1 / 2 : ℂ) + (1 / 2 : ℂ) * r ^ 2) / ((2 - μ))) = (((-2 : ℂ) * r ^ 2 + (15 / 2 : ℂ) * r ^ 4 + (-11 / 2 : ℂ) * r ^ 6) / ((2 - μ))) * ((1 : ℂ)) + (((-1 / 2 : ℂ) * r ^ 3 + (1 : ℂ) * r ^ 5 + (-1 / 2 : ℂ) * r ^ 7) / ((2 - μ))) * (((2 : ℂ) * r) / ((r ^ 2 - 1))) := by
  field_simp
  ring

private theorem rec_L_P4 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    ((-1 / 2 : ℂ) * r ^ 2) * (((1 : ℂ) * r + (-2 : ℂ) * r ^ 3 + (1 : ℂ) * r ^ 5) / ((2 - μ))) = (((-1 / 2 : ℂ) * r ^ 3 + (1 : ℂ) * r ^ 5 + (-1 / 2 : ℂ) * r ^ 7) / ((2 - μ))) * ((1 : ℂ)) := by
  field_simp
  ring

private theorem rec_L_qtt0 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (0 : ℂ) = (((-1 : ℂ) * r + (10 : ℂ) * r ^ 3 + (-12 : ℂ) * r ^ 5) / ((2 - μ))) * (((-2 : ℂ) * r) / ((r ^ 2 - 1) ^ 2)) + (((-2 : ℂ) * r ^ 2 + (15 / 2 : ℂ) * r ^ 4 + (-11 / 2 : ℂ) * r ^ 6) / ((2 - μ))) * (((2 : ℂ) + (6 : ℂ) * r ^ 2) / ((r ^ 2 - 1) ^ 3)) + (((-1 / 2 : ℂ) * r ^ 3 + (1 : ℂ) * r ^ 5 + (-1 / 2 : ℂ) * r ^ 7) / ((2 - μ))) * (((-24 : ℂ) * r + (-24 : ℂ) * r ^ 3) / ((r ^ 2 - 1) ^ 4)) + (((-3 : ℂ) * r ^ 2 + (10 : ℂ) * r ^ 4) / ((2 - μ) * s)) * (((-2 : ℂ) * s) / ((r ^ 2 - 1))) + (((-3 : ℂ) * r ^ 3 + (5 : ℂ) * r ^ 5) / ((2 - μ) * s)) * (((4 : ℂ) * s * r) / ((r ^ 2 - 1) ^ 2)) + (((-1 / 2 : ℂ) * r ^ 4 + (1 / 2 : ℂ) * r ^ 6) / ((2 - μ) * s)) * (((-4 : ℂ) * s + (-12 : ℂ) * s * r ^ 2) / ((r ^ 2 - 1) ^ 3)) + (((-4 : ℂ) * r ^ 3 + (6 : ℂ) * r ^ 5) / ((2 - μ))) * (((1 : ℂ) * r) / ((r ^ 2 - 1) ^ 2)) + (((-1 : ℂ) * r ^ 4 + (1 : ℂ) * r ^ 6) / ((2 - μ))) * (((-1 : ℂ) + (-3 : ℂ) * r ^ 2) / ((r ^ 2 - 1) ^ 3)) := by
  field_simp
  ring

private theorem rec_L_qtt1 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (0 : ℂ) = (((-2 : ℂ) * r ^ 2 + (15 / 2 : ℂ) * r ^ 4 + (-11 / 2 : ℂ) * r ^ 6) / ((2 - μ))) * (((-2 : ℂ) * r) / ((r ^ 2 - 1) ^ 2)) + (((-1 / 2 : ℂ) * r ^ 3 + (1 : ℂ) * r ^ 5 + (-1 / 2 : ℂ) * r ^ 7) / ((2 - μ))) * (((4 : ℂ) + (12 : ℂ) * r ^ 2) / ((r ^ 2 - 1) ^ 3)) + (((-3 : ℂ) * r ^ 3 + (5 : ℂ) * r ^ 5) / ((2 - μ) * s)) * (((-2 : ℂ) * s) / ((r ^ 2 - 1))) + (((-1 / 2 : ℂ) * r ^ 4 + (1 / 2 : ℂ) * r ^ 6) / ((2 - μ) * s)) * (((8 : ℂ) * s * r) / ((r ^ 2 - 1) ^ 2)) + (((-1 : ℂ) * r ^ 4 + (1 : ℂ) * r ^ 6) / ((2 - μ))) * (((1 : ℂ) * r) / ((r ^ 2 - 1) ^ 2)) := by
  field_simp
  ring

private theorem rec_L_qtt2 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (0 : ℂ) = (((-1 / 2 : ℂ) * r ^ 3 + (1 : ℂ) * r ^ 5 + (-1 / 2 : ℂ) * r ^ 7) / ((2 - μ))) * (((-2 : ℂ) * r) / ((r ^ 2 - 1) ^ 2)) + (((-1 / 2 : ℂ) * r ^ 4 + (1 / 2 : ℂ) * r ^ 6) / ((2 - μ) * s)) * (((-2 : ℂ) * s) / ((r ^ 2 - 1))) := by
  field_simp
  ring

private theorem rec_L_qtr0 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (((1 / 4 : ℂ) * μ + (-2 : ℂ) * r ^ 2 + (-1 / 4 : ℂ) * r ^ 2 * μ + (1 : ℂ) * r ^ 4) / ((r ^ 2 - 1) ^ 2)) * (((-1 : ℂ) * r + (4 : ℂ) * r ^ 3 + (-3 : ℂ) * r ^ 5) / ((2 - μ) * s)) + (((1 / 2 : ℂ) * r) / ((r ^ 2 - 1))) * (((-1 : ℂ) + (12 : ℂ) * r ^ 2 + (-15 : ℂ) * r ^ 4) / ((2 - μ) * s)) + ((-1 / 2 : ℂ) * r ^ 2) * (((24 : ℂ) * r + (-60 : ℂ) * r ^ 3) / ((2 - μ) * s)) + (((-2 : ℂ) * s * r + (4 : ℂ) * s * r ^ 3) / ((r ^ 2 - 1))) * (((-2 : ℂ) * r ^ 2) / ((2 - μ))) + ((2 : ℂ) * s * r ^ 2) * (((-4 : ℂ) * r) / ((2 - μ))) + ((-1 / 4 : ℂ) * μ + (4 : ℂ) * r ^ 2 + (1 / 4 : ℂ) * r ^ 2 * μ + (-5 : ℂ) * r ^ 4 + (-2 : ℂ) * s ^ 2 * r ^ 2) * (((1 : ℂ) * r + (-3 : ℂ) * r ^ 3) / ((r ^ 2 - 1) * (2 - μ) * s)) + ((-1 / 2 : ℂ) * r + (3 / 2 : ℂ) * r ^ 3 + (-1 : ℂ) * r ^ 5) * (((-1 : ℂ) + (8 : ℂ) * r ^ 2 + (-3 : ℂ) * r ^ 4) / ((r ^ 2 - 1) ^ 2 * (2 - μ) * s)) + (((-4 : ℂ) * s ^ 2 * r ^ 2) / ((r ^ 2 - 1))) * (((1 / 2 : ℂ) * r + (-1 / 2 : ℂ) * r ^ 3) / ((2 - μ) * s)) + ((-2 : ℂ) * r + (4 : ℂ) * r ^ 3) * (((1 / 2 : ℂ) + (-3 / 2 : ℂ) * r ^ 2) / ((2 - μ) * s)) + ((-1 : ℂ) * r ^ 2 + (1 : ℂ) * r ^ 4) * (((-3 : ℂ) * r) / ((2 - μ) * s)) = (((-1 : ℂ) * r + (10 : ℂ) * r ^ 3 + (-12 : ℂ) * r ^ 5) / ((2 - μ))) * (((2 : ℂ)) / (s)) + (((-3 : ℂ) * r ^ 2 + (10 : ℂ) * r ^ 4) / ((2 - μ) * s)) * (((-2 : ℂ) + (4 : ℂ) * r ^ 2) / (r)) + (((-3 : ℂ) * r ^ 3 + (5 : ℂ) * r ^ 5) / ((2 - μ) * s)) * (((2 : ℂ) + (4 : ℂ) * r ^ 2) / (r ^ 2)) + (((-1 / 2 : ℂ) * r ^ 4 + (1 / 2 : ℂ) * r ^ 6) / ((2 - μ) * s)) * (((-4 : ℂ)) / (r ^ 3)) + (((-4 : ℂ) * r ^ 3 + (6 : ℂ) * r ^ 5) / ((2 - μ))) * (((-2 : ℂ) * s) / ((r ^ 2 - 1))) + (((-1 : ℂ) * r ^ 4 + (1 : ℂ) * r ^ 6) / ((2 - μ))) * (((4 : ℂ) * s * r) / ((r ^ 2 - 1) ^ 2)) := by
  field_simp
  ring

private theorem rec_L_qtr1 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (((1 / 4 : ℂ) * μ + (-2 : ℂ) * r ^ 2 + (-1 / 4 : ℂ) * r ^ 2 * μ + (1 : ℂ) * r ^ 4) / ((r ^ 2 - 1) ^ 2)) * (((-1 : ℂ) * r ^ 2 + (2 : ℂ) * r ^ 4 + (-1 : ℂ) * r ^ 6) / ((2 - μ) * s)) + (((1 / 2 : ℂ) * r) / ((r ^ 2 - 1))) * (((-3 : ℂ) * r + (12 : ℂ) * r ^ 3 + (-9 : ℂ) * r ^ 5) / ((2 - μ) * s)) + ((-1 / 2 : ℂ) * r ^ 2) * (((-4 : ℂ) + (48 : ℂ) * r ^ 2 + (-60 : ℂ) * r ^ 4) / ((2 - μ) * s)) + ((2 : ℂ) * s * r ^ 2) * (((-2 : ℂ) * r ^ 2) / ((2 - μ))) + ((-1 / 4 : ℂ) * μ + (4 : ℂ) * r ^ 2 + (1 / 4 : ℂ) * r ^ 2 * μ + (-5 : ℂ) * r ^ 4 + (-2 : ℂ) * s ^ 2 * r ^ 2) * (((-1 : ℂ) * r ^ 2) / ((2 - μ) * s)) + ((-1 / 2 : ℂ) * r + (3 / 2 : ℂ) * r ^ 3 + (-1 : ℂ) * r ^ 5) * (((3 : ℂ) * r + (-5 : ℂ) * r ^ 3) / ((r ^ 2 - 1) * (2 - μ) * s)) + ((-2 : ℂ) * r + (4 : ℂ) * r ^ 3) * (((1 / 2 : ℂ) * r + (-1 / 2 : ℂ) * r ^ 3) / ((2 - μ) * s)) + ((-1 : ℂ) * r ^ 2 + (1 : ℂ) * r ^ 4) * (((1 : ℂ) + (-3 : ℂ) * r ^ 2) / ((2 - μ) * s)) = (((-2 : ℂ) * r ^ 2 + (15 / 2 : ℂ) * r ^ 4 + (-11 / 2 : ℂ) * r ^ 6) / ((2 - μ))) * (((2 : ℂ)) / (s)) + (((-3 : ℂ) * r ^ 2 + (10 : ℂ) * r ^ 4) / ((2 - μ) * s)) * ((-1 : ℂ) + (1 : ℂ) * r ^ 2) + (((-3 : ℂ) * r ^ 3 + (5 : ℂ) * r ^ 5) / ((2 - μ) * s)) * (((-2 : ℂ) + (6 : ℂ) * r ^ 2) / (r)) + (((-1 / 2 : ℂ) * r ^ 4 + (1 / 2 : ℂ) * r ^ 6) / ((2 - μ) * s)) * (((4 : ℂ) + (10 : ℂ) * r ^ 2) / (r ^ 2)) + (((-1 : ℂ) * r ^ 4 + (1 : ℂ) * r ^ 6) / ((2 - μ))) * (((-2 : ℂ) * s) / ((r ^ 2 - 1))) := by
  field_simp
  ring

private theorem rec_L_qtr2 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (((1 / 2 : ℂ) * r) / ((r ^ 2 - 1))) * (((-1 : ℂ) * r ^ 2 + (2 : ℂ) * r ^ 4 + (-1 : ℂ) * r ^ 6) / ((2 - μ) * s)) + ((-1 / 2 : ℂ) * r ^ 2) * (((-5 : ℂ) * r + (20 : ℂ) * r ^ 3 + (-15 : ℂ) * r ^ 5) / ((2 - μ) * s)) + ((-1 / 2 : ℂ) * r + (3 / 2 : ℂ) * r ^ 3 + (-1 : ℂ) * r ^ 5) * (((-1 : ℂ) * r ^ 2) / ((2 - μ) * s)) + ((-1 : ℂ) * r ^ 2 + (1 : ℂ) * r ^ 4) * (((1 / 2 : ℂ) * r + (-1 / 2 : ℂ) * r ^ 3) / ((2 - μ) * s)) = (((-1 / 2 : ℂ) * r ^ 3 + (1 : ℂ) * r ^ 5 + (-1 / 2 : ℂ) * r ^ 7) / ((2 - μ))) * (((2 : ℂ)) / (s)) + (((-3 : ℂ) * r ^ 3 + (5 : ℂ) * r ^ 5) / ((2 - μ) * s)) * ((-1 : ℂ) + (1 : ℂ) * r ^ 2) + (((-1 / 2 : ℂ) * r ^ 4 + (1 / 2 : ℂ) * r ^ 6) / ((2 - μ) * s)) * (((-2 : ℂ) + (8 : ℂ) * r ^ 2) / (r)) := by
  field_simp
  ring

private theorem rec_L_qtr3 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    ((-1 / 2 : ℂ) * r ^ 2) * (((-1 : ℂ) * r ^ 2 + (2 : ℂ) * r ^ 4 + (-1 : ℂ) * r ^ 6) / ((2 - μ) * s)) = (((-1 / 2 : ℂ) * r ^ 4 + (1 / 2 : ℂ) * r ^ 6) / ((2 - μ) * s)) * ((-1 : ℂ) + (1 : ℂ) * r ^ 2) := by
  field_simp
  ring

private theorem rec_L_qrr0 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (0 : ℂ) = (((-1 : ℂ) * r + (10 : ℂ) * r ^ 3 + (-12 : ℂ) * r ^ 5) / ((2 - μ))) * ((2 : ℂ) * r) + (((-2 : ℂ) * r ^ 2 + (15 / 2 : ℂ) * r ^ 4 + (-11 / 2 : ℂ) * r ^ 6) / ((2 - μ))) * ((2 : ℂ)) + (((-4 : ℂ) * r ^ 3 + (6 : ℂ) * r ^ 5) / ((2 - μ))) * (((-2 : ℂ) + (5 : ℂ) * r ^ 2) / (r)) + (((-1 : ℂ) * r ^ 4 + (1 : ℂ) * r ^ 6) / ((2 - μ))) * (((2 : ℂ) + (5 : ℂ) * r ^ 2) / (r ^ 2)) := by
  field_simp
  ring

private theorem rec_L_qrr1 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (0 : ℂ) = (((-2 : ℂ) * r ^ 2 + (15 / 2 : ℂ) * r ^ 4 + (-11 / 2 : ℂ) * r ^ 6) / ((2 - μ))) * ((2 : ℂ) * r) + (((-1 / 2 : ℂ) * r ^ 3 + (1 : ℂ) * r ^ 5 + (-1 / 2 : ℂ) * r ^ 7) / ((2 - μ))) * ((4 : ℂ)) + (((-4 : ℂ) * r ^ 3 + (6 : ℂ) * r ^ 5) / ((2 - μ))) * ((-1 : ℂ) + (1 : ℂ) * r ^ 2) + (((-1 : ℂ) * r ^ 4 + (1 : ℂ) * r ^ 6) / ((2 - μ))) * (((-2 : ℂ) + (7 : ℂ) * r ^ 2) / (r)) := by
  field_simp
  ring

private theorem rec_L_qrr2 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (0 : ℂ) = (((-1 / 2 : ℂ) * r ^ 3 + (1 : ℂ) * r ^ 5 + (-1 / 2 : ℂ) * r ^ 7) / ((2 - μ))) * ((2 : ℂ) * r) + (((-1 : ℂ) * r ^ 4 + (1 : ℂ) * r ^ 6) / ((2 - μ))) * ((-1 : ℂ) + (1 : ℂ) * r ^ 2) := by
  field_simp
  ring

private theorem rec_L_qt0 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (((1 / 4 : ℂ) * μ + (-2 : ℂ) * r ^ 2 + (-1 / 4 : ℂ) * r ^ 2 * μ + (1 : ℂ) * r ^ 4) / ((r ^ 2 - 1) ^ 2)) * (((-2 : ℂ) + (1 : ℂ) * μ + (6 : ℂ) * r ^ 2 + (-1 : ℂ) * r ^ 2 * μ + (-4 : ℂ) * r ^ 4) / ((2 - μ) * s)) + (((1 / 2 : ℂ) * r) / ((r ^ 2 - 1))) * (((12 : ℂ) * r + (-2 : ℂ) * r * μ + (-16 : ℂ) * r ^ 3) / ((2 - μ) * s)) + ((-1 / 2 : ℂ) * r ^ 2) * (((12 : ℂ) + (-2 : ℂ) * μ + (-48 : ℂ) * r ^ 2) / ((2 - μ) * s)) + (((-2 : ℂ) * s * r + (4 : ℂ) * s * r ^ 3) / ((r ^ 2 - 1))) * (((-4 : ℂ) * r) / ((2 - μ))) + ((2 : ℂ) * s * r ^ 2) * (((-4 : ℂ)) / ((2 - μ))) + ((-1 / 4 : ℂ) * μ + (4 : ℂ) * r ^ 2 + (1 / 4 : ℂ) * r ^ 2 * μ + (-5 : ℂ) * r ^ 4 + (-2 : ℂ) * s ^ 2 * r ^ 2) * (((2 : ℂ) + (-1 : ℂ) * μ + (-4 : ℂ) * r ^ 2) / ((r ^ 2 - 1) * (2 - μ) * s)) + ((-1 / 2 : ℂ) * r + (3 / 2 : ℂ) * r ^ 3 + (-1 : ℂ) * r ^ 5) * (((4 : ℂ) * r + (2 : ℂ) * r * μ) / ((r ^ 2 - 1) ^ 2 * (2 - μ) * s)) + (((-4 : ℂ) * s ^ 2 * r ^ 2) / ((r ^ 2 - 1))) * (((1 : ℂ) + (-1 : ℂ) * r ^ 2) / ((2 - μ) * s)) + ((-2 : ℂ) * r + (4 : ℂ) * r ^ 3) * (((-2 : ℂ) * r) / ((2 - μ) * s)) + ((-1 : ℂ) * r ^ 2 + (1 : ℂ) * r ^ 4) * (((-2 : ℂ)) / ((2 - μ) * s)) = (((-1 : ℂ) * r + (10 : ℂ) * r ^ 3 + (-12 : ℂ) * r ^ 5) / ((2 - μ))) * (((-4 : ℂ) * r) / ((r ^ 2 - 1) * s)) + (((-2 : ℂ) * r ^ 2 + (15 / 2 : ℂ) * r ^ 4 + (-11 / 2 : ℂ) * r ^ 6) / ((2 - μ))) * (((4 : ℂ) + (4 : ℂ) * r ^ 2) / ((r ^ 2 - 1) ^ 2 * s)) + (((-1 / 2 : ℂ) * r ^ 3 + (1 : ℂ) * r ^ 5 + (-1 / 2 : ℂ) * r ^ 7) / ((2 - μ))) * (((-24 : ℂ) * r + (-8 : ℂ) * r ^ 3) / ((r ^ 2 - 1) ^ 3 * s)) + (((-3 : ℂ) * r ^ 2 + (10 : ℂ) * r ^ 4) / ((2 - μ) * s)) * (((1 : ℂ) * μ) / (r ^ 2)) + (((-3 : ℂ) * r ^ 3 + (5 : ℂ) * r ^ 5) / ((2 - μ) * s)) * (((-2 : ℂ) * μ) / (r ^ 3)) + (((-1 / 2 : ℂ) * r ^ 4 + (1 / 2 : ℂ) * r ^ 6) / ((2 - μ) * s)) * (((6 : ℂ) * μ) / (r ^ 4)) + (((-4 : ℂ) * r ^ 2 + (-1 : ℂ) * r ^ 2 * μ + (10 : ℂ) * r ^ 4) / ((2 - μ))) * (((-2 : ℂ) * s) / ((r ^ 2 - 1))) + (((-2 : ℂ) * r ^ 3 + (2 : ℂ) * r ^ 5) / ((2 - μ))) * (((4 : ℂ) * s * r) / ((r ^ 2 - 1) ^ 2)) := by
  field_simp
  ring

private theorem rec_L_qt1 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (((1 / 4 : ℂ) * μ + (-2 : ℂ) * r ^ 2 + (-1 / 4 : ℂ) * r ^ 2 * μ + (1 : ℂ) * r ^ 4) / ((r ^ 2 - 1) ^ 2)) * (((-2 : ℂ) * r + (4 : ℂ) * r ^ 3 + (-2 : ℂ) * r ^ 5) / ((2 - μ) * s)) + (((1 / 2 : ℂ) * r) / ((r ^ 2 - 1))) * (((-4 : ℂ) + (1 : ℂ) * μ + (18 : ℂ) * r ^ 2 + (-1 : ℂ) * r ^ 2 * μ + (-14 : ℂ) * r ^ 4) / ((2 - μ) * s)) + ((-1 / 2 : ℂ) * r ^ 2) * (((48 : ℂ) * r + (-4 : ℂ) * r * μ + (-72 : ℂ) * r ^ 3) / ((2 - μ) * s)) + ((2 : ℂ) * s * r ^ 2) * (((-4 : ℂ) * r) / ((2 - μ))) + ((-1 / 4 : ℂ) * μ + (4 : ℂ) * r ^ 2 + (1 / 4 : ℂ) * r ^ 2 * μ + (-5 : ℂ) * r ^ 4 + (-2 : ℂ) * s ^ 2 * r ^ 2) * (((-2 : ℂ) * r) / ((2 - μ) * s)) + ((-1 / 2 : ℂ) * r + (3 / 2 : ℂ) * r ^ 3 + (-1 : ℂ) * r ^ 5) * (((4 : ℂ) + (-1 : ℂ) * μ + (-6 : ℂ) * r ^ 2) / ((r ^ 2 - 1) * (2 - μ) * s)) + ((-2 : ℂ) * r + (4 : ℂ) * r ^ 3) * (((1 : ℂ) + (-1 : ℂ) * r ^ 2) / ((2 - μ) * s)) + ((-1 : ℂ) * r ^ 2 + (1 : ℂ) * r ^ 4) * (((-4 : ℂ) * r) / ((2 - μ) * s)) = (((-1 : ℂ) * r + (10 : ℂ) * r ^ 3 + (-12 : ℂ) * r ^ 5) / ((2 - μ))) * (((-2 : ℂ)) / (s)) + (((-2 : ℂ) * r ^ 2 + (15 / 2 : ℂ) * r ^ 4 + (-11 / 2 : ℂ) * r ^ 6) / ((2 - μ))) * (((-4 : ℂ) * r) / ((r ^ 2 - 1) * s)) + (((-1 / 2 : ℂ) * r ^ 3 + (1 : ℂ) * r ^ 5 + (-1 / 2 : ℂ) * r ^ 7) / ((2 - μ))) * (((8 : ℂ) + (8 : ℂ) * r ^ 2) / ((r ^ 2 - 1) ^ 2 * s)) + (((-3 : ℂ) * r ^ 3 + (5 : ℂ) * r ^ 5) / ((2 - μ) * s)) * (((1 : ℂ) * μ) / (r ^ 2)) + (((-1 / 2 : ℂ) * r ^ 4 + (1 / 2 : ℂ) * r ^ 6) / ((2 - μ) * s)) * (((-4 : ℂ) * μ) / (r ^ 3)) + (((-2 : ℂ) * r ^ 3 + (2 : ℂ) * r ^ 5) / ((2 - μ))) * (((-2 : ℂ) * s) / ((r ^ 2 - 1))) := by
  field_simp
  ring

private theorem rec_L_qt2 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (((1 / 2 : ℂ) * r) / ((r ^ 2 - 1))) * (((-2 : ℂ) * r + (4 : ℂ) * r ^ 3 + (-2 : ℂ) * r ^ 5) / ((2 - μ) * s)) + ((-1 / 2 : ℂ) * r ^ 2) * (((-6 : ℂ) + (1 : ℂ) * μ + (30 : ℂ) * r ^ 2 + (-1 : ℂ) * r ^ 2 * μ + (-24 : ℂ) * r ^ 4) / ((2 - μ) * s)) + ((-1 / 2 : ℂ) * r + (3 / 2 : ℂ) * r ^ 3 + (-1 : ℂ) * r ^ 5) * (((-2 : ℂ) * r) / ((2 - μ) * s)) + ((-1 : ℂ) * r ^ 2 + (1 : ℂ) * r ^ 4) * (((1 : ℂ) + (-1 : ℂ) * r ^ 2) / ((2 - μ) * s)) = (((-2 : ℂ) * r ^ 2 + (15 / 2 : ℂ) * r ^ 4 + (-11 / 2 : ℂ) * r ^ 6) / ((2 - μ))) * (((-2 : ℂ)) / (s)) + (((-1 / 2 : ℂ) * r ^ 3 + (1 : ℂ) * r ^ 5 + (-1 / 2 : ℂ) * r ^ 7) / ((2 - μ))) * (((-4 : ℂ) * r) / ((r ^ 2 - 1) * s)) + (((-1 / 2 : ℂ) * r ^ 4 + (1 / 2 : ℂ) * r ^ 6) / ((2 - μ) * s)) * (((1 : ℂ) * μ) / (r ^ 2)) := by
  field_simp
  ring

private theorem rec_L_qt3 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    ((-1 / 2 : ℂ) * r ^ 2) * (((-2 : ℂ) * r + (4 : ℂ) * r ^ 3 + (-2 : ℂ) * r ^ 5) / ((2 - μ) * s)) = (((-1 / 2 : ℂ) * r ^ 3 + (1 : ℂ) * r ^ 5 + (-1 / 2 : ℂ) * r ^ 7) / ((2 - μ))) * (((-2 : ℂ)) / (s)) := by
  field_simp
  ring

private theorem rec_L_qr0 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (0 : ℂ) = (((-1 : ℂ) * r + (10 : ℂ) * r ^ 3 + (-12 : ℂ) * r ^ 5) / ((2 - μ))) * ((4 : ℂ)) + (((-4 : ℂ) * r ^ 3 + (6 : ℂ) * r ^ 5) / ((2 - μ))) * (((1 : ℂ) * μ) / (r ^ 2)) + (((-1 : ℂ) * r ^ 4 + (1 : ℂ) * r ^ 6) / ((2 - μ))) * (((-2 : ℂ) * μ) / (r ^ 3)) + (((-4 : ℂ) * r ^ 2 + (-1 : ℂ) * r ^ 2 * μ + (10 : ℂ) * r ^ 4) / ((2 - μ))) * (((-2 : ℂ) + (4 : ℂ) * r ^ 2) / (r)) + (((-2 : ℂ) * r ^ 3 + (2 : ℂ) * r ^ 5) / ((2 - μ))) * (((2 : ℂ) + (4 : ℂ) * r ^ 2) / (r ^ 2)) := by
  field_simp
  ring

private theorem rec_L_qr1 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (0 : ℂ) = (((-2 : ℂ) * r ^ 2 + (15 / 2 : ℂ) * r ^ 4 + (-11 / 2 : ℂ) * r ^ 6) / ((2 - μ))) * ((4 : ℂ)) + (((-1 : ℂ) * r ^ 4 + (1 : ℂ) * r ^ 6) / ((2 - μ))) * (((1 : ℂ) * μ) / (r ^ 2)) + (((-4 : ℂ) * r ^ 2 + (-1 : ℂ) * r ^ 2 * μ + (10 : ℂ) * r ^ 4) / ((2 - μ))) * ((-1 : ℂ) + (1 : ℂ) * r ^ 2) + (((-2 : ℂ) * r ^ 3 + (2 : ℂ) * r ^ 5) / ((2 - μ))) * (((-2 : ℂ) + (6 : ℂ) * r ^ 2) / (r)) := by
  field_simp
  ring

private theorem rec_L_qr2 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (0 : ℂ) = (((-1 / 2 : ℂ) * r ^ 3 + (1 : ℂ) * r ^ 5 + (-1 / 2 : ℂ) * r ^ 7) / ((2 - μ))) * ((4 : ℂ)) + (((-2 : ℂ) * r ^ 3 + (2 : ℂ) * r ^ 5) / ((2 - μ))) * ((-1 : ℂ) + (1 : ℂ) * r ^ 2) := by
  field_simp
  ring

private theorem rec_L_qT0 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (((1 / 4 : ℂ) * μ + (-2 : ℂ) * r ^ 2 + (-1 / 4 : ℂ) * r ^ 2 * μ + (1 : ℂ) * r ^ 4) / ((r ^ 2 - 1) ^ 2)) * (((6 : ℂ) + (-3 : ℂ) * μ + (-10 : ℂ) * r ^ 2 + (3 : ℂ) * r ^ 2 * μ + (4 : ℂ) * r ^ 4) / ((2 - μ))) + (((1 / 2 : ℂ) * r) / ((r ^ 2 - 1))) * (((-20 : ℂ) * r + (6 : ℂ) * r * μ + (16 : ℂ) * r ^ 3) / ((2 - μ))) + ((-1 / 2 : ℂ) * r ^ 2) * (((-20 : ℂ) + (6 : ℂ) * μ + (48 : ℂ) * r ^ 2) / ((2 - μ))) + (((-2 : ℂ) * s * r + (4 : ℂ) * s * r ^ 3) / ((r ^ 2 - 1))) * (((-8 : ℂ) * s * r + (4 : ℂ) * s * r ^ 3) / ((r ^ 2 - 1) * (2 - μ))) + ((2 : ℂ) * s * r ^ 2) * (((8 : ℂ) * s + (-4 : ℂ) * s * r ^ 2 + (4 : ℂ) * s * r ^ 4) / ((r ^ 2 - 1) ^ 2 * (2 - μ))) + ((-1 / 4 : ℂ) * μ + (4 : ℂ) * r ^ 2 + (1 / 4 : ℂ) * r ^ 2 * μ + (-5 : ℂ) * r ^ 4 + (-2 : ℂ) * s ^ 2 * r ^ 2) * (((-2 : ℂ) + (1 : ℂ) * μ + (4 : ℂ) * r ^ 2) / ((r ^ 2 - 1) * (2 - μ))) + ((-1 / 2 : ℂ) * r + (3 / 2 : ℂ) * r ^ 3 + (-1 : ℂ) * r ^ 5) * (((-4 : ℂ) * r + (-2 : ℂ) * r * μ) / ((r ^ 2 - 1) ^ 2 * (2 - μ))) + (((-4 : ℂ) * s ^ 2 * r ^ 2) / ((r ^ 2 - 1))) * (((-1 : ℂ) + (-1 / 2 : ℂ) * μ + (1 : ℂ) * r ^ 2) / ((2 - μ))) + ((-2 : ℂ) * r + (4 : ℂ) * r ^ 3) * (((2 : ℂ) * r) / ((2 - μ))) + ((-1 : ℂ) * r ^ 2 + (1 : ℂ) * r ^ 4) * (((2 : ℂ)) / ((2 - μ))) = (((-1 : ℂ) * r + (10 : ℂ) * r ^ 3 + (-12 : ℂ) * r ^ 5) / ((2 - μ))) * (((4 : ℂ) + (-4 : ℂ) * μ + (-8 : ℂ) * r ^ 2 + (4 : ℂ) * r ^ 2 * μ + (4 : ℂ) * r ^ 4 + (-8 : ℂ) * s ^ 2 * r ^ 2) / (r * (r ^ 2 - 1) ^ 2)) + (((-2 : ℂ) * r ^ 2 + (15 / 2 : ℂ) * r ^ 4 + (-11 / 2 : ℂ) * r ^ 6) / ((2 - μ))) * (((4 : ℂ) + (-4 : ℂ) * μ + (-12 : ℂ) * r ^ 2 + (16 : ℂ) * r ^ 2 * μ + (12 : ℂ) * r ^ 4 + (-12 : ℂ) * r ^ 4 * μ + (-4 : ℂ) * r ^ 6 + (8 : ℂ) * s ^ 2 * r ^ 2 + (24 : ℂ) * s ^ 2 * r ^ 4) / (r ^ 2 * (r ^ 2 - 1) ^ 3)) + (((-1 / 2 : ℂ) * r ^ 3 + (1 : ℂ) * r ^ 5 + (-1 / 2 : ℂ) * r ^ 7) / ((2 - μ))) * (((8 : ℂ) + (-8 : ℂ) * μ + (-32 : ℂ) * r ^ 2 + (32 : ℂ) * r ^ 2 * μ + (48 : ℂ) * r ^ 4 + (-72 : ℂ) * r ^ 4 * μ + (-32 : ℂ) * r ^ 6 + (48 : ℂ) * r ^ 6 * μ + (8 : ℂ) * r ^ 8 + (-96 : ℂ) * s ^ 2 * r ^ 4 + (-96 : ℂ) * s ^ 2 * r ^ 6) / (r ^ 3 * (r ^ 2 - 1) ^ 4)) + (((-4 : ℂ) * r ^ 2 + (-1 : ℂ) * r ^ 2 * μ + (10 : ℂ) * r ^ 4) / ((2 - μ))) * (((-1 : ℂ) + (1 / 2 : ℂ) * μ) / (r ^ 2)) + (((-2 : ℂ) * r ^ 3 + (2 : ℂ) * r ^ 5) / ((2 - μ))) * (((2 : ℂ) + (-1 : ℂ) * μ) / (r ^ 3)) := by
  field_simp
  ring

private theorem rec_L_qT1 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (((1 / 4 : ℂ) * μ + (-2 : ℂ) * r ^ 2 + (-1 / 4 : ℂ) * r ^ 2 * μ + (1 : ℂ) * r ^ 4) / ((r ^ 2 - 1) ^ 2)) * (((6 : ℂ) * r + (-14 : ℂ) * r ^ 3 + (8 : ℂ) * r ^ 5) / ((2 - μ))) + (((1 / 2 : ℂ) * r) / ((r ^ 2 - 1))) * (((12 : ℂ) + (-3 : ℂ) * μ + (-52 : ℂ) * r ^ 2 + (3 : ℂ) * r ^ 2 * μ + (44 : ℂ) * r ^ 4) / ((2 - μ))) + ((-1 / 2 : ℂ) * r ^ 2) * (((-124 : ℂ) * r + (12 : ℂ) * r * μ + (192 : ℂ) * r ^ 3) / ((2 - μ))) + (((-2 : ℂ) * s * r + (4 : ℂ) * s * r ^ 3) / ((r ^ 2 - 1))) * (((4 : ℂ) * s * r ^ 2) / ((2 - μ))) + ((2 : ℂ) * s * r ^ 2) * (((-16 : ℂ) * s * r + (12 : ℂ) * s * r ^ 3) / ((r ^ 2 - 1) * (2 - μ))) + ((-1 / 4 : ℂ) * μ + (4 : ℂ) * r ^ 2 + (1 / 4 : ℂ) * r ^ 2 * μ + (-5 : ℂ) * r ^ 4 + (-2 : ℂ) * s ^ 2 * r ^ 2) * (((-6 : ℂ) * r + (8 : ℂ) * r ^ 3) / ((r ^ 2 - 1) * (2 - μ))) + ((-1 / 2 : ℂ) * r + (3 / 2 : ℂ) * r ^ 3 + (-1 : ℂ) * r ^ 5) * (((8 : ℂ) + (-1 : ℂ) * μ + (-24 : ℂ) * r ^ 2 + (1 : ℂ) * r ^ 2 * μ + (12 : ℂ) * r ^ 4) / ((r ^ 2 - 1) ^ 2 * (2 - μ))) + (((-4 : ℂ) * s ^ 2 * r ^ 2) / ((r ^ 2 - 1))) * (((-1 : ℂ) * r + (1 : ℂ) * r ^ 3) / ((2 - μ))) + ((-2 : ℂ) * r + (4 : ℂ) * r ^ 3) * (((-2 : ℂ) + (-1 / 2 : ℂ) * μ + (4 : ℂ) * r ^ 2) / ((2 - μ))) + ((-1 : ℂ) * r ^ 2 + (1 : ℂ) * r ^ 4) * (((10 : ℂ) * r) / ((2 - μ))) = (((-1 : ℂ) * r + (10 : ℂ) * r ^ 3 + (-12 : ℂ) * r ^ 5) / ((2 - μ))) * (((-4 : ℂ) + (8 : ℂ) * r ^ 2) / ((r ^ 2 - 1))) + (((-2 : ℂ) * r ^ 2 + (15 / 2 : ℂ) * r ^ 4 + (-11 / 2 : ℂ) * r ^ 6) / ((2 - μ))) * (((4 : ℂ) + (-4 : ℂ) * μ + (-16 : ℂ) * r ^ 2 + (4 : ℂ) * r ^ 2 * μ + (4 : ℂ) * r ^ 4 + (-8 : ℂ) * s ^ 2 * r ^ 2) / (r * (r ^ 2 - 1) ^ 2)) + (((-1 / 2 : ℂ) * r ^ 3 + (1 : ℂ) * r ^ 5 + (-1 / 2 : ℂ) * r ^ 7) / ((2 - μ))) * (((8 : ℂ) + (-8 : ℂ) * μ + (-16 : ℂ) * r ^ 2 + (32 : ℂ) * r ^ 2 * μ + (48 : ℂ) * r ^ 4 + (-24 : ℂ) * r ^ 4 * μ + (-8 : ℂ) * r ^ 6 + (16 : ℂ) * s ^ 2 * r ^ 2 + (48 : ℂ) * s ^ 2 * r ^ 4) / (r ^ 2 * (r ^ 2 - 1) ^ 3)) + (((-2 : ℂ) * r ^ 3 + (2 : ℂ) * r ^ 5) / ((2 - μ))) * (((-1 : ℂ) + (1 / 2 : ℂ) * μ) / (r ^ 2)) := by
  field_simp
  ring

private theorem rec_L_qT2 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (((1 / 4 : ℂ) * μ + (-2 : ℂ) * r ^ 2 + (-1 / 4 : ℂ) * r ^ 2 * μ + (1 : ℂ) * r ^ 4) / ((r ^ 2 - 1) ^ 2)) * (((2 : ℂ) * r ^ 2 + (-4 : ℂ) * r ^ 4 + (2 : ℂ) * r ^ 6) / ((2 - μ))) + (((1 / 2 : ℂ) * r) / ((r ^ 2 - 1))) * (((10 : ℂ) * r + (-30 : ℂ) * r ^ 3 + (20 : ℂ) * r ^ 5) / ((2 - μ))) + ((-1 / 2 : ℂ) * r ^ 2) * (((22 : ℂ) + (-3 : ℂ) * μ + (-142 : ℂ) * r ^ 2 + (3 : ℂ) * r ^ 2 * μ + (144 : ℂ) * r ^ 4) / ((2 - μ))) + ((2 : ℂ) * s * r ^ 2) * (((4 : ℂ) * s * r ^ 2) / ((2 - μ))) + ((-1 / 4 : ℂ) * μ + (4 : ℂ) * r ^ 2 + (1 / 4 : ℂ) * r ^ 2 * μ + (-5 : ℂ) * r ^ 4 + (-2 : ℂ) * s ^ 2 * r ^ 2) * (((2 : ℂ) * r ^ 2) / ((2 - μ))) + ((-1 / 2 : ℂ) * r + (3 / 2 : ℂ) * r ^ 3 + (-1 : ℂ) * r ^ 5) * (((-10 : ℂ) * r + (12 : ℂ) * r ^ 3) / ((r ^ 2 - 1) * (2 - μ))) + ((-2 : ℂ) * r + (4 : ℂ) * r ^ 3) * (((-1 : ℂ) * r + (1 : ℂ) * r ^ 3) / ((2 - μ))) + ((-1 : ℂ) * r ^ 2 + (1 : ℂ) * r ^ 4) * (((-3 : ℂ) + (-1 / 2 : ℂ) * μ + (7 : ℂ) * r ^ 2) / ((2 - μ))) = (((-1 : ℂ) * r + (10 : ℂ) * r ^ 3 + (-12 : ℂ) * r ^ 5) / ((2 - μ))) * ((2 : ℂ) * r) + (((-2 : ℂ) * r ^ 2 + (15 / 2 : ℂ) * r ^ 4 + (-11 / 2 : ℂ) * r ^ 6) / ((2 - μ))) * (((-6 : ℂ) + (10 : ℂ) * r ^ 2) / ((r ^ 2 - 1))) + (((-1 / 2 : ℂ) * r ^ 3 + (1 : ℂ) * r ^ 5 + (-1 / 2 : ℂ) * r ^ 7) / ((2 - μ))) * (((4 : ℂ) + (-4 : ℂ) * μ + (-24 : ℂ) * r ^ 2 + (4 : ℂ) * r ^ 2 * μ + (4 : ℂ) * r ^ 4 + (-8 : ℂ) * s ^ 2 * r ^ 2) / (r * (r ^ 2 - 1) ^ 2)) := by
  field_simp
  ring

private theorem rec_L_qT3 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (((1 / 2 : ℂ) * r) / ((r ^ 2 - 1))) * (((2 : ℂ) * r ^ 2 + (-4 : ℂ) * r ^ 4 + (2 : ℂ) * r ^ 6) / ((2 - μ))) + ((-1 / 2 : ℂ) * r ^ 2) * (((14 : ℂ) * r + (-46 : ℂ) * r ^ 3 + (32 : ℂ) * r ^ 5) / ((2 - μ))) + ((-1 / 2 : ℂ) * r + (3 / 2 : ℂ) * r ^ 3 + (-1 : ℂ) * r ^ 5) * (((2 : ℂ) * r ^ 2) / ((2 - μ))) + ((-1 : ℂ) * r ^ 2 + (1 : ℂ) * r ^ 4) * (((-1 : ℂ) * r + (1 : ℂ) * r ^ 3) / ((2 - μ))) = (((-2 : ℂ) * r ^ 2 + (15 / 2 : ℂ) * r ^ 4 + (-11 / 2 : ℂ) * r ^ 6) / ((2 - μ))) * ((2 : ℂ) * r) + (((-1 / 2 : ℂ) * r ^ 3 + (1 : ℂ) * r ^ 5 + (-1 / 2 : ℂ) * r ^ 7) / ((2 - μ))) * (((-8 : ℂ) + (12 : ℂ) * r ^ 2) / ((r ^ 2 - 1))) := by
  field_simp
  ring

private theorem rec_L_qT4 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    ((-1 / 2 : ℂ) * r ^ 2) * (((2 : ℂ) * r ^ 2 + (-4 : ℂ) * r ^ 4 + (2 : ℂ) * r ^ 6) / ((2 - μ))) = (((-1 / 2 : ℂ) * r ^ 3 + (1 : ℂ) * r ^ 5 + (-1 / 2 : ℂ) * r ^ 7) / ((2 - μ))) * ((2 : ℂ) * r) := by
  field_simp
  ring

private theorem rec_L_qL0 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (1 : ℂ) = (((-4 : ℂ) * r ^ 3 + (6 : ℂ) * r ^ 5) / ((2 - μ))) * (((-2 : ℂ)) / (r ^ 3)) + (((-1 : ℂ) * r ^ 4 + (1 : ℂ) * r ^ 6) / ((2 - μ))) * (((6 : ℂ)) / (r ^ 4)) + (((-4 : ℂ) * r ^ 2 + (-1 : ℂ) * r ^ 2 * μ + (10 : ℂ) * r ^ 4) / ((2 - μ))) * (((1 : ℂ)) / (r ^ 2)) + (((-2 : ℂ) * r ^ 3 + (2 : ℂ) * r ^ 5) / ((2 - μ))) * (((-2 : ℂ)) / (r ^ 3)) := by
  field_simp
  ring

private theorem rec_L_qL1 (s r μ : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    (0 : ℂ) = (((-1 : ℂ) * r ^ 4 + (1 : ℂ) * r ^ 6) / ((2 - μ))) * (((-2 : ℂ)) / (r ^ 3)) + (((-2 : ℂ) * r ^ 3 + (2 : ℂ) * r ^ 5) / ((2 - μ))) * (((1 : ℂ)) / (r ^ 2)) := by
  field_simp
  ring

/-- The reconstructed jet solves the sourced harmonic `L` equation up to the master defect and the Bianchi forms of the source. -/
theorem reconstruction_L (s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4 : ℂ) (hs : s ≠ 0) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    harmonicL s r μ (recF0 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4) (recF01 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4) (recF02 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4) (recF1 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4) (recF11 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4) (recF12 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4) (recF2 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4) (recF21 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4) (recF22 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4) (recH s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4) (recH1 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4) (recH2 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4) + qL0 = (((-1 : ℂ) * r + (10 : ℂ) * r ^ 3 + (-12 : ℂ) * r ^ 5) / ((2 - μ))) * masterDefect0 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4 + (((-2 : ℂ) * r ^ 2 + (15 / 2 : ℂ) * r ^ 4 + (-11 / 2 : ℂ) * r ^ 6) / ((2 - μ))) * masterDefect1 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4 + (((-1 / 2 : ℂ) * r ^ 3 + (1 : ℂ) * r ^ 5 + (-1 / 2 : ℂ) * r ^ 7) / ((2 - μ))) * masterDefect2 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4 + (((-3 : ℂ) * r ^ 2 + (10 : ℂ) * r ^ 4) / ((2 - μ) * s)) * bianchiT0 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4 + (((-3 : ℂ) * r ^ 3 + (5 : ℂ) * r ^ 5) / ((2 - μ) * s)) * bianchiT1 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4 + (((-1 / 2 : ℂ) * r ^ 4 + (1 / 2 : ℂ) * r ^ 6) / ((2 - μ) * s)) * bianchiT2 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4 + (((-4 : ℂ) * r ^ 3 + (6 : ℂ) * r ^ 5) / ((2 - μ))) * bianchiR0 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4 + (((-1 : ℂ) * r ^ 4 + (1 : ℂ) * r ^ 6) / ((2 - μ))) * bianchiR1 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4 + (((-4 : ℂ) * r ^ 2 + (-1 : ℂ) * r ^ 2 * μ + (10 : ℂ) * r ^ 4) / ((2 - μ))) * bianchiAng0 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4 + (((-2 : ℂ) * r ^ 3 + (2 : ℂ) * r ^ 5) / ((2 - μ))) * bianchiAng1 s r μ P P1 P2 P3 P4 qtt0 qtt1 qtt2 qtt3 qtt4 qtr0 qtr1 qtr2 qtr3 qtr4 qtr5 qrr0 qrr1 qrr2 qrr3 qrr4 qrr5 qt0 qt1 qt2 qt3 qt4 qr0 qr1 qr2 qr3 qr4 qr5 qT0 qT1 qT2 qT3 qT4 qL0 qL1 qL2 qL3 qL4 := by
  unfold harmonicL recF0 recF01 recF02 recF1 recF11 recF2 recF21 recH recH1 recH2 masterDefect0 masterDefect1 masterDefect2 bianchiT0 bianchiT1 bianchiT2 bianchiR0 bianchiR1 bianchiAng0 bianchiAng1
  linear_combination P * rec_L_P s r μ hs hr hf hμ + P1 * rec_L_P1 s r μ hs hr hf hμ + P2 * rec_L_P2 s r μ hs hr hf hμ + P3 * rec_L_P3 s r μ hs hr hf hμ + P4 * rec_L_P4 s r μ hs hr hf hμ + qtt0 * rec_L_qtt0 s r μ hs hr hf hμ + qtt1 * rec_L_qtt1 s r μ hs hr hf hμ + qtt2 * rec_L_qtt2 s r μ hs hr hf hμ + qtr0 * rec_L_qtr0 s r μ hs hr hf hμ + qtr1 * rec_L_qtr1 s r μ hs hr hf hμ + qtr2 * rec_L_qtr2 s r μ hs hr hf hμ + qtr3 * rec_L_qtr3 s r μ hs hr hf hμ + qrr0 * rec_L_qrr0 s r μ hs hr hf hμ + qrr1 * rec_L_qrr1 s r μ hs hr hf hμ + qrr2 * rec_L_qrr2 s r μ hs hr hf hμ + qt0 * rec_L_qt0 s r μ hs hr hf hμ + qt1 * rec_L_qt1 s r μ hs hr hf hμ + qt2 * rec_L_qt2 s r μ hs hr hf hμ + qt3 * rec_L_qt3 s r μ hs hr hf hμ + qr0 * rec_L_qr0 s r μ hs hr hf hμ + qr1 * rec_L_qr1 s r μ hs hr hf hμ + qr2 * rec_L_qr2 s r μ hs hr hf hμ + qT0 * rec_L_qT0 s r μ hs hr hf hμ + qT1 * rec_L_qT1 s r μ hs hr hf hμ + qT2 * rec_L_qT2 s r μ hs hr hf hμ + qT3 * rec_L_qT3 s r μ hs hr hf hμ + qT4 * rec_L_qT4 s r μ hs hr hf hμ + qL0 * rec_L_qL0 s r μ hs hr hf hμ + qL1 * rec_L_qL1 s r μ hs hr hf hμ

end
end RHTower.D4BMScalarStream
