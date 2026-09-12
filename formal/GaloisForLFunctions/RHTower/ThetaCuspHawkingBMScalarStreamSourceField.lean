import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMScalarStreamSourceHarmonic
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMScalarStreamReconstructionField

/-!
# The scalar–scalar harmonic source as radial functions

The seven harmonic source coefficients are realised as rational-coefficient radial functions
`srcTT, …, srcL` (Horner form over `r^p (r²−1)^q`), smooth on the exterior, with their twisted
derivatives computed explicitly where the Bianchi identities and the master source need them. The
main theorem `ssSourcedMasterData` shows that any smooth undressed master function `y` solving the
sourced master equation `twist²y + (2r/(r²−1))twist y + (μ/(r²(r²−1)) − 4s²/(r²−1)²)y + ssMasterSource = 0`
on the exterior provides the data of the field-level reconstruction, so that the seven sourced
harmonic Einstein equations hold for the reconstructed radial functions (`ssSourced_equation_TT`, …).
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace RHTower.D4BMScalarStream
open GaloisForLFunctions.HTGeometry CoordinateMetricTwoJet GaloisForLFunctions.HTGeometry.TwistedRadial
open Filter Topology Set
open scoped ContDiff
noncomputable section

/-- Harmonic `tt` source coefficient as a radial function. -/
def srcTT (s μ : ℂ) : ℝ → ℂ :=
  ratCoef [((9 / 8 : ℂ) * s ^ 2 + (-3 / 32 : ℂ) * s ^ 2 * μ + (57 / 16 : ℂ) * s ^ 3 + (-3 / 16 : ℂ) * s ^ 3 * μ + (33 / 8 : ℂ) * s ^ 4 + (-3 / 32 : ℂ) * s ^ 4 * μ + (33 / 16 : ℂ) * s ^ 5 + (3 / 8 : ℂ) * s ^ 6), (0 : ℂ), ((-1 / 2 : ℂ) * s + (-1 / 4 : ℂ) * s * μ + (-31 / 8 : ℂ) * s ^ 2 + (-1 / 32 : ℂ) * s ^ 2 * μ + (-113 / 16 : ℂ) * s ^ 3 + (3 / 16 : ℂ) * s ^ 3 * μ + (-17 / 4 : ℂ) * s ^ 4 + (3 / 32 : ℂ) * s ^ 4 * μ + (-25 / 16 : ℂ) * s ^ 5), (0 : ℂ), ((-1 / 4 : ℂ) * μ + (-1 : ℂ) * s + (1 / 4 : ℂ) * s * μ + (5 : ℂ) * s ^ 2 + (1 / 8 : ℂ) * s ^ 2 * μ + (1 / 4 : ℂ) * s ^ 3 + (1 / 2 : ℂ) * s ^ 4), (0 : ℂ), ((1 / 4 : ℂ) * μ + (3 / 2 : ℂ) * s + (-1 / 4 : ℂ) * s ^ 2)] 6 0

/-- Harmonic `tr` source coefficient as a radial function. -/
def srcTR (s μ : ℂ) : ℝ → ℂ :=
  ratCoef [((3 / 4 : ℂ) * s ^ 3 + (15 / 8 : ℂ) * s ^ 4 + (3 / 2 : ℂ) * s ^ 5 + (3 / 8 : ℂ) * s ^ 6), (0 : ℂ), ((-1 : ℂ) * s ^ 2 + (-7 / 2 : ℂ) * s ^ 3 + (-3 / 2 : ℂ) * s ^ 4 + (-1 : ℂ) * s ^ 5), (0 : ℂ), ((3 : ℂ) * s ^ 2 + (-1 / 2 : ℂ) * s ^ 3)] 5 1

/-- Harmonic `rr` source coefficient as a radial function. -/
def srcRR (s μ : ℂ) : ℝ → ℂ :=
  ratCoef [((7 / 8 : ℂ) * s ^ 2 + (3 / 32 : ℂ) * s ^ 2 * μ + (35 / 16 : ℂ) * s ^ 3 + (3 / 16 : ℂ) * s ^ 3 * μ + (7 / 4 : ℂ) * s ^ 4 + (3 / 32 : ℂ) * s ^ 4 * μ + (7 / 16 : ℂ) * s ^ 5), (0 : ℂ), ((1 / 2 : ℂ) * s + (1 / 4 : ℂ) * s * μ + (-21 / 8 : ℂ) * s ^ 2 + (1 / 32 : ℂ) * s ^ 2 * μ + (-83 / 16 : ℂ) * s ^ 3 + (-3 / 16 : ℂ) * s ^ 3 * μ + (-27 / 8 : ℂ) * s ^ 4 + (-3 / 32 : ℂ) * s ^ 4 * μ + (1 / 16 : ℂ) * s ^ 5 + (3 / 8 : ℂ) * s ^ 6), (0 : ℂ), ((1 / 4 : ℂ) * μ + (1 : ℂ) * s + (-1 / 4 : ℂ) * s * μ + (2 : ℂ) * s ^ 2 + (-1 / 8 : ℂ) * s ^ 2 * μ + (-1 / 4 : ℂ) * s ^ 3 + (2 : ℂ) * s ^ 4), (0 : ℂ), ((-1 / 4 : ℂ) * μ + (-3 / 2 : ℂ) * s + (7 / 4 : ℂ) * s ^ 2)] 6 2

/-- Harmonic `t` source coefficient as a radial function. -/
def srcT (s μ : ℂ) : ℝ → ℂ :=
  ratCoef [((3 / 16 : ℂ) * s ^ 3 + (3 / 8 : ℂ) * s ^ 4 + (3 / 16 : ℂ) * s ^ 5), (0 : ℂ), ((1 / 2 : ℂ) * s ^ 2 + (1 / 4 : ℂ) * s ^ 3), (0 : ℂ), ((1 / 2 : ℂ) * s)] 4 0

/-- Harmonic `r` source coefficient as a radial function. -/
def srcR (s μ : ℂ) : ℝ → ℂ :=
  ratCoef [((1 / 2 : ℂ) * s ^ 2 + (19 / 16 : ℂ) * s ^ 3 + (7 / 8 : ℂ) * s ^ 4 + (3 / 16 : ℂ) * s ^ 5), (0 : ℂ), ((1 / 2 : ℂ) * s + (-1 / 4 : ℂ) * s ^ 2 + (-3 / 4 : ℂ) * s ^ 3 + (-1 / 2 : ℂ) * s ^ 4), (0 : ℂ), ((1 / 4 : ℂ) * s ^ 2)] 5 1

/-- Harmonic `T` source coefficient as a radial function. -/
def srcTF (s μ : ℂ) : ℝ → ℂ :=
  ratCoef [(((1 / 2 : ℂ) * s ^ 2 + (-1 / 8 : ℂ) * s ^ 2 * μ + (11 / 8 : ℂ) * s ^ 3 + (-1 / 4 : ℂ) * s ^ 3 * μ + (11 / 8 : ℂ) * s ^ 4 + (-1 / 8 : ℂ) * s ^ 4 * μ + (5 / 8 : ℂ) * s ^ 5 + (1 / 8 : ℂ) * s ^ 6) / ((2 - μ))), (0 : ℂ), (((-2 : ℂ) * s ^ 2 + (1 / 2 : ℂ) * s ^ 2 * μ + (-3 / 2 : ℂ) * s ^ 3 + (-1 / 2 : ℂ) * s ^ 4) / ((2 - μ)))] 4 0

/-- Harmonic `L` source coefficient as a radial function. -/
def srcL (s μ : ℂ) : ℝ → ℂ :=
  ratCoef [((7 / 4 : ℂ) * s ^ 2 + (-1 / 16 : ℂ) * s ^ 2 * μ + (21 / 4 : ℂ) * s ^ 3 + (-1 / 8 : ℂ) * s ^ 3 * μ + (91 / 16 : ℂ) * s ^ 4 + (-1 / 16 : ℂ) * s ^ 4 * μ + (21 / 8 : ℂ) * s ^ 5 + (7 / 16 : ℂ) * s ^ 6), (0 : ℂ), ((1 / 2 : ℂ) * s + (-1 / 4 : ℂ) * s ^ 2 + (1 / 4 : ℂ) * s ^ 2 * μ + (-1 : ℂ) * s ^ 3 + (-1 / 4 : ℂ) * s ^ 4), (0 : ℂ), ((3 / 4 : ℂ) * s ^ 2)] 4 0

/-- Twisted derivative of `srcTR` as a radial function. -/
def srcTR1 (s μ : ℂ) : ℝ → ℂ :=
  ratCoef [((15 / 4 : ℂ) * s ^ 3 + (87 / 8 : ℂ) * s ^ 4 + (45 / 4 : ℂ) * s ^ 5 + (39 / 8 : ℂ) * s ^ 6 + (3 / 4 : ℂ) * s ^ 7), (0 : ℂ), ((-3 : ℂ) * s ^ 2 + (-71 / 4 : ℂ) * s ^ 3 + (-197 / 8 : ℂ) * s ^ 4 + (-33 / 2 : ℂ) * s ^ 5 + (-37 / 8 : ℂ) * s ^ 6), (0 : ℂ), ((8 : ℂ) * s ^ 2 + (23 : ℂ) * s ^ 3 + (13 / 2 : ℂ) * s ^ 4 + (5 : ℂ) * s ^ 5), (0 : ℂ), ((-9 : ℂ) * s ^ 2 + (3 / 2 : ℂ) * s ^ 3)] 6 2

/-- Twisted derivative of `srcRR` as a radial function. -/
def srcRR1 (s μ : ℂ) : ℝ → ℂ :=
  ratCoef [((21 / 4 : ℂ) * s ^ 2 + (9 / 16 : ℂ) * s ^ 2 * μ + (119 / 8 : ℂ) * s ^ 3 + (21 / 16 : ℂ) * s ^ 3 * μ + (119 / 8 : ℂ) * s ^ 4 + (15 / 16 : ℂ) * s ^ 4 * μ + (49 / 8 : ℂ) * s ^ 5 + (3 / 16 : ℂ) * s ^ 5 * μ + (7 / 8 : ℂ) * s ^ 6), (0 : ℂ), ((2 : ℂ) * s + (1 : ℂ) * s * μ + (-73 / 4 : ℂ) * s ^ 2 + (-5 / 16 : ℂ) * s ^ 2 * μ + (-383 / 8 : ℂ) * s ^ 3 + (-41 / 16 : ℂ) * s ^ 3 * μ + (-331 / 8 : ℂ) * s ^ 4 + (-27 / 16 : ℂ) * s ^ 4 * μ + (-87 / 8 : ℂ) * s ^ 5 + (-3 / 16 : ℂ) * s ^ 5 * μ + (13 / 8 : ℂ) * s ^ 6 + (3 / 4 : ℂ) * s ^ 7), (0 : ℂ), ((1 / 2 : ℂ) * μ + (-2 : ℂ) * s + (-2 : ℂ) * s * μ + (27 : ℂ) * s ^ 2 + (-1 : ℂ) * s ^ 2 * μ + (45 : ℂ) * s ^ 3 + (5 / 4 : ℂ) * s ^ 3 * μ + (61 / 2 : ℂ) * s ^ 4 + (3 / 4 : ℂ) * s ^ 4 * μ + (7 / 2 : ℂ) * s ^ 5 + (-3 : ℂ) * s ^ 6), (0 : ℂ), ((-3 / 2 : ℂ) * μ + (-6 : ℂ) * s + (1 : ℂ) * s * μ + (-15 : ℂ) * s ^ 2 + (3 / 4 : ℂ) * s ^ 2 * μ + (5 : ℂ) * s ^ 3 + (-12 : ℂ) * s ^ 4), (0 : ℂ), ((1 : ℂ) * μ + (6 : ℂ) * s + (-7 : ℂ) * s ^ 2)] 7 3

/-- Twisted derivative of `srcR` as a radial function. -/
def srcR1 (s μ : ℂ) : ℝ → ℂ :=
  ratCoef [((5 / 2 : ℂ) * s ^ 2 + (111 / 16 : ℂ) * s ^ 3 + (27 / 4 : ℂ) * s ^ 4 + (43 / 16 : ℂ) * s ^ 5 + (3 / 8 : ℂ) * s ^ 6), (0 : ℂ), ((3 / 2 : ℂ) * s + (-13 / 4 : ℂ) * s ^ 2 + (-177 / 16 : ℂ) * s ^ 3 + (-73 / 8 : ℂ) * s ^ 4 + (-37 / 16 : ℂ) * s ^ 5), (0 : ℂ), ((-5 / 2 : ℂ) * s + (3 / 2 : ℂ) * s ^ 2 + (17 / 4 : ℂ) * s ^ 3 + (5 / 2 : ℂ) * s ^ 4), (0 : ℂ), ((-3 / 4 : ℂ) * s ^ 2)] 6 2

/-- Twisted derivative of `srcT` as a radial function. -/
def srcT1 (s μ : ℂ) : ℝ → ℂ :=
  ratCoef [((3 / 4 : ℂ) * s ^ 3 + (15 / 8 : ℂ) * s ^ 4 + (3 / 2 : ℂ) * s ^ 5 + (3 / 8 : ℂ) * s ^ 6), (0 : ℂ), ((1 : ℂ) * s ^ 2 + (3 / 4 : ℂ) * s ^ 3 + (-1 : ℂ) * s ^ 4 + (-3 / 4 : ℂ) * s ^ 5), (0 : ℂ), ((-1 / 2 : ℂ) * s ^ 3)] 5 1

/-- Twisted derivative of `srcTF` as a radial function. -/
def srcTF1 (s μ : ℂ) : ℝ → ℂ :=
  ratCoef [(((2 : ℂ) * s ^ 2 + (-1 / 2 : ℂ) * s ^ 2 * μ + (13 / 2 : ℂ) * s ^ 3 + (-5 / 4 : ℂ) * s ^ 3 * μ + (33 / 4 : ℂ) * s ^ 4 + (-1 : ℂ) * s ^ 4 * μ + (21 / 4 : ℂ) * s ^ 5 + (-1 / 4 : ℂ) * s ^ 5 * μ + (7 / 4 : ℂ) * s ^ 6 + (1 / 4 : ℂ) * s ^ 7) / ((2 - μ))), (0 : ℂ), (((-6 : ℂ) * s ^ 2 + (3 / 2 : ℂ) * s ^ 2 * μ + (-25 / 2 : ℂ) * s ^ 3 + (2 : ℂ) * s ^ 3 * μ + (-19 / 2 : ℂ) * s ^ 4 + (1 / 2 : ℂ) * s ^ 4 * μ + (-7 / 2 : ℂ) * s ^ 5 + (-1 / 2 : ℂ) * s ^ 6) / ((2 - μ))), (0 : ℂ), (((4 : ℂ) * s ^ 2 + (-1 : ℂ) * s ^ 2 * μ + (3 : ℂ) * s ^ 3 + (1 : ℂ) * s ^ 4) / ((2 - μ)))] 5 1

/-- Second twisted derivative of `srcTF`. -/
def srcTF2 (s μ : ℂ) : ℝ → ℂ :=
  ratCoef [(((10 : ℂ) * s ^ 2 + (-5 / 2 : ℂ) * s ^ 2 * μ + (73 / 2 : ℂ) * s ^ 3 + (-29 / 4 : ℂ) * s ^ 3 * μ + (217 / 4 : ℂ) * s ^ 4 + (-15 / 2 : ℂ) * s ^ 4 * μ + (171 / 4 : ℂ) * s ^ 5 + (-13 / 4 : ℂ) * s ^ 5 * μ + (77 / 4 : ℂ) * s ^ 6 + (-1 / 2 : ℂ) * s ^ 6 * μ + (19 / 4 : ℂ) * s ^ 7 + (1 / 2 : ℂ) * s ^ 8) / ((2 - μ))), (0 : ℂ), (((-32 : ℂ) * s ^ 2 + (8 : ℂ) * s ^ 2 * μ + (-95 : ℂ) * s ^ 3 + (71 / 4 : ℂ) * s ^ 3 * μ + (-445 / 4 : ℂ) * s ^ 4 + (25 / 2 : ℂ) * s ^ 4 * μ + (-265 / 4 : ℂ) * s ^ 5 + (11 / 4 : ℂ) * s ^ 5 * μ + (-83 / 4 : ℂ) * s ^ 6 + (-11 / 4 : ℂ) * s ^ 7) / ((2 - μ))), (0 : ℂ), (((34 : ℂ) * s ^ 2 + (-17 / 2 : ℂ) * s ^ 2 * μ + (147 / 2 : ℂ) * s ^ 3 + (-12 : ℂ) * s ^ 3 * μ + (109 / 2 : ℂ) * s ^ 4 + (-5 / 2 : ℂ) * s ^ 4 * μ + (39 / 2 : ℂ) * s ^ 5 + (5 / 2 : ℂ) * s ^ 6) / ((2 - μ))), (0 : ℂ), (((-12 : ℂ) * s ^ 2 + (3 : ℂ) * s ^ 2 * μ + (-9 : ℂ) * s ^ 3 + (-3 : ℂ) * s ^ 4) / ((2 - μ)))] 6 2

theorem srcTT_eq (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) (hs : s ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) : srcTT s μ r = ssSourceTT s r μ := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  unfold srcTT ssSourceTT
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

theorem srcTR_eq (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) (hs : s ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) : srcTR s μ r = ssSourceTR s r μ := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  unfold srcTR ssSourceTR
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

theorem srcRR_eq (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) (hs : s ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) : srcRR s μ r = ssSourceRR s r μ := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  unfold srcRR ssSourceRR
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

theorem srcT_eq (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) (hs : s ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) : srcT s μ r = ssSourceT s r μ := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  unfold srcT ssSourceT
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

theorem srcR_eq (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) (hs : s ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) : srcR s μ r = ssSourceR s r μ := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  unfold srcR ssSourceR
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

theorem srcTF_eq (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) (hs : s ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) : srcTF s μ r = ssSourceTF s r μ := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  unfold srcTF ssSourceTF
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

theorem srcL_eq (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) (hs : s ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) : srcL s μ r = ssSourceL s r μ := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  unfold srcL ssSourceL
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

theorem srcTR1_eq (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) (hs : s ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) : srcTR1 s μ r = ssSourceTR1 s r μ := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  unfold srcTR1 ssSourceTR1
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

theorem srcRR1_eq (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) (hs : s ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) : srcRR1 s μ r = ssSourceRR1 s r μ := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  unfold srcRR1 ssSourceRR1
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

theorem srcR1_eq (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) (hs : s ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) : srcR1 s μ r = ssSourceR1 s r μ := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  unfold srcR1 ssSourceR1
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

theorem srcT1_eq (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) (hs : s ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) : srcT1 s μ r = ssSourceT1 s r μ := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  unfold srcT1 ssSourceT1
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

theorem srcTF1_eq (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) (hs : s ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) : srcTF1 s μ r = ssSourceTF1 s r μ := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  unfold srcTF1 ssSourceTF1
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

theorem srcTF2_eq (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) (hs : s ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) : srcTF2 s μ r = ssSourceTF2 s r μ := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  unfold srcTF2 ssSourceTF2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

theorem twist_srcTR (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) : twist s (srcTR s μ) r = srcTR1 s μ r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  unfold twist srcTR srcTR1
  rw [(hasDerivAt_ratCoef _ _ _ hr hf).deriv]
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

theorem twist_srcRR (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) : twist s (srcRR s μ) r = srcRR1 s μ r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  unfold twist srcRR srcRR1
  rw [(hasDerivAt_ratCoef _ _ _ hr hf).deriv]
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

theorem twist_srcR (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) : twist s (srcR s μ) r = srcR1 s μ r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  unfold twist srcR srcR1
  rw [(hasDerivAt_ratCoef _ _ _ hr hf).deriv]
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

theorem twist_srcT (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) : twist s (srcT s μ) r = srcT1 s μ r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  unfold twist srcT srcT1
  rw [(hasDerivAt_ratCoef _ _ _ hr hf).deriv]
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

theorem twist_srcTF (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) : twist s (srcTF s μ) r = srcTF1 s μ r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  unfold twist srcTF srcTF1
  rw [(hasDerivAt_ratCoef _ _ _ hr hf).deriv]
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

theorem twist_srcTF1 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) : twist s (srcTF1 s μ) r = srcTF2 s μ r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  unfold twist srcTF1 srcTF2
  rw [(hasDerivAt_ratCoef _ _ _ hr hf).deriv]
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

theorem twistIter_srcTF_two (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    twistIter s 2 (srcTF s μ) r = srcTF2 s μ r := by
  simp only [twistIter_succ, twistIter_zero]
  rw [twist_congr s (g := twist s (srcTF s μ)) (h := srcTF1 s μ) (by
    filter_upwards [exterior_eventually hr1] with r' hr' using twist_srcTF s μ hr')]
  exact twist_srcTF1 s μ hr1

theorem srcTT_contDiffOn (s μ : ℂ) : ContDiffOn ℝ ∞ (srcTT s μ) (Ioi 1) :=
  contDiffOn_ratCoef _ _ _

theorem srcTT_twistSmooth (s μ : ℂ) (n : ℕ) : TwistSmooth s (srcTT s μ) n :=
  fun r hr k _ => differentiableAt_twistIter s (srcTT_contDiffOn s μ) k hr

theorem srcTR_contDiffOn (s μ : ℂ) : ContDiffOn ℝ ∞ (srcTR s μ) (Ioi 1) :=
  contDiffOn_ratCoef _ _ _

theorem srcTR_twistSmooth (s μ : ℂ) (n : ℕ) : TwistSmooth s (srcTR s μ) n :=
  fun r hr k _ => differentiableAt_twistIter s (srcTR_contDiffOn s μ) k hr

theorem srcRR_contDiffOn (s μ : ℂ) : ContDiffOn ℝ ∞ (srcRR s μ) (Ioi 1) :=
  contDiffOn_ratCoef _ _ _

theorem srcRR_twistSmooth (s μ : ℂ) (n : ℕ) : TwistSmooth s (srcRR s μ) n :=
  fun r hr k _ => differentiableAt_twistIter s (srcRR_contDiffOn s μ) k hr

theorem srcT_contDiffOn (s μ : ℂ) : ContDiffOn ℝ ∞ (srcT s μ) (Ioi 1) :=
  contDiffOn_ratCoef _ _ _

theorem srcT_twistSmooth (s μ : ℂ) (n : ℕ) : TwistSmooth s (srcT s μ) n :=
  fun r hr k _ => differentiableAt_twistIter s (srcT_contDiffOn s μ) k hr

theorem srcR_contDiffOn (s μ : ℂ) : ContDiffOn ℝ ∞ (srcR s μ) (Ioi 1) :=
  contDiffOn_ratCoef _ _ _

theorem srcR_twistSmooth (s μ : ℂ) (n : ℕ) : TwistSmooth s (srcR s μ) n :=
  fun r hr k _ => differentiableAt_twistIter s (srcR_contDiffOn s μ) k hr

theorem srcTF_contDiffOn (s μ : ℂ) : ContDiffOn ℝ ∞ (srcTF s μ) (Ioi 1) :=
  contDiffOn_ratCoef _ _ _

theorem srcTF_twistSmooth (s μ : ℂ) (n : ℕ) : TwistSmooth s (srcTF s μ) n :=
  fun r hr k _ => differentiableAt_twistIter s (srcTF_contDiffOn s μ) k hr

theorem srcL_contDiffOn (s μ : ℂ) : ContDiffOn ℝ ∞ (srcL s μ) (Ioi 1) :=
  contDiffOn_ratCoef _ _ _

theorem srcL_twistSmooth (s μ : ℂ) (n : ℕ) : TwistSmooth s (srcL s μ) n :=
  fun r hr k _ => differentiableAt_twistIter s (srcL_contDiffOn s μ) k hr

/-- The undressed sourced master equation for the scalar–scalar source. -/
def SSMasterEquation (s μ : ℂ) (y : ℝ → ℂ) : Prop :=
  ∀ r : ℝ, 1 < r → twist s (twist s y) r + 2 * r / ((r : ℂ) ^ 2 - 1) * twist s y r +
    (μ / ((r : ℂ) ^ 2 * ((r : ℂ) ^ 2 - 1)) - 4 * s ^ 2 / ((r : ℂ) ^ 2 - 1) ^ 2) * y r + ssMasterSource s r μ = 0

theorem masterDefect0R_src (s μ : ℂ) (y : ℝ → ℂ) {r : ℝ} (hr1 : 1 < r) (hs : s ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    masterDefect0R s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ) r =
      twist s (twist s y) r + 2 * r / ((r : ℂ) ^ 2 - 1) * twist s y r +
        (μ / ((r : ℂ) ^ 2 * ((r : ℂ) ^ 2 - 1)) - 4 * s ^ 2 / ((r : ℂ) ^ 2 - 1) ^ 2) * y r + ssMasterSource s r μ := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  rw [masterDefect0R_eq s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ) hr1 hs hμ]
  simp only [twistIter_succ, twistIter_zero]
  rw [twist_srcT s μ hr1, twist_srcTF s μ hr1, twist_congr s (g := twist s (srcTF s μ)) (h := srcTF1 s μ) (by
    filter_upwards [exterior_eventually hr1] with r' hr' using twist_srcTF s μ hr'), twist_srcTF1 s μ hr1]
  simp only [srcTT_eq s μ hr1 hs hμ, srcTR_eq s μ hr1 hs hμ, srcRR_eq s μ hr1 hs hμ, srcT_eq s μ hr1 hs hμ, srcR_eq s μ hr1 hs hμ, srcTF_eq s μ hr1 hs hμ, srcL_eq s μ hr1 hs hμ, srcT1_eq s μ hr1 hs hμ, srcTF1_eq s μ hr1 hs hμ, srcTF2_eq s μ hr1 hs hμ]
  unfold masterDefect0 ssSourceTT ssSourceTR ssSourceRR ssSourceT ssSourceR ssSourceTF ssSourceT1 ssSourceTF1 ssSourceTF2 ssMasterSource
  field_simp
  ring

theorem src_bianchiT (s μ : ℂ) (y : ℝ → ℂ) {r : ℝ} (hr1 : 1 < r) (hs : s ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    bianchiT0R s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ) r = 0 := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  rw [bianchiT0R_eq s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ) hr1 hs hμ]
  simp only [twistIter_succ, twistIter_zero]
  rw [twist_srcTR s μ hr1]
  simp only [srcTT_eq s μ hr1 hs hμ, srcTR_eq s μ hr1 hs hμ, srcRR_eq s μ hr1 hs hμ, srcT_eq s μ hr1 hs hμ, srcR_eq s μ hr1 hs hμ, srcTF_eq s μ hr1 hs hμ, srcL_eq s μ hr1 hs hμ, srcTR1_eq s μ hr1 hs hμ, srcRR1_eq s μ hr1 hs hμ, srcR1_eq s μ hr1 hs hμ]
  unfold bianchiT0 ssSourceTT ssSourceTR ssSourceTR1 ssSourceT
  field_simp
  ring

theorem src_bianchiR (s μ : ℂ) (y : ℝ → ℂ) {r : ℝ} (hr1 : 1 < r) (hs : s ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    bianchiR0R s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ) r = 0 := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  rw [bianchiR0R_eq s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ) hr1 hs hμ]
  simp only [twistIter_succ, twistIter_zero]
  rw [twist_srcRR s μ hr1]
  simp only [srcTT_eq s μ hr1 hs hμ, srcTR_eq s μ hr1 hs hμ, srcRR_eq s μ hr1 hs hμ, srcT_eq s μ hr1 hs hμ, srcR_eq s μ hr1 hs hμ, srcTF_eq s μ hr1 hs hμ, srcL_eq s μ hr1 hs hμ, srcTR1_eq s μ hr1 hs hμ, srcRR1_eq s μ hr1 hs hμ, srcR1_eq s μ hr1 hs hμ]
  unfold bianchiR0 ssSourceTT ssSourceTR ssSourceRR ssSourceRR1 ssSourceR ssSourceL
  field_simp
  ring

theorem src_bianchiAng (s μ : ℂ) (y : ℝ → ℂ) {r : ℝ} (hr1 : 1 < r) (hs : s ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    bianchiAng0R s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ) r = 0 := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  rw [bianchiAng0R_eq s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ) hr1 hs hμ]
  simp only [twistIter_succ, twistIter_zero]
  rw [twist_srcR s μ hr1]
  simp only [srcTT_eq s μ hr1 hs hμ, srcTR_eq s μ hr1 hs hμ, srcRR_eq s μ hr1 hs hμ, srcT_eq s μ hr1 hs hμ, srcR_eq s μ hr1 hs hμ, srcTF_eq s μ hr1 hs hμ, srcL_eq s μ hr1 hs hμ, srcTR1_eq s μ hr1 hs hμ, srcRR1_eq s μ hr1 hs hμ, srcR1_eq s μ hr1 hs hμ]
  unfold bianchiAng0 ssSourceT ssSourceR ssSourceR1 ssSourceTF ssSourceL
  field_simp
  ring

/-- A smooth solution of the undressed sourced master equation yields the field-level data. -/
theorem ssSourcedMasterData (s μ : ℂ) (hs : s ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (y : ℝ → ℂ)
    (hy : ContDiffOn ℝ ∞ y (Ioi 1)) (hODE : SSMasterEquation s μ y) :
    SourcedMasterData s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ) where
  smooth_y := fun r hr k _ => differentiableAt_twistIter s hy k hr
  smooth_tTT := srcTT_twistSmooth s μ 4
  smooth_tTR := srcTR_twistSmooth s μ 4
  smooth_tRR := srcRR_twistSmooth s μ 4
  smooth_tT := srcT_twistSmooth s μ 4
  smooth_tR := srcR_twistSmooth s μ 4
  smooth_tTF := srcTF_twistSmooth s μ 4
  smooth_tL := srcL_twistSmooth s μ 4
  master := fun r hr1 => by rw [masterDefect0R_src s μ y hr1 hs hμ]; exact hODE r hr1
  bianchiT := fun r hr1 => src_bianchiT s μ y hr1 hs hμ
  bianchiR := fun r hr1 => src_bianchiR s μ y hr1 hs hμ
  bianchiAng := fun r hr1 => src_bianchiAng s μ y hr1 hs hμ

/-- The sourced harmonic `tt` equation for the scalar–scalar source and any smooth solution of the master equation. -/
theorem ssSourced_equation_TT (s μ : ℂ) (hs : s ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (y : ℝ → ℂ)
    (hy : ContDiffOn ℝ ∞ y (Ioi 1)) (hODE : SSMasterEquation s μ y) {r : ℝ} (hr1 : 1 < r) :
    harmonicTT s r μ (recF0R s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ) r) (twist s (recF0R s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ)) r) (twist s (twist s (recF0R s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ))) r) (recF1R s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ) r) (twist s (recF1R s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ)) r) (twist s (twist s (recF1R s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ))) r) (recF2R s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ) r) (twist s (recF2R s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ)) r) (twist s (twist s (recF2R s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ))) r) (recHR s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ) r) (twist s (recHR s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ)) r) (twist s (twist s (recHR s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ))) r) + srcTT s μ r = 0 :=
  sourced_equation_TT hs hμ (ssSourcedMasterData s μ hs hμ y hy hODE) hr1

/-- The sourced harmonic `tr` equation for the scalar–scalar source and any smooth solution of the master equation. -/
theorem ssSourced_equation_TR (s μ : ℂ) (hs : s ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (y : ℝ → ℂ)
    (hy : ContDiffOn ℝ ∞ y (Ioi 1)) (hODE : SSMasterEquation s μ y) {r : ℝ} (hr1 : 1 < r) :
    harmonicTR s r μ (recF0R s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ) r) (twist s (recF0R s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ)) r) (twist s (twist s (recF0R s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ))) r) (recF1R s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ) r) (twist s (recF1R s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ)) r) (twist s (twist s (recF1R s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ))) r) (recF2R s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ) r) (twist s (recF2R s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ)) r) (twist s (twist s (recF2R s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ))) r) (recHR s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ) r) (twist s (recHR s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ)) r) (twist s (twist s (recHR s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ))) r) + srcTR s μ r = 0 :=
  sourced_equation_TR hs hμ (ssSourcedMasterData s μ hs hμ y hy hODE) hr1

/-- The sourced harmonic `rr` equation for the scalar–scalar source and any smooth solution of the master equation. -/
theorem ssSourced_equation_RR (s μ : ℂ) (hs : s ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (y : ℝ → ℂ)
    (hy : ContDiffOn ℝ ∞ y (Ioi 1)) (hODE : SSMasterEquation s μ y) {r : ℝ} (hr1 : 1 < r) :
    harmonicRR s r μ (recF0R s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ) r) (twist s (recF0R s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ)) r) (twist s (twist s (recF0R s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ))) r) (recF1R s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ) r) (twist s (recF1R s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ)) r) (twist s (twist s (recF1R s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ))) r) (recF2R s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ) r) (twist s (recF2R s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ)) r) (twist s (twist s (recF2R s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ))) r) (recHR s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ) r) (twist s (recHR s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ)) r) (twist s (twist s (recHR s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ))) r) + srcRR s μ r = 0 :=
  sourced_equation_RR hs hμ (ssSourcedMasterData s μ hs hμ y hy hODE) hr1

/-- The sourced harmonic `t` equation for the scalar–scalar source and any smooth solution of the master equation. -/
theorem ssSourced_equation_T (s μ : ℂ) (hs : s ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (y : ℝ → ℂ)
    (hy : ContDiffOn ℝ ∞ y (Ioi 1)) (hODE : SSMasterEquation s μ y) {r : ℝ} (hr1 : 1 < r) :
    harmonicT s r μ (recF0R s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ) r) (twist s (recF0R s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ)) r) (twist s (twist s (recF0R s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ))) r) (recF1R s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ) r) (twist s (recF1R s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ)) r) (twist s (twist s (recF1R s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ))) r) (recF2R s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ) r) (twist s (recF2R s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ)) r) (twist s (twist s (recF2R s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ))) r) (recHR s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ) r) (twist s (recHR s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ)) r) (twist s (twist s (recHR s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ))) r) + srcT s μ r = 0 :=
  sourced_equation_T hs hμ (ssSourcedMasterData s μ hs hμ y hy hODE) hr1

/-- The sourced harmonic `r` equation for the scalar–scalar source and any smooth solution of the master equation. -/
theorem ssSourced_equation_R (s μ : ℂ) (hs : s ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (y : ℝ → ℂ)
    (hy : ContDiffOn ℝ ∞ y (Ioi 1)) (hODE : SSMasterEquation s μ y) {r : ℝ} (hr1 : 1 < r) :
    harmonicR s r μ (recF0R s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ) r) (twist s (recF0R s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ)) r) (twist s (twist s (recF0R s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ))) r) (recF1R s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ) r) (twist s (recF1R s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ)) r) (twist s (twist s (recF1R s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ))) r) (recF2R s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ) r) (twist s (recF2R s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ)) r) (twist s (twist s (recF2R s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ))) r) (recHR s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ) r) (twist s (recHR s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ)) r) (twist s (twist s (recHR s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ))) r) + srcR s μ r = 0 :=
  sourced_equation_R hs hμ (ssSourcedMasterData s μ hs hμ y hy hODE) hr1

/-- The sourced harmonic `T` equation for the scalar–scalar source and any smooth solution of the master equation. -/
theorem ssSourced_equation_TF (s μ : ℂ) (hs : s ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (y : ℝ → ℂ)
    (hy : ContDiffOn ℝ ∞ y (Ioi 1)) (hODE : SSMasterEquation s μ y) {r : ℝ} (hr1 : 1 < r) :
    harmonicTF s r μ (recF0R s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ) r) (twist s (recF0R s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ)) r) (twist s (twist s (recF0R s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ))) r) (recF1R s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ) r) (twist s (recF1R s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ)) r) (twist s (twist s (recF1R s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ))) r) (recF2R s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ) r) (twist s (recF2R s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ)) r) (twist s (twist s (recF2R s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ))) r) (recHR s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ) r) (twist s (recHR s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ)) r) (twist s (twist s (recHR s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ))) r) + srcTF s μ r = 0 :=
  sourced_equation_TF hs hμ (ssSourcedMasterData s μ hs hμ y hy hODE) hr1

/-- The sourced harmonic `L` equation for the scalar–scalar source and any smooth solution of the master equation. -/
theorem ssSourced_equation_L (s μ : ℂ) (hs : s ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (y : ℝ → ℂ)
    (hy : ContDiffOn ℝ ∞ y (Ioi 1)) (hODE : SSMasterEquation s μ y) {r : ℝ} (hr1 : 1 < r) :
    harmonicL s r μ (recF0R s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ) r) (twist s (recF0R s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ)) r) (twist s (twist s (recF0R s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ))) r) (recF1R s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ) r) (twist s (recF1R s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ)) r) (twist s (twist s (recF1R s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ))) r) (recF2R s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ) r) (twist s (recF2R s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ)) r) (twist s (twist s (recF2R s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ))) r) (recHR s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ) r) (twist s (recHR s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ)) r) (twist s (twist s (recHR s μ y (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ))) r) + srcL s μ r = 0 :=
  sourced_equation_L hs hμ (ssSourcedMasterData s μ hs hμ y hy hODE) hr1

end
end RHTower.D4BMScalarStream
