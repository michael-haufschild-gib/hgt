import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMVectorVectorSourceHarmonic
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMScalarStreamReconstructionField

/-!
# The vector–vector harmonic source as radial functions

The seven harmonic vector–vector source coefficients are realised as rational-coefficient radial functions
`vvSrcTT, …, vvSrcL` (Horner form over `r^p (r²−1)^q`), smooth on the exterior, with their twisted
derivatives computed explicitly where the Bianchi identities and the master source need them. The
main theorem `vvSourcedMasterData` shows that any smooth undressed master function `y` solving the
sourced master equation `twist²y + (2r/(r²−1))twist y + (μ/(r²(r²−1)) − 4s²/(r²−1)²)y + vvMasterSource = 0`
on the exterior provides the data of the field-level reconstruction, so that the seven sourced
harmonic Einstein equations hold for the reconstructed radial functions (`vvSourced_equation_TT`, …).
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace RHTower.D4BMScalarStream
open GaloisForLFunctions.HTGeometry CoordinateMetricTwoJet GaloisForLFunctions.HTGeometry.TwistedRadial
open Filter Topology Set
open scoped ContDiff
noncomputable section

/-- Harmonic `tt` source coefficient as a radial function. -/
def vvSrcTT (s μ : ℂ) : ℝ → ℂ :=
  ratCoef [((-9 / 2 : ℂ) * s ^ 2 + (15 / 8 : ℂ) * s ^ 2 * μ + (-1 / 8 : ℂ) * s ^ 2 * μ ^ 2 + (-45 / 4 : ℂ) * s ^ 3 + (9 / 4 : ℂ) * s ^ 3 * μ + (-10 : ℂ) * s ^ 4 + (5 / 8 : ℂ) * s ^ 4 * μ + (-15 / 4 : ℂ) * s ^ 5 + (-1 / 2 : ℂ) * s ^ 6), (0 : ℂ), ((13 / 2 : ℂ) * s ^ 2 + (-15 / 8 : ℂ) * s ^ 2 * μ + (1 / 8 : ℂ) * s ^ 2 * μ ^ 2 + (61 / 4 : ℂ) * s ^ 3 + (-7 / 4 : ℂ) * s ^ 3 * μ + (23 / 2 : ℂ) * s ^ 4 + (-1 / 8 : ℂ) * s ^ 4 * μ + (11 / 4 : ℂ) * s ^ 5), (0 : ℂ), ((-2 : ℂ) * s ^ 2 + (1 / 2 : ℂ) * s ^ 2 * μ + (-3 : ℂ) * s ^ 3 + (-1 : ℂ) * s ^ 4)] 6 0

/-- Harmonic `tr` source coefficient as a radial function. -/
def vvSrcTR (s μ : ℂ) : ℝ → ℂ :=
  ratCoef [((1 / 2 : ℂ) * s ^ 2 * μ + (-3 : ℂ) * s ^ 3 + (3 / 2 : ℂ) * s ^ 3 * μ + (-11 / 2 : ℂ) * s ^ 4 + (1 / 2 : ℂ) * s ^ 4 * μ + (-3 : ℂ) * s ^ 5 + (-1 / 2 : ℂ) * s ^ 6), (0 : ℂ), ((4 : ℂ) * s ^ 3 + (-1 : ℂ) * s ^ 3 * μ + (6 : ℂ) * s ^ 4 + (2 : ℂ) * s ^ 5)] 5 1

/-- Harmonic `rr` source coefficient as a radial function. -/
def vvSrcRR (s μ : ℂ) : ℝ → ℂ :=
  ratCoef [((-7 / 2 : ℂ) * s ^ 2 + (5 / 8 : ℂ) * s ^ 2 * μ + (1 / 8 : ℂ) * s ^ 2 * μ ^ 2 + (-31 / 4 : ℂ) * s ^ 3 + (1 / 4 : ℂ) * s ^ 3 * μ + (-11 / 2 : ℂ) * s ^ 4 + (-1 / 8 : ℂ) * s ^ 4 * μ + (-5 / 4 : ℂ) * s ^ 5), (0 : ℂ), ((19 / 2 : ℂ) * s ^ 2 + (-13 / 8 : ℂ) * s ^ 2 * μ + (-1 / 8 : ℂ) * s ^ 2 * μ ^ 2 + (71 / 4 : ℂ) * s ^ 3 + (1 / 4 : ℂ) * s ^ 3 * μ + (9 : ℂ) * s ^ 4 + (5 / 8 : ℂ) * s ^ 4 * μ + (1 / 4 : ℂ) * s ^ 5 + (-1 / 2 : ℂ) * s ^ 6), (0 : ℂ), ((-6 : ℂ) * s ^ 2 + (3 / 2 : ℂ) * s ^ 2 * μ + (-9 : ℂ) * s ^ 3 + (-3 : ℂ) * s ^ 4)] 6 2

/-- Harmonic `t` source coefficient as a radial function. -/
def vvSrcT (s μ : ℂ) : ℝ → ℂ :=
  ratCoef [((3 / 2 : ℂ) * s ^ 2 + (7 / 4 : ℂ) * s ^ 3 + (1 / 4 : ℂ) * s ^ 3 * μ + (-1 / 4 : ℂ) * s ^ 5)] 4 0

/-- Harmonic `r` source coefficient as a radial function. -/
def vvSrcR (s μ : ℂ) : ℝ → ℂ :=
  ratCoef [((-1 / 2 : ℂ) * s ^ 2 + (1 / 2 : ℂ) * s ^ 2 * μ + (-5 / 4 : ℂ) * s ^ 3 + (1 / 4 : ℂ) * s ^ 3 * μ + (-1 : ℂ) * s ^ 4 + (-1 / 4 : ℂ) * s ^ 5), (0 : ℂ), ((2 : ℂ) * s ^ 2 + (-1 / 2 : ℂ) * s ^ 2 * μ + (3 : ℂ) * s ^ 3 + (1 : ℂ) * s ^ 4)] 5 1

/-- Harmonic `T` source coefficient as a radial function. -/
def vvSrcTF (s μ : ℂ) : ℝ → ℂ :=
  ratCoef [(((-11 : ℂ) * s ^ 2 + (-57 / 2 : ℂ) * s ^ 3 + (-53 / 2 : ℂ) * s ^ 4 + (-21 / 2 : ℂ) * s ^ 5 + (-3 / 2 : ℂ) * s ^ 6) / ((2 - μ)))] 4 0

/-- Harmonic `L` source coefficient as a radial function. -/
def vvSrcL (s μ : ℂ) : ℝ → ℂ :=
  ratCoef [((-7 : ℂ) * s ^ 2 + (3 / 2 : ℂ) * s ^ 2 * μ + (-19 : ℂ) * s ^ 3 + (7 / 4 : ℂ) * s ^ 3 * μ + (-75 / 4 : ℂ) * s ^ 4 + (1 / 2 : ℂ) * s ^ 4 * μ + (-8 : ℂ) * s ^ 5 + (-5 / 4 : ℂ) * s ^ 6), (0 : ℂ), ((2 : ℂ) * s ^ 2 + (-1 / 2 : ℂ) * s ^ 2 * μ + (3 : ℂ) * s ^ 3 + (1 : ℂ) * s ^ 4)] 4 0

/-- Twisted derivative of `vvSrcTR` as a radial function. -/
def vvSrcTR1 (s μ : ℂ) : ℝ → ℂ :=
  ratCoef [((5 / 2 : ℂ) * s ^ 2 * μ + (-15 : ℂ) * s ^ 3 + (17 / 2 : ℂ) * s ^ 3 * μ + (-67 / 2 : ℂ) * s ^ 4 + (11 / 2 : ℂ) * s ^ 4 * μ + (-26 : ℂ) * s ^ 5 + (1 : ℂ) * s ^ 5 * μ + (-17 / 2 : ℂ) * s ^ 6 + (-1 : ℂ) * s ^ 7), (0 : ℂ), ((-7 / 2 : ℂ) * s ^ 2 * μ + (33 : ℂ) * s ^ 3 + (-27 / 2 : ℂ) * s ^ 3 * μ + (129 / 2 : ℂ) * s ^ 4 + (-11 / 2 : ℂ) * s ^ 4 * μ + (39 : ℂ) * s ^ 5 + (15 / 2 : ℂ) * s ^ 6), (0 : ℂ), ((-20 : ℂ) * s ^ 3 + (5 : ℂ) * s ^ 3 * μ + (-30 : ℂ) * s ^ 4 + (-10 : ℂ) * s ^ 5)] 6 2

/-- Twisted derivative of `vvSrcRR` as a radial function. -/
def vvSrcRR1 (s μ : ℂ) : ℝ → ℂ :=
  ratCoef [((-21 : ℂ) * s ^ 2 + (15 / 4 : ℂ) * s ^ 2 * μ + (3 / 4 : ℂ) * s ^ 2 * μ ^ 2 + (-107 / 2 : ℂ) * s ^ 3 + (11 / 4 : ℂ) * s ^ 3 * μ + (1 / 4 : ℂ) * s ^ 3 * μ ^ 2 + (-97 / 2 : ℂ) * s ^ 4 + (-1 / 4 : ℂ) * s ^ 4 * μ + (-37 / 2 : ℂ) * s ^ 5 + (-1 / 4 : ℂ) * s ^ 5 * μ + (-5 / 2 : ℂ) * s ^ 6), (0 : ℂ), ((73 : ℂ) * s ^ 2 + (-51 / 4 : ℂ) * s ^ 2 * μ + (-7 / 4 : ℂ) * s ^ 2 * μ ^ 2 + (335 / 2 : ℂ) * s ^ 3 + (-19 / 4 : ℂ) * s ^ 3 * μ + (-1 / 4 : ℂ) * s ^ 3 * μ ^ 2 + (253 / 2 : ℂ) * s ^ 4 + (17 / 4 : ℂ) * s ^ 4 * μ + (63 / 2 : ℂ) * s ^ 5 + (5 / 4 : ℂ) * s ^ 5 * μ + (-3 / 2 : ℂ) * s ^ 6 + (-1 : ℂ) * s ^ 7), (0 : ℂ), ((-88 : ℂ) * s ^ 2 + (16 : ℂ) * s ^ 2 * μ + (1 : ℂ) * s ^ 2 * μ ^ 2 + (-172 : ℂ) * s ^ 3 + (1 : ℂ) * s ^ 3 * μ + (-96 : ℂ) * s ^ 4 + (-5 : ℂ) * s ^ 4 * μ + (-8 : ℂ) * s ^ 5 + (4 : ℂ) * s ^ 6), (0 : ℂ), ((36 : ℂ) * s ^ 2 + (-9 : ℂ) * s ^ 2 * μ + (54 : ℂ) * s ^ 3 + (18 : ℂ) * s ^ 4)] 7 3

/-- Twisted derivative of `vvSrcR` as a radial function. -/
def vvSrcR1 (s μ : ℂ) : ℝ → ℂ :=
  ratCoef [((-5 / 2 : ℂ) * s ^ 2 + (5 / 2 : ℂ) * s ^ 2 * μ + (-29 / 4 : ℂ) * s ^ 3 + (9 / 4 : ℂ) * s ^ 3 * μ + (-15 / 2 : ℂ) * s ^ 4 + (1 / 2 : ℂ) * s ^ 4 * μ + (-13 / 4 : ℂ) * s ^ 5 + (-1 / 2 : ℂ) * s ^ 6), (0 : ℂ), ((19 / 2 : ℂ) * s ^ 2 + (-5 : ℂ) * s ^ 2 * μ + (87 / 4 : ℂ) * s ^ 3 + (-11 / 4 : ℂ) * s ^ 3 * μ + (16 : ℂ) * s ^ 4 + (15 / 4 : ℂ) * s ^ 5), (0 : ℂ), ((-10 : ℂ) * s ^ 2 + (5 / 2 : ℂ) * s ^ 2 * μ + (-15 : ℂ) * s ^ 3 + (-5 : ℂ) * s ^ 4)] 6 2

/-- Twisted derivative of `vvSrcT` as a radial function. -/
def vvSrcT1 (s μ : ℂ) : ℝ → ℂ :=
  ratCoef [((6 : ℂ) * s ^ 2 + (10 : ℂ) * s ^ 3 + (1 : ℂ) * s ^ 3 * μ + (7 / 2 : ℂ) * s ^ 4 + (1 / 2 : ℂ) * s ^ 4 * μ + (-1 : ℂ) * s ^ 5 + (-1 / 2 : ℂ) * s ^ 6), (0 : ℂ), ((-6 : ℂ) * s ^ 2 + (-7 : ℂ) * s ^ 3 + (-1 : ℂ) * s ^ 3 * μ + (1 : ℂ) * s ^ 5)] 5 1

/-- Twisted derivative of `vvSrcTF` as a radial function. -/
def vvSrcTF1 (s μ : ℂ) : ℝ → ℂ :=
  ratCoef [(((-44 : ℂ) * s ^ 2 + (-136 : ℂ) * s ^ 3 + (-163 : ℂ) * s ^ 4 + (-95 : ℂ) * s ^ 5 + (-27 : ℂ) * s ^ 6 + (-3 : ℂ) * s ^ 7) / ((2 - μ))), (0 : ℂ), (((44 : ℂ) * s ^ 2 + (114 : ℂ) * s ^ 3 + (106 : ℂ) * s ^ 4 + (42 : ℂ) * s ^ 5 + (6 : ℂ) * s ^ 6) / ((2 - μ)))] 5 1

/-- Second twisted derivative of `vvSrcTF`. -/
def vvSrcTF2 (s μ : ℂ) : ℝ → ℂ :=
  ratCoef [(((-220 : ℂ) * s ^ 2 + (-768 : ℂ) * s ^ 3 + (-1087 : ℂ) * s ^ 4 + (-801 : ℂ) * s ^ 5 + (-325 : ℂ) * s ^ 6 + (-69 : ℂ) * s ^ 7 + (-6 : ℂ) * s ^ 8) / ((2 - μ))), (0 : ℂ), (((440 : ℂ) * s ^ 2 + (1382 : ℂ) * s ^ 3 + (1687 : ℂ) * s ^ 4 + (1003 : ℂ) * s ^ 5 + (291 : ℂ) * s ^ 6 + (33 : ℂ) * s ^ 7) / ((2 - μ))), (0 : ℂ), (((-220 : ℂ) * s ^ 2 + (-570 : ℂ) * s ^ 3 + (-530 : ℂ) * s ^ 4 + (-210 : ℂ) * s ^ 5 + (-30 : ℂ) * s ^ 6) / ((2 - μ)))] 6 2

theorem vvSrcTT_eq (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) (hs : s ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) : vvSrcTT s μ r = vvSourceTT s r μ := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  unfold vvSrcTT vvSourceTT
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

theorem vvSrcTR_eq (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) (hs : s ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) : vvSrcTR s μ r = vvSourceTR s r μ := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  unfold vvSrcTR vvSourceTR
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

theorem vvSrcRR_eq (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) (hs : s ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) : vvSrcRR s μ r = vvSourceRR s r μ := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  unfold vvSrcRR vvSourceRR
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

theorem vvSrcT_eq (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) (hs : s ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) : vvSrcT s μ r = vvSourceT s r μ := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  unfold vvSrcT vvSourceT
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

theorem vvSrcR_eq (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) (hs : s ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) : vvSrcR s μ r = vvSourceR s r μ := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  unfold vvSrcR vvSourceR
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

theorem vvSrcTF_eq (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) (hs : s ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) : vvSrcTF s μ r = vvSourceTF s r μ := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  unfold vvSrcTF vvSourceTF
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

theorem vvSrcL_eq (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) (hs : s ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) : vvSrcL s μ r = vvSourceL s r μ := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  unfold vvSrcL vvSourceL
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

theorem vvSrcTR1_eq (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) (hs : s ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) : vvSrcTR1 s μ r = vvSourceTR1 s r μ := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  unfold vvSrcTR1 vvSourceTR1
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

theorem vvSrcRR1_eq (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) (hs : s ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) : vvSrcRR1 s μ r = vvSourceRR1 s r μ := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  unfold vvSrcRR1 vvSourceRR1
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

theorem vvSrcR1_eq (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) (hs : s ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) : vvSrcR1 s μ r = vvSourceR1 s r μ := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  unfold vvSrcR1 vvSourceR1
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

theorem vvSrcT1_eq (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) (hs : s ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) : vvSrcT1 s μ r = vvSourceT1 s r μ := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  unfold vvSrcT1 vvSourceT1
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

theorem vvSrcTF1_eq (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) (hs : s ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) : vvSrcTF1 s μ r = vvSourceTF1 s r μ := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  unfold vvSrcTF1 vvSourceTF1
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

theorem vvSrcTF2_eq (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) (hs : s ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) : vvSrcTF2 s μ r = vvSourceTF2 s r μ := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  unfold vvSrcTF2 vvSourceTF2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

theorem twist_vvSrcTR (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) : twist s (vvSrcTR s μ) r = vvSrcTR1 s μ r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  unfold twist vvSrcTR vvSrcTR1
  rw [(hasDerivAt_ratCoef _ _ _ hr hf).deriv]
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

theorem twist_vvSrcRR (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) : twist s (vvSrcRR s μ) r = vvSrcRR1 s μ r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  unfold twist vvSrcRR vvSrcRR1
  rw [(hasDerivAt_ratCoef _ _ _ hr hf).deriv]
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

theorem twist_vvSrcR (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) : twist s (vvSrcR s μ) r = vvSrcR1 s μ r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  unfold twist vvSrcR vvSrcR1
  rw [(hasDerivAt_ratCoef _ _ _ hr hf).deriv]
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

theorem twist_vvSrcT (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) : twist s (vvSrcT s μ) r = vvSrcT1 s μ r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  unfold twist vvSrcT vvSrcT1
  rw [(hasDerivAt_ratCoef _ _ _ hr hf).deriv]
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

theorem twist_vvSrcTF (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) : twist s (vvSrcTF s μ) r = vvSrcTF1 s μ r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  unfold twist vvSrcTF vvSrcTF1
  rw [(hasDerivAt_ratCoef _ _ _ hr hf).deriv]
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

theorem twist_vvSrcTF1 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) : twist s (vvSrcTF1 s μ) r = vvSrcTF2 s μ r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  unfold twist vvSrcTF1 vvSrcTF2
  rw [(hasDerivAt_ratCoef _ _ _ hr hf).deriv]
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

theorem twistIter_vvSrcTF_two (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    twistIter s 2 (vvSrcTF s μ) r = vvSrcTF2 s μ r := by
  simp only [twistIter_succ, twistIter_zero]
  rw [twist_congr s (g := twist s (vvSrcTF s μ)) (h := vvSrcTF1 s μ) (by
    filter_upwards [exterior_eventually hr1] with r' hr' using twist_vvSrcTF s μ hr')]
  exact twist_vvSrcTF1 s μ hr1

theorem vvSrcTT_contDiffOn (s μ : ℂ) : ContDiffOn ℝ ∞ (vvSrcTT s μ) (Ioi 1) :=
  contDiffOn_ratCoef _ _ _

theorem vvSrcTT_twistSmooth (s μ : ℂ) (n : ℕ) : TwistSmooth s (vvSrcTT s μ) n :=
  fun r hr k _ => differentiableAt_twistIter s (vvSrcTT_contDiffOn s μ) k hr

theorem vvSrcTR_contDiffOn (s μ : ℂ) : ContDiffOn ℝ ∞ (vvSrcTR s μ) (Ioi 1) :=
  contDiffOn_ratCoef _ _ _

theorem vvSrcTR_twistSmooth (s μ : ℂ) (n : ℕ) : TwistSmooth s (vvSrcTR s μ) n :=
  fun r hr k _ => differentiableAt_twistIter s (vvSrcTR_contDiffOn s μ) k hr

theorem vvSrcRR_contDiffOn (s μ : ℂ) : ContDiffOn ℝ ∞ (vvSrcRR s μ) (Ioi 1) :=
  contDiffOn_ratCoef _ _ _

theorem vvSrcRR_twistSmooth (s μ : ℂ) (n : ℕ) : TwistSmooth s (vvSrcRR s μ) n :=
  fun r hr k _ => differentiableAt_twistIter s (vvSrcRR_contDiffOn s μ) k hr

theorem vvSrcT_contDiffOn (s μ : ℂ) : ContDiffOn ℝ ∞ (vvSrcT s μ) (Ioi 1) :=
  contDiffOn_ratCoef _ _ _

theorem vvSrcT_twistSmooth (s μ : ℂ) (n : ℕ) : TwistSmooth s (vvSrcT s μ) n :=
  fun r hr k _ => differentiableAt_twistIter s (vvSrcT_contDiffOn s μ) k hr

theorem vvSrcR_contDiffOn (s μ : ℂ) : ContDiffOn ℝ ∞ (vvSrcR s μ) (Ioi 1) :=
  contDiffOn_ratCoef _ _ _

theorem vvSrcR_twistSmooth (s μ : ℂ) (n : ℕ) : TwistSmooth s (vvSrcR s μ) n :=
  fun r hr k _ => differentiableAt_twistIter s (vvSrcR_contDiffOn s μ) k hr

theorem vvSrcTF_contDiffOn (s μ : ℂ) : ContDiffOn ℝ ∞ (vvSrcTF s μ) (Ioi 1) :=
  contDiffOn_ratCoef _ _ _

theorem vvSrcTF_twistSmooth (s μ : ℂ) (n : ℕ) : TwistSmooth s (vvSrcTF s μ) n :=
  fun r hr k _ => differentiableAt_twistIter s (vvSrcTF_contDiffOn s μ) k hr

theorem vvSrcL_contDiffOn (s μ : ℂ) : ContDiffOn ℝ ∞ (vvSrcL s μ) (Ioi 1) :=
  contDiffOn_ratCoef _ _ _

theorem vvSrcL_twistSmooth (s μ : ℂ) (n : ℕ) : TwistSmooth s (vvSrcL s μ) n :=
  fun r hr k _ => differentiableAt_twistIter s (vvSrcL_contDiffOn s μ) k hr

/-- The undressed sourced master equation for the vector–vector source. -/
def VVMasterEquation (s μ : ℂ) (y : ℝ → ℂ) : Prop :=
  ∀ r : ℝ, 1 < r → twist s (twist s y) r + 2 * r / ((r : ℂ) ^ 2 - 1) * twist s y r +
    (μ / ((r : ℂ) ^ 2 * ((r : ℂ) ^ 2 - 1)) - 4 * s ^ 2 / ((r : ℂ) ^ 2 - 1) ^ 2) * y r + vvMasterSource s r μ = 0

theorem masterDefect0R_vvSrc (s μ : ℂ) (y : ℝ → ℂ) {r : ℝ} (hr1 : 1 < r) (hs : s ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    masterDefect0R s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ) r =
      twist s (twist s y) r + 2 * r / ((r : ℂ) ^ 2 - 1) * twist s y r +
        (μ / ((r : ℂ) ^ 2 * ((r : ℂ) ^ 2 - 1)) - 4 * s ^ 2 / ((r : ℂ) ^ 2 - 1) ^ 2) * y r + vvMasterSource s r μ := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  rw [masterDefect0R_eq s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ) hr1 hs hμ]
  simp only [twistIter_succ, twistIter_zero]
  rw [twist_vvSrcT s μ hr1, twist_vvSrcTF s μ hr1, twist_congr s (g := twist s (vvSrcTF s μ)) (h := vvSrcTF1 s μ) (by
    filter_upwards [exterior_eventually hr1] with r' hr' using twist_vvSrcTF s μ hr'), twist_vvSrcTF1 s μ hr1]
  simp only [vvSrcTT_eq s μ hr1 hs hμ, vvSrcTR_eq s μ hr1 hs hμ, vvSrcRR_eq s μ hr1 hs hμ, vvSrcT_eq s μ hr1 hs hμ, vvSrcR_eq s μ hr1 hs hμ, vvSrcTF_eq s μ hr1 hs hμ, vvSrcL_eq s μ hr1 hs hμ, vvSrcT1_eq s μ hr1 hs hμ, vvSrcTF1_eq s μ hr1 hs hμ, vvSrcTF2_eq s μ hr1 hs hμ]
  unfold masterDefect0 vvSourceTT vvSourceTR vvSourceRR vvSourceT vvSourceR vvSourceTF vvSourceT1 vvSourceTF1 vvSourceTF2 vvMasterSource
  field_simp
  ring

theorem vvSrc_bianchiT (s μ : ℂ) (y : ℝ → ℂ) {r : ℝ} (hr1 : 1 < r) (hs : s ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    bianchiT0R s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ) r = 0 := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  rw [bianchiT0R_eq s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ) hr1 hs hμ]
  simp only [twistIter_succ, twistIter_zero]
  rw [twist_vvSrcTR s μ hr1]
  simp only [vvSrcTT_eq s μ hr1 hs hμ, vvSrcTR_eq s μ hr1 hs hμ, vvSrcRR_eq s μ hr1 hs hμ, vvSrcT_eq s μ hr1 hs hμ, vvSrcR_eq s μ hr1 hs hμ, vvSrcTF_eq s μ hr1 hs hμ, vvSrcL_eq s μ hr1 hs hμ, vvSrcTR1_eq s μ hr1 hs hμ, vvSrcRR1_eq s μ hr1 hs hμ, vvSrcR1_eq s μ hr1 hs hμ]
  unfold bianchiT0 vvSourceTT vvSourceTR vvSourceTR1 vvSourceT
  field_simp
  ring

theorem vvSrc_bianchiR (s μ : ℂ) (y : ℝ → ℂ) {r : ℝ} (hr1 : 1 < r) (hs : s ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    bianchiR0R s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ) r = 0 := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  rw [bianchiR0R_eq s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ) hr1 hs hμ]
  simp only [twistIter_succ, twistIter_zero]
  rw [twist_vvSrcRR s μ hr1]
  simp only [vvSrcTT_eq s μ hr1 hs hμ, vvSrcTR_eq s μ hr1 hs hμ, vvSrcRR_eq s μ hr1 hs hμ, vvSrcT_eq s μ hr1 hs hμ, vvSrcR_eq s μ hr1 hs hμ, vvSrcTF_eq s μ hr1 hs hμ, vvSrcL_eq s μ hr1 hs hμ, vvSrcTR1_eq s μ hr1 hs hμ, vvSrcRR1_eq s μ hr1 hs hμ, vvSrcR1_eq s μ hr1 hs hμ]
  unfold bianchiR0 vvSourceTT vvSourceTR vvSourceRR vvSourceRR1 vvSourceR vvSourceL
  field_simp
  ring

theorem vvSrc_bianchiAng (s μ : ℂ) (y : ℝ → ℂ) {r : ℝ} (hr1 : 1 < r) (hs : s ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    bianchiAng0R s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ) r = 0 := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  rw [bianchiAng0R_eq s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ) hr1 hs hμ]
  simp only [twistIter_succ, twistIter_zero]
  rw [twist_vvSrcR s μ hr1]
  simp only [vvSrcTT_eq s μ hr1 hs hμ, vvSrcTR_eq s μ hr1 hs hμ, vvSrcRR_eq s μ hr1 hs hμ, vvSrcT_eq s μ hr1 hs hμ, vvSrcR_eq s μ hr1 hs hμ, vvSrcTF_eq s μ hr1 hs hμ, vvSrcL_eq s μ hr1 hs hμ, vvSrcTR1_eq s μ hr1 hs hμ, vvSrcRR1_eq s μ hr1 hs hμ, vvSrcR1_eq s μ hr1 hs hμ]
  unfold bianchiAng0 vvSourceT vvSourceR vvSourceR1 vvSourceTF vvSourceL
  field_simp
  ring

/-- A smooth solution of the undressed sourced master equation yields the field-level data. -/
theorem vvSourcedMasterData (s μ : ℂ) (hs : s ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (y : ℝ → ℂ)
    (hy : ContDiffOn ℝ ∞ y (Ioi 1)) (hODE : VVMasterEquation s μ y) :
    SourcedMasterData s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ) where
  smooth_y := fun r hr k _ => differentiableAt_twistIter s hy k hr
  smooth_tTT := vvSrcTT_twistSmooth s μ 4
  smooth_tTR := vvSrcTR_twistSmooth s μ 4
  smooth_tRR := vvSrcRR_twistSmooth s μ 4
  smooth_tT := vvSrcT_twistSmooth s μ 4
  smooth_tR := vvSrcR_twistSmooth s μ 4
  smooth_tTF := vvSrcTF_twistSmooth s μ 4
  smooth_tL := vvSrcL_twistSmooth s μ 4
  master := fun r hr1 => by rw [masterDefect0R_vvSrc s μ y hr1 hs hμ]; exact hODE r hr1
  bianchiT := fun r hr1 => vvSrc_bianchiT s μ y hr1 hs hμ
  bianchiR := fun r hr1 => vvSrc_bianchiR s μ y hr1 hs hμ
  bianchiAng := fun r hr1 => vvSrc_bianchiAng s μ y hr1 hs hμ

/-- The sourced harmonic `tt` equation for the vector–vector source and any smooth solution of the master equation. -/
theorem vvSourced_equation_TT (s μ : ℂ) (hs : s ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (y : ℝ → ℂ)
    (hy : ContDiffOn ℝ ∞ y (Ioi 1)) (hODE : VVMasterEquation s μ y) {r : ℝ} (hr1 : 1 < r) :
    harmonicTT s r μ (recF0R s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ) r) (twist s (recF0R s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ)) r) (twist s (twist s (recF0R s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ))) r) (recF1R s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ) r) (twist s (recF1R s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ)) r) (twist s (twist s (recF1R s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ))) r) (recF2R s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ) r) (twist s (recF2R s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ)) r) (twist s (twist s (recF2R s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ))) r) (recHR s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ) r) (twist s (recHR s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ)) r) (twist s (twist s (recHR s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ))) r) + vvSrcTT s μ r = 0 :=
  sourced_equation_TT hs hμ (vvSourcedMasterData s μ hs hμ y hy hODE) hr1

/-- The sourced harmonic `tr` equation for the vector–vector source and any smooth solution of the master equation. -/
theorem vvSourced_equation_TR (s μ : ℂ) (hs : s ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (y : ℝ → ℂ)
    (hy : ContDiffOn ℝ ∞ y (Ioi 1)) (hODE : VVMasterEquation s μ y) {r : ℝ} (hr1 : 1 < r) :
    harmonicTR s r μ (recF0R s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ) r) (twist s (recF0R s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ)) r) (twist s (twist s (recF0R s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ))) r) (recF1R s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ) r) (twist s (recF1R s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ)) r) (twist s (twist s (recF1R s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ))) r) (recF2R s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ) r) (twist s (recF2R s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ)) r) (twist s (twist s (recF2R s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ))) r) (recHR s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ) r) (twist s (recHR s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ)) r) (twist s (twist s (recHR s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ))) r) + vvSrcTR s μ r = 0 :=
  sourced_equation_TR hs hμ (vvSourcedMasterData s μ hs hμ y hy hODE) hr1

/-- The sourced harmonic `rr` equation for the vector–vector source and any smooth solution of the master equation. -/
theorem vvSourced_equation_RR (s μ : ℂ) (hs : s ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (y : ℝ → ℂ)
    (hy : ContDiffOn ℝ ∞ y (Ioi 1)) (hODE : VVMasterEquation s μ y) {r : ℝ} (hr1 : 1 < r) :
    harmonicRR s r μ (recF0R s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ) r) (twist s (recF0R s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ)) r) (twist s (twist s (recF0R s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ))) r) (recF1R s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ) r) (twist s (recF1R s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ)) r) (twist s (twist s (recF1R s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ))) r) (recF2R s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ) r) (twist s (recF2R s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ)) r) (twist s (twist s (recF2R s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ))) r) (recHR s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ) r) (twist s (recHR s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ)) r) (twist s (twist s (recHR s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ))) r) + vvSrcRR s μ r = 0 :=
  sourced_equation_RR hs hμ (vvSourcedMasterData s μ hs hμ y hy hODE) hr1

/-- The sourced harmonic `t` equation for the vector–vector source and any smooth solution of the master equation. -/
theorem vvSourced_equation_T (s μ : ℂ) (hs : s ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (y : ℝ → ℂ)
    (hy : ContDiffOn ℝ ∞ y (Ioi 1)) (hODE : VVMasterEquation s μ y) {r : ℝ} (hr1 : 1 < r) :
    harmonicT s r μ (recF0R s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ) r) (twist s (recF0R s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ)) r) (twist s (twist s (recF0R s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ))) r) (recF1R s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ) r) (twist s (recF1R s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ)) r) (twist s (twist s (recF1R s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ))) r) (recF2R s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ) r) (twist s (recF2R s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ)) r) (twist s (twist s (recF2R s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ))) r) (recHR s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ) r) (twist s (recHR s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ)) r) (twist s (twist s (recHR s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ))) r) + vvSrcT s μ r = 0 :=
  sourced_equation_T hs hμ (vvSourcedMasterData s μ hs hμ y hy hODE) hr1

/-- The sourced harmonic `r` equation for the vector–vector source and any smooth solution of the master equation. -/
theorem vvSourced_equation_R (s μ : ℂ) (hs : s ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (y : ℝ → ℂ)
    (hy : ContDiffOn ℝ ∞ y (Ioi 1)) (hODE : VVMasterEquation s μ y) {r : ℝ} (hr1 : 1 < r) :
    harmonicR s r μ (recF0R s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ) r) (twist s (recF0R s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ)) r) (twist s (twist s (recF0R s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ))) r) (recF1R s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ) r) (twist s (recF1R s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ)) r) (twist s (twist s (recF1R s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ))) r) (recF2R s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ) r) (twist s (recF2R s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ)) r) (twist s (twist s (recF2R s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ))) r) (recHR s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ) r) (twist s (recHR s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ)) r) (twist s (twist s (recHR s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ))) r) + vvSrcR s μ r = 0 :=
  sourced_equation_R hs hμ (vvSourcedMasterData s μ hs hμ y hy hODE) hr1

/-- The sourced harmonic `T` equation for the vector–vector source and any smooth solution of the master equation. -/
theorem vvSourced_equation_TF (s μ : ℂ) (hs : s ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (y : ℝ → ℂ)
    (hy : ContDiffOn ℝ ∞ y (Ioi 1)) (hODE : VVMasterEquation s μ y) {r : ℝ} (hr1 : 1 < r) :
    harmonicTF s r μ (recF0R s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ) r) (twist s (recF0R s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ)) r) (twist s (twist s (recF0R s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ))) r) (recF1R s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ) r) (twist s (recF1R s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ)) r) (twist s (twist s (recF1R s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ))) r) (recF2R s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ) r) (twist s (recF2R s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ)) r) (twist s (twist s (recF2R s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ))) r) (recHR s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ) r) (twist s (recHR s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ)) r) (twist s (twist s (recHR s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ))) r) + vvSrcTF s μ r = 0 :=
  sourced_equation_TF hs hμ (vvSourcedMasterData s μ hs hμ y hy hODE) hr1

/-- The sourced harmonic `L` equation for the vector–vector source and any smooth solution of the master equation. -/
theorem vvSourced_equation_L (s μ : ℂ) (hs : s ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (y : ℝ → ℂ)
    (hy : ContDiffOn ℝ ∞ y (Ioi 1)) (hODE : VVMasterEquation s μ y) {r : ℝ} (hr1 : 1 < r) :
    harmonicL s r μ (recF0R s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ) r) (twist s (recF0R s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ)) r) (twist s (twist s (recF0R s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ))) r) (recF1R s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ) r) (twist s (recF1R s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ)) r) (twist s (twist s (recF1R s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ))) r) (recF2R s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ) r) (twist s (recF2R s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ)) r) (twist s (twist s (recF2R s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ))) r) (recHR s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ) r) (twist s (recHR s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ)) r) (twist s (twist s (recHR s μ y (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ))) r) + vvSrcL s μ r = 0 :=
  sourced_equation_L hs hμ (vvSourcedMasterData s μ hs hμ y hy hODE) hr1

end
end RHTower.D4BMScalarStream
