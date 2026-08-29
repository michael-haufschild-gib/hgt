import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinSignedMaassWhittakerTail
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinCuspAnalyticFinitePart
import GaloisForLFunctions.RHTower.ReflectedBiHeatCompletedChannels
import GaloisForLFunctions.RHTower.PrimeLogJumpMellinTrace

/-!
# Full completed-Eisenstein cusp-sector assembly for the balanced Maass current

This module assembles the exact cusp Fourier model required by the two balanced-spin Stokes
steps.  At centered parameter `u`, one completed Eisenstein leg is its two Weyl monomials

`Lambda(2u) Y^(1/2-u) + Lambda(1+2u) Y^(1/2+u)`

plus twice the full signed Whittaker tail.  On a zero-frequency monomial `Y^w`, both two-step
words `R_2 R_0` and `L_(-2) L_0` act by `w(w+1)`; Lean proves this from the corpus complex-cpow
derivative, rather than encoding the coefficient by fiat.

The normalized boundary current is

`Y^(-1) * raised(u) * lowered(u) * scalar(v)`.

Its product expansion has exactly eight sector groups: one all-constant group and seven groups
containing at least one nonconstant tail.  Lean proves the seven mixed groups tend to zero for
every horocycle coordinate.  The all-constant exponent specializes exactly to the prior affine
analytic-family exponent, whose finite part is zero.  The factor `Y^(-1)` is essential: it changes
the three half-powers from constant coordinate `3/2` to the Stokes coordinate `1/2`.

This closes source-faithful cusp-sector algebra and decay.  It does not yet prove equality between
the Fourier model and a Poincare-sum Eisenstein series, nor truncated modular integration by parts.

`[BRIDGE] [PAPER-PROVED] [LEAN-PROVED] [HC94] [FULL CUSP SECTOR ASSEMBLY]`
-/

open Complex Real Finset Filter Topology
open scoped BigOperators NNReal

namespace RHTower
noncomputable section

def d4BMZeroFrequencyMaassRaiseAt (k : ℤ) (Y : ℝ) (value deriv : ℂ) : ℂ :=
  (Y : ℂ) * deriv + (k : ℂ) / 2 * value

def d4BMZeroFrequencyMaassLowerAt (k : ℤ) (Y : ℝ) (value deriv : ℂ) : ℂ :=
  (Y : ℂ) * deriv - (k : ℂ) / 2 * value

theorem d4BM_zeroFrequency_cpow_mul_deriv (w : ℂ) {Y : ℝ} (hY : 0 < Y) :
    (Y : ℂ) * (w * (Y : ℂ) ^ (w - 1)) = w * (Y : ℂ) ^ w := by
  have hYC : (Y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hY.ne'
  rw [show w = (w - 1) + 1 by ring, Complex.cpow_add _ _ hYC]
  simp
  ring

theorem d4BM_zeroFrequency_raiseZero_cpow (w : ℂ) {Y : ℝ} (hY : 0 < Y) :
    d4BMZeroFrequencyMaassRaiseAt 0 Y ((Y : ℂ) ^ w) (w * (Y : ℂ) ^ (w - 1)) =
      w * (Y : ℂ) ^ w := by
  simp [d4BMZeroFrequencyMaassRaiseAt, d4BM_zeroFrequency_cpow_mul_deriv w hY]

theorem d4BM_zeroFrequency_lowerZero_cpow (w : ℂ) {Y : ℝ} (hY : 0 < Y) :
    d4BMZeroFrequencyMaassLowerAt 0 Y ((Y : ℂ) ^ w) (w * (Y : ℂ) ^ (w - 1)) =
      w * (Y : ℂ) ^ w := by
  simp [d4BMZeroFrequencyMaassLowerAt, d4BM_zeroFrequency_cpow_mul_deriv w hY]

theorem d4BM_zeroFrequency_raiseTwoRaiseZero_cpow (w : ℂ) {Y : ℝ} (hY : 0 < Y) :
    d4BMZeroFrequencyMaassRaiseAt 2 Y (w * (Y : ℂ) ^ w)
        (w * (w * (Y : ℂ) ^ (w - 1))) =
      w * (w + 1) * (Y : ℂ) ^ w := by
  rw [d4BMZeroFrequencyMaassRaiseAt]
  rw [show (Y : ℂ) * (w * (w * (Y : ℂ) ^ (w - 1))) =
    w * ((Y : ℂ) * (w * (Y : ℂ) ^ (w - 1))) by ring]
  rw [d4BM_zeroFrequency_cpow_mul_deriv w hY]
  push_cast
  ring

theorem d4BM_zeroFrequency_lowerNegTwoLowerZero_cpow (w : ℂ) {Y : ℝ} (hY : 0 < Y) :
    d4BMZeroFrequencyMaassLowerAt (-2) Y (w * (Y : ℂ) ^ w)
        (w * (w * (Y : ℂ) ^ (w - 1))) =
      w * (w + 1) * (Y : ℂ) ^ w := by
  rw [d4BMZeroFrequencyMaassLowerAt]
  rw [show (Y : ℂ) * (w * (w * (Y : ℂ) ^ (w - 1))) =
    w * ((Y : ℂ) * (w * (Y : ℂ) ^ (w - 1))) by ring]
  rw [d4BM_zeroFrequency_cpow_mul_deriv w hY]
  push_cast
  ring

inductive D4BMCompletedEisensteinCuspLegKind
  | scalar
  | raise
  | lower
  deriving DecidableEq

def d4BMCompletedEisensteinCuspWeylExponent (u : ℂ) (epsilon : Bool) : ℂ :=
  1 / 2 + (d4BMCuspSign epsilon : ℂ) * u

def d4BMCompletedEisensteinCuspConstantCoefficient (u : ℂ) (epsilon : Bool) : ℂ :=
  if epsilon then reflectedCompletedLambda (1 + 2 * u)
  else reflectedCompletedLambda (2 * u)

def d4BMCompletedEisensteinCuspConstantMaassFactor (kind : D4BMCompletedEisensteinCuspLegKind) (w : ℂ) : ℂ :=
  match kind with
  | .scalar => 1
  | .raise => w * (w + 1)
  | .lower => w * (w + 1)

def d4BMCompletedEisensteinCuspConstantTerm (kind : D4BMCompletedEisensteinCuspLegKind) (u : ℂ) (epsilon : Bool) (Y : ℝ) : ℂ :=
  d4BMCompletedEisensteinCuspConstantCoefficient u epsilon *
    d4BMCompletedEisensteinCuspConstantMaassFactor kind (d4BMCompletedEisensteinCuspWeylExponent u epsilon) *
    (Y : ℂ) ^ (d4BMCompletedEisensteinCuspWeylExponent u epsilon)

def d4BMCompletedEisensteinCuspConstantPart (kind : D4BMCompletedEisensteinCuspLegKind) (u : ℂ) (Y : ℝ) : ℂ :=
  d4BMCompletedEisensteinCuspConstantTerm kind u false Y + d4BMCompletedEisensteinCuspConstantTerm kind u true Y

def d4BMCompletedEisensteinCuspTailPart (kind : D4BMCompletedEisensteinCuspLegKind) (u : ℂ) (x Y : ℝ) : ℂ :=
  2 * match kind with
  | .scalar => d4BMCompletedEisensteinFullSignedZeroWord u u x Y
  | .raise => d4BMCompletedEisensteinFullSignedRaiseWord u u x Y
  | .lower => d4BMCompletedEisensteinFullSignedLowerWord u u x Y

def d4BMCompletedEisensteinCuspLeg (kind : D4BMCompletedEisensteinCuspLegKind) (u : ℂ) (x Y : ℝ) : ℂ :=
  d4BMCompletedEisensteinCuspConstantPart kind u Y + d4BMCompletedEisensteinCuspTailPart kind u x Y

theorem d4BM_tendsto_cpow_cuspTailPart (kind : D4BMCompletedEisensteinCuspLegKind) (u w : ℂ) (x : ℝ) :
    Tendsto (fun Y : ℝ => (Y : ℂ) ^ w * d4BMCompletedEisensteinCuspTailPart kind u x Y) atTop (𝓝 0) := by
  cases kind with
  | scalar =>
      have h := tendsto_d4BMCompletedEisensteinComplexPowerFullSignedZeroWord_atTop_zero
        u u w x
      have h2 := h.const_mul (2 : ℂ)
      simp only [mul_zero] at h2
      convert h2 using 1
      funext Y
      simp [d4BMCompletedEisensteinCuspTailPart, d4BMCompletedEisensteinComplexPowerFullSignedZeroWord]
      ring
  | raise =>
      have h := tendsto_d4BMCompletedEisensteinComplexPowerFullSignedRaiseWord_atTop_zero
        u u w x
      have h2 := h.const_mul (2 : ℂ)
      simp only [mul_zero] at h2
      convert h2 using 1
      funext Y
      simp [d4BMCompletedEisensteinCuspTailPart, d4BMCompletedEisensteinComplexPowerFullSignedRaiseWord]
      ring
  | lower =>
      have h := tendsto_d4BMCompletedEisensteinComplexPowerFullSignedLowerWord_atTop_zero
        u u w x
      have h2 := h.const_mul (2 : ℂ)
      simp only [mul_zero] at h2
      convert h2 using 1
      funext Y
      simp [d4BMCompletedEisensteinCuspTailPart, d4BMCompletedEisensteinComplexPowerFullSignedLowerWord]
      ring

theorem d4BM_tendsto_cpow_tail_mul_constantPart
    (tailKind constantKind : D4BMCompletedEisensteinCuspLegKind) (u v w : ℂ) (x : ℝ) :
    Tendsto (fun Y : ℝ =>
      (Y : ℂ) ^ w * d4BMCompletedEisensteinCuspTailPart tailKind u x Y * d4BMCompletedEisensteinCuspConstantPart constantKind v Y)
      atTop (𝓝 0) := by
  let wm := d4BMCompletedEisensteinCuspWeylExponent v false
  let wp := d4BMCompletedEisensteinCuspWeylExponent v true
  let cm := d4BMCompletedEisensteinCuspConstantCoefficient v false * d4BMCompletedEisensteinCuspConstantMaassFactor constantKind wm
  let cp := d4BMCompletedEisensteinCuspConstantCoefficient v true * d4BMCompletedEisensteinCuspConstantMaassFactor constantKind wp
  have hm := (d4BM_tendsto_cpow_cuspTailPart tailKind u (w + wm) x).const_mul cm
  have hp := (d4BM_tendsto_cpow_cuspTailPart tailKind u (w + wp) x).const_mul cp
  have h := hm.add hp
  simp only [mul_zero, add_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with Y hY
  have hYC : (Y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hY.ne'
  dsimp [d4BMCompletedEisensteinCuspConstantPart, d4BMCompletedEisensteinCuspConstantTerm, cm, cp, wm, wp]
  rw [Complex.cpow_add w (d4BMCompletedEisensteinCuspWeylExponent v false) hYC,
    Complex.cpow_add w (d4BMCompletedEisensteinCuspWeylExponent v true) hYC]
  ring

theorem d4BM_tendsto_cpow_tail_mul_twoConstantParts
    (tailKind firstKind secondKind : D4BMCompletedEisensteinCuspLegKind)
    (u v q w : ℂ) (x : ℝ) :
    Tendsto (fun Y : ℝ =>
      (Y : ℂ) ^ w * d4BMCompletedEisensteinCuspTailPart tailKind u x Y *
        d4BMCompletedEisensteinCuspConstantPart firstKind v Y * d4BMCompletedEisensteinCuspConstantPart secondKind q Y)
      atTop (𝓝 0) := by
  let v0 := d4BMCompletedEisensteinCuspWeylExponent v false
  let v1 := d4BMCompletedEisensteinCuspWeylExponent v true
  let q0 := d4BMCompletedEisensteinCuspWeylExponent q false
  let q1 := d4BMCompletedEisensteinCuspWeylExponent q true
  let c00 := d4BMCompletedEisensteinCuspConstantCoefficient v false * d4BMCompletedEisensteinCuspConstantMaassFactor firstKind v0 *
    (d4BMCompletedEisensteinCuspConstantCoefficient q false * d4BMCompletedEisensteinCuspConstantMaassFactor secondKind q0)
  let c01 := d4BMCompletedEisensteinCuspConstantCoefficient v false * d4BMCompletedEisensteinCuspConstantMaassFactor firstKind v0 *
    (d4BMCompletedEisensteinCuspConstantCoefficient q true * d4BMCompletedEisensteinCuspConstantMaassFactor secondKind q1)
  let c10 := d4BMCompletedEisensteinCuspConstantCoefficient v true * d4BMCompletedEisensteinCuspConstantMaassFactor firstKind v1 *
    (d4BMCompletedEisensteinCuspConstantCoefficient q false * d4BMCompletedEisensteinCuspConstantMaassFactor secondKind q0)
  let c11 := d4BMCompletedEisensteinCuspConstantCoefficient v true * d4BMCompletedEisensteinCuspConstantMaassFactor firstKind v1 *
    (d4BMCompletedEisensteinCuspConstantCoefficient q true * d4BMCompletedEisensteinCuspConstantMaassFactor secondKind q1)
  have h00 := (d4BM_tendsto_cpow_cuspTailPart tailKind u (w + v0 + q0) x).const_mul c00
  have h01 := (d4BM_tendsto_cpow_cuspTailPart tailKind u (w + v0 + q1) x).const_mul c01
  have h10 := (d4BM_tendsto_cpow_cuspTailPart tailKind u (w + v1 + q0) x).const_mul c10
  have h11 := (d4BM_tendsto_cpow_cuspTailPart tailKind u (w + v1 + q1) x).const_mul c11
  have h := ((h00.add h01).add h10).add h11
  simp only [mul_zero, add_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with Y hY
  have hYC : (Y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hY.ne'
  dsimp [d4BMCompletedEisensteinCuspConstantPart, d4BMCompletedEisensteinCuspConstantTerm, c00, c01, c10, c11, v0, v1, q0, q1]
  rw [Complex.cpow_add (w + d4BMCompletedEisensteinCuspWeylExponent v false) (d4BMCompletedEisensteinCuspWeylExponent q false) hYC,
    Complex.cpow_add (w + d4BMCompletedEisensteinCuspWeylExponent v false) (d4BMCompletedEisensteinCuspWeylExponent q true) hYC,
    Complex.cpow_add (w + d4BMCompletedEisensteinCuspWeylExponent v true) (d4BMCompletedEisensteinCuspWeylExponent q false) hYC,
    Complex.cpow_add (w + d4BMCompletedEisensteinCuspWeylExponent v true) (d4BMCompletedEisensteinCuspWeylExponent q true) hYC,
    Complex.cpow_add w (d4BMCompletedEisensteinCuspWeylExponent v false) hYC,
    Complex.cpow_add w (d4BMCompletedEisensteinCuspWeylExponent v true) hYC]
  ring

theorem d4BM_tendsto_cuspTailPart (kind : D4BMCompletedEisensteinCuspLegKind) (u : ℂ) (x : ℝ) :
    Tendsto (d4BMCompletedEisensteinCuspTailPart kind u x) atTop (𝓝 0) := by
  have h := d4BM_tendsto_cpow_cuspTailPart kind u 0 x
  simpa using h

def d4BMCompletedEisensteinBalancedFullBoundaryCurrent (u v : ℂ) (x Y : ℝ) : ℂ :=
  (Y : ℂ) ^ (-1 : ℂ) *
    d4BMCompletedEisensteinCuspLeg .raise u x Y * d4BMCompletedEisensteinCuspLeg .lower u x Y * d4BMCompletedEisensteinCuspLeg .scalar v x Y

def d4BMCompletedEisensteinBalancedConstantBoundaryCurrent (u v : ℂ) (Y : ℝ) : ℂ :=
  (Y : ℂ) ^ (-1 : ℂ) *
    d4BMCompletedEisensteinCuspConstantPart .raise u Y * d4BMCompletedEisensteinCuspConstantPart .lower u Y *
      d4BMCompletedEisensteinCuspConstantPart .scalar v Y

def d4BMCompletedEisensteinBalancedMixedBoundaryRemainder (u v : ℂ) (x Y : ℝ) : ℂ :=
  d4BMCompletedEisensteinBalancedFullBoundaryCurrent u v x Y - d4BMCompletedEisensteinBalancedConstantBoundaryCurrent u v Y

theorem d4BM_completedEisensteinBalanced_mixedSectorExpansion (u v : ℂ) (x Y : ℝ) :
    d4BMCompletedEisensteinBalancedMixedBoundaryRemainder u v x Y =
      (Y : ℂ) ^ (-1 : ℂ) *
        (d4BMCompletedEisensteinCuspTailPart .raise u x Y * d4BMCompletedEisensteinCuspConstantPart .lower u Y *
            d4BMCompletedEisensteinCuspConstantPart .scalar v Y +
          d4BMCompletedEisensteinCuspConstantPart .raise u Y * d4BMCompletedEisensteinCuspTailPart .lower u x Y *
            d4BMCompletedEisensteinCuspConstantPart .scalar v Y +
          d4BMCompletedEisensteinCuspConstantPart .raise u Y * d4BMCompletedEisensteinCuspConstantPart .lower u Y *
            d4BMCompletedEisensteinCuspTailPart .scalar v x Y +
          d4BMCompletedEisensteinCuspTailPart .raise u x Y * d4BMCompletedEisensteinCuspTailPart .lower u x Y *
            d4BMCompletedEisensteinCuspConstantPart .scalar v Y +
          d4BMCompletedEisensteinCuspTailPart .raise u x Y * d4BMCompletedEisensteinCuspConstantPart .lower u Y *
            d4BMCompletedEisensteinCuspTailPart .scalar v x Y +
          d4BMCompletedEisensteinCuspConstantPart .raise u Y * d4BMCompletedEisensteinCuspTailPart .lower u x Y *
            d4BMCompletedEisensteinCuspTailPart .scalar v x Y +
          d4BMCompletedEisensteinCuspTailPart .raise u x Y * d4BMCompletedEisensteinCuspTailPart .lower u x Y *
            d4BMCompletedEisensteinCuspTailPart .scalar v x Y) := by
  simp [d4BMCompletedEisensteinBalancedMixedBoundaryRemainder, d4BMCompletedEisensteinBalancedFullBoundaryCurrent,
    d4BMCompletedEisensteinBalancedConstantBoundaryCurrent, d4BMCompletedEisensteinCuspLeg]
  ring

theorem tendsto_d4BMCompletedEisensteinBalancedMixedBoundaryRemainder_atTop_zero (u v : ℂ) (x : ℝ) :
    Tendsto (d4BMCompletedEisensteinBalancedMixedBoundaryRemainder u v x) atTop (𝓝 0) := by
  have h1 := d4BM_tendsto_cpow_tail_mul_twoConstantParts
    .raise .lower .scalar u u v (-1) x
  have h2raw := d4BM_tendsto_cpow_tail_mul_twoConstantParts
    .lower .raise .scalar u u v (-1) x
  have h2 : Tendsto (fun Y : ℝ =>
      (Y : ℂ) ^ (-1 : ℂ) * d4BMCompletedEisensteinCuspConstantPart .raise u Y *
        d4BMCompletedEisensteinCuspTailPart .lower u x Y * d4BMCompletedEisensteinCuspConstantPart .scalar v Y) atTop (𝓝 0) := by
    apply h2raw.congr'
    exact Filter.Eventually.of_forall fun Y => by ring
  have h3raw := d4BM_tendsto_cpow_tail_mul_twoConstantParts
    .scalar .raise .lower v u u (-1) x
  have h3 : Tendsto (fun Y : ℝ =>
      (Y : ℂ) ^ (-1 : ℂ) * d4BMCompletedEisensteinCuspConstantPart .raise u Y *
        d4BMCompletedEisensteinCuspConstantPart .lower u Y * d4BMCompletedEisensteinCuspTailPart .scalar v x Y) atTop (𝓝 0) := by
    apply h3raw.congr'
    exact Filter.Eventually.of_forall fun Y => by ring
  have h4a := d4BM_tendsto_cpow_tail_mul_constantPart .raise .scalar u v (-1) x
  have h4b := d4BM_tendsto_cuspTailPart .lower u x
  have h4raw := h4a.mul h4b
  simp only [mul_zero] at h4raw
  have h4 : Tendsto (fun Y : ℝ =>
      (Y : ℂ) ^ (-1 : ℂ) * d4BMCompletedEisensteinCuspTailPart .raise u x Y *
        d4BMCompletedEisensteinCuspTailPart .lower u x Y * d4BMCompletedEisensteinCuspConstantPart .scalar v Y) atTop (𝓝 0) := by
    apply h4raw.congr'
    exact Filter.Eventually.of_forall fun Y => by ring
  have h5a := d4BM_tendsto_cpow_tail_mul_constantPart .raise .lower u u (-1) x
  have h5b := d4BM_tendsto_cuspTailPart .scalar v x
  have h5raw := h5a.mul h5b
  simp only [mul_zero] at h5raw
  have h5 : Tendsto (fun Y : ℝ =>
      (Y : ℂ) ^ (-1 : ℂ) * d4BMCompletedEisensteinCuspTailPart .raise u x Y *
        d4BMCompletedEisensteinCuspConstantPart .lower u Y * d4BMCompletedEisensteinCuspTailPart .scalar v x Y) atTop (𝓝 0) := by
    apply h5raw.congr'
    exact Filter.Eventually.of_forall fun Y => by ring
  have h6a := d4BM_tendsto_cpow_tail_mul_constantPart .lower .raise u u (-1) x
  have h6b := d4BM_tendsto_cuspTailPart .scalar v x
  have h6raw := h6a.mul h6b
  simp only [mul_zero] at h6raw
  have h6 : Tendsto (fun Y : ℝ =>
      (Y : ℂ) ^ (-1 : ℂ) * d4BMCompletedEisensteinCuspConstantPart .raise u Y *
        d4BMCompletedEisensteinCuspTailPart .lower u x Y * d4BMCompletedEisensteinCuspTailPart .scalar v x Y) atTop (𝓝 0) := by
    apply h6raw.congr'
    exact Filter.Eventually.of_forall fun Y => by ring
  have h7a := d4BM_tendsto_cpow_cuspTailPart .raise u (-1) x
  have h7b := d4BM_tendsto_cuspTailPart .lower u x
  have h7c := d4BM_tendsto_cuspTailPart .scalar v x
  have h7raw := (h7a.mul h7b).mul h7c
  simp only [mul_zero] at h7raw
  have h7 : Tendsto (fun Y : ℝ =>
      (Y : ℂ) ^ (-1 : ℂ) * d4BMCompletedEisensteinCuspTailPart .raise u x Y *
        d4BMCompletedEisensteinCuspTailPart .lower u x Y * d4BMCompletedEisensteinCuspTailPart .scalar v x Y) atTop (𝓝 0) := by
    apply h7raw.congr'
    exact Filter.Eventually.of_forall fun Y => by ring
  have hsum := (((((h1.add h2).add h3).add h4).add h5).add h6).add h7
  simp only [add_zero] at hsum
  apply hsum.congr'
  exact Filter.Eventually.of_forall fun Y => by
    rw [d4BM_completedEisensteinBalanced_mixedSectorExpansion]
    ring

def d4BMCompletedEisensteinBalancedConstantBoundaryCoefficient
    (u v : ℂ) (epsilonOne epsilonTwo epsilonThree : Bool) : ℂ :=
  d4BMCompletedEisensteinCuspConstantCoefficient u epsilonOne *
      d4BMCompletedEisensteinCuspConstantMaassFactor .raise (d4BMCompletedEisensteinCuspWeylExponent u epsilonOne) *
    (d4BMCompletedEisensteinCuspConstantCoefficient u epsilonTwo *
      d4BMCompletedEisensteinCuspConstantMaassFactor .lower (d4BMCompletedEisensteinCuspWeylExponent u epsilonTwo)) *
    d4BMCompletedEisensteinCuspConstantCoefficient v epsilonThree

def d4BMCompletedEisensteinBalancedConstantBoundaryFamily (u v : ℂ) :
    D4BMDiagonalEisensteinCuspAffineExponent →₀ ℂ :=
  d4BMDiagonalEisensteinCuspBoundaryFamily (d4BMCompletedEisensteinBalancedConstantBoundaryCoefficient u v)

theorem d4BM_completedEisensteinBalancedConstantBoundary_finitePart_zero (u v : ℂ) :
    d4BMCuspAnalyticFamilyFinitePart (d4BMCompletedEisensteinBalancedConstantBoundaryFamily u v) = 0 := by
  exact d4BMCuspAnalyticFamilyFinitePart_diagonalEisensteinBoundary_eq_zero
    (d4BMCompletedEisensteinBalancedConstantBoundaryCoefficient u v)

def d4BMSpecializeDiagonalCuspAffineExponent (u v : ℂ)
    (a : D4BMDiagonalEisensteinCuspAffineExponent) : ℂ :=
  (a 0 : ℂ) / 2 + (a 1 : ℂ) * u + (a 2 : ℂ) * v

theorem d4BM_diagonalCuspBoundaryExponent_specialization
    (u v : ℂ) (epsilonOne epsilonTwo epsilonThree : Bool) :
    d4BMSpecializeDiagonalCuspAffineExponent u v
        (d4BMDiagonalEisensteinCuspBoundaryExponent
          epsilonOne epsilonTwo epsilonThree) =
      -1 + d4BMCompletedEisensteinCuspWeylExponent u epsilonOne + d4BMCompletedEisensteinCuspWeylExponent u epsilonTwo +
        d4BMCompletedEisensteinCuspWeylExponent v epsilonThree := by
  simp [d4BMSpecializeDiagonalCuspAffineExponent, d4BMDiagonalEisensteinCuspBoundaryExponent,
    d4BMCompletedEisensteinCuspWeylExponent]
  ring

theorem d4BM_completedEisensteinBalanced_fullCuspBoundaryClosure (u v : ℂ) (x : ℝ) :
    d4BMCuspAnalyticFamilyFinitePart (d4BMCompletedEisensteinBalancedConstantBoundaryFamily u v) = 0 ∧
      Tendsto (d4BMCompletedEisensteinBalancedMixedBoundaryRemainder u v x) atTop (𝓝 0) :=
  ⟨d4BM_completedEisensteinBalancedConstantBoundary_finitePart_zero u v, tendsto_d4BMCompletedEisensteinBalancedMixedBoundaryRemainder_atTop_zero u v x⟩

end
end RHTower
