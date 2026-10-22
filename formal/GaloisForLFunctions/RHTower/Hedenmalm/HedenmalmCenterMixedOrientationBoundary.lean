import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmHankelKreinChamber
import GaloisForLFunctions.RHTower.XiHedenmalmMomentOrientationBoundary

/-!
# Exact Hedenmalm center-mixed orientation boundary

The pointed moment module reconstructs the Hedenmalm Bezoutian but does not orient it.  This file
identifies its missing sign with the Fourier sign of the actual center-mixed theta density, without
assuming either sign.  On the centered upper half-strip, the Bezoutian diagonal is the split
Hankel--Krein current divided by the positive factor `2a`.  The Fourier transform of the canonical
autocorrelation tangent is exactly the same current.  Consequently, nonnegativity of that concrete
Fourier transform throughout the critical aperture is equivalent to RH.

This is an unconditional equivalence and normalization theorem, not a positivity theorem.
-/

open Complex Real
open scoped FourierTransform

noncomputable section

namespace RHTower

/-- On the upper centered line of aperture `a`, the Hedenmalm Bezoutian diagonal is exactly the
theta-orbit Krein current divided by `2a`. -/
theorem xiHedenmalmBezoutian_upper_conj_eq_krein_div
    {a : ℝ} (ha : 0 < a) (b : ℝ) :
    xiHedenmalmBezoutian
        ((b : ℂ) + (a : ℂ) * I)
        ((b : ℂ) - (a : ℂ) * I) =
      ((hedenmalmHankelKreinForm
        (thetaXiHankelOrbitValuePlus a b)
        (thetaXiHankelOrbitTangentPlus a b)
        (thetaXiHankelOrbitValueMinus a b)
        (thetaXiHankelOrbitTangentMinus a b) : ℝ) : ℂ) / (2 * a) := by
  have hne : (b : ℂ) - (a : ℂ) * I ≠ (b : ℂ) + (a : ℂ) * I := by
    intro h
    have him := congrArg Complex.im h
    simp at him
    linarith
  rw [xiHedenmalmBezoutian_eq_div hne,
    thetaXiHankelOrbit_kreinForm_eq]
  rw [show XiC ((b : ℂ) + (a : ℂ) * I) =
      thetaXiHankelOrbitValueMinus a b by rfl,
    show XiC ((b : ℂ) - (a : ℂ) * I) =
      thetaXiHankelOrbitValuePlus a b by rfl]
  rw [show deriv XiC ((b : ℂ) + (a : ℂ) * I) =
      I * thetaXiHankelOrbitTangentMinus a b by
        simp [thetaXiHankelOrbitTangentMinus, ← mul_assoc, I_mul_I],
    show deriv XiC ((b : ℂ) - (a : ℂ) * I) =
      I * thetaXiHankelOrbitTangentPlus a b by
        simp [thetaXiHankelOrbitTangentPlus, ← mul_assoc, I_mul_I]]
  rw [thetaXiHankelOrbitValueMinus_eq_conj,
    thetaXiHankelOrbitTangentMinus_eq_neg_conj]
  let u := thetaXiHankelOrbitValuePlus a b
  let v := thetaXiHankelOrbitTangentPlus a b
  have hconjMul :
      (starRingEnd ℂ) ((starRingEnd ℂ) u * v) =
        (starRingEnd ℂ) v * u := by
    rw [map_mul, starRingEnd_self_apply]
    ring
  have hnum :
      I * (-((starRingEnd ℂ) v)) * u -
          (starRingEnd ℂ) u * (I * v) =
        -I * (((2 * (((starRingEnd ℂ) u * v).re) : ℝ) : ℂ)) := by
    calc
      I * (-((starRingEnd ℂ) v)) * u -
          (starRingEnd ℂ) u * (I * v) =
          -I * (((starRingEnd ℂ) u * v) +
            (starRingEnd ℂ) ((starRingEnd ℂ) u * v)) := by
              rw [hconjMul]
              ring
      _ = -I * (((2 * (((starRingEnd ℂ) u * v).re) : ℝ) : ℂ)) := by
        rw [Complex.add_conj]
  change
    (I * (-((starRingEnd ℂ) v)) * u -
        (starRingEnd ℂ) u * (I * v)) /
        ((b : ℂ) - (a : ℂ) * I - ((b : ℂ) + (a : ℂ) * I)) =
      (((2 * (((starRingEnd ℂ) u * v).re) : ℝ) : ℂ)) / (2 * a)
  rw [hnum, show (b : ℂ) - (a : ℂ) * I - ((b : ℂ) + (a : ℂ) * I) =
      -(2 * (a : ℂ) * I) by ring]
  have haC : (a : ℂ) ≠ 0 := ofReal_ne_zero.mpr ha.ne'
  have hden : -(2 * (a : ℂ) * I) ≠ 0 :=
    neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero (by norm_num) haC) I_ne_zero)
  have htwoa : (2 * (a : ℂ)) ≠ 0 :=
    mul_ne_zero (by norm_num) haC
  field_simp [hden, htwoa]

/-- Real form of the exact upper-diagonal normalization. -/
theorem xiHedenmalmBezoutian_upper_conj_re_eq_krein_div
    {a : ℝ} (ha : 0 < a) (b : ℝ) :
    (xiHedenmalmBezoutian
        ((b : ℂ) + (a : ℂ) * I)
        ((b : ℂ) - (a : ℂ) * I)).re =
      hedenmalmHankelKreinForm
        (thetaXiHankelOrbitValuePlus a b)
        (thetaXiHankelOrbitTangentPlus a b)
        (thetaXiHankelOrbitValueMinus a b)
        (thetaXiHankelOrbitTangentMinus a b) / (2 * a) := by
  rw [xiHedenmalmBezoutian_upper_conj_eq_krein_div ha]
  rw [Complex.div_re]
  simp [Complex.normSq_apply]
  field_simp [ha.ne']

/-- At every regular critical-aperture point, the Bezoutian reconstructed from the pointed moment
germ is the same normalized theta-orbit current. -/
theorem xiHedenmalmPointedMomentBezoutian_upper_conj_eq_krein_div
    {a : ℝ} (ha : 0 < a) (hahalf : a < 1 / 2) (b : ℝ)
    (hzeta : riemannZeta
      ((1 : ℂ) / 2 + ((b : ℂ) + (a : ℂ) * I) * I) ≠ 0) :
    xiHedenmalmPointedMomentBezoutian
        ((b : ℂ) + (a : ℂ) * I)
        ((b : ℂ) - (a : ℂ) * I) =
      ((hedenmalmHankelKreinForm
        (thetaXiHankelOrbitValuePlus a b)
        (thetaXiHankelOrbitTangentPlus a b)
        (thetaXiHankelOrbitValueMinus a b)
        (thetaXiHankelOrbitTangentMinus a b) : ℝ) : ℂ) / (2 * a) := by
  let z : ℂ := (b : ℂ) + (a : ℂ) * I
  have hzIm : z.im = a := by simp [z]
  have hcz : (starRingEnd ℂ) z = (b : ℂ) - (a : ℂ) * I := by
    apply Complex.ext <;> simp [z]
  have hpointed :=
    xiHedenmalmPointedMomentBezoutian_conj_eq_normSq_mul_sourceDiagonal
      (z := z) (by simpa only [hzIm] using ha)
  have hactual := xiHedenmalmBezoutian_conj_eq_normSq_mul_sourceDiagonal
    (z := z) (by simpa only [hzIm] using ha)
      (by simpa only [hzIm] using hahalf) hzeta
  have heq : xiHedenmalmPointedMomentBezoutian z ((starRingEnd ℂ) z) =
      xiHedenmalmBezoutian z ((starRingEnd ℂ) z) := hpointed.trans hactual.symm
  rw [hcz] at heq
  rw [show z = (b : ℂ) + (a : ℂ) * I by rfl] at heq
  rw [heq]
  exact xiHedenmalmBezoutian_upper_conj_eq_krein_div ha b

/-- The actual theta/Xi orbit remains in the nonnegative chamber throughout the critical
aperture. -/
def ThetaXiHankelOrbitNonnegative : Prop :=
  ∀ a : ℝ, 0 < a → a < 1 / 2 → ∀ b : ℝ,
    0 ≤ hedenmalmHankelKreinForm
      (thetaXiHankelOrbitValuePlus a b)
      (thetaXiHankelOrbitTangentPlus a b)
      (thetaXiHankelOrbitValueMinus a b)
      (thetaXiHankelOrbitTangentMinus a b)

/-- Exact endpoint of the theta-orbit chamber route: global nonnegative-chamber avoidance is
equivalent to RH. -/
theorem thetaXiHankelOrbitNonnegative_iff_riemannHypothesis :
    ThetaXiHankelOrbitNonnegative ↔ RiemannHypothesis := by
  constructor
  · intro horbit
    apply xiHedenmalmUpperHermitianDiagonalNonnegative_iff_riemannHypothesis.mp
    intro z hzpos hzhalf _hzeta
    let a : ℝ := z.im
    let b : ℝ := z.re
    have hz : (b : ℂ) + (a : ℂ) * I = z := by
      apply Complex.ext <;> simp [a, b]
    have hcz : (b : ℂ) - (a : ℂ) * I = (starRingEnd ℂ) z := by
      apply Complex.ext <;> simp [a, b]
    have ha0 : 0 < a := by exact hzpos
    have hahalf : a < 1 / 2 := by exact hzhalf
    have hcurrent := horbit a ha0 hahalf b
    have hEq := xiHedenmalmBezoutian_upper_conj_re_eq_krein_div ha0 b
    rw [hz, hcz] at hEq
    rw [hEq]
    exact div_nonneg hcurrent (mul_nonneg (by norm_num) hzpos.le)
  · intro hRH a ha0 hahalf b
    have hgate : XiHedenmalmUpperHermitianDiagonalNonnegative :=
      xiHedenmalmUpperHermitianDiagonalNonnegative_iff_riemannHypothesis.mpr hRH
    let z : ℂ := (b : ℂ) + (a : ℂ) * I
    have hzIm : z.im = a := by simp [z]
    have hspos : 0 < ((1 : ℂ) / 2 + z * I).re := by
      simp [z, mul_re]
      linarith
    have hs1 : (1 : ℂ) / 2 + z * I ≠ 1 := by
      intro hs
      have hre := congrArg Complex.re hs
      simp [z, mul_re] at hre
      linarith
    have hright : (1 : ℂ) / 2 + (starRingEnd ℂ) z * I ∈ rightHalf := by
      rw [mem_rightHalf]
      simp [z, mul_re]
      linarith
    have hXiConj : XiC ((starRingEnd ℂ) z) ≠ 0 := by
      rw [XiC]
      exact rh_iff_xi_ne_zero_right.mp hRH _ hright
    have hXi : XiC z ≠ 0 := by
      intro hz0
      apply hXiConj
      rw [xiHedenmalm_XiC_conj, hz0]
      simp
    have hzeta : riemannZeta ((1 : ℂ) / 2 + z * I) ≠ 0 := by
      intro hzeta0
      apply hXi
      rw [XiC]
      exact (xi_eq_zero_iff hspos hs1).mpr hzeta0
    have hB := hgate z (by simpa only [hzIm] using ha0)
      (by simpa only [hzIm] using hahalf) hzeta
    have hEq := xiHedenmalmBezoutian_upper_conj_re_eq_krein_div ha0 b
    have hz : (b : ℂ) + (a : ℂ) * I = z := rfl
    have hcz : (b : ℂ) - (a : ℂ) * I = (starRingEnd ℂ) z := by
      apply Complex.ext <;> simp [z]
    rw [hz, hcz] at hEq
    rw [hEq] at hB
    have hdenpos : 0 < 2 * a := mul_pos (by norm_num) ha0
    have hmul := mul_nonneg hB hdenpos.le
    rw [div_mul_cancel₀ _ hdenpos.ne'] at hmul
    exact hmul

/-- Fourier nonnegativity of the actual center-mixed theta density, expressed through its
canonical autocorrelation tangent. -/
def ThetaCuspCenterMixedFourierNonnegative : Prop :=
  ∀ (a : ℝ) (ha : |a| < 1), 0 < a → a < 1 / 2 → ∀ b : ℝ,
    0 ≤ (FourierTransform.fourier
      (thetaCuspHorizontalAutocorrelationTangent a ha)
      (b / (2 * Real.pi))).re

/-- The center-mixed Fourier sign and the theta-orbit Krein-chamber sign are exactly the same
condition. -/
theorem thetaCuspCenterMixedFourierNonnegative_iff_thetaXiHankelOrbit :
    ThetaCuspCenterMixedFourierNonnegative ↔
      ThetaXiHankelOrbitNonnegative := by
  constructor
  · intro hfourier a ha0 hahalf b
    have ha : |a| < 1 := by
      rw [abs_of_pos ha0]
      linarith
    have h := hfourier a ha ha0 hahalf b
    rw [fourier_thetaCuspHorizontalAutocorrelationTangent_scaled_eq_kreinForm ha b] at h
    simpa using h
  · intro horbit a ha ha0 hahalf b
    have h := horbit a ha0 hahalf b
    rw [fourier_thetaCuspHorizontalAutocorrelationTangent_scaled_eq_kreinForm ha b]
    simpa using h

/-- Exact source-side endpoint: nonnegativity of the concrete center-mixed theta Fourier current
throughout the critical aperture is equivalent to RH.  No sign is proved here. -/
theorem thetaCuspCenterMixedFourierNonnegative_iff_riemannHypothesis :
    ThetaCuspCenterMixedFourierNonnegative ↔ RiemannHypothesis :=
  thetaCuspCenterMixedFourierNonnegative_iff_thetaXiHankelOrbit.trans
    thetaXiHankelOrbitNonnegative_iff_riemannHypothesis

end RHTower
