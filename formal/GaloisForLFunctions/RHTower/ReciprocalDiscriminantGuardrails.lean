import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Reciprocal discriminant guardrails

This file formalizes four elementary reciprocal-coordinate facts used by the
zeta/RH route: a positive-real-part atom can have a negative bulk cross term;
the first two shifted minors of a nonreal conjugate pair are negative
imaginary-defect squares; an off-line FE quartet realizes the corresponding
seam-coordinate formulas; and only the true FE seam center folds pairs while
sending critical-line points to positive real atoms.
-/

namespace RHTower

noncomputable section

/-- The real discriminant cross term between `u + i v` and a real bulk atom `x`. -/
def discriminantCross (u v x : ℝ) : ℝ :=
  ((((u : ℂ) + v * Complex.I) * (((u : ℂ) + v * Complex.I) - x) ^ 2)).re

theorem discriminantCross_eq (u v x : ℝ) :
    discriminantCross u v x =
      x ^ 2 * u - 2 * x * u ^ 2 + 2 * x * v ^ 2 + u ^ 3 - 3 * u * v ^ 2 := by
  simp [discriminantCross, Complex.mul_re, pow_two]
  ring

theorem discriminantCross_self (u v : ℝ) :
    discriminantCross u v u = -u * v ^ 2 := by
  rw [discriminantCross_eq]
  ring

theorem discriminantCross_self_neg {u v : ℝ} (hu : 0 < u) (hv : v ≠ 0) :
    discriminantCross u v u < 0 := by
  rw [discriminantCross_self]
  have hv2 : 0 < v ^ 2 := sq_pos_of_ne_zero hv
  nlinarith [mul_pos hu hv2]

theorem discriminantCross_one_one : discriminantCross 1 1 1 = -1 := by
  norm_num [discriminantCross_self]

/-- Moments of a conjugate reciprocal pair `u ± i v`, each with real weight `mu`. -/
def reciprocalConjugatePairMoment (mu u v : ℝ) (k : ℕ) : ℝ :=
  2 * mu * (((u : ℂ) + v * Complex.I) ^ k).re

theorem reciprocalConjugatePair_det_zero (mu u v : ℝ) :
    reciprocalConjugatePairMoment mu u v 1 *
        reciprocalConjugatePairMoment mu u v 3 -
      reciprocalConjugatePairMoment mu u v 2 ^ 2 =
      -4 * mu ^ 2 * (u ^ 2 + v ^ 2) * v ^ 2 := by
  simp [reciprocalConjugatePairMoment, pow_succ, Complex.mul_re]
  ring

theorem reciprocalConjugatePair_det_one (mu u v : ℝ) :
    reciprocalConjugatePairMoment mu u v 2 *
        reciprocalConjugatePairMoment mu u v 4 -
      reciprocalConjugatePairMoment mu u v 3 ^ 2 =
      -4 * mu ^ 2 * (u ^ 2 + v ^ 2) ^ 2 * v ^ 2 := by
  simp [reciprocalConjugatePairMoment, pow_succ, Complex.mul_re]
  ring

theorem reciprocalConjugatePair_det_both_neg {mu u v : ℝ}
    (hmu : mu ≠ 0) (hv : v ≠ 0) :
    reciprocalConjugatePairMoment mu u v 1 *
          reciprocalConjugatePairMoment mu u v 3 -
        reciprocalConjugatePairMoment mu u v 2 ^ 2 < 0 ∧
      reciprocalConjugatePairMoment mu u v 2 *
          reciprocalConjugatePairMoment mu u v 4 -
        reciprocalConjugatePairMoment mu u v 3 ^ 2 < 0 := by
  rw [reciprocalConjugatePair_det_zero, reciprocalConjugatePair_det_one]
  have hmu2 : 0 < mu ^ 2 := sq_pos_of_ne_zero hmu
  have hv2 : 0 < v ^ 2 := sq_pos_of_ne_zero hv
  have hsum : 0 < u ^ 2 + v ^ 2 := by positivity
  have hprod0 : 0 < 4 * mu ^ 2 * (u ^ 2 + v ^ 2) * v ^ 2 := by positivity
  have hprod1 : 0 < 4 * mu ^ 2 * (u ^ 2 + v ^ 2) ^ 2 * v ^ 2 := by positivity
  constructor <;> nlinarith

/-- The reciprocal atom of the seam point `a + i gamma`. -/
def seamReciprocalAtom (a gamma : ℝ) : ℂ :=
  Complex.mk ((gamma ^ 2 - a ^ 2) / (a ^ 2 + gamma ^ 2) ^ 2)
    (2 * a * gamma / (a ^ 2 + gamma ^ 2) ^ 2)

theorem seamReciprocalAtom_im (a gamma : ℝ) :
    (seamReciprocalAtom a gamma).im =
      2 * a * gamma / (a ^ 2 + gamma ^ 2) ^ 2 := by
  rfl

theorem seamReciprocalAtom_normSq (a gamma : ℝ)
    (hden : a ^ 2 + gamma ^ 2 ≠ 0) :
    Complex.normSq (seamReciprocalAtom a gamma) =
      1 / (a ^ 2 + gamma ^ 2) ^ 2 := by
  simp [seamReciprocalAtom, Complex.normSq_apply]
  field_simp [hden]
  ring

/-- The coordinate formula is the actual reciprocal square of `a + i gamma`. -/
theorem seamReciprocalAtom_eq_neg_inv_sq (a gamma : ℝ)
    (hden : a ^ 2 + gamma ^ 2 ≠ 0) :
    seamReciprocalAtom a gamma = -((((a : ℂ) + gamma * Complex.I) ^ 2)⁻¹) := by
  apply Complex.ext <;>
    simp [seamReciprocalAtom, Complex.inv_re, Complex.inv_im,
      Complex.normSq_apply, pow_two, Complex.mul_re, Complex.mul_im] <;>
    field_simp [hden] <;>
    ring

theorem seamOfflineQuartet_det_zero (a gamma : ℝ)
    (hden : a ^ 2 + gamma ^ 2 ≠ 0) :
    reciprocalConjugatePairMoment 2 (seamReciprocalAtom a gamma).re
          (seamReciprocalAtom a gamma).im 1 *
        reciprocalConjugatePairMoment 2 (seamReciprocalAtom a gamma).re
          (seamReciprocalAtom a gamma).im 3 -
      reciprocalConjugatePairMoment 2 (seamReciprocalAtom a gamma).re
          (seamReciprocalAtom a gamma).im 2 ^ 2 =
      -64 * a ^ 2 * gamma ^ 2 / (a ^ 2 + gamma ^ 2) ^ 6 := by
  rw [reciprocalConjugatePair_det_zero]
  rw [show (seamReciprocalAtom a gamma).re ^ 2 +
      (seamReciprocalAtom a gamma).im ^ 2 =
      Complex.normSq (seamReciprocalAtom a gamma) by
      simp [Complex.normSq_apply, pow_two],
    seamReciprocalAtom_normSq a gamma hden, seamReciprocalAtom_im]
  field_simp [hden]
  ring

theorem seamOfflineQuartet_det_one (a gamma : ℝ)
    (hden : a ^ 2 + gamma ^ 2 ≠ 0) :
    reciprocalConjugatePairMoment 2 (seamReciprocalAtom a gamma).re
          (seamReciprocalAtom a gamma).im 2 *
        reciprocalConjugatePairMoment 2 (seamReciprocalAtom a gamma).re
          (seamReciprocalAtom a gamma).im 4 -
      reciprocalConjugatePairMoment 2 (seamReciprocalAtom a gamma).re
          (seamReciprocalAtom a gamma).im 3 ^ 2 =
      -64 * a ^ 2 * gamma ^ 2 / (a ^ 2 + gamma ^ 2) ^ 8 := by
  rw [reciprocalConjugatePair_det_one]
  rw [show (seamReciprocalAtom a gamma).re ^ 2 +
      (seamReciprocalAtom a gamma).im ^ 2 =
      Complex.normSq (seamReciprocalAtom a gamma) by
      simp [Complex.normSq_apply, pow_two],
    seamReciprocalAtom_normSq a gamma hden, seamReciprocalAtom_im]
  field_simp [hden]
  ring

theorem seamOfflineQuartet_det_both_neg {a gamma : ℝ}
    (ha : a ≠ 0) (hgamma : gamma ≠ 0) :
    reciprocalConjugatePairMoment 2 (seamReciprocalAtom a gamma).re
          (seamReciprocalAtom a gamma).im 1 *
        reciprocalConjugatePairMoment 2 (seamReciprocalAtom a gamma).re
          (seamReciprocalAtom a gamma).im 3 -
      reciprocalConjugatePairMoment 2 (seamReciprocalAtom a gamma).re
          (seamReciprocalAtom a gamma).im 2 ^ 2 < 0 ∧
    reciprocalConjugatePairMoment 2 (seamReciprocalAtom a gamma).re
          (seamReciprocalAtom a gamma).im 2 *
        reciprocalConjugatePairMoment 2 (seamReciprocalAtom a gamma).re
          (seamReciprocalAtom a gamma).im 4 -
      reciprocalConjugatePairMoment 2 (seamReciprocalAtom a gamma).re
          (seamReciprocalAtom a gamma).im 3 ^ 2 < 0 := by
  have hdenpos : 0 < a ^ 2 + gamma ^ 2 := by
    have ha2 : 0 < a ^ 2 := sq_pos_of_ne_zero ha
    positivity
  have hden : a ^ 2 + gamma ^ 2 ≠ 0 := ne_of_gt hdenpos
  rw [seamOfflineQuartet_det_zero a gamma hden,
    seamOfflineQuartet_det_one a gamma hden]
  have hnum : 0 < 64 * a ^ 2 * gamma ^ 2 := by positivity
  have hden6 : 0 < (a ^ 2 + gamma ^ 2) ^ 6 := by positivity
  have hden8 : 0 < (a ^ 2 + gamma ^ 2) ^ 8 := by positivity
  have hq6 : 0 < 64 * a ^ 2 * gamma ^ 2 / (a ^ 2 + gamma ^ 2) ^ 6 :=
    div_pos hnum hden6
  have hq8 : 0 < 64 * a ^ 2 * gamma ^ 2 / (a ^ 2 + gamma ^ 2) ^ 8 :=
    div_pos hnum hden8
  constructor
  · rw [show -64 * a ^ 2 * gamma ^ 2 / (a ^ 2 + gamma ^ 2) ^ 6 =
      -(64 * a ^ 2 * gamma ^ 2 / (a ^ 2 + gamma ^ 2) ^ 6) by ring]
    exact neg_lt_zero.mpr hq6
  · rw [show -64 * a ^ 2 * gamma ^ 2 / (a ^ 2 + gamma ^ 2) ^ 8 =
      -(64 * a ^ 2 * gamma ^ 2 / (a ^ 2 + gamma ^ 2) ^ 8) by ring]
    exact neg_lt_zero.mpr hq8

/-- The reciprocal-square atom formed after shifting the seam center by `eps`. -/
def offCenterReciprocalAtom (w : ℂ) (eps : ℝ) : ℂ :=
  -(((w - (eps : ℂ)) ^ 2)⁻¹)

/-- A nonzero FE pair folds to one reciprocal atom exactly at the true seam center. -/
theorem offCenterReciprocalAtom_fePair_eq_iff {w : ℂ} (hw : w ≠ 0) (eps : ℝ) :
    offCenterReciprocalAtom w eps = offCenterReciprocalAtom (-w) eps ↔ eps = 0 := by
  constructor
  · intro h
    have hinv : ((w - (eps : ℂ)) ^ 2)⁻¹ = (((-w) - (eps : ℂ)) ^ 2)⁻¹ :=
      neg_injective h
    have hsq : (w - (eps : ℂ)) ^ 2 = ((-w) - (eps : ℂ)) ^ 2 :=
      inv_injective hinv
    have hprod : (4 : ℂ) * w * (eps : ℂ) = 0 := by
      calc
        (4 : ℂ) * w * (eps : ℂ) = ((-w) - (eps : ℂ)) ^ 2 -
            (w - (eps : ℂ)) ^ 2 := by ring
        _ = 0 := by rw [← hsq]; ring
    rcases mul_eq_zero.mp hprod with h4w | heps
    · rcases mul_eq_zero.mp h4w with h4 | hw0
      · norm_num at h4
      · exact (hw hw0).elim
    · exact_mod_cast heps
  · rintro rfl
    simp [offCenterReciprocalAtom, pow_two]

theorem offCenterReciprocalAtom_criticalLine_eq_seam (eps gamma : ℝ)
    (hden : eps ^ 2 + gamma ^ 2 ≠ 0) :
    offCenterReciprocalAtom (gamma * Complex.I) eps =
      seamReciprocalAtom (-eps) gamma := by
  rw [seamReciprocalAtom_eq_neg_inv_sq (-eps) gamma (by simpa using hden)]
  unfold offCenterReciprocalAtom
  have hbase : gamma * Complex.I - (eps : ℂ) =
      ((-eps : ℝ) : ℂ) + gamma * Complex.I := by
    push_cast
    ring
  rw [hbase]

theorem offCenterReciprocalAtom_criticalLine_im (eps gamma : ℝ)
    (hgamma : gamma ≠ 0) :
    (offCenterReciprocalAtom (gamma * Complex.I) eps).im =
      -2 * eps * gamma /
        ((eps ^ 2 - gamma ^ 2) ^ 2 + 4 * eps ^ 2 * gamma ^ 2) := by
  have hdenpos : 0 < eps ^ 2 + gamma ^ 2 := by
    have hgamma2 : 0 < gamma ^ 2 := sq_pos_of_ne_zero hgamma
    positivity
  have hden : eps ^ 2 + gamma ^ 2 ≠ 0 := ne_of_gt hdenpos
  rw [offCenterReciprocalAtom_criticalLine_eq_seam eps gamma hden,
    seamReciprocalAtom_im]
  have hdeneq : (eps ^ 2 - gamma ^ 2) ^ 2 + 4 * eps ^ 2 * gamma ^ 2 =
      (eps ^ 2 + gamma ^ 2) ^ 2 := by ring
  rw [hdeneq]
  ring

theorem offCenterReciprocalAtom_criticalLine_im_ne_zero {eps gamma : ℝ}
    (heps : eps ≠ 0) (hgamma : gamma ≠ 0) :
    (offCenterReciprocalAtom (gamma * Complex.I) eps).im ≠ 0 := by
  rw [offCenterReciprocalAtom_criticalLine_im eps gamma hgamma]
  apply div_ne_zero
  · exact mul_ne_zero (mul_ne_zero (by norm_num) heps) hgamma
  · have hdenpos : 0 < eps ^ 2 + gamma ^ 2 := by
      have hgamma2 : 0 < gamma ^ 2 := sq_pos_of_ne_zero hgamma
      positivity
    have heq : (eps ^ 2 - gamma ^ 2) ^ 2 + 4 * eps ^ 2 * gamma ^ 2 =
        (eps ^ 2 + gamma ^ 2) ^ 2 := by ring
    rw [heq]
    positivity

/-- At the true seam center, every nonzero critical-line point maps to a positive real atom. -/
theorem offCenterReciprocalAtom_zero_criticalLine {gamma : ℝ} (hgamma : gamma ≠ 0) :
    offCenterReciprocalAtom (gamma * Complex.I) 0 =
        ((gamma ^ 2)⁻¹ : ℝ) ∧
      0 < (gamma ^ 2)⁻¹ := by
  constructor
  · have hgamma2 : gamma ^ 2 ≠ 0 := pow_ne_zero 2 hgamma
    have hden : (0 : ℝ) ^ 2 + gamma ^ 2 ≠ 0 := by simpa using hgamma2
    rw [offCenterReciprocalAtom_criticalLine_eq_seam 0 gamma hden]
    apply Complex.ext
    · simp [seamReciprocalAtom, ← Complex.ofReal_pow]
      field_simp [hgamma]
    · simp [seamReciprocalAtom, ← Complex.ofReal_pow]
  · exact inv_pos.mpr (sq_pos_of_ne_zero hgamma)

end

end RHTower
