import GaloisForLFunctions.HTGeometry.PoissonFatou

/-!
# Radial Poisson orientation chambers

The positive Poisson kernel is the group delay of a first-order all-pass section.  Comparing two
radial observations retains more information than either positive delay alone: for
`0 < inner < outer < 1`, the sign of their difference is exactly the sign of

`cos theta - (outer + inner) / (1 + outer * inner)`.

This is an observability statement, not an evolution law.  The radial pair is the clock; its value
difference reads an orientation chamber.  The same rational response is the real part of one local
Euler factor, providing the source-facing bridge used by the finite-Euler specialization.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The unique cosine threshold at which two radial Poisson observations agree. -/
def poissonRadialThreshold (outer inner : ℝ) : ℝ :=
  (outer + inner) / (1 + outer * inner)

/-- The disk rational response underlying one local Euler factor. -/
def diskEulerResponse (r theta : ℝ) : ℂ :=
  (r : ℂ) * Complex.exp (((-theta : ℝ) : ℂ) * Complex.I) /
    (1 - (r : ℂ) * Complex.exp (((-theta : ℝ) : ℂ) * Complex.I))

/-- The local Euler response is half the Poisson kernel minus its constant mode. -/
theorem diskEulerResponse_re {r theta : ℝ} (hr : |r| < 1) :
    (diskEulerResponse r theta).re = (poissonKer r theta - 1) / 2 := by
  have hden : 0 < 1 - 2 * r * Real.cos theta + r ^ (2 : ℕ) :=
    poissonKer_denom_pos hr theta
  rw [diskEulerResponse, Complex.exp_ofReal_mul_I]
  simp [Complex.div_re, Complex.normSq_apply, poissonKer, Real.cos_neg, Real.sin_neg,
    Complex.cos_ofReal_re, Complex.sin_ofReal_re]
  have hnormden :
      (1 - r * Real.cos theta) * (1 - r * Real.cos theta) +
          r * Real.sin theta * (r * Real.sin theta) =
        1 - 2 * r * Real.cos theta + r ^ (2 : ℕ) := by
    nlinarith [Real.sin_sq_add_cos_sq theta]
  rw [hnormden]
  have hden' : 1 - r * Real.cos theta * 2 + r ^ (2 : ℕ) ≠ 0 := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hden.ne'
  field_simp [hden']
  nlinarith [Real.sin_sq_add_cos_sq theta]

/-- Exact factorization of the radial Poisson difference into a positive scale and an
orientation-bearing affine cosine factor. -/
theorem poissonKer_sub_factor {outer inner theta : ℝ}
    (hinner0 : 0 < inner) (hord : inner < outer) (houter1 : outer < 1) :
    poissonKer outer theta - poissonKer inner theta =
      (2 * (outer - inner) /
        ((1 - 2 * outer * Real.cos theta + outer ^ (2 : ℕ)) *
          (1 - 2 * inner * Real.cos theta + inner ^ (2 : ℕ)))) *
        ((1 + outer * inner) * Real.cos theta - (outer + inner)) := by
  have houter0 : 0 < outer := lt_trans hinner0 hord
  have hdenOuter : 1 - 2 * outer * Real.cos theta + outer ^ (2 : ℕ) ≠ 0 :=
    (poissonKer_denom_pos (by simpa [abs_of_pos houter0] using houter1) theta).ne'
  have hdenInner : 1 - 2 * inner * Real.cos theta + inner ^ (2 : ℕ) ≠ 0 :=
    (poissonKer_denom_pos
      (by rw [abs_of_pos hinner0]; exact lt_trans hord houter1) theta).ne'
  rw [poissonKer, poissonKer]
  have hdenOuter' : 1 - outer * 2 * Real.cos theta + outer ^ (2 : ℕ) ≠ 0 := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hdenOuter
  have hdenInner' : 1 - 2 * Real.cos theta * inner + inner ^ (2 : ℕ) ≠ 0 := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hdenInner
  have hdenProd' :
      (1 - outer * 2 * Real.cos theta + outer ^ (2 : ℕ)) *
        (1 - 2 * Real.cos theta * inner + inner ^ (2 : ℕ)) ≠ 0 :=
    mul_ne_zero hdenOuter' hdenInner'
  field_simp [hdenOuter', hdenInner', hdenProd']
  ring

/-- The scale in the radial-difference factorization is strictly positive. -/
theorem poissonRadialScale_pos {outer inner theta : ℝ}
    (hinner0 : 0 < inner) (hord : inner < outer) (houter1 : outer < 1) :
    0 < 2 * (outer - inner) /
      ((1 - 2 * outer * Real.cos theta + outer ^ (2 : ℕ)) *
        (1 - 2 * inner * Real.cos theta + inner ^ (2 : ℕ))) := by
  have houter0 : 0 < outer := lt_trans hinner0 hord
  exact div_pos (mul_pos (by norm_num) (sub_pos.mpr hord))
    (mul_pos
      (poissonKer_denom_pos (by simpa [abs_of_pos houter0] using houter1) theta)
      (poissonKer_denom_pos
        (by rw [abs_of_pos hinner0]; exact lt_trans hord houter1) theta))

/-- The radial threshold is positive. -/
theorem poissonRadialThreshold_pos {outer inner : ℝ}
    (hinner0 : 0 < inner) (hord : inner < outer) :
    0 < poissonRadialThreshold outer inner := by
  unfold poissonRadialThreshold
  exact div_pos (add_pos (lt_trans hinner0 hord) hinner0)
    (by nlinarith [mul_pos (lt_trans hinner0 hord) hinner0])

/-- The radial threshold lies strictly below one for two disk radii. -/
theorem poissonRadialThreshold_lt_one {outer inner : ℝ}
    (hinner0 : 0 < inner) (hord : inner < outer) (houter1 : outer < 1) :
    poissonRadialThreshold outer inner < 1 := by
  have hinner1 : inner < 1 := lt_trans hord houter1
  have hprod : 0 < (1 - outer) * (1 - inner) :=
    mul_pos (sub_pos.mpr houter1) (sub_pos.mpr hinner1)
  have hden : 0 < 1 + outer * inner := by
    nlinarith [mul_pos (lt_trans hinner0 hord) hinner0]
  rw [poissonRadialThreshold, div_lt_one hden]
  nlinarith

/-- Complete positive chamber for a radial Poisson difference. -/
theorem poissonKer_sub_pos_iff {outer inner theta : ℝ}
    (hinner0 : 0 < inner) (hord : inner < outer) (houter1 : outer < 1) :
    0 < poissonKer outer theta - poissonKer inner theta ↔
      poissonRadialThreshold outer inner < Real.cos theta := by
  rw [poissonKer_sub_factor hinner0 hord houter1]
  have hscale := poissonRadialScale_pos hinner0 hord houter1 (theta := theta)
  rw [mul_pos_iff_of_pos_left hscale]
  have hden : 0 < 1 + outer * inner := by
    nlinarith [mul_pos (lt_trans hinner0 hord) hinner0]
  rw [poissonRadialThreshold, div_lt_iff₀ hden]
  constructor <;> intro h <;> nlinarith

/-- Exact boundary of the radial Poisson orientation chambers. -/
theorem poissonKer_sub_eq_zero_iff {outer inner theta : ℝ}
    (hinner0 : 0 < inner) (hord : inner < outer) (houter1 : outer < 1) :
    poissonKer outer theta - poissonKer inner theta = 0 ↔
      Real.cos theta = poissonRadialThreshold outer inner := by
  rw [poissonKer_sub_factor hinner0 hord houter1]
  have hscale := poissonRadialScale_pos hinner0 hord houter1 (theta := theta)
  rw [mul_eq_zero]
  simp only [ne_of_gt hscale, false_or]
  have hden : 0 < 1 + outer * inner := by
    nlinarith [mul_pos (lt_trans hinner0 hord) hinner0]
  rw [poissonRadialThreshold, eq_div_iff hden.ne']
  constructor <;> intro h <;> nlinarith

/-- Complete negative chamber for a radial Poisson difference. -/
theorem poissonKer_sub_neg_iff {outer inner theta : ℝ}
    (hinner0 : 0 < inner) (hord : inner < outer) (houter1 : outer < 1) :
    poissonKer outer theta - poissonKer inner theta < 0 ↔
      Real.cos theta < poissonRadialThreshold outer inner := by
  rw [poissonKer_sub_factor hinner0 hord houter1]
  have hscale := poissonRadialScale_pos hinner0 hord houter1 (theta := theta)
  rw [mul_neg_iff]
  simp only [hscale, true_and, lt_asymm hscale, false_and, or_false]
  have hden : 0 < 1 + outer * inner := by
    nlinarith [mul_pos (lt_trans hinner0 hord) hinner0]
  rw [poissonRadialThreshold, lt_div_iff₀ hden]
  constructor <;> intro h <;> nlinarith

/-- Every nontrivial radial pair has a strict positive orientation witness at phase zero. -/
theorem poissonKer_sub_pos_at_zero {outer inner : ℝ}
    (hinner0 : 0 < inner) (hord : inner < outer) (houter1 : outer < 1) :
    0 < poissonKer outer 0 - poissonKer inner 0 := by
  rw [poissonKer_sub_pos_iff hinner0 hord houter1, Real.cos_zero]
  exact poissonRadialThreshold_lt_one hinner0 hord houter1

/-- Every nontrivial radial pair has a strict negative orientation witness at phase pi. -/
theorem poissonKer_sub_neg_at_pi {outer inner : ℝ}
    (hinner0 : 0 < inner) (hord : inner < outer) (houter1 : outer < 1) :
    poissonKer outer Real.pi - poissonKer inner Real.pi < 0 := by
  rw [poissonKer_sub_neg_iff hinner0 hord houter1, Real.cos_pi]
  have hpos := poissonRadialThreshold_pos hinner0 hord
  linarith

end

end GaloisForLFunctions.HTGeometry
