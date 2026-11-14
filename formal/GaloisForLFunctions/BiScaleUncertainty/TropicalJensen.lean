import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Tropical Jensen identities for finite signed splines

The slope jump of `w |x-t|` is `2w`. Its integrated root or pole count on
`[-r,r]` is therefore the corresponding signed part of `w` times
`max 0 (|r|-|t|)`. Summing the elementary absolute-value identity proves
Jensen reciprocity without analytic premises.

These are the continuous finite-divisor instances of Cao–Korhonen–Wang,
*Nevanlinna theory for generalized tropical meromorphic functions*,
Theorem 3.3. Signed scaling also corrects Lemma 2.5: a negative scalar
exchanges positive and negative parts.
-/

namespace GaloisForLFunctions.BiScaleUncertainty.TropicalJensen
open scoped BigOperators
noncomputable section

/-- Two-point tropical proximity. -/
def proximity (r : ℝ) (f : ℝ → ℝ) : ℝ := (max 0 (f r) + max 0 (f (-r))) / 2

private theorem positive_sub_negative (x : ℝ) : max 0 x - max 0 (-x) = x := by
  rcases le_total 0 x with h | h
  · rw [max_eq_right h, max_eq_left (neg_nonpos.mpr h)]
    ring
  · rw [max_eq_left h, max_eq_right (neg_nonneg.mpr h)]
    ring

/-- Positive and negative proximity recover the signed boundary average. -/
theorem proximity_sub_neg (r : ℝ) (f : ℝ → ℝ) :
    proximity r f - proximity r (fun x => -f x) = (f r + f (-r)) / 2 := by
  unfold proximity
  linarith only [positive_sub_negative (f r), positive_sub_negative (f (-r))]

private theorem positive_mul (a b : ℝ) :
    max 0 (a * b) = max 0 a * max 0 b + max 0 (-a) * max 0 (-b) := by
  rcases le_total 0 a with ha | ha <;> rcases le_total 0 b with hb | hb
  · rw [max_eq_right ha, max_eq_right hb, max_eq_left (neg_nonpos.mpr ha),
      max_eq_left (neg_nonpos.mpr hb), max_eq_right (mul_nonneg ha hb)]
    ring
  · rw [max_eq_right ha, max_eq_left hb, max_eq_left (neg_nonpos.mpr ha),
      max_eq_right (neg_nonneg.mpr hb), max_eq_left (mul_nonpos_of_nonneg_of_nonpos ha hb)]
    ring
  · rw [max_eq_left ha, max_eq_right hb, max_eq_right (neg_nonneg.mpr ha),
      max_eq_left (neg_nonpos.mpr hb), max_eq_left (mul_nonpos_of_nonpos_of_nonneg ha hb)]
    ring
  · rw [max_eq_left ha, max_eq_left hb, max_eq_right (neg_nonneg.mpr ha),
      max_eq_right (neg_nonneg.mpr hb), max_eq_right (mul_nonneg_of_nonpos_of_nonpos ha hb)]
    ring

/-- Exact homogeneity for every real scalar, including negative scalars. -/
theorem proximity_signed_scaling (a r : ℝ) (f : ℝ → ℝ) :
    proximity r (fun x => a * f x) =
      max 0 a * proximity r f + max 0 (-a) * proximity r (fun x => -f x) := by
  simp only [proximity, positive_mul]
  ring

/-- Unrestricted signed homogeneity already fails on the constant function one. -/
theorem proximity_not_signed_homogeneous (r : ℝ) :
    proximity r (fun _ => (-1 : ℝ)) ≠ -proximity r (fun _ => (1 : ℝ)) := by
  simp [proximity]

/-- The exact error in taking a tropical maximum is nonnegative and bounded by target proximity. -/
theorem proximity_max_bounds (r : ℝ) (f g : ℝ → ℝ) :
    0 ≤ proximity r (fun x => max (f x) (g x)) - proximity r f ∧
      proximity r (fun x => max (f x) (g x)) - proximity r f ≤ proximity r g := by
  have point (x : ℝ) :
      max 0 (f x) ≤ max 0 (max (f x) (g x)) ∧
      max 0 (max (f x) (g x)) ≤ max 0 (f x) + max 0 (g x) := by
    constructor
    · exact max_le_max_left 0 (le_max_left _ _)
    · exact max_le (add_nonneg (le_max_left _ _) (le_max_left _ _))
        (max_le ((le_max_right _ _).trans (le_add_of_nonneg_right (le_max_left _ _)))
          ((le_max_right _ _).trans (le_add_of_nonneg_left (le_max_left _ _))))
  unfold proximity
  constructor <;> linarith only [(point r).1, (point r).2, (point (-r)).1, (point (-r)).2]

/-- The integrated slope-jump kernel. -/
def tentCount (r t : ℝ) : ℝ := max 0 (|r| - |t|)

theorem absolute_jensen (r t : ℝ) :
    (|r - t| + |-r - t|) / 2 - |t| = tentCount r t := by
  unfold tentCount
  rw [show -r - t = -(r + t) by ring, abs_neg]
  simp only [abs_def, max_def]
  split_ifs <;> linarith

/-- A continuous finite piecewise-linear function with prescribed slope jumps. -/
def spline (s : Finset ℝ) (w : ℝ → ℝ) (a b x : ℝ) : ℝ :=
  a * x + b + ∑ t ∈ s, w t * |x - t|

/-- Integrated pole multiplicities; each negative weight contributes slope jump `2w`. -/
def poleCount (s : Finset ℝ) (w : ℝ → ℝ) (r : ℝ) : ℝ :=
  ∑ t ∈ s, max 0 (-w t) * tentCount r t

/-- Tropical characteristic of a finite spline. -/
def characteristic (s : Finset ℝ) (w : ℝ → ℝ) (a b r : ℝ) : ℝ :=
  proximity r (spline s w a b) + poleCount s w r

/-- Finite-divisor Jensen formula, with the affine part cancelling exactly. -/
theorem spline_jensen (s : Finset ℝ) (w : ℝ → ℝ) (a b r : ℝ) :
    (spline s w a b r + spline s w a b (-r)) / 2 - spline s w a b 0 =
      ∑ t ∈ s, w t * tentCount r t := by
  have hsum : (∑ t ∈ s, w t * |r - t|) + (∑ t ∈ s, w t * |-r - t|) -
      2 * (∑ t ∈ s, w t * |t|) = 2 * ∑ t ∈ s, w t * tentCount r t := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    linear_combination 2 * w t * absolute_jensen r t
  simp only [spline, mul_zero, zero_add, zero_sub, abs_neg]
  linarith only [hsum]

theorem spline_neg (s : Finset ℝ) (w : ℝ → ℝ) (a b x : ℝ) :
    spline s (fun t => -w t) (-a) (-b) x = -spline s w a b x := by
  simp only [spline, neg_mul, Finset.sum_neg_distrib]
  ring

/-- Jensen reciprocity: negation exchanges roots and poles, leaving the value at the centre. -/
theorem characteristic_neg (s : Finset ℝ) (w : ℝ → ℝ) (a b r : ℝ) :
    characteristic s w a b r - characteristic s (fun t => -w t) (-a) (-b) r =
      spline s w a b 0 := by
  have hcount : poleCount s (fun t => -w t) r - poleCount s w r =
      ∑ t ∈ s, w t * tentCount r t := by
    simp only [poleCount, neg_neg, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro t _
    rw [← sub_mul, positive_sub_negative]
  have hn : spline s (fun t => -w t) (-a) (-b) = fun x => -spline s w a b x :=
    funext (spline_neg s w a b)
  have hp := proximity_sub_neg r (spline s w a b)
  unfold characteristic
  rw [hn]
  linarith only [hp, hcount, spline_jensen s w a b r]

end
end GaloisForLFunctions.BiScaleUncertainty.TropicalJensen
