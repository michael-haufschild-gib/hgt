import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.TheCalibratedDepthBandsApproachTheTop

/-!
# Positive windows for reflection-symmetric blocks

Reflecting a positive depth across zero preserves its positive ordinate.
The reflected contribution is bounded by the coefficient mass at positive
heights, while the calibrated main contribution grows exponentially.
-/

open Complex Finset
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality

/-- A calibrated exponent together with its reflection across the imaginary axis. -/
def calibratedReflectedExponent {ι : Type*} (x : ℝ) (z : ι → ℂ) (p : ι × Bool) : ℂ :=
  if p.2 then (x : ℂ) + z p.1 else -conj ((x : ℂ) + z p.1)

/-- The reflected block is the sum of its positive- and negative-depth halves. -/
theorem splineExponentialBlock_reflected_eq {ι : Type*} [Fintype ι]
    (x : ℝ) (z : ι → ℂ) (t : ℝ) :
    splineExponentialBlock (calibratedReflectedExponent x z) t =
      splineExponentialBlock (fun i => (x : ℂ) + z i) t +
        splineExponentialBlock (fun i => -conj ((x : ℂ) + z i)) t := by
  classical
  unfold splineExponentialBlock
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, calibratedReflectedExponent, Bool.false_eq_true,
    ↓reduceIte, Finset.sum_add_distrib]
  ring

/-- Coefficient mass splits exactly between the two reflected halves. -/
theorem splineBlockWeight_reflected_eq {ι : Type*} [Fintype ι]
    (x : ℝ) (z : ι → ℂ) :
    splineBlockWeight (calibratedReflectedExponent x z) =
      splineBlockWeight (fun i => (x : ℂ) + z i) +
        splineBlockWeight (fun i => -conj ((x : ℂ) + z i)) := by
  classical
  unfold splineBlockWeight
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, calibratedReflectedExponent, Bool.false_eq_true,
    ↓reduceIte, Finset.sum_add_distrib]
  ring

/-- Reflection preserves ordinates, and both real parts lie below the upper depth bound. -/
theorem calibratedReflectedExponent_geometry {ι : Type*} (z : ι → ℂ)
    {x η D : ℝ} (hη : 0 ≤ η) (hx : η ≤ x) (hD : x + η ≤ D)
    (hz : ∀ i, |(z i).re| ≤ η) (p : ι × Bool) :
    (calibratedReflectedExponent x z p).im = (z p.1).im ∧
      |(calibratedReflectedExponent x z p).re| ≤ D := by
  have hi := abs_le.mp (hz p.1)
  have hlo : 0 ≤ x + (z p.1).re := by linarith only [hi.1, hx]
  have hhi : x + (z p.1).re ≤ D := by linarith only [hi.2, hD]
  rcases p with ⟨i, b⟩
  cases b
  · constructor
    · simp [calibratedReflectedExponent]
    · simpa [calibratedReflectedExponent, abs_of_nonneg hlo] using hhi
  · constructor
    · simp [calibratedReflectedExponent]
    · simpa [calibratedReflectedExponent, abs_of_nonneg hlo] using hhi

/-- The complete reflected block stays positive on the calibrated window, up to its small mass. -/
theorem two_re_reflected_calibrated_block_ge {ι : Type*} [Fintype ι]
    (z : ι → ℂ) {x η T R v : ℝ} (hη : 0 ≤ η) (hx : η ≤ x)
    (hz : ∀ i, |(z i).re| ≤ η) (ht : 0 ≤ T + v) (hv : |v| ≤ R)
    (hpos : ∀ a : ℝ, |a| ≤ R + 8 →
      (3 / 4 : ℝ) ≤ (∑ j, Complex.exp (((T + a : ℝ) : ℂ) * z j)).re) :
    (3 / 2 : ℝ) * Real.exp (x * (T + v - 8)) -
        splineBlockWeight (calibratedReflectedExponent x z) ≤
      2 * (splineExponentialBlock (calibratedReflectedExponent x z) (T + v)).re := by
  have hx0 : 0 ≤ x := hη.trans hx
  have hmain := splineExponentialBlock_re_ge_of_positive_window z hx0 hv hpos
  have hneg : ∀ i, (-conj ((x : ℂ) + z i)).re ≤ 0 := by
    intro i
    simp only [Complex.neg_re, Complex.conj_re, Complex.add_re, Complex.ofReal_re]
    have hi := (abs_le.mp (hz i)).1
    linarith only [hi, hx]
  have hreflect := abs_two_re_splineExponentialBlock_le
    (fun i => -conj ((x : ℂ) + z i)) ht hneg
  simp only [zero_mul, Real.exp_zero, mul_one] at hreflect
  have hweight : splineBlockWeight (fun i => -conj ((x : ℂ) + z i)) ≤
      splineBlockWeight (calibratedReflectedExponent x z) := by
    rw [splineBlockWeight_reflected_eq]
    exact le_add_of_nonneg_left (splineBlockWeight_nonneg _)
  have hlo := (abs_le.mp (hreflect.trans hweight)).1
  rw [splineExponentialBlock_reflected_eq, Complex.add_re]
  linarith only [hmain, hlo]

/-- Normalization at the upper depth leaves a uniformly bounded coefficient function. -/
theorem abs_normalized_spline_block_le {ι : Type*} [Fintype ι]
    (w : ι → ℂ) {D t : ℝ} (ht : 0 ≤ t) (hw : ∀ i, (w i).re ≤ D) :
    |Real.exp (-(D * t)) * (2 * (splineExponentialBlock w t).re)| ≤ splineBlockWeight w := by
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  have hh := mul_le_mul_of_nonneg_left (abs_two_re_splineExponentialBlock_le w ht hw)
    (Real.exp_pos (-(D * t))).le
  have he : Real.exp (-(D * t)) * (splineBlockWeight w * Real.exp (D * t)) =
      splineBlockWeight w := by
    rw [mul_left_comm, ← Real.exp_add]
    simp only [neg_add_cancel, Real.exp_zero, mul_one]
  rwa [he] at hh

end GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality
