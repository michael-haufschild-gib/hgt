import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# The two-extension trace difference is a gap-occupancy moment

Two interlacing spectra compactified by `x(t) = 1/(1+t²)` cut the unit interval into disjoint gaps
`(x(q_k), x(p_k))`.  The smoothing weight `f_j(t) = (1+t²)^{-(j+1)}` is exactly `x(t)^{j+1}`, so the
difference of its two spectral sums telescopes across each gap, and the fundamental theorem of
calculus turns that telescope into `(j+1)` times the `j`-th moment of the occupancy measure
`1_{E} dx`.  Together with the forced odd eigenvalue at the origin, which contributes `x(0)^{j+1}
= 1`, this is the exact trace identity of the smoothing hierarchy.

Nothing here is asymptotic: the identity holds at every finite aperture, for every `j`, and needs
no trace-class or spectral-shift theory — only that the gaps are disjoint.
-/

open MeasureTheory Set intervalIntegral

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- The compactification of a spectral point. -/
def spectralCompactify (t : ℝ) : ℝ := 1 / (1 + t ^ 2)

theorem spectralCompactify_pos (t : ℝ) : 0 < spectralCompactify t := by
  rw [spectralCompactify]
  positivity

theorem spectralCompactify_le_one (t : ℝ) : spectralCompactify t ≤ 1 := by
  rw [spectralCompactify, div_le_one (by positivity)]
  nlinarith [sq_nonneg t]

theorem spectralCompactify_zero : spectralCompactify 0 = 1 := by
  rw [spectralCompactify]
  norm_num

/-- The smoothing weight `f_j(t) = (1+t²)^{-(j+1)}` is the compactified variable to the power
`j+1`. -/
theorem smoothingWeight_eq (j : ℕ) (t : ℝ) :
    (1 + t ^ 2) ^ (-(j + 1 : ℝ)) = spectralCompactify t ^ (j + 1) := by
  have hpos : (0 : ℝ) < 1 + t ^ 2 := by positivity
  rw [spectralCompactify, div_pow, one_pow, Real.rpow_neg hpos.le]
  rw [show ((j : ℝ) + 1) = ((j + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  rw [one_div]

/-! ## The telescoping identity -/

/-- **The gap moment.**  The `j`-th moment of the occupancy of one gap is the telescoped difference
of the `(j+1)`-st powers of its endpoints. -/
theorem intervalIntegral_pow_eq (j : ℕ) (a b : ℝ) :
    (j + 1 : ℝ) * (∫ t in a..b, t ^ j) = b ^ (j + 1) - a ^ (j + 1) := by
  rw [integral_pow]
  field_simp

/-- **`(210)`: the trace difference is `2(j+1)` times the gap moment, minus the forced odd
eigenvalue at the origin.** -/
theorem traceDifference_eq_gapMoment (j : ℕ) {n : ℕ} (p q : Fin n → ℝ) :
    2 * ∑ k, (spectralCompactify (p k) ^ (j + 1) - spectralCompactify (q k) ^ (j + 1))
        - spectralCompactify 0 ^ (j + 1)
      = 2 * (j + 1 : ℝ)
          * (∑ k, ∫ t in (spectralCompactify (q k))..(spectralCompactify (p k)), t ^ j) - 1 := by
  rw [spectralCompactify_zero, one_pow]
  congr 1
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h := intervalIntegral_pow_eq j (spectralCompactify (q k)) (spectralCompactify (p k))
  rw [show (2 : ℝ) * (j + 1 : ℝ) * (∫ t in (spectralCompactify (q k))..(spectralCompactify (p k)),
      t ^ j) = 2 * ((j + 1 : ℝ) * ∫ t in (spectralCompactify (q k))..(spectralCompactify (p k)),
      t ^ j) by ring, h]

/-! ## The occupancy measure -/

/-- **The occupancy moment as a single integral.**  Over a disjoint family of gaps the moment of the
occupancy measure is the sum of the gap moments. -/
theorem integral_iUnion_gaps (j : ℕ) {n : ℕ} (y x : Fin n → ℝ)
    (hdisj : Pairwise (Function.onFun Disjoint fun k => Ioc (y k) (x k)))
    (hint : IntegrableOn (fun t : ℝ => t ^ j) (⋃ k, Ioc (y k) (x k)) volume) :
    (∫ t in ⋃ k, Ioc (y k) (x k), t ^ j) = ∑ k, ∫ t in Ioc (y k) (x k), t ^ j := by
  rw [integral_iUnion (fun k => measurableSet_Ioc) hdisj hint, tsum_fintype]

/-- The gap integral in interval form. -/
theorem integral_Ioc_eq_intervalIntegral (j : ℕ) {a b : ℝ} (hab : a ≤ b) :
    (∫ t in Ioc a b, t ^ j) = ∫ t in a..b, t ^ j := by
  rw [intervalIntegral.integral_of_le hab]

end GaloisForLFunctions.HTGeometry
