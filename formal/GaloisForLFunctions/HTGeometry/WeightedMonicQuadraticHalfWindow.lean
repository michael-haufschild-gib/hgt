import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Sharp weighted monic quadratic floor on a half-window

For weight `x² dx` on `[0,R]`, the monic polynomial in `x²` minimizing squared norm is
`x⁴ - (10/9) R² x² + (5/21) R⁴`.  Its norm is exactly `64 R¹¹ / 43659`.
The completed-square identity below proves the bound for every monic quadratic without
numerical integration.
-/

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

/-- Sharp weighted degree-two monic norm on a half-window. -/
theorem weighted_monic_quadratic_floor (R α β : ℝ) (hR : 0 ≤ R) :
    (64 / 43659 : ℝ) * R ^ (11 : ℕ) ≤
      ∫ x : ℝ in 0..R,
        x ^ (2 : ℕ) * (x ^ (4 : ℕ) + α * x ^ (2 : ℕ) + β) ^ (2 : ℕ) := by
  let F : ℝ → ℝ := fun x =>
    x ^ (11 : ℕ) / 11 +
      (2 * α / 9) * x ^ (9 : ℕ) +
      ((α ^ (2 : ℕ) + 2 * β) / 7) * x ^ (7 : ℕ) +
      (2 * α * β / 5) * x ^ (5 : ℕ) +
      (β ^ (2 : ℕ) / 3) * x ^ (3 : ℕ)
  have hder (x : ℝ) : HasDerivAt F
      (x ^ (2 : ℕ) * (x ^ (4 : ℕ) + α * x ^ (2 : ℕ) + β) ^ (2 : ℕ)) x := by
    have hsum := (((((hasDerivAt_pow 11 x).div_const (11 : ℝ)).add
      ((hasDerivAt_pow 9 x).const_mul (2 * α / 9))).add
      ((hasDerivAt_pow 7 x).const_mul ((α ^ (2 : ℕ) + 2 * β) / 7))).add
      ((hasDerivAt_pow 5 x).const_mul (2 * α * β / 5))).add
      ((hasDerivAt_pow 3 x).const_mul (β ^ (2 : ℕ) / 3))
    have hf : F =
        ((((fun t : ℝ => t ^ (11 : ℕ) / 11) +
          (fun t : ℝ => (2 * α / 9) * t ^ (9 : ℕ))) +
          (fun t : ℝ => ((α ^ (2 : ℕ) + 2 * β) / 7) * t ^ (7 : ℕ))) +
          (fun t : ℝ => (2 * α * β / 5) * t ^ (5 : ℕ))) +
          (fun t : ℝ => (β ^ (2 : ℕ) / 3) * t ^ (3 : ℕ)) := by
      funext t
      simp only [F, Pi.add_apply]
    have hval : x ^ (2 : ℕ) *
        (x ^ (4 : ℕ) + α * x ^ (2 : ℕ) + β) ^ (2 : ℕ) =
        (11 : ℝ) * x ^ (11 - 1) / 11 +
          (2 * α / 9) * (9 * x ^ (9 - 1)) +
          ((α ^ (2 : ℕ) + 2 * β) / 7) * (7 * x ^ (7 - 1)) +
          (2 * α * β / 5) * (5 * x ^ (5 - 1)) +
          (β ^ (2 : ℕ) / 3) * (3 * x ^ (3 - 1)) := by
      norm_num
      ring
    rw [hf, hval]
    exact hsum
  have hint : IntervalIntegrable
      (fun x : ℝ => x ^ (2 : ℕ) *
        (x ^ (4 : ℕ) + α * x ^ (2 : ℕ) + β) ^ (2 : ℕ))
      volume 0 R := by
    have hc : Continuous (fun x : ℝ => x ^ (2 : ℕ) *
        (x ^ (4 : ℕ) + α * x ^ (2 : ℕ) + β) ^ (2 : ℕ)) := by fun_prop
    exact hc.intervalIntegrable 0 R
  have hcalc :
      (∫ x : ℝ in 0..R,
        x ^ (2 : ℕ) * (x ^ (4 : ℕ) + α * x ^ (2 : ℕ) + β) ^ (2 : ℕ)) =
      R ^ (11 : ℕ) / 11 +
        (2 * α / 9) * R ^ (9 : ℕ) +
        ((α ^ (2 : ℕ) + 2 * β) / 7) * R ^ (7 : ℕ) +
        (2 * α * β / 5) * R ^ (5 : ℕ) +
        (β ^ (2 : ℕ) / 3) * R ^ (3 : ℕ) := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx => hder x) hint
    change (∫ x : ℝ in 0..R,
      x ^ (2 : ℕ) * (x ^ (4 : ℕ) + α * x ^ (2 : ℕ) + β) ^ (2 : ℕ)) =
      F R - F 0 at h
    simpa [F] using h
  let A : ℝ := α + (10 / 9) * R ^ (2 : ℕ)
  let B : ℝ := β - (5 / 21) * R ^ (4 : ℕ)
  have hidentity :
      R ^ (11 : ℕ) / 11 +
        (2 * α / 9) * R ^ (9 : ℕ) +
        ((α ^ (2 : ℕ) + 2 * β) / 7) * R ^ (7 : ℕ) +
        (2 * α * β / 5) * R ^ (5 : ℕ) +
        (β ^ (2 : ℕ) / 3) * R ^ (3 : ℕ) =
      (64 / 43659 : ℝ) * R ^ (11 : ℕ) +
        (4 / 175 : ℝ) * A ^ (2 : ℕ) * R ^ (7 : ℕ) +
        (R ^ (3 : ℕ) / 3) *
          (B + (3 / 5 : ℝ) * A * R ^ (2 : ℕ)) ^ (2 : ℕ) := by
    dsimp [A, B]
    ring
  rw [hcalc, hidentity]
  have h1 : 0 ≤ (4 / 175 : ℝ) * A ^ (2 : ℕ) * R ^ (7 : ℕ) := by positivity
  have h2 : 0 ≤ (R ^ (3 : ℕ) / 3) *
      (B + (3 / 5 : ℝ) * A * R ^ (2 : ℕ)) ^ (2 : ℕ) := by positivity
  linarith

end GaloisForLFunctions.HTGeometry
