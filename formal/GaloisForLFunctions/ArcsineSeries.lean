import Mathlib
import GaloisForLFunctions.ArcsineCentralBinomial

/-!
# The Maclaurin series of `arcsin`

`arcsin u = ∑ centralBinom(j) / (4^j (2j+1)) · u^{2j+1}` on `|u| < 1`, obtained by integrating the
central-binomial generating function `∑ centralBinom(j)/4^j · u^{2j} = (1-u²)^{-1/2}` term by term:
the series has the same derivative as `arcsin` on the open unit ball and agrees at `0`.
-/

namespace GaloisForLFunctions

open scoped Nat

/-- The arcsine Taylor coefficient `c_j = centralBinom(j) / (4^j (2j+1))`. -/
noncomputable def arcsinCoeff (j : ℕ) : ℝ := (Nat.centralBinom j : ℝ) / (4 ^ j * (2 * (j : ℝ) + 1))

theorem arcsinCoeff_nonneg (j : ℕ) : 0 ≤ arcsinCoeff j := by unfold arcsinCoeff; positivity

/-- `c_j · (2j+1) = centralBinom(j)/4^j`: the derivative coefficient of `c_j u^{2j+1}`. -/
theorem arcsinCoeff_mul (j : ℕ) :
    arcsinCoeff j * ((2 * j + 1 : ℕ) : ℝ) = (Nat.centralBinom j : ℝ) / 4 ^ j := by
  unfold arcsinCoeff
  have h2 : (2 * (j : ℝ) + 1) ≠ 0 := by positivity
  have h4 : (4 : ℝ) ^ j ≠ 0 := by positivity
  push_cast
  field_simp

theorem arcsinCoeff_le (j : ℕ) : arcsinCoeff j ≤ (Nat.centralBinom j : ℝ) / 4 ^ j := by
  unfold arcsinCoeff
  rw [div_mul_eq_div_div]
  apply div_le_self (by positivity)
  simp only [le_add_iff_nonneg_left]; positivity

/-- The arcsine series has derivative `(1-x²)^{-1/2}` on the open unit ball, by term-by-term
differentiation of the uniformly convergent power series. -/
theorem arcsin_series_hasDerivAt {x : ℝ} (hx : |x| < 1) :
    HasDerivAt (fun y => ∑' j : ℕ, arcsinCoeff j * y ^ (2 * j + 1))
      ((1 - x ^ 2) ^ (-1 / 2 : ℝ)) x := by
  set r := (|x| + 1) / 2 with hrdef
  have hr0 : 0 < r := by rw [hrdef]; positivity
  have hr1 : |r| < 1 := by rw [abs_of_pos hr0, hrdef]; linarith [abs_nonneg x]
  have hxr : x ∈ Metric.ball (0 : ℝ) r := by
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, hrdef]; linarith
  have h0r : (0 : ℝ) ∈ Metric.ball (0 : ℝ) r := by
    rw [Metric.mem_ball, dist_self]; exact hr0
  have hderiv := hasDerivAt_tsum_of_isPreconnected
    (u := fun j => (Nat.centralBinom j : ℝ) / 4 ^ j * r ^ (2 * j))
    (g := fun j (y : ℝ) => arcsinCoeff j * y ^ (2 * j + 1))
    (g' := fun j (y : ℝ) => arcsinCoeff j * (((2 * j + 1 : ℕ) : ℝ) * y ^ (2 * j)))
    (centralBinom_gf r hr1).summable
    Metric.isOpen_ball
    (convex_ball 0 r).isPreconnected
    (fun j y _ => by
      simpa [mul_assoc] using (hasDerivAt_pow (2 * j + 1) y).const_mul (arcsinCoeff j))
    (fun j y hy => by
      rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hy
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      have hac : |arcsinCoeff j| = arcsinCoeff j := abs_of_nonneg (arcsinCoeff_nonneg j)
      have hnn : |((2 * j + 1 : ℕ) : ℝ)| = ((2 * j + 1 : ℕ) : ℝ) := abs_of_nonneg (by positivity)
      have hyp : |y ^ (2 * j)| = |y| ^ (2 * j) := abs_pow y (2 * j)
      rw [hac, hnn, hyp, ← mul_assoc, arcsinCoeff_mul]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact pow_le_pow_left₀ (abs_nonneg y) (le_of_lt hy) (2 * j))
    h0r
    (by simp)
    hxr
  have heq : (∑' j : ℕ, arcsinCoeff j * (((2 * j + 1 : ℕ) : ℝ) * x ^ (2 * j)))
      = (1 - x ^ 2) ^ (-1 / 2 : ℝ) := by
    rw [← (centralBinom_gf x hx).tsum_eq]
    congr 1; ext j; rw [← mul_assoc, arcsinCoeff_mul]
  rwa [heq] at hderiv

theorem summable_arcsin_series {u : ℝ} (hu : |u| < 1) :
    Summable (fun j : ℕ => arcsinCoeff j * u ^ (2 * j + 1)) := by
  have hbound : Summable (fun j : ℕ => |u| * ((Nat.centralBinom j : ℝ) / 4 ^ j * |u| ^ (2 * j))) :=
    ((centralBinom_gf |u| (by rwa [abs_abs])).summable).mul_left |u|
  apply hbound.of_norm_bounded
  intro j
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg (arcsinCoeff_nonneg j)]
  calc arcsinCoeff j * |u| ^ (2 * j + 1)
      ≤ ((Nat.centralBinom j : ℝ) / 4 ^ j) * |u| ^ (2 * j + 1) :=
        mul_le_mul_of_nonneg_right (arcsinCoeff_le j) (by positivity)
    _ = |u| * ((Nat.centralBinom j : ℝ) / 4 ^ j * |u| ^ (2 * j)) := by rw [pow_succ]; ring

/-- **Maclaurin series of `arcsin`.**  On `|u| < 1`,
`arcsin u = ∑ centralBinom(j)/(4^j (2j+1)) · u^{2j+1}`. -/
theorem arcsin_hasSum {u : ℝ} (hu : |u| < 1) :
    HasSum (fun j : ℕ => arcsinCoeff j * u ^ (2 * j + 1)) (Real.arcsin u) := by
  have hEq : Set.EqOn (fun y => ∑' j : ℕ, arcsinCoeff j * y ^ (2 * j + 1)) Real.arcsin
      (Metric.ball 0 1) := by
    apply IsOpen.eqOn_of_deriv_eq Metric.isOpen_ball (convex_ball 0 1).isPreconnected
    · intro y hy
      rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hy
      exact (arcsin_series_hasDerivAt hy).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hy
      have h1 : y ≠ -1 := by rintro rfl; norm_num at hy
      have h2 : y ≠ 1 := by rintro rfl; norm_num at hy
      exact (Real.hasDerivAt_arcsin h1 h2).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hy
      have h1 : y ≠ -1 := by rintro rfl; norm_num at hy
      have h2 : y ≠ 1 := by rintro rfl; norm_num at hy
      have hpos : (0 : ℝ) ≤ 1 - y ^ 2 := by nlinarith [abs_lt.mp hy]
      rw [(arcsin_series_hasDerivAt hy).deriv, (Real.hasDerivAt_arcsin h1 h2).deriv,
        show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.rpow_neg hpos, ← Real.sqrt_eq_rpow, one_div]
    · rw [Metric.mem_ball, dist_self]; norm_num
    · simp
  have hmem : u ∈ Metric.ball (0 : ℝ) 1 := by
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]; exact hu
  have hs := (summable_arcsin_series hu).hasSum
  rwa [show (∑' j : ℕ, arcsinCoeff j * u ^ (2 * j + 1)) = Real.arcsin u from hEq hmem] at hs

/-- **Chord bound for `arcsin`** via Jordan's inequality (`Real.mul_le_sin`): for `0 ≤ u ≤ 1`,
`arcsin u ≤ (π/2)·u`.  Applying `sin x ≥ (2/π)x` at `x = arcsin u` gives `u ≥ (2/π)·arcsin u`. -/
theorem arcsin_le_pi_half_mul (u : ℝ) (h0 : 0 ≤ u) (h1 : u ≤ 1) :
    Real.arcsin u ≤ Real.pi / 2 * u := by
  have harc0 : 0 ≤ Real.arcsin u := Real.arcsin_nonneg.mpr h0
  have hsin : 2 / Real.pi * Real.arcsin u ≤ Real.sin (Real.arcsin u) :=
    Real.mul_le_sin harc0 (Real.arcsin_le_pi_div_two u)
  rw [Real.sin_arcsin (by linarith) h1] at hsin
  have key := mul_le_mul_of_nonneg_left hsin (by positivity : (0 : ℝ) ≤ Real.pi / 2)
  rwa [show Real.pi / 2 * (2 / Real.pi * Real.arcsin u) = Real.arcsin u by field_simp] at key

end GaloisForLFunctions
