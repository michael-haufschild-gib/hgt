import GaloisForLFunctions.HTGeometry.StieltjesMomentProblem
import Mathlib.Analysis.SpecialFunctions.NonIntegrable

/-!
# Shifted reciprocal-seam square tests are not admissible explicit-formula tests

In the explicit-formula variable the shifted reciprocal-seam square test is
`h(t) = t^(-2r) · p(t^(-2))²`.  Writing `p` through its coefficient reversal turns this into

`h(t) = (revPoly p)(t²)² / t^(2r + 4d)`,   `d = deg p`,

with `(revPoly p)(0) = leadingCoeff p ≠ 0`.  So the hard-edge pole has order exactly `2r + 4d ≥ 2`
and the test is not interval integrable on any interval containing the seam.  At the other end
`t^(2r) h(t) = p(t^(-2))² → p(0)²`, so the decay is exactly polynomial of order `2r` — never
rapid.  Either failure alone puts these tests outside the standard Weil/Guinand test class.
-/

open scoped BigOperators
open MeasureTheory Polynomial Asymptotics Filter Topology

noncomputable section

namespace RHTower

/-- The coefficient reversal of a real polynomial. -/
def seamRevPoly (p : Polynomial ℝ) : Polynomial ℝ :=
  ∑ i ∈ Finset.range (p.natDegree + 1), Polynomial.C (p.coeff i) * X ^ (p.natDegree - i)

theorem seamRevPoly_eval (p : Polynomial ℝ) (u : ℝ) :
    (seamRevPoly p).eval u =
      ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * u ^ (p.natDegree - i) := by
  rw [seamRevPoly, Polynomial.eval_finsetSum]
  exact Finset.sum_congr rfl (fun i _ => by simp)

theorem seamRevPoly_eval_zero (p : Polynomial ℝ) :
    (seamRevPoly p).eval 0 = p.leadingCoeff := by
  classical
  rw [seamRevPoly_eval, Finset.sum_eq_single p.natDegree]
  · rw [Nat.sub_self, pow_zero, mul_one, Polynomial.leadingCoeff]
  · intro i hi hine
    have hlt : i < p.natDegree := by
      have := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      omega
    rw [zero_pow (by omega), mul_zero]
  · intro h
    exact absurd (Finset.self_mem_range_succ p.natDegree) h

theorem seamRevPoly_eval_of_ne_zero (p : Polynomial ℝ) {u : ℝ} (hu : u ≠ 0) :
    (seamRevPoly p).eval u = u ^ p.natDegree * p.eval u⁻¹ := by
  rw [seamRevPoly_eval, Polynomial.eval_eq_sum_range, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hle : i ≤ p.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hui : (u : ℝ) ^ i ≠ 0 := pow_ne_zero i hu
  have key : u ^ p.natDegree * ((u : ℝ) ^ i)⁻¹ = u ^ (p.natDegree - i) := by
    field_simp
    rw [← pow_add, Nat.add_sub_cancel' hle]
  rw [inv_pow, ← key]
  ring

/-- The zero-side square test of the shifted reciprocal-seam form, in the explicit-formula
variable. -/
def seamSquareTest (r : ℕ) (p : Polynomial ℝ) (t : ℝ) : ℝ :=
  (t ^ (2 * r))⁻¹ * (p.eval ((t ^ 2)⁻¹)) ^ 2

/-- **The exact hard-edge exponent.**  Away from the seam the square test is the reversed
polynomial squared over `t ^ (2r + 4d)`. -/
theorem seamSquareTest_eq (r : ℕ) (p : Polynomial ℝ) {t : ℝ} (ht : t ≠ 0) :
    seamSquareTest r p t =
      ((seamRevPoly p).eval (t ^ 2)) ^ 2 / t ^ (2 * r + 4 * p.natDegree) := by
  have ht2 : (t ^ 2 : ℝ) ≠ 0 := pow_ne_zero 2 ht
  have hrev := seamRevPoly_eval_of_ne_zero p ht2
  have hp : p.eval ((t ^ 2)⁻¹) = ((seamRevPoly p).eval (t ^ 2)) / (t ^ 2) ^ p.natDegree := by
    rw [hrev]
    field_simp
  have hexp : ((t : ℝ) ^ 2) ^ p.natDegree * ((t : ℝ) ^ 2) ^ p.natDegree * t ^ (2 * r) =
      t ^ (2 * r + 4 * p.natDegree) := by
    rw [← pow_mul, ← pow_add, ← pow_add]
    congr 1
    omega
  rw [seamSquareTest, hp, div_pow, ← hexp]
  field_simp

/-- **The square tests are not interval integrable across the seam.**  For a nonzero polynomial and
`r ≥ 1` the hard-edge pole has order at least two, so the test is not integrable on any interval
containing the seam. -/
theorem not_intervalIntegrable_seamSquareTest {r : ℕ} (hr : 1 ≤ r) {p : Polynomial ℝ}
    (hp : p ≠ 0) {a b : ℝ} (hne : a ≠ b) (h0 : (0 : ℝ) ∈ Set.uIcc a b) :
    ¬ IntervalIntegrable (seamSquareTest r p) volume a b := by
  set d : ℕ := p.natDegree with hd
  set L : ℝ := p.leadingCoeff with hL
  have hL0 : L ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp
  have hpos : 0 < L ^ 2 := sq_pos_of_ne_zero hL0
  have hcont : ContinuousAt (fun t : ℝ => ((seamRevPoly p).eval (t ^ 2)) ^ 2) 0 :=
    (((seamRevPoly p).continuous.comp (continuous_pow 2)).pow 2).continuousAt
  have hval : ((seamRevPoly p).eval ((0 : ℝ) ^ 2)) ^ 2 = L ^ 2 := by
    rw [show ((0 : ℝ) ^ 2) = 0 by ring, seamRevPoly_eval_zero]
  have hnear : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), L ^ 2 / 2 ≤ ((seamRevPoly p).eval (t ^ 2)) ^ 2 := by
    have hlt : L ^ 2 / 2 < ((seamRevPoly p).eval ((0 : ℝ) ^ 2)) ^ 2 := by rw [hval]; linarith
    exact hcont.eventually (eventually_ge_nhds hlt)
  have hball : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), |t| ≤ 1 := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) one_pos] with t ht
    exact le_of_lt (by simpa [Real.dist_eq] using ht)
  refine not_intervalIntegrable_of_sub_inv_isBigO_punctured ?_ hne (by simpa using h0)
  refine Asymptotics.IsBigO.of_bound (2 / L ^ 2) ?_
  filter_upwards [nhdsWithin_le_nhds hnear, nhdsWithin_le_nhds hball,
    self_mem_nhdsWithin] with t hnr hb ht0
  have ht : t ≠ 0 := by simpa using ht0
  have habs : 0 < |t| := abs_pos.mpr ht
  have hden : |t| ^ (2 * r + 4 * d) ≤ |t| := by
    calc |t| ^ (2 * r + 4 * d) ≤ |t| ^ 1 := by
          refine pow_le_pow_of_le_one (abs_nonneg t) hb ?_
          omega
      _ = |t| := pow_one _
  have hlow : L ^ 2 / 2 * |t|⁻¹ ≤ |seamSquareTest r p t| := by
    have hnum0 : |((seamRevPoly p).eval (t ^ 2)) ^ 2| = ((seamRevPoly p).eval (t ^ 2)) ^ 2 :=
      abs_of_nonneg (sq_nonneg _)
    have hden0 : |t ^ (2 * r + 4 * d)| = |t| ^ (2 * r + 4 * d) := abs_pow t _
    rw [seamSquareTest_eq r p ht, abs_div, hnum0, hden0, le_div_iff₀ (pow_pos habs _)]
    have hstep : L ^ 2 / 2 * |t|⁻¹ * |t| ^ (2 * r + 4 * d) ≤ L ^ 2 / 2 * |t|⁻¹ * |t| :=
      mul_le_mul_of_nonneg_left hden (by positivity)
    have heq : L ^ 2 / 2 * |t|⁻¹ * |t| = L ^ 2 / 2 := by field_simp
    linarith [hnr]
  rw [sub_zero, Real.norm_eq_abs, Real.norm_eq_abs, abs_inv, div_mul_eq_mul_div,
    le_div_iff₀ hpos]
  nlinarith [hlow]

/-- **Only polynomial decay at infinity.**  Multiplying by `t ^ (2r)` recovers the square of the
polynomial evaluated at the reciprocal square. -/
theorem seamSquareTest_decay_exact (r : ℕ) (p : Polynomial ℝ) {t : ℝ} (ht : t ≠ 0) :
    t ^ (2 * r) * seamSquareTest r p t = (p.eval ((t ^ 2)⁻¹)) ^ 2 := by
  rw [seamSquareTest, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ ht), one_mul]

/-- The decay exponent is exactly `2r`: the square test decays polynomially, never rapidly. -/
theorem seamSquareTest_decay_limit (r : ℕ) (p : Polynomial ℝ) :
    Filter.Tendsto (fun t : ℝ => t ^ (2 * r) * seamSquareTest r p t) Filter.atTop
      (nhds ((p.eval 0) ^ 2)) := by
  have h1 : Filter.Tendsto (fun t : ℝ => (t ^ 2)⁻¹) Filter.atTop (nhds 0) :=
    Filter.Tendsto.inv_tendsto_atTop (tendsto_pow_atTop (by norm_num))
  have h2 : Filter.Tendsto (fun t : ℝ => (p.eval ((t ^ 2)⁻¹)) ^ 2) Filter.atTop
      (nhds ((p.eval 0) ^ 2)) :=
    ((p.continuous.continuousAt.tendsto.comp h1).pow 2)
  refine h2.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
  exact (seamSquareTest_decay_exact r p (ne_of_gt ht)).symm

end RHTower
