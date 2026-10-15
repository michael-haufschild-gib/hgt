import GaloisForLFunctions.RHTower.MarkovCubicLogSecantAndTenPointNineRatioPBAP

/-!
# Simpson's Fourth-Order Logarithmic Inequality, the `(6n - 5) / (6(n - 1)n(2n - 1))` Right-Endpoint Envelope, and Coercivity up to `spectralSecondMoment / L² < 6367 / 545 > 11.682`

In Module 56 and Module 57, the upper bound on the left secant slope
`(log x - log (n - 1)) / (x - (n - 1))` came from the second-order Trapezoidal inequality
`log b - log a ≤ ((b - a) / 2) * (1 / a + 1 / b)`. Because the Trapezoidal error on `1 / t` is
`+(b - a)^3 / (12 t^3)` while the Midpoint error is `-(b - a)^3 / (24 t^3)`, their `(1/3, 2/3)`
convex combination — **Simpson's Rule** — cancels the cubic error completely, leaving a strictly
positive fourth derivative `(t⁻¹)⁽⁴⁾ = 24 / t^5 > 0`.

In this module, we prove Simpson's fourth-order logarithmic upper bound and use it to tighten the
two-endpoint linear-parabola envelope for `(log x - cellSecant log n x) / √x`:

1. **Section 1 (Simpson's Fourth-Order Upper Bound for `log b - log a` and the
   `(6n - 5) / (6(n - 1)n(2n - 1))` Right-Endpoint Linear-Parabola Envelope):**
   - Applying the Mean Value Theorem to
     `ψ(t) = log t - (1 / (6a)) t + (a / 6) t⁻¹ + (8a / 3) (t + a)⁻¹`, whose derivative is
     identically `ψ'(t) = -(t - a)^4 / (6 a t^2 (t + a)^2) ≤ 0`, proves **Simpson's Upper Bound**
     (`log_sub_log_le_simpson`):
     `log b - log a ≤ ((b - a) / 6) * (1 / a + 1 / b) + 4 * (b - a) / (3 * (a + b))`.
   - Combining Simpson's upper bound on `[n - 1, x]` with the Midpoint lower bound on `[x, n]` and
     our single-denominator secant convexity identities for `1 / x`, `1 / (x + n - 1)`, and
     `1 / (x + n)` proves (`simpson_slope_bound_le_linear_of_mem_Ioo` and
     `log_sub_cellSecant_log_le_simpson_linear_mul_cellParabola`) that for all `2 ≤ n` and
     `x ∈ [n - 1, n]`:
     `log x - cellSecant log n x ≤ ((n - x) / ((n - 1)(2n - 1)) + (6n - 5)(x - (n - 1)) / (6(n - 1)n(2n - 1))) * cellParabola n x`!
     At `n = 2`, the right-endpoint coefficient drops from `1 / 4 = 9 / 36 = 0.25` to
     `7 / 36 ≈ 0.19444` (within `0.0013` of the exact transcendental limit `log 2 - 1 / 2 ≈ 0.19315`!).

2. **Section 2 (Unified `(√2, √3)` Rationalization `53 / (180√2) + 151 / (1260√3) ≤ 5 / 18` and
   the `109 / 1728` Logarithmic Cell-Defect Bound):**
   - Grouping the `1 / √2` terms (`n = 3` left endpoint `1 / (10√2)` + `n = 2` right endpoint
     `7 / (36√2) = 53 / (180√2)`) and the `1 / √3` terms (`n = 4` left endpoint `1 / (21√3)` +
     `n = 3` right endpoint `13 / (180√3) = 151 / (1260√3)`) across the two endpoint series yields
     `53 / (180√2) + 151 / (1260√3) ≤ 5 / 18` (`0.277394 < 0.277778`).
   - Combining with the rational `n = 2` left endpoint (`1 / 3`), `n = 4` right endpoint (`≤ 1 / 48`),
     and `n ≥ 5` tails (`≤ 1 / 12 + 1 / 24 = 1 / 8`) gives
     `1 / 3 + 5 / 18 + 1 / 48 + 1 / 8 = 109 / 144`, and multiplying by `1 / 12` reduces the
     curvature constant from `193 / 2880 ≈ 0.06701` to **`109 / 1728 ≈ 0.06308`**
     (`neg_one_hundred_nine_seventeen_twenty_eighths_spectralSecondMoment_add_l2_le_secantNumeratorCellDefect`):
     `-(109 / 1728) * (spectralSecondMoment f.1 + ∫ u, ‖f.1 u‖ ^ 2) ≤ secantNumeratorCellDefect f.1 N`!

3. **Section 3 (The `(6367 / 8640) ∫ ‖f.1‖² - (109 / 1728) spectralSecondMoment f.1` Coercivity Law,
   the `(1403 / 1728) ∫ ‖f.1‖² - (109 / 1728) spectralSecondMoment f.1` Prime-Blind Cone Law, and
   Unconditional `markovEnergy ≥ 0` up to `spectralSecondMoment F ≤ (6367 / 545 - δ) ∫ ‖F‖² > 11.682 ∫ ‖F‖²`):**
   - Absorbing `(109 / 1728) * ∫ ‖f.1‖²` yields:
     - `(6367 / 8640) * ∫ ‖f.1‖² - (109 / 1728) * spectralSecondMoment f.1 ≤ rightCellQuadratureDefect (weilContinuumLogProfile f.1) N`
       (critical ratio **`6367 / 545 > 11.6825`**!), and
     - on the Prime-Blind Cone (`logVector f = 0`), since `8` divides `1728` (`7 / 8 = 1512 / 1728`),
       `(1403 / 1728) * ∫ ‖f.1‖² - (109 / 1728) * spectralSecondMoment f.1 ≤ rightCellQuadratureDefect (weilContinuumLogProfile f.1) N`
       (critical ratio **`1403 / 109 > 12.8715`**!).
-/

open Complex MeasureTheory Filter Topology Set Finsupp
open scoped Real ComplexConjugate ContDiff FourierTransform
open Zeta23
open GaloisForLFunctions.RHTower
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

open WeilOneSided WeilSpectral WeilLevyPole WeilLevyPoleGauss WeilLevyCoshCrossover LebesgueAtomWeil
open RHTower.NonnegativeCone

/-! ## Section 1: Simpson's Fourth-Order Upper Bound for `log b - log a` and the `(6n - 5) / (6(n - 1)n(2n - 1))` Right-Endpoint Linear-Parabola Envelope -/

/-- **Simpson's Fourth-Order Upper Bound for `Real.log b - Real.log a`**:
for any `0 < a ≤ b`,
`Real.log b - Real.log a ≤ ((b - a) / 6) * (1 / a + 1 / b) + 4 * (b - a) / (3 * (a + b))`. -/
theorem log_sub_log_le_simpson {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Real.log b - Real.log a ≤
      ((b - a) / 6) * (1 / a + 1 / b) + 4 * (b - a) / (3 * (a + b)) := by
  rcases eq_or_lt_of_le hab with rfl | hab_lt
  · norm_num
  have hb : 0 < b := ha.trans hab_lt
  let ψ : ℝ → ℝ := fun t =>
    Real.log t - (1 / (6 * a)) * t + (a / 6) * t⁻¹ + (8 * a / 3) * (t + a)⁻¹
  let ψ' : ℝ → ℝ := fun t =>
    t⁻¹ - (1 / (6 * a)) * 1 + (a / 6) * (-(t ^ 2)⁻¹) +
      (8 * a / 3) * (-(1 + 0) / (t + a) ^ 2)
  have hd : ∀ t ∈ Icc a b, HasDerivAt ψ (ψ' t) t := by
    intro t ht
    have ht_pos : 0 < t := ha.trans_le ht.1
    have hta_pos : 0 < t + a := add_pos ht_pos ha
    exact (((Real.hasDerivAt_log ht_pos.ne').sub
      ((hasDerivAt_id t).const_mul (1 / (6 * a)))).add
      ((hasDerivAt_inv ht_pos.ne').const_mul (a / 6))).add
      ((((hasDerivAt_id t).add (hasDerivAt_const t a)).inv hta_pos.ne').const_mul (8 * a / 3))
  obtain ⟨c, hc, hc_slope⟩ := exists_hasDerivAt_eq_slope ψ ψ' hab_lt
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => hd t ⟨ht.1.le, ht.2.le⟩)
  have hc_pos : 0 < c := ha.trans hc.1
  have hca_pos : 0 < c + a := add_pos hc_pos ha
  have hba_pos : 0 < b - a := sub_pos.mpr hab_lt
  have hψ'_le : ψ' c ≤ 0 := by
    have hψ'_eq : ψ' c = -(c - a) ^ 4 / (6 * a * c ^ 2 * (c + a) ^ 2) := by
      dsimp [ψ']
      have ha0 : a ≠ 0 := ha.ne'
      have hc0 : c ≠ 0 := hc_pos.ne'
      have hca0 : c + a ≠ 0 := hca_pos.ne'
      field_simp [ha0, hc0, hca0]
      ring
    rw [hψ'_eq, neg_div]
    exact neg_nonpos.mpr (div_nonneg (by positivity) (by positivity))
  have hdiff_eq : ψ b - ψ a = ψ' c * (b - a) := ((eq_div_iff hba_pos.ne').mp hc_slope).symm
  have hdiff_le : ψ b - ψ a ≤ 0 := by
    rw [hdiff_eq]
    exact mul_nonpos_of_nonpos_of_nonneg hψ'_le hba_pos.le
  have halg : ψ b - ψ a =
      (Real.log b - Real.log a) -
        (((b - a) / 6) * (1 / a + 1 / b) + 4 * (b - a) / (3 * (a + b))) := by
    dsimp [ψ]
    have ha0 : a ≠ 0 := ha.ne'
    have hb0 : b ≠ 0 := hb.ne'
    have hab0 : b + a ≠ 0 := (add_pos hb ha).ne'
    have hab0' : a + b ≠ 0 := (add_pos ha hb).ne'
    field_simp [ha0, hb0, hab0, hab0']
    ring
  linarith

/-- **Simpson Two-Endpoint Linear Envelope for the Slope Difference on `(n - 1, n)`**:
for `2 ≤ n` and `x ∈ (n - 1, n)`,
`(1 / 6) * (1 / (n - 1) + 1 / x) + 4 / (3 * (x + (n - 1))) - 2 / (x + n) ≤ (n - x) / ((n - 1)(2n - 1)) + (6n - 5)(x - (n - 1)) / (6(n - 1)n(2n - 1))`. -/
theorem simpson_slope_bound_le_linear_of_mem_Ioo
    {n : ℕ} (hn : 2 ≤ n) {x : ℝ} (hx1 : (n : ℝ) - 1 < x) (hx2 : x < (n : ℝ)) :
    (1 / 6) * (1 / ((n : ℝ) - 1) + 1 / x) + 4 / (3 * ((n : ℝ) - 1 + x)) - 2 / (x + (n : ℝ)) ≤
      ((n : ℝ) - x) * (1 / (((n : ℝ) - 1) * (2 * (n : ℝ) - 1))) +
        (x - ((n : ℝ) - 1)) *
          ((6 * (n : ℝ) - 5) / (6 * ((n : ℝ) - 1) * (n : ℝ) * (2 * (n : ℝ) - 1))) := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn1_pos : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hn_pos : (0 : ℝ) < (n : ℝ) := by linarith
  have hx_pos : 0 < x := hn1_pos.trans hx1
  have h2n1_pos : (0 : ℝ) < 2 * (n : ℝ) - 1 := by linarith
  have hxn_pos : 0 < x + (n : ℝ) := by linarith
  have hxn1_pos : 0 < (n : ℝ) - 1 + x := by linarith
  have hpf1 : 1 / ((n : ℝ) - 1) - 2 / (2 * (n : ℝ) - 1) =
      1 / (((n : ℝ) - 1) * (2 * (n : ℝ) - 1)) := by
    rw [div_sub_div 1 2 hn1_pos.ne' h2n1_pos.ne']
    ring
  have hpf2 :
      (1 / 6) * (1 / ((n : ℝ) - 1)) - (5 / 6) * (1 / (n : ℝ)) +
        (4 / 3) * (1 / (2 * (n : ℝ) - 1)) =
      (6 * (n : ℝ) - 5) / (6 * ((n : ℝ) - 1) * (n : ℝ) * (2 * (n : ℝ) - 1)) := by
    have hstep1 :
        1 / ((n : ℝ) - 1) - 5 / (n : ℝ) =
          (5 - 4 * (n : ℝ)) / (((n : ℝ) - 1) * (n : ℝ)) := by
      rw [div_sub_div 1 5 hn1_pos.ne' hn_pos.ne']
      ring
    have hstep2 :
        (5 - 4 * (n : ℝ)) / (((n : ℝ) - 1) * (n : ℝ)) + 8 / (2 * (n : ℝ) - 1) =
          (6 * (n : ℝ) - 5) / ((((n : ℝ) - 1) * (n : ℝ)) * (2 * (n : ℝ) - 1)) := by
      rw [div_add_div _ _ (by positivity) h2n1_pos.ne']
      ring
    have hlin :
        (1 / 6) * (1 / ((n : ℝ) - 1)) - (5 / 6) * (1 / (n : ℝ)) +
          (4 / 3) * (1 / (2 * (n : ℝ) - 1)) =
        (1 / 6) * ((1 / ((n : ℝ) - 1) - 5 / (n : ℝ)) + 8 / (2 * (n : ℝ) - 1)) := by ring
    rw [hlin, hstep1, hstep2, ← mul_div_assoc, div_eq_div_iff (by positivity) (by positivity)]
    ring
  have h1_sum :
      ((n : ℝ) - x) / ((n : ℝ) - 1) + (x - ((n : ℝ) - 1)) / (n : ℝ) =
        (2 * (n : ℝ) - 1 - x) / (((n : ℝ) - 1) * (n : ℝ)) := by
    rw [div_add_div _ _ hn1_pos.ne' hn_pos.ne']
    ring
  have h1_diff :
      (2 * (n : ℝ) - 1 - x) / (((n : ℝ) - 1) * (n : ℝ)) - 1 / x =
        cellParabola n x / ((((n : ℝ) - 1) * (n : ℝ)) * x) := by
    rw [div_sub_div _ _ (by positivity) hx_pos.ne']
    unfold cellParabola
    ring
  have h2_sum :
      (2 * ((n : ℝ) - x)) / (2 * (n : ℝ) - 1) + (x - ((n : ℝ) - 1)) / (n : ℝ) =
        (3 * (n : ℝ) - 1 - x) / ((2 * (n : ℝ) - 1) * (n : ℝ)) := by
    rw [div_add_div _ _ h2n1_pos.ne' hn_pos.ne']
    ring
  have h2_diff :
      (3 * (n : ℝ) - 1 - x) / ((2 * (n : ℝ) - 1) * (n : ℝ)) - 2 / (x + (n : ℝ)) =
        cellParabola n x / (((2 * (n : ℝ) - 1) * (n : ℝ)) * (x + (n : ℝ))) := by
    rw [div_sub_div _ _ (by positivity) hxn_pos.ne']
    unfold cellParabola
    ring
  have h3_sum :
      ((n : ℝ) - x) / ((n : ℝ) - 1) + (2 * (x - ((n : ℝ) - 1))) / (2 * (n : ℝ) - 1) =
        (3 * (n : ℝ) - 2 - x) / (((n : ℝ) - 1) * (2 * (n : ℝ) - 1)) := by
    rw [div_add_div _ _ hn1_pos.ne' h2n1_pos.ne']
    ring
  have h3_diff :
      (3 * (n : ℝ) - 2 - x) / (((n : ℝ) - 1) * (2 * (n : ℝ) - 1)) - 2 / ((n : ℝ) - 1 + x) =
        cellParabola n x / ((((n : ℝ) - 1) * (2 * (n : ℝ) - 1)) * ((n : ℝ) - 1 + x)) := by
    rw [div_sub_div _ _ (by positivity) hxn1_pos.ne']
    unfold cellParabola
    ring
  have hrhs_decomp :
      ((n : ℝ) - x) * (1 / ((n : ℝ) - 1) - 2 / (2 * (n : ℝ) - 1)) +
        (x - ((n : ℝ) - 1)) *
          ((1 / 6) * (1 / ((n : ℝ) - 1)) - (5 / 6) * (1 / (n : ℝ)) +
            (4 / 3) * (1 / (2 * (n : ℝ) - 1))) =
      (1 / 6) * (1 / ((n : ℝ) - 1)) +
        (1 / 6) * (((n : ℝ) - x) / ((n : ℝ) - 1) + (x - ((n : ℝ) - 1)) / (n : ℝ)) +
        (2 / 3) * (((n : ℝ) - x) / ((n : ℝ) - 1) + (2 * (x - ((n : ℝ) - 1))) / (2 * (n : ℝ) - 1)) -
        ((2 * ((n : ℝ) - x)) / (2 * (n : ℝ) - 1) + (x - ((n : ℝ) - 1)) / (n : ℝ)) := by
    ring
  have hpar_nonneg : 0 ≤ cellParabola n x := cellParabola_nonneg_of_mem_Icc ⟨hx1.le, hx2.le⟩
  have hden_cmp1 :
      2 / (((2 * (n : ℝ) - 1) * (n : ℝ)) * (x + (n : ℝ))) ≤
        1 / ((((n : ℝ) - 1) * (n : ℝ)) * x) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hpoly :
        1 * (((2 * (n : ℝ) - 1) * (n : ℝ)) * (x + (n : ℝ))) -
          2 * ((((n : ℝ) - 1) * (n : ℝ)) * x) =
        (n : ℝ) * ((2 * (n : ℝ) - 1) * (n : ℝ) + x) := by ring
    have hpos : 0 ≤ (n : ℝ) * ((2 * (n : ℝ) - 1) * (n : ℝ) + x) := by positivity
    linarith
  have hden_cmp2 :
      1 / (((2 * (n : ℝ) - 1) * (n : ℝ)) * (x + (n : ℝ))) ≤
        1 / ((((n : ℝ) - 1) * (2 * (n : ℝ) - 1)) * ((n : ℝ) - 1 + x)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hpoly :
        1 * (((2 * (n : ℝ) - 1) * (n : ℝ)) * (x + (n : ℝ))) -
          1 * ((((n : ℝ) - 1) * (2 * (n : ℝ) - 1)) * ((n : ℝ) - 1 + x)) =
        (2 * (n : ℝ) - 1) * (x + (2 * (n : ℝ) - 1)) := by ring
    have hpos : 0 ≤ (2 * (n : ℝ) - 1) * (x + (2 * (n : ℝ) - 1)) := by positivity
    linarith
  have hmul1 := mul_le_mul_of_nonneg_left hden_cmp1
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 6) hpar_nonneg)
  have hmul2 := mul_le_mul_of_nonneg_left hden_cmp2
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2 / 3) hpar_nonneg)
  have hmul1_lhs :
      (1 / 6) * cellParabola n x * (2 / (((2 * (n : ℝ) - 1) * (n : ℝ)) * (x + (n : ℝ)))) =
        (1 / 3) * (cellParabola n x / (((2 * (n : ℝ) - 1) * (n : ℝ)) * (x + (n : ℝ)))) := by ring
  have hmul1_rhs :
      (1 / 6) * cellParabola n x * (1 / ((((n : ℝ) - 1) * (n : ℝ)) * x)) =
        (1 / 6) * (cellParabola n x / ((((n : ℝ) - 1) * (n : ℝ)) * x)) := by ring
  have hmul2_lhs :
      (2 / 3) * cellParabola n x * (1 / (((2 * (n : ℝ) - 1) * (n : ℝ)) * (x + (n : ℝ)))) =
        (2 / 3) * (cellParabola n x / (((2 * (n : ℝ) - 1) * (n : ℝ)) * (x + (n : ℝ)))) := by ring
  have hmul2_rhs :
      (2 / 3) * cellParabola n x * (1 / ((((n : ℝ) - 1) * (2 * (n : ℝ) - 1)) * ((n : ℝ) - 1 + x))) =
        (2 / 3) * (cellParabola n x / ((((n : ℝ) - 1) * (2 * (n : ℝ) - 1)) * ((n : ℝ) - 1 + x))) := by ring
  have hfour_thirds :
      (2 / 3) * (2 / ((n : ℝ) - 1 + x)) = 4 / (3 * ((n : ℝ) - 1 + x)) := by
    rw [← mul_div_assoc, div_eq_div_iff (by positivity) (by positivity)]
    ring
  rw [← hpf1, ← hpf2, hrhs_decomp, h1_sum, h2_sum, h3_sum]
  linarith

/-- **Simpson Two-Endpoint Linear-Parabola Bound for `Real.log x - cellSecant Real.log n x`**:
for `2 ≤ n` and `x ∈ Icc (n - 1) n`,
`Real.log x - cellSecant Real.log n x ≤ ((n - x) / ((n - 1)(2n - 1)) + (6n - 5)(x - (n - 1)) / (6(n - 1)n(2n - 1))) * cellParabola n x`. -/
theorem log_sub_cellSecant_log_le_simpson_linear_mul_cellParabola
    {n : ℕ} (hn : 2 ≤ n) {x : ℝ} (hx : x ∈ Icc ((n : ℝ) - 1) (n : ℝ)) :
    Real.log x - cellSecant Real.log n x ≤
      (((n : ℝ) - x) * (1 / (((n : ℝ) - 1) * (2 * (n : ℝ) - 1))) +
        (x - ((n : ℝ) - 1)) *
          ((6 * (n : ℝ) - 5) / (6 * ((n : ℝ) - 1) * (n : ℝ) * (2 * (n : ℝ) - 1)))) *
        cellParabola n x := by
  rcases eq_or_lt_of_le hx.1 with rfl | hx1
  · rw [cellParabola_left_eq_zero, mul_zero]
    unfold cellSecant
    linarith
  rcases eq_or_lt_of_le hx.2 with rfl | hx2
  · rw [cellParabola_right_eq_zero, mul_zero]
    unfold cellSecant
    linarith
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn1_pos : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hx_pos : 0 < x := hn1_pos.trans hx1
  have hx1_pos : 0 < x - ((n : ℝ) - 1) := sub_pos.mpr hx1
  have hx2_pos : 0 < (n : ℝ) - x := sub_pos.mpr hx2
  have hleft_slope :
      (Real.log x - Real.log ((n : ℝ) - 1)) / (x - ((n : ℝ) - 1)) ≤
        (1 / 6) * (1 / ((n : ℝ) - 1) + 1 / x) + 4 / (3 * ((n : ℝ) - 1 + x)) := by
    rw [div_le_iff₀ hx1_pos]
    have hsimp := log_sub_log_le_simpson hn1_pos hx.1
    have h4 : 4 / (3 * ((n : ℝ) - 1 + x)) * (x - ((n : ℝ) - 1)) =
        4 * (x - ((n : ℝ) - 1)) / (3 * ((n : ℝ) - 1 + x)) := by ring
    linarith
  have hright_slope :
      2 / (x + (n : ℝ)) ≤ (Real.log (n : ℝ) - Real.log x) / ((n : ℝ) - x) := by
    rw [le_div_iff₀ hx2_pos]
    have hmid := two_mul_sub_div_add_le_log_sub_log hx_pos hx.2
    have heq : 2 / (x + (n : ℝ)) * ((n : ℝ) - x) = 2 * ((n : ℝ) - x) / (x + (n : ℝ)) := by ring
    linarith
  have hlin := simpson_slope_bound_le_linear_of_mem_Ioo hn hx1 hx2
  have hslope_le :
      (Real.log x - Real.log ((n : ℝ) - 1)) / (x - ((n : ℝ) - 1)) -
        (Real.log (n : ℝ) - Real.log x) / ((n : ℝ) - x) ≤
      ((n : ℝ) - x) * (1 / (((n : ℝ) - 1) * (2 * (n : ℝ) - 1))) +
        (x - ((n : ℝ) - 1)) *
          ((6 * (n : ℝ) - 5) / (6 * ((n : ℝ) - 1) * (n : ℝ) * (2 * (n : ℝ) - 1))) := by
    linarith
  rw [sub_cellSecant_eq_cellParabola_mul_slope_diff Real.log n ⟨hx1, hx2⟩, mul_comm]
  exact mul_le_mul_of_nonneg_right hslope_le (cellParabola_nonneg_of_mem_Icc hx)

/-- **Pointwise Simpson Linear-Parabola Bound on `(Real.log x - cellSecant Real.log n x) / √x`**:
for `2 ≤ n` and `x ∈ Icc (n - 1) n`,
`(Real.log x - cellSecant Real.log n x) / √x ≤ (((n - x) / ((n - 1)(2n - 1)√(n - 1)) + (6n - 5)(x - (n - 1)) / (6(n - 1)n(2n - 1)√n))) * cellParabola n x`. -/
theorem log_sub_cellSecant_log_div_sqrt_le_simpson_linear_mul_cellParabola
    {n : ℕ} (hn : 2 ≤ n) {x : ℝ} (hx : x ∈ Icc ((n : ℝ) - 1) (n : ℝ)) :
    (Real.log x - cellSecant Real.log n x) / Real.sqrt x ≤
      (((n : ℝ) - x) * (1 / (((n : ℝ) - 1) * (2 * (n : ℝ) - 1) * Real.sqrt ((n : ℝ) - 1))) +
        (x - ((n : ℝ) - 1)) *
          ((6 * (n : ℝ) - 5) / (6 * ((n : ℝ) - 1) * (n : ℝ) * (2 * (n : ℝ) - 1) * Real.sqrt (n : ℝ)))) *
        cellParabola n x := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn1_pos : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hn_pos : (0 : ℝ) < (n : ℝ) := by linarith
  have h2n1_pos : (0 : ℝ) < 2 * (n : ℝ) - 1 := by linarith
  have hlog := log_sub_cellSecant_log_le_simpson_linear_mul_cellParabola hn hx
  have hsqrt := inv_sqrt_le_cellSecant_inv_sqrt hn hx
  let u := (n : ℝ) - x
  let v := x - ((n : ℝ) - 1)
  have hu : 0 ≤ u := sub_nonneg.mpr hx.2
  have hv : 0 ≤ v := sub_nonneg.mpr hx.1
  have huv : u + v = 1 := by dsimp [u, v]; ring
  let A₀ := 1 / (((n : ℝ) - 1) * (2 * (n : ℝ) - 1))
  let A₁ := (6 * (n : ℝ) - 5) / (6 * ((n : ℝ) - 1) * (n : ℝ) * (2 * (n : ℝ) - 1))
  let B₀ := 1 / Real.sqrt ((n : ℝ) - 1)
  let B₁ := 1 / Real.sqrt (n : ℝ)
  have hA_le : A₁ ≤ A₀ := by
    dsimp [A₀, A₁]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hpoly :
        1 * (6 * ((n : ℝ) - 1) * (n : ℝ) * (2 * (n : ℝ) - 1)) -
          (6 * (n : ℝ) - 5) * (((n : ℝ) - 1) * (2 * (n : ℝ) - 1)) =
        5 * (((n : ℝ) - 1) * (2 * (n : ℝ) - 1)) := by ring
    have hpos : 0 ≤ 5 * (((n : ℝ) - 1) * (2 * (n : ℝ) - 1)) := by positivity
    linarith
  have hB_le : B₁ ≤ B₀ := by
    dsimp [B₀, B₁]
    exact one_div_le_one_div_of_le (Real.sqrt_pos.mpr hn1_pos) (Real.sqrt_le_sqrt (by linarith))
  have hA_nonneg : 0 ≤ A₀ * u + A₁ * v := by
    have h6n5 : 0 ≤ 6 * (n : ℝ) - 5 := by linarith
    dsimp [A₀, A₁]
    positivity
  have hpar_nonneg := cellParabola_nonneg_of_mem_Icc hx
  have hmul1 :
      (Real.log x - cellSecant Real.log n x) * (1 / Real.sqrt x) ≤
        ((A₀ * u + A₁ * v) * cellParabola n x) * (1 / Real.sqrt x) := by
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    have heq : (A₀ * u + A₁ * v) * cellParabola n x =
        (((n : ℝ) - x) * (1 / (((n : ℝ) - 1) * (2 * (n : ℝ) - 1))) +
          (x - ((n : ℝ) - 1)) *
            ((6 * (n : ℝ) - 5) / (6 * ((n : ℝ) - 1) * (n : ℝ) * (2 * (n : ℝ) - 1)))) *
          cellParabola n x := by
      dsimp [A₀, A₁, u, v]
      ring
    linarith
  have hmul2 :
      ((A₀ * u + A₁ * v) * cellParabola n x) * (1 / Real.sqrt x) ≤
        ((A₀ * u + A₁ * v) * (B₀ * u + B₁ * v)) * cellParabola n x := by
    have h := mul_le_mul_of_nonneg_left hsqrt (mul_nonneg hA_nonneg hpar_nonneg)
    have heq1 : (A₀ * u + A₁ * v) * cellParabola n x *
        (((n : ℝ) - x) * (1 / Real.sqrt ((n : ℝ) - 1)) +
          (x - ((n : ℝ) - 1)) * (1 / Real.sqrt (n : ℝ))) =
        ((A₀ * u + A₁ * v) * (B₀ * u + B₁ * v)) * cellParabola n x := by
      dsimp [B₀, B₁, u, v]
      ring
    linarith
  have hcheb := mul_le_mul_of_nonneg_right
    (chebyshev_secant_mul_le hA_le hB_le hu hv huv) hpar_nonneg
  have hrhs_eq :
      (A₀ * B₀ * u + A₁ * B₁ * v) * cellParabola n x =
        (((n : ℝ) - x) * (1 / (((n : ℝ) - 1) * (2 * (n : ℝ) - 1) * Real.sqrt ((n : ℝ) - 1))) +
          (x - ((n : ℝ) - 1)) *
            ((6 * (n : ℝ) - 5) / (6 * ((n : ℝ) - 1) * (n : ℝ) * (2 * (n : ℝ) - 1) * Real.sqrt (n : ℝ)))) *
          cellParabola n x := by
    have hAB₀ : A₀ * B₀ = 1 / (((n : ℝ) - 1) * (2 * (n : ℝ) - 1) * Real.sqrt ((n : ℝ) - 1)) := by
      dsimp [A₀, B₀]
      rw [one_div_mul_one_div]
    have hAB₁ : A₁ * B₁ =
        (6 * (n : ℝ) - 5) / (6 * ((n : ℝ) - 1) * (n : ℝ) * (2 * (n : ℝ) - 1) * Real.sqrt (n : ℝ)) := by
      dsimp [A₁, B₁]
      rw [div_mul_div_comm, mul_one]
    rw [hAB₀, hAB₁]
    dsimp [u, v]
    ring
  rw [div_eq_mul_one_div]
  linarith

/-! ## Section 2: Unified `(√2, √3)` Rationalization `53 / (180√2) + 151 / (1260√3) ≤ 5 / 18` and the `109 / 1728` Logarithmic Cell-Defect Bound -/

/-- **Unified Rationalization of the `(√2, √3)` Terms Across Both Endpoints**:
`53 / (180 * √2) + 151 / (1260 * √3) ≤ 5 / 18` via `1393 / 985 ≤ √2` and `265 / 153 ≤ √3`
(`10441 / 50148 + 2567 / 37100 = 267857729 / 965599200 < 5 / 18`). -/
theorem fifty_three_div_one_eighty_sqrt_two_add_one_fifty_one_div_twelve_sixty_sqrt_three_le_five_eighteenths :
    53 / (180 * Real.sqrt 2) + 151 / (1260 * Real.sqrt 3) ≤ 5 / 18 := by
  have hsqrt2_ge : (1393 / 985 : ℝ) ≤ Real.sqrt 2 := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1393 / 985)]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hsqrt3_ge : (265 / 153 : ℝ) ≤ Real.sqrt 3 := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 265 / 153)]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hsqrt2_pos : 0 < 180 * Real.sqrt 2 := mul_pos (by norm_num) (Real.sqrt_pos.mpr (by norm_num))
  have hsqrt3_pos : 0 < 1260 * Real.sqrt 3 := mul_pos (by norm_num) (Real.sqrt_pos.mpr (by norm_num))
  have h1 : 53 / (180 * Real.sqrt 2) ≤ 10441 / 50148 := by
    rw [div_le_iff₀ hsqrt2_pos]
    linarith
  have h2 : 151 / (1260 * Real.sqrt 3) ≤ 2567 / 37100 := by
    rw [div_le_iff₀ hsqrt3_pos]
    linarith
  linarith

/-- For every `2 ≤ n`, the Simpson right-endpoint weight satisfies
`(6n - 5) / (6(n - 1)n(2n - 1)√n) ≤ 1 / (2(n - 1)n√n)`. -/
theorem simpson_right_weight_le_half_inv_pred_mul_sqrt {n : ℕ} (hn : 2 ≤ n) :
    (6 * (n : ℝ) - 5) / (6 * ((n : ℝ) - 1) * (n : ℝ) * (2 * (n : ℝ) - 1) * Real.sqrt (n : ℝ)) ≤
      1 / (2 * ((n : ℝ) - 1) * (n : ℝ) * Real.sqrt (n : ℝ)) := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn1_pos : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hn_pos : (0 : ℝ) < (n : ℝ) := by linarith
  have h2n1_pos : (0 : ℝ) < 2 * (n : ℝ) - 1 := by linarith
  have hsqrt_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn_pos
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hpoly :
      1 * (6 * ((n : ℝ) - 1) * (n : ℝ) * (2 * (n : ℝ) - 1) * Real.sqrt (n : ℝ)) -
        (6 * (n : ℝ) - 5) * (2 * ((n : ℝ) - 1) * (n : ℝ) * Real.sqrt (n : ℝ)) =
      4 * ((n : ℝ) - 1) * (n : ℝ) * Real.sqrt (n : ℝ) := by ring
  have hpos : 0 ≤ 4 * ((n : ℝ) - 1) * (n : ℝ) * Real.sqrt (n : ℝ) := by positivity
  linarith

/-- **Uniform Cutoff-Independent Bound `109 / 144` on the Combined Simpson Endpoint Series**:
`∑ n ∈ Finset.Icc 2 N, (1 / ((n - 1)(2n - 1)√(n - 1)) + (6n - 5) / (6(n - 1)n(2n - 1)√n)) ≤ 109 / 144`. -/
theorem sum_Icc_two_simpson_endpoint_weights_le_one_hundred_nine_one_forty_fourths (N : ℕ) :
    (∑ n ∈ Finset.Icc 2 N,
      (1 / (((n : ℝ) - 1) * (2 * (n : ℝ) - 1) * Real.sqrt ((n : ℝ) - 1)) +
        (6 * (n : ℝ) - 5) /
          (6 * ((n : ℝ) - 1) * (n : ℝ) * (2 * (n : ℝ) - 1) * Real.sqrt (n : ℝ)))) ≤ 109 / 144 := by
  let g : ℕ → ℝ := fun n =>
    1 / (((n : ℝ) - 1) * (2 * (n : ℝ) - 1) * Real.sqrt ((n : ℝ) - 1)) +
      (6 * (n : ℝ) - 5) /
        (6 * ((n : ℝ) - 1) * (n : ℝ) * (2 * (n : ℝ) - 1) * Real.sqrt (n : ℝ))
  have hg2 : g 2 = 1 / 3 + 7 / (36 * Real.sqrt 2) := by
    dsimp [g]
    norm_num
  have hg3 : g 3 = 1 / (10 * Real.sqrt 2) + 13 / (180 * Real.sqrt 3) := by
    dsimp [g]
    norm_num
  have hg4 : g 4 = 1 / (21 * Real.sqrt 3) + 19 / 1008 := by
    dsimp [g]
    have h4 : (4 : ℝ) = 2 ^ 2 := by norm_num
    rw [h4, Real.sqrt_sq (by norm_num)]
    norm_num
  have hg3_nonneg : 0 ≤ g 3 := by rw [hg3]; positivity
  have hg4_nonneg : 0 ≤ g 4 := by rw [hg4]; positivity
  have h234 : g 2 + g 3 + g 4 ≤ 1 / 3 + 5 / 18 + 1 / 48 := by
    have hsqrt23 :=
      fifty_three_div_one_eighty_sqrt_two_add_one_fifty_one_div_twelve_sixty_sqrt_three_le_five_eighteenths
    have hcomb2 :
        7 / (36 * Real.sqrt 2) + 1 / (10 * Real.sqrt 2) = 53 / (180 * Real.sqrt 2) := by
      have hne : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
      rw [div_add_div _ _ (by positivity) (by positivity),
        div_eq_div_iff (by positivity) (by positivity)]
      ring
    have hcomb3 :
        13 / (180 * Real.sqrt 3) + 1 / (21 * Real.sqrt 3) = 151 / (1260 * Real.sqrt 3) := by
      rw [div_add_div _ _ (by positivity) (by positivity),
        div_eq_div_iff (by positivity) (by positivity)]
      ring
    rw [hg2, hg3, hg4]
    linarith
  have htail5 : (∑ n ∈ Finset.Icc 5 N, g n) ≤ 1 / 8 := by
    have hle :
        (∑ n ∈ Finset.Icc 5 N, g n) ≤
          ((1 / 2) * ∑ n ∈ Finset.Icc 5 N, 1 / (((n : ℝ) - 1) ^ 2 * Real.sqrt ((n : ℝ) - 1))) +
            ∑ n ∈ Finset.Icc 5 N, 1 / (2 * ((n : ℝ) - 1) * (n : ℝ) * Real.sqrt (n : ℝ)) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun n hn => ?_
      rw [Finset.mem_Icc] at hn
      exact add_le_add
        (inv_pred_mul_two_mul_sub_one_mul_sqrt_pred_le_half_inv_sq (by omega))
        (simpson_right_weight_le_half_inv_pred_mul_sqrt (by omega))
    have h5_left := sum_Icc_five_inv_sq_pred_mul_sqrt_pred_le_one_sixth N
    have h5_right := sum_Icc_five_inv_two_mul_pred_mul_sqrt_le_one_twenty_fourth N
    linarith
  by_cases hN4 : 4 ≤ N
  · change (∑ n ∈ Finset.Icc 2 N, g n) ≤ 109 / 144
    rw [sum_Icc_eq_add_sum_Icc_succ g (by omega : 2 ≤ N),
      sum_Icc_eq_add_sum_Icc_succ g (by omega : 3 ≤ N),
      sum_Icc_eq_add_sum_Icc_succ g hN4]
    linarith
  · by_cases hN3 : 3 ≤ N
    · have hN_eq : N = 3 := by omega
      subst hN_eq
      change (∑ n ∈ Finset.Icc 2 3, g n) ≤ 109 / 144
      rw [sum_Icc_eq_add_sum_Icc_succ g (by omega : 2 ≤ 3),
        Finset.Icc_self, Finset.sum_singleton]
      linarith
    · by_cases hN2 : 2 ≤ N
      · have hN_eq : N = 2 := by omega
        subst hN_eq
        change (∑ n ∈ Finset.Icc 2 2, g n) ≤ 109 / 144
        rw [Finset.Icc_self, Finset.sum_singleton]
        linarith
      · rw [Finset.Icc_eq_empty hN2, Finset.sum_empty]
        norm_num

/-- **Cutoff-Independent `-(109 / 1728) (spectralSecondMoment f.1 + ∫ ‖f.1‖²) ≤ secantNumeratorCellDefect f.1 N`**: -/
theorem neg_one_hundred_nine_seventeen_twenty_eighths_spectralSecondMoment_add_l2_le_secantNumeratorCellDefect
    (f : WeilTestFn)
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2))
    (N : ℕ) :
    -(109 / 1728) * (spectralSecondMoment f.1 + ∫ u : ℝ, ‖f.1 u‖ ^ 2) ≤
      secantNumeratorCellDefect f.1 N := by
  let M := spectralSecondMoment f.1 + ∫ u : ℝ, ‖f.1 u‖ ^ 2
  have hnorm_nonneg : 0 ≤ ∫ u : ℝ, ‖f.1 u‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hM_nonneg : 0 ≤ M := add_nonneg (spectralSecondMoment_nonneg f.1) hnorm_nonneg
  let c₀ : ℕ → ℝ := fun n =>
    M * (1 / (((n : ℝ) - 1) * (2 * (n : ℝ) - 1) * Real.sqrt ((n : ℝ) - 1)))
  let c₁ : ℕ → ℝ := fun n =>
    M * ((6 * (n : ℝ) - 5) /
      (6 * ((n : ℝ) - 1) * (n : ℝ) * (2 * (n : ℝ) - 1) * Real.sqrt (n : ℝ)))
  have hsq := integrable_paperFT_norm_sq f
  have hplanch := one_div_two_pi_mul_integral_paperFT_norm_sq_mul_two_eq f
  have hcos : ∀ t : ℝ, Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * cosLogProfile r t) :=
    integrable_paperFT_norm_sq_mul_two_cosLogProfile f
  have hcell_bound :
      -(∑ n ∈ Finset.Icc 2 N, (c₀ n + c₁ n) / 12) ≤ secantNumeratorCellDefect f.1 N := by
    rw [secantNumeratorCellDefect, ← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun n hn => ?_
    have hn_mem := Finset.mem_Icc.mp hn
    have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_mem.1
    have hle : (n : ℝ) - 1 ≤ (n : ℝ) := by linarith
    have hinv : ContinuousOn (fun x : ℝ => (Real.sqrt x)⁻¹) (uIcc ((n : ℝ) - 1) (n : ℝ)) := by
      refine ContinuousOn.inv₀ Real.continuous_sqrt.continuousOn fun x hx => ?_
      rw [uIcc_of_le hle] at hx
      exact ne_of_gt (Real.sqrt_pos.mpr (by linarith [hx.1]))
    have hnum_int : IntervalIntegrable
        (fun x : ℝ =>
          (weilSymmetricLogNumerator f.1 x -
            cellSecant (weilSymmetricLogNumerator f.1) n x) / Real.sqrt x)
        volume ((n : ℝ) - 1) (n : ℝ) := by
      have hnum : ContinuousOn
          (fun x : ℝ => weilSymmetricLogNumerator f.1 x)
          (uIcc ((n : ℝ) - 1) (n : ℝ)) := by
        refine (continuousOn_weilSymmetricLogNumerator f).mono fun x hx => ?_
        rw [uIcc_of_le hle] at hx
        rw [mem_Ici]
        linarith [hx.1]
      have hsec : ContinuousOn
          (fun x : ℝ => cellSecant (weilSymmetricLogNumerator f.1) n x)
          (uIcc ((n : ℝ) - 1) (n : ℝ)) := by
        unfold cellSecant
        exact ((continuousOn_const.sub continuousOn_id).mul continuousOn_const).add
          ((continuousOn_id.sub continuousOn_const).mul continuousOn_const)
      simp_rw [div_eq_mul_inv]
      exact ((hnum.sub hsec).mul hinv).intervalIntegrable
    have hpoly_int : IntervalIntegrable
        (fun x : ℝ => -((c₀ n * ((n : ℝ) - x) + c₁ n * (x - ((n : ℝ) - 1))) * cellParabola n x))
        volume ((n : ℝ) - 1) (n : ℝ) := by
      unfold cellParabola
      exact ((((continuousOn_const.mul (continuousOn_const.sub continuousOn_id)).add
        (continuousOn_const.mul (continuousOn_id.sub continuousOn_const))).mul
        ((continuousOn_id.sub continuousOn_const).mul
          (continuousOn_const.sub continuousOn_id))).neg).intervalIntegrable
    have hpoly_eval :
        (∫ x in ((n : ℝ) - 1)..(n : ℝ),
          -((c₀ n * ((n : ℝ) - x) + c₁ n * (x - ((n : ℝ) - 1))) * cellParabola n x)) =
        -((c₀ n + c₁ n) / 12) := by
      rw [intervalIntegral.integral_neg, integral_linear_mul_cellParabola_eq_add_div_twelve]
    rw [← hpoly_eval]
    refine intervalIntegral.integral_mono_on hle hpoly_int hnum_int fun x hx => ?_
    have hlog_cmp :
        |weilSymmetricLogNumerator f.1 x - cellSecant (weilSymmetricLogNumerator f.1) n x| ≤
          M * (Real.log x - cellSecant Real.log n x) := by
      have hint_diff : Integrable fun r : ℝ =>
          ‖paperFT f.1 r‖ ^ 2 * (2 * (cosLogProfile r x - cellSecant (cosLogProfile r) n x)) := by
        have hlin :
            (fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * (cosLogProfile r x - cellSecant (cosLogProfile r) n x))) =
            fun r : ℝ =>
              ‖paperFT f.1 r‖ ^ 2 * (2 * cosLogProfile r x) -
                (((n : ℝ) - x) * (‖paperFT f.1 r‖ ^ 2 * (2 * cosLogProfile r ((n : ℝ) - 1))) +
                  (x - ((n : ℝ) - 1)) * (‖paperFT f.1 r‖ ^ 2 * (2 * cosLogProfile r (n : ℝ)))) := by
          ext r
          unfold cellSecant
          ring
        rw [hlin]
        exact (hcos x).sub (((hcos ((n : ℝ) - 1)).const_mul _).add ((hcos (n : ℝ)).const_mul _))
      rw [weilSymmetricLogNumerator_sub_cellSecant_eq_spectral f n x,
        abs_mul, abs_of_pos (div_pos one_pos Real.two_pi_pos)]
      have hrhs_eq :
          M * (Real.log x - cellSecant Real.log n x) =
            (1 / (2 * π)) * ∫ r : ℝ,
              (‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2) + (1 / 2) * (‖paperFT f.1 r‖ ^ 2 * 2)) *
                (Real.log x - cellSecant Real.log n x) := by
        have hplanch' : (∫ u : ℝ, ‖f.1 u‖ ^ 2) =
            (1 / (2 * π)) * ((1 / 2) * ∫ r : ℝ, ‖paperFT f.1 r‖ ^ 2 * 2) := by
          linarith [hplanch]
        dsimp [M]
        unfold spectralSecondMoment
        rw [integral_mul_const, integral_add hint2 ((hsq.mul_const 2).const_mul (1 / 2)),
          integral_const_mul, hplanch']
        ring
      rw [hrhs_eq]
      refine mul_le_mul_of_nonneg_left (abs_integral_le_integral_abs.trans ?_)
        (div_nonneg zero_le_one Real.two_pi_pos.le)
      refine integral_mono hint_diff.abs
        ((hint2.add ((hsq.mul_const 2).const_mul (1 / 2))).mul_const _) fun r => ?_
      dsimp
      rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg _), abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      have ht_pos : ∀ t ∈ Icc ((n : ℝ) - 1) (n : ℝ), 0 < t := fun t ht => by linarith [ht.1]
      have hcmp := abs_sub_cellSecant_le_mul_log_sub_cellSecant_of_abs_deriv2_le_div_sq hn_mem.1
        (fun t ht => hasDerivAt_cosLogProfile r (ht_pos t ht))
        (fun t ht => hasDerivAt_cosLogProfileDeriv r (ht_pos t ht))
        (fun t ht => abs_cosLogProfileDeriv2_le_sq_add_half_div_sq r (ht_pos t ht)) hx
      have hweight : 0 ≤ ‖paperFT f.1 r‖ ^ 2 * 2 := mul_nonneg (sq_nonneg _) (by norm_num)
      have hmul := mul_le_mul_of_nonneg_left hcmp hweight
      linarith
    have hdiv_cmp :
        -(M * ((Real.log x - cellSecant Real.log n x) / Real.sqrt x)) ≤
          (weilSymmetricLogNumerator f.1 x - cellSecant (weilSymmetricLogNumerator f.1) n x) /
            Real.sqrt x := by
      have hlow := (abs_le.mp hlog_cmp).1
      have hdiv := div_le_div_of_nonneg_right hlow (Real.sqrt_nonneg x)
      linarith [mul_div_assoc M (Real.log x - cellSecant Real.log n x) (Real.sqrt x),
        neg_div (Real.sqrt x) (M * (Real.log x - cellSecant Real.log n x))]
    have hlin_par := mul_le_mul_of_nonneg_left
      (log_sub_cellSecant_log_div_sqrt_le_simpson_linear_mul_cellParabola hn_mem.1 hx) hM_nonneg
    have halg :
        M * ((((n : ℝ) - x) * (1 / (((n : ℝ) - 1) * (2 * (n : ℝ) - 1) * Real.sqrt ((n : ℝ) - 1))) +
          (x - ((n : ℝ) - 1)) *
            ((6 * (n : ℝ) - 5) /
              (6 * ((n : ℝ) - 1) * (n : ℝ) * (2 * (n : ℝ) - 1) * Real.sqrt (n : ℝ)))) *
          cellParabola n x) =
        (c₀ n * ((n : ℝ) - x) + c₁ n * (x - ((n : ℝ) - 1))) * cellParabola n x := by
      dsimp [c₀, c₁]
      ring
    linarith
  have hsum_le :
      (∑ n ∈ Finset.Icc 2 N, (c₀ n + c₁ n) / 12) ≤ (109 / 1728) * M := by
    have hcongr :
        (∑ n ∈ Finset.Icc 2 N, (c₀ n + c₁ n) / 12) =
          (M / 12) * ∑ n ∈ Finset.Icc 2 N,
            (1 / (((n : ℝ) - 1) * (2 * (n : ℝ) - 1) * Real.sqrt ((n : ℝ) - 1)) +
              (6 * (n : ℝ) - 5) /
                (6 * ((n : ℝ) - 1) * (n : ℝ) * (2 * (n : ℝ) - 1) * Real.sqrt (n : ℝ))) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      dsimp [c₀, c₁]
      ring
    rw [hcongr]
    have h109 := sum_Icc_two_simpson_endpoint_weights_le_one_hundred_nine_one_forty_fourths N
    have hmul := mul_le_mul_of_nonneg_left h109 (by linarith : 0 ≤ M / 12)
    linarith
  linarith

/-! ## Section 3: The `(6367 / 8640) ∫ ‖f.1‖² - (109 / 1728) spectralSecondMoment f.1` Coercivity Law, the `(1403 / 1728) ∫ ‖f.1‖² - (109 / 1728) spectralSecondMoment f.1` Prime-Blind Cone Law, and Unconditional `markovEnergy ≥ 0` up to `spectralSecondMoment F ≤ (6367 / 545 - δ) ∫ ‖F‖² > 11.682 ∫ ‖F‖²` -/

/-- **Pure Second-Moment `(6367 / 8640) ∫ ‖f.1‖² - (109 / 1728) spectralSecondMoment f.1` Lower Bound
on `rightCellQuadratureDefect` (Critical Ratio `6367 / 545 > 11.6825`)**: -/
theorem six_thousand_three_hundred_sixty_seven_eighty_six_fortieths_l2_sub_one_hundred_nine_seventeen_twenty_eighths_spectralSecondMoment_le_rightCellQuadratureDefect
    (f : WeilTestFn)
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2))
    {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest f.1 f.1 (Real.log N) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log N) = 0)
    (hN : ∀ n : ℕ, N < n →
      EF.weilTest f.1 f.1 (Real.log n) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log n) = 0) :
    (6367 / 8640) * (∫ u : ℝ, ‖f.1 u‖ ^ 2) - (109 / 1728) * spectralSecondMoment f.1 ≤
      rightCellQuadratureDefect (weilContinuumLogProfile f.1) N := by
  have h1 := four_fifths_l2_add_secantNumerator_le_rightCellQuadratureDefect f hN1 hN0 hN
  have h2 := neg_one_hundred_nine_seventeen_twenty_eighths_spectralSecondMoment_add_l2_le_secantNumeratorCellDefect
    f hint2 N
  linarith

/-- **Prime-Blind Cone `(1403 / 1728) ∫ ‖f.1‖² - (109 / 1728) spectralSecondMoment f.1` Lower Bound
on `rightCellQuadratureDefect` (Critical Ratio `1403 / 109 > 12.8715`)**:
on the Prime-Blind Cone (`logVector f = 0`), absorbing `(109 / 1728) * ∫ ‖f.1‖²` into Module 52's
`(7 / 8) * ∫ ‖f.1‖² = (1512 / 1728) * ∫ ‖f.1‖²` origin surplus leaves `1403 / 1728`! -/
theorem one_thousand_four_hundred_three_seventeen_twenty_eighths_l2_sub_one_hundred_nine_seventeen_twenty_eighths_spectralSecondMoment_le_rightCellQuadratureDefect_of_logVector_eq_zero
    (f : WeilTestFn) (hblind : logVector f = 0)
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2))
    {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest f.1 f.1 (Real.log N) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log N) = 0)
    (hN : ∀ n : ℕ, N < n →
      EF.weilTest f.1 f.1 (Real.log n) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log n) = 0) :
    (1403 / 1728) * (∫ u : ℝ, ‖f.1 u‖ ^ 2) - (109 / 1728) * spectralSecondMoment f.1 ≤
      rightCellQuadratureDefect (weilContinuumLogProfile f.1) N := by
  have h1 := seven_eighths_l2_add_secantNumerator_le_rightCellQuadratureDefect_of_logVector_eq_zero
    f hblind hN1 hN0 hN
  have h2 := neg_one_hundred_nine_seventeen_twenty_eighths_spectralSecondMoment_add_l2_le_secantNumeratorCellDefect
    f hint2 N
  linarith

/-- **Unconditional `0 ≤ markovEnergy F` on the Primitive Hyperplane whenever
`spectralSecondMoment F ≤ (6367 / 545 - δ) ∫ ‖F‖² > 11.682 ∫ ‖F‖²`**: -/
theorem markovEnergy_ofReal_nonneg_of_spectralSecondMoment_le_six_thousand_three_hundred_sixty_seven_five_forty_fifths_of_cosh_zero
    (m : ℕ) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hcosh : coshHalfMoment f = 0)
    (hint2 : Integrable fun r : ℝ => ‖paperFT (realWeilTestFn f hf hfc).1 r‖ ^ 2 * (2 * r ^ 2))
    {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log N) = 0 ∧
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log N) = 0)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log x) = 0 ∧
        EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log x) = 0)
    (hdiff : ∀ n ∈ Finset.Icc 2 N,
      0 ≤ iteratedForwardDiff m (logValue (realWeilTestFn f hf hfc).1) n)
    {δ : ℝ} (hδ : 0 < δ)
    (hsec_bound : spectralSecondMoment (realWeilTestFn f hf hfc).1 ≤
      (6367 / 545 - δ) * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) :
    0 ≤ markovEnergy (realWeilTestFn f hf hfc).1 := by
  let θ := max (max 1 (Real.log (N : ℝ))) (3456 / (109 * δ))
  have hθ1 : 1 ≤ θ := (le_max_left 1 (Real.log (N : ℝ))).trans (le_max_left _ _)
  have hθ0 : 0 ≤ θ := by linarith
  have hθlog : Real.log (N : ℝ) ≤ θ :=
    (le_max_right 1 (Real.log (N : ℝ))).trans (le_max_left _ _)
  have h109δ : 0 < 109 * δ := by linarith
  have hθδ_le : 3456 / (109 * δ) ≤ θ := le_max_right _ _
  have hθδ : 3456 ≤ θ * (109 * δ) := (div_le_iff₀ h109δ).mp hθδ_le
  have hbase := four_fifths_secantNumerator_upgraded_l2_le_markovEnergy_of_cosh_zero
    m hθ0 hf hfc hcosh hN1 hθlog hN0 hN hdiff
  have hnum := neg_one_hundred_nine_seventeen_twenty_eighths_spectralSecondMoment_add_l2_le_secantNumeratorCellDefect
    (realWeilTestFn f hf hfc) hint2 N
  have hθnum := mul_le_mul_of_nonneg_left hnum hθ0
  have hθbound := mul_le_mul_of_nonneg_left hsec_bound (by positivity : 0 ≤ (109 / 1728) * θ)
  have hnorm_nonneg : 0 ≤ ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  have hθδ_norm := mul_le_mul_of_nonneg_right hθδ hnorm_nonneg
  have hres_nonneg : 0 ≤ (θ - 1) * bochnerResolventEnergy
      (EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1) :=
    mul_nonneg (by linarith) (bochnerResolventEnergy_weilTest_nonneg _)
  have hsinh_nonneg : 0 ≤ 2 * θ * sinhHalfMoment f ^ 2 := by positivity
  linarith

end RHTower

end
