import GaloisForLFunctions.RHTower.MarkovLogDefectComparisonAndTwoFiftySevenThirtyFirstsPBAP

/-!
# Two-Endpoint Linear-Parabola Envelope for `log x - cellSecant log n x`, Algebraic Secant Convexity of `1 / √x`, and Coercivity up to `spectralSecondMoment / L² < 2111 / 193 > 10.937`

In Module 56, we proved the Exact Logarithmic Secant Comparison Theorem:
`|g x - cellSecant g n x| ≤ A * (log x - cellSecant log n x)` whenever `|g'' t| ≤ A / t ^ 2` on
`[n - 1, n]`. However, when bounding the cell integral
`∫_{n-1}^n ((log x - cellSecant log n x) / √x) dx`, Module 56 replaced both factors by their
worst-case left-endpoint values at `x = n - 1`:
- `log x - cellSecant log n x ≤ (1 / ((n - 1)(2n - 1))) * cellParabola n x`, and
- `1 / √x ≤ 1 / √(n - 1)`.

On the dominant cell `n = 2` (`[1, 2]`), the slope-difference envelope drops from `1 / 3` at `x = 1`
to `1 / 4` at `x = 2`, while `1 / √x` drops from `1` at `x = 1` to `1 / √2` at `x = 2`. Because
`cellParabola n x = (x - (n - 1))(n - x)` is symmetric about the cell midpoint `x = n - 1 / 2`,
any linear envelope `c₀ (n - x) + c₁ (x - (n - 1))` integrates against `cellParabola n x` to
`(c₀ + c₁) / 12` — averaging the left and right endpoint values rather than taking the left-endpoint
maximum!

In this module, we establish this two-endpoint cubic-parabola quadrature refinement:

1. **Section 1 (Two-Endpoint Linear-Parabola Envelope for `log x - cellSecant log n x`, Algebraic
   Secant Convexity of `1 / √x`, and the `(c₀ + c₁) / 12` Quartic Cell Integral):**
   - We prove (`slope_bound_le_linear_of_mem_Ioo` and `log_sub_cellSecant_log_le_linear_mul_cellParabola`)
     that for all `2 ≤ n` and `x ∈ [n - 1, n]`,
     `log x - cellSecant log n x ≤ ((n - x) / ((n - 1)(2n - 1)) + (x - (n - 1)) / (2(n - 1)n)) * cellParabola n x`.
   - We prove (`inv_sqrt_le_cellSecant_inv_sqrt`) by pure polynomial factorization in
     `a = √(n - 1)`, `b = √n`, `s = √x` (`(b - a)(s - a)(b - s)(a b + s(a + b)) ≥ 0`) that
     `1 / √x ≤ (n - x) / √(n - 1) + (x - (n - 1)) / √n` on `[n - 1, n]`.
   - Combining these via the Chebyshev secant product inequality (`chebyshev_secant_mul_le`) and
     integrating against `cellParabola n x` via the odd-symmetry vanishing identity
     `∫_{n-1}^n (2n - 1 - 2x) * cellParabola n x = 0` (`integral_linear_mul_cellParabola_eq_add_div_twelve`)
     replaces `1 / (6 (n - 1)(2n - 1) √(n - 1))` by
     `(1 / 12) * (1 / ((n - 1)(2n - 1) √(n - 1)) + 1 / (2(n - 1)n √n))`.

2. **Section 2 (The `23 / 80` Right-Endpoint Series `∑_{n=2}^N 1 / (2(n - 1)n√n) ≤ 23 / 80` and
   the `193 / 2880` Logarithmic Cell-Defect Bound):**
   - Using `1 / (2 m (m + 1) √(m + 1)) ≤ (1 / 3) * (1 / (m √m) - 1 / ((m + 1) √(m + 1)))` (`m ≥ 1`),
     the `n ≥ 5` tail of `1 / (2(n - 1)n√n)` telescopes to at most `(1 / 3) / (4√4) = 1 / 24`, the
     `n = 4` term is the exact rational `1 / (2 · 3 · 4 · √4) = 1 / 48`, and the `n = 2, 3` terms
     satisfy `1 / (4√2) + 1 / (12√3) ≤ 9 / 40`, yielding
     `∑_{n=2}^N 1 / (2(n - 1)n√n) ≤ 9 / 40 + 1 / 48 + 1 / 24 = 23 / 80`.
   - Averaging with Module 56's `31 / 60` bound gives the curvature constant
     `(1 / 12) * (31 / 60 + 23 / 80) = 193 / 2880 ≈ 0.06701`
     (`neg_one_ninety_three_twenty_eight_eightieths_spectralSecondMoment_add_l2_le_secantNumeratorCellDefect`):
     `-(193 / 2880) * (spectralSecondMoment f.1 + ∫ u, ‖f.1 u‖ ^ 2) ≤ secantNumeratorCellDefect f.1 N`!

3. **Section 3 (The `(2111 / 2880) ∫ ‖f.1‖² - (193 / 2880) spectralSecondMoment f.1` Coercivity Law,
   the `(2327 / 2880) ∫ ‖f.1‖² - (193 / 2880) spectralSecondMoment f.1` Prime-Blind Cone Law, and
   Unconditional `markovEnergy ≥ 0` up to `spectralSecondMoment F ≤ (2111 / 193 - δ) ∫ ‖F‖² > 10.937 ∫ ‖F‖²`):**
   - Since both `5` and `8` divide `2880` (`4 / 5 = 2304 / 2880` and `7 / 8 = 2520 / 2880`),
     absorbing `(193 / 2880) * ∫ ‖f.1‖²` yields:
     - `(2111 / 2880) * ∫ ‖f.1‖² - (193 / 2880) * spectralSecondMoment f.1 ≤ rightCellQuadratureDefect (weilContinuumLogProfile f.1) N`
       (critical ratio **`2111 / 193 > 10.9378`**, crossing `10` for the first time!), and
     - on the Prime-Blind Cone (`logVector f = 0`),
       `(2327 / 2880) * ∫ ‖f.1‖² - (193 / 2880) * spectralSecondMoment f.1 ≤ rightCellQuadratureDefect (weilContinuumLogProfile f.1) N`
       (critical ratio **`2327 / 193 > 12.0569`**, crossing `12` for the first time!).
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

/-! ## Section 1: Two-Endpoint Linear-Parabola Envelope for `log x - cellSecant log n x`, Algebraic Secant Convexity of `1 / √x`, and the `(c₀ + c₁) / 12` Quartic Cell Integral -/

/-- **Two-Endpoint Linear Envelope for the Hermite–Hadamard Slope Difference on `(n - 1, n)`**:
for `2 ≤ n` and `x ∈ (n - 1, n)`,
`(1 / 2) * (1 / (n - 1) + 1 / x) - 2 / (x + n) ≤ ((n - x) / ((n - 1)(2n - 1)) + (x - (n - 1)) / (2(n - 1)n))`. -/
theorem slope_bound_le_linear_of_mem_Ioo
    {n : ℕ} (hn : 2 ≤ n) {x : ℝ} (hx1 : (n : ℝ) - 1 < x) (hx2 : x < (n : ℝ)) :
    (1 / 2) * (1 / ((n : ℝ) - 1) + 1 / x) - 2 / (x + (n : ℝ)) ≤
      ((n : ℝ) - x) * (1 / (((n : ℝ) - 1) * (2 * (n : ℝ) - 1))) +
        (1 / 2) * (x - ((n : ℝ) - 1)) * (1 / (((n : ℝ) - 1) * (n : ℝ))) := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn1_pos : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hn_pos : (0 : ℝ) < (n : ℝ) := by linarith
  have hx_pos : 0 < x := hn1_pos.trans hx1
  have h2n1_pos : (0 : ℝ) < 2 * (n : ℝ) - 1 := by linarith
  have hxn_pos : 0 < x + (n : ℝ) := by linarith
  have hx1_pos : 0 < x - ((n : ℝ) - 1) := sub_pos.mpr hx1
  have hx2_pos : 0 < (n : ℝ) - x := sub_pos.mpr hx2
  have hpf1 : 1 / ((n : ℝ) - 1) - 2 / (2 * (n : ℝ) - 1) =
      1 / (((n : ℝ) - 1) * (2 * (n : ℝ) - 1)) := by
    rw [div_sub_div 1 2 hn1_pos.ne' h2n1_pos.ne']
    ring
  have hpf2 : 1 / ((n : ℝ) - 1) - 1 / (n : ℝ) =
      1 / (((n : ℝ) - 1) * (n : ℝ)) := by
    rw [div_sub_div 1 1 hn1_pos.ne' hn_pos.ne']
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
  have hrhs_decomp :
      ((n : ℝ) - x) * (1 / ((n : ℝ) - 1) - 2 / (2 * (n : ℝ) - 1)) +
        (1 / 2) * (x - ((n : ℝ) - 1)) * (1 / ((n : ℝ) - 1) - 1 / (n : ℝ)) =
      (1 / 2) * (1 / ((n : ℝ) - 1)) +
        (1 / 2) * (((n : ℝ) - x) / ((n : ℝ) - 1) + (x - ((n : ℝ) - 1)) / (n : ℝ)) -
        ((2 * ((n : ℝ) - x)) / (2 * (n : ℝ) - 1) + (x - ((n : ℝ) - 1)) / (n : ℝ)) := by
    ring
  have hden_cmp :
      2 / (((2 * (n : ℝ) - 1) * (n : ℝ)) * (x + (n : ℝ))) ≤
        1 / ((((n : ℝ) - 1) * (n : ℝ)) * x) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hpoly :
        1 * (((2 * (n : ℝ) - 1) * (n : ℝ)) * (x + (n : ℝ))) -
          2 * ((((n : ℝ) - 1) * (n : ℝ)) * x) =
        (n : ℝ) * ((2 * (n : ℝ) - 1) * (n : ℝ) + x) := by ring
    have hpos : 0 ≤ (n : ℝ) * ((2 * (n : ℝ) - 1) * (n : ℝ) + x) := by positivity
    linarith
  have hpar_nonneg : 0 ≤ (1 / 2) * cellParabola n x :=
    mul_nonneg (by norm_num) (cellParabola_nonneg_of_mem_Icc ⟨hx1.le, hx2.le⟩)
  have hmul := mul_le_mul_of_nonneg_left hden_cmp hpar_nonneg
  have hmul_lhs :
      (1 / 2) * cellParabola n x * (2 / (((2 * (n : ℝ) - 1) * (n : ℝ)) * (x + (n : ℝ)))) =
        cellParabola n x / (((2 * (n : ℝ) - 1) * (n : ℝ)) * (x + (n : ℝ))) := by ring
  have hmul_rhs :
      (1 / 2) * cellParabola n x * (1 / ((((n : ℝ) - 1) * (n : ℝ)) * x)) =
        (1 / 2) * (cellParabola n x / ((((n : ℝ) - 1) * (n : ℝ)) * x)) := by ring
  rw [← hpf1, ← hpf2, hrhs_decomp, h1_sum, h2_sum]
  linarith

/-- **Two-Endpoint Linear-Parabola Bound for `Real.log x - cellSecant Real.log n x` on `[n - 1, n]`**:
for `2 ≤ n` and `x ∈ Icc (n - 1) n`,
`Real.log x - cellSecant Real.log n x ≤ (((n - x) / ((n - 1)(2n - 1)) + (x - (n - 1)) / (2(n - 1)n))) * cellParabola n x`. -/
theorem log_sub_cellSecant_log_le_linear_mul_cellParabola
    {n : ℕ} (hn : 2 ≤ n) {x : ℝ} (hx : x ∈ Icc ((n : ℝ) - 1) (n : ℝ)) :
    Real.log x - cellSecant Real.log n x ≤
      (((n : ℝ) - x) * (1 / (((n : ℝ) - 1) * (2 * (n : ℝ) - 1))) +
        (1 / 2) * (x - ((n : ℝ) - 1)) * (1 / (((n : ℝ) - 1) * (n : ℝ)))) *
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
        (1 / 2) * (1 / ((n : ℝ) - 1) + 1 / x) := by
    rw [div_le_iff₀ hx1_pos]
    have htrap := log_sub_log_le_half_mul_inv_add_inv hn1_pos hx.1
    linarith
  have hright_slope :
      2 / (x + (n : ℝ)) ≤ (Real.log (n : ℝ) - Real.log x) / ((n : ℝ) - x) := by
    rw [le_div_iff₀ hx2_pos]
    have hmid := two_mul_sub_div_add_le_log_sub_log hx_pos hx.2
    have heq : 2 / (x + (n : ℝ)) * ((n : ℝ) - x) = 2 * ((n : ℝ) - x) / (x + (n : ℝ)) := by ring
    linarith
  have hlin := slope_bound_le_linear_of_mem_Ioo hn hx1 hx2
  have hslope_le :
      (Real.log x - Real.log ((n : ℝ) - 1)) / (x - ((n : ℝ) - 1)) -
        (Real.log (n : ℝ) - Real.log x) / ((n : ℝ) - x) ≤
      ((n : ℝ) - x) * (1 / (((n : ℝ) - 1) * (2 * (n : ℝ) - 1))) +
        (1 / 2) * (x - ((n : ℝ) - 1)) * (1 / (((n : ℝ) - 1) * (n : ℝ))) := by
    linarith
  rw [sub_cellSecant_eq_cellParabola_mul_slope_diff Real.log n ⟨hx1, hx2⟩, mul_comm]
  exact mul_le_mul_of_nonneg_right hslope_le (cellParabola_nonneg_of_mem_Icc hx)

/-- **Algebraic Secant Convexity of `1 / √x` on `[n - 1, n]`**:
for `2 ≤ n` and `x ∈ Icc (n - 1) n`,
`1 / √x ≤ (n - x) * (1 / √(n - 1)) + (x - (n - 1)) * (1 / √n)`. -/
theorem inv_sqrt_le_cellSecant_inv_sqrt
    {n : ℕ} (hn : 2 ≤ n) {x : ℝ} (hx : x ∈ Icc ((n : ℝ) - 1) (n : ℝ)) :
    1 / Real.sqrt x ≤
      ((n : ℝ) - x) * (1 / Real.sqrt ((n : ℝ) - 1)) +
        (x - ((n : ℝ) - 1)) * (1 / Real.sqrt (n : ℝ)) := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn1_pos : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hn_pos : (0 : ℝ) < (n : ℝ) := by linarith
  have hx_pos : 0 < x := hn1_pos.trans_le hx.1
  let a := Real.sqrt ((n : ℝ) - 1)
  let b := Real.sqrt (n : ℝ)
  let s := Real.sqrt x
  have ha_pos : 0 < a := Real.sqrt_pos.mpr hn1_pos
  have hb_pos : 0 < b := Real.sqrt_pos.mpr hn_pos
  have hs_pos : 0 < s := Real.sqrt_pos.mpr hx_pos
  have ha_le_s : a ≤ s := Real.sqrt_le_sqrt hx.1
  have hs_le_b : s ≤ b := Real.sqrt_le_sqrt hx.2
  have ha_le_b : a ≤ b := Real.sqrt_le_sqrt (by linarith)
  have ha_sq : a ^ 2 = (n : ℝ) - 1 := Real.sq_sqrt hn1_pos.le
  have hb_sq : b ^ 2 = (n : ℝ) := Real.sq_sqrt hn_pos.le
  have hs_sq : s ^ 2 = x := Real.sq_sqrt hx_pos.le
  have hsum :
      ((n : ℝ) - x) * (1 / a) + (x - ((n : ℝ) - 1)) * (1 / b) =
        (((n : ℝ) - x) * b + (x - ((n : ℝ) - 1)) * a) / (a * b) := by
    have h1 : ((n : ℝ) - x) * (1 / a) + (x - ((n : ℝ) - 1)) * (1 / b) =
        ((n : ℝ) - x) / a + (x - ((n : ℝ) - 1)) / b := by ring
    rw [h1, div_add_div _ _ ha_pos.ne' hb_pos.ne']
    ring
  change 1 / s ≤ ((n : ℝ) - x) * (1 / a) + (x - ((n : ℝ) - 1)) * (1 / b)
  rw [hsum, div_le_div_iff₀ hs_pos (mul_pos ha_pos hb_pos)]
  have hba_sq : b ^ 2 - a ^ 2 = 1 := by linarith [ha_sq, hb_sq]
  have hpoly :
      (((n : ℝ) - x) * b + (x - ((n : ℝ) - 1)) * a) * s - 1 * (a * b) =
        (b - a) * (s - a) * (b - s) * (a + b + s) := by
    rw [← ha_sq, ← hb_sq, ← hs_sq, ← hba_sq]
    ring
  have hprod_nonneg : 0 ≤ (b - a) * (s - a) * (b - s) * (a + b + s) :=
    mul_nonneg (mul_nonneg (mul_nonneg (sub_nonneg.mpr ha_le_b) (sub_nonneg.mpr ha_le_s))
      (sub_nonneg.mpr hs_le_b)) (by positivity)
  linarith

/-- **Chebyshev Secant Product Inequality**:
for any similarly ordered `A₁ ≤ A₀`, `B₁ ≤ B₀` and nonnegative weights `0 ≤ u, v` with `u + v = 1`,
`(A₀ * u + A₁ * v) * (B₀ * u + B₁ * v) ≤ A₀ * B₀ * u + A₁ * B₁ * v`. -/
theorem chebyshev_secant_mul_le
    {A₀ A₁ B₀ B₁ u v : ℝ} (hA : A₁ ≤ A₀) (hB : B₁ ≤ B₀)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u + v = 1) :
    (A₀ * u + A₁ * v) * (B₀ * u + B₁ * v) ≤ A₀ * B₀ * u + A₁ * B₁ * v := by
  have hid :
      (A₀ * B₀ * u + A₁ * B₁ * v) * (u + v) - (A₀ * u + A₁ * v) * (B₀ * u + B₁ * v) =
        (A₀ - A₁) * (B₀ - B₁) * u * v := by ring
  have hnonneg : 0 ≤ (A₀ - A₁) * (B₀ - B₁) * u * v :=
    mul_nonneg (mul_nonneg (mul_nonneg (sub_nonneg.mpr hA) (sub_nonneg.mpr hB)) hu) hv
  rw [huv, mul_one] at hid
  linarith

/-- **Pointwise Two-Endpoint Linear-Parabola Bound on `(Real.log x - cellSecant Real.log n x) / √x`**:
for `2 ≤ n` and `x ∈ Icc (n - 1) n`,
`(Real.log x - cellSecant Real.log n x) / √x ≤ (((n - x) / ((n - 1)(2n - 1)√(n - 1)) + (x - (n - 1)) / (2(n - 1)n√n))) * cellParabola n x`. -/
theorem log_sub_cellSecant_log_div_sqrt_le_linear_mul_cellParabola
    {n : ℕ} (hn : 2 ≤ n) {x : ℝ} (hx : x ∈ Icc ((n : ℝ) - 1) (n : ℝ)) :
    (Real.log x - cellSecant Real.log n x) / Real.sqrt x ≤
      (((n : ℝ) - x) * (1 / (((n : ℝ) - 1) * (2 * (n : ℝ) - 1) * Real.sqrt ((n : ℝ) - 1))) +
        (x - ((n : ℝ) - 1)) * (1 / (2 * ((n : ℝ) - 1) * (n : ℝ) * Real.sqrt (n : ℝ)))) *
        cellParabola n x := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn1_pos : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hn_pos : (0 : ℝ) < (n : ℝ) := by linarith
  have h2n1_pos : (0 : ℝ) < 2 * (n : ℝ) - 1 := by linarith
  have hlog := log_sub_cellSecant_log_le_linear_mul_cellParabola hn hx
  have hsqrt := inv_sqrt_le_cellSecant_inv_sqrt hn hx
  let u := (n : ℝ) - x
  let v := x - ((n : ℝ) - 1)
  have hu : 0 ≤ u := sub_nonneg.mpr hx.2
  have hv : 0 ≤ v := sub_nonneg.mpr hx.1
  have huv : u + v = 1 := by dsimp [u, v]; ring
  let A₀ := 1 / (((n : ℝ) - 1) * (2 * (n : ℝ) - 1))
  let A₁ := 1 / (2 * ((n : ℝ) - 1) * (n : ℝ))
  let B₀ := 1 / Real.sqrt ((n : ℝ) - 1)
  let B₁ := 1 / Real.sqrt (n : ℝ)
  have hA₁_eq : (1 / 2) * (1 / (((n : ℝ) - 1) * (n : ℝ))) = A₁ := by
    dsimp [A₁]
    rw [one_div_mul_one_div, mul_assoc]
  have hA_le : A₁ ≤ A₀ := by
    dsimp [A₀, A₁]
    refine one_div_le_one_div_of_le (by positivity) (by nlinarith)
  have hB_le : B₁ ≤ B₀ := by
    dsimp [B₀, B₁]
    exact one_div_le_one_div_of_le (Real.sqrt_pos.mpr hn1_pos) (Real.sqrt_le_sqrt (by linarith))
  have hA_nonneg : 0 ≤ A₀ * u + A₁ * v := by
    dsimp [A₀, A₁]
    positivity
  have hpar_nonneg := cellParabola_nonneg_of_mem_Icc hx
  have hmul1 :
      (Real.log x - cellSecant Real.log n x) * (1 / Real.sqrt x) ≤
        ((A₀ * u + A₁ * v) * cellParabola n x) * (1 / Real.sqrt x) := by
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    have heq : (A₀ * u + A₁ * v) * cellParabola n x =
        (((n : ℝ) - x) * (1 / (((n : ℝ) - 1) * (2 * (n : ℝ) - 1))) +
          (1 / 2) * (x - ((n : ℝ) - 1)) * (1 / (((n : ℝ) - 1) * (n : ℝ)))) *
          cellParabola n x := by
      rw [← hA₁_eq]
      dsimp [A₀, u, v]
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
          (x - ((n : ℝ) - 1)) * (1 / (2 * ((n : ℝ) - 1) * (n : ℝ) * Real.sqrt (n : ℝ)))) *
          cellParabola n x := by
    have hAB₀ : A₀ * B₀ = 1 / (((n : ℝ) - 1) * (2 * (n : ℝ) - 1) * Real.sqrt ((n : ℝ) - 1)) := by
      dsimp [A₀, B₀]
      rw [one_div_mul_one_div]
    have hAB₁ : A₁ * B₁ = 1 / (2 * ((n : ℝ) - 1) * (n : ℝ) * Real.sqrt (n : ℝ)) := by
      dsimp [A₁, B₁]
      rw [one_div_mul_one_div]
    rw [hAB₀, hAB₁]
    dsimp [u, v]
    ring
  rw [div_eq_mul_one_div]
  linarith

/-- **Exact Quartic Cell Integral of `(c₀ (n - x) + c₁ (x - (n - 1))) * cellParabola n x`**:
because `cellParabola n x` has integral `1 / 6` and `(2n - 1 - 2x) * cellParabola n x` is the exact
derivative of `(1 / 2) * (cellParabola n x)^2` (which vanishes at both endpoints `n - 1` and `n`),
`∫ x in (n - 1)..n, (c₀ * (n - x) + c₁ * (x - (n - 1))) * cellParabola n x = (c₀ + c₁) / 12`. -/
theorem integral_linear_mul_cellParabola_eq_add_div_twelve (c₀ c₁ : ℝ) (n : ℕ) :
    (∫ x in ((n : ℝ) - 1)..(n : ℝ),
      (c₀ * ((n : ℝ) - x) + c₁ * (x - ((n : ℝ) - 1))) * cellParabola n x) =
      (c₀ + c₁) / 12 := by
  let F : ℝ → ℝ := fun x =>
    ((c₀ + c₁) / 2) *
      (-(1 / 3) * (x * (x * x)) + ((2 * (n : ℝ) - 1) / 2) * (x * x) - (n : ℝ) * ((n : ℝ) - 1) * x) +
    ((c₀ - c₁) / 4) * (cellParabola n x * cellParabola n x)
  have hd : ∀ x ∈ uIcc ((n : ℝ) - 1) (n : ℝ),
      HasDerivAt F ((c₀ * ((n : ℝ) - x) + c₁ * (x - ((n : ℝ) - 1))) * cellParabola n x) x := by
    intro x _
    have hpoly : HasDerivAt
        (fun t : ℝ => -(1 / 3) * (t * (t * t)) + ((2 * (n : ℝ) - 1) / 2) * (t * t) - (n : ℝ) * ((n : ℝ) - 1) * t)
        ((-(1 / 3) * (1 * (x * x) + x * (1 * x + x * 1)) +
          ((2 * (n : ℝ) - 1) / 2) * (1 * x + x * 1)) - (n : ℝ) * ((n : ℝ) - 1) * 1) x := by
      exact ((((hasDerivAt_id x).mul ((hasDerivAt_id x).mul (hasDerivAt_id x))).const_mul (-(1 / 3))).add
        (((hasDerivAt_id x).mul (hasDerivAt_id x)).const_mul ((2 * (n : ℝ) - 1) / 2))).sub
        ((hasDerivAt_id x).const_mul ((n : ℝ) * ((n : ℝ) - 1)))
    have hpar := hasDerivAt_cellParabola n x
    have hsq := hpar.mul hpar
    have hcomb := (hpoly.const_mul ((c₀ + c₁) / 2)).add (hsq.const_mul ((c₀ - c₁) / 4))
    refine hcomb.congr_deriv ?_
    unfold cellParabola
    ring
  have hint : IntervalIntegrable
      (fun x : ℝ => (c₀ * ((n : ℝ) - x) + c₁ * (x - ((n : ℝ) - 1))) * cellParabola n x)
      volume ((n : ℝ) - 1) (n : ℝ) := by
    unfold cellParabola
    exact (((continuousOn_const.mul (continuousOn_const.sub continuousOn_id)).add
      (continuousOn_const.mul (continuousOn_id.sub continuousOn_const))).mul
      ((continuousOn_id.sub continuousOn_const).mul
        (continuousOn_const.sub continuousOn_id))).intervalIntegrable
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint]
  dsimp [F]
  rw [cellParabola_left_eq_zero, cellParabola_right_eq_zero]
  ring

/-! ## Section 2: The `23 / 80` Right-Endpoint Series `∑_{n=2}^N 1 / (2(n - 1)n√n) ≤ 23 / 80` and the `193 / 2880` Logarithmic Cell-Defect Bound -/

/-- **Universal Telescoping Step for the Right-Endpoint `1 / (2 m (m + 1) √(m + 1))` Series**:
for any `1 ≤ m`,
`1 / (2 * m * (m + 1) * √(m + 1)) ≤ (1 / 3) * (1 / (m * √m) - 1 / ((m + 1) * √(m + 1)))`. -/
theorem inv_two_mul_mul_succ_mul_sqrt_succ_le_third_sub {m : ℝ} (hm : 1 ≤ m) :
    1 / (2 * m * (m + 1) * Real.sqrt (m + 1)) ≤
      (1 / 3) * (1 / (m * Real.sqrt m) - 1 / ((m + 1) * Real.sqrt (m + 1))) := by
  have hm_pos : 0 < m := by linarith
  have hm1_pos : 0 < m + 1 := by linarith
  have hsqrt_m : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm_pos
  have hsqrt_m1 : 0 < Real.sqrt (m + 1) := Real.sqrt_pos.mpr hm1_pos
  have hstep : (m + 3 / 2) * Real.sqrt m ≤ (m + 1) * Real.sqrt (m + 1) := by
    have hsq_lhs : 0 ≤ (m + 3 / 2) * Real.sqrt m := by positivity
    rw [← Real.sqrt_sq hsq_lhs, ← Real.sqrt_sq (by positivity : 0 ≤ (m + 1) * Real.sqrt (m + 1))]
    refine Real.sqrt_le_sqrt ?_
    rw [mul_pow, mul_pow, Real.sq_sqrt hm_pos.le, Real.sq_sqrt hm1_pos.le]
    nlinarith
  have hdiff :
      1 / (m * Real.sqrt m) - 1 / ((m + 1) * Real.sqrt (m + 1)) =
        ((m + 1) * Real.sqrt (m + 1) - m * Real.sqrt m) /
          ((m * Real.sqrt m) * ((m + 1) * Real.sqrt (m + 1))) := by
    rw [div_sub_div 1 1 (by positivity) (by positivity)]
    ring
  rw [hdiff]
  have h3_le : (3 / 2) * Real.sqrt m ≤ (m + 1) * Real.sqrt (m + 1) - m * Real.sqrt m := by
    linarith [hstep]
  have hdiv_le := div_le_div_of_nonneg_right h3_le
    (by positivity : 0 ≤ (m * Real.sqrt m) * ((m + 1) * Real.sqrt (m + 1)))
  have hmul := mul_le_mul_of_nonneg_left hdiv_le (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hcancel :
      (1 / 3) * (((3 / 2) * Real.sqrt m) / ((m * Real.sqrt m) * ((m + 1) * Real.sqrt (m + 1)))) =
        1 / (2 * m * (m + 1) * Real.sqrt (m + 1)) := by
    rw [← mul_div_assoc, div_eq_div_iff (by positivity) (by positivity)]
    ring
  linarith

/-- **Telescoping Tail Bound for `n ≥ 5`**:
`∑ n ∈ Finset.Icc 5 N, 1 / (2 * (n - 1) * n * √n) ≤ 1 / 24`. -/
theorem sum_Icc_five_inv_two_mul_pred_mul_sqrt_le_one_twenty_fourth (N : ℕ) :
    (∑ n ∈ Finset.Icc 5 N,
      1 / (2 * ((n : ℝ) - 1) * (n : ℝ) * Real.sqrt (n : ℝ))) ≤ 1 / 24 := by
  let g : ℕ → ℝ := fun n => 1 / (((n : ℝ) - 1) * Real.sqrt ((n : ℝ) - 1))
  have htel_all : ∀ k : ℕ, (∑ n ∈ Finset.Icc 5 (5 + k), (g n - g (n + 1))) = g 5 - g (5 + k + 1) := by
    intro k
    induction k with
    | zero =>
      simp
    | succ k ih =>
      have hIcc : Finset.Icc 5 (5 + (k + 1)) =
          insert (5 + (k + 1)) (Finset.Icc 5 (5 + k)) := by
        ext m
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      have hnotmem : 5 + (k + 1) ∉ Finset.Icc 5 (5 + k) := by
        simp only [Finset.mem_Icc]
        omega
      rw [hIcc, Finset.sum_insert hnotmem, ih, ← Nat.add_assoc]
      ring
  have hle :
      (∑ n ∈ Finset.Icc 5 N, 1 / (2 * ((n : ℝ) - 1) * (n : ℝ) * Real.sqrt (n : ℝ))) ≤
        (1 / 3) * ∑ n ∈ Finset.Icc 5 N, (g n - g (n + 1)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun n hn => ?_
    rw [Finset.mem_Icc] at hn
    have hn5 : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1
    have hstep := inv_two_mul_mul_succ_mul_sqrt_succ_le_third_sub (m := (n : ℝ) - 1) (by linarith)
    have h1 : (n : ℝ) - 1 + 1 = (n : ℝ) := by ring
    have hg_succ : g (n + 1) = 1 / ((n : ℝ) * Real.sqrt (n : ℝ)) := by
      dsimp [g]
      push_cast
      rw [add_sub_cancel_right]
    rw [hg_succ]
    dsimp [g]
    rwa [h1] at hstep
  by_cases hN : 5 ≤ N
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
    have htel := htel_all k
    have hg5 : g 5 = 1 / 8 := by
      dsimp [g]
      have h4 : (5 : ℝ) - 1 = 2 ^ 2 := by norm_num
      rw [h4, Real.sqrt_sq (by norm_num)]
      norm_num
    have hg_nonneg : 0 ≤ g (5 + k + 1) := by
      dsimp [g]
      have hpos : (0 : ℝ) ≤ (5 + k + 1 : ℕ) - 1 := by
        push_cast
        linarith
      exact div_nonneg zero_le_one (mul_nonneg hpos (Real.sqrt_nonneg _))
    rw [htel, hg5] at hle
    linarith
  · rw [Finset.Icc_eq_empty hN, Finset.sum_empty]
    norm_num

/-- **Rational Bound on the Isolated `n = 2` and `n = 3` Right-Endpoint Terms**:
`1 / (4 * √2) + 1 / (12 * √3) ≤ 9 / 40` via `1393 / 985 ≤ √2` and `265 / 153 ≤ √3`
(`985 / 5572 + 51 / 1060 = 83017 / 369145 < 9 / 40`). -/
theorem inv_four_sqrt_two_add_inv_twelve_sqrt_three_le_nine_fortieths :
    1 / (4 * Real.sqrt 2) + 1 / (12 * Real.sqrt 3) ≤ 9 / 40 := by
  have hsqrt2_ge : (1393 / 985 : ℝ) ≤ Real.sqrt 2 := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1393 / 985)]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hsqrt3_ge : (265 / 153 : ℝ) ≤ Real.sqrt 3 := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 265 / 153)]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hsqrt2_pos : 0 < 4 * Real.sqrt 2 := mul_pos (by norm_num) (Real.sqrt_pos.mpr (by norm_num))
  have hsqrt3_pos : 0 < 12 * Real.sqrt 3 := mul_pos (by norm_num) (Real.sqrt_pos.mpr (by norm_num))
  have h1 : 1 / (4 * Real.sqrt 2) ≤ 985 / 5572 := by
    rw [div_le_iff₀ hsqrt2_pos]
    linarith
  have h2 : 1 / (12 * Real.sqrt 3) ≤ 51 / 1060 := by
    rw [div_le_iff₀ hsqrt3_pos]
    linarith
  linarith

/-- **Uniform Cutoff-Independent Bound `∑_{n=2}^N 1 / (2(n - 1)n√n) ≤ 23 / 80` for All `N : ℕ`**:
combining `n = 2, 3` (`≤ 9 / 40`), `n = 4` (`= 1 / 48`), and `n ≥ 5` (`≤ 1 / 24`) gives
`9 / 40 + 1 / 48 + 1 / 24 = 23 / 80`! -/
theorem sum_Icc_two_inv_two_mul_pred_mul_sqrt_le_twenty_three_eightieths (N : ℕ) :
    (∑ n ∈ Finset.Icc 2 N,
      1 / (2 * ((n : ℝ) - 1) * (n : ℝ) * Real.sqrt (n : ℝ))) ≤ 23 / 80 := by
  let g : ℕ → ℝ := fun n => 1 / (2 * ((n : ℝ) - 1) * (n : ℝ) * Real.sqrt (n : ℝ))
  have hg2 : g 2 = 1 / (4 * Real.sqrt 2) := by dsimp [g]; norm_num
  have hg3 : g 3 = 1 / (12 * Real.sqrt 3) := by dsimp [g]; norm_num
  have hg4 : g 4 = 1 / 48 := by
    dsimp [g]
    have h4 : (4 : ℝ) = 2 ^ 2 := by norm_num
    rw [h4, Real.sqrt_sq (by norm_num)]
    norm_num
  have hg3_nonneg : 0 ≤ g 3 := by rw [hg3]; positivity
  have h23 := inv_four_sqrt_two_add_inv_twelve_sqrt_three_le_nine_fortieths
  have htail5 : (∑ n ∈ Finset.Icc 5 N, g n) ≤ 1 / 24 :=
    sum_Icc_five_inv_two_mul_pred_mul_sqrt_le_one_twenty_fourth N
  have htail4 : (∑ n ∈ Finset.Icc 4 N, g n) ≤ 1 / 16 := by
    by_cases hN4 : 4 ≤ N
    · rw [sum_Icc_eq_add_sum_Icc_succ g hN4, hg4]
      linarith
    · rw [Finset.Icc_eq_empty hN4, Finset.sum_empty]
      norm_num
  by_cases hN3 : 3 ≤ N
  · change (∑ n ∈ Finset.Icc 2 N, g n) ≤ 23 / 80
    rw [sum_Icc_eq_add_sum_Icc_succ g (by omega : 2 ≤ N),
      sum_Icc_eq_add_sum_Icc_succ g hN3, hg2, hg3]
    linarith
  · by_cases hN2 : 2 ≤ N
    · have hN_eq : N = 2 := by omega
      subst hN_eq
      change (∑ n ∈ Finset.Icc 2 2, g n) ≤ 23 / 80
      rw [Finset.Icc_self, Finset.sum_singleton]
      linarith [hg2, hg3, hg3_nonneg, h23]
    · rw [Finset.Icc_eq_empty hN2, Finset.sum_empty]
      norm_num

/-- **Cutoff-Independent `-(193 / 2880) (spectralSecondMoment f.1 + ∫ ‖f.1‖²) ≤ secantNumeratorCellDefect f.1 N`**:
combining the Exact Logarithmic Secant Comparison Theorem with the two-endpoint linear-parabola
envelope and `(1 / 12) * (31 / 60 + 23 / 80) = 193 / 2880`! -/
theorem neg_one_ninety_three_twenty_eight_eightieths_spectralSecondMoment_add_l2_le_secantNumeratorCellDefect
    (f : WeilTestFn)
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2))
    (N : ℕ) :
    -(193 / 2880) * (spectralSecondMoment f.1 + ∫ u : ℝ, ‖f.1 u‖ ^ 2) ≤
      secantNumeratorCellDefect f.1 N := by
  let M := spectralSecondMoment f.1 + ∫ u : ℝ, ‖f.1 u‖ ^ 2
  have hnorm_nonneg : 0 ≤ ∫ u : ℝ, ‖f.1 u‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hM_nonneg : 0 ≤ M := add_nonneg (spectralSecondMoment_nonneg f.1) hnorm_nonneg
  let c₀ : ℕ → ℝ := fun n =>
    M * (1 / (((n : ℝ) - 1) * (2 * (n : ℝ) - 1) * Real.sqrt ((n : ℝ) - 1)))
  let c₁ : ℕ → ℝ := fun n =>
    M * (1 / (2 * ((n : ℝ) - 1) * (n : ℝ) * Real.sqrt (n : ℝ)))
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
      (log_sub_cellSecant_log_div_sqrt_le_linear_mul_cellParabola hn_mem.1 hx) hM_nonneg
    have halg :
        M * ((((n : ℝ) - x) * (1 / (((n : ℝ) - 1) * (2 * (n : ℝ) - 1) * Real.sqrt ((n : ℝ) - 1))) +
          (x - ((n : ℝ) - 1)) * (1 / (2 * ((n : ℝ) - 1) * (n : ℝ) * Real.sqrt (n : ℝ)))) *
          cellParabola n x) =
        (c₀ n * ((n : ℝ) - x) + c₁ n * (x - ((n : ℝ) - 1))) * cellParabola n x := by
      dsimp [c₀, c₁]
      ring
    linarith
  have hsum_le :
      (∑ n ∈ Finset.Icc 2 N, (c₀ n + c₁ n) / 12) ≤ (193 / 2880) * M := by
    have hcongr :
        (∑ n ∈ Finset.Icc 2 N, (c₀ n + c₁ n) / 12) =
          (M / 12) * ((∑ n ∈ Finset.Icc 2 N,
              1 / (((n : ℝ) - 1) * (2 * (n : ℝ) - 1) * Real.sqrt ((n : ℝ) - 1))) +
            ∑ n ∈ Finset.Icc 2 N,
              1 / (2 * ((n : ℝ) - 1) * (n : ℝ) * Real.sqrt (n : ℝ))) := by
      rw [ ← Finset.sum_add_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      dsimp [c₀, c₁]
      ring
    rw [hcongr]
    have h1 := sum_Icc_two_inv_pred_mul_two_mul_sub_one_mul_sqrt_pred_le_thirty_one_sixtieths N
    have h2 := sum_Icc_two_inv_two_mul_pred_mul_sqrt_le_twenty_three_eightieths N
    have hmul := mul_le_mul_of_nonneg_left (add_le_add h1 h2) (by linarith : 0 ≤ M / 12)
    linarith
  linarith

/-! ## Section 3: The `(2111 / 2880) ∫ ‖f.1‖² - (193 / 2880) spectralSecondMoment f.1` Coercivity Law, the `(2327 / 2880) ∫ ‖f.1‖² - (193 / 2880) spectralSecondMoment f.1` Prime-Blind Cone Law, and Unconditional `markovEnergy ≥ 0` up to `spectralSecondMoment F ≤ (2111 / 193 - δ) ∫ ‖F‖² > 10.937 ∫ ‖F‖²` -/

/-- **Pure Second-Moment `(2111 / 2880) ∫ ‖f.1‖² - (193 / 2880) spectralSecondMoment f.1` Lower Bound
on `rightCellQuadratureDefect` (Critical Ratio `2111 / 193 > 10.9378`)**:
absorbing `(193 / 2880) * ∫ ‖f.1‖²` into `(4 / 5) * ∫ ‖f.1‖² = (2304 / 2880) * ∫ ‖f.1‖²` leaves
`2111 / 2880 > 11 / 15` with common denominator `2880`! -/
theorem two_thousand_one_hundred_eleven_twenty_eight_eightieths_l2_sub_one_ninety_three_twenty_eight_eightieths_spectralSecondMoment_le_rightCellQuadratureDefect
    (f : WeilTestFn)
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2))
    {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest f.1 f.1 (Real.log N) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log N) = 0)
    (hN : ∀ n : ℕ, N < n →
      EF.weilTest f.1 f.1 (Real.log n) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log n) = 0) :
    (2111 / 2880) * (∫ u : ℝ, ‖f.1 u‖ ^ 2) - (193 / 2880) * spectralSecondMoment f.1 ≤
      rightCellQuadratureDefect (weilContinuumLogProfile f.1) N := by
  have h1 := four_fifths_l2_add_secantNumerator_le_rightCellQuadratureDefect f hN1 hN0 hN
  have h2 := neg_one_ninety_three_twenty_eight_eightieths_spectralSecondMoment_add_l2_le_secantNumeratorCellDefect
    f hint2 N
  linarith

/-- **Prime-Blind Cone `(2327 / 2880) ∫ ‖f.1‖² - (193 / 2880) spectralSecondMoment f.1` Lower Bound
on `rightCellQuadratureDefect` (Critical Ratio `2327 / 193 > 12.0569`)**:
on the Prime-Blind Cone (`logVector f = 0`), absorbing `(193 / 2880) * ∫ ‖f.1‖²` into Module 52's
`(7 / 8) * ∫ ‖f.1‖² = (2520 / 2880) * ∫ ‖f.1‖²` origin surplus leaves `2327 / 2880 > 4 / 5`! -/
theorem two_thousand_three_hundred_twenty_seven_twenty_eight_eightieths_l2_sub_one_ninety_three_twenty_eight_eightieths_spectralSecondMoment_le_rightCellQuadratureDefect_of_logVector_eq_zero
    (f : WeilTestFn) (hblind : logVector f = 0)
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2))
    {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest f.1 f.1 (Real.log N) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log N) = 0)
    (hN : ∀ n : ℕ, N < n →
      EF.weilTest f.1 f.1 (Real.log n) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log n) = 0) :
    (2327 / 2880) * (∫ u : ℝ, ‖f.1 u‖ ^ 2) - (193 / 2880) * spectralSecondMoment f.1 ≤
      rightCellQuadratureDefect (weilContinuumLogProfile f.1) N := by
  have h1 := seven_eighths_l2_add_secantNumerator_le_rightCellQuadratureDefect_of_logVector_eq_zero
    f hblind hN1 hN0 hN
  have h2 := neg_one_ninety_three_twenty_eight_eightieths_spectralSecondMoment_add_l2_le_secantNumeratorCellDefect
    f hint2 N
  linarith

/-- **Unconditional `0 ≤ markovEnergy F` on the Primitive Hyperplane whenever
`spectralSecondMoment F ≤ (2111 / 193 - δ) ∫ ‖F‖² > 10.937 ∫ ‖F‖²`**: -/
theorem markovEnergy_ofReal_nonneg_of_spectralSecondMoment_le_two_thousand_one_hundred_eleven_one_ninety_thirds_of_cosh_zero
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
      (2111 / 193 - δ) * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) :
    0 ≤ markovEnergy (realWeilTestFn f hf hfc).1 := by
  let θ := max (max 1 (Real.log (N : ℝ))) (5760 / (193 * δ))
  have hθ1 : 1 ≤ θ := (le_max_left 1 (Real.log (N : ℝ))).trans (le_max_left _ _)
  have hθ0 : 0 ≤ θ := by linarith
  have hθlog : Real.log (N : ℝ) ≤ θ :=
    (le_max_right 1 (Real.log (N : ℝ))).trans (le_max_left _ _)
  have h193δ : 0 < 193 * δ := by linarith
  have hθδ_le : 5760 / (193 * δ) ≤ θ := le_max_right _ _
  have hθδ : 5760 ≤ θ * (193 * δ) := (div_le_iff₀ h193δ).mp hθδ_le
  have hbase := four_fifths_secantNumerator_upgraded_l2_le_markovEnergy_of_cosh_zero
    m hθ0 hf hfc hcosh hN1 hθlog hN0 hN hdiff
  have hnum := neg_one_ninety_three_twenty_eight_eightieths_spectralSecondMoment_add_l2_le_secantNumeratorCellDefect
    (realWeilTestFn f hf hfc) hint2 N
  have hθnum := mul_le_mul_of_nonneg_left hnum hθ0
  have hθbound := mul_le_mul_of_nonneg_left hsec_bound (by positivity : 0 ≤ (193 / 2880) * θ)
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
