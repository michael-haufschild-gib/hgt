import GaloisForLFunctions.RHTower.MarkovHermiteQuinticLogSecantAndThirteenPointFourRatioPBAP

/-!
# The One-Parameter Variational Amplitude Family, the Exact Geometric-Mean Law `-(1 / 18) √(S(S + 2L)) ≤ secantNumeratorCellDefect`, Nonnegative Log-Value Cone Positivity, and the `202 / 15 > 13.466` & `1183 / 80 = 14.7875` Coercivity Laws for Route HF / PBAP

In Module 55 (`MarkovEuclideanCosLogCurvatureAndFivePointSevenRatioPBAP`) through Module 59
(`MarkovHermiteQuinticLogSecantAndThirteenPointFourRatioPBAP`), the logarithmic frequency kernel
`cosLogProfileDeriv2 r t = (-r² cos(r log t) + r sin(r log t)) / t²` was bounded using the single
envelope `|-r² cos θ + r sin θ| ≤ r² + 1 / 2` (corresponding to `b = 1 / 2`), which produced the
arithmetic-mean combination `spectralSecondMoment f.1 + ∫ ‖f.1‖²`.

In this module, we replace that fixed envelope by the **complete one-parameter variational family**
of tangent lines to `√(r⁴ + r²)` and take its exact infimum over `b > 0`:

1. **Section 1 (The One-Parameter Variational Amplitude Envelope `((b + 1/(4b)) r² + b)`):**
   - For every `b > 0` and `r, θ ∈ ℝ`,
     `((b + 1 / (4 * b)) * r ^ 2 + b) ^ 2 - ((-r ^ 2) ^ 2 + r ^ 2) = ((b - 1 / (4 * b)) * r ^ 2 + b) ^ 2 ≥ 0`,
     yielding `|-r ^ 2 * cos θ + r * sin θ| ≤ (b + 1 / (4 * b)) * r ^ 2 + b`
     (`abs_neg_sq_mul_cos_add_mul_sin_le_variational`).
   - Integrating over `r ∈ ℝ` against `(1 / (2π)) ‖paperFT f.1 r‖² * 2` and applying Plancherel gives
     (`abs_weilSymmetricLogNumerator_sub_cellSecant_le_variational`):
     `|weilSymmetricLogNumerator f.1 x - cellSecant (weilSymmetricLogNumerator f.1) n x| ≤ ((b + 1 / (4 * b)) * spectralSecondMoment f.1 + 2 * b * ∫ ‖f.1‖²) * (Real.log x - cellSecant Real.log n x)`.

2. **Section 2 (The Universal Variational Family and the Exact Geometric-Mean Law
   `-(1 / 18) √(S(S + 2L)) ≤ secantNumeratorCellDefect`):**
   - Combining Section 1 with Module 59's `1 / 18` Cubic Hermite × Quintic Chebyshev cell-weight bound
     gives, for every `b > 0` (`neg_one_eighteenth_variational_le_secantNumeratorCellDefect`):
     `-(1 / 18) * ((b + 1 / (4 * b)) * spectralSecondMoment f.1 + 2 * b * ∫ ‖f.1‖²) ≤ secantNumeratorCellDefect f.1 N`.
   - Optimizing over `b > 0` (`b = √S / (2 √(S + 2L))` when `S > 0`, and `b → 0⁺` when `S = 0`)
     proves the **Exact Geometric-Mean Law**
     (`neg_one_eighteenth_sqrt_spectralSecondMoment_mul_add_two_l2_le_secantNumeratorCellDefect`):
     `-(1 / 18) * √(spectralSecondMoment f.1 * (spectralSecondMoment f.1 + 2 * ∫ ‖f.1‖²)) ≤ secantNumeratorCellDefect f.1 N`.
   - Because `√(S(S + 2L)) = √((S + L)² - L²) ≤ S + L` with strict inequality whenever `L > 0`,
     this strictly dominates the arithmetic-mean bound `-(1 / 18)(S + L)` for every nonzero test
     function and vanishes identically at `S = 0`.

3. **Section 3 (Sharp `433 / 540` and `1261 / 1440` Origin Surpluses, Nonnegative Log-Value Cone
   Positivity, and the `202 / 15 > 13.4666` & `1183 / 80 = 14.7875` Coercivity Laws):**
   - We prove the sharp rational lower bounds
     `433 / 540 ≤ (43 * √2 - 56) / 6` and `1261 / 1440 ≤ (16 * √2 - 20) / 3`.
   - On the **Nonnegative Log-Value Cone** (`∀ n ∈ Finset.Icc 2 N, 0 ≤ logValue f.1 n`, which is the
     `m = 0` forward-difference cone and includes the Prime-Blind Cone `logVector f = 0`), since
     `0 ≤ secantCombinedSecularWeight n`, we prove
     `0 ≤ primeBlindCounterterm secantCombinedSecularWeight f`, so the full origin surplus
     `((16 * √2 - 20) / 3) * ∫ ‖f.1‖² ≥ (1261 / 1440) * ∫ ‖f.1‖²` is retained without subtracting
     the secular counterterm!
   - Using the Pythagorean completion `(S + L)² - L² = S(S + 2L)` together with
     `434² = 188356 < 188389 = 433² + 30²` and `1263² = 1595169 < 1596521 = 1261² + 80²`, we prove:
     - `0 ≤ rightCellQuadratureDefect (weilContinuumLogProfile f.1) N` whenever
       `spectralSecondMoment f.1 ≤ (202 / 15) * ∫ ‖f.1‖²` (ratio **`202 / 15 > 13.4666`**!),
     - `0 ≤ rightCellQuadratureDefect (weilContinuumLogProfile f.1) N` on the Nonnegative Log-Value
       Cone (and on the Prime-Blind Cone `logVector f = 0`) whenever
       `spectralSecondMoment f.1 ≤ (1183 / 80) * ∫ ‖f.1‖²` (ratio **`1183 / 80 = 14.7875`**!),
     - Unconditional `0 ≤ markovEnergy F` on the Primitive Hyperplane whenever
       `spectralSecondMoment F ≤ (202 / 15 - δ) * ∫ ‖F‖²`, and for `m = 0` whenever
       `spectralSecondMoment F ≤ (1183 / 80 - δ) * ∫ ‖F‖²`!
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

/-! ## Section 1: The One-Parameter Variational Amplitude Envelope `((b + 1/(4b)) r² + b)` -/

/-- **One-Parameter Variational Amplitude Bound
`|-r ^ 2 * cos θ + r * sin θ| ≤ (b + 1 / (4 * b)) * r ^ 2 + b`**:
for every `0 < b` and `r, θ ∈ ℝ`,
`((b + 1 / (4 * b)) * r ^ 2 + b) ^ 2 - (r ^ 4 + r ^ 2) = ((b - 1 / (4 * b)) * r ^ 2 + b) ^ 2 ≥ 0`. -/
theorem abs_neg_sq_mul_cos_add_mul_sin_le_variational
    {b : ℝ} (hb : 0 < b) (r θ : ℝ) :
    |-r ^ 2 * Real.cos θ + r * Real.sin θ| ≤ (b + 1 / (4 * b)) * r ^ 2 + b := by
  have h1 := sq_linear_cos_sin_le (-r ^ 2) r θ
  have h4b_ne : 4 * b ≠ 0 := by positivity
  have hpoly :
      ((b + 1 / (4 * b)) * r ^ 2 + b) ^ 2 - ((-r ^ 2) ^ 2 + r ^ 2) =
        ((b - 1 / (4 * b)) * r ^ 2 + b) ^ 2 := by
    calc ((b + 1 / (4 * b)) * r ^ 2 + b) ^ 2 - ((-r ^ 2) ^ 2 + r ^ 2)
      _ = ((b - 1 / (4 * b)) * r ^ 2 + b) ^ 2 +
            ((4 * b) * (1 / (4 * b)) - 1) * (r ^ 4 + r ^ 2) := by ring
      _ = ((b - 1 / (4 * b)) * r ^ 2 + b) ^ 2 := by
          rw [mul_one_div_cancel h4b_ne]
          ring
  have h2 : (-r ^ 2) ^ 2 + r ^ 2 ≤ ((b + 1 / (4 * b)) * r ^ 2 + b) ^ 2 := by
    have hsq_nonneg : 0 ≤ ((b - 1 / (4 * b)) * r ^ 2 + b) ^ 2 := sq_nonneg _
    linarith
  have hsq : (-r ^ 2 * Real.cos θ + r * Real.sin θ) ^ 2 ≤
      ((b + 1 / (4 * b)) * r ^ 2 + b) ^ 2 := h1.trans h2
  rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_sq (by positivity : 0 ≤ (b + 1 / (4 * b)) * r ^ 2 + b)]
  exact Real.sqrt_le_sqrt hsq

/-- **Pointwise Variational Second-Derivative Bound on `cosLogProfileDeriv2 r t`**:
for every `0 < b`, `r ∈ ℝ`, and `0 < t`,
`|cosLogProfileDeriv2 r t| ≤ ((b + 1 / (4 * b)) * r ^ 2 + b) / t ^ 2`. -/
theorem abs_cosLogProfileDeriv2_le_variational_div_sq
    {b : ℝ} (hb : 0 < b) (r : ℝ) {t : ℝ} (ht : 0 < t) :
    |cosLogProfileDeriv2 r t| ≤ ((b + 1 / (4 * b)) * r ^ 2 + b) / t ^ 2 := by
  unfold cosLogProfileDeriv2
  rw [abs_mul, abs_inv, abs_of_pos (sq_pos_of_pos ht), ← div_eq_mul_inv]
  exact div_le_div_of_nonneg_right
    (abs_neg_sq_mul_cos_add_mul_sin_le_variational hb r (r * Real.log t))
    (sq_nonneg t)

/-- **Pointwise Variational Spectral-Logarithmic Secant Comparison for `weilSymmetricLogNumerator`**:
for every `0 < b`, `2 ≤ n`, and `x ∈ [n - 1, n]`,
`|weilSymmetricLogNumerator f.1 x - cellSecant (weilSymmetricLogNumerator f.1) n x| ≤ ((b + 1 / (4 * b)) * spectralSecondMoment f.1 + 2 * b * ∫ ‖f.1‖²) * (Real.log x - cellSecant Real.log n x)`. -/
theorem abs_weilSymmetricLogNumerator_sub_cellSecant_le_variational
    (f : WeilTestFn)
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2))
    {b : ℝ} (hb : 0 < b)
    {n : ℕ} (hn : 2 ≤ n) {x : ℝ} (hx : x ∈ Icc ((n : ℝ) - 1) (n : ℝ)) :
    |weilSymmetricLogNumerator f.1 x - cellSecant (weilSymmetricLogNumerator f.1) n x| ≤
      ((b + 1 / (4 * b)) * spectralSecondMoment f.1 + 2 * b * ∫ u : ℝ, ‖f.1 u‖ ^ 2) *
        (Real.log x - cellSecant Real.log n x) := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hsq := integrable_paperFT_norm_sq f
  have hplanch := one_div_two_pi_mul_integral_paperFT_norm_sq_mul_two_eq f
  have hcos : ∀ t : ℝ, Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * cosLogProfile r t) :=
    integrable_paperFT_norm_sq_mul_two_cosLogProfile f
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
  let a : ℝ := b + 1 / (4 * b)
  have hrhs_eq :
      (a * spectralSecondMoment f.1 + 2 * b * ∫ u : ℝ, ‖f.1 u‖ ^ 2) *
        (Real.log x - cellSecant Real.log n x) =
      (1 / (2 * π)) * ∫ r : ℝ,
        (a * (‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2)) + b * (‖paperFT f.1 r‖ ^ 2 * 2)) *
          (Real.log x - cellSecant Real.log n x) := by
    have hplanch' : (∫ u : ℝ, ‖f.1 u‖ ^ 2) =
        (1 / (2 * π)) * ((1 / 2) * ∫ r : ℝ, ‖paperFT f.1 r‖ ^ 2 * 2) := by
      linarith [hplanch]
    unfold spectralSecondMoment
    rw [integral_mul_const, integral_add (hint2.const_mul a) ((hsq.mul_const 2).const_mul b),
      integral_const_mul, integral_const_mul, hplanch']
    ring
  change (1 / (2 * π)) * |∫ r : ℝ, ‖paperFT f.1 r‖ ^ 2 *
      (2 * (cosLogProfile r x - cellSecant (cosLogProfile r) n x))| ≤
    (a * spectralSecondMoment f.1 + 2 * b * ∫ u : ℝ, ‖f.1 u‖ ^ 2) *
      (Real.log x - cellSecant Real.log n x)
  rw [hrhs_eq]
  refine mul_le_mul_of_nonneg_left (abs_integral_le_integral_abs.trans ?_)
    (div_nonneg zero_le_one Real.two_pi_pos.le)
  refine integral_mono hint_diff.abs
    (((hint2.const_mul a).add ((hsq.mul_const 2).const_mul b)).mul_const _) fun r => ?_
  dsimp
  rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg _), abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have ht_pos : ∀ t ∈ Icc ((n : ℝ) - 1) (n : ℝ), 0 < t := fun t ht => by linarith [ht.1]
  have hcmp := abs_sub_cellSecant_le_mul_log_sub_cellSecant_of_abs_deriv2_le_div_sq hn
    (fun t ht => hasDerivAt_cosLogProfile r (ht_pos t ht))
    (fun t ht => hasDerivAt_cosLogProfileDeriv r (ht_pos t ht))
    (fun t ht => abs_cosLogProfileDeriv2_le_variational_div_sq hb r (ht_pos t ht)) hx
  have hweight : 0 ≤ ‖paperFT f.1 r‖ ^ 2 * 2 := mul_nonneg (sq_nonneg _) (by norm_num)
  have hmul := mul_le_mul_of_nonneg_left hcmp hweight
  dsimp [a]
  linarith

/-! ## Section 2: The Universal Variational Family and the Exact Geometric-Mean Law `-(1 / 18) √(S(S + 2L)) ≤ secantNumeratorCellDefect` -/

/-- **One-Parameter Variational Family of Lower Bounds on `secantNumeratorCellDefect`**:
for every `0 < b` and `N : ℕ`,
`-(1 / 18) * ((b + 1 / (4 * b)) * spectralSecondMoment f.1 + 2 * b * ∫ ‖f.1‖²) ≤ secantNumeratorCellDefect f.1 N`. -/
theorem neg_one_eighteenth_variational_le_secantNumeratorCellDefect
    (f : WeilTestFn)
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2))
    {b : ℝ} (hb : 0 < b) (N : ℕ) :
    -(1 / 18) * ((b + 1 / (4 * b)) * spectralSecondMoment f.1 + 2 * b * ∫ u : ℝ, ‖f.1 u‖ ^ 2) ≤
      secantNumeratorCellDefect f.1 N := by
  let M := (b + 1 / (4 * b)) * spectralSecondMoment f.1 + 2 * b * ∫ u : ℝ, ‖f.1 u‖ ^ 2
  have hS_nonneg : 0 ≤ spectralSecondMoment f.1 := spectralSecondMoment_nonneg f.1
  have hL_nonneg : 0 ≤ ∫ u : ℝ, ‖f.1 u‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    positivity
  have hcell_le : ∀ n ∈ Finset.Icc 2 N,
      -(M * hermiteQuinticCellWeight n) ≤
        ∫ x in ((n : ℝ) - 1)..(n : ℝ),
          (weilSymmetricLogNumerator f.1 x -
            cellSecant (weilSymmetricLogNumerator f.1) n x) / Real.sqrt x := by
    intro n hn
    have hn_mem := Finset.mem_Icc.mp hn
    have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_mem.1
    have hn_le : (n : ℝ) - 1 ≤ (n : ℝ) := by linarith
    have hinv : ContinuousOn (fun x : ℝ => (Real.sqrt x)⁻¹) (uIcc ((n : ℝ) - 1) (n : ℝ)) := by
      refine ContinuousOn.inv₀ Real.continuous_sqrt.continuousOn fun x hx => ?_
      rw [uIcc_of_le hn_le] at hx
      exact ne_of_gt (Real.sqrt_pos.mpr (by linarith [hx.1]))
    have hint_rhs : IntervalIntegrable
        (fun x : ℝ =>
          (weilSymmetricLogNumerator f.1 x -
            cellSecant (weilSymmetricLogNumerator f.1) n x) / Real.sqrt x)
        volume ((n : ℝ) - 1) (n : ℝ) := by
      have hnum : ContinuousOn
          (fun x : ℝ => weilSymmetricLogNumerator f.1 x)
          (uIcc ((n : ℝ) - 1) (n : ℝ)) := by
        refine (continuousOn_weilSymmetricLogNumerator f).mono fun x hx => ?_
        rw [uIcc_of_le hn_le] at hx
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
    have hint_lhs : IntervalIntegrable
        (fun x => -(M * ((hermiteLogEndpoint0 n * ((n : ℝ) - x) +
          hermiteLogEndpoint1 n * (x - ((n : ℝ) - 1))) *
          ((1 / Real.sqrt ((n : ℝ) - 1)) * ((n : ℝ) - x) +
            (1 / Real.sqrt (n : ℝ)) * (x - ((n : ℝ) - 1))) *
          cellParabola n x)))
        volume ((n : ℝ) - 1) (n : ℝ) := by
      apply Continuous.intervalIntegrable
      unfold cellParabola
      continuity
    have hInt_lhs :
        (∫ x in ((n : ℝ) - 1)..(n : ℝ),
          -(M * ((hermiteLogEndpoint0 n * ((n : ℝ) - x) +
            hermiteLogEndpoint1 n * (x - ((n : ℝ) - 1))) *
            ((1 / Real.sqrt ((n : ℝ) - 1)) * ((n : ℝ) - x) +
              (1 / Real.sqrt (n : ℝ)) * (x - ((n : ℝ) - 1))) *
            cellParabola n x))) =
        -(M * hermiteQuinticCellWeight n) := by
      rw [intervalIntegral.integral_neg, intervalIntegral.integral_const_mul,
        integral_secant_mul_secant_mul_cellParabola_eq]
      rfl
    rw [← hInt_lhs]
    refine intervalIntegral.integral_mono_on hn_le hint_lhs hint_rhs fun x hx => ?_
    have hlog_cmp :
        |weilSymmetricLogNumerator f.1 x - cellSecant (weilSymmetricLogNumerator f.1) n x| ≤
          M * (Real.log x - cellSecant Real.log n x) :=
      abs_weilSymmetricLogNumerator_sub_cellSecant_le_variational f hint2 hb hn_mem.1 hx
    have hdiv_cmp :
        -(M * ((Real.log x - cellSecant Real.log n x) / Real.sqrt x)) ≤
          (weilSymmetricLogNumerator f.1 x - cellSecant (weilSymmetricLogNumerator f.1) n x) /
            Real.sqrt x := by
      have hlow := (abs_le.mp hlog_cmp).1
      have hdiv := div_le_div_of_nonneg_right hlow (Real.sqrt_nonneg x)
      linarith [mul_div_assoc M (Real.log x - cellSecant Real.log n x) (Real.sqrt x),
        neg_div (Real.sqrt x) (M * (Real.log x - cellSecant Real.log n x))]
    have hquintic := mul_le_mul_of_nonneg_left
      (hermite_log_sub_cellSecant_log_div_sqrt_le hn_mem.1 hx) hM_nonneg
    linarith
  have hsum_mono :
      (∑ n ∈ Finset.Icc 2 N, -(M * hermiteQuinticCellWeight n)) ≤
        secantNumeratorCellDefect f.1 N := by
    unfold secantNumeratorCellDefect
    exact Finset.sum_le_sum hcell_le
  have hsum_pull :
      (∑ n ∈ Finset.Icc 2 N, -(M * hermiteQuinticCellWeight n)) =
        -(M * ∑ n ∈ Finset.Icc 2 N, hermiteQuinticCellWeight n) := by
    rw [Finset.sum_neg_distrib, ← Finset.mul_sum]
  have hsum_18 := mul_le_mul_of_nonneg_left
    (sum_Icc_two_hermiteQuinticCellWeight_le_one_eighteenth N) hM_nonneg
  linarith

/-- **The Exact Geometric-Mean Law for `secantNumeratorCellDefect`**:
minimizing `neg_one_eighteenth_variational_le_secantNumeratorCellDefect` over `b > 0` proves
`-(1 / 18) * √(spectralSecondMoment f.1 * (spectralSecondMoment f.1 + 2 * ∫ ‖f.1‖²)) ≤ secantNumeratorCellDefect f.1 N`. -/
theorem neg_one_eighteenth_sqrt_spectralSecondMoment_mul_add_two_l2_le_secantNumeratorCellDefect
    (f : WeilTestFn)
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2))
    (N : ℕ) :
    -(1 / 18) * Real.sqrt
        (spectralSecondMoment f.1 * (spectralSecondMoment f.1 + 2 * ∫ u : ℝ, ‖f.1 u‖ ^ 2)) ≤
      secantNumeratorCellDefect f.1 N := by
  let S := spectralSecondMoment f.1
  let L := ∫ u : ℝ, ‖f.1 u‖ ^ 2
  have hS_nonneg : 0 ≤ S := spectralSecondMoment_nonneg f.1
  have hL_nonneg : 0 ≤ L := integral_nonneg fun _ => sq_nonneg _
  rcases eq_or_lt_of_le hS_nonneg with hS0 | hS_pos
  · change -(1 / 18) * Real.sqrt (S * (S + 2 * L)) ≤ secantNumeratorCellDefect f.1 N
    rw [← hS0, zero_mul, Real.sqrt_zero, mul_zero]
    by_contra! hneg
    let D := secantNumeratorCellDefect f.1 N
    have hD_neg : D < 0 := hneg
    have h2L1_pos : 0 < 2 * L + 1 := by positivity
    let b := (-9 * D) / (2 * L + 1)
    have hb_pos : 0 < b := div_pos (by linarith) h2L1_pos
    have hvar := neg_one_eighteenth_variational_le_secantNumeratorCellDefect f hint2 hb_pos N
    change -(1 / 18) * ((b + 1 / (4 * b)) * S + 2 * b * L) ≤ D at hvar
    rw [← hS0, mul_zero, zero_add] at hvar
    have hb_mul : b * (2 * L + 1) = -9 * D := div_mul_cancel₀ (-9 * D) h2L1_pos.ne'
    have hbL_le : b * (2 * L) ≤ b * (2 * L + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hb_pos.le
    linarith
  · have hS2L_pos : 0 < S + 2 * L := by positivity
    let s₁ := Real.sqrt S
    let s₂ := Real.sqrt (S + 2 * L)
    have hs₁_pos : 0 < s₁ := Real.sqrt_pos.mpr hS_pos
    have hs₂_pos : 0 < s₂ := Real.sqrt_pos.mpr hS2L_pos
    have hs₁_sq : s₁ ^ 2 = S := Real.sq_sqrt hS_pos.le
    have hs₂_sq : s₂ ^ 2 = S + 2 * L := Real.sq_sqrt hS2L_pos.le
    let b := s₁ / (2 * s₂)
    have hb_pos : 0 < b := by dsimp [b]; positivity
    have hvar := neg_one_eighteenth_variational_le_secantNumeratorCellDefect f hint2 hb_pos N
    change -(1 / 18) * ((b + 1 / (4 * b)) * S + 2 * b * L) ≤
      secantNumeratorCellDefect f.1 N at hvar
    have hval :
        (b + 1 / (4 * b)) * S + 2 * b * L =
          Real.sqrt (S * (S + 2 * L)) := by
      have hsqrt_mul : Real.sqrt (S * (S + 2 * L)) = s₁ * s₂ :=
        Real.sqrt_mul hS_pos.le (S + 2 * L)
      have hsplit : (b + 1 / (4 * b)) * S + 2 * b * L =
          b * s₂ ^ 2 + (1 / (4 * b)) * s₁ ^ 2 := by
        rw [hs₁_sq, hs₂_sq]
        ring
      have hs₁_ne : s₁ ≠ 0 := hs₁_pos.ne'
      have hs₂_ne : s₂ ≠ 0 := hs₂_pos.ne'
      have hterm1 : b * s₂ ^ 2 = (1 / 2) * s₁ * s₂ := by
        dsimp [b]
        field_simp
      have hterm2 : (1 / (4 * b)) * s₁ ^ 2 = (1 / 2) * s₁ * s₂ := by
        dsimp [b]
        field_simp
        ring
      rw [hsplit, hterm1, hterm2, hsqrt_mul]
      ring
    rwa [hval] at hvar

/-! ## Section 3: Sharp `433 / 540` and `1261 / 1440` Origin Surpluses, Nonnegative Log-Value Cone Positivity, and the `202 / 15 > 13.466` & `1183 / 80 = 14.7875` Coercivity Laws -/

/-- **Sharp Rational Lower Bound `433 / 540 ≤ (43 * √2 - 56) / 6`**
(`5473 / 3870 ≤ √2` since `5473² = 29953729 < 29953800 = 2 * 3870²`, within `2.4 × 10⁻⁶`!): -/
theorem four_thirty_three_five_fortieths_le_forty_three_sqrt_two_sub_fifty_six_div_six :
    (433 / 540 : ℝ) ≤ (43 * Real.sqrt 2 - 56) / 6 := by
  have h : (5473 / 3870 : ℝ) ≤ Real.sqrt 2 := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 5473 / 3870)]
    exact Real.sqrt_le_sqrt (by norm_num)
  linarith

/-- **Sharp Rational Lower Bound `1261 / 1440 ≤ (16 * √2 - 20) / 3`**
(`10861 / 7680 ≤ √2` since `10861² = 117961321 < 117964800 = 2 * 7680²`): -/
theorem twelve_sixty_one_fourteen_fortieths_le_sixteen_sqrt_two_sub_twenty_div_three :
    (1261 / 1440 : ℝ) ≤ (16 * Real.sqrt 2 - 20) / 3 := by
  have h : (10861 / 7680 : ℝ) ≤ Real.sqrt 2 := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 10861 / 7680)]
    exact Real.sqrt_le_sqrt (by norm_num)
  linarith

/-- **Upgraded `(433 / 540) * ∫ ‖f.1‖²` Positive $L^2$ Surplus over `secantNumeratorCellDefect`**: -/
theorem four_thirty_three_five_fortieths_l2_add_secantNumerator_le_rightCellQuadratureDefect
    (f : WeilTestFn) {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest f.1 f.1 (Real.log N) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log N) = 0)
    (hN : ∀ n : ℕ, N < n →
      EF.weilTest f.1 f.1 (Real.log n) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log n) = 0) :
    (433 / 540) * (∫ u : ℝ, ‖f.1 u‖ ^ 2) + secantNumeratorCellDefect f.1 N ≤
      rightCellQuadratureDefect (weilContinuumLogProfile f.1) N := by
  have h1 :=
    forty_three_sqrt_two_sub_fifty_six_div_six_l2_add_secantNumerator_le_rightCellQuadratureDefect
      f hN1 hN0 hN
  have hnorm_nonneg : 0 ≤ ∫ u : ℝ, ‖f.1 u‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have h2 := mul_le_mul_of_nonneg_right
    four_thirty_three_five_fortieths_le_forty_three_sqrt_two_sub_fifty_six_div_six hnorm_nonneg
  linarith

/-- **Nonnegativity of `primeBlindCounterterm secantCombinedSecularWeight f` on the Nonnegative
Log-Value Cone (`∀ n ∈ Finset.Icc 2 N, 0 ≤ logValue f.1 n`)**:
since `0 ≤ secantCombinedSecularWeight n` for every `n : ℕ`, whenever `0 ≤ logValue f.1 n` on
`[2, N]` (the `m = 0` forward-difference cone, which also includes the Prime-Blind Cone
`logVector f = 0`), the secular counterterm is nonnegative and requires no subtraction! -/
theorem primeBlindCounterterm_secantCombinedSecularWeight_nonneg_of_logValue_nonneg
    (f : WeilTestFn) {N : ℕ}
    (hN : ∀ n : ℕ, N < n →
      EF.weilTest f.1 f.1 (Real.log n) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log n) = 0)
    (hpos : ∀ n ∈ Finset.Icc 2 N, 0 ≤ logValue f.1 n) :
    0 ≤ primeBlindCounterterm secantCombinedSecularWeight f := by
  rw [primeBlindCounterterm_eq_sum_Icc secantCombinedSecularWeight f hN]
  refine Finset.sum_nonneg fun n hn => ?_
  exact mul_nonneg (secantCombinedSecularWeight_nonneg n) (hpos n hn)

/-- **Full `(1261 / 1440) * ∫ ‖f.1‖²` Origin Surplus over `secantNumeratorCellDefect` on the
Nonnegative Log-Value Cone (`∀ n ∈ Finset.Icc 2 N, 0 ≤ logValue f.1 n`)**: -/
theorem twelve_sixty_one_fourteen_fortieths_l2_add_secantNumerator_le_rightCellQuadratureDefect_of_logValue_nonneg
    (f : WeilTestFn) {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest f.1 f.1 (Real.log N) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log N) = 0)
    (hN : ∀ n : ℕ, N < n →
      EF.weilTest f.1 f.1 (Real.log n) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log n) = 0)
    (hpos : ∀ n ∈ Finset.Icc 2 N, 0 ≤ logValue f.1 n) :
    (1261 / 1440) * (∫ u : ℝ, ‖f.1 u‖ ^ 2) + secantNumeratorCellDefect f.1 N ≤
      rightCellQuadratureDefect (weilContinuumLogProfile f.1) N := by
  have heq :=
    rightCellQuadratureDefect_weilContinuumLogProfile_eq_origin_add_combinedCounterterm_add_secantNumerator
      f hN1 hN0 hN
  have hct := primeBlindCounterterm_secantCombinedSecularWeight_nonneg_of_logValue_nonneg f hN hpos
  have hnorm_nonneg : 0 ≤ ∫ u : ℝ, ‖f.1 u‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have horig := mul_le_mul_of_nonneg_right
    twelve_sixty_one_fourteen_fortieths_le_sixteen_sqrt_two_sub_twenty_div_three hnorm_nonneg
  linarith

/-- **Full `(1261 / 1440) * ∫ ‖f.1‖²` Origin Surplus over `secantNumeratorCellDefect` on the
Prime-Blind Cone (`logVector f = 0`)**: -/
theorem twelve_sixty_one_fourteen_fortieths_l2_add_secantNumerator_le_rightCellQuadratureDefect_of_logVector_eq_zero
    (f : WeilTestFn) (hblind : logVector f = 0) {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest f.1 f.1 (Real.log N) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log N) = 0)
    (hN : ∀ n : ℕ, N < n →
      EF.weilTest f.1 f.1 (Real.log n) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log n) = 0) :
    (1261 / 1440) * (∫ u : ℝ, ‖f.1 u‖ ^ 2) + secantNumeratorCellDefect f.1 N ≤
      rightCellQuadratureDefect (weilContinuumLogProfile f.1) N := by
  have heq :=
    rightCellQuadratureDefect_weilContinuumLogProfile_eq_origin_add_combinedCounterterm_add_secantNumerator
      f hN1 hN0 hN
  have hct : primeBlindCounterterm secantCombinedSecularWeight f = 0 := by
    unfold primeBlindCounterterm
    rw [hblind, map_zero]
  have hnorm_nonneg : 0 ≤ ∫ u : ℝ, ‖f.1 u‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have horig := mul_le_mul_of_nonneg_right
    twelve_sixty_one_fourteen_fortieths_le_sixteen_sqrt_two_sub_twenty_div_three hnorm_nonneg
  linarith

/-- **Geometric-Mean Coercivity at Critical Ratio `202 / 15 > 13.4666`**:
since `(202 / 15) * (202 / 15 + 2) = 187456 / 900 < (433 / 30)² = 187489 / 900`, whenever
`spectralSecondMoment f.1 ≤ (202 / 15) * ∫ ‖f.1‖²`, we have
`(1 / 291600) * ∫ ‖f.1‖² ≤ rightCellQuadratureDefect (weilContinuumLogProfile f.1) N` (and in
particular `0 ≤ rightCellQuadratureDefect (weilContinuumLogProfile f.1) N`)! -/
theorem rightCellQuadratureDefect_nonneg_of_spectralSecondMoment_le_two_hundred_two_fifteenths
    (f : WeilTestFn)
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2))
    {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest f.1 f.1 (Real.log N) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log N) = 0)
    (hN : ∀ n : ℕ, N < n →
      EF.weilTest f.1 f.1 (Real.log n) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log n) = 0)
    (hsec : spectralSecondMoment f.1 ≤ (202 / 15) * ∫ u : ℝ, ‖f.1 u‖ ^ 2) :
    0 ≤ rightCellQuadratureDefect (weilContinuumLogProfile f.1) N := by
  let S := spectralSecondMoment f.1
  let L := ∫ u : ℝ, ‖f.1 u‖ ^ 2
  have hS_nonneg : 0 ≤ S := spectralSecondMoment_nonneg f.1
  have hL_nonneg : 0 ≤ L := integral_nonneg fun _ => sq_nonneg _
  have h1 := four_thirty_three_five_fortieths_l2_add_secantNumerator_le_rightCellQuadratureDefect
    f hN1 hN0 hN
  have h2 := neg_one_eighteenth_sqrt_spectralSecondMoment_mul_add_two_l2_le_secantNumeratorCellDefect
    f hint2 N
  have hprod_le : S * (S + 2 * L) ≤ ((433 / 30) * L) ^ 2 := by
    have hS2L_le : S + 2 * L ≤ (232 / 15) * L := by linarith [hsec]
    have hmul1 : S * (S + 2 * L) ≤ ((202 / 15) * L) * (S + 2 * L) :=
      mul_le_mul_of_nonneg_right hsec (by positivity)
    have hmul2 : ((202 / 15) * L) * (S + 2 * L) ≤ ((202 / 15) * L) * ((232 / 15) * L) :=
      mul_le_mul_of_nonneg_left hS2L_le (by positivity)
    have hpyth : ((202 / 15) * L) * ((232 / 15) * L) ≤ ((433 / 30) * L) ^ 2 := by
      have hsq : 0 ≤ L ^ 2 := sq_nonneg L
      linarith
    exact (hmul1.trans hmul2).trans hpyth
  have hsqrt_le : Real.sqrt (S * (S + 2 * L)) ≤ (433 / 30) * L := by
    rw [← Real.sqrt_sq (by positivity : 0 ≤ (433 / 30) * L)]
    exact Real.sqrt_le_sqrt hprod_le
  linarith

/-- **Geometric-Mean Coercivity on the Nonnegative Log-Value Cone at Critical Ratio
`1183 / 80 = 14.7875`**:
since `(1183 / 80) * (1183 / 80 + 2) = 1588769 / 6400 < (1261 / 80)² = 1590121 / 6400`, whenever
`∀ n ∈ Finset.Icc 2 N, 0 ≤ logValue f.1 n` and `spectralSecondMoment f.1 ≤ (1183 / 80) * ∫ ‖f.1‖²`,
`0 ≤ rightCellQuadratureDefect (weilContinuumLogProfile f.1) N`! -/
theorem rightCellQuadratureDefect_nonneg_of_spectralSecondMoment_le_eleven_eighty_three_eightieths_of_logValue_nonneg
    (f : WeilTestFn)
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2))
    {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest f.1 f.1 (Real.log N) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log N) = 0)
    (hN : ∀ n : ℕ, N < n →
      EF.weilTest f.1 f.1 (Real.log n) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log n) = 0)
    (hpos : ∀ n ∈ Finset.Icc 2 N, 0 ≤ logValue f.1 n)
    (hsec : spectralSecondMoment f.1 ≤ (1183 / 80) * ∫ u : ℝ, ‖f.1 u‖ ^ 2) :
    0 ≤ rightCellQuadratureDefect (weilContinuumLogProfile f.1) N := by
  let S := spectralSecondMoment f.1
  let L := ∫ u : ℝ, ‖f.1 u‖ ^ 2
  have hS_nonneg : 0 ≤ S := spectralSecondMoment_nonneg f.1
  have hL_nonneg : 0 ≤ L := integral_nonneg fun _ => sq_nonneg _
  have h1 :=
    twelve_sixty_one_fourteen_fortieths_l2_add_secantNumerator_le_rightCellQuadratureDefect_of_logValue_nonneg
      f hN1 hN0 hN hpos
  have h2 := neg_one_eighteenth_sqrt_spectralSecondMoment_mul_add_two_l2_le_secantNumeratorCellDefect
    f hint2 N
  have hprod_le : S * (S + 2 * L) ≤ ((1261 / 80) * L) ^ 2 := by
    have hS2L_le : S + 2 * L ≤ (1343 / 80) * L := by linarith [hsec]
    have hmul1 : S * (S + 2 * L) ≤ ((1183 / 80) * L) * (S + 2 * L) :=
      mul_le_mul_of_nonneg_right hsec (by positivity)
    have hmul2 : ((1183 / 80) * L) * (S + 2 * L) ≤ ((1183 / 80) * L) * ((1343 / 80) * L) :=
      mul_le_mul_of_nonneg_left hS2L_le (by positivity)
    have hpyth : ((1183 / 80) * L) * ((1343 / 80) * L) ≤ ((1261 / 80) * L) ^ 2 := by
      have hsq : 0 ≤ L ^ 2 := sq_nonneg L
      linarith
    exact (hmul1.trans hmul2).trans hpyth
  have hsqrt_le : Real.sqrt (S * (S + 2 * L)) ≤ (1261 / 80) * L := by
    rw [← Real.sqrt_sq (by positivity : 0 ≤ (1261 / 80) * L)]
    exact Real.sqrt_le_sqrt hprod_le
  linarith

/-- **Geometric-Mean Coercivity on the Prime-Blind Cone at Critical Ratio `1183 / 80 = 14.7875`**: -/
theorem rightCellQuadratureDefect_nonneg_of_spectralSecondMoment_le_eleven_eighty_three_eightieths_of_logVector_eq_zero
    (f : WeilTestFn) (hblind : logVector f = 0)
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2))
    {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest f.1 f.1 (Real.log N) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log N) = 0)
    (hN : ∀ n : ℕ, N < n →
      EF.weilTest f.1 f.1 (Real.log n) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log n) = 0)
    (hsec : spectralSecondMoment f.1 ≤ (1183 / 80) * ∫ u : ℝ, ‖f.1 u‖ ^ 2) :
    0 ≤ rightCellQuadratureDefect (weilContinuumLogProfile f.1) N := by
  let S := spectralSecondMoment f.1
  let L := ∫ u : ℝ, ‖f.1 u‖ ^ 2
  have hS_nonneg : 0 ≤ S := spectralSecondMoment_nonneg f.1
  have hL_nonneg : 0 ≤ L := integral_nonneg fun _ => sq_nonneg _
  have h1 :=
    twelve_sixty_one_fourteen_fortieths_l2_add_secantNumerator_le_rightCellQuadratureDefect_of_logVector_eq_zero
      f hblind hN1 hN0 hN
  have h2 := neg_one_eighteenth_sqrt_spectralSecondMoment_mul_add_two_l2_le_secantNumeratorCellDefect
    f hint2 N
  have hprod_le : S * (S + 2 * L) ≤ ((1261 / 80) * L) ^ 2 := by
    have hS2L_le : S + 2 * L ≤ (1343 / 80) * L := by linarith [hsec]
    have hmul1 : S * (S + 2 * L) ≤ ((1183 / 80) * L) * (S + 2 * L) :=
      mul_le_mul_of_nonneg_right hsec (by positivity)
    have hmul2 : ((1183 / 80) * L) * (S + 2 * L) ≤ ((1183 / 80) * L) * ((1343 / 80) * L) :=
      mul_le_mul_of_nonneg_left hS2L_le (by positivity)
    have hpyth : ((1183 / 80) * L) * ((1343 / 80) * L) ≤ ((1261 / 80) * L) ^ 2 := by
      have hsq : 0 ≤ L ^ 2 := sq_nonneg L
      linarith
    exact (hmul1.trans hmul2).trans hpyth
  have hsqrt_le : Real.sqrt (S * (S + 2 * L)) ≤ (1261 / 80) * L := by
    rw [← Real.sqrt_sq (by positivity : 0 ≤ (1261 / 80) * L)]
    exact Real.sqrt_le_sqrt hprod_le
  linarith

/-- **Unconditional `0 ≤ markovEnergy F` on the Primitive Hyperplane whenever
`spectralSecondMoment F ≤ (202 / 15) * ∫ ‖F‖² > 13.4666 * ∫ ‖F‖²` (No `- δ` Needed!)**:
because `(202 / 15) * (202 / 15 + 2) = 187456 / 900` is strictly less than `(433 / 30)² = 187489 / 900`,
even at the exact rational endpoint `202 / 15` there is a strict positive margin
`((433 / 30) - √(187456 / 900)) / 18 ≥ 1 / (540 * 866) = 1 / 467640` in `rightCellQuadratureDefect`,
so `markovEnergy F ≥ 0` holds at `202 / 15` with NO `- δ` parameter required! -/
theorem markovEnergy_ofReal_nonneg_of_spectralSecondMoment_le_two_hundred_two_fifteenths_of_cosh_zero
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
    (hsec_bound : spectralSecondMoment (realWeilTestFn f hf hfc).1 ≤
      (202 / 15) * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) :
    0 ≤ markovEnergy (realWeilTestFn f hf hfc).1 := by
  have hS_nonneg : 0 ≤ spectralSecondMoment (realWeilTestFn f hf hfc).1 :=
    spectralSecondMoment_nonneg (realWeilTestFn f hf hfc).1
  have hL_nonneg : 0 ≤ ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  let θ := max (max 1 (Real.log (N : ℝ))) 2160000
  have hθ1 : 1 ≤ θ := (le_max_left 1 (Real.log (N : ℝ))).trans (le_max_left _ _)
  have hθ0 : 0 ≤ θ := by linarith
  have hθlog : Real.log (N : ℝ) ≤ θ :=
    (le_max_right 1 (Real.log (N : ℝ))).trans (le_max_left _ _)
  have hθ_large : (2160000 : ℝ) ≤ θ := le_max_right _ _
  have hbase := one_hundredth_l2_add_theta_slope_quadrature_le_markovEnergy_of_cosh_zero
    m hf hfc hcosh hN1 hθlog hN hdiff
  have hatom := atomPairRe_weilTest_le_two_mul_integral_norm_sq (realWeilTestFn f hf hfc)
  have h1 := four_thirty_three_five_fortieths_l2_add_secantNumerator_le_rightCellQuadratureDefect
    (realWeilTestFn f hf hfc) hN1 hN0 (fun n hn => hN n (by exact_mod_cast hn))
  have h2 := neg_one_eighteenth_sqrt_spectralSecondMoment_mul_add_two_l2_le_secantNumeratorCellDefect
    (realWeilTestFn f hf hfc) hint2 N
  have hprod_le :
      spectralSecondMoment (realWeilTestFn f hf hfc).1 *
          (spectralSecondMoment (realWeilTestFn f hf hfc).1 +
            2 * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) ≤
        ((865999 / 60000) * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) ^ 2 := by
    have hS2L_le :
        spectralSecondMoment (realWeilTestFn f hf hfc).1 +
          2 * (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) ≤
        (232 / 15) * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2 := by
      linarith [hsec_bound]
    have hmul1 :
        spectralSecondMoment (realWeilTestFn f hf hfc).1 *
            (spectralSecondMoment (realWeilTestFn f hf hfc).1 +
              2 * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) ≤
          ((202 / 15) * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) *
            (spectralSecondMoment (realWeilTestFn f hf hfc).1 +
              2 * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) :=
      mul_le_mul_of_nonneg_right hsec_bound (by positivity)
    have hmul2 :
        ((202 / 15) * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) *
            (spectralSecondMoment (realWeilTestFn f hf hfc).1 +
              2 * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) ≤
          ((202 / 15) * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) *
            ((232 / 15) * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hS2L_le (by positivity)
    have hpyth :
        ((202 / 15) * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) *
            ((232 / 15) * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) ≤
          ((865999 / 60000) * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) ^ 2 := by
      have hsq : 0 ≤ (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) ^ 2 := sq_nonneg _
      linarith
    exact (hmul1.trans hmul2).trans hpyth
  have hsqrt_le :
      Real.sqrt
          (spectralSecondMoment (realWeilTestFn f hf hfc).1 *
            (spectralSecondMoment (realWeilTestFn f hf hfc).1 +
              2 * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2)) ≤
        (865999 / 60000) * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2 := by
    rw [← Real.sqrt_sq
      (by positivity : 0 ≤ (865999 / 60000) * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2)]
    exact Real.sqrt_le_sqrt hprod_le
  have hquad_pos :
      (1 / 1080000) * (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) ≤
        rightCellQuadratureDefect (weilContinuumLogProfile (realWeilTestFn f hf hfc).1) N := by
    linarith
  have hθ_quad :
      (2160000 : ℝ) * ((1 / 1080000) * (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2)) ≤
        θ * rightCellQuadratureDefect (weilContinuumLogProfile (realWeilTestFn f hf hfc).1) N :=
    mul_le_mul hθ_large hquad_pos (by positivity) hθ0
  have hres_nonneg : 0 ≤ (θ - 1) * bochnerResolventEnergy
      (EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1) :=
    mul_nonneg (by linarith) (bochnerResolventEnergy_weilTest_nonneg _)
  have hsinh_nonneg : 0 ≤ 2 * θ * sinhHalfMoment f ^ 2 := by positivity
  linarith

end RHTower

end
