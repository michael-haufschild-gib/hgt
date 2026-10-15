import GaloisForLFunctions.RHTower.MarkovSimpsonLogSecantAndElevenPointSixRatioPBAP

/-!
# Exact Cubic Hermite Logarithmic Envelope, Quintic Chebyshev Cell Quadrature, the `1 / 18` Logarithmic Cell-Defect Bound, and the `67 / 5 = 13.4` Coercivity Ratio (`59 / 4 = 14.75` on the Prime-Blind Cone) for Route HF / PBAP

This module sharpens the Markov/PBAP logarithmic secant cell-defect theory from Module 58
(`MarkovSimpsonLogSecantAndElevenPointSixRatioPBAP`) in three complementary directions that
eliminate all separate upper/lower endpoint slack in the logarithmic slope difference AND retain
the negative Chebyshev covariance term in the product of two secants:

1. **Exact Cubic Hermite Envelope for `Real.log x - cellSecant Real.log n x` (`hermite_log_sub_cellSecant_log_le`)**:
   Instead of bounding `(Real.log x - Real.log (n - 1)) / (x - (n - 1))` and
   `(Real.log n - Real.log x) / (n - x)` by separate rational envelopes, we compare `Real.log x`
   directly against its **exact Cubic Hermite Interpolant** on `[n - 1, n]`:
   `H₃(x) = cellSecant Real.log n x + (A₀(n)(n - x) + A₁(n)(x - (n - 1))) * cellParabola n x`,
   where
   - `A₀(n) = 1 / (n - 1) - (Real.log n - Real.log (n - 1))`,
   - `A₁(n) = (Real.log n - Real.log (n - 1)) - 1 / n`.
   Because `(n - 1) A₀(n) + n A₁(n) = Real.log n - Real.log (n - 1)` and
   `(n - 1) n (A₀(n) + A₁(n)) = 1`, the derivative of `D(t) = H₃(t) - Real.log t` satisfies the
   exact polynomial factorization
   `t * D'(t) = cellParabola n t * ((A₀(n) + A₁(n)) - 3 * (A₀(n) - A₁(n)) * t)`.
   Since `A₀(n) - A₁(n) ≥ 0` and `D(n - 1) = D(n) = 0`, first-order MVT on `[n - 1, x]` (when
   `D'(x) ≥ 0`) or `[x, n]` (when `D'(x) ≤ 0`) yields `0 ≤ D(x)` for all `x ∈ [n - 1, n]`.

2. **Exact Quintic Chebyshev Cell Integral (`integral_secant_mul_secant_mul_cellParabola_eq`)**:
   Instead of dropping the negative Chebyshev covariance term
   `-(A₀ - A₁)(B₀ - B₁) * cellParabola n x` when multiplying the two secants
   `A₀(n - x) + A₁(x - (n - 1))` and `B₀(n - x) + B₁(x - (n - 1))`, we integrate the full
   degree-4 polynomial against `cellParabola n x` over `[n - 1, n]`:
   `∫_{n-1}^n (A₀(n - x) + A₁(x - (n - 1)))(B₀(n - x) + B₁(x - (n - 1))) * cellParabola n x dx = (A₀ B₀ + A₁ B₁) / 12 - (A₀ - A₁)(B₀ - B₁) / 30`.
   Substituting `A₀ = hermiteLogEndpoint0 n`, `A₁ = hermiteLogEndpoint1 n`,
   `B₀ = 1 / √(n - 1)`, `B₁ = 1 / √n` yields the exact telescopic-plus-negative-correction identity
   (`hermiteQuinticCellWeight_eq`):
   `hermiteQuinticCellWeight n = (1 / 12) * (1 / ((n - 1)√(n - 1)) - 1 / (n√n)) - (1 / √(n - 1) - 1 / √n) * ((1 / 30)(1 / (n - 1) + 1 / n) + (Real.log n - Real.log (n - 1)) / 60)`.

3. **Fourth-Order Midpoint Lower Bound for `Real.log b - Real.log a`, the `(n - 5)(n + 4) ≥ 0`
   Tail Telescoping Law, and the Global `1 / 18` Logarithmic Cell-Defect Bound**:
   - By first-order MVT on `g(t) = Real.log t - Real.log a - 2(t - a)/(t + a) - 2(t - a)³/(3(t + a)³)`
     whose derivative is `g'(t) = (t - a)⁴ / (t(t + a)⁴) ≥ 0`, we prove
     `2(b - a)/(a + b) + 2(b - a)³/(3(a + b)³) ≤ Real.log b - Real.log a`
     (giving `56 / 81 ≤ Real.log 2` at `n = 2`).
   - Using `(b - a)(b² + a²) - (2 / 3)(b³ - a³) = (1 / 3)(b - a)³ ≥ 0` and, for `n ≥ 5`,
     `81(n - 1)n - 20(2n - 1)² = (n - 5)(n + 4) ≥ 0`, we prove that for all `n ≥ 5`,
     `hermiteQuinticCellWeight n ≤ (811 / 14580) * (1 / ((n - 1)√(n - 1)) - 1 / (n√n))`,
     which telescopes on `[5, N]` to `≤ 811 / 116640`.
   - Combining `n = 2, 3, 4` with the `[5, N]` tail proves
     `∑_{n=2}^N hermiteQuinticCellWeight n ≤ 1 / 18`,
     yielding:
     - `-(1 / 18) * (spectralSecondMoment f.1 + ∫ ‖f.1‖²) ≤ secantNumeratorCellDefect f.1 N`,
     - `(67 / 90) * ∫ ‖f.1‖² - (1 / 18) * spectralSecondMoment f.1 ≤ rightCellQuadratureDefect (weilContinuumLogProfile f.1) N`
       (critical ratio **`67 / 5 = 13.4`**!), and
     - on the Prime-Blind Cone (`logVector f = 0`),
       `(59 / 72) * ∫ ‖f.1‖² - (1 / 18) * spectralSecondMoment f.1 ≤ rightCellQuadratureDefect (weilContinuumLogProfile f.1) N`
       (critical ratio **`59 / 4 = 14.75`**!).
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

/-! ## Section 1: Exact Cubic Hermite Envelope for `Real.log x - cellSecant Real.log n x` and the Quintic Chebyshev Cell Integral -/

/-- The exact left-endpoint slope excess of `Real.log` over its secant on `[n - 1, n]`:
`A₀(n) = 1 / (n - 1) - (Real.log n - Real.log (n - 1))`. -/
def hermiteLogEndpoint0 (n : ℕ) : ℝ :=
  1 / ((n : ℝ) - 1) - (Real.log (n : ℝ) - Real.log ((n : ℝ) - 1))

/-- The exact right-endpoint slope excess of the secant of `Real.log` over `1 / n` on `[n - 1, n]`:
`A₁(n) = (Real.log n - Real.log (n - 1)) - 1 / n`. -/
def hermiteLogEndpoint1 (n : ℕ) : ℝ :=
  (Real.log (n : ℝ) - Real.log ((n : ℝ) - 1)) - 1 / (n : ℝ)

theorem hermiteLogEndpoint_linear_log_eq {n : ℕ} (hn : 2 ≤ n) :
    Real.log (n : ℝ) - Real.log ((n : ℝ) - 1) =
      ((n : ℝ) - 1) * hermiteLogEndpoint0 n + (n : ℝ) * hermiteLogEndpoint1 n := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn1_ne : (n : ℝ) - 1 ≠ 0 := by linarith
  have hn_ne : (n : ℝ) ≠ 0 := by linarith
  calc Real.log (n : ℝ) - Real.log ((n : ℝ) - 1)
    _ = ((n : ℝ) - 1) * (1 / ((n : ℝ) - 1)) - (n : ℝ) * (1 / (n : ℝ)) +
          (Real.log (n : ℝ) - Real.log ((n : ℝ) - 1)) := by
        rw [mul_one_div_cancel hn1_ne, mul_one_div_cancel hn_ne]
        ring
    _ = ((n : ℝ) - 1) * hermiteLogEndpoint0 n + (n : ℝ) * hermiteLogEndpoint1 n := by
        unfold hermiteLogEndpoint0 hermiteLogEndpoint1
        ring

theorem hermiteLogEndpoint_add_mul_eq_one {n : ℕ} (hn : 2 ≤ n) :
    ((n : ℝ) - 1) * (n : ℝ) * (hermiteLogEndpoint0 n + hermiteLogEndpoint1 n) = 1 := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn1_ne : (n : ℝ) - 1 ≠ 0 := by linarith
  have hn_ne : (n : ℝ) ≠ 0 := by linarith
  calc ((n : ℝ) - 1) * (n : ℝ) * (hermiteLogEndpoint0 n + hermiteLogEndpoint1 n)
    _ = (n : ℝ) * (((n : ℝ) - 1) * (1 / ((n : ℝ) - 1))) -
          ((n : ℝ) - 1) * ((n : ℝ) * (1 / (n : ℝ))) := by
        unfold hermiteLogEndpoint0 hermiteLogEndpoint1
        ring
    _ = (n : ℝ) * 1 - ((n : ℝ) - 1) * 1 := by
        rw [mul_one_div_cancel hn1_ne, mul_one_div_cancel hn_ne]
    _ = 1 := by ring

theorem hermiteLogEndpoint0_sub_hermiteLogEndpoint1_nonneg {n : ℕ} (hn : 2 ≤ n) :
    0 ≤ hermiteLogEndpoint0 n - hermiteLogEndpoint1 n := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn1_pos : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hn1_le : (n : ℝ) - 1 ≤ (n : ℝ) := by linarith
  have htrap := log_sub_log_le_half_mul_inv_add_inv hn1_pos hn1_le
  unfold hermiteLogEndpoint0 hermiteLogEndpoint1
  linarith

/-- **Exact Cubic Hermite Upper Bound for `Real.log x - cellSecant Real.log n x` on `[n - 1, n]`**:
for any `2 ≤ n` and `x ∈ [n - 1, n]`,
`Real.log x - cellSecant Real.log n x ≤ (hermiteLogEndpoint0 n * (n - x) + hermiteLogEndpoint1 n * (x - (n - 1))) * cellParabola n x`. -/
theorem hermite_log_sub_cellSecant_log_le
    {n : ℕ} (hn : 2 ≤ n) {x : ℝ} (hx : x ∈ Icc ((n : ℝ) - 1) (n : ℝ)) :
    Real.log x - cellSecant Real.log n x ≤
      (hermiteLogEndpoint0 n * ((n : ℝ) - x) +
        hermiteLogEndpoint1 n * (x - ((n : ℝ) - 1))) * cellParabola n x := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn1_pos : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  let L : ℝ := Real.log (n : ℝ) - Real.log ((n : ℝ) - 1)
  let A₀ : ℝ := hermiteLogEndpoint0 n
  let A₁ : ℝ := hermiteLogEndpoint1 n
  let D : ℝ → ℝ := fun t =>
    Real.log ((n : ℝ) - 1) +
      (L + A₀) * (t - ((n : ℝ) - 1)) -
      (2 * A₀ - A₁) * (t - ((n : ℝ) - 1)) ^ 2 +
      (A₀ - A₁) * (t - ((n : ℝ) - 1)) ^ 3 -
      Real.log t
  let D' : ℝ → ℝ := fun t =>
    0 + (L + A₀) * (1 - 0) -
      (2 * A₀ - A₁) * ((2 : ℕ) * (t - ((n : ℝ) - 1)) ^ (2 - 1) * (1 - 0)) +
      (A₀ - A₁) * ((3 : ℕ) * (t - ((n : ℝ) - 1)) ^ (3 - 1) * (1 - 0)) -
      t⁻¹
  have hd : ∀ t ∈ Icc ((n : ℝ) - 1) (n : ℝ), HasDerivAt D (D' t) t := by
    intro t ht
    have ht_pos : 0 < t := hn1_pos.trans_le ht.1
    have hu : HasDerivAt (fun y => y - ((n : ℝ) - 1)) (1 - 0) t :=
      (hasDerivAt_id t).sub (hasDerivAt_const t ((n : ℝ) - 1))
    exact ((((hasDerivAt_const t (Real.log ((n : ℝ) - 1))).add
      (hu.const_mul (L + A₀))).sub
      ((hu.pow 2).const_mul (2 * A₀ - A₁))).add
      ((hu.pow 3).const_mul (A₀ - A₁))).sub
      (Real.hasDerivAt_log ht_pos.ne')
  have hL : L = ((n : ℝ) - 1) * A₀ + (n : ℝ) * A₁ := hermiteLogEndpoint_linear_log_eq hn
  have hone : ((n : ℝ) - 1) * (n : ℝ) * (A₀ + A₁) = 1 := hermiteLogEndpoint_add_mul_eq_one hn
  have hD'_mul : ∀ t ∈ Icc ((n : ℝ) - 1) (n : ℝ),
      t * D' t = cellParabola n t * ((A₀ + A₁) - 3 * (A₀ - A₁) * t) := by
    intro t ht
    have ht_pos : 0 < t := hn1_pos.trans_le ht.1
    calc t * D' t
      _ = t * (0 + (L + A₀) * (1 - 0) -
            (2 * A₀ - A₁) * ((2 : ℕ) * (t - ((n : ℝ) - 1)) ^ (2 - 1) * (1 - 0)) +
            (A₀ - A₁) * ((3 : ℕ) * (t - ((n : ℝ) - 1)) ^ (3 - 1) * (1 - 0))) - 1 := by
          dsimp [D']
          rw [mul_sub, mul_inv_cancel₀ ht_pos.ne']
      _ = t * (0 + ((((n : ℝ) - 1) * A₀ + (n : ℝ) * A₁) + A₀) * (1 - 0) -
            (2 * A₀ - A₁) * ((2 : ℕ) * (t - ((n : ℝ) - 1)) ^ (2 - 1) * (1 - 0)) +
            (A₀ - A₁) * ((3 : ℕ) * (t - ((n : ℝ) - 1)) ^ (3 - 1) * (1 - 0))) -
            ((n : ℝ) - 1) * (n : ℝ) * (A₀ + A₁) := by
          rw [hL, hone]
      _ = cellParabola n t * ((A₀ + A₁) - 3 * (A₀ - A₁) * t) := by
          unfold cellParabola
          push_cast
          ring
  have hD_left : D ((n : ℝ) - 1) = 0 := by
    dsimp [D]
    ring
  have hD_right : D (n : ℝ) = 0 := by
    dsimp [D, L]
    ring
  have hA_diff_nonneg : 0 ≤ A₀ - A₁ := hermiteLogEndpoint0_sub_hermiteLogEndpoint1_nonneg hn
  have hD_nonneg : 0 ≤ D x := by
    rcases le_total 0 ((A₀ + A₁) - 3 * (A₀ - A₁) * x) with hlin_pos | hlin_neg
    · rcases eq_or_lt_of_le hx.1 with h_eq | h_lt
      · rw [← h_eq, hD_left]
      · obtain ⟨c, hc, hc_slope⟩ := exists_hasDerivAt_eq_slope D D' h_lt
          (fun t ht => (hd t ⟨ht.1, ht.2.trans hx.2⟩).continuousAt.continuousWithinAt)
          (fun t ht => hd t ⟨ht.1.le, ht.2.le.trans hx.2⟩)
        have hc_mem : c ∈ Icc ((n : ℝ) - 1) (n : ℝ) := ⟨hc.1.le, hc.2.le.trans hx.2⟩
        have hc_pos : 0 < c := hn1_pos.trans hc.1
        have hpar_c : 0 ≤ cellParabola n c := cellParabola_nonneg_of_mem_Icc hc_mem
        have hlin_c : 0 ≤ (A₀ + A₁) - 3 * (A₀ - A₁) * c := by
          have hcx : c ≤ x := hc.2.le
          have hmul : 3 * (A₀ - A₁) * c ≤ 3 * (A₀ - A₁) * x :=
            mul_le_mul_of_nonneg_left hcx (by linarith)
          linarith
        have hmul_c : 0 ≤ c * D' c := by
          rw [hD'_mul c hc_mem]
          exact mul_nonneg hpar_c hlin_c
        have hD'_c : 0 ≤ D' c := nonneg_of_mul_nonneg_right hmul_c hc_pos
        have hba_pos : 0 < x - ((n : ℝ) - 1) := sub_pos.mpr h_lt
        have hdiff_eq : D x - D ((n : ℝ) - 1) = D' c * (x - ((n : ℝ) - 1)) :=
          ((eq_div_iff hba_pos.ne').mp hc_slope).symm
        linarith [mul_nonneg hD'_c hba_pos.le]
    · rcases eq_or_lt_of_le hx.2 with rfl | h_lt
      · rw [hD_right]
      · obtain ⟨c, hc, hc_slope⟩ := exists_hasDerivAt_eq_slope D D' h_lt
          (fun t ht => (hd t ⟨hx.1.trans ht.1, ht.2⟩).continuousAt.continuousWithinAt)
          (fun t ht => hd t ⟨hx.1.trans ht.1.le, ht.2.le⟩)
        have hc_mem : c ∈ Icc ((n : ℝ) - 1) (n : ℝ) := ⟨hx.1.trans hc.1.le, hc.2.le⟩
        have hc_pos : 0 < c := hn1_pos.trans_le hc_mem.1
        have hpar_c : 0 ≤ cellParabola n c := cellParabola_nonneg_of_mem_Icc hc_mem
        have hlin_c : (A₀ + A₁) - 3 * (A₀ - A₁) * c ≤ 0 := by
          have hxc : x ≤ c := hc.1.le
          have hmul : 3 * (A₀ - A₁) * x ≤ 3 * (A₀ - A₁) * c :=
            mul_le_mul_of_nonneg_left hxc (by linarith)
          linarith
        have hmul_c : c * D' c ≤ 0 := by
          rw [hD'_mul c hc_mem]
          exact mul_nonpos_of_nonneg_of_nonpos hpar_c hlin_c
        have hD'_c : D' c ≤ 0 := nonpos_of_mul_nonpos_right hmul_c hc_pos
        have hba_pos : 0 < (n : ℝ) - x := sub_pos.mpr h_lt
        have hdiff_eq : D (n : ℝ) - D x = D' c * ((n : ℝ) - x) :=
          ((eq_div_iff hba_pos.ne').mp hc_slope).symm
        linarith [mul_nonpos_of_nonpos_of_nonneg hD'_c hba_pos.le]
  have hD_eq :
      D x = (A₀ * ((n : ℝ) - x) + A₁ * (x - ((n : ℝ) - 1))) * cellParabola n x -
        (Real.log x - cellSecant Real.log n x) := by
    dsimp [D, L]
    unfold cellParabola cellSecant
    ring
  linarith

theorem hermiteLogEndpoint1_nonneg {n : ℕ} (hn : 2 ≤ n) :
    0 ≤ hermiteLogEndpoint1 n := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn1_pos : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hn_pos : (0 : ℝ) < (n : ℝ) := by linarith
  have h2n1_pos : (0 : ℝ) < 2 * (n : ℝ) - 1 := by linarith
  have hn1_le : (n : ℝ) - 1 ≤ (n : ℝ) := by linarith
  have hmid := two_mul_sub_div_add_le_log_sub_log hn1_pos hn1_le
  have hle : 1 / (n : ℝ) ≤ 2 * ((n : ℝ) - ((n : ℝ) - 1)) / ((n : ℝ) - 1 + (n : ℝ)) := by
    rw [div_le_div_iff₀ hn_pos (by linarith)]
    linarith
  unfold hermiteLogEndpoint1
  linarith

theorem hermiteLogEndpoint0_nonneg {n : ℕ} (hn : 2 ≤ n) :
    0 ≤ hermiteLogEndpoint0 n := by
  have h1 := hermiteLogEndpoint1_nonneg hn
  have hdiff := hermiteLogEndpoint0_sub_hermiteLogEndpoint1_nonneg hn
  linarith

/-- **Pointwise Cubic Hermite × Secant `1 / √x` Upper Bound on `[n - 1, n]`**:
for `2 ≤ n` and `x ∈ [n - 1, n]`,
`(Real.log x - cellSecant Real.log n x) / √x ≤ (hermiteLogEndpoint0 n * (n - x) + hermiteLogEndpoint1 n * (x - (n - 1))) * ((1 / √(n - 1)) * (n - x) + (1 / √n) * (x - (n - 1))) * cellParabola n x`. -/
theorem hermite_log_sub_cellSecant_log_div_sqrt_le
    {n : ℕ} (hn : 2 ≤ n) {x : ℝ} (hx : x ∈ Icc ((n : ℝ) - 1) (n : ℝ)) :
    (Real.log x - cellSecant Real.log n x) / Real.sqrt x ≤
      (hermiteLogEndpoint0 n * ((n : ℝ) - x) +
        hermiteLogEndpoint1 n * (x - ((n : ℝ) - 1))) *
      ((1 / Real.sqrt ((n : ℝ) - 1)) * ((n : ℝ) - x) +
        (1 / Real.sqrt (n : ℝ)) * (x - ((n : ℝ) - 1))) *
      cellParabola n x := by
  have hA0 : 0 ≤ hermiteLogEndpoint0 n := hermiteLogEndpoint0_nonneg hn
  have hA1 : 0 ≤ hermiteLogEndpoint1 n := hermiteLogEndpoint1_nonneg hn
  have h1 : 0 ≤ (n : ℝ) - x := sub_nonneg.mpr hx.2
  have h2 : 0 ≤ x - ((n : ℝ) - 1) := sub_nonneg.mpr hx.1
  have hpar : 0 ≤ cellParabola n x := cellParabola_nonneg_of_mem_Icc hx
  have hcub_nonneg :
      0 ≤ (hermiteLogEndpoint0 n * ((n : ℝ) - x) +
        hermiteLogEndpoint1 n * (x - ((n : ℝ) - 1))) * cellParabola n x := by
    positivity
  have hsqrt_nonneg : 0 ≤ 1 / Real.sqrt x := by positivity
  have hlog_le := hermite_log_sub_cellSecant_log_le hn hx
  have hsqrt_le := inv_sqrt_le_cellSecant_inv_sqrt hn hx
  have hstep1 :
      (Real.log x - cellSecant Real.log n x) / Real.sqrt x ≤
        ((hermiteLogEndpoint0 n * ((n : ℝ) - x) +
          hermiteLogEndpoint1 n * (x - ((n : ℝ) - 1))) * cellParabola n x) *
          (1 / Real.sqrt x) := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_right hlog_le hsqrt_nonneg
  have hstep2 :
      ((hermiteLogEndpoint0 n * ((n : ℝ) - x) +
        hermiteLogEndpoint1 n * (x - ((n : ℝ) - 1))) * cellParabola n x) *
        (1 / Real.sqrt x) ≤
      ((hermiteLogEndpoint0 n * ((n : ℝ) - x) +
        hermiteLogEndpoint1 n * (x - ((n : ℝ) - 1))) * cellParabola n x) *
        (((n : ℝ) - x) * (1 / Real.sqrt ((n : ℝ) - 1)) +
          (x - ((n : ℝ) - 1)) * (1 / Real.sqrt (n : ℝ))) :=
    mul_le_mul_of_nonneg_left hsqrt_le hcub_nonneg
  calc (Real.log x - cellSecant Real.log n x) / Real.sqrt x
    _ ≤ ((hermiteLogEndpoint0 n * ((n : ℝ) - x) +
          hermiteLogEndpoint1 n * (x - ((n : ℝ) - 1))) * cellParabola n x) *
        (((n : ℝ) - x) * (1 / Real.sqrt ((n : ℝ) - 1)) +
          (x - ((n : ℝ) - 1)) * (1 / Real.sqrt (n : ℝ))) := hstep1.trans hstep2
    _ = (hermiteLogEndpoint0 n * ((n : ℝ) - x) +
          hermiteLogEndpoint1 n * (x - ((n : ℝ) - 1))) *
        ((1 / Real.sqrt ((n : ℝ) - 1)) * ((n : ℝ) - x) +
          (1 / Real.sqrt (n : ℝ)) * (x - ((n : ℝ) - 1))) *
        cellParabola n x := by ring

/-- **Exact Quintic Chebyshev Cell Integral**:
for any `A₀, A₁, B₀, B₁ : ℝ` and `n : ℕ`,
`∫ x in (n - 1)..n, (A₀(n - x) + A₁(x - (n - 1)))(B₀(n - x) + B₁(x - (n - 1))) * cellParabola n x = (A₀ B₀ + A₁ B₁) / 12 - (A₀ - A₁)(B₀ - B₁) / 30`. -/
theorem integral_secant_mul_secant_mul_cellParabola_eq
    (A₀ A₁ B₀ B₁ : ℝ) (n : ℕ) :
    (∫ x in ((n : ℝ) - 1)..(n : ℝ),
      (A₀ * ((n : ℝ) - x) + A₁ * (x - ((n : ℝ) - 1))) *
        (B₀ * ((n : ℝ) - x) + B₁ * (x - ((n : ℝ) - 1))) *
        cellParabola n x) =
      (A₀ * B₀ + A₁ * B₁) / 12 - (A₀ - A₁) * (B₀ - B₁) / 30 := by
  let Q : ℝ → ℝ := fun x =>
    A₀ * B₀ * ((1 / 2) * (x - ((n : ℝ) - 1)) ^ 2 -
      (2 / 3) * (x - ((n : ℝ) - 1)) ^ 3 +
      (1 / 4) * (x - ((n : ℝ) - 1)) ^ 4) +
    A₁ * B₁ * ((1 / 3) * (x - ((n : ℝ) - 1)) ^ 3 -
      (1 / 4) * (x - ((n : ℝ) - 1)) ^ 4) -
    (A₀ - A₁) * (B₀ - B₁) * ((1 / 3) * (x - ((n : ℝ) - 1)) ^ 3 -
      (1 / 2) * (x - ((n : ℝ) - 1)) ^ 4 +
      (1 / 5) * (x - ((n : ℝ) - 1)) ^ 5)
  have hderiv : ∀ x ∈ uIcc ((n : ℝ) - 1) (n : ℝ),
      HasDerivAt Q
        ((A₀ * ((n : ℝ) - x) + A₁ * (x - ((n : ℝ) - 1))) *
          (B₀ * ((n : ℝ) - x) + B₁ * (x - ((n : ℝ) - 1))) *
          cellParabola n x) x := by
    intro x _
    have hu : HasDerivAt (fun t => t - ((n : ℝ) - 1)) (1 - 0) x :=
      (hasDerivAt_id x).sub (hasDerivAt_const x ((n : ℝ) - 1))
    have h1 := ((((hu.pow 2).const_mul (1 / 2)).sub
      ((hu.pow 3).const_mul (2 / 3))).add
      ((hu.pow 4).const_mul (1 / 4))).const_mul (A₀ * B₀)
    have h2 := (((hu.pow 3).const_mul (1 / 3)).sub
      ((hu.pow 4).const_mul (1 / 4))).const_mul (A₁ * B₁)
    have h3 := ((((hu.pow 3).const_mul (1 / 3)).sub
      ((hu.pow 4).const_mul (1 / 2))).add
      ((hu.pow 5).const_mul (1 / 5))).const_mul ((A₀ - A₁) * (B₀ - B₁))
    refine ((h1.add h2).sub h3).congr_deriv ?_
    unfold cellParabola
    push_cast
    ring
  have hint : IntervalIntegrable
      (fun x => (A₀ * ((n : ℝ) - x) + A₁ * (x - ((n : ℝ) - 1))) *
        (B₀ * ((n : ℝ) - x) + B₁ * (x - ((n : ℝ) - 1))) *
        cellParabola n x)
      volume ((n : ℝ) - 1) (n : ℝ) := by
    apply Continuous.intervalIntegrable
    unfold cellParabola
    continuity
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  dsimp [Q]
  ring

/-! ## Section 2: Fourth-Order Midpoint Lower Bound for `Real.log b - Real.log a`, the `(n - 5)(n + 4) ≥ 0` Tail Telescoping Law, and the `1 / 18` Series Bound -/

/-- The exact Quintic Chebyshev cell integral weight on `[n - 1, n]`:
`(A₀ B₀ + A₁ B₁) / 12 - (A₀ - A₁)(B₀ - B₁) / 30` where `A₀, A₁` are the Cubic Hermite
logarithmic endpoint slopes and `B₀ = 1 / √(n - 1)`, `B₁ = 1 / √n`. -/
def hermiteQuinticCellWeight (n : ℕ) : ℝ :=
  (hermiteLogEndpoint0 n * (1 / Real.sqrt ((n : ℝ) - 1)) +
    hermiteLogEndpoint1 n * (1 / Real.sqrt (n : ℝ))) / 12 -
  (hermiteLogEndpoint0 n - hermiteLogEndpoint1 n) *
    (1 / Real.sqrt ((n : ℝ) - 1) - 1 / Real.sqrt (n : ℝ)) / 30

/-- **Exact Telescopic-Plus-Negative-Correction Decomposition of `hermiteQuinticCellWeight`**: -/
theorem hermiteQuinticCellWeight_eq (n : ℕ) :
    hermiteQuinticCellWeight n =
      (1 / 12) * ((1 / ((n : ℝ) - 1)) * (1 / Real.sqrt ((n : ℝ) - 1)) -
        (1 / (n : ℝ)) * (1 / Real.sqrt (n : ℝ))) -
      (1 / Real.sqrt ((n : ℝ) - 1) - 1 / Real.sqrt (n : ℝ)) *
        ((1 / 30) * (1 / ((n : ℝ) - 1) + 1 / (n : ℝ)) +
          (Real.log (n : ℝ) - Real.log ((n : ℝ) - 1)) / 60) := by
  unfold hermiteQuinticCellWeight hermiteLogEndpoint0 hermiteLogEndpoint1
  ring

/-- **Fourth-Order Midpoint Lower Bound for `Real.log b - Real.log a`**:
for any `0 < a ≤ b`,
`2 * (b - a) / (a + b) + 2 * (b - a) ^ 3 / (3 * (a + b) ^ 3) ≤ Real.log b - Real.log a`. -/
theorem two_mul_sub_div_add_add_two_mul_cube_div_three_cube_le_log_sub_log
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    2 * (b - a) / (a + b) + 2 * (b - a) ^ 3 / (3 * (a + b) ^ 3) ≤
      Real.log b - Real.log a := by
  rcases eq_or_lt_of_le hab with rfl | hab_lt
  · norm_num
  have hb : 0 < b := ha.trans hab_lt
  let g : ℝ → ℝ := fun t =>
    Real.log t - Real.log a - 2 * ((t - a) * (t + a)⁻¹) -
      (2 / 3) * ((t - a) ^ 3 * ((t + a) ^ 3)⁻¹)
  let g' : ℝ → ℝ := fun t =>
    t⁻¹ - 0 -
      2 * ((1 - 0) * (t + a)⁻¹ + (t - a) * (-(1 + 0) / (t + a) ^ 2)) -
      (2 / 3) * (((3 : ℕ) * (t - a) ^ (3 - 1) * (1 - 0)) * ((t + a) ^ 3)⁻¹ +
        (t - a) ^ 3 * (-((3 : ℕ) * (t + a) ^ (3 - 1) * (1 + 0)) / ((t + a) ^ 3) ^ 2))
  have hd : ∀ t ∈ Icc a b, HasDerivAt g (g' t) t := by
    intro t ht
    have ht_pos : 0 < t := ha.trans_le ht.1
    have hta_pos : 0 < t + a := add_pos ht_pos ha
    have hta3_pos : 0 < (t + a) ^ 3 := by positivity
    have hsub : HasDerivAt (fun y => y - a) (1 - 0) t :=
      (hasDerivAt_id t).sub (hasDerivAt_const t a)
    have hadd : HasDerivAt (fun y => y + a) (1 + 0) t :=
      (hasDerivAt_id t).add (hasDerivAt_const t a)
    have hterm1 := (hsub.mul (hadd.inv hta_pos.ne')).const_mul 2
    have hterm2 := ((hsub.pow 3).mul ((hadd.pow 3).inv hta3_pos.ne')).const_mul (2 / 3)
    exact (((Real.hasDerivAt_log ht_pos.ne').sub (hasDerivAt_const t (Real.log a))).sub
      hterm1).sub hterm2
  obtain ⟨c, hc, hc_slope⟩ := exists_hasDerivAt_eq_slope g g' hab_lt
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => hd t ⟨ht.1.le, ht.2.le⟩)
  have hc_pos : 0 < c := ha.trans hc.1
  have hca_pos : 0 < c + a := add_pos hc_pos ha
  have hba_pos : 0 < b - a := sub_pos.mpr hab_lt
  have hg'_nonneg : 0 ≤ g' c := by
    have hg'_eq : g' c = (c - a) ^ 4 / (c * (c + a) ^ 4) := by
      dsimp [g']
      have hc0 : c ≠ 0 := hc_pos.ne'
      have hca0 : c + a ≠ 0 := hca_pos.ne'
      field_simp [hc0, hca0]
      ring
    rw [hg'_eq]
    positivity
  have hdiff_eq : g b - g a = g' c * (b - a) := ((eq_div_iff hba_pos.ne').mp hc_slope).symm
  have hdiff_nonneg : 0 ≤ g b - g a := by
    rw [hdiff_eq]
    exact mul_nonneg hg'_nonneg hba_pos.le
  have halg : g b - g a =
      (Real.log b - Real.log a) -
        (2 * (b - a) / (a + b) + 2 * (b - a) ^ 3 / (3 * (a + b) ^ 3)) := by
    dsimp [g]
    have hab0 : b + a ≠ 0 := (add_pos hb ha).ne'
    have hab0' : a + b ≠ 0 := (add_pos ha hb).ne'
    field_simp [hab0, hab0']
    ring
  linarith

/-- **Cubic Difference Inequality `(2 / 3)(b³ - a³) ≤ (b - a)(b² + a²)`**: -/
theorem two_thirds_sub_cube_le_sub_mul_add_sq {a b : ℝ} (hab : a ≤ b) :
    (2 / 3) * (b ^ 3 - a ^ 3) ≤ (b - a) * (b ^ 2 + a ^ 2) := by
  have hba : 0 ≤ b - a := sub_nonneg.mpr hab
  have hpoly :
      (b - a) * (b ^ 2 + a ^ 2) - (2 / 3) * (b ^ 3 - a ^ 3) =
        (1 / 3) * (b - a) ^ 3 := by ring
  have hpos : 0 ≤ (1 / 3) * (b - a) ^ 3 := by positivity
  linarith

/-- **Specialization of `(2 / 3)(b³ - a³) ≤ (b - a)(b² + a²)` to `b = 1 / √(n - 1)`, `a = 1 / √n`**: -/
theorem two_thirds_inv_mul_sqrt_sub_le {n : ℕ} (hn : 2 ≤ n) :
    (2 / 3) * ((1 / ((n : ℝ) - 1)) * (1 / Real.sqrt ((n : ℝ) - 1)) -
      (1 / (n : ℝ)) * (1 / Real.sqrt (n : ℝ))) ≤
    (1 / Real.sqrt ((n : ℝ) - 1) - 1 / Real.sqrt (n : ℝ)) *
      (1 / ((n : ℝ) - 1) + 1 / (n : ℝ)) := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn1_pos : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hn_pos : (0 : ℝ) < (n : ℝ) := by linarith
  have hsqrt_le : Real.sqrt ((n : ℝ) - 1) ≤ Real.sqrt (n : ℝ) :=
    Real.sqrt_le_sqrt (by linarith)
  have hab : 1 / Real.sqrt (n : ℝ) ≤ 1 / Real.sqrt ((n : ℝ) - 1) :=
    one_div_le_one_div_of_le (Real.sqrt_pos.mpr hn1_pos) hsqrt_le
  have hcube := two_thirds_sub_cube_le_sub_mul_add_sq hab
  have hsq1 : (1 / Real.sqrt ((n : ℝ) - 1)) ^ 2 = 1 / ((n : ℝ) - 1) := by
    rw [div_pow, one_pow, Real.sq_sqrt hn1_pos.le]
  have hsq2 : (1 / Real.sqrt (n : ℝ)) ^ 2 = 1 / (n : ℝ) := by
    rw [div_pow, one_pow, Real.sq_sqrt hn_pos.le]
  have hcube1 :
      (1 / Real.sqrt ((n : ℝ) - 1)) ^ 3 =
        (1 / ((n : ℝ) - 1)) * (1 / Real.sqrt ((n : ℝ) - 1)) := by
    calc (1 / Real.sqrt ((n : ℝ) - 1)) ^ 3
      _ = (1 / Real.sqrt ((n : ℝ) - 1)) ^ 2 * (1 / Real.sqrt ((n : ℝ) - 1)) := by ring
      _ = (1 / ((n : ℝ) - 1)) * (1 / Real.sqrt ((n : ℝ) - 1)) := by rw [hsq1]
  have hcube2 :
      (1 / Real.sqrt (n : ℝ)) ^ 3 =
        (1 / (n : ℝ)) * (1 / Real.sqrt (n : ℝ)) := by
    calc (1 / Real.sqrt (n : ℝ)) ^ 3
      _ = (1 / Real.sqrt (n : ℝ)) ^ 2 * (1 / Real.sqrt (n : ℝ)) := by ring
      _ = (1 / (n : ℝ)) * (1 / Real.sqrt (n : ℝ)) := by rw [hsq2]
  rw [hsq1, hsq2, hcube1, hcube2] at hcube
  exact hcube

/-- **The `(n - 5)(n + 4) ≥ 0` Midpoint-to-Trapezoidal Ratio Bound for `5 ≤ n`**:
for all `5 ≤ n`, `(40 / 81) * (1 / (n - 1) + 1 / n) ≤ 2 / (2n - 1)`. -/
theorem forty_eighty_firsts_mul_inv_pred_add_inv_le_two_div_two_mul_sub_one
    {n : ℕ} (hn : 5 ≤ n) :
    (40 / 81) * (1 / ((n : ℝ) - 1) + 1 / (n : ℝ)) ≤ 2 / (2 * (n : ℝ) - 1) := by
  have hn5 : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn1_pos : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hn_pos : (0 : ℝ) < (n : ℝ) := by linarith
  have h2n1_pos : (0 : ℝ) < 2 * (n : ℝ) - 1 := by linarith
  have hn5_nonneg : (0 : ℝ) ≤ (n : ℝ) - 5 := by linarith
  have hn4_nonneg : (0 : ℝ) ≤ (n : ℝ) + 4 := by linarith
  have hsum :
      1 / ((n : ℝ) - 1) + 1 / (n : ℝ) =
        (2 * (n : ℝ) - 1) / (((n : ℝ) - 1) * (n : ℝ)) := by
    rw [div_add_div 1 1 hn1_pos.ne' hn_pos.ne']
    ring
  have hlhs :
      (40 / 81) * (1 / ((n : ℝ) - 1) + 1 / (n : ℝ)) =
        (40 * (2 * (n : ℝ) - 1)) / (81 * (((n : ℝ) - 1) * (n : ℝ))) := by
    rw [hsum, div_mul_div_comm]
  rw [hlhs, div_le_div_iff₀ (by positivity) h2n1_pos]
  have hpoly :
      2 * (81 * (((n : ℝ) - 1) * (n : ℝ))) -
        40 * (2 * (n : ℝ) - 1) * (2 * (n : ℝ) - 1) =
      2 * ((n : ℝ) - 5) * ((n : ℝ) + 4) := by ring
  have hpos : 0 ≤ 2 * ((n : ℝ) - 5) * ((n : ℝ) + 4) := by positivity
  linarith

/-- **Telescoping Upper Bound for `hermiteQuinticCellWeight n` on `5 ≤ n`**:
for all `5 ≤ n`,
`hermiteQuinticCellWeight n ≤ (811 / 14580) * ((1 / (n - 1)) * (1 / √(n - 1)) - (1 / n) * (1 / √n))`. -/
theorem hermiteQuinticCellWeight_le_of_five_le {n : ℕ} (hn : 5 ≤ n) :
    hermiteQuinticCellWeight n ≤
      (811 / 14580) * ((1 / ((n : ℝ) - 1)) * (1 / Real.sqrt ((n : ℝ) - 1)) -
        (1 / (n : ℝ)) * (1 / Real.sqrt (n : ℝ))) := by
  have hn2 : 2 ≤ n := by omega
  have hn_real : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn1_pos : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hn1_le : (n : ℝ) - 1 ≤ (n : ℝ) := by linarith
  have hmid := two_mul_sub_div_add_le_log_sub_log hn1_pos hn1_le
  have hmid_simp :
      2 * ((n : ℝ) - ((n : ℝ) - 1)) / ((n : ℝ) - 1 + (n : ℝ)) =
        2 / (2 * (n : ℝ) - 1) := by
    congr 1 <;> ring
  rw [hmid_simp] at hmid
  have hratio := (forty_eighty_firsts_mul_inv_pred_add_inv_le_two_div_two_mul_sub_one hn).trans hmid
  have hsqrt_le : Real.sqrt ((n : ℝ) - 1) ≤ Real.sqrt (n : ℝ) :=
    Real.sqrt_le_sqrt hn1_le
  have hdiff_nonneg : 0 ≤ 1 / Real.sqrt ((n : ℝ) - 1) - 1 / Real.sqrt (n : ℝ) :=
    sub_nonneg.mpr (one_div_le_one_div_of_le (Real.sqrt_pos.mpr hn1_pos) hsqrt_le)
  have hweight_lower :
      (101 / 2430) * (1 / ((n : ℝ) - 1) + 1 / (n : ℝ)) ≤
        (1 / 30) * (1 / ((n : ℝ) - 1) + 1 / (n : ℝ)) +
          (Real.log (n : ℝ) - Real.log ((n : ℝ) - 1)) / 60 := by linarith
  have hmul := mul_le_mul_of_nonneg_left hweight_lower hdiff_nonneg
  have hcube := two_thirds_inv_mul_sqrt_sub_le hn2
  have hcube_scaled := mul_le_mul_of_nonneg_left hcube (by norm_num : (0 : ℝ) ≤ 101 / 2430)
  rw [hermiteQuinticCellWeight_eq]
  linarith

/-- **Tail Sum Bound on `Icc 5 N` for `hermiteQuinticCellWeight`**:
`∑ n ∈ Finset.Icc 5 N, hermiteQuinticCellWeight n ≤ 811 / 116640`. -/
theorem sum_Icc_five_hermiteQuinticCellWeight_le (N : ℕ) :
    (∑ n ∈ Finset.Icc 5 N, hermiteQuinticCellWeight n) ≤ 811 / 116640 := by
  let g : ℕ → ℝ := fun n => (1 / ((n : ℝ) - 1)) * (1 / Real.sqrt ((n : ℝ) - 1))
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
      (∑ n ∈ Finset.Icc 5 N, hermiteQuinticCellWeight n) ≤
        (811 / 14580) * ∑ n ∈ Finset.Icc 5 N, (g n - g (n + 1)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun n hn => ?_
    rw [Finset.mem_Icc] at hn
    have hstep := hermiteQuinticCellWeight_le_of_five_le hn.1
    have hg_succ : g (n + 1) = (1 / (n : ℝ)) * (1 / Real.sqrt (n : ℝ)) := by
      dsimp [g]
      push_cast
      rw [add_sub_cancel_right]
    rw [hg_succ]
    exact hstep
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
      positivity
    rw [htel, hg5] at hle
    linarith
  · rw [Finset.Icc_eq_empty hN, Finset.sum_empty]
    norm_num

/-- **Exact Rationalization Bound `329 / (12150 √2) + 43 / (4200 √3) ≤ 20489 / 816480`**: -/
theorem three_twenty_nine_div_twelve_one_fifty_sqrt_two_add_forty_three_div_forty_two_hundred_sqrt_three_le :
    329 / (12150 * Real.sqrt 2) + 43 / (4200 * Real.sqrt 3) ≤ 20489 / 816480 := by
  let A : ℝ := 329 / (12150 * Real.sqrt 2)
  let B : ℝ := 43 / (4200 * Real.sqrt 3)
  let C : ℝ := 20489 / 816480
  have hA_nonneg : 0 ≤ A := by dsimp [A]; positivity
  have hB_nonneg : 0 ≤ B := by dsimp [B]; positivity
  have hC_nonneg : 0 ≤ C := by dsimp [C]; positivity
  have hA2 : A ^ 2 = 329 ^ 2 / (12150 ^ 2 * 2) := by
    dsimp [A]
    rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hB2 : B ^ 2 = 43 ^ 2 / (4200 ^ 2 * 3) := by
    dsimp [B]
    rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  have hdiff_nonneg : 0 ≤ C ^ 2 - A ^ 2 - B ^ 2 := by
    rw [hA2, hB2]
    dsimp [C]
    norm_num
  have h2AB_sq : (2 * A * B) ^ 2 ≤ (C ^ 2 - A ^ 2 - B ^ 2) ^ 2 := by
    calc (2 * A * B) ^ 2
      _ = 4 * A ^ 2 * B ^ 2 := by ring
      _ ≤ (C ^ 2 - A ^ 2 - B ^ 2) ^ 2 := by
          rw [hA2, hB2]
          dsimp [C]
          norm_num
  have h2AB : 2 * A * B ≤ C ^ 2 - A ^ 2 - B ^ 2 :=
    (abs_le_of_sq_le_sq' h2AB_sq hdiff_nonneg).2
  have hAB_sq : (A + B) ^ 2 ≤ C ^ 2 := by
    calc (A + B) ^ 2
      _ = A ^ 2 + B ^ 2 + 2 * A * B := by ring
      _ ≤ C ^ 2 := by linarith
  exact (abs_le_of_sq_le_sq' hAB_sq hC_nonneg).2

/-- **The Global `1 / 18` Series Bound for `hermiteQuinticCellWeight`**:
for every `N : ℕ`,
`∑ n ∈ Finset.Icc 2 N, hermiteQuinticCellWeight n ≤ 1 / 18`. -/
theorem sum_Icc_two_hermiteQuinticCellWeight_le_one_eighteenth (N : ℕ) :
    (∑ n ∈ Finset.Icc 2 N, hermiteQuinticCellWeight n) ≤ 1 / 18 := by
  have h2_bound :
      hermiteQuinticCellWeight 2 ≤
        (1 / 12) * (1 - (1 / 2) * (1 / Real.sqrt 2)) -
          (1 - 1 / Real.sqrt 2) * (299 / 4860) := by
    rw [hermiteQuinticCellWeight_eq]
    have hlog2 := two_mul_sub_div_add_add_two_mul_cube_div_three_cube_le_log_sub_log
      (by norm_num : (0 : ℝ) < 1) (by norm_num : (1 : ℝ) ≤ 2)
    have hsqrt2_ge : (1 : ℝ) ≤ Real.sqrt 2 := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt (by norm_num)
    have hdiff2 : 0 ≤ 1 - 1 / Real.sqrt 2 := by
      have := one_div_le_one_div_of_le one_pos hsqrt2_ge
      linarith
    have h1 : ((2 : ℕ) : ℝ) - 1 = 1 := by norm_num
    have h2 : ((2 : ℕ) : ℝ) = 2 := by norm_num
    rw [h1, h2, Real.sqrt_one]
    have hmul := mul_le_mul_of_nonneg_left hlog2 hdiff2
    linarith
  have h3_bound :
      hermiteQuinticCellWeight 3 ≤
        (1 / 12) * ((1 / 2) * (1 / Real.sqrt 2) - (1 / 3) * (1 / Real.sqrt 3)) -
          (1 / Real.sqrt 2 - 1 / Real.sqrt 3) * (31 / 900) := by
    rw [hermiteQuinticCellWeight_eq]
    have hlog3 := two_mul_sub_div_add_le_log_sub_log
      (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≤ 3)
    have hsqrt3_ge : Real.sqrt 2 ≤ Real.sqrt 3 := Real.sqrt_le_sqrt (by norm_num)
    have hdiff3 : 0 ≤ 1 / Real.sqrt 2 - 1 / Real.sqrt 3 :=
      sub_nonneg.mpr (one_div_le_one_div_of_le (Real.sqrt_pos.mpr (by norm_num)) hsqrt3_ge)
    have h1 : ((3 : ℕ) : ℝ) - 1 = 2 := by norm_num
    have h2 : ((3 : ℕ) : ℝ) = 3 := by norm_num
    rw [h1, h2]
    have hmul := mul_le_mul_of_nonneg_left hlog3 hdiff3
    linarith
  have h4_bound :
      hermiteQuinticCellWeight 4 ≤
        (1 / 12) * ((1 / 3) * (1 / Real.sqrt 3) - 1 / 8) -
          (1 / Real.sqrt 3 - 1 / 2) * (61 / 2520) := by
    rw [hermiteQuinticCellWeight_eq]
    have hlog4 := two_mul_sub_div_add_le_log_sub_log
      (by norm_num : (0 : ℝ) < 3) (by norm_num : (3 : ℝ) ≤ 4)
    have h4_eq : (4 : ℝ) = 2 ^ 2 := by norm_num
    have hsqrt4 : Real.sqrt 4 = 2 := by
      rw [h4_eq, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
    have hsqrt4_ge : Real.sqrt 3 ≤ Real.sqrt 4 := Real.sqrt_le_sqrt (by norm_num)
    have hdiff4 : 0 ≤ 1 / Real.sqrt 3 - 1 / 2 := by
      have := one_div_le_one_div_of_le (Real.sqrt_pos.mpr (by norm_num)) hsqrt4_ge
      rw [hsqrt4] at this
      linarith
    have h1 : ((4 : ℕ) : ℝ) - 1 = 3 := by norm_num
    have h2 : ((4 : ℕ) : ℝ) = 4 := by norm_num
    rw [h1, h2, hsqrt4]
    have hmul := mul_le_mul_of_nonneg_left hlog4 hdiff4
    linarith
  have hsqrt23 :=
    three_twenty_nine_div_twelve_one_fifty_sqrt_two_add_forty_three_div_forty_two_hundred_sqrt_three_le
  have hsqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsqrt3_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hsqrt3_le_2 : Real.sqrt 3 ≤ 2 := by
    have h4 : (2 : ℝ) = Real.sqrt (2 ^ 2) := (Real.sqrt_sq (by norm_num)).symm
    rw [h4]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hinv_sqrt3_ge_half : (1 / 2 : ℝ) ≤ 1 / Real.sqrt 3 :=
    one_div_le_one_div_of_le hsqrt3_pos hsqrt3_le_2
  have hsqrt2_le_sqrt3 : Real.sqrt 2 ≤ Real.sqrt 3 := Real.sqrt_le_sqrt (by norm_num)
  have hinv_sqrt2_ge_inv_sqrt3 : 1 / Real.sqrt 3 ≤ 1 / Real.sqrt 2 :=
    one_div_le_one_div_of_le hsqrt2_pos hsqrt2_le_sqrt3
  have h234_alg :
      ((1 / 12) * (1 - (1 / 2) * (1 / Real.sqrt 2)) -
        (1 - 1 / Real.sqrt 2) * (299 / 4860)) +
      ((1 / 12) * ((1 / 2) * (1 / Real.sqrt 2) - (1 / 3) * (1 / Real.sqrt 3)) -
        (1 / Real.sqrt 2 - 1 / Real.sqrt 3) * (31 / 900)) +
      ((1 / 12) * ((1 / 3) * (1 / Real.sqrt 3) - 1 / 8) -
        (1 / Real.sqrt 3 - 1 / 2) * (61 / 2520)) +
      811 / 116640 =
      12431 / 408240 +
        (329 / 12150) * (1 / Real.sqrt 2) + (43 / 4200) * (1 / Real.sqrt 3) := by
    ring
  have hrad_eq :
      (329 / 12150) * (1 / Real.sqrt 2) + (43 / 4200) * (1 / Real.sqrt 3) =
        329 / (12150 * Real.sqrt 2) + 43 / (4200 * Real.sqrt 3) := by
    rw [div_mul_div_comm, div_mul_div_comm, mul_one, mul_one]
  have htail5 := sum_Icc_five_hermiteQuinticCellWeight_le N
  by_cases hN4 : 4 ≤ N
  · rw [sum_Icc_eq_add_sum_Icc_succ hermiteQuinticCellWeight (by omega : 2 ≤ N),
      sum_Icc_eq_add_sum_Icc_succ hermiteQuinticCellWeight (by omega : 3 ≤ N),
      sum_Icc_eq_add_sum_Icc_succ hermiteQuinticCellWeight hN4]
    linarith
  · by_cases hN3 : 3 ≤ N
    · have hN_eq : N = 3 := by omega
      subst hN_eq
      rw [sum_Icc_eq_add_sum_Icc_succ hermiteQuinticCellWeight (by omega : 2 ≤ 3),
        Finset.Icc_self, Finset.sum_singleton]
      have h4_rhs_nonneg :
          0 ≤ (1 / 12) * ((1 / 3) * (1 / Real.sqrt 3) - 1 / 8) -
            (1 / Real.sqrt 3 - 1 / 2) * (61 / 2520) := by linarith
      linarith
    · by_cases hN2 : 2 ≤ N
      · have hN_eq : N = 2 := by omega
        subst hN_eq
        rw [Finset.Icc_self, Finset.sum_singleton]
        have h34_rhs_nonneg :
            0 ≤ ((1 / 12) * ((1 / 2) * (1 / Real.sqrt 2) - (1 / 3) * (1 / Real.sqrt 3)) -
              (1 / Real.sqrt 2 - 1 / Real.sqrt 3) * (31 / 900)) +
              ((1 / 12) * ((1 / 3) * (1 / Real.sqrt 3) - 1 / 8) -
                (1 / Real.sqrt 3 - 1 / 2) * (61 / 2520)) := by linarith
        linarith
      · rw [Finset.Icc_eq_empty hN2, Finset.sum_empty]
        norm_num

/-- **Pointwise Spectral-Logarithmic Secant Comparison for `weilSymmetricLogNumerator`**:
for `2 ≤ n` and `x ∈ [n - 1, n]`,
`|weilSymmetricLogNumerator f.1 x - cellSecant (weilSymmetricLogNumerator f.1) n x| ≤ (spectralSecondMoment f.1 + ∫ ‖f.1‖²) * (Real.log x - cellSecant Real.log n x)`. -/
theorem abs_weilSymmetricLogNumerator_sub_cellSecant_le_spectralSecondMoment_add_l2_mul_log_sub_cellSecant
    (f : WeilTestFn)
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2))
    {n : ℕ} (hn : 2 ≤ n) {x : ℝ} (hx : x ∈ Icc ((n : ℝ) - 1) (n : ℝ)) :
    |weilSymmetricLogNumerator f.1 x - cellSecant (weilSymmetricLogNumerator f.1) n x| ≤
      (spectralSecondMoment f.1 + ∫ u : ℝ, ‖f.1 u‖ ^ 2) *
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
  have hrhs_eq :
      (spectralSecondMoment f.1 + ∫ u : ℝ, ‖f.1 u‖ ^ 2) *
        (Real.log x - cellSecant Real.log n x) =
      (1 / (2 * π)) * ∫ r : ℝ,
        (‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2) + (1 / 2) * (‖paperFT f.1 r‖ ^ 2 * 2)) *
          (Real.log x - cellSecant Real.log n x) := by
    have hplanch' : (∫ u : ℝ, ‖f.1 u‖ ^ 2) =
        (1 / (2 * π)) * ((1 / 2) * ∫ r : ℝ, ‖paperFT f.1 r‖ ^ 2 * 2) := by
      linarith [hplanch]
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
  have hcmp := abs_sub_cellSecant_le_mul_log_sub_cellSecant_of_abs_deriv2_le_div_sq hn
    (fun t ht => hasDerivAt_cosLogProfile r (ht_pos t ht))
    (fun t ht => hasDerivAt_cosLogProfileDeriv r (ht_pos t ht))
    (fun t ht => abs_cosLogProfileDeriv2_le_sq_add_half_div_sq r (ht_pos t ht)) hx
  have hweight : 0 ≤ ‖paperFT f.1 r‖ ^ 2 * 2 := mul_nonneg (sq_nonneg _) (by norm_num)
  have hmul := mul_le_mul_of_nonneg_left hcmp hweight
  linarith

/-- **The `-(1 / 18) * (spectralSecondMoment f.1 + ∫ ‖f.1‖²) ≤ secantNumeratorCellDefect f.1 N`
Bound via Exact Cubic Hermite × Quintic Chebyshev Quadrature**: -/
theorem neg_one_eighteenth_spectralSecondMoment_add_l2_le_secantNumeratorCellDefect
    (f : WeilTestFn)
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2))
    (N : ℕ) :
    -(1 / 18) * (spectralSecondMoment f.1 + ∫ u : ℝ, ‖f.1 u‖ ^ 2) ≤
      secantNumeratorCellDefect f.1 N := by
  let M := spectralSecondMoment f.1 + ∫ u : ℝ, ‖f.1 u‖ ^ 2
  have hM_nonneg : 0 ≤ M := add_nonneg (spectralSecondMoment_nonneg f.1)
    (integral_nonneg fun _ => sq_nonneg _)
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
      abs_weilSymmetricLogNumerator_sub_cellSecant_le_spectralSecondMoment_add_l2_mul_log_sub_cellSecant
        f hint2 hn_mem.1 hx
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

/-! ## Section 3: The `(67 / 90) ∫ ‖f.1‖² - (1 / 18) spectralSecondMoment f.1` Coercivity Law (`67 / 5 = 13.4`), the `(59 / 72)` Prime-Blind Cone Law (`59 / 4 = 14.75`), and Unconditional `markovEnergy ≥ 0` -/

/-- **Pure Second-Moment `(67 / 90) ∫ ‖f.1‖² - (1 / 18) spectralSecondMoment f.1` Lower Bound
on `rightCellQuadratureDefect` (Critical Ratio `67 / 5 = 13.4`)**: -/
theorem sixty_seven_ninetieths_l2_sub_one_eighteenth_spectralSecondMoment_le_rightCellQuadratureDefect
    (f : WeilTestFn)
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2))
    {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest f.1 f.1 (Real.log N) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log N) = 0)
    (hN : ∀ n : ℕ, N < n →
      EF.weilTest f.1 f.1 (Real.log n) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log n) = 0) :
    (67 / 90) * (∫ u : ℝ, ‖f.1 u‖ ^ 2) - (1 / 18) * spectralSecondMoment f.1 ≤
      rightCellQuadratureDefect (weilContinuumLogProfile f.1) N := by
  have h1 := four_fifths_l2_add_secantNumerator_le_rightCellQuadratureDefect f hN1 hN0 hN
  have h2 := neg_one_eighteenth_spectralSecondMoment_add_l2_le_secantNumeratorCellDefect
    f hint2 N
  linarith

/-- **Prime-Blind Cone `(59 / 72) ∫ ‖f.1‖² - (1 / 18) spectralSecondMoment f.1` Lower Bound
on `rightCellQuadratureDefect` (Critical Ratio `59 / 4 = 14.75`)**:
on the Prime-Blind Cone (`logVector f = 0`), absorbing `(1 / 18) * ∫ ‖f.1‖²` into Module 52's
`(7 / 8) * ∫ ‖f.1‖² = (63 / 72) * ∫ ‖f.1‖²` origin surplus leaves `59 / 72`! -/
theorem fifty_nine_seventy_seconds_l2_sub_one_eighteenth_spectralSecondMoment_le_rightCellQuadratureDefect_of_logVector_eq_zero
    (f : WeilTestFn) (hblind : logVector f = 0)
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2))
    {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest f.1 f.1 (Real.log N) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log N) = 0)
    (hN : ∀ n : ℕ, N < n →
      EF.weilTest f.1 f.1 (Real.log n) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log n) = 0) :
    (59 / 72) * (∫ u : ℝ, ‖f.1 u‖ ^ 2) - (1 / 18) * spectralSecondMoment f.1 ≤
      rightCellQuadratureDefect (weilContinuumLogProfile f.1) N := by
  have h1 := seven_eighths_l2_add_secantNumerator_le_rightCellQuadratureDefect_of_logVector_eq_zero
    f hblind hN1 hN0 hN
  have h2 := neg_one_eighteenth_spectralSecondMoment_add_l2_le_secantNumeratorCellDefect
    f hint2 N
  linarith

/-- **Unconditional `0 ≤ markovEnergy F` on the Primitive Hyperplane whenever
`spectralSecondMoment F ≤ (67 / 5 - δ) ∫ ‖F‖² = (13.4 - δ) ∫ ‖F‖²`**: -/
theorem markovEnergy_ofReal_nonneg_of_spectralSecondMoment_le_sixty_seven_fifths_of_cosh_zero
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
      (67 / 5 - δ) * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) :
    0 ≤ markovEnergy (realWeilTestFn f hf hfc).1 := by
  let θ := max (max 1 (Real.log (N : ℝ))) (36 / δ)
  have hθ1 : 1 ≤ θ := (le_max_left 1 (Real.log (N : ℝ))).trans (le_max_left _ _)
  have hθ0 : 0 ≤ θ := by linarith
  have hθlog : Real.log (N : ℝ) ≤ θ :=
    (le_max_right 1 (Real.log (N : ℝ))).trans (le_max_left _ _)
  have hθδ_le : 36 / δ ≤ θ := le_max_right _ _
  have hθδ : 36 ≤ θ * δ := (div_le_iff₀ hδ).mp hθδ_le
  have hbase := four_fifths_secantNumerator_upgraded_l2_le_markovEnergy_of_cosh_zero
    m hθ0 hf hfc hcosh hN1 hθlog hN0 hN hdiff
  have hnum := neg_one_eighteenth_spectralSecondMoment_add_l2_le_secantNumeratorCellDefect
    (realWeilTestFn f hf hfc) hint2 N
  have hθnum := mul_le_mul_of_nonneg_left hnum hθ0
  have hθbound := mul_le_mul_of_nonneg_left hsec_bound (by positivity : 0 ≤ (1 / 18) * θ)
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
