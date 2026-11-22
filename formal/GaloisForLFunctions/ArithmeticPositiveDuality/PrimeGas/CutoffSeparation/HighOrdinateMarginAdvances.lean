import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CutoffSeparation.ZetaFreeTruncationMargin
import GaloisForLFunctions.RHTower.XiWindowZeroCount
import GaloisForLFunctions.ExceptionalLayerTheory.NonrealZeroRepulsionAndCoMovingRemainders

/-!
# Unconditional `ζ`-free cutoff lower bounds past height `67`: height `70`, unit-band caps, and repulsion

Upper bounds on truncation error do not by themselves bound `‖renormalizedCutoff‖` from below.
Targeting the remaining strip `{1/2 < Re w ≤ 20999/24000 ∧ |Im w| > 67}`, this module proves three
unconditional **actual-cutoff reading lower-bound** advances (zero computations, standard axioms only)
and isolates the exact open RH frontier above height `70`:

1. **Analytic verified-height advance through `|Im w| ≤ 70`
   (`rhVerifiedThrough_seventy`, `exists_zetaFree_margin_of_abs_im_le_seventy`)**:
   evaluating the Fejér edge budget (`budget_at_edge`) at bandwidth `L = 17/5` (`N = 30`, prime
   powers `< 30`) with exact Chebyshev phase minimization on `{2, 4, 8, 16}`, `{3, 9, 27}`, and
   `{5, 25}` excludes all off-line zeros across `67 < |Im w| ≤ 70`, certifying an actual finite
   cutoff `X₀ ≥ 1` with `zetaFreeTruncationBound t j X₀ w < ‖renormalizedCutoff t j X₀ w‖` at
   **every** point of `1/2 < Re w ≤ 20999/24000` with `|Im w| ≤ 70` and reducing `RiemannHypothesis`
   to `70 < |Im w|` (`rh_iff_zetaFree_margin_above_seventy`).
2. **Factor-of-2 reflected Lorentzian cap and pigeonhole cutoff lower bounds at every height `τ`
   (`ncard_missingZetaFreeMarginWindow_le`, `exists_point_with_zetaFree_margin_of_card_gt`)**:
   at **every** height `τ ∈ ℝ` (including all `|τ| > 70`, with no exceptional heights) and every
   half-width `h ≥ 0`, pairing each missing-margin point `w` in `1/2 < Re w ≤ 20999/24000` with its
   same-ordinate partner `conj (1 - w)` in `Re < 1/2` proves at most
   `4 (1 + h^2) (xiLineTwoLogDerivConstant + log(|τ| + 4))` points in `[τ - h, τ + h]` can lack a
   strict `ζ`-free cutoff margin. Consequently, every finite probe set exceeding that logarithmic
   threshold — and infinitely many points in every nonempty horizontal subinterval `(a, b)` at every
   height `τ` — unconditionally admits an actual cutoff exceeding its `ζ`-free threshold.
3. **Five-point zero-repulsion cutoff lower bound (`five_point_repulsion_forces_zetaFree_margin`)**:
   for any `1 < σ_* ≤ 2` and any two candidate points `w₁, w₂` in `1/2 < Re w ≤ 20999/24000` with
   `4 ≤ Im w₁` and `Im w₁ + 4 ≤ Im w₂` whose abscissae exceed the 5-point repulsion budget, at least
   one of `w₁` or `w₂` unconditionally possesses an actual cutoff `X₀ ≥ 1` beating
   `zetaFreeTruncationBound`.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CutoffSeparation

open AntipodalSpectrum Complex Filter Set
open ArithmeticFunction (vonMangoldt)
open scoped Topology ComplexConjugate

/-! ### Part 1: Analytic Fejér budget at `L = 17 / 5` (`N = 30`) and verified height `70` -/

section HeightSeventy

open GaloisForLFunctions.VerifiedHeightRungs.HadamardBudget
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.BezoutValuationIncidence

/-- Four-harmonic Chebyshev floor for `p = 2` on `[-1, 1]` at bandwidth `L = 17 / 5`. -/
private theorem family_two_seventy {A B C D u : ℝ} (hu0 : -1 ≤ u)
    (hD : 0 ≤ D) (hCD : 16 * D ≤ 4 * C) (hBC : 4 * C ≤ 2 * B)
    (hABC : 0 ≤ A - 4 * B + 5 * C) :
    -A + B - C + D ≤ A * u + B * (2 * u ^ 2 - 1) + C * (4 * u ^ 3 - 3 * u) +
      D * (8 * u ^ 4 - 8 * u ^ 2 + 1) := by
  have hlin : 0 ≤ (A - 2 * B + C) + (2 * B - 4 * C) * u := by
    have hsub : -(2 * B - 4 * C) ≤ (2 * B - 4 * C) * u := by nlinarith only [hu0, hBC]
    linarith only [hABC, hsub]
  have hquad : 0 ≤ u ^ 2 * ((4 * C - 8 * D) + 8 * D * u) := by
    have hinner : 0 ≤ (4 * C - 8 * D) + 8 * D * u := by nlinarith only [hu0, hD, hCD]
    exact mul_nonneg (sq_nonneg u) hinner
  have hQ : 0 ≤ A + 2 * B * (u - 1) + C * (2 * u - 1) ^ 2 + 8 * D * u ^ 2 * (u - 1) := by
    have heq : A + 2 * B * (u - 1) + C * (2 * u - 1) ^ 2 + 8 * D * u ^ 2 * (u - 1) =
        ((A - 2 * B + C) + (2 * B - 4 * C) * u) + u ^ 2 * ((4 * C - 8 * D) + 8 * D * u) := by ring
    rw [heq]; linarith only [hlin, hquad]
  have hprod := mul_nonneg (by linarith only [hu0] : 0 ≤ u + 1) hQ
  have hfac : (u + 1) * (A + 2 * B * (u - 1) + C * (2 * u - 1) ^ 2 + 8 * D * u ^ 2 * (u - 1)) =
      (A * u + B * (2 * u ^ 2 - 1) + C * (4 * u ^ 3 - 3 * u) +
        D * (8 * u ^ 4 - 8 * u ^ 2 + 1)) - (-A + B - C + D) := by ring
  linarith only [hprod, hfac]

/-- Three-harmonic Chebyshev floor for `p = 3` (`3, 9, 27`) on `[-1, 1]`. -/
private theorem family_three_cubic {A B C v : ℝ} (hv0 : -1 ≤ v)
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hAB : 4 * B ≤ A) :
    -A + B - C ≤ A * v + B * (2 * v ^ 2 - 1) + C * (4 * v ^ 3 - 3 * v) := by
  have hQ : 0 ≤ A + 2 * B * (v - 1) + C * (2 * v - 1) ^ 2 := by
    have hsq : 0 ≤ C * (2 * v - 1) ^ 2 := mul_nonneg hC (sq_nonneg _)
    nlinarith only [hv0, hB, hAB, hsq]
  have hprod := mul_nonneg (by linarith only [hv0] : 0 ≤ v + 1) hQ
  nlinarith only [hprod]

private theorem prime_term_le_seventy {x x0 p : ℝ} (h0 : x0 ≤ x) (hx0 : 17 / 10 ≤ x0) (hp : 0 < p) :
    x / p * (1 - x / (17 / 5)) ≤ x0 / p * (1 - x0 / (17 / 5)) := by
  have h := mul_nonneg (sub_nonneg.mpr h0) (by linarith only [h0, hx0] : 0 ≤ (x + x0) / (17 / 5) - 1)
  have e : x0 / p * (1 - x0 / (17 / 5)) - x / p * (1 - x / (17 / 5)) =
      (x - x0) * ((x + x0) / (17 / 5) - 1) / p := by field_simp; ring
  have h2 : 0 ≤ x0 / p * (1 - x0 / (17 / 5)) - x / p * (1 - x / (17 / 5)) := by
    rw [e]; exact div_nonneg h hp.le
  linarith only [h2]

private theorem le_log_of_two_pow_le' {p : ℝ} {k m : ℕ} (hk : 0 < k)
    (h : (2 : ℝ) ^ m ≤ p ^ k) : (m : ℝ) / k * Real.log 2 ≤ Real.log p := by
  have hl := Real.log_le_log (by positivity) h
  rw [Real.log_pow, Real.log_pow] at hl
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  rw [div_mul_eq_mul_div, div_le_iff₀ hk']
  linarith only [hl]

private theorem log_le_of_pow_le_two_pow' {p : ℝ} (hp : 0 < p) {k m : ℕ} (hk : 0 < k)
    (h : p ^ k ≤ (2 : ℝ) ^ m) : Real.log p ≤ (m : ℝ) / k * Real.log 2 := by
  have hl := Real.log_le_log (by positivity) h
  rw [Real.log_pow, Real.log_pow] at hl
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  rw [div_mul_eq_mul_div, le_div_iff₀ hk']
  linarith only [hl]

private theorem log3_lb70 : (1.09857 : ℝ) ≤ Real.log 3 := by
  have h := le_log_of_two_pow_le' (p := 3) (k := 53) (m := 84) (by norm_num) (by norm_num)
  have h2 := Real.log_two_gt_d9; norm_num at h ⊢; linarith only [h, h2]

private theorem log3_ub70 : Real.log 3 ≤ 1.09872 := by
  have h := log_le_of_pow_le_two_pow' (p := 3) (by norm_num) (k := 94) (m := 149) (by norm_num) (by norm_num)
  have h2 := Real.log_two_lt_d9; norm_num at h ⊢; linarith only [h, h2]

private theorem log5_lb70 : (1.60937 : ℝ) ≤ Real.log 5 := by
  have h := le_log_of_two_pow_le' (p := 5) (k := 87) (m := 202) (by norm_num) (by norm_num)
  have h2 := Real.log_two_gt_d9; norm_num at h ⊢; linarith only [h, h2]

private theorem log5_ub70 : Real.log 5 ≤ 1.60952 := by
  have h := log_le_of_pow_le_two_pow' (p := 5) (by norm_num) (k := 59) (m := 137) (by norm_num) (by norm_num)
  have h2 := Real.log_two_lt_d9; norm_num at h ⊢; linarith only [h, h2]

private theorem log7_lb70 : (1.94582 : ℝ) ≤ Real.log 7 := by
  have h := le_log_of_two_pow_le' (p := 7) (k := 83) (m := 233) (by norm_num) (by norm_num)
  have h2 := Real.log_two_gt_d9; norm_num at h ⊢; linarith only [h, h2]

private theorem log11_lb70 : (2.3976 : ℝ) ≤ Real.log 11 := by
  have h := le_log_of_two_pow_le' (p := 11) (k := 61) (m := 211) (by norm_num) (by norm_num)
  have h2 := Real.log_two_gt_d9; norm_num at h ⊢; linarith only [h, h2]

private theorem log13_lb70 : (2.56464 : ℝ) ≤ Real.log 13 := by
  have h := le_log_of_two_pow_le' (p := 13) (k := 90) (m := 333) (by norm_num)
    (by rw [show (333 : ℕ) = 166 + 167 by rfl, pow_add]; norm_num)
  have h2 := Real.log_two_gt_d9; norm_num at h ⊢; linarith only [h, h2]

private theorem log17_lb70 : (2.83286 : ℝ) ≤ Real.log 17 := by
  have h := le_log_of_two_pow_le' (p := 17) (k := 92) (m := 376) (by norm_num)
    (by rw [show (376 : ℕ) = 188 + 188 by rfl, pow_add]; norm_num)
  have h2 := Real.log_two_gt_d9; norm_num at h ⊢; linarith only [h, h2]

private theorem log19_lb70 : (2.94401 : ℝ) ≤ Real.log 19 := by
  have h := le_log_of_two_pow_le' (p := 19) (k := 93) (m := 395) (by norm_num)
    (by rw [show (395 : ℕ) = 197 + 198 by rfl, pow_add]; norm_num)
  have h2 := Real.log_two_gt_d9; norm_num at h ⊢; linarith only [h, h2]

private theorem log23_lb70 : (3.13528 : ℝ) ≤ Real.log 23 := by
  have h := le_log_of_two_pow_le' (p := 23) (k := 86) (m := 389) (by norm_num)
    (by rw [show (389 : ℕ) = 194 + 195 by rfl, pow_add]; norm_num)
  have h2 := Real.log_two_gt_d9; norm_num at h ⊢; linarith only [h, h2]

private theorem log29_lb70 : (3.36671 : ℝ) ≤ Real.log 29 := by
  have h := le_log_of_two_pow_le' (p := 29) (k := 91) (m := 442) (by norm_num)
    (by rw [show (442 : ℕ) = 221 + 221 by rfl, pow_add]; norm_num)
  have h2 := Real.log_two_gt_d9; norm_num at h ⊢; linarith only [h, h2]

private theorem log_pi_lb70 : (1.1444 : ℝ) ≤ Real.log Real.pi := by
  have hpow : (2 : ℝ) ^ 71 ≤ Real.pi ^ 43 := by
    calc (2 : ℝ) ^ 71 ≤ 3.1415 ^ 43 := by norm_num
      _ ≤ Real.pi ^ 43 := pow_le_pow_left₀ (by norm_num) Real.pi_gt_d4.le 43
  have h := le_log_of_two_pow_le' (p := Real.pi) (k := 43) (m := 71) (by norm_num) hpow
  have h2 := Real.log_two_gt_d9; norm_num at h ⊢; linarith only [h, h2]

private theorem exp_seventeen_le : Real.exp 17 ≤ 24154953 := by
  have h : Real.exp 17 = Real.exp 1 ^ 17 := by rw [← Real.exp_nat_mul]; norm_num
  rw [h]
  calc Real.exp 1 ^ 17 ≤ 2.7182818286 ^ 17 :=
        pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 17
    _ ≤ 24154953 := by norm_num

private theorem twenty_nine_le_exp_band : (29 : ℝ) ≤ Real.exp (17 / 5) := by
  have hpow : (29 : ℝ) ^ 5 ≤ Real.exp (17 / 5) ^ 5 := by
    rw [← Real.exp_nat_mul]; norm_num
    have h17 : Real.exp 17 = Real.exp 1 ^ 17 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h17]
    calc (20511149 : ℝ) ≤ 2.7182818283 ^ 17 := by norm_num
      _ ≤ Real.exp 1 ^ 17 := pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 17
  exact (pow_le_pow_iff_left₀ (by norm_num) (Real.exp_pos _).le (by norm_num : 5 ≠ 0)).mp hpow

private theorem exp_band_le_thirty : Real.exp (17 / 5) ≤ 30 := by
  have hpow : Real.exp (17 / 5) ^ 5 ≤ (30 : ℝ) ^ 5 := by
    rw [← Real.exp_nat_mul]
    have h17 : (5 : ℕ) * (17 / 5 : ℝ) = 17 := by norm_num
    rw [h17]
    exact exp_seventeen_le.trans (by norm_num)
  exact (pow_le_pow_iff_left₀ (Real.exp_pos _).le (by norm_num) (by norm_num : 5 ≠ 0)).mp hpow

private theorem exp_neg_seventeen_tenths_ge : (0.182683 : ℝ) ≤ Real.exp (-(17 / 10)) := by
  have hpow : (0.182683 : ℝ) ^ 10 ≤ Real.exp (-(17 / 10)) ^ 10 := by
    rw [← Real.exp_nat_mul]
    have h17 : (10 : ℕ) * -(17 / 10 : ℝ) = -17 := by norm_num
    rw [h17, Real.exp_neg, ← one_div, le_div_iff₀ (Real.exp_pos 17)]
    calc (0.182683 : ℝ) ^ 10 * Real.exp 17
        ≤ (0.182683 : ℝ) ^ 10 * 24154953 :=
          mul_le_mul_of_nonneg_left exp_seventeen_le (by norm_num)
      _ ≤ 1 := by norm_num
  exact (pow_le_pow_iff_left₀ (by norm_num) (Real.exp_pos _).le (by norm_num : 10 ≠ 0)).mp hpow

private theorem log_le_band {n : ℝ} (h0 : 0 < n) (h29 : n ≤ 29) : Real.log n ≤ 17 / 5 := by
  rw [Real.log_le_iff_le_exp h0]
  linarith only [h29, twenty_nine_le_exp_band]

private theorem band_le_log (n : ℕ) (hn : 30 ≤ n) : 17 / 5 ≤ Real.log n := by
  have hn' : (30 : ℝ) ≤ n := by exact_mod_cast hn
  rw [Real.le_log_iff_exp_le (by linarith only [hn'])]
  linarith only [hn', exp_band_le_thirty]

private theorem tri_band_eq {u : ℝ} (h0 : 0 ≤ u) (hhi : u ≤ 17 / 5) :
    triangleFn (17 / 5) u = 1 - u / (17 / 5) := by
  unfold triangleFn
  rw [abs_of_nonneg h0, max_eq_left]
  linarith only [hhi]

private theorem poly_eq_seventy (γ : ℝ) :
    ∑ n ∈ Finset.range 30, vonMangoldt n / n * triangleFn (17 / 5) (Real.log n) *
        Real.cos (γ * Real.log n) =
      (Real.log 2 / 2 * (1 - Real.log 2 / (17 / 5)) * Real.cos (γ * Real.log 2) +
        Real.log 2 / 4 * (1 - 2 * Real.log 2 / (17 / 5)) * Real.cos (2 * (γ * Real.log 2)) +
        Real.log 2 / 8 * (1 - 3 * Real.log 2 / (17 / 5)) * Real.cos (3 * (γ * Real.log 2)) +
        Real.log 2 / 16 * (1 - 4 * Real.log 2 / (17 / 5)) * Real.cos (2 * (2 * (γ * Real.log 2)))) +
      (Real.log 3 / 3 * (1 - Real.log 3 / (17 / 5)) * Real.cos (γ * Real.log 3) +
        Real.log 3 / 9 * (1 - 2 * Real.log 3 / (17 / 5)) * Real.cos (2 * (γ * Real.log 3)) +
        Real.log 3 / 27 * (1 - 3 * Real.log 3 / (17 / 5)) * Real.cos (3 * (γ * Real.log 3))) +
      (Real.log 5 / 5 * (1 - Real.log 5 / (17 / 5)) * Real.cos (γ * Real.log 5) +
        Real.log 5 / 25 * (1 - 2 * Real.log 5 / (17 / 5)) * Real.cos (2 * (γ * Real.log 5))) +
      Real.log 7 / 7 * (1 - Real.log 7 / (17 / 5)) * Real.cos (γ * Real.log 7) +
      Real.log 11 / 11 * (1 - Real.log 11 / (17 / 5)) * Real.cos (γ * Real.log 11) +
      Real.log 13 / 13 * (1 - Real.log 13 / (17 / 5)) * Real.cos (γ * Real.log 13) +
      Real.log 17 / 17 * (1 - Real.log 17 / (17 / 5)) * Real.cos (γ * Real.log 17) +
      Real.log 19 / 19 * (1 - Real.log 19 / (17 / 5)) * Real.cos (γ * Real.log 19) +
      Real.log 23 / 23 * (1 - Real.log 23 / (17 / 5)) * Real.cos (γ * Real.log 23) +
      Real.log 29 / 29 * (1 - Real.log 29 / (17 / 5)) * Real.cos (γ * Real.log 29) := by
  have hc {a b : ℕ} (h : Nat.Coprime a b) (ha : 2 ≤ a) (hb : 2 ≤ b) : vonMangoldt (a * b) = 0 :=
    vonMangoldt_mul_eq_zero_of_coprime h ha hb
  have hpow (p k : ℕ) (hp : p.Prime) (hk : k ≠ 0) : vonMangoldt (p ^ k) = Real.log p := by
    rw [ArithmeticFunction.vonMangoldt_apply_pow hk, ArithmeticFunction.vonMangoldt_apply_prime hp]
  have h0 : vonMangoldt 0 = 0 := ArithmeticFunction.map_zero
  have h1 : vonMangoldt 1 = 0 := ArithmeticFunction.vonMangoldt_apply_one
  have h6 : vonMangoldt 6 = 0 := hc (a := 2) (b := 3) (by norm_num) (by norm_num) (by norm_num)
  have h10 : vonMangoldt 10 = 0 := hc (a := 2) (b := 5) (by norm_num) (by norm_num) (by norm_num)
  have h12 : vonMangoldt 12 = 0 := hc (a := 3) (b := 4) (by norm_num) (by norm_num) (by norm_num)
  have h14 : vonMangoldt 14 = 0 := hc (a := 2) (b := 7) (by norm_num) (by norm_num) (by norm_num)
  have h15 : vonMangoldt 15 = 0 := hc (a := 3) (b := 5) (by norm_num) (by norm_num) (by norm_num)
  have h18 : vonMangoldt 18 = 0 := hc (a := 2) (b := 9) (by norm_num) (by norm_num) (by norm_num)
  have h20 : vonMangoldt 20 = 0 := hc (a := 4) (b := 5) (by norm_num) (by norm_num) (by norm_num)
  have h21 : vonMangoldt 21 = 0 := hc (a := 3) (b := 7) (by norm_num) (by norm_num) (by norm_num)
  have h22 : vonMangoldt 22 = 0 := hc (a := 2) (b := 11) (by norm_num) (by norm_num) (by norm_num)
  have h24 : vonMangoldt 24 = 0 := hc (a := 3) (b := 8) (by norm_num) (by norm_num) (by norm_num)
  have h26 : vonMangoldt 26 = 0 := hc (a := 2) (b := 13) (by norm_num) (by norm_num) (by norm_num)
  have h28 : vonMangoldt 28 = 0 := hc (a := 4) (b := 7) (by norm_num) (by norm_num) (by norm_num)
  have hp2 : vonMangoldt 2 = Real.log 2 := by simpa using hpow 2 1 (by norm_num) (by norm_num)
  have hp3 : vonMangoldt 3 = Real.log 3 := by simpa using hpow 3 1 (by norm_num) (by norm_num)
  have hp5 : vonMangoldt 5 = Real.log 5 := by simpa using hpow 5 1 (by norm_num) (by norm_num)
  have hp7 : vonMangoldt 7 = Real.log 7 := by simpa using hpow 7 1 (by norm_num) (by norm_num)
  have hp11 : vonMangoldt 11 = Real.log 11 := by simpa using hpow 11 1 (by norm_num) (by norm_num)
  have hp13 : vonMangoldt 13 = Real.log 13 := by simpa using hpow 13 1 (by norm_num) (by norm_num)
  have hp17 : vonMangoldt 17 = Real.log 17 := by simpa using hpow 17 1 (by norm_num) (by norm_num)
  have hp19 : vonMangoldt 19 = Real.log 19 := by simpa using hpow 19 1 (by norm_num) (by norm_num)
  have hp23 : vonMangoldt 23 = Real.log 23 := by simpa using hpow 23 1 (by norm_num) (by norm_num)
  have hp29 : vonMangoldt 29 = Real.log 29 := by simpa using hpow 29 1 (by norm_num) (by norm_num)
  have hp4 : vonMangoldt 4 = Real.log 2 := by
    have := hpow 2 2 (by norm_num) (by norm_num); norm_num at this; exact this
  have hp8 : vonMangoldt 8 = Real.log 2 := by
    have := hpow 2 3 (by norm_num) (by norm_num); norm_num at this; exact this
  have hp16 : vonMangoldt 16 = Real.log 2 := by
    have := hpow 2 4 (by norm_num) (by norm_num); norm_num at this; exact this
  have hp9 : vonMangoldt 9 = Real.log 3 := by
    have := hpow 3 2 (by norm_num) (by norm_num); norm_num at this; exact this
  have hp27 : vonMangoldt 27 = Real.log 3 := by
    have := hpow 3 3 (by norm_num) (by norm_num); norm_num at this; exact this
  have hp25 : vonMangoldt 25 = Real.log 5 := by
    have := hpow 5 2 (by norm_num) (by norm_num); norm_num at this; exact this
  have hl4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hl8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
  have hl16 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
  have hl9 : Real.log 9 = 2 * Real.log 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hl27 : Real.log 27 = 3 * Real.log 3 := by
    rw [show (27 : ℝ) = 3 ^ 3 by norm_num, Real.log_pow]; norm_num
  have hl25 : Real.log 25 = 2 * Real.log 5 := by
    rw [show (25 : ℝ) = 5 ^ 2 by norm_num, Real.log_pow]; norm_num
  have ht (m : ℝ) (h1m : 1 ≤ m) (h29 : m ≤ 29) :
      triangleFn (17 / 5) (Real.log m) = 1 - Real.log m / (17 / 5) :=
    tri_band_eq (Real.log_nonneg h1m) (log_le_band (by linarith only [h1m]) h29)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_ofNat, Nat.cast_zero,
    Nat.cast_one, h0, h1, h6, h10, h12, h14, h15, h18, h20, h21, h22, h24, h26, h28,
    hp2, hp3, hp4, hp5, hp7, hp8, hp9, hp11, hp13, hp16, hp17, hp19, hp23, hp25, hp27, hp29,
    zero_div, zero_mul, zero_add, add_zero]
  rw [ht 2 (by norm_num) (by norm_num), ht 3 (by norm_num) (by norm_num),
    ht 4 (by norm_num) (by norm_num), ht 5 (by norm_num) (by norm_num),
    ht 7 (by norm_num) (by norm_num), ht 8 (by norm_num) (by norm_num),
    ht 9 (by norm_num) (by norm_num), ht 11 (by norm_num) (by norm_num),
    ht 13 (by norm_num) (by norm_num), ht 16 (by norm_num) (by norm_num),
    ht 17 (by norm_num) (by norm_num), ht 19 (by norm_num) (by norm_num),
    ht 23 (by norm_num) (by norm_num), ht 25 (by norm_num) (by norm_num),
    ht 27 (by norm_num) (by norm_num), ht 29 (by norm_num) (by norm_num),
    hl4, hl8, hl16, hl9, hl27, hl25]
  have e2 : γ * (2 * Real.log 2) = 2 * (γ * Real.log 2) := by ring
  have e3 : γ * (3 * Real.log 2) = 3 * (γ * Real.log 2) := by ring
  have e4 : γ * (4 * Real.log 2) = 2 * (2 * (γ * Real.log 2)) := by ring
  have e9 : γ * (2 * Real.log 3) = 2 * (γ * Real.log 3) := by ring
  have e27 : γ * (3 * Real.log 3) = 3 * (γ * Real.log 3) := by ring
  have e25 : γ * (2 * Real.log 5) = 2 * (γ * Real.log 5) := by ring
  rw [e2, e3, e4, e9, e27, e25]
  ring

private theorem poly_ge_seventy (γ : ℝ) :
    -(0.8631 : ℝ) ≤ ∑ n ∈ Finset.range 30,
      vonMangoldt n / n * triangleFn (17 / 5) (Real.log n) *
        Real.cos (γ * Real.log n) := by
  rw [poly_eq_seventy]
  have hl2a := Real.log_two_gt_d9
  have hl2b := Real.log_two_lt_d9
  obtain ⟨l2, hl2⟩ : ∃ l2, l2 = Real.log 2 := ⟨_, rfl⟩
  rw [← hl2] at hl2a hl2b ⊢
  obtain ⟨s, hs⟩ : ∃ s, s = l2 ^ 2 := ⟨_, rfl⟩
  have hs1 : (0.6931471803 : ℝ) ^ 2 ≤ s := by rw [hs]; exact pow_le_pow_left₀ (by norm_num) hl2a.le 2
  have hs2 : s ≤ (0.6931471808 : ℝ) ^ 2 := by rw [hs]; exact pow_le_pow_left₀ (by linarith only [hl2a]) hl2b.le 2
  norm_num at hs1 hs2
  -- Family of `2`: `{2, 4, 8, 16}`.
  obtain ⟨u, hu⟩ : ∃ u, u = Real.cos (γ * l2) := ⟨_, rfl⟩
  have hu0 : -1 ≤ u := by rw [hu]; exact Real.neg_one_le_cos _
  have ec2 : Real.cos (2 * (γ * l2)) = 2 * u ^ 2 - 1 := by rw [Real.cos_two_mul, hu]
  have ec3 : Real.cos (3 * (γ * l2)) = 4 * u ^ 3 - 3 * u := by rw [Real.cos_three_mul, hu]
  have ec4 : Real.cos (2 * (2 * (γ * l2))) = 8 * u ^ 4 - 8 * u ^ 2 + 1 := by
    rw [Real.cos_two_mul, ec2]; ring
  have eA2 : l2 / 2 * (1 - l2 / (17 / 5)) = l2 / 2 - 5 * s / 34 := by rw [hs]; ring
  have eB2 : l2 / 4 * (1 - 2 * l2 / (17 / 5)) = l2 / 4 - 5 * s / 34 := by rw [hs]; ring
  have eC2 : l2 / 8 * (1 - 3 * l2 / (17 / 5)) = l2 / 8 - 15 * s / 136 := by rw [hs]; ring
  have eD2 : l2 / 16 * (1 - 4 * l2 / (17 / 5)) = l2 / 16 - 5 * s / 68 := by rw [hs]; ring
  have hfam2 := family_two_seventy
    (A := l2 / 2 - 5 * s / 34) (B := l2 / 4 - 5 * s / 34)
    (C := l2 / 8 - 15 * s / 136) (D := l2 / 16 - 5 * s / 68)
    hu0 (by linarith only [hl2a, hs2]) (by linarith only [hl2a, hl2b, hs1, hs2])
    (by linarith only [hl2a, hl2b, hs1, hs2]) (by linarith only [hl2a, hl2b, hs1, hs2])
  -- Family of `3`: `{3, 9, 27}`.
  have hl3a := log3_lb70
  have hl3b := log3_ub70
  obtain ⟨l3, hl3⟩ : ∃ l3, l3 = Real.log 3 := ⟨_, rfl⟩
  rw [← hl3] at hl3a hl3b ⊢
  obtain ⟨v, hv⟩ : ∃ v, v = Real.cos (γ * l3) := ⟨_, rfl⟩
  have hv0 : -1 ≤ v := by rw [hv]; exact Real.neg_one_le_cos _
  have ecv2 : Real.cos (2 * (γ * l3)) = 2 * v ^ 2 - 1 := by rw [Real.cos_two_mul, hv]
  have ecv3 : Real.cos (3 * (γ * l3)) = 4 * v ^ 3 - 3 * v := by rw [Real.cos_three_mul, hv]
  have hl3s1 : (1.09857 : ℝ) ^ 2 ≤ l3 ^ 2 := pow_le_pow_left₀ (by norm_num) hl3a 2
  have hl3s2 : l3 ^ 2 ≤ (1.09872 : ℝ) ^ 2 := pow_le_pow_left₀ (by linarith only [hl3a]) hl3b 2
  norm_num at hl3s1 hl3s2
  have eA3 : l3 / 3 * (1 - l3 / (17 / 5)) = l3 / 3 - 5 * l3 ^ 2 / 51 := by ring
  have eB3 : l3 / 9 * (1 - 2 * l3 / (17 / 5)) = l3 / 9 - 10 * l3 ^ 2 / 153 := by ring
  have eC3 : l3 / 27 * (1 - 3 * l3 / (17 / 5)) = l3 / 27 - 5 * l3 ^ 2 / 153 := by ring
  have hfam3 := family_three_cubic
    (A := l3 / 3 - 5 * l3 ^ 2 / 51) (B := l3 / 9 - 10 * l3 ^ 2 / 153)
    (C := l3 / 27 - 5 * l3 ^ 2 / 153) hv0
    (by linarith only [hl3a, hl3s2]) (by linarith only [hl3a, hl3s2])
    (by linarith only [hl3a, hl3b, hl3s1, hl3s2])
  -- Family of `5`: `{5, 25}`.
  have hl5a := log5_lb70
  have hl5b := log5_ub70
  obtain ⟨l5, hl5⟩ : ∃ l5, l5 = Real.log 5 := ⟨_, rfl⟩
  rw [← hl5] at hl5a hl5b ⊢
  obtain ⟨y, hy⟩ : ∃ y, y = Real.cos (γ * l5) := ⟨_, rfl⟩
  have hy0 : -1 ≤ y := by rw [hy]; exact Real.neg_one_le_cos _
  have ecy2 : Real.cos (2 * (γ * l5)) = 2 * y ^ 2 - 1 := by rw [Real.cos_two_mul, hy]
  have hl5s1 : (1.60937 : ℝ) ^ 2 ≤ l5 ^ 2 := pow_le_pow_left₀ (by norm_num) hl5a 2
  have hl5s2 : l5 ^ 2 ≤ (1.60952 : ℝ) ^ 2 := pow_le_pow_left₀ (by linarith only [hl5a]) hl5b 2
  norm_num at hl5s1 hl5s2
  have eE5 : l5 / 5 * (1 - l5 / (17 / 5)) = l5 / 5 - l5 ^ 2 / 17 := by ring
  have eF5 : l5 / 25 * (1 - 2 * l5 / (17 / 5)) = l5 / 25 - 2 * l5 ^ 2 / 85 := by ring
  have hfam5 := family_three
    (E := l5 / 5 - l5 ^ 2 / 17) (F := l5 / 25 - 2 * l5 ^ 2 / 85) hy0
    (by linarith only [hl5a, hl5s2]) (by linarith only [hl5a, hl5b, hl5s1, hl5s2])
  -- Single primes `7, 11, 13, 17, 19, 23, 29`.
  have hp (x x0 p : ℝ) (θ : ℝ) (h0 : x0 ≤ x) (hx0 : 17 / 10 ≤ x0) (hp : 0 < p) (hxhi : x ≤ 17 / 5) :
      -(x0 / p * (1 - x0 / (17 / 5))) ≤ x / p * (1 - x / (17 / 5)) * Real.cos θ := by
    have hnonneg : 0 ≤ x / p * (1 - x / (17 / 5)) := by
      have : 0 ≤ 1 - x / (17 / 5) := by linarith only [hxhi]
      have hx : 0 ≤ x := by linarith only [h0, hx0]
      positivity
    have hle := prime_term_le_seventy h0 hx0 hp
    have hcos := Real.neg_one_le_cos θ
    nlinarith only [hnonneg, hle, hcos]
  have h7 := hp _ 1.94582 7 (γ * Real.log 7) log7_lb70 (by norm_num) (by norm_num)
    (log_le_band (by norm_num) (by norm_num))
  have h11 := hp _ 2.3976 11 (γ * Real.log 11) log11_lb70 (by norm_num) (by norm_num)
    (log_le_band (by norm_num) (by norm_num))
  have h13 := hp _ 2.56464 13 (γ * Real.log 13) log13_lb70 (by norm_num) (by norm_num)
    (log_le_band (by norm_num) (by norm_num))
  have h17 := hp _ 2.83286 17 (γ * Real.log 17) log17_lb70 (by norm_num) (by norm_num)
    (log_le_band (by norm_num) (by norm_num))
  have h19 := hp _ 2.94401 19 (γ * Real.log 19) log19_lb70 (by norm_num) (by norm_num)
    (log_le_band (by norm_num) (by norm_num))
  have h23 := hp _ 3.13528 23 (γ * Real.log 23) log23_lb70 (by norm_num) (by norm_num)
    (log_le_band (by norm_num) (by norm_num))
  have h29 := hp _ 3.36671 29 (γ * Real.log 29) log29_lb70 (by norm_num) (by norm_num)
    (log_le_band (by norm_num) (by norm_num))
  norm_num at h7 h11 h13 h17 h19 h23 h29
  rw [eA2, eB2, eC2, eD2, eA3, eB3, eC3, eE5, eF5,
    ec2, ec3, ec4, ecv2, ecv3, ecy2, ← hu, ← hv, ← hy]
  norm_num at hfam2 hfam3 hfam5 ⊢
  linarith only [hfam2, hfam3, hfam5, h7, h11, h13, h17, h19, h23, h29,
    hl2a, hl2b, hs1, hs2, hl3a, hl3b, hl3s1, hl3s2, hl5a, hl5b, hl5s1, hl5s2]

private theorem budget_left_ge_seventy :
    (2.0769 : ℝ) ≤ 2 * (2 - 4 * (1 - Real.exp (-((17 / 5 : ℝ) / 2))) / (17 / 5)) := by
  have he := exp_neg_seventeen_tenths_ge
  rw [show ((17 / 5 : ℝ) / 2) = 17 / 10 by norm_num]
  norm_num at he ⊢
  linarith only [he]

private theorem arch_lt_seventy {γ : ℝ} (h67 : 67 ≤ γ) (h70 : γ ≤ 70) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      8 / (17 / 5) / γ ^ 2 + 9 / (2 * Real.pi * (17 / 5)) / γ < 1.2137 := by
  have hγ0 : 0 < γ := by linarith only [h67]
  have hlog_le : Real.log (9 / 4 + γ ^ 2 / 4) ≤ 903 / 88 * Real.log 2 := by
    have h1 : Real.log (9 / 4 + γ ^ 2 / 4) ≤ Real.log (4909 / 4) :=
      Real.log_le_log (by positivity) (by nlinarith only [h67, h70])
    have h2 : Real.log (4909 / 4) ≤ (903 : ℝ) / (88 : ℕ) * Real.log 2 :=
      log_le_of_pow_le_two_pow' (p := 4909 / 4) (by norm_num) (k := 88) (m := 903)
        (by norm_num)
        (by rw [show (903 : ℕ) = 200 + (200 + (200 + (200 + 103))) by rfl,
            pow_add, pow_add, pow_add, pow_add]; norm_num)
    norm_num at h2
    exact h1.trans h2
  have htail1 : 8 / (17 / 5) / γ ^ 2 ≤ 8 / (17 / 5) / 67 ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (pow_le_pow_left₀ (by norm_num) h67 2)
  have htail2 : 9 / (2 * Real.pi * (17 / 5)) / γ ≤ 0.4214 / 67 := by
    have hc : 9 / (2 * Real.pi * (17 / 5)) ≤ 0.4214 := by
      have hπ := Real.pi_gt_d4
      rw [div_le_iff₀ (by positivity)]
      linarith only [hπ]
    exact (div_le_div_of_nonneg_right hc hγ0.le).trans
      (div_le_div_of_nonneg_left (by norm_num) (by norm_num) h67)
  have hπ := log_pi_lb70
  have hl2 := Real.log_two_lt_d9
  norm_num at htail1 htail2 ⊢
  linarith only [hlog_le, htail1, htail2, hπ, hl2]

/-- **Analytic RH verification through height `70`** (zero computations): no off-line zero of `ξ`
has ordinate in `(0, 70]`. -/
theorem rhVerifiedThrough_seventy : _root_.RHTower.RHVerifiedThrough 70 := by
  intro ρ hzero hre0 hre1 him0 him70
  rcases le_or_gt ρ.im 67 with hle67 | hgt67
  · exact rhVerifiedThrough_sixtySeven hzero hre0 hre1 him0 hle67
  · by_contra hoff
    let rhoSupport : _root_.RHTower.XiDivisorSupport :=
      ⟨ρ, _root_.RHTower.mem_xi_divisor_support_of_eq_zero hzero⟩
    let q : _root_.RHTower.XiZeroCopy := by
      have hpos := _root_.RHTower.xi_divisor_pos_on_support rhoSupport
      have hn : 0 < Int.toNat
          ((MeromorphicOn.divisor _root_.RHTower.xi Set.univ) (rhoSupport : ℂ)) := by omega
      exact ⟨rhoSupport, ⟨0, hn⟩⟩
    have hqre : (q.1 : ℂ).re ≠ 1 / 2 := hoff
    have hqim : (q.1 : ℂ).im = ρ.im := rfl
    have hb := budget_at_edge (L := 17 / 5) (N := 30) (by norm_num)
      (fun n hn => band_le_log n hn) q hqre hqim (by linarith only [hgt67])
    have hpoly := poly_ge_seventy ρ.im
    have hleft := budget_left_ge_seventy
    have harch := arch_lt_seventy hgt67.le him70
    norm_num at hb hleft harch hpoly
    linarith only [hb, hleft, harch, hpoly]

end HeightSeventy

/-- Unconditional nonvanishing of `ζ(w)` across `1/2 < Re w < 1` for all `|Im w| ≤ 70`. -/
theorem riemannZeta_ne_zero_of_strip_abs_im_le_seventy {w : ℂ}
    (hlo : 1 / 2 < w.re) (hhi : w.re < 1) (him : |w.im| ≤ 70) :
    riemannZeta w ≠ 0 := by
  intro hz
  have hw0 : 0 < w.re := by linarith
  have hw1 : w ≠ 1 := fun he => hhi.ne (by rw [he, Complex.one_re])
  have hxi : _root_.RHTower.xi w = 0 := (_root_.RHTower.xi_eq_zero_iff hw0 hw1).mpr hz
  have hgt := VerifiedHeightRungs.lt_abs_im_of_rhVerifiedThrough
    rhVerifiedThrough_seventy hxi hw0 hhi (by linarith)
  linarith

/-- Unconditional `|ζ(w)|`-free single-cutoff margin for the actual shell weights across the entire
band `1/2 < Re w < 1`, `|Im w| ≤ 70` (advancing unconditionally across `67 < |Im w| ≤ 70`). -/
theorem exists_zetaFree_margin_of_abs_im_le_seventy (t : ExceptionalTime) (j : ℕ)
    {w : ℂ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1) (him : |w.im| ≤ 70) :
    ∃ X₀ : ℕ, 1 ≤ X₀ ∧ zetaFreeTruncationBound t j X₀ w < ‖renormalizedCutoff t j X₀ w‖ := by
  have hw0 : 0 < w.re := by linarith
  have hw1 : w ≠ 1 := fun he => hhi.ne (by rw [he, Complex.one_re])
  exact (exists_zetaFree_margin_iff_zeta_ne_zero t j hw0 hw1).mpr
    (riemannZeta_ne_zero_of_strip_abs_im_le_seventy hlo hhi him)

/-- Exact reduction of `RiemannHypothesis` to the `|ζ(w)|`-free single-cutoff margin above height `70`:
`1/2 < Re w ≤ 20999 / 24000` and `70 < |Im w|`. -/
theorem rh_iff_zetaFree_margin_above_seventy (t : ExceptionalTime) (j : ℕ) :
    RiemannHypothesis ↔
      ∀ w : ℂ, 1 / 2 < w.re → w.re ≤ 20999 / 24000 → 70 < |w.im| →
        ∃ X₀ : ℕ, 1 ≤ X₀ ∧ zetaFreeTruncationBound t j X₀ w < ‖renormalizedCutoff t j X₀ w‖ := by
  rw [_root_.RHTower.riemannHypothesis_iff_riemannZeta_ne_zero_of_mem_upper_strip]
  constructor
  · intro hRH w hlo hhi _
    have hw0 : 0 < w.re := by linarith
    have hw_lt1 : w.re < 1 := by linarith
    have hw1 : w ≠ 1 := fun he => hw_lt1.ne (by rw [he, Complex.one_re])
    exact (exists_zetaFree_margin_iff_zeta_ne_zero t j hw0 hw1).mpr (hRH w hlo hw_lt1)
  · intro hmarg w hlo hhi
    rcases lt_or_ge (20999 / 24000 : ℝ) w.re with hright | hstrip
    · exact MetaplecticMobiusDescent.CubicEisenstein.riemannZeta_ne_zero_of_sub_seven_eighths_lt_re
        hright
    · rcases le_or_gt |w.im| 70 with hlow | hhigh
      · exact riemannZeta_ne_zero_of_strip_abs_im_le_seventy hlo hhi hlow
      · have hw0 : 0 < w.re := by linarith
        have hw1 : w ≠ 1 := fun he => hhi.ne (by rw [he, Complex.one_re])
        exact (exists_zetaFree_margin_iff_zeta_ne_zero t j hw0 hw1).mp (hmarg w hlo hstrip hhigh)

/-! ### Part 2: Reflected Lorentzian window cap and pigeonhole lower bounds at every height `τ` -/

/-- Set of points in `{1/2 < Re w ≤ 20999/24000 ∧ |Im w - τ| ≤ h}` lacking a strict `ζ`-free
single-cutoff margin for clock `(t, j)`. -/
def missingZetaFreeMarginWindow (t : ExceptionalTime) (j : ℕ) (h τ : ℝ) : Set ℂ :=
  {w : ℂ | 1 / 2 < w.re ∧ w.re ≤ 20999 / 24000 ∧ |w.im - τ| ≤ h ∧
    ¬∃ X₀ : ℕ, 1 ≤ X₀ ∧ zetaFreeTruncationBound t j X₀ w < ‖renormalizedCutoff t j X₀ w‖}

private def mkXiZeroCopy {z : ℂ} (h0 : 0 < z.re) (h1 : z.re < 1) (hz : riemannZeta z = 0) :
    _root_.RHTower.XiZeroCopy := by
  have hz_ne1 : z ≠ 1 := fun he => h1.ne (by rw [he, Complex.one_re])
  have hxi : _root_.RHTower.xi z = 0 := (_root_.RHTower.xi_eq_zero_iff h0 hz_ne1).mpr hz
  let s : _root_.RHTower.XiDivisorSupport :=
    ⟨z, _root_.RHTower.mem_xi_divisor_support_of_eq_zero hxi⟩
  have hpos := _root_.RHTower.xi_divisor_pos_on_support s
  exact ⟨s, ⟨0, by omega⟩⟩

/-- At **every** height `τ ∈ ℝ` (including all `|τ| > 70`) and every half-width `h ≥ 0`, the set of
points in `{1/2 < Re w ≤ 20999/24000 ∧ |Im w - τ| ≤ h}` lacking a strict `ζ`-free cutoff margin is
finite of cardinality at most `4 (1 + h^2) (xiLineTwoLogDerivConstant + log(|τ| + 4))`. -/
theorem ncard_missingZetaFreeMarginWindow_le (t : ExceptionalTime) (j : ℕ) (h τ : ℝ) :
    (missingZetaFreeMarginWindow t j h τ).Finite ∧
      ((missingZetaFreeMarginWindow t j h τ).ncard : ℝ) ≤
        4 * (1 + h ^ 2) * (_root_.RHTower.xiLineTwoLogDerivConstant + Real.log (|τ| + 4)) := by
  classical
  set M := missingZetaFreeMarginWindow t j h τ
  set W := _root_.RHTower.xiOrdinateWindow h τ
  have hW_fin : W.Finite := _root_.RHTower.finite_xiOrdinateWindow h τ
  -- Every `w ∈ M` satisfies `ζ(w) = 0` and produces two disjoint `XiZeroCopy`s in `W`: `w` and `conj(1 - w)`.
  have hz_of_mem : ∀ w ∈ M, 0 < w.re ∧ w.re < 1 ∧ riemannZeta w = 0 := by
    rintro w ⟨hlo, hhi, _, hnot⟩
    have hw0 : 0 < w.re := by linarith
    have hw_lt1 : w.re < 1 := by linarith
    have hw1 : w ≠ 1 := fun he => hw_lt1.ne (by rw [he, Complex.one_re])
    exact ⟨hw0, hw_lt1,
      by_contra fun hne => hnot ((exists_zetaFree_margin_iff_zeta_ne_zero t j hw0 hw1).mpr hne)⟩
  let ι₁ : M → _root_.RHTower.XiZeroCopy := fun w =>
    mkXiZeroCopy (hz_of_mem w.1 w.2).1 (hz_of_mem w.1 w.2).2.1 (hz_of_mem w.1 w.2).2.2
  have hι₁_val : ∀ x : M, ((ι₁ x).1 : ℂ) = x.1 := fun _ => rfl
  have hι₁_inj : Function.Injective ι₁ := fun x y hxy =>
    Subtype.ext (by simpa only [hι₁_val] using congrArg (fun q : _root_.RHTower.XiZeroCopy => (q.1 : ℂ)) hxy)
  have hι₁_mem : ∀ x : M, ι₁ x ∈ W := fun x => by
    rw [_root_.RHTower.mem_xiOrdinateWindow_iff, hι₁_val]
    exact x.2.2.2.1
  have hM_fin : M.Finite := by
    haveI : Finite W := hW_fin.to_subtype
    exact Finite.of_injective (fun x : M => (⟨ι₁ x, hι₁_mem x⟩ : W)) fun x y hxy =>
      hι₁_inj (congrArg Subtype.val hxy)
  -- Construct the reflected injection `w ↦ conj (1 - w)` into `W` with `Re < 1 / 2`.
  have h_refl : ∀ x : M, 0 < (conj (1 - x.1)).re ∧ (conj (1 - x.1)).re < 1 ∧
      riemannZeta (conj (1 - x.1)) = 0 := by
    intro x
    obtain ⟨hw0, hw1, hzw⟩ := hz_of_mem x.1 x.2
    have hz1w : riemannZeta (1 - x.1) = 0 :=
      _root_.RHTower.riemannZeta_one_sub_eq_zero_of_mem_openStrip hzw hw0 hw1
    refine ⟨?_, ?_, by rw [riemannZeta_conj, hz1w, map_zero]⟩
    · simp only [Complex.conj_re, Complex.sub_re, Complex.one_re]; linarith
    · simp only [Complex.conj_re, Complex.sub_re, Complex.one_re]; linarith
  let ι₂ : M → _root_.RHTower.XiZeroCopy := fun x =>
    mkXiZeroCopy (h_refl x).1 (h_refl x).2.1 (h_refl x).2.2
  have hι₂_val : ∀ x : M, ((ι₂ x).1 : ℂ) = conj (1 - x.1) := fun _ => rfl
  have hι₂_inj : Function.Injective ι₂ := by
    intro x y hxy
    have hc : conj (1 - x.1) = conj (1 - y.1) := by
      simpa only [hι₂_val] using congrArg (fun q : _root_.RHTower.XiZeroCopy => (q.1 : ℂ)) hxy
    have h1 : 1 - x.1 = 1 - y.1 := by
      have := congrArg (starRingEnd ℂ) hc
      simpa using this
    exact Subtype.ext (by linear_combination -h1)
  have hι₂_mem : ∀ x : M, ι₂ x ∈ W := fun x => by
    rw [_root_.RHTower.mem_xiOrdinateWindow_iff, hι₂_val]
    have him_eq : (conj (1 - x.1)).im = x.1.im := by simp
    rw [him_eq]
    exact x.2.2.2.1
  -- `range ι₁` (`Re > 1/2`) and `range ι₂` (`Re < 1/2`) are disjoint subsets of `W`.
  have hdisj : Disjoint (Set.range ι₁) (Set.range ι₂) := by
    rw [Set.disjoint_left]
    rintro _ ⟨x, rfl⟩ ⟨y, heq⟩
    have hre_eq := congrArg (fun q : _root_.RHTower.XiZeroCopy => ((q.1 : ℂ)).re) heq
    rw [hι₂_val, hι₁_val, Complex.conj_re, Complex.sub_re, Complex.one_re] at hre_eq
    linarith [x.2.1, y.2.1]
  let FM : Finset M := hM_fin.toFinset.attach.map
    ⟨fun x => ⟨x.1, hM_fin.mem_toFinset.mp x.2⟩,
      fun x y h => Subtype.ext (by simpa using congrArg Subtype.val h)⟩
  let I₁ : Finset _root_.RHTower.XiZeroCopy := FM.image ι₁
  let I₂ : Finset _root_.RHTower.XiZeroCopy := FM.image ι₂
  have hI_disj : Disjoint I₁ I₂ := by
    rw [Finset.disjoint_left]
    intro q hq1 hq2
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hq1
    obtain ⟨y, _, heq⟩ := Finset.mem_image.mp hq2
    exact Set.disjoint_left.mp hdisj ⟨x, rfl⟩ ⟨y, heq⟩
  have hI_sub : (I₁ ∪ I₂ : Finset _root_.RHTower.XiZeroCopy) ⊆ hW_fin.toFinset := by
    intro q hq
    rw [Set.Finite.mem_toFinset]
    rcases Finset.mem_union.mp hq with h1 | h2
    · obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp h1; exact hι₁_mem x
    · obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp h2; exact hι₂_mem x
  have hcard_union : 2 * M.ncard ≤ W.ncard := by
    have hc1 : I₁.card = FM.card := Finset.card_image_of_injective FM hι₁_inj
    have hc2 : I₂.card = FM.card := Finset.card_image_of_injective FM hι₂_inj
    have hFM_eq : FM.card = M.ncard := by
      dsimp only [FM]
      rw [Finset.card_map, Finset.card_attach, ← Set.ncard_eq_toFinset_card M hM_fin]
    have hW_eq : hW_fin.toFinset.card = W.ncard := (Set.ncard_eq_toFinset_card W hW_fin).symm
    have hle := Finset.card_le_card hI_sub
    rw [Finset.card_union_of_disjoint hI_disj, hc1, hc2, hFM_eq, hW_eq] at hle
    omega
  have hW_bound := _root_.RHTower.ncard_xiOrdinateWindow_le_log h τ
  have h2_le : 2 * (M.ncard : ℝ) ≤ (W.ncard : ℝ) := by exact_mod_cast hcard_union
  exact ⟨hM_fin, by linarith⟩

/-- **Unconditional pigeonhole reading lower bound at every height `τ`:** in any ordinate window
`[τ - h, τ + h]` (including `h = 0`, a single horizontal line at arbitrary height `|τ| > 70`), out
of every finite probe set `S ⊆ {1/2 < Re w ≤ 20999/24000 ∧ |Im w - τ| ≤ h}` whose size exceeds
`4 (1 + h^2) (xiLineTwoLogDerivConstant + log(|τ| + 4))`, at least one point `w ∈ S` unconditionally
admits an actual finite cutoff `X₀ ≥ 1` beating `zetaFreeTruncationBound`. -/
theorem exists_point_with_zetaFree_margin_of_card_gt (t : ExceptionalTime) (j : ℕ)
    {h τ : ℝ} {S : Finset ℂ}
    (hS : ∀ w ∈ S, 1 / 2 < w.re ∧ w.re ≤ 20999 / 24000 ∧ |w.im - τ| ≤ h)
    (hcard : 4 * (1 + h ^ 2) * (_root_.RHTower.xiLineTwoLogDerivConstant + Real.log (|τ| + 4)) <
      (S.card : ℝ)) :
    ∃ w ∈ S, ∃ X₀ : ℕ, 1 ≤ X₀ ∧ zetaFreeTruncationBound t j X₀ w < ‖renormalizedCutoff t j X₀ w‖ := by
  by_contra hno
  have hall_bad : ∀ w ∈ S,
      ¬∃ X₀ : ℕ, 1 ≤ X₀ ∧ zetaFreeTruncationBound t j X₀ w < ‖renormalizedCutoff t j X₀ w‖ :=
    fun w hw hex => hno ⟨w, hw, hex⟩
  obtain ⟨hM_fin, hM_le⟩ := ncard_missingZetaFreeMarginWindow_le t j h τ
  have hsub : (S : Set ℂ) ⊆ missingZetaFreeMarginWindow t j h τ := fun w hw =>
    ⟨(hS w hw).1, (hS w hw).2.1, (hS w hw).2.2, hall_bad w hw⟩
  have hle_ncard : S.card ≤ (missingZetaFreeMarginWindow t j h τ).ncard := by
    rw [← Set.ncard_coe_finset S]
    exact Set.ncard_le_ncard hsub hM_fin
  have hle_r : (S.card : ℝ) ≤ ((missingZetaFreeMarginWindow t j h τ).ncard : ℝ) := by
    exact_mod_cast hle_ncard
  linarith

/-- At **every** height `τ ∈ ℝ` (including all `|τ| > 70`) and on **every** nonempty open interval
`(a, b) ⊆ (1/2, 20999/24000]`, infinitely many points `σ + iτ` unconditionally possess an actual
finite cutoff `X₀ ≥ 1` whose magnitude exceeds `zetaFreeTruncationBound`. -/
theorem infinite_zetaFree_margin_on_horizontal_interval (t : ExceptionalTime) (j : ℕ)
    (τ : ℝ) {a b : ℝ} (hab : a < b) (ha : 1 / 2 ≤ a) (hb : b ≤ 20999 / 24000) :
    {σ : ℝ | a < σ ∧ σ < b ∧
      ∃ X₀ : ℕ, 1 ≤ X₀ ∧
        zetaFreeTruncationBound t j X₀ ((σ : ℂ) + (τ : ℂ) * Complex.I) <
          ‖renormalizedCutoff t j X₀ ((σ : ℂ) + (τ : ℂ) * Complex.I)‖}.Infinite := by
  have hIoo_inf : (Set.Ioo a b).Infinite := Set.Ioo_infinite hab
  obtain ⟨hM_fin, _⟩ := ncard_missingZetaFreeMarginWindow_le t j 0 τ
  let emb : ℝ → ℂ := fun σ => (σ : ℂ) + (τ : ℂ) * Complex.I
  have hemb_inj : Function.Injective emb := fun x y hxy => by
    have := congrArg Complex.re hxy
    simpa [emb] using this
  have hbad_fin : {σ : ℝ | a < σ ∧ σ < b ∧
      ¬∃ X₀ : ℕ, 1 ≤ X₀ ∧
        zetaFreeTruncationBound t j X₀ (emb σ) < ‖renormalizedCutoff t j X₀ (emb σ)‖}.Finite := by
    refine (hM_fin.preimage hemb_inj.injOn).subset ?_
    rintro σ ⟨hσa, hσb, hnot⟩
    refine ⟨by simp [emb]; linarith, by simp [emb]; linarith, ?_, hnot⟩
    simp [emb]
  have hdiff_inf : (Set.Ioo a b \ {σ : ℝ | a < σ ∧ σ < b ∧
      ¬∃ X₀ : ℕ, 1 ≤ X₀ ∧
        zetaFreeTruncationBound t j X₀ (emb σ) < ‖renormalizedCutoff t j X₀ (emb σ)‖}).Infinite :=
    hIoo_inf.sdiff hbad_fin
  refine hdiff_inf.mono ?_
  rintro σ ⟨⟨hσa, hσb⟩, hnot_bad⟩
  refine ⟨hσa, hσb, ?_⟩
  by_contra hno
  exact hnot_bad ⟨hσa, hσb, hno⟩

/-! ### Part 3: Five-point zero-repulsion cutoff lower bound -/

/-- **Five-point zero-repulsion cutoff margin law:** for any `1 < σ_* ≤ 2` and any two points
`w₁, w₂` in `1/2 < Re w ≤ 20999/24000` with `4 ≤ Im w₁` and `Im w₁ + 4 ≤ Im w₂` violating the
5-point Hadamard repulsion inequality, at least one of `w₁` or `w₂` unconditionally admits an
actual finite cutoff `X₀ ≥ 1` whose magnitude exceeds `zetaFreeTruncationBound`. -/
theorem five_point_repulsion_forces_zetaFree_margin (t : ExceptionalTime) (j : ℕ)
    {σs : ℝ} (hσ1 : 1 < σs) (hσ2 : σs ≤ 2) {w₁ w₂ : ℂ}
    (hlo₁ : 1 / 2 < w₁.re) (hhi₁ : w₁.re ≤ 20999 / 24000)
    (hlo₂ : 1 / 2 < w₂.re) (hhi₂ : w₂.re ≤ 20999 / 24000)
    (hγ₁ : 4 ≤ w₁.im) (hgap : w₁.im + 4 ≤ w₂.im)
    (hviol : 2 / (σs - 1) + Real.log w₁.im + Real.log w₂.im +
        (Real.log (w₂.im + w₁.im) + Real.log (w₂.im - w₁.im)) / 2 + 13 / 5 <
      2 / (σs - w₁.re) + 2 / (σs - w₂.re)) :
    (∃ X₀ : ℕ, 1 ≤ X₀ ∧ zetaFreeTruncationBound t j X₀ w₁ < ‖renormalizedCutoff t j X₀ w₁‖) ∨
      (∃ X₀ : ℕ, 1 ≤ X₀ ∧ zetaFreeTruncationBound t j X₀ w₂ < ‖renormalizedCutoff t j X₀ w₂‖) := by
  by_contra hboth
  have hno₁ : ¬∃ X₀ : ℕ, 1 ≤ X₀ ∧ zetaFreeTruncationBound t j X₀ w₁ < ‖renormalizedCutoff t j X₀ w₁‖ :=
    fun hex => hboth (Or.inl hex)
  have hno₂ : ¬∃ X₀ : ℕ, 1 ≤ X₀ ∧ zetaFreeTruncationBound t j X₀ w₂ < ‖renormalizedCutoff t j X₀ w₂‖ :=
    fun hex => hboth (Or.inr hex)
  have hw₁0 : 0 < w₁.re := by linarith
  have hw₁_lt1 : w₁.re < 1 := by linarith
  have hw₁_ne1 : w₁ ≠ 1 := fun he => hw₁_lt1.ne (by rw [he, Complex.one_re])
  have hw₂0 : 0 < w₂.re := by linarith
  have hw₂_lt1 : w₂.re < 1 := by linarith
  have hw₂_ne1 : w₂ ≠ 1 := fun he => hw₂_lt1.ne (by rw [he, Complex.one_re])
  have hz₁ : riemannZeta w₁ = 0 :=
    by_contra fun hne => hno₁ ((exists_zetaFree_margin_iff_zeta_ne_zero t j hw₁0 hw₁_ne1).mpr hne)
  have hz₂ : riemannZeta w₂ = 0 :=
    by_contra fun hne => hno₂ ((exists_zetaFree_margin_iff_zeta_ne_zero t j hw₂0 hw₂_ne1).mpr hne)
  let q₁ := mkXiZeroCopy hw₁0 hw₁_lt1 hz₁
  let q₂ := mkXiZeroCopy hw₂0 hw₂_lt1 hz₂
  have hrep := ExceptionalLayerTheory.two_zero_five_point_repulsion_inequality hσ1 hσ2 q₁ q₂ hγ₁ hgap
  have hfib₁ : (1 : ℝ) ≤ ((_root_.RHTower.xiZeroCopyFiber q₁.1).card : ℝ) := by
    have hmem : q₁ ∈ _root_.RHTower.xiZeroCopyFiber q₁.1 := by
      simp [_root_.RHTower.xiZeroCopyFiber]
    exact_mod_cast Finset.card_pos.mpr ⟨q₁, hmem⟩
  have hfib₂ : (1 : ℝ) ≤ ((_root_.RHTower.xiZeroCopyFiber q₂.1).card : ℝ) := by
    have hmem : q₂ ∈ _root_.RHTower.xiZeroCopyFiber q₂.1 := by
      simp [_root_.RHTower.xiZeroCopyFiber]
    exact_mod_cast Finset.card_pos.mpr ⟨q₂, hmem⟩
  have hq₁_val : (q₁.1 : ℂ) = w₁ := rfl
  have hq₂_val : (q₂.1 : ℂ) = w₂ := rfl
  rw [hq₁_val, hq₂_val] at hrep
  have hd₁ : 0 < σs - w₁.re := by linarith
  have hd₂ : 0 < σs - w₂.re := by linarith
  have hm₁ : 2 / (σs - w₁.re) ≤
      2 * ((_root_.RHTower.xiZeroCopyFiber q₁.1).card : ℝ) / (σs - w₁.re) :=
    div_le_div_of_nonneg_right (by linarith) hd₁.le
  have hm₂ : 2 / (σs - w₂.re) ≤
      2 * ((_root_.RHTower.xiZeroCopyFiber q₂.1).card : ℝ) / (σs - w₂.re) :=
    div_le_div_of_nonneg_right (by linarith) hd₂.le
  linarith

#print axioms rhVerifiedThrough_seventy
#print axioms exists_zetaFree_margin_of_abs_im_le_seventy
#print axioms rh_iff_zetaFree_margin_above_seventy
#print axioms ncard_missingZetaFreeMarginWindow_le
#print axioms exists_point_with_zetaFree_margin_of_card_gt
#print axioms infinite_zetaFree_margin_on_horizontal_interval
#print axioms five_point_repulsion_forces_zetaFree_margin

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CutoffSeparation
