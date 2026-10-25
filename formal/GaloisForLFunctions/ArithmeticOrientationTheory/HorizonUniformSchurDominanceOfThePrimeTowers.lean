import GaloisForLFunctions.ArithmeticOrientationTheory.CosetToeplitzDominanceAndShiftedPairSelectivity

/-!
# Horizon-uniform multiplicative Schur dominance of the prime towers

For a profile `q : ℕ → ℝ` supported on `[1, X]`, dropping non-singleton Cholesky squares on each
prime tower leaves an active diagonal charge of order `θ(X / n) + (1 / 2) log n`, which exceeds the
Archimedean–polar reflected-diagonal weight `archReflectedDiagWeight n ≈ n / 2` below the
square-root horizon `n ≲ 3 √X`.

This module eliminates the `√X` horizon completely by bounding the full sum of prime-tower quadratic
forms via weighted multiplicative Schur majorization across all prime powers simultaneously:

1. **Uniform prime-tower lower bound via absolute interior correlations
   (`towerOddPrimeSide_ge_neg_towerBounds`, `sum_towerOddPrimeSide_ge_neg_vonMangoldt_corr`).**
   Combining the scale-suppressed coset decomposition of `towerOddPrimeSide` (`0 ≤ 1 - p^{-i} ≤ 1`
   for `i ≥ 1`) with the coset law applied to `Function.update (fun n => |q n|) 1 0` and prime-power
   uniqueness (`sum_vonMangoldt_mul_eq_sum_towers`) yields, for **every** cutoff `X ≥ 1`, **every**
   finite set of primes `S : Finset ℕ`, and **every** profile `q` supported on `[1, X]`:
   `∑_{p ∈ S} towerOddPrimeSide q X p (K p) ≥
      -2 ∑_{m=2}^X (Λ(m) / √m) ∑_{a=2}^X |q(a)| |q(a m)| - ∑_{n=2}^X (Λ(n) / n) q(n)²`.

2. **Asymmetric multiplicative Schur decomposition (`two_mul_vonMangoldt_div_sqrt_le_schur`,
   `two_mul_sum_vonMangoldt_corr_le_schur_split`).**
   For every `m ≥ 2` and `a ≥ 1`, expanding `(Λ(m) / (m √m)) (|q(a)| - m |q(a m)|)² ≥ 0` gives
   `2 (Λ(m) / √m) |q(a)| |q(a m)| ≤ (Λ(m) / (m √m)) q(a)² + (Λ(m) √m) q(a m)²`.
   * The lower-index (`a = n`) coefficient sums to `∑_{m=2}^X Λ(m) / (m √m) ≤ 8` uniformly in `X`
     by fourth-root telescoping (`sum_Icc_vonMangoldt_div_mul_sqrt_le_eight`).
   * Reindexing `b = a m` (`a ≥ N₀`, `m ≥ 2`) restricts `m` to `{m ∈ b.divisors | 2 ≤ m ≤ b / N₀}`,
     which is empty for `b < 2 N₀` and bounded via `∑_{d ∣ b} Λ(d) = log b` by `√(b / N₀) log b`
     for `b ≥ 2 N₀` (`sum_dilated_vonMangoldt_sqrt_le_divisor_bound`).

3. **All-`X`, all-`S` global positivity on `[25, X]` and `O(1)` finite-head localization on `[1, X]`
   (`sum_towerOddPrimeSide_add_archDiag_ge_twelfth_linear_of_support_ge_25`,
    `sum_towerOddPrimeSide_add_archDiag_nonneg_of_support_ge_25`,
    `sum_towerOddPrimeSide_add_archDiag_ge_tail_sub_head_255`).**
   * For **every** `X ≥ 1`, **every** finite prime set `S`, and **every** arbitrary-sign profile `q`
     supported on `[1, X]` with `q(n) = 0` for `2 ≤ n < 25` (and arbitrary `q(1)`),
     `(∑_{p ∈ S} towerOddPrimeSide q X p (K p)) + ∑_{n=25}^X archReflectedDiagWeight n · q(n)²
        ≥ (1 / 12) ∑_{n=25}^X n · q(n)² ≥ 0`.
   * For **every** `X ≥ 1`, **every** finite prime set `S`, and **every** unrestricted profile `q`
     vanishing above `X`,
     `(∑_{p ∈ S} towerOddPrimeSide q X p (K p)) + ∑_{n=2}^X archReflectedDiagWeight n · q(n)²
        ≥ (1 / 16) ∑_{n=256}^X n · q(n)² - 106 ∑_{n=2}^{min(X, 255)} q(n)²`.
-/

open Finset ArithmeticFunction
open GaloisForLFunctions.ArithmeticIncidencePositivity

namespace GaloisForLFunctions.ArithmeticOrientationTheory

noncomputable section
set_option autoImplicit false

/-! ## §1. Elementary fourth-root, logarithmic, and telescoping inequalities -/

/-- The iterated square root `x^{1/4} = √(√x)` on `ℝ`. -/
def fourthRoot (x : ℝ) : ℝ :=
  Real.sqrt (Real.sqrt x)

theorem fourthRoot_nonneg (x : ℝ) : 0 ≤ fourthRoot x :=
  Real.sqrt_nonneg _

theorem fourthRoot_pos {x : ℝ} (hx : 0 < x) : 0 < fourthRoot x :=
  Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hx)

theorem fourthRoot_sq (x : ℝ) : fourthRoot x ^ 2 = Real.sqrt x :=
  Real.sq_sqrt (Real.sqrt_nonneg x)

theorem fourthRoot_pow_four {x : ℝ} (hx : 0 ≤ x) : fourthRoot x ^ 4 = x := by
  calc fourthRoot x ^ 4
      = (fourthRoot x ^ 2) ^ 2 := by ring
    _ = Real.sqrt x ^ 2 := by rw [fourthRoot_sq]
    _ = x := Real.sq_sqrt hx

theorem fourthRoot_mono {x y : ℝ} (hxy : x ≤ y) : fourthRoot x ≤ fourthRoot y :=
  Real.sqrt_le_sqrt (Real.sqrt_le_sqrt hxy)

theorem fourthRoot_one : fourthRoot 1 = 1 := by
  simp [fourthRoot]

theorem fourthRoot_256 : fourthRoot 256 = 4 := by
  unfold fourthRoot
  have h1 : Real.sqrt 256 = 16 := by
    rw [show (256 : ℝ) = 16 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have h2 : Real.sqrt 16 = 4 := by
    rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [h1, h2]

/-- **Universal fourth-root bound on `Real.log`:** for every `x > 0`,
`Real.log x ≤ 2 * fourthRoot x`. -/
theorem log_le_two_mul_fourthRoot {x : ℝ} (hx : 0 < x) :
    Real.log x ≤ 2 * fourthRoot x := by
  set v : ℝ := fourthRoot x with hv_def
  have hv0 : 0 < v := fourthRoot_pos hx
  have hx_eq : x = v ^ 4 := (fourthRoot_pow_four hx.le).symm
  have hlog_x : Real.log x = 4 * Real.log v := by
    rw [hx_eq, Real.log_pow]
    push_cast
    ring
  have hv_split : Real.log v = Real.log 2 + Real.log (v / 2) := by
    conv_lhs => rw [show v = 2 * (v / 2) by ring]
    exact Real.log_mul two_ne_zero (by positivity)
  have hlog_div : Real.log (v / 2) ≤ v / 2 - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have hl2 := Real.log_two_lt_d9
  linarith

/-- **Universal square-root bound on `Real.log`:** for every `x > 0`,
`Real.log x ≤ (4 / 5) * Real.sqrt x`. -/
theorem log_le_four_fifths_mul_sqrt {x : ℝ} (hx : 0 < x) :
    Real.log x ≤ (4 / 5) * Real.sqrt x := by
  set s : ℝ := Real.sqrt x with hs_def
  have hs0 : 0 < s := Real.sqrt_pos.mpr hx
  have hx_eq : x = s ^ 2 := (Real.sq_sqrt hx.le).symm
  have hlog_x : Real.log x = 2 * Real.log s := by
    rw [hx_eq, Real.log_pow]
    push_cast
    ring
  have hs_split : Real.log s = Real.log 2 + Real.log (5 / 4) + Real.log ((2 / 5) * s) := by
    conv_lhs => rw [show s = 2 * (5 / 4) * ((2 / 5) * s) by ring]
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_mul (by norm_num) (by norm_num)]
  have hlog_54 : Real.log (5 / 4) ≤ 5 / 4 - 1 :=
    Real.log_le_sub_one_of_pos (by norm_num)
  have hlog_25s : Real.log ((2 / 5) * s) ≤ (2 / 5) * s - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have hl2 := Real.log_two_lt_d9
  linarith

/-- Pointwise fourth-root telescoping bound: for every `m ≥ 2`,
`Λ m / ((m : ℝ) * Real.sqrt m) ≤ 8 * (1 / fourthRoot ((m - 1 : ℕ) : ℝ) - 1 / fourthRoot (m : ℝ))`. -/
theorem vonMangoldt_div_mul_sqrt_le_eight_mul_sub {m : ℕ} (hm : 2 ≤ m) :
    Λ m / ((m : ℝ) * Real.sqrt m) ≤
      8 * (1 / fourthRoot ((m - 1 : ℕ) : ℝ) - 1 / fourthRoot (m : ℝ)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hm1_pos : (0 : ℝ) < ((m - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < m - 1)
  set u : ℝ := fourthRoot ((m - 1 : ℕ) : ℝ) with hu_def
  set v : ℝ := fourthRoot (m : ℝ) with hv_def
  have hu0 : 0 < u := fourthRoot_pos hm1_pos
  have hv0 : 0 < v := fourthRoot_pos hm0
  have huv : u ≤ v := fourthRoot_mono (by exact_mod_cast (Nat.sub_le m 1))
  have hu4 : u ^ 4 = (m : ℝ) - 1 := by
    rw [hu_def, fourthRoot_pow_four hm1_pos.le, Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
  have hv4 : v ^ 4 = (m : ℝ) := fourthRoot_pow_four hm0.le
  have hv2 : v ^ 2 = Real.sqrt m := fourthRoot_sq (m : ℝ)
  have hdiff4 : v ^ 4 - u ^ 4 = 1 := by linarith
  have hfac : v ^ 4 - u ^ 4 = (v - u) * (v ^ 3 + v ^ 2 * u + v * u ^ 2 + u ^ 3) := by ring
  have hsum_le : v ^ 3 + v ^ 2 * u + v * u ^ 2 + u ^ 3 ≤ 4 * v ^ 3 := by
    have hnonneg : 0 ≤ (v - u) * (3 * v ^ 2 + 2 * v * u + u ^ 2) :=
      mul_nonneg (sub_nonneg.mpr huv) (by positivity)
    linarith [show 4 * v ^ 3 - (v ^ 3 + v ^ 2 * u + v * u ^ 2 + u ^ 3) =
      (v - u) * (3 * v ^ 2 + 2 * v * u + u ^ 2) by ring]
  have hone_le : 1 ≤ (v - u) * (4 * v ^ 3) := by
    calc (1 : ℝ) = v ^ 4 - u ^ 4 := hdiff4.symm
      _ = (v - u) * (v ^ 3 + v ^ 2 * u + v * u ^ 2 + u ^ 3) := hfac
      _ ≤ (v - u) * (4 * v ^ 3) := mul_le_mul_of_nonneg_left hsum_le (sub_nonneg.mpr huv)
  have hlam : Λ m ≤ 2 * v :=
    ArithmeticFunction.vonMangoldt_le_log.trans (log_le_two_mul_fourthRoot hm0)
  have hdenom : (m : ℝ) * Real.sqrt m = v ^ 6 := by
    calc (m : ℝ) * Real.sqrt m = v ^ 4 * v ^ 2 := by rw [hv4, hv2]
      _ = v ^ 6 := by ring
  have hstep1 : Λ m / ((m : ℝ) * Real.sqrt m) ≤ (2 * v) / v ^ 6 := by
    rw [hdenom]
    exact div_le_div_of_nonneg_right hlam (by positivity)
  have hstep2 : (2 * v) / v ^ 6 = 2 / v ^ 5 := by
    have hv_ne : v ≠ 0 := hv0.ne'
    field_simp
  have hstep3 : 2 / v ^ 5 ≤ 8 * (v - u) / (u * v) := by
    rw [div_le_div_iff₀ (pow_pos hv0 5) (mul_pos hu0 hv0)]
    have hmul1 : 2 * (u * v) ≤ 2 * v ^ 2 := by nlinarith
    have hmul2 : 2 * v ^ 2 ≤ 8 * (v - u) * v ^ 5 := by
      have h := mul_le_mul_of_nonneg_right hone_le (show 0 ≤ 2 * v ^ 2 by positivity)
      linarith [show (v - u) * (4 * v ^ 3) * (2 * v ^ 2) = 8 * (v - u) * v ^ 5 by ring]
    linarith
  have hstep4 : 8 * (v - u) / (u * v) = 8 * (1 / u - 1 / v) := by
    have hu_ne : u ≠ 0 := hu0.ne'
    have hv_ne : v ≠ 0 := hv0.ne'
    field_simp
  linarith

/-- Exact telescoping identity over `Icc 2 X` (`X ≥ 1`). -/
theorem sum_Icc_two_sub_succ (g : ℕ → ℝ) {X : ℕ} (hX : 1 ≤ X) :
    ∑ m ∈ Icc 2 X, (g (m - 1) - g m) = g 1 - g X := by
  induction X with
  | zero => omega
  | succ X ih =>
    rcases Nat.eq_zero_or_pos X with rfl | hXpos
    · simp
    · have hIcc : Icc 2 (X + 1) = insert (X + 1) (Icc 2 X) := by
        ext m; simp only [mem_Icc, mem_insert]; omega
      have hnot : X + 1 ∉ Icc 2 X := by simp
      rw [hIcc, sum_insert hnot, ih hXpos]
      simp only [Nat.add_sub_cancel]
      ring

/-- **Uniform convergent bound:** for **every** `X : ℕ`,
`∑ m ∈ Icc 2 X, Λ m / ((m : ℝ) * Real.sqrt m) ≤ 8`. -/
theorem sum_Icc_vonMangoldt_div_mul_sqrt_le_eight (X : ℕ) :
    ∑ m ∈ Icc 2 X, Λ m / ((m : ℝ) * Real.sqrt m) ≤ 8 := by
  rcases Nat.eq_zero_or_pos X with rfl | hX
  · simp
  · calc ∑ m ∈ Icc 2 X, Λ m / ((m : ℝ) * Real.sqrt m)
        ≤ ∑ m ∈ Icc 2 X, 8 * (1 / fourthRoot ((m - 1 : ℕ) : ℝ) - 1 / fourthRoot (m : ℝ)) :=
          sum_le_sum fun m hm => vonMangoldt_div_mul_sqrt_le_eight_mul_sub (mem_Icc.mp hm).1
      _ = 8 * ∑ m ∈ Icc 2 X, (1 / fourthRoot ((m - 1 : ℕ) : ℝ) - 1 / fourthRoot (m : ℝ)) := by
          rw [← mul_sum]
      _ = 8 * (1 / fourthRoot ((1 : ℕ) : ℝ) - 1 / fourthRoot (X : ℝ)) := by
          rw [sum_Icc_two_sub_succ (fun k => 1 / fourthRoot (k : ℝ)) hX]
      _ ≤ 8 := by
          rw [Nat.cast_one, fourthRoot_one, div_one]
          have hnonneg : 0 ≤ 1 / fourthRoot (X : ℝ) :=
            div_nonneg zero_le_one (fourthRoot_nonneg _)
          linarith

/-! ## §2. Prime-tower lower bound by absolute interior correlations -/

/-- Rewriting `(m : ℝ) ^ (-(1 / 2 : ℝ))` as `(Real.sqrt m)⁻¹`. -/
private theorem rpow_neg_half_eq_inv_sqrt (m : ℕ) :
    (m : ℝ) ^ (-(1 / 2 : ℝ)) = (Real.sqrt m)⁻¹ := by
  rw [Real.rpow_neg (Nat.cast_nonneg m), ← Real.sqrt_eq_rpow]

/-- Single-prime lower bound on `towerOddPrimeSide` in terms of the positive-profile interior
tower sums through `Nat.log p X`. -/
theorem towerOddPrimeSide_ge_neg_towerBounds (q : ℕ → ℝ) {X : ℕ} (hX : 1 ≤ X)
    (hq : ∀ n, X < n → q n = 0) {p : ℕ} (hp : p.Prime) {K : ℕ}
    (hK : ∀ i, K < i → q (p ^ i) = 0) :
    towerOddPrimeSide q X p K ≥
      -2 * (∑ k ∈ Icc 1 (Nat.log p X),
          Λ (p ^ k) * ((Real.sqrt (p ^ k : ℕ))⁻¹ * ∑ a ∈ Icc 2 X, |q a| * |q (a * p ^ k)|)) -
        ∑ i ∈ Icc 1 (Nat.log p X), Λ (p ^ i) * (((p ^ i : ℕ) : ℝ)⁻¹ * q (p ^ i) ^ 2) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hlog0 : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_le)
  set qAbs : ℕ → ℝ := Function.update (fun n => |q n|) 1 0 with hqAbs_def
  have hq_abs : ∀ n, X < n → (fun m => |q m|) n = 0 := fun n hn => by simp [hq n hn]
  have hK_abs : ∀ i, K < i → (fun m => |q m|) (p ^ i) = 0 := fun i hi => by simp [hK i hi]
  have hqAbs_supp : ∀ n, X < n → qAbs n = 0 := fun n hn => by
    rw [hqAbs_def, Function.update_of_ne (by omega)]
    simp [hq n hn]
  -- 1. Non-unit coset Toeplitz comparison against `qAbs`.
  have hnonunit : ∀ a' ∈ (pfreeLabels p X).erase 1,
      -cosetToeplitz qAbs p X (2 * K) a' ≤ cosetToeplitz q p X (2 * K) a' := by
    intro a' ha'
    rw [hqAbs_def,
      cosetToeplitz_update_one_of_ne_one (fun n => |q n|) 0 hp X (2 * K)
        (mem_of_mem_erase ha') (mem_erase.mp ha').1]
    unfold cosetToeplitz
    rw [← sum_neg_distrib]
    refine sum_le_sum fun k _ => ?_
    rw [← mul_neg, ← sum_neg_distrib]
    refine mul_le_mul_of_nonneg_left (sum_le_sum fun i _ => ?_) (by positivity)
    have habs := neg_abs_le (q (p ^ i * a') * q (p ^ (i + k) * a'))
    rwa [abs_mul] at habs
  -- 2. Scale-suppressed unit-coset comparison (`0 ≤ 1 - p^{-i} ≤ 1` for `i ≥ 1`).
  have hunit : -cosetToeplitz qAbs p X (2 * K) 1 ≤ scaleSuppressedUnitToeplitz q p K := by
    rw [hqAbs_def, cosetToeplitz_update_one_zero_unit (fun n => |q n|) hq_abs hp hK_abs]
    unfold interiorUnitToeplitz scaleSuppressedUnitToeplitz
    rw [← sum_neg_distrib]
    refine sum_le_sum fun k _ => ?_
    rw [← mul_neg, ← sum_neg_distrib]
    refine mul_le_mul_of_nonneg_left (sum_le_sum fun i hi => ?_) (by positivity)
    have hi1 : 1 ≤ i := (mem_Icc.mp hi).1
    have hpi_gt1 : (1 : ℝ) < (p : ℝ) ^ (i : ℝ) := by
      rw [Real.rpow_natCast]
      exact_mod_cast lt_of_lt_of_le hp.one_lt (Nat.le_self_pow (by omega) p)
    have hpi_inv_pos : 0 < (p : ℝ) ^ (-(i : ℝ)) := Real.rpow_pos_of_pos hp0 _
    have hpi_inv_lt1 : (p : ℝ) ^ (-(i : ℝ)) < 1 := by
      rw [Real.rpow_neg hp0.le]
      exact inv_lt_one_of_one_lt₀ hpi_gt1
    have hw0 : 0 ≤ 1 - (p : ℝ) ^ (-(i : ℝ)) := by linarith
    have hw1 : 1 - (p : ℝ) ^ (-(i : ℝ)) ≤ 1 := by linarith
    have habs : -(|q (p ^ i)| * |q (p ^ (i + k))|) ≤
        -(1 - (p : ℝ) ^ (-(i : ℝ))) * (|q (p ^ i)| * |q (p ^ (i + k))|) := by
      nlinarith [mul_nonneg (abs_nonneg (q (p ^ i))) (abs_nonneg (q (p ^ (i + k))))]
    have hsign : -(1 - (p : ℝ) ^ (-(i : ℝ))) * (|q (p ^ i)| * |q (p ^ (i + k))|) ≤
        (1 - (p : ℝ) ^ (-(i : ℝ))) * q (p ^ i) * q (p ^ (i + k)) := by
      have hprod := neg_abs_le (q (p ^ i) * q (p ^ (i + k)))
      rw [abs_mul] at hprod
      nlinarith
    linarith
  -- 3. Combine cosets into `towerRatioPart qAbs X p (2 * K)`.
  have h1mem : 1 ∈ pfreeLabels p X := by
    simp only [pfreeLabels, mem_filter, mem_Icc]
    exact ⟨⟨le_rfl, hX⟩, hp.not_dvd_one⟩
  have hcoset_sum :
      -towerRatioPart qAbs X p (2 * K) ≤
        Real.log p * (∑ a' ∈ (pfreeLabels p X).erase 1, cosetToeplitz q p X (2 * K) a' +
          scaleSuppressedUnitToeplitz q p K) := by
    rw [towerRatioPart_eq_sum_cosets qAbs hqAbs_supp hp (2 * K), ← sum_erase_add _ _ h1mem]
    have hsum_ge : -(cosetToeplitz qAbs p X (2 * K) 1 +
          ∑ a' ∈ (pfreeLabels p X).erase 1, cosetToeplitz qAbs p X (2 * K) a') ≤
        ∑ a' ∈ (pfreeLabels p X).erase 1, cosetToeplitz q p X (2 * K) a' +
          scaleSuppressedUnitToeplitz q p K := by
      have hnonunit_sum := sum_le_sum hnonunit
      rw [sum_neg_distrib] at hnonunit_sum
      linarith
    have hmul := mul_le_mul_of_nonneg_left hsum_ge hlog0
    linarith
  -- 4. Bound `towerRatioPart qAbs X p (2 * K)` by the `Icc 1 (Nat.log p X)` sum.
  have hratio_term : ∀ k : ℕ, 1 ≤ k →
      Λ (p ^ k) * ((p ^ k : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) * ratioCorr qAbs X (p ^ k) =
        Λ (p ^ k) * ((Real.sqrt (p ^ k : ℕ))⁻¹ * ∑ a ∈ Icc 2 X, |q a| * |q (a * p ^ k)|) := by
    intro k hk1
    rw [rpow_neg_half_eq_inv_sqrt, ratioCorr_eq_one_add_Icc_two qAbs hX]
    have hqAbs1 : qAbs 1 = 0 := by simp [hqAbs_def]
    rw [hqAbs1, zero_mul, zero_add]
    have hpk2 : 2 ≤ p ^ k := hp.two_le.trans (Nat.le_self_pow (by omega) p)
    have hsum_eq : ∑ a ∈ Icc 2 X, qAbs a * qAbs (a * p ^ k) =
        ∑ a ∈ Icc 2 X, |q a| * |q (a * p ^ k)| := by
      refine sum_congr rfl fun a ha => ?_
      have ha2 : 2 ≤ a := (mem_Icc.mp ha).1
      have ham2 : 2 ≤ a * p ^ k := by nlinarith
      simp only [hqAbs_def, Function.update_of_ne (by omega : a ≠ 1),
        Function.update_of_ne (by omega : a * p ^ k ≠ 1)]
    rw [hsum_eq, mul_assoc]
  have hratio_le : towerRatioPart qAbs X p (2 * K) ≤
      ∑ k ∈ Icc 1 (Nat.log p X),
        Λ (p ^ k) * ((Real.sqrt (p ^ k : ℕ))⁻¹ * ∑ a ∈ Icc 2 X, |q a| * |q (a * p ^ k)|) := by
    unfold towerRatioPart
    rw [sum_congr rfl fun k hk => hratio_term k (mem_Icc.mp hk).1]
    rcases le_or_gt (2 * K) (Nat.log p X) with hle | hgt
    · refine sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right hle) fun k _ _ => ?_
      exact mul_nonneg vonMangoldt_nonneg
        (mul_nonneg (by positivity) (sum_nonneg fun a _ => by positivity))
    · rw [sum_subset (Icc_subset_Icc_right hgt.le)]
      intro k hk hnot
      have hk_gt : Nat.log p X < k := by simp only [mem_Icc] at hk hnot; omega
      have hpk_gt : X < p ^ k :=
        lt_of_lt_of_le (Nat.lt_pow_succ_log_self hp.one_lt X) (Nat.pow_le_pow_right hp.pos hk_gt)
      have hz : ∑ a ∈ Icc 2 X, |q a| * |q (a * p ^ k)| = 0 :=
        sum_eq_zero fun a ha => by
          have ha2 : 2 ≤ a := (mem_Icc.mp ha).1
          have ham_gt : X < a * p ^ k := lt_of_lt_of_le hpk_gt (Nat.le_mul_of_pos_left _ (by omega))
          simp [hq _ ham_gt]
      rw [hz, mul_zero, mul_zero]
  -- 5. Bound the prime diagonal `Real.log p * ∑ i ∈ Icc 1 K, p^{-i} q(p^i)²` by `Icc 1 (Nat.log p X)`.
  have hdiag_le : Real.log p * ∑ i ∈ Icc 1 K, (p : ℝ) ^ (-(i : ℝ)) * q (p ^ i) ^ 2 ≤
      ∑ i ∈ Icc 1 (Nat.log p X), Λ (p ^ i) * (((p ^ i : ℕ) : ℝ)⁻¹ * q (p ^ i) ^ 2) := by
    rw [mul_sum]
    have hdiag_term : ∀ i ∈ Icc 1 K,
        Real.log p * ((p : ℝ) ^ (-(i : ℝ)) * q (p ^ i) ^ 2) =
          Λ (p ^ i) * (((p ^ i : ℕ) : ℝ)⁻¹ * q (p ^ i) ^ 2) := by
      intro i hi
      have hi1 : 1 ≤ i := (mem_Icc.mp hi).1
      rw [vonMangoldt_apply_pow (by omega), vonMangoldt_apply_prime hp,
        Real.rpow_neg hp0.le, Real.rpow_natCast, Nat.cast_pow]
    rw [sum_congr rfl hdiag_term]
    rcases le_or_gt K (Nat.log p X) with hle | hgt
    · refine sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right hle) fun i _ _ => ?_
      exact mul_nonneg vonMangoldt_nonneg (by positivity)
    · rw [sum_subset (Icc_subset_Icc_right hgt.le)]
      intro i hi hnot
      have hi_gt : Nat.log p X < i := by simp only [mem_Icc] at hi hnot; omega
      have hpi_gt : X < p ^ i :=
        lt_of_lt_of_le (Nat.lt_pow_succ_log_self hp.one_lt X) (Nat.pow_le_pow_right hp.pos hi_gt)
      simp [hq _ hpi_gt]
  -- 6. Assemble via `towerOddPrimeSide_eq_scaleSuppressed_sub_diag`.
  rw [towerOddPrimeSide_eq_scaleSuppressed_sub_diag q hX hq hp hK]
  linarith

/-- Summing a nonnegative function weighted by `Λ` over the prime towers of any finite set of
primes `S` is bounded above by the global `Icc 2 X` sum `∑ m ∈ Icc 2 X, Λ m * F m`. -/
theorem sum_primes_tower_le_sum_Icc_two {F : ℕ → ℝ} {X : ℕ} (hX : 1 ≤ X)
    (hF : ∀ m ∈ Icc 2 X, 0 ≤ F m) {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) :
    ∑ p ∈ S, ∑ k ∈ Icc 1 (Nat.log p X), Λ (p ^ k) * F (p ^ k) ≤
      ∑ m ∈ Icc 2 X, Λ m * F m := by
  have hfilter : ∑ p ∈ S, ∑ k ∈ Icc 1 (Nat.log p X), Λ (p ^ k) * F (p ^ k) =
      ∑ p ∈ S.filter (fun p => p ≤ X), ∑ k ∈ Icc 1 (Nat.log p X), Λ (p ^ k) * F (p ^ k) := by
    symm
    refine sum_subset (filter_subset _ _) fun p hp hnot => ?_
    have hpX : X < p := by simp only [mem_filter, hp, true_and, not_le] at hnot; exact hnot
    rw [Nat.log_of_lt hpX]
    simp
  have hsub : S.filter (fun p => p ≤ X) ⊆ (Icc 1 X).filter Nat.Prime := by
    intro p hp
    simp only [mem_filter, mem_Icc] at hp ⊢
    exact ⟨⟨(hS p hp.1).one_le, hp.2⟩, hS p hp.1⟩
  have hnonneg : ∀ p ∈ (Icc 1 X).filter Nat.Prime, p ∉ S.filter (fun p => p ≤ X) →
      0 ≤ ∑ k ∈ Icc 1 (Nat.log p X), Λ (p ^ k) * F (p ^ k) := by
    intro p hp _
    have hpP : p.Prime := (mem_filter.mp hp).2
    refine sum_nonneg fun k hk => mul_nonneg vonMangoldt_nonneg (hF (p ^ k) ?_)
    simp only [mem_Icc] at hk ⊢
    exact ⟨hpP.two_le.trans (Nat.le_self_pow (by omega) p),
      Nat.pow_le_of_le_log (by omega : X ≠ 0) hk.2⟩
  have hIcc1 : ∑ m ∈ Icc 1 X, Λ m * F m = ∑ m ∈ Icc 2 X, Λ m * F m := by
    have hsplit : Icc 1 X = insert 1 (Icc 2 X) := by
      ext m; simp only [mem_Icc, mem_insert]; omega
    have hnot1 : (1 : ℕ) ∉ Icc 2 X := by simp
    rw [hsplit, sum_insert hnot1, vonMangoldt_apply_one, zero_mul, zero_add]
  calc ∑ p ∈ S, ∑ k ∈ Icc 1 (Nat.log p X), Λ (p ^ k) * F (p ^ k)
      = ∑ p ∈ S.filter (fun p => p ≤ X), ∑ k ∈ Icc 1 (Nat.log p X), Λ (p ^ k) * F (p ^ k) :=
        hfilter
    _ ≤ ∑ p ∈ (Icc 1 X).filter Nat.Prime, ∑ k ∈ Icc 1 (Nat.log p X), Λ (p ^ k) * F (p ^ k) :=
        sum_le_sum_of_subset_of_nonneg hsub hnonneg
    _ = ∑ m ∈ Icc 1 X, Λ m * F m := (sum_vonMangoldt_mul_eq_sum_towers F X).symm
    _ = ∑ m ∈ Icc 2 X, Λ m * F m := hIcc1

/-- **Global `S`-independent prime-tower lower bound (`sum_towerOddPrimeSide_ge_neg_vonMangoldt_corr`):**
for **every** `X ≥ 1`, **every** finite set of primes `S : Finset ℕ` (with zero upper bound on
`max S`), and **every** profile `q` supported on `[1, X]`, summing `towerOddPrimeSide` over `p ∈ S`
is bounded below by the negative absolute von Mangoldt ratio correlation and prime-power diagonal. -/
theorem sum_towerOddPrimeSide_ge_neg_vonMangoldt_corr (q : ℕ → ℝ) {X : ℕ} (hX : 1 ≤ X)
    (hq : ∀ n, X < n → q n = 0) {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime)
    (K : ℕ → ℕ) (hK : ∀ p ∈ S, ∀ i, K p < i → q (p ^ i) = 0) :
    ∑ p ∈ S, towerOddPrimeSide q X p (K p) ≥
      -2 * ∑ m ∈ Icc 2 X, (Λ m / Real.sqrt m) * (∑ a ∈ Icc 2 X, |q a| * |q (a * m)|) -
        ∑ n ∈ Icc 2 X, (Λ n / (n : ℝ)) * q n ^ 2 := by
  have hp_each : ∀ p ∈ S,
      -2 * (∑ k ∈ Icc 1 (Nat.log p X),
          Λ (p ^ k) * ((Real.sqrt (p ^ k : ℕ))⁻¹ * ∑ a ∈ Icc 2 X, |q a| * |q (a * p ^ k)|)) -
        (∑ i ∈ Icc 1 (Nat.log p X), Λ (p ^ i) * (((p ^ i : ℕ) : ℝ)⁻¹ * q (p ^ i) ^ 2)) ≤
      towerOddPrimeSide q X p (K p) :=
    fun p hp => towerOddPrimeSide_ge_neg_towerBounds q hX hq (hS p hp) (hK p hp)
  have hsum_p := sum_le_sum hp_each
  rw [sum_sub_distrib, ← mul_sum] at hsum_p
  have hF1 := sum_primes_tower_le_sum_Icc_two
    (F := fun m => (Real.sqrt m)⁻¹ * ∑ a ∈ Icc 2 X, |q a| * |q (a * m)|) hX
    (fun m _ => mul_nonneg (by positivity) (sum_nonneg fun a _ => by positivity)) hS
  have hF2 := sum_primes_tower_le_sum_Icc_two
    (F := fun m => (m : ℝ)⁻¹ * q m ^ 2) hX
    (fun m _ => by positivity) hS
  have hF1_eq : ∑ m ∈ Icc 2 X, Λ m * ((Real.sqrt m)⁻¹ * ∑ a ∈ Icc 2 X, |q a| * |q (a * m)|) =
      ∑ m ∈ Icc 2 X, (Λ m / Real.sqrt m) * ∑ a ∈ Icc 2 X, |q a| * |q (a * m)| :=
    sum_congr rfl fun m _ => by rw [div_eq_mul_inv, mul_assoc]
  have hF2_eq : ∑ n ∈ Icc 2 X, Λ n * ((n : ℝ)⁻¹ * q n ^ 2) =
      ∑ n ∈ Icc 2 X, (Λ n / (n : ℝ)) * q n ^ 2 :=
    sum_congr rfl fun n _ => by rw [div_eq_mul_inv, mul_assoc]
  linarith

/-! ## §3. Asymmetric multiplicative Schur decomposition and divisor reindexing -/

/-- **Weighted multiplicative Schur inequality:** for every `m ≥ 1` and `x, y : ℝ`,
`2 * (Λ m / Real.sqrt m) * (x * y) ≤
  (Λ m / ((m : ℝ) * Real.sqrt m)) * x ^ 2 + (Λ m * Real.sqrt m) * y ^ 2`. -/
theorem two_mul_vonMangoldt_div_sqrt_le_schur {m : ℕ} (hm : 1 ≤ m) (x y : ℝ) :
    2 * (Λ m / Real.sqrt m) * (x * y) ≤
      (Λ m / ((m : ℝ) * Real.sqrt m)) * x ^ 2 + (Λ m * Real.sqrt m) * y ^ 2 := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  set s : ℝ := Real.sqrt m with hs_def
  have hs0 : 0 < s := Real.sqrt_pos.mpr hm0
  have hs2 : s * s = (m : ℝ) := Real.mul_self_sqrt hm0.le
  rw [← hs2]
  have hnonneg : 0 ≤ (Λ m / ((s * s) * s)) * (x - (s * s) * y) ^ 2 :=
    mul_nonneg (div_nonneg vonMangoldt_nonneg (by positivity)) (sq_nonneg _)
  have hid :
      (Λ m / ((s * s) * s)) * x ^ 2 + (Λ m * s) * y ^ 2 - 2 * (Λ m / s) * (x * y) =
        (Λ m / ((s * s) * s)) * (x - (s * s) * y) ^ 2 := by
    have hs_ne : s ≠ 0 := hs0.ne'
    field_simp
    ring
  linarith

/-- **Divisor reindexing bound for dilated squares:** for any `N₀ ≥ 2`, `X : ℕ`, and profile `q`
vanishing above `X`, reindexing `b = a * m` (`m ∈ Icc 2 X`, `a ∈ Icc N₀ X`) bounds the dilated
square sum by `∑ b ∈ Icc (2 * N₀) X, (Real.sqrt ((b : ℝ) / N₀) * Real.log b) * q b ^ 2`. -/
theorem sum_dilated_vonMangoldt_sqrt_le_divisor_bound (q : ℕ → ℝ) {N₀ X : ℕ} (hN₀ : 2 ≤ N₀)
    (hq : ∀ n, X < n → q n = 0) :
    ∑ m ∈ Icc 2 X, ∑ a ∈ Icc N₀ X, (Λ m * Real.sqrt m) * q (a * m) ^ 2 ≤
      ∑ b ∈ Icc (2 * N₀) X, (Real.sqrt ((b : ℝ) / (N₀ : ℝ)) * Real.log b) * q b ^ 2 := by
  have hN0_pos : 0 < N₀ := by omega
  have hN0_real : (0 : ℝ) < N₀ := by exact_mod_cast hN0_pos
  -- Restrict to pairs `(m, a)` with `a * m ≤ X` since `q (a * m) = 0` for `a * m > X`.
  set P := (Icc 2 X ×ˢ Icc N₀ X).filter (fun p : ℕ × ℕ => p.2 * p.1 ≤ X) with hP_def
  have hprod_eq : ∑ m ∈ Icc 2 X, ∑ a ∈ Icc N₀ X, (Λ m * Real.sqrt m) * q (a * m) ^ 2 =
      ∑ p ∈ P, (Λ p.1 * Real.sqrt p.1) * q (p.2 * p.1) ^ 2 := by
    rw [← sum_product']
    symm
    refine sum_subset (filter_subset _ _) fun p hp hnot => ?_
    have hgt : X < p.2 * p.1 := by simp only [hP_def, mem_filter, hp, true_and, not_le] at hnot; exact hnot
    simp [hq _ hgt]
  rw [hprod_eq]
  have hmaps : ∀ p ∈ P, p.2 * p.1 ∈ Icc (2 * N₀) X := by
    intro p hp
    simp only [hP_def, mem_filter, mem_product, mem_Icc] at hp ⊢
    exact ⟨by nlinarith [hp.1.1.1, hp.1.2.1], hp.2⟩
  rw [← sum_fiberwise_of_maps_to hmaps]
  refine sum_le_sum fun b hb => ?_
  have hb_min : 2 * N₀ ≤ b := (mem_Icc.mp hb).1
  have hb_pos : 0 < b := by omega
  -- On the fiber `{p ∈ P | p.2 * p.1 = b}`, `p.2 * p.1` is constant `b` and `p ↦ p.1` is injective
  -- into `b.divisors.filter (fun m => 2 ≤ m ∧ m ≤ b / N₀)`.
  set Fb := P.filter (fun p => p.2 * p.1 = b) with hFb_def
  set Db := b.divisors.filter (fun m => 2 ≤ m ∧ m ≤ b / N₀) with hDb_def
  have hcongr_b : ∑ p ∈ Fb, (Λ p.1 * Real.sqrt p.1) * q (p.2 * p.1) ^ 2 =
      (∑ p ∈ Fb, Λ p.1 * Real.sqrt p.1) * q b ^ 2 := by
    rw [sum_mul]
    refine sum_congr rfl fun p hp => ?_
    rw [(mem_filter.mp hp).2]
  rw [hcongr_b]
  refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  have hinj : ∀ p₁ ∈ Fb, ∀ p₂ ∈ Fb, p₁.1 = p₂.1 → p₁ = p₂ := by
    intro p₁ hp₁ p₂ hp₂ hm
    have hm2 : 2 ≤ p₁.1 := (mem_Icc.mp (mem_product.mp (mem_filter.mp (mem_filter.mp hp₁).1).1).1).1
    have heq1 : p₁.2 * p₁.1 = b := (mem_filter.mp hp₁).2
    have heq2 : p₂.2 * p₁.1 = b := by rw [hm]; exact (mem_filter.mp hp₂).2
    have ha : p₁.2 = p₂.2 := Nat.eq_of_mul_eq_mul_right (by omega : 0 < p₁.1) (heq1.trans heq2.symm)
    exact Prod.ext hm ha
  have himg_sub : Fb.image Prod.fst ⊆ Db := by
    intro m hm
    rcases mem_image.mp hm with ⟨⟨m', a⟩, hp, rfl⟩
    have hpP := (mem_filter.mp hp).1
    have hab : a * m' = b := (mem_filter.mp hp).2
    have hm2 : 2 ≤ m' := (mem_Icc.mp (mem_product.mp (mem_filter.mp hpP).1).1).1
    have haN : N₀ ≤ a := (mem_Icc.mp (mem_product.mp (mem_filter.mp hpP).1).2).1
    simp only [hDb_def, mem_filter, Nat.mem_divisors]
    refine ⟨⟨⟨a, by rw [mul_comm, hab]⟩, by omega⟩, hm2, ?_⟩
    exact (Nat.le_div_iff_mul_le hN0_pos).mpr (by nlinarith)
  have hstep1 : ∑ p ∈ Fb, Λ p.1 * Real.sqrt p.1 ≤ ∑ m ∈ Db, Λ m * Real.sqrt m := by
    rw [← sum_image (f := fun m : ℕ => Λ m * Real.sqrt m) hinj]
    exact sum_le_sum_of_subset_of_nonneg himg_sub fun m _ _ =>
      mul_nonneg vonMangoldt_nonneg (Real.sqrt_nonneg _)
  have hstep2 : ∑ m ∈ Db, Λ m * Real.sqrt m ≤
      (∑ m ∈ Db, Λ m) * Real.sqrt ((b : ℝ) / (N₀ : ℝ)) := by
    rw [sum_mul]
    refine sum_le_sum fun m hm => ?_
    have hm_le : m ≤ b / N₀ := (mem_filter.mp hm).2.2
    have hm_mul : (m : ℝ) * (N₀ : ℝ) ≤ (b : ℝ) := by
      exact_mod_cast (Nat.le_div_iff_mul_le hN0_pos).mp hm_le
    have hm_div : (m : ℝ) ≤ (b : ℝ) / (N₀ : ℝ) := (le_div_iff₀ hN0_real).mpr hm_mul
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hm_div) vonMangoldt_nonneg
  have hstep3 : ∑ m ∈ Db, Λ m ≤ Real.log b := by
    rw [← ArithmeticFunction.vonMangoldt_sum]
    exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => vonMangoldt_nonneg
  calc ∑ p ∈ Fb, Λ p.1 * Real.sqrt p.1
      ≤ ∑ m ∈ Db, Λ m * Real.sqrt m := hstep1
    _ ≤ (∑ m ∈ Db, Λ m) * Real.sqrt ((b : ℝ) / (N₀ : ℝ)) := hstep2
    _ ≤ Real.log b * Real.sqrt ((b : ℝ) / (N₀ : ℝ)) :=
        mul_le_mul_of_nonneg_right hstep3 (Real.sqrt_nonneg _)
    _ = Real.sqrt ((b : ℝ) / (N₀ : ℝ)) * Real.log b := mul_comm _ _

/-- **Combined Schur + telescoping + divisor bound on the von Mangoldt ratio correlation:**
for any `N₀ ≥ 2`, `X : ℕ`, and profile `q` vanishing on `[2, N₀ - 1]` and `(X, ∞)`,
`2 * ∑ m ∈ Icc 2 X, (Λ m / Real.sqrt m) * ∑ a ∈ Icc 2 X, |q a| * |q (a * m)| ≤
  8 * ∑ n ∈ Icc N₀ X, q n ^ 2 +
  ∑ n ∈ Icc (2 * N₀) X, (Real.sqrt ((n : ℝ) / N₀) * Real.log n) * q n ^ 2`. -/
theorem two_mul_sum_vonMangoldt_corr_le_schur_split (q : ℕ → ℝ) {N₀ X : ℕ} (hN₀ : 2 ≤ N₀)
    (hq : ∀ n, X < n → q n = 0) (hq_low : ∀ n, 2 ≤ n → n < N₀ → q n = 0) :
    2 * ∑ m ∈ Icc 2 X, (Λ m / Real.sqrt m) * (∑ a ∈ Icc 2 X, |q a| * |q (a * m)|) ≤
      8 * ∑ n ∈ Icc N₀ X, q n ^ 2 +
        ∑ n ∈ Icc (2 * N₀) X, (Real.sqrt ((n : ℝ) / (N₀ : ℝ)) * Real.log n) * q n ^ 2 := by
  -- Restrict inner sum from `Icc 2 X` to `Icc N₀ X`.
  have hinner_eq : ∀ m : ℕ,
      ∑ a ∈ Icc 2 X, |q a| * |q (a * m)| = ∑ a ∈ Icc N₀ X, |q a| * |q (a * m)| := by
    intro m
    symm
    refine sum_subset (Icc_subset_Icc_left hN₀) fun a ha hnot => ?_
    have ha2 : 2 ≤ a := (mem_Icc.mp ha).1
    have haX : a ≤ X := (mem_Icc.mp ha).2
    have haN : a < N₀ := by simp only [mem_Icc, haX, and_true, not_le] at hnot; exact hnot
    simp [hq_low a ha2 haN]
  have h1 : 2 * ∑ m ∈ Icc 2 X, (Λ m / Real.sqrt m) * (∑ a ∈ Icc 2 X, |q a| * |q (a * m)|) =
      ∑ m ∈ Icc 2 X, ∑ a ∈ Icc N₀ X, 2 * (Λ m / Real.sqrt m) * (|q a| * |q (a * m)|) := by
    rw [mul_sum]
    refine sum_congr rfl fun m _ => ?_
    rw [hinner_eq m, mul_sum, mul_sum]
    refine sum_congr rfl fun a _ => ?_
    ring
  rw [h1]
  have hschur : ∑ m ∈ Icc 2 X, ∑ a ∈ Icc N₀ X, 2 * (Λ m / Real.sqrt m) * (|q a| * |q (a * m)|) ≤
      (∑ m ∈ Icc 2 X, Λ m / ((m : ℝ) * Real.sqrt m)) * (∑ a ∈ Icc N₀ X, q a ^ 2) +
        ∑ m ∈ Icc 2 X, ∑ a ∈ Icc N₀ X, (Λ m * Real.sqrt m) * q (a * m) ^ 2 := by
    have hpt : ∀ m ∈ Icc 2 X,
        ∑ a ∈ Icc N₀ X, 2 * (Λ m / Real.sqrt m) * (|q a| * |q (a * m)|) ≤
          (Λ m / ((m : ℝ) * Real.sqrt m)) * (∑ a ∈ Icc N₀ X, q a ^ 2) +
            ∑ a ∈ Icc N₀ X, (Λ m * Real.sqrt m) * q (a * m) ^ 2 := by
      intro m hm
      have hm1 : 1 ≤ m := le_trans (by omega) (mem_Icc.mp hm).1
      rw [mul_sum, ← sum_add_distrib]
      refine sum_le_sum fun a _ => ?_
      have h := two_mul_vonMangoldt_div_sqrt_le_schur hm1 |q a| |q (a * m)|
      rwa [sq_abs, sq_abs] at h
    calc ∑ m ∈ Icc 2 X, ∑ a ∈ Icc N₀ X, 2 * (Λ m / Real.sqrt m) * (|q a| * |q (a * m)|)
        ≤ ∑ m ∈ Icc 2 X, ((Λ m / ((m : ℝ) * Real.sqrt m)) * (∑ a ∈ Icc N₀ X, q a ^ 2) +
            ∑ a ∈ Icc N₀ X, (Λ m * Real.sqrt m) * q (a * m) ^ 2) := sum_le_sum hpt
      _ = (∑ m ∈ Icc 2 X, Λ m / ((m : ℝ) * Real.sqrt m)) * (∑ a ∈ Icc N₀ X, q a ^ 2) +
            ∑ m ∈ Icc 2 X, ∑ a ∈ Icc N₀ X, (Λ m * Real.sqrt m) * q (a * m) ^ 2 := by
          rw [sum_add_distrib, ← sum_mul]
  have h8 : (∑ m ∈ Icc 2 X, Λ m / ((m : ℝ) * Real.sqrt m)) * (∑ a ∈ Icc N₀ X, q a ^ 2) ≤
      8 * ∑ a ∈ Icc N₀ X, q a ^ 2 :=
    mul_le_mul_of_nonneg_right (sum_Icc_vonMangoldt_div_mul_sqrt_le_eight X)
      (sum_nonneg fun _ _ => sq_nonneg _)
  have hdiv := sum_dilated_vonMangoldt_sqrt_le_divisor_bound q hN₀ hq
  linarith

/-! ## §4. Sharp rational lower bounds on `archReflectedDiagWeight` and horizon-uniform dominance -/

/-- **Sharp asymptotic lower bound on `archReflectedDiagWeight`:** for every integer `n ≥ 3`,
`(n : ℝ) / 2 - 6 / 5 < archReflectedDiagWeight n`. -/
theorem half_sub_six_fifths_lt_archReflectedDiagWeight {n : ℕ} (hn : 3 ≤ n) :
    (n : ℝ) / 2 - 6 / 5 < archReflectedDiagWeight n := by
  rw [archReflectedDiagWeight_eq (by omega)]
  set x : ℝ := (n : ℝ) with hx_def
  have hx3 : 3 ≤ x := by rw [hx_def]; exact_mod_cast hn
  have hx4_gt1 : 1 < x ^ 4 := by
    have h2 : 9 ≤ x ^ 2 := by nlinarith
    nlinarith
  have hden : 0 < 2 * x * (x ^ 4 - 1) := by nlinarith
  have hrewrite : x / 2 - 6 / 5 = (5 * x - 12) / 10 := by ring
  rw [hrewrite, div_lt_div_iff₀ (by norm_num) hden]
  have hid :
      ((x - 1) ^ 2 * (x ^ 4 - 1) - 2 * x ^ 4) * 10 - (5 * x - 12) * (2 * x * (x ^ 4 - 1)) =
        2 * ((x - 3) * (2 * x ^ 4 + x ^ 3 + 3 * x ^ 2 + 9 * x + 25) + 70) := by ring
  have hpos : 0 < 2 * x ^ 4 + x ^ 3 + 3 * x ^ 2 + 9 * x + 25 := by positivity
  have hnonneg : 0 ≤ (x - 3) * (2 * x ^ 4 + x ^ 3 + 3 * x ^ 2 + 9 * x + 25) :=
    mul_nonneg (by linarith) hpos.le
  linarith

/-- For every integer `n ≥ 2`, `-1 ≤ archReflectedDiagWeight n`. -/
theorem neg_one_le_archReflectedDiagWeight {n : ℕ} (hn : 2 ≤ n) :
    -1 ≤ archReflectedDiagWeight n := by
  rcases eq_or_lt_of_le hn with rfl | hn3
  · rw [archReflectedDiagWeight_eq (by omega)]
    norm_num
  · have h := half_sub_six_fifths_lt_archReflectedDiagWeight (by omega : 3 ≤ n)
    have hn3' : (3 : ℝ) ≤ n := by exact_mod_cast hn3
    linarith

/-- Splitting an `Icc a X` sum at an arbitrary threshold `M` (`a ≤ M + 1`), uniformly in `X : ℕ`. -/
theorem sum_Icc_split_at (f : ℕ → ℝ) {a M X : ℕ} (haM : a ≤ M + 1) :
    ∑ n ∈ Icc a X, f n = ∑ n ∈ Icc a (min X M), f n + ∑ n ∈ Icc (M + 1) X, f n := by
  rcases le_or_gt X M with hXM | hMX
  · have hemp : Icc (M + 1) X = ∅ := Icc_eq_empty (by omega)
    rw [min_eq_left hXM, hemp, sum_empty, add_zero]
  · rw [min_eq_right hMX.le]
    have hunion : Icc a X = Icc a M ∪ Icc (M + 1) X := by
      ext n; simp only [mem_Icc, mem_union]; omega
    have hdisj : Disjoint (Icc a M) (Icc (M + 1) X) := by
      rw [disjoint_left]
      intro n hn1 hn2
      simp only [mem_Icc] at hn1 hn2
      omega
    rw [hunion, sum_union hdisj]

/-- **All-`X`, all-`S` linear coercivity on `[25, X]`
(`sum_towerOddPrimeSide_add_archDiag_ge_twelfth_linear_of_support_ge_25`):**
for **every** `X ≥ 1`, **every** finite set of primes `S : Finset ℕ`, and **every** profile
`q : ℕ → ℝ` of **arbitrary sign** supported on `[1, X]` with `q n = 0` for `2 ≤ n < 25` (and
arbitrary `q 1`), the Archimedean–polar reflected diagonal dominates all prime towers
simultaneously with linear coercivity `(1 / 12) ∑_{n=25}^X n · q(n)²`. -/
theorem sum_towerOddPrimeSide_add_archDiag_ge_twelfth_linear_of_support_ge_25
    (q : ℕ → ℝ) {X : ℕ} (hX : 1 ≤ X) (hq : ∀ n, X < n → q n = 0)
    (hq25 : ∀ n, 2 ≤ n → n < 25 → q n = 0)
    {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime)
    (K : ℕ → ℕ) (hK : ∀ p ∈ S, ∀ i, K p < i → q (p ^ i) = 0) :
    (∑ p ∈ S, towerOddPrimeSide q X p (K p)) +
      ∑ n ∈ Icc 25 X, archReflectedDiagWeight n * q n ^ 2 ≥
        (1 / 12) * ∑ n ∈ Icc 25 X, (n : ℝ) * q n ^ 2 := by
  have hbase := sum_towerOddPrimeSide_ge_neg_vonMangoldt_corr q hX hq hS K hK
  have hschur := two_mul_sum_vonMangoldt_corr_le_schur_split q (by omega : 2 ≤ 25) hq hq25
  -- Restrict the prime diagonal from `Icc 2 X` to `Icc 25 X`.
  have hdiag_eq : ∑ n ∈ Icc 2 X, (Λ n / (n : ℝ)) * q n ^ 2 =
      ∑ n ∈ Icc 25 X, (Λ n / (n : ℝ)) * q n ^ 2 := by
    symm
    refine sum_subset (Icc_subset_Icc_left (by omega)) fun n hn hnot => ?_
    have hn2 : 2 ≤ n := (mem_Icc.mp hn).1
    have hnX : n ≤ X := (mem_Icc.mp hn).2
    have hn25 : n < 25 := by simp only [mem_Icc, hnX, and_true, not_le] at hnot; exact hnot
    simp [hq25 n hn2 hn25]
  -- Pointwise prime diagonal bound `Λ n / n ≤ 4 / 25` for `n ≥ 25`.
  have hlam_25 : ∀ n : ℕ, 25 ≤ n → Λ n / (n : ℝ) ≤ 4 / 25 := by
    intro n hn25
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hn25' : (25 : ℝ) ≤ n := by exact_mod_cast hn25
    have hsqrt5 : 5 ≤ Real.sqrt n := by
      rw [show (5 : ℝ) = Real.sqrt 25 by rw [show (25 : ℝ) = 5 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt hn25'
    have hlam : Λ n ≤ (4 / 5) * Real.sqrt n :=
      ArithmeticFunction.vonMangoldt_le_log.trans (log_le_four_fifths_mul_sqrt hn0)
    have h1 : Λ n / (n : ℝ) ≤ ((4 / 5) * Real.sqrt n) / (Real.sqrt n * Real.sqrt n) := by
      rw [Real.mul_self_sqrt hn0.le]
      exact div_le_div_of_nonneg_right hlam hn0.le
    have hsqrt_ne : Real.sqrt n ≠ 0 := (Real.sqrt_pos.mpr hn0).ne'
    have h2 : ((4 / 5) * Real.sqrt n) / (Real.sqrt n * Real.sqrt n) = (4 / 5) / Real.sqrt n := by
      field_simp
    have h3 : (4 / 5) / Real.sqrt n ≤ (4 / 5) / 5 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hsqrt5
    linarith
  have hdiag_bound : ∑ n ∈ Icc 25 X, (Λ n / (n : ℝ)) * q n ^ 2 ≤
      (4 / 25) * ∑ n ∈ Icc 25 X, q n ^ 2 := by
    rw [mul_sum]
    exact sum_le_sum fun n hn =>
      mul_le_mul_of_nonneg_right (hlam_25 n (mem_Icc.mp hn).1) (sq_nonneg _)
  -- Pointwise dilated divisor bound `√(n / 25) log n ≤ (4 / 25) n` for `n ≥ 50`.
  have hdiv_bound : ∑ n ∈ Icc (2 * 25) X,
        (Real.sqrt ((n : ℝ) / (25 : ℝ)) * Real.log n) * q n ^ 2 ≤
      ∑ n ∈ Icc 50 X, ((4 / 25) * (n : ℝ)) * q n ^ 2 := by
    refine sum_le_sum fun n hn => mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    have hn50 : 50 ≤ n := (mem_Icc.mp hn).1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hsq25 : Real.sqrt ((n : ℝ) / 25) = Real.sqrt n / 5 := by
      rw [Real.sqrt_div hn0.le, show (25 : ℝ) = 5 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [hsq25]
    calc (Real.sqrt n / 5) * Real.log n
        ≤ (Real.sqrt n / 5) * ((4 / 5) * Real.sqrt n) :=
          mul_le_mul_of_nonneg_left (log_le_four_fifths_mul_sqrt hn0) (by positivity)
      _ = (4 / 25) * (Real.sqrt n * Real.sqrt n) := by ring
      _ = (4 / 25) * (n : ℝ) := by rw [Real.mul_self_sqrt hn0.le]
  -- Split `Icc 25 X` at `49` (`25..min X 49` and `50..X`) and compare coefficients pointwise.
  have hsplit_arch := sum_Icc_split_at (fun n => archReflectedDiagWeight n * q n ^ 2)
    (a := 25) (M := 49) (X := X) (by omega)
  have hsplit_sq := sum_Icc_split_at (fun n => q n ^ 2)
    (a := 25) (M := 49) (X := X) (by omega)
  have hsplit_lin := sum_Icc_split_at (fun n => (n : ℝ) * q n ^ 2)
    (a := 25) (M := 49) (X := X) (by omega)
  have hband_low :
      (1 / 12) * ∑ n ∈ Icc 25 (min X 49), (n : ℝ) * q n ^ 2 ≤
        ∑ n ∈ Icc 25 (min X 49), archReflectedDiagWeight n * q n ^ 2 -
          (8 + 4 / 25) * ∑ n ∈ Icc 25 (min X 49), q n ^ 2 := by
    rw [mul_sum, mul_sum, ← sum_sub_distrib]
    refine sum_le_sum fun n hn => ?_
    have hn25 : 25 ≤ n := (mem_Icc.mp hn).1
    have hn25' : (25 : ℝ) ≤ n := by exact_mod_cast hn25
    have harch := half_sub_six_fifths_lt_archReflectedDiagWeight (by omega : 3 ≤ n)
    have hcoef : (1 / 12 : ℝ) * (n : ℝ) ≤ archReflectedDiagWeight n - (8 + 4 / 25) := by linarith
    nlinarith [sq_nonneg (q n)]
  have hband_high :
      (1 / 12) * ∑ n ∈ Icc 50 X, (n : ℝ) * q n ^ 2 ≤
        ∑ n ∈ Icc 50 X, archReflectedDiagWeight n * q n ^ 2 -
          (8 + 4 / 25) * ∑ n ∈ Icc 50 X, q n ^ 2 -
          ∑ n ∈ Icc 50 X, ((4 / 25) * (n : ℝ)) * q n ^ 2 := by
    rw [mul_sum, mul_sum, ← sum_sub_distrib, ← sum_sub_distrib]
    refine sum_le_sum fun n hn => ?_
    have hn50 : 50 ≤ n := (mem_Icc.mp hn).1
    have hn50' : (50 : ℝ) ≤ n := by exact_mod_cast hn50
    have harch := half_sub_six_fifths_lt_archReflectedDiagWeight (by omega : 3 ≤ n)
    have hcoef : (1 / 12 : ℝ) * (n : ℝ) ≤
        archReflectedDiagWeight n - (8 + 4 / 25) - (4 / 25) * (n : ℝ) := by linarith
    nlinarith [sq_nonneg (q n)]
  linarith

/-- **Global nonnegativity on `[25, X]` (`sum_towerOddPrimeSide_add_archDiag_nonneg_of_support_ge_25`):**
for **every** `X ≥ 1`, **every** finite prime set `S`, and **every** arbitrary-sign profile `q`
supported on `[1, X]` with `q n = 0` for `2 ≤ n < 25` (and arbitrary `q 1`),
`0 ≤ (∑ p ∈ S, towerOddPrimeSide q X p (K p)) + ∑ n ∈ Icc 25 X, archReflectedDiagWeight n * q n ^ 2`. -/
theorem sum_towerOddPrimeSide_add_archDiag_nonneg_of_support_ge_25
    (q : ℕ → ℝ) {X : ℕ} (hX : 1 ≤ X) (hq : ∀ n, X < n → q n = 0)
    (hq25 : ∀ n, 2 ≤ n → n < 25 → q n = 0)
    {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime)
    (K : ℕ → ℕ) (hK : ∀ p ∈ S, ∀ i, K p < i → q (p ^ i) = 0) :
    0 ≤ (∑ p ∈ S, towerOddPrimeSide q X p (K p)) +
      ∑ n ∈ Icc 25 X, archReflectedDiagWeight n * q n ^ 2 := by
  have hcoercive :=
    sum_towerOddPrimeSide_add_archDiag_ge_twelfth_linear_of_support_ge_25 q hX hq hq25 hS K hK
  have hlin_nonneg : 0 ≤ (1 / 12 : ℝ) * ∑ n ∈ Icc 25 X, (n : ℝ) * q n ^ 2 :=
    mul_nonneg (by norm_num) (sum_nonneg fun n _ => by positivity)
  linarith

/-- **Horizon-uniform `O(1)` finite-head localization on unrestricted `[1, X]`
(`sum_towerOddPrimeSide_add_archDiag_ge_tail_sub_head_255`):**
for **every** `X ≥ 1`, **every** finite set of primes `S : Finset ℕ`, and **every** unrestricted
profile `q : ℕ → ℝ` vanishing above `X` (with arbitrary values on `[1, X]`), the Archimedean–polar
reflected diagonal plus all prime towers in `S` dominates `(1 / 16) ∑_{n=256}^X n · q(n)²` up to
a bounded `O(1)` finite-head quadratic form `-106 ∑_{n=2}^{min(X, 255)} q(n)²` independent of `X`
and `S`. -/
theorem sum_towerOddPrimeSide_add_archDiag_ge_tail_sub_head_255
    (q : ℕ → ℝ) {X : ℕ} (hX : 1 ≤ X) (hq : ∀ n, X < n → q n = 0)
    {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime)
    (K : ℕ → ℕ) (hK : ∀ p ∈ S, ∀ i, K p < i → q (p ^ i) = 0) :
    (∑ p ∈ S, towerOddPrimeSide q X p (K p)) +
      ∑ n ∈ Icc 2 X, archReflectedDiagWeight n * q n ^ 2 ≥
        (1 / 16) * ∑ n ∈ Icc 256 X, (n : ℝ) * q n ^ 2 -
          106 * ∑ n ∈ Icc 2 (min X 255), q n ^ 2 := by
  have hbase := sum_towerOddPrimeSide_ge_neg_vonMangoldt_corr q hX hq hS K hK
  have hschur := two_mul_sum_vonMangoldt_corr_le_schur_split q (le_rfl : 2 ≤ 2) hq
    (fun _ h1 h2 => by omega)
  -- 1. Prime diagonal bound `Λ n / n ≤ 1` for all `n ≥ 2`.
  have hdiag_le : ∑ n ∈ Icc 2 X, (Λ n / (n : ℝ)) * q n ^ 2 ≤ ∑ n ∈ Icc 2 X, q n ^ 2 := by
    refine sum_le_sum fun n hn => ?_
    have hn2 : 2 ≤ n := (mem_Icc.mp hn).1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hn2' : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    have hlam : Λ n ≤ (4 / 5) * Real.sqrt n :=
      ArithmeticFunction.vonMangoldt_le_log.trans (log_le_four_fifths_mul_sqrt hn0)
    have hsqrt_le : Real.sqrt n ≤ (n : ℝ) := by
      have hsq : Real.sqrt n * Real.sqrt n = (n : ℝ) := Real.mul_self_sqrt hn0.le
      have h1 : 1 ≤ Real.sqrt n := by
        rw [show (1 : ℝ) = Real.sqrt 1 by simp]
        exact Real.sqrt_le_sqrt (by linarith)
      nlinarith
    have h1 : Λ n / (n : ℝ) ≤ 1 := by
      rw [div_le_iff₀ hn0]
      linarith
    nlinarith [sq_nonneg (q n)]
  -- 2. Extend the `Icc 4 X` divisor sum to `Icc 2 X` and bound `√(n/2) log n ≤ (3/2) fourthRoot n ^ 3`.
  have hsqrt2_gt : (4 / 3 : ℝ) < Real.sqrt 2 := by
    rw [show (4 / 3 : ℝ) = Real.sqrt (16 / 9) by
      rw [show (16 / 9 : ℝ) = (4 / 3) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hdiv_pt : ∀ n : ℕ, 2 ≤ n →
      Real.sqrt ((n : ℝ) / (2 : ℝ)) * Real.log n ≤ (3 / 2) * fourthRoot (n : ℝ) ^ 3 := by
    intro n hn2
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hinv_sqrt2 : 1 / Real.sqrt 2 ≤ 3 / 4 := by
      rw [div_le_iff₀ (Real.sqrt_pos.mpr (by norm_num))]
      linarith
    have hsq_div : Real.sqrt ((n : ℝ) / 2) ≤ (3 / 4) * Real.sqrt n := by
      rw [Real.sqrt_div hn0.le, div_eq_mul_one_div, mul_comm _ (1 / Real.sqrt 2)]
      exact mul_le_mul_of_nonneg_right hinv_sqrt2 (Real.sqrt_nonneg _)
    have hlog := log_le_two_mul_fourthRoot hn0
    have hlog_nonneg : 0 ≤ Real.log n :=
      Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
    calc Real.sqrt ((n : ℝ) / 2) * Real.log n
        ≤ ((3 / 4) * Real.sqrt n) * (2 * fourthRoot (n : ℝ)) :=
          mul_le_mul hsq_div hlog hlog_nonneg (by positivity)
      _ = (3 / 2) * (fourthRoot (n : ℝ) ^ 2 * fourthRoot (n : ℝ)) := by
          rw [fourthRoot_sq]; ring
      _ = (3 / 2) * fourthRoot (n : ℝ) ^ 3 := by ring
  have hdiv_all : ∑ n ∈ Icc (2 * 2) X, (Real.sqrt ((n : ℝ) / (2 : ℝ)) * Real.log n) * q n ^ 2 ≤
      ∑ n ∈ Icc 2 X, ((3 / 2) * fourthRoot (n : ℝ) ^ 3) * q n ^ 2 := by
    calc ∑ n ∈ Icc (2 * 2) X, (Real.sqrt ((n : ℝ) / (2 : ℝ)) * Real.log n) * q n ^ 2
        ≤ ∑ n ∈ Icc (2 * 2) X, ((3 / 2) * fourthRoot (n : ℝ) ^ 3) * q n ^ 2 :=
          sum_le_sum fun n hn =>
            mul_le_mul_of_nonneg_right (hdiv_pt n (by have := (mem_Icc.mp hn).1; omega)) (sq_nonneg _)
      _ ≤ ∑ n ∈ Icc 2 X, ((3 / 2) * fourthRoot (n : ℝ) ^ 3) * q n ^ 2 :=
          sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_left (by omega)) fun n _ _ =>
            mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg (fourthRoot_nonneg _) 3)) (sq_nonneg _)
  -- 3. Split all `Icc 2 X` sums at `255` into `Icc 2 (min X 255)` and `Icc 256 X`.
  have hsp_arch := sum_Icc_split_at (fun n => archReflectedDiagWeight n * q n ^ 2)
    (a := 2) (M := 255) (X := X) (by omega)
  have hsp_sq := sum_Icc_split_at (fun n => q n ^ 2)
    (a := 2) (M := 255) (X := X) (by omega)
  have hsp_fr := sum_Icc_split_at (fun n => ((3 / 2) * fourthRoot (n : ℝ) ^ 3) * q n ^ 2)
    (a := 2) (M := 255) (X := X) (by omega)
  -- Head bound (`2 ≤ n ≤ min X 255`): `arch ≥ -1` and `(3/2) fourthRoot n ^ 3 ≤ 96`.
  have hhead : -106 * ∑ n ∈ Icc 2 (min X 255), q n ^ 2 ≤
      ∑ n ∈ Icc 2 (min X 255), archReflectedDiagWeight n * q n ^ 2 -
        9 * ∑ n ∈ Icc 2 (min X 255), q n ^ 2 -
        ∑ n ∈ Icc 2 (min X 255), ((3 / 2) * fourthRoot (n : ℝ) ^ 3) * q n ^ 2 := by
    rw [mul_sum, mul_sum, ← sum_sub_distrib, ← sum_sub_distrib]
    refine sum_le_sum fun n hn => ?_
    have hn2 : 2 ≤ n := (mem_Icc.mp hn).1
    have hn255 : n ≤ 255 := (mem_Icc.mp hn).2.trans (min_le_right X 255)
    have harch := neg_one_le_archReflectedDiagWeight hn2
    have hfr_le4 : fourthRoot (n : ℝ) ≤ 4 := by
      rw [← fourthRoot_256]
      exact fourthRoot_mono (by exact_mod_cast (by omega : n ≤ 256))
    have hfr0 : 0 ≤ fourthRoot (n : ℝ) := fourthRoot_nonneg _
    have hfr3 : fourthRoot (n : ℝ) ^ 3 ≤ 64 := by
      have hfr2 : fourthRoot (n : ℝ) ^ 2 ≤ 16 := by nlinarith
      nlinarith
    have hcoef : (-106 : ℝ) ≤ archReflectedDiagWeight n - 9 - (3 / 2) * fourthRoot (n : ℝ) ^ 3 := by
      linarith
    nlinarith [sq_nonneg (q n)]
  -- Tail bound (`256 ≤ n ≤ X`): `fourthRoot n ≥ 4` gives `(3/2) fourthRoot n ^ 3 ≤ (3/8) n`,
  -- leaving `(1/2 - 3/8) n - (9 + 6/5) = (1/8) n - 51/5 ≥ (1/16) n` for `n ≥ 256`.
  have htail : (1 / 16) * ∑ n ∈ Icc 256 X, (n : ℝ) * q n ^ 2 ≤
      ∑ n ∈ Icc 256 X, archReflectedDiagWeight n * q n ^ 2 -
        9 * ∑ n ∈ Icc 256 X, q n ^ 2 -
        ∑ n ∈ Icc 256 X, ((3 / 2) * fourthRoot (n : ℝ) ^ 3) * q n ^ 2 := by
    rw [mul_sum, mul_sum, ← sum_sub_distrib, ← sum_sub_distrib]
    refine sum_le_sum fun n hn => ?_
    have hn256 : 256 ≤ n := (mem_Icc.mp hn).1
    have hn256' : (256 : ℝ) ≤ n := by exact_mod_cast hn256
    have hn0 : (0 : ℝ) ≤ n := by positivity
    have harch := half_sub_six_fifths_lt_archReflectedDiagWeight (by omega : 3 ≤ n)
    have hfr_ge4 : 4 ≤ fourthRoot (n : ℝ) := by
      rw [← fourthRoot_256]
      exact fourthRoot_mono hn256'
    have hfr3_pos : 0 ≤ fourthRoot (n : ℝ) ^ 3 := pow_nonneg (fourthRoot_nonneg _) 3
    have hfr4 : 4 * fourthRoot (n : ℝ) ^ 3 ≤ (n : ℝ) := by
      calc 4 * fourthRoot (n : ℝ) ^ 3
          ≤ fourthRoot (n : ℝ) * fourthRoot (n : ℝ) ^ 3 :=
            mul_le_mul_of_nonneg_right hfr_ge4 hfr3_pos
        _ = fourthRoot (n : ℝ) ^ 4 := by ring
        _ = (n : ℝ) := fourthRoot_pow_four hn0
    have hcoef : (1 / 16 : ℝ) * (n : ℝ) ≤
        archReflectedDiagWeight n - 9 - (3 / 2) * fourthRoot (n : ℝ) ^ 3 := by
      linarith
    nlinarith [sq_nonneg (q n)]
  linarith

end

end GaloisForLFunctions.ArithmeticOrientationTheory
