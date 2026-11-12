import GaloisForLFunctions.PrimeExponentialSums.VinogradovAtRationals
import GaloisForLFunctions.RHTower.Sieve.GapSums
import GaloisForLFunctions.ShortIntervalPrimesInProgressions.SiegelWalfisz

/-!
# Minor arcs for primes

For every `A ∈ ℕ` there is `N₀` such that for `N ≥ N₀`, every `q` with
`(log N)^{2A+12} ≤ q ≤ N/(log N)^{2A+12}` and every primitive `q`-th root of unity `ζ`,

`‖Σ_{n ≤ N} Λ(n) ζⁿ‖ ≤ N/(log N)^A` (`norm_sum_vonMangoldt_pow_le_minor`).

Vinogradov's bound (`VinogradovAtRationals`) with `U = ⌊N^{1/4}⌋`: with `L = log N`, every term of
the majorant is at most `N/(5L^A)` once `L^{2A+12} ≤ q ≤ N/L^{2A+12}` and `U ≥ 115200 L^{2A+8}`
(`vinogradovBound_le`); the Type-II terms carry `√(1/q + 1/U)` against powers of `L`.
-/

open Finset ArithmeticFunction Filter
open GaloisForLFunctions.BezoutValuationIncidence RHTower.Sieve
open scoped BigOperators

namespace GaloisForLFunctions.PrimeExponentialSums

noncomputable section
set_option autoImplicit false

/-- `log₂ n + 1 ≤ 4 log n` for `n ≥ 2`. -/
theorem nat_log_two_add_one_le {n : ℕ} (hn : 2 ≤ n) : (Nat.log 2 n : ℝ) + 1 ≤ 4 * Real.log n := by
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have h1 : (2 : ℝ) ^ (Nat.log 2 n) ≤ n := by exact_mod_cast Nat.pow_log_le_self 2 (by omega)
  have h2 : (Nat.log 2 n : ℝ) * Real.log 2 ≤ Real.log n := by
    have := Real.log_le_log (by positivity) h1
    rwa [Real.log_pow] at this
  have h3 : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have hk : (Nat.log 2 n : ℝ) * (1 / 2) ≤ (Nat.log 2 n : ℝ) * Real.log 2 :=
    mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg _)
  linarith

/-- `W_q ≤ q (1 + log N)` for `q ≤ N`. -/
theorem rootHarmonicSum_le_of_le {q N : ℕ} (hqN : q ≤ N) :
    rootHarmonicSum q ≤ q * (1 + Real.log N) := by
  refine (rootHarmonicSum_le q).trans ?_
  have := real_log_natCast_mono hqN
  have : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  nlinarith

/-! ### Pure inequalities -/

section Arith

variable {L M U N q W : ℝ}

/-- `1/(M²L¹²)` and `1/U` against `M²L⁵` and `M²L⁸`. -/
theorem small_of_parameters (hL20 : 20 ≤ L) (hM1 : 1 ≤ M) (hU : 115200 * M ^ 2 * L ^ 8 ≤ U) :
    800 * M ^ 2 * L ^ 5 * (1 / (M ^ 2 * L ^ 12) + 1 / U) ≤ 1 ∧
      57600 * M ^ 2 * L ^ 8 * (1 / (M ^ 2 * L ^ 12) + 1 / U) ≤ 1 := by
  have hL0 : 0 < L := by linarith
  have hM0 : 0 < M := by linarith
  have hU0 : 0 < U := lt_of_lt_of_le (by positivity) hU
  have hL3 : (8000 : ℝ) ≤ L ^ 3 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 20) hL20 3
    norm_num at this
    linarith
  have hL4 : (160000 : ℝ) ≤ L ^ 4 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 20) hL20 4
    norm_num at this
    linarith
  have hL7 : (1280000000 : ℝ) ≤ L ^ 7 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 20) hL20 7
    norm_num at this
    linarith
  have e1 : 800 * M ^ 2 * L ^ 5 * (1 / (M ^ 2 * L ^ 12)) = 800 / L ^ 7 := by
    field_simp
  have e2 : 57600 * M ^ 2 * L ^ 8 * (1 / (M ^ 2 * L ^ 12)) = 57600 / L ^ 4 := by
    field_simp
  have f1 : 800 * M ^ 2 * L ^ 5 * (1 / U) ≤ 800 / (115200 * L ^ 3) := by
    rw [mul_one_div, div_le_div_iff₀ hU0 (by positivity)]
    have : 800 * M ^ 2 * L ^ 5 * (115200 * L ^ 3) = 800 * (115200 * M ^ 2 * L ^ 8) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hU (by norm_num)
  have f2 : 57600 * M ^ 2 * L ^ 8 * (1 / U) ≤ 57600 / 115200 := by
    rw [mul_one_div, div_le_div_iff₀ hU0 (by norm_num)]
    have : 57600 * M ^ 2 * L ^ 8 * 115200 = 57600 * (115200 * M ^ 2 * L ^ 8) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hU (by norm_num)
  have g1 : 800 / L ^ 7 ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have g2 : 800 / (115200 * L ^ 3) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have g3 : 57600 / L ^ 4 ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  constructor
  · rw [mul_add, e1]; linarith
  · rw [mul_add, e2]; linarith

/-- The short sum: `U log U ≤ N/(5M)`. -/
theorem shortTerm_le (hL1 : 1 ≤ L) (hM1 : 1 ≤ M) (hU : 115200 * M ^ 2 * L ^ 8 ≤ U)
    (hU4 : U ^ 4 ≤ N) {lU : ℝ} (hlU0 : 0 ≤ lU) (hlU : lU ≤ L) : U * lU ≤ N / (5 * M) := by
  have hM0 : 0 < M := by linarith
  have hU1 : 1 ≤ U := by
    have : 1 ≤ 115200 * M ^ 2 * L ^ 8 := by
      have : 1 ≤ M ^ 2 * L ^ 8 := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hM1) (one_le_pow₀ hL1)
      linarith
    linarith
  have h1 : 5 * M * L ≤ U ^ 3 := by
    have hML : 5 * M * L ≤ 115200 * M ^ 2 * L ^ 8 := by
      have h8 : L ≤ L ^ 8 := le_self_pow₀ hL1 (by norm_num)
      have hM2 : M ≤ M ^ 2 := le_self_pow₀ hM1 (by norm_num)
      have : M * L ≤ M ^ 2 * L ^ 8 := mul_le_mul hM2 h8 (by linarith) (by positivity)
      nlinarith
    have hU3 : U ≤ U ^ 3 := le_self_pow₀ hU1 (by norm_num)
    linarith
  rw [le_div_iff₀ (by positivity)]
  have hU0 : 0 ≤ U := by linarith
  calc U * lU * (5 * M) ≤ U * L * (5 * M) := by gcongr
    _ = U * (5 * M * L) := by ring
    _ ≤ U * U ^ 3 := by gcongr
    _ = U ^ 4 := by ring
    _ ≤ N := hU4

/-- The Type-I terms: at most `3N/(10M)`. -/
theorem typeITerms_le (hL20 : 20 ≤ L) (hM1 : 1 ≤ M) (hU : 115200 * M ^ 2 * L ^ 8 ≤ U)
    (hU4 : U ^ 4 ≤ N) (hq1 : M ^ 2 * L ^ 12 ≤ q) (hq2 : q * (M ^ 2 * L ^ 12) ≤ N)
    (hW0 : 0 ≤ W) (hW : W ≤ q * (1 + L)) {lU : ℝ} (hlU0 : 0 ≤ lU) (hlU : lU ≤ L) :
    lU * ((U / q + 1) * W + N / q * (1 + lU)) + (2 * L * ((U / q + 1) * W) + N / q * (1 + lU) * L)
      ≤ 3 * (N / (10 * M)) := by
  have hL1 : 1 ≤ L := by linarith
  have hL0 : 0 < L := by linarith
  have hM0 : 0 < M := by linarith
  have hP : 0 < M ^ 2 * L ^ 12 := by positivity
  have hq0 : 0 < q := lt_of_lt_of_le hP hq1
  have hU0 : 0 < U := lt_of_lt_of_le (by positivity) hU
  have hN0 : 0 < N := lt_of_lt_of_le (by positivity) hU4
  -- `(U/q + 1) W ≤ (U + q)(1 + L)`
  have hUq : (U / q + 1) * W ≤ (U + q) * (1 + L) := by
    calc (U / q + 1) * W ≤ (U / q + 1) * (q * (1 + L)) := mul_le_mul_of_nonneg_left hW (by positivity)
      _ = (U + q) * (1 + L) := by field_simp
  have hUq0 : 0 ≤ (U / q + 1) * W := by positivity
  have hNq0 : 0 ≤ N / q := by positivity
  have hlU1 : 1 + lU ≤ 1 + L := by linarith
  -- each piece is a multiple of `X = (U + q + N/q)(1 + L) L`
  have hpieces : lU * ((U / q + 1) * W + N / q * (1 + lU)) +
      (2 * L * ((U / q + 1) * W) + N / q * (1 + lU) * L) ≤ 3 * ((U + q + N / q) * (1 + L) * L) := by
    have e1 : lU * ((U / q + 1) * W) ≤ L * ((U + q) * (1 + L)) := mul_le_mul hlU hUq hUq0 hL0.le
    have e2 : lU * (N / q * (1 + lU)) ≤ L * (N / q * (1 + L)) :=
      mul_le_mul hlU (mul_le_mul_of_nonneg_left hlU1 hNq0) (by positivity) hL0.le
    have e3 : 2 * L * ((U / q + 1) * W) ≤ 2 * L * ((U + q) * (1 + L)) :=
      mul_le_mul_of_nonneg_left hUq (by positivity)
    have e4 : N / q * (1 + lU) * L ≤ N / q * (1 + L) * L :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlU1 hNq0) hL0.le
    have e5 : 0 ≤ (U + q) * (1 + L) * L := by positivity
    have e6 : 0 ≤ N / q * (1 + L) * L := by positivity
    calc _ = lU * ((U / q + 1) * W) + lU * (N / q * (1 + lU)) + 2 * L * ((U / q + 1) * W) +
          N / q * (1 + lU) * L := by ring
      _ ≤ L * ((U + q) * (1 + L)) + L * (N / q * (1 + L)) + 2 * L * ((U + q) * (1 + L)) +
          N / q * (1 + L) * L := by linarith
      _ ≤ 3 * ((U + q + N / q) * (1 + L) * L) := by nlinarith
  refine hpieces.trans ?_
  -- `U + q + N/q ≤ N/U³ + 2N/(M²L¹²)`
  have hU3 : U ≤ N / U ^ 3 := by
    rw [le_div_iff₀ (by positivity)]
    calc U * U ^ 3 = U ^ 4 := by ring
      _ ≤ N := hU4
  have hqN : q ≤ N / (M ^ 2 * L ^ 12) := by rw [le_div_iff₀ hP]; exact hq2
  have hNq : N / q ≤ N / (M ^ 2 * L ^ 12) := div_le_div_of_nonneg_left hN0.le hP hq1
  have hsum : U + q + N / q ≤ N / U ^ 3 + 2 * (N / (M ^ 2 * L ^ 12)) := by linarith
  have hb1 : N / U ^ 3 * (20 * M * L ^ 2) ≤ N / 2 := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    have h40 : 40 * M * L ^ 2 ≤ U ^ 3 := by
      have hML : 40 * M * L ^ 2 ≤ 115200 * M ^ 2 * L ^ 8 := by
        have h8 : L ^ 2 ≤ L ^ 8 := pow_le_pow_right₀ hL1 (by norm_num)
        have hM2 : M ≤ M ^ 2 := le_self_pow₀ hM1 (by norm_num)
        have : M * L ^ 2 ≤ M ^ 2 * L ^ 8 := mul_le_mul hM2 h8 (by positivity) (by positivity)
        nlinarith
      have hU1 : 1 ≤ U := by nlinarith [one_le_pow₀ hL1 (n := 8), one_le_pow₀ hM1 (n := 2)]
      have hU3' : U ≤ U ^ 3 := le_self_pow₀ hU1 (by norm_num)
      linarith
    nlinarith
  have hb2 : 2 * (N / (M ^ 2 * L ^ 12)) * (20 * M * L ^ 2) ≤ N / 2 := by
    have e : 2 * (N / (M ^ 2 * L ^ 12)) * (20 * M * L ^ 2) = N * (40 / (M * L ^ 10)) := by
      field_simp; ring
    rw [e]
    have : 40 / (M * L ^ 10) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have : (80 : ℝ) ≤ L ^ 10 := by
        have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 20) hL20 10
        norm_num at this
        linarith
      nlinarith [one_le_pow₀ hL1 (n := 10)]
    nlinarith
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  rw [le_div_iff₀ (by positivity)]
  have hL2 : (1 + L) * L ≤ 2 * L ^ 2 := by nlinarith
  have hsum0 : 0 ≤ U + q + N / q := by positivity
  calc (U + q + N / q) * (1 + L) * L * (10 * M)
      = 10 * M * ((U + q + N / q) * ((1 + L) * L)) := by ring
    _ ≤ 10 * M * ((N / U ^ 3 + 2 * (N / (M ^ 2 * L ^ 12))) * (2 * L ^ 2)) := by
        gcongr
    _ = N / U ^ 3 * (20 * M * L ^ 2) + 2 * (N / (M ^ 2 * L ^ 12)) * (20 * M * L ^ 2) := by
        ring
    _ ≤ N / 2 + N / 2 := add_le_add hb1 hb2
    _ = N := by ring

/-- The inner Type-II sums, against `a = 1/(M²L¹²)` and `b = 1/U`. -/
theorem typeII_inner_le (hL20 : 20 ≤ L) (hM1 : 1 ≤ M) (hU : 115200 * M ^ 2 * L ^ 8 ≤ U)
    (hU4 : U ^ 4 ≤ N) (hq1 : M ^ 2 * L ^ 12 ≤ q) (hq2 : q * (M ^ 2 * L ^ 12) ≤ N)
    (hW0 : 0 ≤ W) (hW : W ≤ q * (1 + L)) :
    N / q + U * U * W / q + N / U + W ≤ 2 * L * N * (1 / (M ^ 2 * L ^ 12) + 1 / U) ∧
      N ^ 2 / q + N ^ 2 / U + N ^ 2 * W / (U * q) + N * W
        ≤ 2 * L * N ^ 2 * (1 / (M ^ 2 * L ^ 12) + 1 / U) := by
  have hL1 : 1 ≤ L := by linarith
  have hM0 : 0 < M := by linarith
  have hP : 0 < M ^ 2 * L ^ 12 := by positivity
  have hq0 : 0 < q := lt_of_lt_of_le hP hq1
  have hU0 : 0 < U := lt_of_lt_of_le (by positivity) hU
  have hU1 : 1 ≤ U := le_trans (by nlinarith [one_le_pow₀ hL1 (n := 8), one_le_pow₀ hM1 (n := 2)]) hU
  have hN0 : 0 < N := lt_of_lt_of_le (by positivity) hU4
  set a := 1 / (M ^ 2 * L ^ 12) with ha
  set b := 1 / U with hb
  have ha0 : 0 < a := by positivity
  have hb0 : 0 < b := by positivity
  have hbb : b ^ 2 ≤ b := by
    have : b ≤ 1 := by rw [hb, div_le_one hU0]; exact hU1
    nlinarith
  have hNq : N / q ≤ N * a := by
    rw [ha, mul_one_div]; exact div_le_div_of_nonneg_left hN0.le hP hq1
  have hqa : q ≤ N * a := by
    rw [ha, mul_one_div, le_div_iff₀ hP]; exact hq2
  have hUU : U * U ≤ N * b ^ 2 := by
    rw [hb, div_pow, one_pow, mul_one_div, le_div_iff₀ (by positivity)]
    nlinarith
  have hWq : W / q ≤ 1 + L := by rw [div_le_iff₀ hq0]; linarith
  have hWa : W ≤ N * a * (1 + L) :=
    hW.trans (mul_le_mul_of_nonneg_right hqa (by linarith))
  have hL2 : 2 + L ≤ 2 * L := by linarith
  constructor
  · have t2 : U * U * W / q ≤ N * b ^ 2 * (1 + L) := by
      rw [mul_div_assoc]
      exact mul_le_mul hUU hWq (div_nonneg hW0 hq0.le) (by positivity)
    have t2' : N * b ^ 2 * (1 + L) ≤ N * b * (1 + L) := by
      have := mul_le_mul_of_nonneg_left hbb hN0.le
      nlinarith
    have hNU : N / U = N * b := by rw [hb, mul_one_div]
    have : N / q + U * U * W / q + N / U + W ≤ N * (2 + L) * (a + b) := by nlinarith
    calc N / q + U * U * W / q + N / U + W ≤ N * (2 + L) * (a + b) := this
      _ ≤ N * (2 * L) * (a + b) := by gcongr
      _ = 2 * L * N * (a + b) := by ring
  · have t1 : N ^ 2 / q ≤ N ^ 2 * a := by
      rw [sq, mul_div_assoc]
      exact (mul_le_mul_of_nonneg_left hNq hN0.le).trans_eq (by ring)
    have t2 : N ^ 2 / U = N ^ 2 * b := by rw [hb, mul_one_div]
    have t3 : N ^ 2 * W / (U * q) ≤ N ^ 2 * b * (1 + L) := by
      have e : N ^ 2 * W / (U * q) = N ^ 2 * b * (W / q) := by rw [hb]; field_simp
      rw [e]
      exact mul_le_mul_of_nonneg_left hWq (by positivity)
    have t4 : N * W ≤ N ^ 2 * a * (1 + L) := by
      have := mul_le_mul_of_nonneg_left hWa hN0.le
      nlinarith
    have : N ^ 2 / q + N ^ 2 / U + N ^ 2 * W / (U * q) + N * W ≤ N ^ 2 * (2 + L) * (a + b) := by
      nlinarith
    calc _ ≤ N ^ 2 * (2 + L) * (a + b) := this
      _ ≤ N ^ 2 * (2 * L) * (a + b) := by gcongr
      _ = 2 * L * N ^ 2 * (a + b) := by ring

/-- The Type-II term of the double convolution: at most `N/(5M)`. -/
theorem typeIIa_le (hL20 : 20 ≤ L) (hM1 : 1 ≤ M) (hU : 115200 * M ^ 2 * L ^ 8 ≤ U)
    (hU4 : U ^ 4 ≤ N) (hq1 : M ^ 2 * L ^ 12 ≤ q) (hq2 : q * (M ^ 2 * L ^ 12) ≤ N)
    (hW0 : 0 ≤ W) (hW : W ≤ q * (1 + L)) {g : ℝ} (_hg0 : 0 ≤ g) (hg : g ≤ 4 * L) :
    L * (g * Real.sqrt (N * (N / q + U * U * W / q + N / U + W))) ≤ N / (5 * M) := by
  have hL0 : 0 < L := by linarith
  have hM0 : 0 < M := by linarith
  have hN0 : 0 < N := lt_of_lt_of_le (by
    have hU0 : 0 < U := lt_of_lt_of_le (by positivity) hU
    positivity) hU4
  obtain ⟨hin, -⟩ := typeII_inner_le hL20 hM1 hU hU4 hq1 hq2 hW0 hW
  obtain ⟨hsmall, -⟩ := small_of_parameters hL20 hM1 hU
  have hX : N * (N / q + U * U * W / q + N / U + W) ≤ (N / (20 * M * L ^ 2)) ^ 2 := by
    have hrhs : (N / (20 * M * L ^ 2)) ^ 2 = N ^ 2 / (400 * M ^ 2 * L ^ 4) := by
      field_simp; ring
    rw [hrhs, le_div_iff₀ (by positivity)]
    calc N * (N / q + U * U * W / q + N / U + W) * (400 * M ^ 2 * L ^ 4)
        ≤ N * (2 * L * N * (1 / (M ^ 2 * L ^ 12) + 1 / U)) * (400 * M ^ 2 * L ^ 4) := by gcongr
      _ = N ^ 2 * (800 * M ^ 2 * L ^ 5 * (1 / (M ^ 2 * L ^ 12) + 1 / U)) := by ring
      _ ≤ N ^ 2 * 1 := by gcongr
      _ = N ^ 2 := mul_one _
  have hsq : Real.sqrt (N * (N / q + U * U * W / q + N / U + W)) ≤ N / (20 * M * L ^ 2) := by
    calc _ ≤ Real.sqrt ((N / (20 * M * L ^ 2)) ^ 2) := Real.sqrt_le_sqrt hX
      _ = N / (20 * M * L ^ 2) := Real.sqrt_sq (by positivity)
  calc L * (g * Real.sqrt (N * (N / q + U * U * W / q + N / U + W)))
      ≤ L * (4 * L * (N / (20 * M * L ^ 2))) := by gcongr
    _ = N / (5 * M) := by field_simp; ring

/-- The Type-II term of `(Λ − Λ_U) ∗ g`: at most `N/(5M)`. -/
theorem typeIIb_le (hL20 : 20 ≤ L) (hM1 : 1 ≤ M) (hU : 115200 * M ^ 2 * L ^ 8 ≤ U)
    (hU4 : U ^ 4 ≤ N) (hq1 : M ^ 2 * L ^ 12 ≤ q) (hq2 : q * (M ^ 2 * L ^ 12) ≤ N)
    (hW0 : 0 ≤ W) (hW : W ≤ q * (1 + L)) {g H : ℝ} (_hg0 : 0 ≤ g) (hg : g ≤ 4 * L) (hH0 : 0 ≤ H)
    (hH : H ≤ 1 + L) :
    g * (1 + L) * Real.sqrt (2 * (1 + H ^ 3) * (N ^ 2 / q + N ^ 2 / U + N ^ 2 * W / (U * q) + N * W))
      ≤ N / (5 * M) := by
  have hL1 : 1 ≤ L := by linarith
  have hL0 : 0 < L := by linarith
  have hM0 : 0 < M := by linarith
  have hU0 : 0 < U := lt_of_lt_of_le (by positivity) hU
  have hN0 : 0 < N := lt_of_lt_of_le (by positivity) hU4
  have hP : 0 < M ^ 2 * L ^ 12 := by positivity
  have hq0 : 0 < q := lt_of_lt_of_le hP hq1
  obtain ⟨-, hin⟩ := typeII_inner_le hL20 hM1 hU hU4 hq1 hq2 hW0 hW
  obtain ⟨-, hsmall⟩ := small_of_parameters hL20 hM1 hU
  have hH3 : 2 * (1 + H ^ 3) ≤ 18 * L ^ 3 := by
    have h1 : H ^ 3 ≤ (2 * L) ^ 3 := pow_le_pow_left₀ hH0 (by linarith) 3
    have h2 : (1 : ℝ) ≤ L ^ 3 := one_le_pow₀ hL1
    nlinarith
  have hin0 : 0 ≤ N ^ 2 / q + N ^ 2 / U + N ^ 2 * W / (U * q) + N * W := by positivity
  have hY : 2 * (1 + H ^ 3) * (N ^ 2 / q + N ^ 2 / U + N ^ 2 * W / (U * q) + N * W)
      ≤ (N / (40 * M * L ^ 2)) ^ 2 := by
    have hrhs : (N / (40 * M * L ^ 2)) ^ 2 = N ^ 2 / (1600 * M ^ 2 * L ^ 4) := by
      field_simp; ring
    rw [hrhs, le_div_iff₀ (by positivity)]
    calc 2 * (1 + H ^ 3) * (N ^ 2 / q + N ^ 2 / U + N ^ 2 * W / (U * q) + N * W)
          * (1600 * M ^ 2 * L ^ 4)
        ≤ 18 * L ^ 3 * (2 * L * N ^ 2 * (1 / (M ^ 2 * L ^ 12) + 1 / U)) *
            (1600 * M ^ 2 * L ^ 4) := by gcongr
      _ = N ^ 2 * (57600 * M ^ 2 * L ^ 8 * (1 / (M ^ 2 * L ^ 12) + 1 / U)) := by ring
      _ ≤ N ^ 2 * 1 := by gcongr
      _ = N ^ 2 := mul_one _
  have hsq : Real.sqrt (2 * (1 + H ^ 3) * (N ^ 2 / q + N ^ 2 / U + N ^ 2 * W / (U * q) + N * W))
      ≤ N / (40 * M * L ^ 2) := by
    calc _ ≤ Real.sqrt ((N / (40 * M * L ^ 2)) ^ 2) := Real.sqrt_le_sqrt hY
      _ = N / (40 * M * L ^ 2) := Real.sqrt_sq (by positivity)
  have h1L : 1 + L ≤ 2 * L := by linarith
  calc g * (1 + L) * Real.sqrt (2 * (1 + H ^ 3) * (N ^ 2 / q + N ^ 2 / U + N ^ 2 * W / (U * q) +
        N * W))
      ≤ (4 * L) * (2 * L) * (N / (40 * M * L ^ 2)) := by gcongr
    _ = N / (5 * M) := by field_simp; ring

end Arith

/-- **The majorant on the minor arcs.** -/
theorem vinogradovBound_le {A q U N : ℕ} (hL20 : 20 ≤ Real.log N) (hU2 : 2 ≤ U)
    (hU4 : (U : ℝ) ^ 4 ≤ N) (hUL : 115200 * Real.log N ^ (2 * A + 8) ≤ U)
    (hq1 : Real.log N ^ (2 * A + 12) ≤ q) (hq2 : (q : ℝ) ≤ N / Real.log N ^ (2 * A + 12)) :
    vinogradovBound q U N ≤ N / Real.log N ^ A := by
  set L := Real.log N with hL
  set M := L ^ A with hMdef
  have hL1 : 1 ≤ L := by linarith
  have hM1 : 1 ≤ M := one_le_pow₀ hL1
  have hM0 : 0 < M := by linarith
  have hLKM : L ^ (2 * A + 12) = M ^ 2 * L ^ 12 := by rw [hMdef, ← pow_mul, ← pow_add]; ring_nf
  have hL8M : L ^ (2 * A + 8) = M ^ 2 * L ^ 8 := by rw [hMdef, ← pow_mul, ← pow_add]; ring_nf
  rw [hL8M] at hUL
  rw [hLKM] at hq1 hq2
  have hU' : 115200 * M ^ 2 * L ^ 8 ≤ (U : ℝ) := by linarith
  have hq2' : (q : ℝ) * (M ^ 2 * L ^ 12) ≤ N := by rwa [le_div_iff₀ (by positivity)] at hq2
  have hN3 : 3 ≤ N := by
    by_contra h
    push Not at h
    have hle : (N : ℝ) ≤ 2 := by exact_mod_cast (show N ≤ 2 by omega)
    have hlog : Real.log N ≤ Real.log 2 := by
      rcases Nat.eq_zero_or_pos N with h0 | h0
      · rw [h0, Nat.cast_zero, Real.log_zero]
        exact Real.log_nonneg (by norm_num)
      · exact Real.log_le_log (by exact_mod_cast h0) hle
    have := Real.log_two_lt_d9
    linarith
  have hqpos : (0 : ℝ) < q := lt_of_lt_of_le (by positivity) hq1
  have hqN : q ≤ N := by
    have : (q : ℝ) ≤ N := by
      have : (q : ℝ) ≤ q * (M ^ 2 * L ^ 12) :=
        le_mul_of_one_le_right hqpos.le (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hM1)
          (one_le_pow₀ hL1))
      linarith
    exact_mod_cast this
  have hW := rootHarmonicSum_le_of_le hqN
  rw [← hL] at hW
  have hW0 := rootHarmonicSum_nonneg q
  have hlogU0 : 0 ≤ Real.log U := Real.log_natCast_nonneg U
  have hlogU : Real.log U ≤ L := by
    rw [hL]
    refine real_log_natCast_mono ?_
    have hU1 : (1 : ℝ) ≤ U := by exact_mod_cast (show 1 ≤ U by omega)
    have : (U : ℝ) ≤ N := (le_self_pow₀ hU1 (by norm_num : 4 ≠ 0)).trans hU4
    exact_mod_cast this
  have hlog2U : (Nat.log 2 U : ℝ) + 1 ≤ 4 * L :=
    (nat_log_two_add_one_le hU2).trans (by linarith)
  have hlog2N : (Nat.log 2 N : ℝ) + 1 ≤ 4 * L := by
    rw [hL]; exact nat_log_two_add_one_le (by omega)
  have hinv : invSum N ≤ 1 + L := by rw [hL]; exact invSum_le_one_add_log (by omega)
  have h0 := shortTerm_le hL1 hM1 hU' hU4 hlogU0 hlogU
  have h1 := typeITerms_le hL20 hM1 hU' hU4 hq1 hq2' hW0 hW hlogU0 hlogU
  have h2 := typeIIa_le hL20 hM1 hU' hU4 hq1 hq2' hW0 hW (by positivity) hlog2U
  have h3 := typeIIb_le hL20 hM1 hU' hU4 hq1 hq2' hW0 hW (by positivity) hlog2N
    (invSum_nonneg N) hinv
  unfold vinogradovBound typeIIBlockBound
  rw [← hL]
  have hfin : N / (5 * M) + 3 * (N / (10 * M)) + N / (5 * M) + N / (5 * M) ≤ (N : ℝ) / M := by
    have e : (N : ℝ) / (5 * M) + 3 * (N / (10 * M)) + N / (5 * M) + N / (5 * M)
        = 9 / 10 * (N / M) := by field_simp; ring
    rw [e]
    have : 0 ≤ (N : ℝ) / M := by positivity
    linarith
  linarith

/-- **Minor arcs for primes.** For every `A` there is `N₀` such that for `N ≥ N₀`, every `q` with
`(log N)^{2A+12} ≤ q ≤ N/(log N)^{2A+12}` and every primitive `q`-th root `ζ`,
`‖Σ_{n ≤ N} Λ(n) ζⁿ‖ ≤ N/(log N)^A`. -/
theorem norm_sum_vonMangoldt_pow_le_minor (A : ℕ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ q : ℕ, Real.log N ^ (2 * A + 12) ≤ q →
      (q : ℝ) ≤ N / Real.log N ^ (2 * A + 12) → ∀ ζ : ℂ, IsPrimitiveRoot ζ q →
        ‖∑ n ∈ Icc 1 N, ((vonMangoldt n : ℝ) : ℂ) * ζ ^ n‖ ≤ N / Real.log N ^ A := by
  set C : ℝ := 115200 with hC
  have hlogN : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hev1 := hlogN.eventually (eventually_ge_atTop (20 : ℝ))
  have hpow := (ShortIntervalPrimesInProgressions.eventually_log_pow_le (8 * A + 32)
    (δ := 1 / (16 * C ^ 4)) (by positivity))
  have hev2 := tendsto_natCast_atTop_atTop.eventually hpow
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (hev1.and hev2)
  refine ⟨N₀, fun N hN q hq1 hq2 ζ hζ => ?_⟩
  obtain ⟨hL20, hpowN⟩ := hN₀ N hN
  set U := Nat.sqrt (Nat.sqrt N) with hUdef
  set L := Real.log N with hL
  have hL1 : 1 ≤ L := by linarith
  -- `U⁴ ≤ N < (U + 1)⁴`
  have hU4 : (U : ℝ) ^ 4 ≤ N := by
    have h1 : U * U ≤ Nat.sqrt N := Nat.sqrt_le (Nat.sqrt N)
    have h2 : Nat.sqrt N * Nat.sqrt N ≤ N := Nat.sqrt_le N
    have : U ^ 4 ≤ N := by
      calc U ^ 4 = (U * U) * (U * U) := by ring
        _ ≤ Nat.sqrt N * Nat.sqrt N := Nat.mul_le_mul h1 h1
        _ ≤ N := h2
    exact_mod_cast this
  have hNU : (N : ℝ) < ((U : ℝ) + 1) ^ 4 := by
    have h1 : Nat.sqrt N < (U + 1) * (U + 1) := Nat.lt_succ_sqrt (Nat.sqrt N)
    have h2 : N < (Nat.sqrt N + 1) * (Nat.sqrt N + 1) := Nat.lt_succ_sqrt N
    have : N < (U + 1) ^ 4 := by
      have h3 : Nat.sqrt N + 1 ≤ (U + 1) * (U + 1) := h1
      calc N < (Nat.sqrt N + 1) * (Nat.sqrt N + 1) := h2
        _ ≤ ((U + 1) * (U + 1)) * ((U + 1) * (U + 1)) := Nat.mul_le_mul h3 h3
        _ = (U + 1) ^ 4 := by ring
    exact_mod_cast this
  -- `U ≥ C L^{2A+8}`
  have hUL : C * L ^ (2 * A + 8) ≤ U := by
    by_contra hlt
    push Not at hlt
    have hCL1 : 1 ≤ C * L ^ (2 * A + 8) := by
      have := one_le_pow₀ (n := 2 * A + 8) hL1
      rw [hC]; nlinarith
    have hU1 : (U : ℝ) + 1 ≤ 2 * (C * L ^ (2 * A + 8)) := by linarith
    have h4 : ((U : ℝ) + 1) ^ 4 ≤ 16 * C ^ 4 * L ^ (8 * A + 32) := by
      calc ((U : ℝ) + 1) ^ 4 ≤ (2 * (C * L ^ (2 * A + 8))) ^ 4 :=
            pow_le_pow_left₀ (by positivity) hU1 4
        _ = 16 * C ^ 4 * L ^ (8 * A + 32) := by ring
    have h5 : 16 * C ^ 4 * L ^ (8 * A + 32) ≤ N := by
      have := hpowN
      have hC4 : 0 < 16 * C ^ 4 := by positivity
      calc 16 * C ^ 4 * L ^ (8 * A + 32) ≤ 16 * C ^ 4 * (1 / (16 * C ^ 4) * (N : ℝ)) := by
            gcongr
        _ = (N : ℝ) := by field_simp
    linarith
  have hU2 : 2 ≤ U := by
    have : (2 : ℝ) ≤ U := le_trans (by
      have := one_le_pow₀ (n := 2 * A + 8) hL1
      rw [hC]; nlinarith) hUL
    exact_mod_cast this
  have hqpos : (0 : ℝ) < q := lt_of_lt_of_le (by positivity) hq1
  have hq : 0 < q := by exact_mod_cast hqpos
  have hN3 : 3 ≤ N := by
    by_contra h
    push Not at h
    have hle : (N : ℝ) ≤ 2 := by exact_mod_cast (show N ≤ 2 by omega)
    have hlog : Real.log N ≤ Real.log 2 := by
      rcases Nat.eq_zero_or_pos N with h0 | h0
      · rw [h0, Nat.cast_zero, Real.log_zero]
        exact Real.log_nonneg (by norm_num)
      · exact Real.log_le_log (by exact_mod_cast h0) hle
    have := Real.log_two_lt_d9
    linarith
  refine (norm_sum_vonMangoldt_pow_le hq hζ (le_trans (by norm_num) hU2) hN3).trans ?_
  exact vinogradovBound_le hL20 hU2 hU4 (by rw [hC] at hUL; exact hUL) hq1 hq2

end

end GaloisForLFunctions.PrimeExponentialSums
