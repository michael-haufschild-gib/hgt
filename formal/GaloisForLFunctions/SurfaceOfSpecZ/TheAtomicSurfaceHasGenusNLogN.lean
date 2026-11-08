import GaloisForLFunctions.SurfaceOfSpecZ.TheAtomicGenusIsNLogN

/-!
# The atomic surface of degree `N` has genus of order `N log N`, unconditionally

`TheAtomicGenusIsNLogN` tests the atomic Frobenius graphs on one dyadic block. This file tests them on
all degrees `1 ≤ n ≤ N` at once: the defect of `Σ_{n ≤ N} x_n Γ_n` with self-defect `2gn`
(`genusDefect`) is nonnegative for every `x` as soon as

  `g ≥ 4N(1 + log N)`   (`genusDefect_Icc_nonneg_of_le`),

and only if `g ≥ M(log M − 17)/16`, `M = ⌊N/2⌋` (`genus_ge_of_genusDefect_Icc_nonneg`). So the atomic
surface truncated at degree `N` is a curve of genus `≍ N log N`, and this holds unconditionally.

**Bookkeeping of the three channels.** Off the diagonal `Γ_m·Γ_n = √(mn)(ω(|log m − log n|) + w(m, n))`
(`frobeniusIntersection_eq_sqrt_mul`), with `ω` the archimedean Lévy density and `w` Weil's prime
kernel.
* the jets: `ω(|log m − log n|) ≤ N/|m − n|` (`archLevyDensity_le`), a harmonic row sum `2N(1 + log N)`;
* the primes: `0 ≤ w ≤ 2` (`weilPrimeKernel_le_two`), a row sum `2N`;
* the pole `m + n`: rank two, `2(Σ x_n)(Σ n x_n) ≥ −N(2 + log N) Σ n x_n²` by Cauchy–Schwarz.
Only the jets reach order `N log N`, and the dyadic block shows they do (`TheAtomicGenusIsNLogN`).
The primes, where the zeros of `ζ` enter, are of lower order: the atomic diagonal is the archimedean
divergence, and the arithmetic sits below it.
-/

open Finset

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ

open ArithmeticEffectivityTheory
open scoped ArithmeticFunction.vonMangoldt

/-! ### The three channels -/

/-- Off the diagonal the Frobenius intersection is the archimedean plus the prime kernel. -/
theorem frobeniusIntersection_eq_sqrt_mul {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    frobeniusIntersection m n = Real.sqrt ((m : ℝ) * n) *
      (RHTower.archLevyDensity |Real.log m - Real.log n| + weilPrimeKernel m n) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [frobeniusIntersection, weilDeltaKernel, mul_sub, mul_sub, sqrt_mul_two_cosh hm' hn']
  ring

theorem vonMangoldt_div_sqrt_le_two (k : ℕ) : Λ k / Real.sqrt k ≤ 2 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hs : 0 < Real.sqrt k := Real.sqrt_pos.mpr (by linarith)
  rw [div_le_iff₀ hs]
  have h1 : Λ k ≤ Real.log k := ArithmeticFunction.vonMangoldt_le_log
  have h2 : Real.log k = 2 * Real.log (Real.sqrt k) := by
    rw [Real.log_sqrt (by linarith)]; ring
  have h3 := Real.log_le_sub_one_of_pos hs
  linarith

theorem weilPrimeKernel_nonneg (m n : ℕ) : 0 ≤ weilPrimeKernel m n := by
  unfold weilPrimeKernel
  split_ifs
  · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
  · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
  · exact le_rfl

/-- The prime kernel is at most `2`: `Λ(t)/√t ≤ 2`. -/
theorem weilPrimeKernel_le_two (m n : ℕ) : weilPrimeKernel m n ≤ 2 := by
  unfold weilPrimeKernel
  split_ifs
  · exact vonMangoldt_div_sqrt_le_two _
  · exact vonMangoldt_div_sqrt_le_two _
  · norm_num

/-- **The jets are harmonic.** For distinct degrees `≤ N`, `ω(|log m − log n|) ≤ N/|m − n|`. -/
theorem archLevyDensity_le {N m n : ℕ} (hm : m ∈ Icc 1 N) (hn : n ∈ Icc 1 N) (hmn : m ≠ n) :
    RHTower.archLevyDensity |Real.log m - Real.log n| ≤ N / |(m : ℝ) - n| := by
  rw [mem_Icc] at hm hn
  have hm' : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hmn' : (m : ℝ) ≠ n := by exact_mod_cast hmn
  have hs : 0 < Real.sqrt ((m : ℝ) * n) := Real.sqrt_pos.mpr (by positivity)
  have key := sqrt_mul_archLevyDensity hm' hn'
  have ha : 0 < min (m : ℝ) n := lt_min hm' hn'
  have hab : min (m : ℝ) n < max (m : ℝ) n := min_lt_max.mpr hmn'
  have hba : max (m : ℝ) n - min (m : ℝ) n = |(m : ℝ) - n| := max_sub_min_eq_abs_sub _ _
  rw [jet_eq ha hab] at key
  set a := min (m : ℝ) n
  set b := max (m : ℝ) n
  have hd : 0 < b - a := by linarith
  have hb0 : 0 < b := ha.trans hab
  have h1 : a * b ^ 2 / ((b - a) * (b + a)) ≤ a * b / (b - a) := by
    rw [div_le_div_iff₀ (by positivity) hd]
    have : a * b ^ 2 * (b - a) ≤ a * b * ((b - a) * (b + a)) := by
      have h := mul_le_mul_of_nonneg_left (show b ≤ b + a by linarith)
        (mul_nonneg (mul_nonneg ha.le hb0.le) hd.le)
      nlinarith [h]
    linarith
  have hsqrtN : Real.sqrt ((m : ℝ) * n) ≤ N := by
    have hmn2 : (m : ℝ) * n ≤ (N : ℝ) * N :=
      mul_le_mul (by exact_mod_cast hm.2) (by exact_mod_cast hn.2) hn'.le (Nat.cast_nonneg N)
    calc Real.sqrt ((m : ℝ) * n) ≤ Real.sqrt ((N : ℝ) * N) := Real.sqrt_le_sqrt hmn2
      _ = N := Real.sqrt_mul_self (Nat.cast_nonneg N)
  have h2 : a * b ≤ Real.sqrt ((m : ℝ) * n) * N := by
    rw [min_mul_max]
    calc (m : ℝ) * n = Real.sqrt ((m : ℝ) * n) * Real.sqrt ((m : ℝ) * n) :=
          (Real.mul_self_sqrt (by positivity)).symm
      _ ≤ Real.sqrt ((m : ℝ) * n) * N := mul_le_mul_of_nonneg_left hsqrtN (Real.sqrt_nonneg _)
  have h3 : Real.sqrt ((m : ℝ) * n) * RHTower.archLevyDensity |Real.log m - Real.log n| ≤
      Real.sqrt ((m : ℝ) * n) * (N / |(m : ℝ) - n|) := by
    rw [key, ← hba, mul_div_assoc']
    exact h1.trans (div_le_div_of_nonneg_right h2 hd.le)
  exact le_of_mul_le_mul_left h3 hs

/-- A row of `[1, N]` has harmonic mass at most `2(1 + log N)`. -/
theorem row_inv_le_Icc {N m : ℕ} (hm : m ∈ Icc 1 N) :
    ∑ n ∈ Icc 1 N, (if m = n then 0 else 1 / |(m : ℝ) - n|) ≤ 2 * (1 + Real.log N) := by
  rw [mem_Icc] at hm
  have hsplit : ∀ n ∈ Icc 1 N, (if m = n then (0 : ℝ) else 1 / |(m : ℝ) - n|) =
      (if m < n then 1 / ((n : ℝ) - m) else 0) + (if n < m then 1 / ((m : ℝ) - n) else 0) := by
    intro n _
    rcases lt_trichotomy m n with h | rfl | h
    · have h' : (m : ℝ) < n := by exact_mod_cast h
      rw [if_neg h.ne, if_pos h, if_neg (not_lt.mpr h.le), add_zero, abs_of_neg (by linarith),
        neg_sub]
    · simp
    · have h' : (n : ℝ) < m := by exact_mod_cast h
      rw [if_neg h.ne', if_neg (not_lt.mpr h.le), if_pos h, zero_add, abs_of_pos (by linarith)]
  rw [sum_congr rfl hsplit, sum_add_distrib, ← sum_filter, ← sum_filter]
  have hf1 : (Icc 1 N).filter (fun n => m < n) = Ico (m + 1) (N + 1) := by
    ext n; simp only [mem_filter, mem_Icc, mem_Ico]; omega
  have hf2 : (Icc 1 N).filter (fun n => n < m) = Ico 1 m := by
    ext n; simp only [mem_filter, mem_Icc, mem_Ico]; omega
  rw [hf1, hf2, sum_Ico_inv_sub, sum_Ico_inv_sub' hm.1]
  have h1 : invSum (N + 1 - (m + 1)) ≤ 1 + Real.log N :=
    (invSum_mono (by omega)).trans (invSum_le N)
  have h2 : invSum (m - 1) ≤ 1 + Real.log N := (invSum_mono (by omega)).trans (invSum_le N)
  linarith

/-- The pair weight `N/|m − n| + 2` dominates the normalized intersection of distinct degrees. -/
def atomicWeight (N m n : ℕ) : ℝ := N / |(m : ℝ) - n| + 2

theorem kernel_le_atomicWeight {N m n : ℕ} (hm : m ∈ Icc 1 N) (hn : n ∈ Icc 1 N) (hmn : m ≠ n) :
    RHTower.archLevyDensity |Real.log m - Real.log n| + weilPrimeKernel m n ≤ atomicWeight N m n :=
  add_le_add (archLevyDensity_le hm hn hmn) (weilPrimeKernel_le_two m n)

theorem row_atomicWeight_le {N m : ℕ} (hm : m ∈ Icc 1 N) :
    ∑ n ∈ Icc 1 N, (if m = n then 0 else atomicWeight N m n) ≤
      2 * N * (1 + Real.log N) + 2 * N := by
  have hcard : ((Icc 1 N).card : ℝ) = N := by rw [Nat.card_Icc]; push_cast; ring
  have hpt : ∀ n ∈ Icc 1 N, (if m = n then (0 : ℝ) else atomicWeight N m n) ≤
      N * (if m = n then 0 else 1 / |(m : ℝ) - n|) + 2 := by
    intro n _
    by_cases hmn : m = n
    · rw [if_pos hmn, if_pos hmn]; norm_num
    · rw [if_neg hmn, if_neg hmn, atomicWeight, mul_one_div]
  calc _ ≤ ∑ n ∈ Icc 1 N, ((N : ℝ) * (if m = n then 0 else 1 / |(m : ℝ) - n|) + 2) :=
        sum_le_sum hpt
    _ = N * ∑ n ∈ Icc 1 N, (if m = n then 0 else 1 / |(m : ℝ) - n|) + 2 * N := by
        rw [sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul, hcard]; ring
    _ ≤ 2 * N * (1 + Real.log N) + 2 * N := by
        have := row_inv_le_Icc hm
        nlinarith [mul_le_mul_of_nonneg_left this (Nat.cast_nonneg N)]

/-! ### The pole -/

/-- `2(Σ x_n)(Σ n x_n) ≥ −N(2 + log N) Σ n x_n²` over `[1, N]`. -/
theorem pole_ge {N : ℕ} (hN : 1 ≤ N) (x : ℕ → ℝ) :
    -((N : ℝ) * (2 + Real.log N) * ∑ n ∈ Icc 1 N, n * x n ^ 2) ≤
      2 * (∑ n ∈ Icc 1 N, x n) * ∑ n ∈ Icc 1 N, n * x n := by
  set A := ∑ n ∈ Icc 1 N, x n
  set B := ∑ n ∈ Icc 1 N, (n : ℝ) * x n
  set S := ∑ n ∈ Icc 1 N, (n : ℝ) * x n ^ 2
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hS : 0 ≤ S := sum_nonneg fun n _ => by positivity
  -- Cauchy–Schwarz with the weights `1/n` and `n`
  have hA : A ^ 2 ≤ (∑ n ∈ Icc 1 N, 1 / (n : ℝ)) * S := by
    refine sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun n _ => by positivity)
      (fun n _ => by positivity) fun n hn => ?_
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    rw [show 1 / (n : ℝ) * (n * x n ^ 2) = x n ^ 2 by field_simp]
  have hB : B ^ 2 ≤ (∑ n ∈ Icc 1 N, (n : ℝ)) * S := by
    refine sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun n _ => by positivity)
      (fun n _ => by positivity) fun n _ => ?_
    rw [mul_pow]; nlinarith [sq_nonneg (x n), Nat.cast_nonneg (α := ℝ) n]
  have hH : ∑ n ∈ Icc 1 N, 1 / (n : ℝ) ≤ 1 + Real.log N := by
    have h := harmonic_le_one_add_log N
    rw [harmonic_eq_sum_Icc, Rat.cast_sum] at h
    simpa [one_div] using h
  have hsumN : ∑ n ∈ Icc 1 N, (n : ℝ) ≤ N * N := by
    calc ∑ n ∈ Icc 1 N, (n : ℝ) ≤ ∑ _n ∈ Icc 1 N, (N : ℝ) :=
          sum_le_sum fun n hn => by exact_mod_cast (mem_Icc.mp hn).2
      _ = N * N := by rw [sum_const, nsmul_eq_mul, Nat.card_Icc]; push_cast; ring
  have hA' : A ^ 2 ≤ (1 + Real.log N) * S := hA.trans (mul_le_mul_of_nonneg_right hH hS)
  have hB' : B ^ 2 ≤ N * N * S := hB.trans (mul_le_mul_of_nonneg_right hsumN hS)
  -- `2|AB| ≤ N A² + B²/N`
  have hN0 : (0 : ℝ) < N := by linarith
  have hAM : -(N * A ^ 2 + B ^ 2 / N) ≤ 2 * A * B := by
    have h := sq_nonneg (N * A + B)
    have : 0 ≤ (N * A ^ 2 + B ^ 2 / N + 2 * A * B) * N := by
      have e : (N * A ^ 2 + B ^ 2 / N + 2 * A * B) * N = (N * A + B) ^ 2 := by
        field_simp; ring
      rw [e]; exact h
    have := (mul_nonneg_iff_of_pos_right hN0).mp this
    linarith
  have hB'' : B ^ 2 / N ≤ N * S := by
    rw [div_le_iff₀ hN0]; nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hA' hN0.le]

/-! ### The genus of the atomic surface -/

/-- **Hodge index for the atomic surface of degree `N` with genus `4N(1 + log N)`.** -/
theorem genusDefect_Icc_nonneg_of_le {g : ℝ} {N : ℕ} (hN : 1 ≤ N)
    (hg : 4 * N * (1 + Real.log N) ≤ g) (x : ℕ → ℝ) :
    0 ≤ genusDefect g (Icc 1 N) x := by
  set T := Icc 1 N with hT
  set S := ∑ n ∈ T, (n : ℝ) * x n ^ 2 with hSdef
  set ρ : ℝ := 2 * N * (1 + Real.log N) + 2 * N with hρ
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hN'
  have hS : 0 ≤ S := sum_nonneg fun n _ => by positivity
  -- split each off-diagonal term into its pole part and its intersection part
  have hterm : ∀ m ∈ T, ∀ n ∈ T, (if m = n then (0 : ℝ) else
      x m * x n * (((m : ℝ) + n) - frobeniusIntersection m n)) =
      (if m = n then 0 else x m * x n * ((m : ℝ) + n)) -
        (if m = n then 0 else x m * x n * Real.sqrt ((m : ℝ) * n) *
          (RHTower.archLevyDensity |Real.log m - Real.log n| + weilPrimeKernel m n)) := by
    intro m hm n hn
    by_cases hmn : m = n
    · simp [hmn]
    · rw [if_neg hmn, if_neg hmn, if_neg hmn,
        frobeniusIntersection_eq_sqrt_mul (by have := (mem_Icc.mp hm).1; omega)
          (by have := (mem_Icc.mp hn).1; omega)]
      ring
  -- the pole part: `2(Σ x)(Σ n x) − 2 Σ n x²`
  have hpole : ∑ m ∈ T, ∑ n ∈ T, (if m = n then (0 : ℝ) else x m * x n * ((m : ℝ) + n)) =
      2 * (∑ n ∈ T, x n) * (∑ n ∈ T, (n : ℝ) * x n) - 2 * S := by
    have hfull : ∑ m ∈ T, ∑ n ∈ T, x m * x n * ((m : ℝ) + n) =
        2 * (∑ n ∈ T, x n) * (∑ n ∈ T, (n : ℝ) * x n) := by
      have h1 := sum_mul_sum T T (fun m => (m : ℝ) * x m) x
      have h2 := sum_mul_sum T T x (fun n => (n : ℝ) * x n)
      calc ∑ m ∈ T, ∑ n ∈ T, x m * x n * ((m : ℝ) + n)
          = ∑ m ∈ T, ∑ n ∈ T, ((m : ℝ) * x m * x n + x m * ((n : ℝ) * x n)) :=
            sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring
        _ = (∑ m ∈ T, (m : ℝ) * x m) * (∑ n ∈ T, x n) +
              (∑ m ∈ T, x m) * (∑ n ∈ T, (n : ℝ) * x n) := by
            rw [h1, h2, ← sum_add_distrib]; exact sum_congr rfl fun _ _ => sum_add_distrib.symm
        _ = _ := by ring
    have hdiag : ∑ m ∈ T, ∑ n ∈ T, (if m = n then x m * x n * ((m : ℝ) + n) else 0) = 2 * S := by
      rw [hSdef, mul_sum]
      refine sum_congr rfl fun m hm => ?_
      rw [sum_ite_eq T m (fun n => x m * x n * ((m : ℝ) + n)), if_pos hm]
      ring
    have hsplit : ∑ m ∈ T, ∑ n ∈ T, x m * x n * ((m : ℝ) + n) =
        ∑ m ∈ T, ∑ n ∈ T, (if m = n then x m * x n * ((m : ℝ) + n) else 0) +
          ∑ m ∈ T, ∑ n ∈ T, (if m = n then (0 : ℝ) else x m * x n * ((m : ℝ) + n)) := by
      rw [← sum_add_distrib]
      exact sum_congr rfl fun m _ => by
        rw [← sum_add_distrib]; exact sum_congr rfl fun n _ => by split_ifs <;> ring
    linarith
  -- the intersection part is at most `ρ S`
  have hpt : ∀ m ∈ T, ∀ n ∈ T, (if m = n then (0 : ℝ) else x m * x n * Real.sqrt ((m : ℝ) * n) *
      (RHTower.archLevyDensity |Real.log m - Real.log n| + weilPrimeKernel m n)) ≤
      (if m = n then 0 else (m : ℝ) * x m ^ 2 / 2 * atomicWeight N m n) +
        (if n = m then 0 else (n : ℝ) * x n ^ 2 / 2 * atomicWeight N n m) := by
    intro m hm n hn
    by_cases hmn : m = n
    · simp [hmn]
    rw [if_neg hmn, if_neg hmn, if_neg (Ne.symm hmn)]
    have hK0 : 0 ≤ RHTower.archLevyDensity |Real.log m - Real.log n| + weilPrimeKernel m n := by
      have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by have := (mem_Icc.mp hm).1; omega)
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by have := (mem_Icc.mp hn).1; omega)
      have hlogne : Real.log m ≠ Real.log n := fun h =>
        hmn (by exact_mod_cast Real.log_injOn_pos hm0 hn0 h)
      exact add_nonneg (RHTower.archLevyDensity_pos (abs_pos.mpr (sub_ne_zero.mpr hlogne))).le
        (weilPrimeKernel_nonneg m n)
    have hK := kernel_le_atomicWeight hm hn hmn
    have hsym : atomicWeight N n m = atomicWeight N m n := by
      rw [atomicWeight, atomicWeight, abs_sub_comm]
    rw [hsym]
    -- `|x_m x_n| √(mn) ≤ (m x_m² + n x_n²)/2`
    have hmn2 : |x m * x n| * Real.sqrt ((m : ℝ) * n) ≤ ((m : ℝ) * x m ^ 2 + n * x n ^ 2) / 2 := by
      rw [abs_mul, Real.sqrt_mul (Nat.cast_nonneg m)]
      have hsm := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) m)
      have hsn := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) n)
      nlinarith [sq_nonneg (Real.sqrt m * |x m| - Real.sqrt n * |x n|), sq_abs (x m), sq_abs (x n)]
    have hw0 : 0 ≤ atomicWeight N m n := hK0.trans hK
    have hprod : x m * x n * Real.sqrt ((m : ℝ) * n) *
        (RHTower.archLevyDensity |Real.log m - Real.log n| + weilPrimeKernel m n) ≤
        |x m * x n| * Real.sqrt ((m : ℝ) * n) * atomicWeight N m n := by
      have h1 : x m * x n ≤ |x m * x n| := le_abs_self _
      have hs0 : 0 ≤ Real.sqrt ((m : ℝ) * n) := Real.sqrt_nonneg _
      calc x m * x n * Real.sqrt ((m : ℝ) * n) *
            (RHTower.archLevyDensity |Real.log m - Real.log n| + weilPrimeKernel m n)
          ≤ |x m * x n| * Real.sqrt ((m : ℝ) * n) *
            (RHTower.archLevyDensity |Real.log m - Real.log n| + weilPrimeKernel m n) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hs0) hK0
        _ ≤ |x m * x n| * Real.sqrt ((m : ℝ) * n) * atomicWeight N m n :=
            mul_le_mul_of_nonneg_left hK (mul_nonneg (abs_nonneg _) hs0)
    nlinarith [mul_le_mul_of_nonneg_right hmn2 hw0]
  have hrow : ∀ m ∈ T, (m : ℝ) * x m ^ 2 / 2 *
      ∑ n ∈ T, (if m = n then 0 else atomicWeight N m n) ≤ (m : ℝ) * x m ^ 2 / 2 * ρ :=
    fun m hm => mul_le_mul_of_nonneg_left (row_atomicWeight_le hm) (by positivity)
  have hinter : ∑ m ∈ T, ∑ n ∈ T, (if m = n then (0 : ℝ) else
      x m * x n * Real.sqrt ((m : ℝ) * n) *
        (RHTower.archLevyDensity |Real.log m - Real.log n| + weilPrimeKernel m n)) ≤ ρ * S := by
    refine (sum_le_sum fun m hm => sum_le_sum fun n hn => hpt m hm n hn).trans ?_
    simp_rw [sum_add_distrib]
    rw [sum_comm (s := T) (t := T)
      (f := fun m n => if n = m then (0 : ℝ) else (n : ℝ) * x n ^ 2 / 2 * atomicWeight N n m)]
    have hfac : ∀ m ∈ T, ∑ n ∈ T, (if m = n then (0 : ℝ) else
        (m : ℝ) * x m ^ 2 / 2 * atomicWeight N m n) =
        (m : ℝ) * x m ^ 2 / 2 * ∑ n ∈ T, (if m = n then 0 else atomicWeight N m n) := by
      intro m _
      rw [mul_sum]
      exact sum_congr rfl fun n _ => by split_ifs <;> simp
    rw [sum_congr rfl hfac, sum_congr rfl hfac]
    have h1 := sum_le_sum hrow
    have h2 : ∑ m ∈ T, (m : ℝ) * x m ^ 2 / 2 * ρ = ρ / 2 * S := by
      rw [hSdef, mul_sum]; exact sum_congr rfl fun _ _ => by ring
    linarith
  have hpoleb := pole_ge hN x
  unfold genusDefect
  rw [sum_congr rfl fun m hm => sum_congr rfl fun n hn => hterm m hm n hn]
  simp_rw [sum_sub_distrib]
  rw [hpole]
  have hdiag : ∑ n ∈ T, 2 * g * n * x n ^ 2 = 2 * g * S := by
    rw [hSdef, mul_sum]; exact sum_congr rfl fun _ _ => by ring
  rw [hdiag]
  have hgS : (8 * N * (1 + Real.log N)) * S ≤ 2 * g * S :=
    mul_le_mul_of_nonneg_right (by linarith) hS
  have hcoef : (N : ℝ) * (2 + Real.log N) + 2 + ρ ≤ 8 * N * (1 + Real.log N) := by
    rw [hρ]; nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hcoef hS]

/-! ### The lower bound from a dyadic block -/

theorem genusDefect_congr {g : ℝ} {S : Finset ℕ} {x y : ℕ → ℝ} (h : ∀ n ∈ S, x n = y n) :
    genusDefect g S x = genusDefect g S y := by
  unfold genusDefect
  rw [sum_congr rfl fun n hn => by rw [h n hn],
    sum_congr rfl fun m hm => sum_congr rfl fun n hn => by rw [h m hm, h n hn]]

/-- Probes supported on `T ⊆ S` see only `T`. -/
theorem genusDefect_restrict {g : ℝ} {S T : Finset ℕ} (hTS : T ⊆ S) {x : ℕ → ℝ}
    (hx : ∀ n, n ∉ T → x n = 0) : genusDefect g S x = genusDefect g T x := by
  unfold genusDefect
  congr 1
  · exact (sum_subset hTS fun n _ hn => by simp [hx n hn]).symm
  · rw [← sum_subset hTS fun m _ hm => by simp [hx m hm]]
    refine sum_congr rfl fun m _ => (sum_subset hTS fun n _ hn => ?_).symm
    split_ifs <;> simp [hx n hn]

/-- **The atomic surface of degree `N` needs genus `≥ M(log M − 17)/16`, `M = ⌊N/2⌋`.** -/
theorem genus_ge_of_genusDefect_Icc_nonneg {g : ℝ} (hg : 0 ≤ g) {N : ℕ}
    (h : ∀ x : ℕ → ℝ, 0 ≤ genusDefect g (Icc 1 N) x) :
    ((N / 2 : ℕ) : ℝ) * (Real.log (N / 2 : ℕ) - 17) / 16 ≤ g := by
  set M := N / 2 with hM
  rcases Nat.eq_zero_or_pos M with hM0 | hM0
  · rw [hM0]; simpa using hg
  have hsub : Ico M (2 * M) ⊆ Icc 1 N := by
    intro n hn; rw [mem_Ico] at hn; rw [mem_Icc]; omega
  set x : ℕ → ℝ := fun n => if n ∈ Ico M (2 * M) then 1 else 0 with hx
  have h1 := h x
  rw [genusDefect_restrict hsub (fun n hn => by simp [hx, hn]),
    genusDefect_congr (y := 1) (fun n hn => by simp [hx, hn])] at h1
  exact genus_ge_of_genusDefect_nonneg hg h1

end GaloisForLFunctions.SurfaceOfSpecZ
