import GaloisForLFunctions.WindowTowerOfSpecZ.TheAtomicLatticeSeesTheMertensSum
import GaloisForLFunctions.ArithmeticOfSquareRootPrecision.WherePrecisionIsLost
import GaloisForLFunctions.BiScaleUncertainty.ExplicitNyquistPolarAndChebyshevFactorialProducer
import GaloisForLFunctions.RHTower.Sieve.BivariateConvolutionSummatorySwap

/-!
# The atomic lattice has the sharp Schur bound `½ log N`

**The Mangoldt inequality** (`mangoldtHarmonic_le_log`): `Σ_{d≤N} Λ(d)/d ≤ log N` for every `N ≥ 1`.

The proof uses an exact row identity. For `n ≤ N`, with `N = nK + r`, `0 ≤ r < n`,
`Σ_{k≤K} (N − nk) = (N² − nN + r(n − r)) / (2n)`. Summing `Λ(n)` against this and using
`Σ_{d∣m} Λ(d) = log m` gives
`Σ_{m≤N} (N − m) log m ≥ (N²/2) (Σ_{n≤N} Λ(n)/n − ψ(N)/N)`, whence
`M(N) ≤ ψ(N)/N + 2 P(N)/N²` with `P(N) = Σ_{m≤N} (N − m) log m`
(`mangoldtHarmonic_le_psi_add_integrated`). Stirling gives `2P(N)/N² ≤ log N − 3/2 + 2/N`, so only
`ψ(N) ≤ 3N/2 − 2` remains: it follows by doubling from the central-binomial bound on `ψ(2n) − ψ(n)`,
and for `N < 320` from `lcm(1, …, N) ≤ 3^N`.

**The Schur bound** (`abs_sum_vonMangoldt_mul_le_half_log`). Retaining the cutoff `d ≤ N/m` in the
AM–GM split, the row weight at `m` is `M(⌊N/m⌋) + log m ≤ log (N/m) + log m = log N`, so
`|Σ_{k≤N} (Λ * g)(k) g(k)/k| ≤ ½ log N · Σ_{k≤N} g(k)²/k`. On atomic window tests of level `N` this reads
`|⟨ρ_A(Λ)ιg, ιg⟩| ≤ ½ log N ‖ιg‖²` (`abs_integral_windowRep_vonMangoldt_atomic_le_half_log`).
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.WindowTowerOfSpecZ

open CohomologyOfWindowsOfSpecZ ArithmeticFunction

/-- The Mangoldt harmonic sum `M(N) = Σ_{d≤N} Λ(d)/d`. -/
def mangoldtHarmonic (N : ℕ) : ℝ := ∑ d ∈ Icc 1 N, vonMangoldt d / d

/-- The integrated logarithm `P(N) = Σ_{m≤N} (N − m) log m`. -/
def integratedLog (N : ℕ) : ℝ := ∑ m ∈ Icc 1 N, ((N : ℝ) - m) * Real.log m

/-- The divisor expansion of the integrated logarithm. -/
theorem integratedLog_eq_sum (N : ℕ) :
    integratedLog N =
      ∑ n ∈ Icc 1 N, vonMangoldt n * ∑ k ∈ Icc 1 (N / n), ((N : ℝ) - n * k) := by
  have h := RHTower.Sieve.sum_Icc_divisorsAntidiagonal_swap
    (fun a b : ℕ => ((N : ℝ) - ((a * b : ℕ) : ℝ)) * vonMangoldt a) N
  unfold integratedLog
  have hleft : ∀ m ∈ Icc 1 N, ((N : ℝ) - m) * Real.log m =
      ∑ x ∈ m.divisorsAntidiagonal,
        ((N : ℝ) - ((x.1 * x.2 : ℕ) : ℝ)) * vonMangoldt x.1 := by
    intro m _
    have hcongr : ∑ x ∈ m.divisorsAntidiagonal,
        ((N : ℝ) - ((x.1 * x.2 : ℕ) : ℝ)) * vonMangoldt x.1 =
        ((N : ℝ) - m) * ∑ x ∈ m.divisorsAntidiagonal, vonMangoldt x.1 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun x hx => by rw [(Nat.mem_divisorsAntidiagonal.mp hx).1]
    rw [hcongr, Nat.sum_divisorsAntidiagonal (fun a _ => vonMangoldt a), vonMangoldt_sum]
  rw [Finset.sum_congr rfl hleft, h]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  push_cast
  ring

/-- The arithmetic progression of one row. -/
theorem sum_row_eq (N n K : ℕ) :
    ∑ k ∈ Icc 1 K, ((N : ℝ) - n * k) = K * N - n * (K * (K + 1) / 2) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    push_cast
    ring

/-- **The row inequality**: `1/n − 1/N ≤ (2/N²) Σ_{k≤⌊N/n⌋} (N − nk)`, with defect `r(n − r)` for
`N = n⌊N/n⌋ + r`. -/
theorem row_le {N n : ℕ} (hn : 1 ≤ n) (hN : 1 ≤ N) :
    (1 : ℝ) / n - 1 / N ≤ 2 / (N : ℝ) ^ 2 * ∑ k ∈ Icc 1 (N / n), ((N : ℝ) - n * k) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [sum_row_eq]
  set K := N / n with hK
  set r := N % n with hr
  have hdecomp : (N : ℝ) = n * K + r := by
    have := Nat.div_add_mod N n
    exact_mod_cast this.symm
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hrn : (r : ℝ) ≤ n := by
    exact_mod_cast (Nat.mod_lt N hn).le
  have hprod : 0 ≤ (r : ℝ) * (n - r) := mul_nonneg hr0 (sub_nonneg.mpr hrn)
  have hkey : (N : ℝ) ^ 2 - n * N ≤ 2 * n * (K * N - n * (K * (K + 1) / 2)) := by
    rw [hdecomp]
    nlinarith only [hprod]
  rw [div_sub_div _ _ hn0.ne' hN0.ne', div_mul_eq_mul_div, div_le_div_iff₀ (by positivity)
    (by positivity)]
  have hN2 : 0 < (N : ℝ) ^ 2 := by positivity
  nlinarith only [mul_le_mul_of_nonneg_left hkey hN0.le, hN0, hn0]

/-- **The comparison** `M(N) ≤ ψ(N)/N + 2 P(N)/N²`. -/
theorem mangoldtHarmonic_le_psi_add_integrated {N : ℕ} (hN : 1 ≤ N) :
    mangoldtHarmonic N ≤
      (∑ n ∈ Icc 1 N, vonMangoldt n) / N + 2 / (N : ℝ) ^ 2 * integratedLog N := by
  rw [integratedLog_eq_sum, Finset.sum_div, Finset.mul_sum, ← Finset.sum_add_distrib]
  unfold mangoldtHarmonic
  refine Finset.sum_le_sum fun n hn => ?_
  have hΛ : 0 ≤ vonMangoldt n := vonMangoldt_nonneg
  have hrow := mul_le_mul_of_nonneg_left (row_le (Finset.mem_Icc.mp hn).1 hN) hΛ
  have e1 : vonMangoldt n * ((1 : ℝ) / n - 1 / N) = vonMangoldt n / n - vonMangoldt n / N := by
    ring
  have e2 : vonMangoldt n * (2 / (N : ℝ) ^ 2 * ∑ k ∈ Icc 1 (N / n), ((N : ℝ) - n * k)) =
      2 / (N : ℝ) ^ 2 * (vonMangoldt n * ∑ k ∈ Icc 1 (N / n), ((N : ℝ) - n * k)) := by ring
  rw [e1, e2] at hrow
  linarith only [hrow]

theorem sum_log_eq_log_factorial (N : ℕ) :
    ∑ m ∈ Icc 1 N, Real.log m = Real.log (N.factorial : ℕ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Nat.factorial_succ, Nat.cast_mul,
      Real.log_mul (by exact_mod_cast (Nat.succ_ne_zero N))
        (by exact_mod_cast (Nat.factorial_ne_zero N))]
    ring

/-- One step of the integrated logarithm is the logarithm of the factorial. -/
theorem integratedLog_succ (N : ℕ) :
    integratedLog (N + 1) = integratedLog N + Real.log (N.factorial : ℕ) := by
  unfold integratedLog
  rw [Finset.sum_Icc_succ_top (by omega), ← sum_log_eq_log_factorial, ← Finset.sum_add_distrib]
  push_cast
  rw [sub_self, zero_mul, add_zero]
  refine Finset.sum_congr rfl fun m _ => ?_
  ring

/-- **Integrated Stirling**: `P(N) ≤ ½N² log N − ¾N² + N`. -/
theorem integratedLog_le {N : ℕ} (hN : 1 ≤ N) :
    integratedLog N ≤ (N : ℝ) ^ 2 * Real.log N / 2 - 3 * (N : ℝ) ^ 2 / 4 + N := by
  induction N, hN using Nat.le_induction with
  | base => simp [integratedLog]; norm_num
  | succ N hN ih =>
    rw [integratedLog_succ]
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have hfac := (ArithmeticOfSquareRootPrecision.log_factorial_sub_bounds hN).2
    have hstep : 2 / (2 * (N : ℝ) + 1) ≤ Real.log ((N : ℝ) + 1) - Real.log N := by
      have h := Real.le_log_one_add_of_nonneg (x := 1 / (N : ℝ)) (by positivity)
      have e1 : 2 * (1 / (N : ℝ)) / (1 / (N : ℝ) + 2) = 2 / (2 * (N : ℝ) + 1) := by
        field_simp
        ring
      have e2 : Real.log (1 + 1 / (N : ℝ)) = Real.log ((N : ℝ) + 1) - Real.log N := by
        rw [← Real.log_div (by positivity) hN0.ne']
        congr 1
        field_simp
      rwa [e1, e2] at h
    have hpos : 0 < 2 * (N : ℝ) + 1 := by positivity
    have hquot : (N : ℝ) / 2 + 3 / 4 ≤ ((N : ℝ) + 1) ^ 2 / 2 * (2 / (2 * (N : ℝ) + 1)) := by
      have e : ((N : ℝ) + 1) ^ 2 / 2 * (2 / (2 * (N : ℝ) + 1)) =
          ((N : ℝ) + 1) ^ 2 / (2 * (N : ℝ) + 1) := by ring
      rw [e, le_div_iff₀ hpos]
      nlinarith only [hN0]
    have hlog := mul_le_mul_of_nonneg_left hstep
      (show 0 ≤ ((N : ℝ) + 1) ^ 2 / 2 by positivity)
    push_cast
    nlinarith only [ih, hfac, hquot, hlog]

/-- The base range of the doubling: `lcm(1, …, n) ≤ 3 ^ n` for `n < 320`. -/
theorem lcmUpto_le_three_pow : ∀ n : ℕ, n < 320 → Nat.lcmUpto n ≤ 3 ^ n := by
  decide +kernel

/-- `ψ(n) = Σ_{m≤n} Λ(m)` agrees with Mathlib's Chebyshev function at natural points. -/
theorem sum_vonMangoldt_eq_psi (n : ℕ) :
    ∑ m ∈ Icc 1 n, vonMangoldt m = Chebyshev.psi n := by
  rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast]
  rw [show Icc 0 n = insert 0 (Icc 1 n) by
    ext x; simp only [mem_Icc, mem_insert]; omega]
  rw [Finset.sum_insert (by simp)]
  simp

/-- The three smallest levels, from `lcm(1, 2, 3, 4) = 12`. -/
private theorem sum_vonMangoldt_le_tiny {n : ℕ} (h2 : 2 ≤ n) (h5 : n < 5) :
    ∑ m ∈ Icc 1 n, vonMangoldt m ≤ 3 / 2 * (n : ℝ) - 2 := by
  rw [sum_vonMangoldt_eq_psi, Chebyshev.psi_eq_log_lcmUpto]
  have hlog2 := Real.log_two_lt_d9
  have hpow (a b : ℕ) (ha : 0 < a) (hab : a ≤ 2 ^ b) : Real.log a ≤ b * Real.log 2 := by
    have h := Real.log_le_log (x := (a : ℝ)) (y := 2 ^ b) (by exact_mod_cast ha)
      (by exact_mod_cast hab)
    rwa [Real.log_pow] at h
  interval_cases n
  · have : Nat.lcmUpto 2 = 2 := by decide +kernel
    rw [this]
    have h := hpow 2 1 (by norm_num) (by norm_num)
    push_cast at h ⊢
    linarith only [h, hlog2]
  · have : Nat.lcmUpto 3 = 6 := by decide +kernel
    rw [this]
    have h := hpow 6 3 (by norm_num) (by norm_num)
    push_cast at h ⊢
    linarith only [h, hlog2]
  · have : Nat.lcmUpto 4 = 12 := by decide +kernel
    rw [this]
    have h := hpow 12 4 (by norm_num) (by norm_num)
    push_cast at h ⊢
    linarith only [h, hlog2]

/-- Below `320` the lcm bound gives `ψ(n) ≤ 3n/2 − 2` from `n = 5` on. -/
private theorem sum_vonMangoldt_le_small {n : ℕ} (h5 : 5 ≤ n) (h : n < 320) :
    ∑ m ∈ Icc 1 n, vonMangoldt m ≤ 3 / 2 * (n : ℝ) - 2 := by
  rw [sum_vonMangoldt_eq_psi, Chebyshev.psi_eq_log_lcmUpto]
  have hlcm := lcmUpto_le_three_pow n h
  have hpos : (0 : ℝ) < Nat.lcmUpto n := by exact_mod_cast Nat.lcmUpto_pos n
  have hle : (Nat.lcmUpto n : ℝ) ≤ (3 : ℝ) ^ n := by exact_mod_cast hlcm
  have hlog := Real.log_le_log hpos hle
  rw [Real.log_pow] at hlog
  have hlog3 : Real.log 3 ≤ 11 / 10 := by
    have h1 : Real.log 3 ≤ (8 / 5) * Real.log 2 := by
      have h35 := Real.log_le_log (by norm_num : (0 : ℝ) < 3 ^ 5)
        (by norm_num : (3 : ℝ) ^ 5 ≤ 2 ^ 8)
      rw [Real.log_pow, Real.log_pow] at h35
      push_cast at h35
      linarith only [h35]
    have h2 := Real.log_two_lt_d9
    have hsharp : Real.log 3 ≤ (65 / 41) * Real.log 2 := by
      have h35 := Real.log_le_log (by norm_num : (0 : ℝ) < 3 ^ 41)
        (by norm_num : (3 : ℝ) ^ 41 ≤ 2 ^ 65)
      rw [Real.log_pow, Real.log_pow] at h35
      push_cast at h35
      linarith only [h35]
    linarith only [hsharp, h2]
  have hn5 : (5 : ℝ) ≤ n := by exact_mod_cast h5
  nlinarith only [hlog, hlog3, hn5]

/-- `3 log (2n + 1) ≤ (1136/10000) n + 1/2` for `n ≥ 159`, by the tangent line of the logarithm
at `150`. -/
private theorem three_log_le {n : ℕ} (hn : 159 ≤ n) :
    3 * Real.log (2 * (n : ℝ) + 1) ≤ 1136 / 10000 * (n : ℝ) + 1 / 2 := by
  have hn0 : (159 : ℝ) ≤ n := by exact_mod_cast hn
  have htan := Real.log_le_sub_one_of_pos (show 0 < (2 * (n : ℝ) + 1) / 150 by positivity)
  rw [Real.log_div (by positivity) (by norm_num)] at htan
  have hlog150 : Real.log 150 ≤ (29 / 4) * Real.log 2 := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 150 ^ 4)
      (by norm_num : (150 : ℝ) ^ 4 ≤ 2 ^ 29)
    rw [Real.log_pow, Real.log_pow] at h
    push_cast at h
    linarith only [h]
  have h2 := Real.log_two_lt_d9
  linarith only [htan, hlog150, h2, hn0]

/-- **The Chebyshev budget** `ψ(N) ≤ 3N/2 − 2` for every `N ≥ 2`: doubling from `N < 320`. -/
theorem sum_vonMangoldt_le {N : ℕ} (hN : 2 ≤ N) :
    ∑ m ∈ Icc 1 N, vonMangoldt m ≤ 3 / 2 * (N : ℝ) - 2 := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    by_cases htiny : N < 5
    · exact sum_vonMangoldt_le_tiny hN htiny
    push Not at htiny
    by_cases hsmall : N < 320
    · exact sum_vonMangoldt_le_small htiny hsmall
    push Not at hsmall
    have h2 := Real.log_two_lt_d9
    have hdouble (n : ℕ) (hn : 159 ≤ n) (hnN : n < N) :
        ∑ m ∈ Icc 1 (2 * n), vonMangoldt m ≤ 3 * (n : ℝ) - 2 -
          (1136 / 10000 * (n : ℝ) - 2 * Real.log (2 * (n : ℝ) + 1) - 1) := by
      have hstep := BiScaleUncertainty.chebyshevPsi_two_mul_sub_le_linear_add_log
        (show 1 ≤ n by omega)
      have hih := ih n hnN (by omega)
      unfold _root_.RHTower.chebyshevPsi at hstep
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have hmul : (2 * Real.log 2) * (n : ℝ) ≤ (2 * 0.6931471808) * (n : ℝ) :=
        mul_le_mul_of_nonneg_right (by linarith only [h2]) hn0
      norm_num at hmul
      linarith only [hstep, hih, hmul]
    rcases Nat.even_or_odd' N with ⟨n, rfl | rfl⟩
    · have hn : 159 ≤ n := by omega
      have hd := hdouble n hn (by omega)
      have hlog := three_log_le hn
      have hn0 : (159 : ℝ) ≤ n := by exact_mod_cast hn
      push_cast
      linarith only [hd, hlog, hn0]
    · have hn : 159 ≤ n := by omega
      have hd := hdouble n hn (by omega)
      have hlog := three_log_le hn
      have hsucc : ∑ m ∈ Icc 1 (2 * n + 1), vonMangoldt m =
          ∑ m ∈ Icc 1 (2 * n), vonMangoldt m + vonMangoldt (2 * n + 1) :=
        Finset.sum_Icc_succ_top (by omega) _
      have hΛ : vonMangoldt (2 * n + 1) ≤ Real.log (2 * (n : ℝ) + 1) := by
        have := vonMangoldt_le_log (n := 2 * n + 1)
        push_cast at this
        exact this
      rw [hsucc]
      push_cast
      linarith only [hd, hlog, hΛ]

/-- **The Mangoldt inequality** `Σ_{d≤N} Λ(d)/d ≤ log N` for every `N ≥ 1`. -/
theorem mangoldtHarmonic_le_log {N : ℕ} (hN : 1 ≤ N) : mangoldtHarmonic N ≤ Real.log N := by
  rcases Nat.lt_or_ge N 2 with h1 | h2
  · obtain rfl : N = 1 := by omega
    simp [mangoldtHarmonic]
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hcomp := mangoldtHarmonic_le_psi_add_integrated hN
  have hpsi := sum_vonMangoldt_le h2
  have hint := integratedLog_le hN
  have h1 : (∑ n ∈ Icc 1 N, vonMangoldt n) / N ≤ 3 / 2 - 2 / N := by
    rw [div_le_iff₀ hN0]
    have e : (3 / 2 - 2 / (N : ℝ)) * N = 3 / 2 * N - 2 := by field_simp
    rw [e]
    exact hpsi
  have h2 : 2 / (N : ℝ) ^ 2 * integratedLog N ≤ Real.log N - 3 / 2 + 2 / N := by
    have hcoef : 0 ≤ 2 / (N : ℝ) ^ 2 := by positivity
    refine (mul_le_mul_of_nonneg_left hint hcoef).trans_eq ?_
    field_simp
    ring
  linarith only [hcomp, h1, h2]

/-- **The sharp Schur bound on the truncated Dirichlet ring**. -/
theorem abs_sum_vonMangoldt_mul_le_half_log (N : ℕ) (g : ArithmeticFunction ℝ) :
    |∑ k ∈ Icc 1 N, (vonMangoldt * g) k * g k / k| ≤
      Real.log N / 2 * ∑ k ∈ Icc 1 N, g k ^ 2 / k := by
  have hexp : ∑ k ∈ Icc 1 N, (Λ * g) k * g k / k =
      ∑ x ∈ (Icc 1 N ×ˢ Icc 1 N).filter (fun x => x.1 * x.2 ≤ N),
        Λ x.1 * g x.2 * g (x.1 * x.2) / ((x.1 * x.2 : ℕ) : ℝ) := by
    rw [← sum_Icc_divisorsAntidiagonal]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ArithmeticFunction.mul_apply, Finset.sum_mul, Finset.sum_div]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [(Nat.mem_divisorsAntidiagonal.mp hx).1]
  set S := (Icc 1 N ×ˢ Icc 1 N).filter (fun x => x.1 * x.2 ≤ N) with hS
  -- the first half regroups by `m`: the Mertens sum up to `N/m`
  have hfirst : ∑ x ∈ S, (Λ x.1 / x.1) * (g x.2 ^ 2 / x.2) / 2 =
      ∑ m ∈ Icc 1 N, (mangoldtHarmonic (N / m) / 2) * (g m ^ 2 / m) := by
    rw [hS, Finset.sum_filter, Finset.sum_product_right]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm1 := (Finset.mem_Icc.mp hm).1
    unfold mangoldtHarmonic
    rw [Finset.sum_div, Finset.sum_mul, ← Finset.sum_filter]
    have hset : (Icc 1 N).filter (fun d => d * m ≤ N) = Icc 1 (N / m) := by
      ext d
      simp only [Finset.mem_filter, Finset.mem_Icc, Nat.le_div_iff_mul_le hm1]
      constructor
      · rintro ⟨⟨h1, _⟩, h3⟩
        exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩
        refine ⟨⟨h1, ?_⟩, h3⟩
        nlinarith only [h3, hm1]
    rw [hset]
    refine Finset.sum_congr rfl fun d _ => ?_
    ring
  -- the second half regroups by `k = dm`: `Σ_{d∣k} Λ(d) = log k`
  have hsecond : ∑ x ∈ S, Λ x.1 * (g (x.1 * x.2) ^ 2 / ((x.1 * x.2 : ℕ) : ℝ)) / 2 =
      ∑ k ∈ Icc 1 N, (Real.log k / 2) * (g k ^ 2 / k) := by
    rw [hS, ← sum_Icc_divisorsAntidiagonal N (fun x => Λ x.1 * (g (x.1 * x.2) ^ 2 /
      ((x.1 * x.2 : ℕ) : ℝ)) / 2)]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hcongr : ∑ x ∈ k.divisorsAntidiagonal, Λ x.1 * (g (x.1 * x.2) ^ 2 /
        ((x.1 * x.2 : ℕ) : ℝ)) / 2 =
        (∑ x ∈ k.divisorsAntidiagonal, Λ x.1) * (g k ^ 2 / k) / 2 := by
      rw [Finset.sum_mul, Finset.sum_div]
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [(Nat.mem_divisorsAntidiagonal.mp hx).1]
    rw [hcongr, Nat.sum_divisorsAntidiagonal (fun a _ => Λ a), vonMangoldt_sum]
    ring
  have hrow : ∀ m ∈ Icc 1 N, mangoldtHarmonic (N / m) + Real.log m ≤ Real.log N := by
    intro m hm
    obtain ⟨hm1, hmN⟩ := Finset.mem_Icc.mp hm
    have hK : 1 ≤ N / m := (Nat.one_le_div_iff hm1).mpr hmN
    have hM := mangoldtHarmonic_le_log hK
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
    have hK0 : (0 : ℝ) < ((N / m : ℕ) : ℝ) := by exact_mod_cast hK
    have hprod : (((N / m : ℕ) : ℝ)) * m ≤ N := by
      exact_mod_cast Nat.div_mul_le_self N m
    have hlog := Real.log_le_log (mul_pos hK0 hm0) hprod
    rw [Real.log_mul hK0.ne' hm0.ne'] at hlog
    linarith only [hM, hlog]
  have hsplit : ∀ x ∈ S, Λ x.1 * (g x.2 ^ 2 + g (x.1 * x.2) ^ 2) / 2 / ((x.1 * x.2 : ℕ) : ℝ) =
      (Λ x.1 / x.1) * (g x.2 ^ 2 / x.2) / 2 +
        Λ x.1 * (g (x.1 * x.2) ^ 2 / ((x.1 * x.2 : ℕ) : ℝ)) / 2 := fun x hx => by
    obtain ⟨hp, _⟩ := Finset.mem_filter.mp hx
    obtain ⟨h1, h2⟩ := Finset.mem_product.mp hp
    have ha : (0 : ℝ) < x.1 := by exact_mod_cast (Finset.mem_Icc.mp h1).1
    have hb : (0 : ℝ) < x.2 := by exact_mod_cast (Finset.mem_Icc.mp h2).1
    rw [Nat.cast_mul]
    field_simp
  rw [hexp]
  calc |∑ x ∈ S, Λ x.1 * g x.2 * g (x.1 * x.2) / ((x.1 * x.2 : ℕ) : ℝ)|
      ≤ ∑ x ∈ S, |Λ x.1 * g x.2 * g (x.1 * x.2) / ((x.1 * x.2 : ℕ) : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x ∈ S, Λ x.1 * (g x.2 ^ 2 + g (x.1 * x.2) ^ 2) / 2 / ((x.1 * x.2 : ℕ) : ℝ) :=
        Finset.sum_le_sum fun x _ => abs_term_le x.1 x.2 g
    _ = ∑ x ∈ S, ((Λ x.1 / x.1) * (g x.2 ^ 2 / x.2) / 2 +
          Λ x.1 * (g (x.1 * x.2) ^ 2 / ((x.1 * x.2 : ℕ) : ℝ)) / 2) := Finset.sum_congr rfl hsplit
    _ = ∑ m ∈ Icc 1 N, ((mangoldtHarmonic (N / m) + Real.log m) / 2) * (g m ^ 2 / m) := by
        rw [Finset.sum_add_distrib, hfirst, hsecond, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun m _ => ?_
        ring
    _ ≤ ∑ m ∈ Icc 1 N, (Real.log N / 2) * (g m ^ 2 / m) := by
        refine Finset.sum_le_sum fun m hm => ?_
        have hw : 0 ≤ g m ^ 2 / (m : ℝ) := div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
        exact mul_le_mul_of_nonneg_right (by linarith only [hrow m hm]) hw
    _ = _ := by rw [Finset.mul_sum]

/-- **The sharp atomic bound**: on atomic window tests of level `N`,
`|⟨ρ_A(Λ)ιg, ιg⟩| ≤ ½ log N · ‖ιg‖²`. -/
theorem abs_integral_windowRep_vonMangoldt_atomic_le_half_log {A : ℝ} {N : ℕ} {φ : ℝ → ℝ} {δ : ℝ}
    (hA : windowLevel A = N) (hφ : IsAtomProfile N δ φ) (hc : Continuous φ)
    (g : ArithmeticFunction ℝ) :
    |∫ u, windowRepFun A vonMangoldt (atomicEmbedding N φ g) u * atomicEmbedding N φ g u| ≤
      Real.log N / 2 * ∫ u, atomicEmbedding N φ g u ^ 2 := by
  have hnorm : ∫ u, atomicEmbedding N φ g u ^ 2 =
      (∫ v, φ v ^ 2) * ∑ k ∈ Icc 1 N, g k ^ 2 / k := by
    have h := integral_atomicEmbedding_mul hφ hc g g
    simp only [← sq] at h
    exact h
  rw [integral_windowRep_atomicEmbedding hA hφ hc, hnorm, abs_mul,
    abs_of_nonneg (MeasureTheory.integral_nonneg fun v => sq_nonneg _)]
  have hb := abs_sum_vonMangoldt_mul_le_half_log N g
  have hsq : 0 ≤ ∫ v, φ v ^ 2 := MeasureTheory.integral_nonneg fun v => sq_nonneg _
  calc (∫ v, φ v ^ 2) * |∑ k ∈ Icc 1 N, (vonMangoldt * g) k * g k / k|
      ≤ (∫ v, φ v ^ 2) * (Real.log N / 2 * ∑ k ∈ Icc 1 N, g k ^ 2 / k) :=
        mul_le_mul_of_nonneg_left hb hsq
    _ = _ := by ring

end GaloisForLFunctions.WindowTowerOfSpecZ

#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.mangoldtHarmonic_le_log
#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.abs_integral_windowRep_vonMangoldt_atomic_le_half_log
