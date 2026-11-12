import GaloisForLFunctions.PrimeExponentialSums.VinogradovMinorArc
import GaloisForLFunctions.LogarithmicChowla.DiscreteFourier

/-!
# From von Mangoldt sums to prime sums

Abel summation against `g(n) = e(nθ)/log n` turns bounds for partial sums of `Λ(n) f(n)` into
bounds for prime sums `Σ_{P < p ≤ Q} f(p) e(pθ)`.

* **Abel** (`norm_sum_mul_le_of_partial`): partial sums at most `B` give
  `|Σ a(n) g(n)| ≤ B (|g(Q)| + Σ |Δg|)`; for `g(n) = e(nθ)/log n` the bracket is at most
  `(2 + 2π|θ|(Q − P))/log P` (`weight_bounds`).
* **Twisted primes** (`norm_sum_primes_le_of_windows`): for `|f| ≤ 1`,
  `|Σ_{P < p ≤ Q} f(p) e(pθ)| ≤ B (2 + 2π|θ|(Q − P))/log P + (ψ(Q) − θ(Q))/log 2`; the last term
  pays for the proper prime powers, where `Λ(n)/log n ≤ 1/log 2`.
* **Untwisted primes** (`norm_sum_primes_ex_le`): for `0 < |θ| ≤ 1/2` and
  `|θ(t) − θ(P) − (t − P)| ≤ E` on `[P, Q]`,
  `|Σ_{P < p ≤ Q} e(pθ)| ≤ E (2 + 2π|θ|(Q − P))/log P + 1/(2|θ| log P)`: the primes are the
  integers weighted by `1/log n` (geometric sums, `|Σ e(nθ)| ≤ 1/(2|θ|)`) plus the PNT remainder.
-/

open Finset ArithmeticFunction
open GaloisForLFunctions.LogarithmicChowla
open scoped BigOperators

namespace GaloisForLFunctions.PrimeExponentialSums

noncomputable section
set_option autoImplicit false

/-- **Abel summation.** With `S(t) = Σ_{P < n ≤ t} a(n)`,
`Σ_{P < n ≤ Q} a(n) g(n) = S(Q) g(Q) − Σ_{P ≤ n < Q} S(n)(g(n+1) − g(n))`. -/
theorem sum_Ioc_mul_eq_abel (a g : ℕ → ℂ) (P Q : ℕ) (hPQ : P ≤ Q) :
    ∑ n ∈ Ioc P Q, a n * g n = (∑ m ∈ Ioc P Q, a m) * g Q -
      ∑ n ∈ Ico P Q, (∑ m ∈ Ioc P n, a m) * (g (n + 1) - g n) := by
  induction Q, hPQ using Nat.le_induction with
  | base => simp
  | succ Q hQ ih =>
    rw [sum_Ioc_succ_top hQ, sum_Ioc_succ_top hQ, sum_Ico_succ_top hQ, ih]
    ring

/-- **Abel's bound.** If every partial sum `S(t)`, `P ≤ t ≤ Q`, is at most `B`, then
`|Σ_{P < n ≤ Q} a(n) g(n)| ≤ B (|g(Q)| + Σ_{P ≤ n < Q} |g(n+1) − g(n)|)`. -/
theorem norm_sum_mul_le_of_partial (a g : ℕ → ℂ) {P Q : ℕ} (hPQ : P ≤ Q) {B : ℝ}
    (hB : ∀ t, P ≤ t → t ≤ Q → ‖∑ m ∈ Ioc P t, a m‖ ≤ B) :
    ‖∑ n ∈ Ioc P Q, a n * g n‖ ≤ B * (‖g Q‖ + ∑ n ∈ Ico P Q, ‖g (n + 1) - g n‖) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB P le_rfl hPQ)
  rw [sum_Ioc_mul_eq_abel a g P Q hPQ]
  refine (norm_sub_le _ _).trans ?_
  rw [mul_add, norm_mul]
  refine add_le_add (mul_le_mul_of_nonneg_right (hB Q hPQ le_rfl) (norm_nonneg _)) ?_
  refine (norm_sum_le _ _).trans ?_
  rw [mul_sum]
  refine sum_le_sum fun n hn => ?_
  rw [norm_mul]
  have hn' := mem_Ico.mp hn
  exact mul_le_mul_of_nonneg_right (hB n hn'.1 hn'.2.le) (norm_nonneg _)

/-- `|e(x + θ) − e(x)| ≤ 2π|θ|`. -/
theorem norm_ex_add_sub_le (x θ : ℝ) : ‖ex (x + θ) - ex x‖ ≤ 2 * Real.pi * |θ| := by
  rw [ex_add, show ex x * ex θ - ex x = ex x * (ex θ - 1) by ring, norm_mul, norm_ex, one_mul]
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2 * Real.pi * θ)
  rw [ex]
  have e : (2 * (Real.pi : ℂ) * Complex.I * θ) = Complex.I * ((2 * Real.pi * θ : ℝ) : ℂ) := by
    push_cast; ring
  rw [e]
  refine h.trans (le_of_eq ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]

/-- Telescoping: `Σ_{P ≤ n < Q} (1/log n − 1/log (n+1)) = 1/log P − 1/log Q`. -/
theorem sum_Ico_inv_log_sub {P Q : ℕ} (hPQ : P ≤ Q) :
    ∑ n ∈ Ico P Q, (1 / Real.log n - 1 / Real.log (n + 1 : ℕ))
      = 1 / Real.log P - 1 / Real.log Q := by
  induction Q, hPQ using Nat.le_induction with
  | base => simp
  | succ Q hQ ih =>
    rw [sum_Ico_succ_top hQ, ih]
    ring

/-- The weight `g(n) = e(nθ)/log n`: its last value and total variation on `[P, Q]`. -/
theorem weight_bounds {P Q : ℕ} (hP : 2 ≤ P) (hPQ : P ≤ Q) (θ : ℝ) :
    ‖ex (Q * θ) / (Real.log Q : ℂ)‖ +
        ∑ n ∈ Ico P Q, ‖ex ((n + 1 : ℕ) * θ) / (Real.log (n + 1 : ℕ) : ℂ) -
          ex (n * θ) / (Real.log n : ℂ)‖
      ≤ (2 + 2 * Real.pi * |θ| * (Q - P)) / Real.log P := by
  have hlogP : 0 < Real.log P := Real.log_pos (by exact_mod_cast (show 1 < P by omega))
  have hlogmono : ∀ m : ℕ, P ≤ m → Real.log P ≤ Real.log m := fun m hm =>
    Real.log_le_log (by exact_mod_cast (show 0 < P by omega)) (by exact_mod_cast hm)
  have hlast : ‖ex (Q * θ) / (Real.log Q : ℂ)‖ ≤ 1 / Real.log P := by
    rw [norm_div, norm_ex, Complex.norm_real, Real.norm_of_nonneg (hlogP.le.trans (hlogmono Q hPQ))]
    exact div_le_div_of_nonneg_left zero_le_one hlogP (hlogmono Q hPQ)
  have hstep : ∀ n ∈ Ico P Q, ‖ex ((n + 1 : ℕ) * θ) / (Real.log (n + 1 : ℕ) : ℂ) -
      ex (n * θ) / (Real.log n : ℂ)‖ ≤ 2 * Real.pi * |θ| / Real.log P +
        (1 / Real.log n - 1 / Real.log (n + 1 : ℕ)) := by
    intro n hn
    have hnP : P ≤ n := (mem_Ico.mp hn).1
    have hln : Real.log P ≤ Real.log n := hlogmono n hnP
    have hln1 : Real.log P ≤ Real.log (n + 1 : ℕ) := hlogmono (n + 1) (by omega)
    have hln0 : 0 < Real.log n := lt_of_lt_of_le hlogP hln
    have hln10 : 0 < Real.log (n + 1 : ℕ) := lt_of_lt_of_le hlogP hln1
    have hlog_le : Real.log n ≤ Real.log (n + 1 : ℕ) :=
      Real.log_le_log (by exact_mod_cast (show 0 < n by omega)) (by exact_mod_cast (by omega))
    have hsplit : ex ((n + 1 : ℕ) * θ) / (Real.log (n + 1 : ℕ) : ℂ) - ex (n * θ) / (Real.log n : ℂ)
        = (ex ((n + 1 : ℕ) * θ) - ex (n * θ)) / (Real.log (n + 1 : ℕ) : ℂ) +
          ex (n * θ) * ((1 / Real.log (n + 1 : ℕ) - 1 / Real.log n : ℝ) : ℂ) := by
      have h1 : (Real.log (n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hln10.ne'
      have h2 : (Real.log n : ℂ) ≠ 0 := by exact_mod_cast hln0.ne'
      push_cast
      field_simp
      ring
    rw [hsplit]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hln10.le]
      have hd : ‖ex ((n + 1 : ℕ) * θ) - ex (n * θ)‖ ≤ 2 * Real.pi * |θ| := by
        have := norm_ex_add_sub_le (n * θ) θ
        rwa [show (n : ℝ) * θ + θ = ((n + 1 : ℕ) : ℝ) * θ by push_cast; ring] at this
      calc ‖ex ((n + 1 : ℕ) * θ) - ex (n * θ)‖ / Real.log (n + 1 : ℕ)
          ≤ 2 * Real.pi * |θ| / Real.log (n + 1 : ℕ) := div_le_div_of_nonneg_right hd hln10.le
        _ ≤ 2 * Real.pi * |θ| / Real.log P :=
            div_le_div_of_nonneg_left (by positivity) hlogP hln1
    · rw [norm_mul, norm_ex, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm,
        abs_of_nonneg]
      rw [sub_nonneg]
      exact div_le_div_of_nonneg_left zero_le_one hln0 hlog_le
  have htel := sum_Ico_inv_log_sub hPQ
  have hQ0 : 0 ≤ 1 / Real.log Q := by
    have := hlogmono Q hPQ
    positivity
  calc ‖ex (Q * θ) / (Real.log Q : ℂ)‖ + ∑ n ∈ Ico P Q, ‖ex ((n + 1 : ℕ) * θ) /
        (Real.log (n + 1 : ℕ) : ℂ) - ex (n * θ) / (Real.log n : ℂ)‖
      ≤ 1 / Real.log P + ∑ n ∈ Ico P Q, (2 * Real.pi * |θ| / Real.log P +
          (1 / Real.log n - 1 / Real.log (n + 1 : ℕ))) := add_le_add hlast (sum_le_sum hstep)
    _ = 1 / Real.log P + ((Q - P : ℕ) * (2 * Real.pi * |θ| / Real.log P) +
          (1 / Real.log P - 1 / Real.log Q)) := by
        rw [sum_add_distrib, htel, sum_const, Nat.card_Ico, nsmul_eq_mul]
    _ ≤ (2 + 2 * Real.pi * |θ| * (Q - P)) / Real.log P := by
        rw [Nat.cast_sub hPQ]
        have e : 1 / Real.log P + (((Q : ℝ) - P) * (2 * Real.pi * |θ| / Real.log P) +
            (1 / Real.log P - 1 / Real.log Q)) = (2 + 2 * Real.pi * |θ| * (Q - P)) / Real.log P
              - 1 / Real.log Q := by
          field_simp; ring
        rw [e]
        linarith

/-- Off the primes, `ψ(Q) − θ(Q)` is the von Mangoldt mass of the proper prime powers. -/
theorem sum_vonMangoldt_not_prime_eq (Q : ℕ) :
    ∑ n ∈ (Ioc 0 Q).filter (fun n => ¬ n.Prime), vonMangoldt n
      = Chebyshev.psi Q - Chebyshev.theta Q := by
  rw [Chebyshev.psi, Chebyshev.theta, Nat.floor_natCast,
    ← sum_filter_add_sum_filter_not (Ioc 0 Q) Nat.Prime (fun n => vonMangoldt n)]
  have h : ∑ n ∈ (Ioc 0 Q).filter Nat.Prime, vonMangoldt n
      = ∑ p ∈ (Ioc 0 Q).filter Nat.Prime, Real.log p :=
    sum_congr rfl fun n hn => vonMangoldt_apply_prime (mem_filter.mp hn).2
  rw [h]
  ring

/-- `(ψ(Q) − θ(Q))/log 2 ≤ 3√Q log Q`. -/
theorem psi_sub_theta_div_log_two_le {Q : ℕ} (hQ : 1 ≤ Q) :
    (Chebyshev.psi Q - Chebyshev.theta Q) / Real.log 2 ≤ 3 * Real.sqrt Q * Real.log Q := by
  have h := Chebyshev.psi_sub_theta_le (x := (Q : ℝ)) (by exact_mod_cast hQ)
  have hl2 : (2 : ℝ) / 3 < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hl20 : 0 < Real.log 2 := by linarith
  have hQ0 : 0 ≤ Real.sqrt Q * Real.log Q :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.log_nonneg (by exact_mod_cast hQ))
  rw [div_le_iff₀ hl20]
  nlinarith

/-- **Twisted prime sums.** For `|f| ≤ 1`, `2 ≤ P ≤ Q` and partial sums
`|Σ_{P < n ≤ t} Λ(n) f(n)| ≤ B` on `[P, Q]`:
`|Σ_{P < p ≤ Q} f(p) e(pθ)| ≤ B (2 + 2π|θ|(Q − P))/log P + (ψ(Q) − θ(Q))/log 2`. -/
theorem norm_sum_primes_le_of_windows (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) {P Q : ℕ}
    (hP : 2 ≤ P) (hPQ : P ≤ Q) (θ : ℝ) {B : ℝ}
    (hB : ∀ t, P ≤ t → t ≤ Q → ‖∑ n ∈ Ioc P t, (vonMangoldt n : ℂ) * f n‖ ≤ B) :
    ‖∑ p ∈ (Ioc P Q).filter Nat.Prime, f p * ex (p * θ)‖
      ≤ B * ((2 + 2 * Real.pi * |θ| * (Q - P)) / Real.log P) +
        (Chebyshev.psi Q - Chebyshev.theta Q) / Real.log 2 := by
  set a : ℕ → ℂ := fun n => (vonMangoldt n : ℂ) * f n with ha
  set g : ℕ → ℂ := fun n => ex (n * θ) / (Real.log n : ℂ) with hg
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB P le_rfl hPQ)
  have hmain : ‖∑ n ∈ Ioc P Q, a n * g n‖
      ≤ B * ((2 + 2 * Real.pi * |θ| * (Q - P)) / Real.log P) :=
    (norm_sum_mul_le_of_partial a g hPQ hB).trans
      (mul_le_mul_of_nonneg_left (weight_bounds hP hPQ θ) hB0)
  have hsplit : ∑ n ∈ Ioc P Q, a n * g n
      = ∑ p ∈ (Ioc P Q).filter Nat.Prime, f p * ex (p * θ) +
        ∑ n ∈ (Ioc P Q).filter (fun n => ¬ n.Prime), a n * g n := by
    rw [← sum_filter_add_sum_filter_not (Ioc P Q) Nat.Prime]
    congr 1
    refine sum_congr rfl fun p hp => ?_
    have hpp := (mem_filter.mp hp).2
    have hlog : (Real.log p : ℂ) ≠ 0 := by
      exact_mod_cast (Real.log_pos (by exact_mod_cast hpp.one_lt)).ne'
    simp only [ha, hg, vonMangoldt_apply_prime hpp]
    field_simp
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hpow : ‖∑ n ∈ (Ioc P Q).filter (fun n => ¬ n.Prime), a n * g n‖
      ≤ (Chebyshev.psi Q - Chebyshev.theta Q) / Real.log 2 := by
    refine (norm_sum_le _ _).trans ?_
    rw [← sum_vonMangoldt_not_prime_eq, sum_div]
    calc ∑ n ∈ (Ioc P Q).filter (fun n => ¬ n.Prime), ‖a n * g n‖
        ≤ ∑ n ∈ (Ioc P Q).filter (fun n => ¬ n.Prime), vonMangoldt n / Real.log 2 := by
          refine sum_le_sum fun n hn => ?_
          have hn2 : 2 ≤ n := by
            have := (mem_Ioc.mp (mem_filter.mp hn).1).1
            omega
          have hlogn : Real.log 2 ≤ Real.log n :=
            Real.log_le_log (by norm_num) (by exact_mod_cast hn2)
          have hL : 0 ≤ vonMangoldt n := vonMangoldt_nonneg
          simp only [ha, hg]
          rw [norm_mul, norm_mul, norm_div, norm_ex, Complex.norm_real,
            Real.norm_of_nonneg hL, Complex.norm_real,
            Real.norm_of_nonneg (hl2.le.trans hlogn)]
          calc vonMangoldt n * ‖f n‖ * (1 / Real.log n) ≤ vonMangoldt n * 1 * (1 / Real.log n) := by
                gcongr
                exact hf n
            _ ≤ vonMangoldt n / Real.log 2 := by
                rw [mul_one, mul_one_div]
                exact div_le_div_of_nonneg_left hL hl2 hlogn
      _ ≤ ∑ n ∈ (Ioc 0 Q).filter (fun n => ¬ n.Prime), vonMangoldt n / Real.log 2 := by
          refine sum_le_sum_of_subset_of_nonneg
            (filter_subset_filter _ (Ioc_subset_Ioc_left (Nat.zero_le P))) fun n _ _ => ?_
          have : 0 ≤ vonMangoldt n := vonMangoldt_nonneg
          positivity
  have hsub : ∑ p ∈ (Ioc P Q).filter Nat.Prime, f p * ex (p * θ)
      = ∑ n ∈ Ioc P Q, a n * g n - ∑ n ∈ (Ioc P Q).filter (fun n => ¬ n.Prime), a n * g n := by
    rw [hsplit]; ring
  rw [hsub]
  exact (norm_sub_le _ _).trans (add_le_add hmain hpow)

/-- Closed form of a geometric sum over `(P, t]`. -/
theorem sub_one_mul_sum_Ioc_pow (z : ℂ) {P t : ℕ} (hPt : P ≤ t) :
    (z - 1) * ∑ n ∈ Ioc P t, z ^ n = z ^ (t + 1) - z ^ (P + 1) := by
  induction t, hPt using Nat.le_induction with
  | base => simp
  | succ t ht ih =>
    rw [sum_Ioc_succ_top ht, mul_add, ih]
    ring

/-- `ex(nθ) = ex(θ)^n`. -/
theorem ex_nat_mul (n : ℕ) (θ : ℝ) : ex (n * θ) = ex θ ^ n := by
  induction n with
  | zero => simp [ex_zero]
  | succ n ih =>
    rw [pow_succ, ← ih, ← ex_add]
    congr 1
    push_cast
    ring

/-- **Chord bound.** `|e(θ) − 1| = 2|sin πθ| ≥ 4|θ|` for `|θ| ≤ 1/2`. -/
theorem four_mul_abs_le_norm_ex_sub_one {θ : ℝ} (hθ : |θ| ≤ 1 / 2) :
    4 * |θ| ≤ ‖ex θ - 1‖ := by
  have e : ex θ = Complex.exp (Complex.I * ((2 * Real.pi * θ : ℝ) : ℂ)) := by
    rw [ex]
    congr 1
    push_cast
    ring
  rw [e, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul, abs_two,
    show 2 * Real.pi * θ / 2 = Real.pi * θ by ring]
  have hpi : 0 < Real.pi := Real.pi_pos
  have hJ : 2 / Real.pi * (Real.pi * |θ|) ≤ Real.sin (Real.pi * |θ|) :=
    Real.mul_le_sin (by positivity) (by nlinarith [abs_nonneg θ])
  have hJ' : 2 / Real.pi * (Real.pi * |θ|) = 2 * |θ| := by field_simp
  rw [hJ'] at hJ
  have habs : Real.sin (Real.pi * |θ|) ≤ |Real.sin (Real.pi * θ)| := by
    rcases le_total 0 θ with h | h
    · rw [abs_of_nonneg h]
      exact le_abs_self _
    · rw [abs_of_nonpos h, mul_neg, Real.sin_neg]
      exact neg_le_abs _
  linarith

/-- **Geometric sums.** For `0 < |θ| ≤ 1/2`: `|Σ_{P < n ≤ t} e(nθ)| ≤ 1/(2|θ|)`. -/
theorem norm_sum_Ioc_ex_le {θ : ℝ} (hθ0 : θ ≠ 0) (hθ : |θ| ≤ 1 / 2) {P t : ℕ} (hPt : P ≤ t) :
    ‖∑ n ∈ Ioc P t, ex (n * θ)‖ ≤ 1 / (2 * |θ|) := by
  have hc := four_mul_abs_le_norm_ex_sub_one hθ
  have hθpos : 0 < |θ| := abs_pos.mpr hθ0
  have hz : 0 < ‖ex θ - 1‖ := lt_of_lt_of_le (by positivity) hc
  have hsum : ∑ n ∈ Ioc P t, ex (n * θ) = ∑ n ∈ Ioc P t, ex θ ^ n :=
    sum_congr rfl fun n _ => ex_nat_mul n θ
  have hclosed := sub_one_mul_sum_Ioc_pow (ex θ) hPt
  have hnum : ‖ex θ ^ (t + 1) - ex θ ^ (P + 1)‖ ≤ 2 := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_pow, norm_pow, norm_ex, one_pow, one_pow]
    norm_num
  rw [hsum]
  have heq : ‖∑ n ∈ Ioc P t, ex θ ^ n‖ = ‖ex θ ^ (t + 1) - ex θ ^ (P + 1)‖ / ‖ex θ - 1‖ := by
    rw [← hclosed, norm_mul]
    field_simp
  rw [heq, div_le_div_iff₀ hz (by positivity)]
  nlinarith

/-- The von Mangoldt-free prime weight: `Σ_{P < n ≤ t} [n prime] log n = θ(t) − θ(P)`. -/
theorem sum_Ioc_primeLog_eq {P t : ℕ} (hPt : P ≤ t) :
    ∑ n ∈ Ioc P t, (if n.Prime then Real.log n else 0)
      = Chebyshev.theta t - Chebyshev.theta P := by
  rw [Chebyshev.theta, Chebyshev.theta, Nat.floor_natCast, Nat.floor_natCast, sum_filter,
    sum_filter, ← sum_Ioc_consecutive _ (Nat.zero_le P) hPt]
  ring

/-- **Untwisted prime sums.** For `0 < |θ| ≤ 1/2`, `2 ≤ P ≤ Q` and
`|θ(t) − θ(P) − (t − P)| ≤ E` on `[P, Q]`:
`|Σ_{P < p ≤ Q} e(pθ)| ≤ E (2 + 2π|θ|(Q − P))/log P + 1/(2|θ| log P)`. -/
theorem norm_sum_primes_ex_le {P Q : ℕ} (hP : 2 ≤ P) (hPQ : P ≤ Q) {θ : ℝ} (hθ0 : θ ≠ 0)
    (hθ : |θ| ≤ 1 / 2) {E : ℝ}
    (hE : ∀ t : ℕ, P ≤ t → t ≤ Q →
      |Chebyshev.theta t - Chebyshev.theta P - ((t : ℝ) - P)| ≤ E) :
    ‖∑ p ∈ (Ioc P Q).filter Nat.Prime, ex (p * θ)‖
      ≤ E * ((2 + 2 * Real.pi * |θ| * (Q - P)) / Real.log P) +
        1 / (2 * |θ|) * (1 / Real.log P) := by
  set a : ℕ → ℂ := fun n => (((if n.Prime then Real.log n else 0) - 1 : ℝ) : ℂ) with ha
  set g : ℕ → ℂ := fun n => ex (n * θ) / (Real.log n : ℂ) with hg
  set b : ℕ → ℂ := fun n => ex (n * θ) with hb
  set w : ℕ → ℂ := fun n => ((1 / Real.log n : ℝ) : ℂ) with hw
  have hlogP : 0 < Real.log P := Real.log_pos (by exact_mod_cast (show 1 < P by omega))
  have hlogmono : ∀ m : ℕ, P ≤ m → Real.log P ≤ Real.log m := fun m hm =>
    Real.log_le_log (by exact_mod_cast (show 0 < P by omega)) (by exact_mod_cast hm)
  -- the PNT remainder against `e(nθ)/log n`
  have hpartA : ∀ t, P ≤ t → t ≤ Q → ‖∑ m ∈ Ioc P t, a m‖ ≤ E := by
    intro t hPt htQ
    have h1 : ∑ m ∈ Ioc P t, a m
        = (((Chebyshev.theta t - Chebyshev.theta P) - ((t : ℝ) - P) : ℝ) : ℂ) := by
      simp only [ha]
      rw [← Complex.ofReal_sum, sum_sub_distrib, sum_Ioc_primeLog_eq hPt, sum_const,
        Nat.card_Ioc, nsmul_eq_mul, mul_one, Nat.cast_sub hPt]
    rw [h1, Complex.norm_real, Real.norm_eq_abs]
    exact hE t hPt htQ
  have hE0 : 0 ≤ E := (abs_nonneg _).trans (hE P le_rfl hPQ)
  have hA : ‖∑ n ∈ Ioc P Q, a n * g n‖ ≤ E * ((2 + 2 * Real.pi * |θ| * (Q - P)) / Real.log P) :=
    (norm_sum_mul_le_of_partial a g hPQ hpartA).trans
      (mul_le_mul_of_nonneg_left (weight_bounds hP hPQ θ) hE0)
  -- the integers against `1/log n`
  have hpartB : ∀ t, P ≤ t → t ≤ Q → ‖∑ m ∈ Ioc P t, b m‖ ≤ 1 / (2 * |θ|) :=
    fun t hPt _ => norm_sum_Ioc_ex_le hθ0 hθ hPt
  have hwvar : ‖w Q‖ + ∑ n ∈ Ico P Q, ‖w (n + 1) - w n‖ = 1 / Real.log P := by
    have hstep : ∀ n ∈ Ico P Q, ‖w (n + 1) - w n‖
        = 1 / Real.log n - 1 / Real.log (n + 1 : ℕ) := by
      intro n hn
      have hnP : P ≤ n := (mem_Ico.mp hn).1
      have hln0 : 0 < Real.log n := lt_of_lt_of_le hlogP (hlogmono n hnP)
      have hlog_le : Real.log n ≤ Real.log (n + 1 : ℕ) :=
        Real.log_le_log (by exact_mod_cast (show 0 < n by omega)) (by exact_mod_cast (by omega))
      simp only [hw]
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm,
        abs_of_nonneg (sub_nonneg.mpr (div_le_div_of_nonneg_left zero_le_one hln0 hlog_le))]
    rw [sum_congr rfl hstep, sum_Ico_inv_log_sub hPQ]
    simp only [hw]
    rw [Complex.norm_real, Real.norm_of_nonneg (by
      have := hlogP.le.trans (hlogmono Q hPQ)
      positivity)]
    ring
  have hB : ‖∑ n ∈ Ioc P Q, b n * w n‖ ≤ 1 / (2 * |θ|) * (1 / Real.log P) := by
    have := norm_sum_mul_le_of_partial b w hPQ hpartB
    rwa [hwvar] at this
  -- the primes are the sum of the two
  have hsplit : ∑ p ∈ (Ioc P Q).filter Nat.Prime, ex (p * θ)
      = ∑ n ∈ Ioc P Q, a n * g n + ∑ n ∈ Ioc P Q, b n * w n := by
    rw [← sum_add_distrib, sum_filter]
    refine sum_congr rfl fun n hn => ?_
    have hn2 : 2 ≤ n := by
      have := (mem_Ioc.mp hn).1
      omega
    have hlog : (Real.log n : ℂ) ≠ 0 := by
      exact_mod_cast (Real.log_pos (by exact_mod_cast (show 1 < n by omega))).ne'
    simp only [ha, hg, hb, hw]
    split_ifs with hp
    · simp only [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_div]
      rw [mul_one_div, mul_div_assoc', ← add_div, eq_div_iff hlog]
      ring
    · simp only [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_zero, Complex.ofReal_div]
      ring
  rw [hsplit]
  exact (norm_add_le _ _).trans (add_le_add hA hB)

end

end GaloisForLFunctions.PrimeExponentialSums
