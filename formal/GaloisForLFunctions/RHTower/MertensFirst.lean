/-
Mertens' first theorem in von Mangoldt form: the prime-weighted harmonic sum
`∑_{d ≤ n} Λ(d)/d` tracks `log n` with a uniformly bounded error.  Elementary —
the divisor identity `∑_{d ∣ m} Λ(d) = log m` summed over `m ≤ n`, a
Stirling-free two-sided bound on `∑_{m ≤ n} log m`, and Chebyshev's `ψ(x) = O(x)`.
No prime number theorem.  This is the quantitative pole input for the
near-critical Steinhaus carrier's log-derivative (mathlib carries only the
divergence of `∑ 1/p`, not the asymptotic).
-/
import Mathlib

namespace RHTower
namespace Mertens

open Finset ArithmeticFunction

/-- Summatory von Mangoldt divisor swap:
`∑_{m ≤ n} log m = ∑_{d ≤ n} Λ(d) · ⌊n/d⌋`. -/
theorem log_summatory_eq (n : ℕ) :
    ∑ m ∈ Finset.Icc 1 n, Real.log m
      = ∑ d ∈ Finset.Icc 1 n, Λ d * ((n / d : ℕ) : ℝ) := by
  have hIcc : Finset.Icc 1 n = Finset.Ioc 0 n := by ext x; simp [Nat.lt_iff_add_one_le]
  calc ∑ m ∈ Finset.Icc 1 n, Real.log m
      = ∑ m ∈ Finset.Icc 1 n, ∑ d ∈ m.divisors, Λ d :=
        Finset.sum_congr rfl fun m _ => (vonMangoldt_sum).symm
    _ = ∑ d ∈ Finset.Icc 1 n, ∑ _m ∈ (Finset.Icc 1 n).filter (d ∣ ·), Λ d := by
        rw [Finset.sum_comm']
        intro m d
        simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
        constructor
        · rintro ⟨⟨hm1, hmn⟩, hdm, _⟩
          exact ⟨⟨⟨hm1, hmn⟩, hdm⟩, Nat.pos_of_dvd_of_pos hdm (by omega),
            le_trans (Nat.le_of_dvd (by omega) hdm) hmn⟩
        · rintro ⟨⟨⟨hm1, hmn⟩, hdm⟩, _⟩
          exact ⟨⟨hm1, hmn⟩, hdm, by omega⟩
    _ = ∑ d ∈ Finset.Icc 1 n, Λ d * ((n / d : ℕ) : ℝ) := by
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
        congr 1
        rw [hIcc, show ((Finset.Ioc 0 n).filter (d ∣ ·)) = {x ∈ Finset.Ioc 0 n | d ∣ x} from rfl,
          Nat.Ioc_filter_dvd_card_eq_div]

/-- `∑_{m ≤ n} log m ≤ n · log n`. -/
theorem sum_log_le (n : ℕ) : ∑ m ∈ Finset.Icc 1 n, Real.log m ≤ (n:ℝ) * Real.log n := by
  calc ∑ m ∈ Finset.Icc 1 n, Real.log m
      ≤ ∑ _m ∈ Finset.Icc 1 n, Real.log n := by
        refine Finset.sum_le_sum fun m hm => ?_
        rw [Finset.mem_Icc] at hm
        exact Real.log_le_log (by exact_mod_cast hm.1) (by exact_mod_cast hm.2)
    _ = (n:ℝ) * Real.log n := by rw [Finset.sum_const, Nat.card_Icc]; push_cast; ring

/-- `n · log n − n ≤ ∑_{m ≤ n} log m` (Stirling-free lower bound via
`log(1 + 1/k) ≤ 1/k`). -/
theorem sum_log_ge (n : ℕ) : (n:ℝ) * Real.log n - n ≤ ∑ m ∈ Finset.Icc 1 n, Real.log m := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ k + 1)]
    have hstep : (k:ℝ) * (Real.log (k+1) - Real.log k) ≤ 1 := by
      rcases Nat.eq_zero_or_pos k with hk | hk
      · simp [hk]
      · have hk0 : (0:ℝ) < k := by exact_mod_cast hk
        have hlog : Real.log ((k+1)/k) ≤ (k+1)/k - 1 := Real.log_le_sub_one_of_pos (by positivity)
        rw [Real.log_div (by positivity) (by positivity)] at hlog
        have hkk : (k:ℝ) * ((↑k+1)/↑k) = ↑k + 1 := by field_simp
        calc (k:ℝ) * (Real.log (k+1) - Real.log k)
            ≤ (k:ℝ) * ((↑k+1)/↑k - 1) := by nlinarith [hlog, hk0]
          _ = 1 := by rw [mul_sub, hkk]; ring
    push_cast
    nlinarith [ih, hstep]

/-- `∑_{d ≤ n} Λ(d) = ψ(n) ≤ (log 4 + 4)·n` (Chebyshev). -/
theorem sum_vonMangoldt_Icc_le (n : ℕ) :
    ∑ d ∈ Finset.Icc 1 n, Λ d ≤ (Real.log 4 + 4) * n := by
  have hpsi : Chebyshev.psi n = ∑ d ∈ Finset.Icc 1 n, Λ d := by
    rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast,
      show Finset.Icc 0 n = insert 0 (Finset.Icc 1 n) from by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega,
      Finset.sum_insert (by simp)]
    simp
  rw [← hpsi]; exact Chebyshev.psi_le_const_mul_self (by positivity)

/-- The lower floor bound `(n : ℝ)/d < ⌊n/d⌋ + 1`. -/
theorem cast_div_lt (n d : ℕ) (hd : 0 < d) : (n:ℝ)/d < ((n/d : ℕ):ℝ) + 1 := by
  have h1 : n < (n/d + 1) * d := by nlinarith [Nat.div_add_mod n d, Nat.mod_lt n hd]
  rw [div_lt_iff₀ (by exact_mod_cast hd : (0:ℝ) < d)]; exact_mod_cast h1

/-- **Mertens' first theorem (von Mangoldt form).**  The prime-weighted harmonic
sum tracks `log n` with a bounded error: `|∑_{d ≤ n} Λ(d)/d − log n| ≤ log 4 + 4`,
uniformly for `n ≥ 1`.  Elementary; no prime number theorem. -/
theorem mertens_first (n : ℕ) (hn : 1 ≤ n) :
    |(∑ d ∈ Finset.Icc 1 n, Λ d / d) - Real.log n| ≤ Real.log 4 + 4 := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  set S := ∑ d ∈ Finset.Icc 1 n, Λ d / d with hS
  have hUP : ∑ d ∈ Finset.Icc 1 n, Λ d * ((n/d:ℕ):ℝ) ≤ (n:ℝ) * S := by
    rw [hS, Finset.mul_sum]
    refine Finset.sum_le_sum fun d hd => ?_
    rw [Finset.mem_Icc] at hd
    have hΛ : 0 ≤ Λ d := vonMangoldt_nonneg
    calc Λ d * ((n/d:ℕ):ℝ) ≤ Λ d * ((n:ℝ)/d) :=
          mul_le_mul_of_nonneg_left Nat.cast_div_le hΛ
      _ = (n:ℝ) * (Λ d / d) := by ring
  have hLO : (n:ℝ) * S - ∑ d ∈ Finset.Icc 1 n, Λ d
      ≤ ∑ d ∈ Finset.Icc 1 n, Λ d * ((n/d:ℕ):ℝ) := by
    rw [hS, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun d hd => ?_
    rw [Finset.mem_Icc] at hd
    have hΛ : 0 ≤ Λ d := vonMangoldt_nonneg
    have hlt := cast_div_lt n d (by omega)
    calc (n:ℝ) * (Λ d / d) - Λ d = Λ d * ((n:ℝ)/d - 1) := by ring
      _ ≤ Λ d * ((n/d:ℕ):ℝ) := mul_le_mul_of_nonneg_left (by linarith) hΛ
  have heq := log_summatory_eq n
  have hlo := sum_log_ge n
  have hhi := sum_log_le n
  have hv := sum_vonMangoldt_Icc_le n
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · nlinarith [hUP, hlo, heq, hn0, hlog4]
  · nlinarith [hLO, hhi, heq, hv, hn0, hlog4]

open Filter Asymptotics in
/-- Consumer form: `∑_{d ≤ n} Λ(d)/d = log n + O(1)`. -/
theorem mertens_first_isBigO :
    (fun n : ℕ => (∑ d ∈ Finset.Icc 1 n, Λ d / d) - Real.log n) =O[atTop] (fun _ => (1:ℝ)) := by
  rw [isBigO_iff]
  refine ⟨Real.log 4 + 4, ?_⟩
  filter_upwards [eventually_ge_atTop 1] with n hn
  simpa using mertens_first n hn

/-- `log x ≤ (1/α)·x^α` for any exponent `α > 0` and `x > 0`. -/
theorem log_le_rpow {x α : ℝ} (hx : 0 < x) (hα : 0 < α) : Real.log x ≤ (1/α) * x ^ α := by
  have hxr : (0:ℝ) < x ^ α := Real.rpow_pos_of_pos hx _
  have h1 : Real.log (x ^ α) ≤ x ^ α - 1 := Real.log_le_sub_one_of_pos hxr
  rw [Real.log_rpow hx] at h1
  rw [show (1/α) * x ^ α = x ^ α / α from by ring, le_div_iff₀ hα]
  nlinarith [h1]

/-- `∑ log n / n^s` converges for every real `s > 1`: the convergence input
for the Abel-summed prime-power tail `∑_{p^k, k ≥ 2} (log p)/p^k` of Mertens'
theorem. -/
theorem summable_log_div_rpow {s : ℝ} (hs : 1 < s) :
    Summable (fun n : ℕ => Real.log n / (n:ℝ)^s) := by
  set α := (s - 1)/2 with hα
  have hα0 : 0 < α := by rw [hα]; linarith
  have hsa : 1 < s - α := by rw [hα]; linarith
  have hg : Summable (fun n : ℕ => (1/α) * (1/(n:ℝ)^(s - α))) :=
    (Real.summable_one_div_nat_rpow.mpr hsa).mul_left _
  refine hg.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
  · rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp only [Nat.cast_zero, Real.log_zero, zero_div]; positivity
    · exact div_nonneg (Real.log_nonneg (by exact_mod_cast hn)) (by positivity)
  · rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp only [Nat.cast_zero, Real.log_zero, zero_div]; positivity
    · have hn0 : (0:ℝ) < n := by exact_mod_cast hn
      have hlog := log_le_rpow hn0 hα0
      rw [div_le_iff₀ (by positivity : (0:ℝ) < (n:ℝ)^s)]
      have hrp : (1/α) * (1/(n:ℝ)^(s-α)) * (n:ℝ)^s = (1/α) * (n:ℝ)^α := by
        rw [one_div ((n:ℝ)^(s-α)), ← Real.rpow_neg hn0.le, mul_assoc,
          ← Real.rpow_add hn0, show -(s-α) + s = α from by ring]
      rw [hrp]; exact hlog

/-- Abel summation for the reciprocal weight: for a sequence `a` with `a 0 = 0`,
`∑_{i=1}^N a(i)/i = A(N)/N + ∑_{i=1}^{N-1} A(i)/(i(i+1))`, where `A(k) = ∑_{i≤k} a(i)`.
The partial sums `A` carry the arithmetic content; this converts the reciprocal-
weighted sum into one governed by them. -/
theorem abel_tail_identity (a : ℕ → ℝ) (ha0 : a 0 = 0) (N : ℕ) (hN : 0 < N) :
    ∑ i ∈ Finset.Icc 1 N, a i / (i:ℝ)
      = (∑ i ∈ Finset.range (N+1), a i) / N
        + ∑ i ∈ Finset.Icc 1 (N-1), (∑ j ∈ Finset.range (i+1), a j) / ((i:ℝ) * (i+1)) := by
  have hIoc : Finset.Ioc 0 N = Finset.Icc 1 N := by ext x; simp; omega
  have hIoc2 : Finset.Ioc 0 (N-1) = Finset.Icc 1 (N-1) := by ext x; simp; omega
  have key := Finset.sum_Ioc_by_parts (fun i => (i:ℝ)⁻¹) a hN
  simp only [smul_eq_mul] at key
  rw [hIoc] at key
  rw [Finset.sum_congr rfl (fun i _ => div_eq_inv_mul (a i) (i:ℝ)), key,
    Finset.sum_range_one, ha0, mul_zero, sub_zero, hIoc2, inv_mul_eq_div, sub_eq_add_neg]
  congr 1
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_Icc] at hi
  have hi0 : (0:ℝ) < (i:ℝ) := by exact_mod_cast hi.1
  have hi1 : (i:ℝ) + 1 ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- The non-prime von Mangoldt weight: `Λ(n)` on non-primes (the prime powers
`p^k, k ≥ 2`), zero on primes. -/
noncomputable def notPrimeVonMangoldt (n : ℕ) : ℝ := if n.Prime then 0 else Λ n

/-- Its partial sums are exactly Chebyshev's `ψ − θ` (the prime-power excess). -/
theorem sum_notPrimeVonMangoldt (k : ℕ) :
    ∑ i ∈ Finset.range (k+1), notPrimeVonMangoldt i
      = Chebyshev.psi k - Chebyshev.theta k := by
  rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Nat.floor_natCast]
  rw [show Finset.range (k+1) = Finset.Icc 0 k from by
    ext x; simp only [Finset.mem_range, Finset.mem_Icc]; omega]
  rw [show Finset.Icc 0 k = insert 0 (Finset.Ioc 0 k) from by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ioc]; omega]
  rw [Finset.sum_insert (by simp), notPrimeVonMangoldt, if_neg (by decide),
    vonMangoldt_apply, if_neg (by decide), zero_add]
  simp only [notPrimeVonMangoldt]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun n hn => ?_
  by_cases hp : n.Prime <;> simp [hp]

/-- The prime-power excess `ψ(N) − θ(N)`, divided by `N`, is uniformly bounded
(`≤ 8`): the Abel boundary term. -/
theorem psi_theta_div_le (N : ℕ) (hN : 1 ≤ N) :
    (Chebyshev.psi N - Chebyshev.theta N) / N ≤ 8 := by
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0:ℝ) < N := by linarith
  have h1 : Chebyshev.psi N - Chebyshev.theta N ≤ 2 * Real.sqrt N * Real.log N :=
    Chebyshev.psi_sub_theta_le hN1
  have h2 : Real.log N ≤ 4 * (N:ℝ)^(1/4:ℝ) := by
    have := log_le_rpow hN0 (show (0:ℝ) < 1/4 by norm_num); norm_num at this ⊢; linarith
  have hsqrt : Real.sqrt N = (N:ℝ)^(1/2:ℝ) := Real.sqrt_eq_rpow _
  have hmul : (N:ℝ)^(1/2:ℝ) * (N:ℝ)^(1/4:ℝ) = (N:ℝ)^(3/4:ℝ) := by
    rw [← Real.rpow_add hN0]; norm_num
  have hle34 : (N:ℝ)^(3/4:ℝ) ≤ N := by
    calc (N:ℝ)^(3/4:ℝ) ≤ (N:ℝ)^(1:ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
      _ = N := by rw [Real.rpow_one]
  have hsqrtpos : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
  rw [div_le_iff₀ hN0]
  calc Chebyshev.psi N - Chebyshev.theta N ≤ 2 * Real.sqrt N * Real.log N := h1
    _ ≤ 2 * Real.sqrt N * (4 * (N:ℝ)^(1/4:ℝ)) := by nlinarith [hsqrtpos, h2]
    _ = 8 * ((N:ℝ)^(1/2:ℝ) * (N:ℝ)^(1/4:ℝ)) := by rw [hsqrt]; ring
    _ = 8 * (N:ℝ)^(3/4:ℝ) := by rw [hmul]
    _ ≤ 8 * N := by nlinarith [hle34]

/-- Each Abel summand `(ψ(i) − θ(i))/(i(i+1))` is dominated by `2 log i / i^{3/2}`. -/
theorem psi_theta_term_le (i : ℕ) (hi : 1 ≤ i) :
    (Chebyshev.psi i - Chebyshev.theta i) / ((i:ℝ) * (i+1))
      ≤ 2 * Real.log i / (i:ℝ)^(3/2:ℝ) := by
  have hi1 : (1:ℝ) ≤ i := by exact_mod_cast hi
  have hi0 : (0:ℝ) < i := by linarith
  have h1 : Chebyshev.psi i - Chebyshev.theta i ≤ 2 * Real.sqrt i * Real.log i :=
    Chebyshev.psi_sub_theta_le hi1
  have h0 : 0 ≤ Chebyshev.psi i - Chebyshev.theta i := by
    rw [← sum_notPrimeVonMangoldt]
    exact Finset.sum_nonneg fun j _ => by
      rw [notPrimeVonMangoldt]; split <;> simp [vonMangoldt_nonneg]
  have hsqrt : Real.sqrt i = (i:ℝ)^(1/2:ℝ) := Real.sqrt_eq_rpow _
  have hlogpos : 0 ≤ Real.log i := Real.log_nonneg hi1
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have key : (2 * Real.sqrt i * Real.log i) * (i:ℝ)^(3/2:ℝ)
      ≤ (2 * Real.log i) * ((i:ℝ) * (i+1)) := by
    rw [hsqrt]
    have e1 : (i:ℝ)^(1/2:ℝ) * (i:ℝ)^(3/2:ℝ) = (i:ℝ)^2 := by
      rw [← Real.rpow_add hi0]; norm_num
    have hii : (i:ℝ)^2 ≤ (i:ℝ) * (i+1) := by nlinarith [hi0]
    nlinarith [hlogpos, hii, e1, Real.rpow_nonneg hi0.le (3/2:ℝ)]
  nlinarith [key, h0, h1, Real.rpow_nonneg hi0.le (3/2:ℝ), hlogpos]

/-- The convergent Abel-tail total `∑' 2 log i / i^{3/2}`. -/
noncomputable def mertensTail : ℝ := ∑' i : ℕ, 2 * (Real.log i / (i:ℝ)^(3/2:ℝ))

theorem mertensTail_summable :
    Summable (fun i : ℕ => 2 * (Real.log i / (i:ℝ)^(3/2:ℝ))) :=
  (summable_log_div_rpow (by norm_num)).mul_left 2

/-- The prime-power tail `∑_{n ≤ N, ¬prime} Λ(n)/n` is uniformly bounded. -/
theorem tail_bounded (N : ℕ) :
    ∑ i ∈ Finset.Icc 1 N, notPrimeVonMangoldt i / (i:ℝ) ≤ 8 + mertensTail := by
  have hT0 : 0 ≤ mertensTail := by rw [mertensTail]; exact tsum_nonneg fun i => by positivity
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp; linarith
  rw [abel_tail_identity notPrimeVonMangoldt (by simp [notPrimeVonMangoldt]) N hN]
  simp only [sum_notPrimeVonMangoldt]
  have hterm : ∑ i ∈ Finset.Icc 1 (N-1),
        (Chebyshev.psi i - Chebyshev.theta i) / ((i:ℝ)*(i+1)) ≤ mertensTail := by
    calc ∑ i ∈ Finset.Icc 1 (N-1), (Chebyshev.psi i - Chebyshev.theta i) / ((i:ℝ)*(i+1))
        ≤ ∑ i ∈ Finset.Icc 1 (N-1), 2 * (Real.log i / (i:ℝ)^(3/2:ℝ)) := by
          refine Finset.sum_le_sum fun i hi => ?_
          rw [Finset.mem_Icc] at hi
          rw [← mul_div_assoc]
          exact psi_theta_term_le i hi.1
      _ ≤ mertensTail := by
          rw [mertensTail]
          exact Summable.sum_le_tsum _ (fun i _ => by positivity) mertensTail_summable
  linarith [psi_theta_div_le N hN, hterm]

/-- **Mertens' first theorem, prime form.**  `∑_{p ≤ N} (log p)/p = log N + O(1)`,
with an explicit constant.  Obtained from the von Mangoldt form by Abel
summation of the prime-power tail against Chebyshev's `ψ − θ`. -/
theorem mertens_first_prime (N : ℕ) (hN : 1 ≤ N) :
    |(∑ n ∈ Finset.Icc 1 N with n.Prime, Real.log n / (n:ℝ)) - Real.log N|
      ≤ (Real.log 4 + 4) + (8 + mertensTail) := by
  have hsplit : ∑ n ∈ Finset.Icc 1 N, Λ n / (n:ℝ)
      = (∑ n ∈ Finset.Icc 1 N with n.Prime, Real.log n / (n:ℝ))
        + ∑ i ∈ Finset.Icc 1 N, notPrimeVonMangoldt i / (i:ℝ) := by
    rw [Finset.sum_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [notPrimeVonMangoldt]
    by_cases hp : n.Prime
    · simp [hp, vonMangoldt_apply_prime hp]
    · simp [hp]
  have hm := mertens_first N hN
  have ht := tail_bounded N
  have ht0 : 0 ≤ ∑ i ∈ Finset.Icc 1 N, notPrimeVonMangoldt i / (i:ℝ) :=
    Finset.sum_nonneg fun i _ => by
      rw [notPrimeVonMangoldt]
      split <;> [positivity; exact div_nonneg vonMangoldt_nonneg (by positivity)]
  rw [abs_le] at hm ⊢
  constructor <;> [linarith [hm.1, hsplit, ht, ht0]; linarith [hm.2, hsplit, ht, ht0]]

end Mertens
end RHTower
