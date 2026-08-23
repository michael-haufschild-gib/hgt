import GaloisForLFunctions.RHTower.SqrtTelescopeSums
import GaloisForLFunctions.RHTower.PsiRatioImprove
import GaloisForLFunctions.RHTower.Sieve.MultiplicativeLogRecursion
import GaloisForLFunctions.RHTower.Sieve.RamarePhaseError

/-!
# Halász's recursion for an ordinary multiplicative function

Dropping the coprimality condition from `f(ab) = f(a)f(b)` costs only `O(N)`: the divisor swap is
exact without any multiplicativity, and the defect `f(dk) − f(d)f(k)` is supported on the `k`
divisible by the least prime factor of `d`.  Summing that defect against `Λ` needs only
`∑_p log p / p² ≤ 4`, which follows from `log n ≤ 2√n` and the telescoping tail of `n^{-3/2}`.
-/

namespace RHTower.Sieve

open Real ArithmeticFunction

noncomputable section

theorem log_div_sq_le_inv_sqrt_cube {n : ℕ} (hn : 1 ≤ n) :
    Real.log n / (n : ℝ) ^ 2 ≤ 2 * (1 / Real.sqrt ((n : ℝ) ^ 3)) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hlog := RHTower.log_le_two_sqrt hn0
  have hs0 : (0 : ℝ) < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
  have hsq : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) := Real.mul_self_sqrt hn0.le
  have hcube : Real.sqrt ((n : ℝ) ^ 3) = (n : ℝ) * Real.sqrt (n : ℝ) := by
    rw [show ((n : ℝ)) ^ 3 = ((n : ℝ)) ^ 2 * (n : ℝ) by ring, Real.sqrt_mul (by positivity),
      Real.sqrt_sq hn0.le]
  rw [hcube, div_le_iff₀ (by positivity)]
  have h2 : 2 * (1 / ((n : ℝ) * Real.sqrt (n : ℝ))) * (n : ℝ) ^ 2
      = 2 * (n : ℝ) / Real.sqrt (n : ℝ) := by
    field_simp
  rw [h2]
  have h3 : 2 * (n : ℝ) / Real.sqrt (n : ℝ) = 2 * Real.sqrt (n : ℝ) := by
    rw [eq_comm, eq_div_iff (ne_of_gt hs0)]
    nlinarith [hsq]
  rw [h3]
  exact hlog

/-- `∑_{2 ≤ n ≤ N} log n / n² ≤ 4`. -/
theorem sum_log_div_sq_Icc_le (N : ℕ) :
    ∑ n ∈ Finset.Icc 2 N, Real.log n / (n : ℝ) ^ 2 ≤ 4 := by
  rcases Nat.lt_or_ge N 1 with hN | hN
  · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
    norm_num
  · have hterm : ∀ n ∈ Finset.Icc 2 N, Real.log n / (n : ℝ) ^ 2
        ≤ 2 * (1 / Real.sqrt ((n : ℝ) ^ 3)) := by
      intro n hn
      rw [Finset.mem_Icc] at hn
      exact log_div_sq_le_inv_sqrt_cube (by omega)
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.mul_sum]
    have htail := RHTower.sum_inv_sqrt_cube_le (R := 2) (by norm_num) N (by omega)
    have hone : ((2 - 1 : ℕ) : ℝ) = 1 := by norm_num
    rw [hone, Real.sqrt_one] at htail
    linarith

/-- **The divisor swap without any multiplicativity.**  The log-weighted sum is the von Mangoldt
average of the shifted values `f(dk)`. -/
theorem sum_mul_log_eq_vonMangoldt_raw (f : ℕ → ℂ) (N : ℕ) :
    ∑ m ∈ Finset.Icc 1 N, f m * ((Real.log (m : ℝ) : ℝ) : ℂ)
      = ∑ d ∈ Finset.Icc 1 N,
          ((Λ d : ℝ) : ℂ) * ∑ k ∈ Finset.Icc 1 (N / d), f (d * k) := by
  classical
  have hpt : ∀ m ∈ Finset.Icc 1 N,
      f m * ((Real.log (m : ℝ) : ℝ) : ℂ)
        = ∑ d ∈ m.divisors, ((Λ d : ℝ) : ℂ) * f (d * (m / d)) := by
    intro m hm
    rw [Finset.mem_Icc] at hm
    have hm0 : m ≠ 0 := by omega
    have hlog : ∑ d ∈ m.divisors, Λ d = Real.log m := vonMangoldt_sum
    have hval : ∀ d ∈ m.divisors, ((Λ d : ℝ) : ℂ) * f (d * (m / d))
        = ((Λ d : ℝ) : ℂ) * f m := by
      intro d hd
      rw [Nat.mem_divisors] at hd
      rw [Nat.mul_div_cancel' hd.1]
    rw [Finset.sum_congr rfl hval, ← Finset.sum_mul, ← Complex.ofReal_sum, hlog]
    ring
  rw [Finset.sum_congr rfl hpt]
  have hswap := sum_divisors_swap (M := ℂ) N (fun d k => ((Λ d : ℝ) : ℂ) * f (d * k))
  rw [hswap]
  exact Finset.sum_congr rfl fun d _ => (Finset.mul_sum _ _ _).symm

theorem minFac_dvd_of_not_coprime_primePow {d k : ℕ} (hd : IsPrimePow d)
    (h : ¬ Nat.Coprime d k) : d.minFac ∣ k := by
  obtain ⟨p, n, hp, hn, rfl⟩ := hd
  have hp' : Nat.Prime p := hp.nat_prime
  have hd0 : p ^ n ≠ 0 := pow_ne_zero _ hp'.pos.ne'
  have hgcd : Nat.gcd (p ^ n) k ≠ 1 := h
  have hgcd0 : Nat.gcd (p ^ n) k ≠ 0 := by
    intro hc
    exact hd0 (Nat.eq_zero_of_gcd_eq_zero_left hc)
  set q := (Nat.gcd (p ^ n) k).minFac with hq
  have hqp : Nat.Prime q := Nat.minFac_prime hgcd
  have hqg : q ∣ Nat.gcd (p ^ n) k := Nat.minFac_dvd _
  have hqd : q ∣ p ^ n := hqg.trans (Nat.gcd_dvd_left _ _)
  have hqk : q ∣ k := hqg.trans (Nat.gcd_dvd_right _ _)
  have hqeq : q = p := (Nat.prime_dvd_prime_iff_eq hqp hp').mp (hqp.dvd_of_dvd_pow hqd)
  have hmin : (p ^ n).minFac = p := by
    rcases Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0) with ⟨m, rfl⟩
    exact Nat.Prime.pow_minFac hp' (by omega)
  rw [hmin, ← hqeq]
  exact hqk

theorem norm_sub_shift_le {f : ℕ → ℂ}
    (hf : ∀ a b : ℕ, Nat.Coprime a b → f (a * b) = f a * f b)
    (hbdd : ∀ n : ℕ, ‖f n‖ ≤ 1) (d k : ℕ) :
    ‖f (d * k) - f d * f k‖ ≤ if Nat.Coprime d k then 0 else 2 := by
  split_ifs with h
  · rw [hf d k h, sub_self, norm_zero]
  · refine le_trans (norm_sub_le _ _) ?_
    have h1 := hbdd (d * k)
    have h2 := hbdd d
    have h3 := hbdd k
    rw [norm_mul]
    nlinarith [norm_nonneg (f d), norm_nonneg (f k)]

/-- The coprimality defect of the inner sum at a prime power. -/
theorem norm_sum_shift_sub_le {f : ℕ → ℂ}
    (hf : ∀ a b : ℕ, Nat.Coprime a b → f (a * b) = f a * f b)
    (hbdd : ∀ n : ℕ, ‖f n‖ ≤ 1) {d : ℕ} (hd : IsPrimePow d) (M : ℕ) :
    ‖(∑ k ∈ Finset.Icc 1 M, f (d * k)) - f d * ∑ k ∈ Finset.Icc 1 M, f k‖
      ≤ 2 * ((M / d.minFac : ℕ) : ℝ) := by
  classical
  have hrw : (∑ k ∈ Finset.Icc 1 M, f (d * k)) - f d * ∑ k ∈ Finset.Icc 1 M, f k
      = ∑ k ∈ Finset.Icc 1 M, (f (d * k) - f d * f k) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  rw [hrw]
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ k ∈ Finset.Icc 1 M, ‖f (d * k) - f d * f k‖
      ≤ (if d.minFac ∣ k then (2 : ℝ) else 0) := by
    intro k _
    refine le_trans (norm_sub_shift_le hf hbdd d k) ?_
    by_cases hc : Nat.Coprime d k
    · rw [if_pos hc]
      positivity
    · rw [if_neg hc, if_pos (minFac_dvd_of_not_coprime_primePow hd hc)]
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, card_Icc_filter_dvd M d.minFac]
  ring_nf
  exact le_refl _

/-- **Lemma C.**  Halász's recursion for an ORDINARY (coprime) multiplicative function: dropping the
coprimality condition costs only `O(N)`. -/
theorem norm_sum_mul_log_sub_vonMangoldt_le_coprime {f : ℕ → ℂ}
    (hf : ∀ a b : ℕ, Nat.Coprime a b → f (a * b) = f a * f b)
    (hbdd : ∀ n : ℕ, ‖f n‖ ≤ 1) (N : ℕ) :
    ‖(∑ m ∈ Finset.Icc 1 N, f m * ((Real.log (m : ℝ) : ℝ) : ℂ))
        - ∑ d ∈ Finset.Icc 1 N, ((Λ d : ℝ) : ℂ) * f d * ∑ k ∈ Finset.Icc 1 (N / d), f k‖
      ≤ (16 + (8 + RHTower.Mertens.mertensTail)) * (N : ℝ) := by
  classical
  set D : ℕ → ℂ := fun d =>
    (∑ k ∈ Finset.Icc 1 (N / d), f (d * k)) - f d * ∑ k ∈ Finset.Icc 1 (N / d), f k with hD
  have hDbound : ∀ d : ℕ, IsPrimePow d →
      ‖D d‖ ≤ 2 * (((N / d) / d.minFac : ℕ) : ℝ) := by
    intro d hd
    exact norm_sum_shift_sub_le hf hbdd hd (N / d)
  have hdiff : (∑ m ∈ Finset.Icc 1 N, f m * ((Real.log (m : ℝ) : ℝ) : ℂ))
      - ∑ d ∈ Finset.Icc 1 N, ((Λ d : ℝ) : ℂ) * f d * ∑ k ∈ Finset.Icc 1 (N / d), f k
      = ∑ d ∈ Finset.Icc 1 N, ((Λ d : ℝ) : ℂ) * D d := by
    rw [sum_mul_log_eq_vonMangoldt_raw f N, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [hD]
    ring
  rw [hdiff]
  set W : ℕ → ℂ := fun d => if IsPrimePow d then D d else 0 with hW
  have hWD : ∀ d ∈ Finset.Icc 1 N, ((Λ d : ℝ) : ℂ) * D d = ((Λ d : ℝ) : ℂ) * W d := by
    intro d _
    by_cases hd : IsPrimePow d
    · show ((Λ d : ℝ) : ℂ) * D d = ((Λ d : ℝ) : ℂ) * (if IsPrimePow d then D d else 0)
      rw [if_pos hd]
    · show ((Λ d : ℝ) : ℂ) * D d = ((Λ d : ℝ) : ℂ) * (if IsPrimePow d then D d else 0)
      rw [if_neg hd, ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hd]
      simp
  rw [Finset.sum_congr rfl hWD]
  have hsplit : ∑ d ∈ Finset.Icc 1 N, ((Λ d : ℝ) : ℂ) * W d
      = (∑ p ∈ Finset.Icc 1 N with Nat.Prime p, ((Real.log (p : ℝ) : ℝ) : ℂ) * W p)
        + ∑ d ∈ Finset.Icc 1 N, ((RHTower.Mertens.notPrimeVonMangoldt d : ℝ) : ℂ) * W d := by
    rw [Finset.sum_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [RHTower.Mertens.notPrimeVonMangoldt]
    by_cases hp : d.Prime
    · rw [if_pos hp, if_pos hp, ArithmeticFunction.vonMangoldt_apply_prime hp]
      push_cast
      ring
    · rw [if_neg hp, if_neg hp]
      ring
  rw [hsplit]
  refine le_trans (norm_add_le _ _) ?_
  have hWsize : ∀ d ∈ Finset.Icc 1 N, ‖W d‖ ≤ ((N / d : ℕ) : ℝ) := by
    intro d hd
    by_cases hpp : IsPrimePow d
    · show ‖(if IsPrimePow d then D d else 0)‖ ≤ ((N / d : ℕ) : ℝ)
      rw [if_pos hpp]
      refine le_trans (hDbound d hpp) ?_
      have hmin : 2 ≤ d.minFac := (Nat.minFac_prime hpp.ne_one).two_le
      have h1 : ((N / d) / d.minFac : ℕ) ≤ (N / d) / 2 := Nat.div_le_div_left hmin (by norm_num)
      have h1R : (((N / d) / d.minFac : ℕ) : ℝ) ≤ (((N / d) / 2 : ℕ) : ℝ) := by
        exact_mod_cast h1
      have h2 : 2 * (((N / d) / 2 : ℕ) : ℝ) ≤ ((N / d : ℕ) : ℝ) := by
        have := Nat.div_mul_le_self (N / d) 2
        have hcast : ((((N / d) / 2) * 2 : ℕ) : ℝ) ≤ ((N / d : ℕ) : ℝ) := by exact_mod_cast this
        push_cast at hcast ⊢
        linarith
      linarith
    · show ‖(if IsPrimePow d then D d else 0)‖ ≤ ((N / d : ℕ) : ℝ)
      rw [if_neg hpp, norm_zero]
      positivity
  have htail := norm_sum_notPrimeVonMangoldt_weight_le (N := N) W hWsize
  have hhead : ‖∑ p ∈ Finset.Icc 1 N with Nat.Prime p,
      ((Real.log (p : ℝ) : ℝ) : ℂ) * W p‖ ≤ 16 * (N : ℝ) := by
    refine le_trans (norm_sum_le _ _) ?_
    have hterm : ∀ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
        ‖((Real.log (p : ℝ) : ℝ) : ℂ) * W p‖
          ≤ 2 * (N : ℝ) * (Real.log (p : ℝ) / (p : ℝ) ^ 2) := by
      intro p hp
      rw [Finset.mem_filter, Finset.mem_Icc] at hp
      obtain ⟨⟨hp1, hpN⟩, hpp⟩ := hp
      have hp2 : 2 ≤ p := hpp.two_le
      have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
      have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
      have hlogp : (0 : ℝ) ≤ Real.log p := Real.log_nonneg (by linarith)
      have hWp : ‖W p‖ ≤ 2 * (((N / p) / p : ℕ) : ℝ) := by
        show ‖(if IsPrimePow p then D p else 0)‖ ≤ 2 * (((N / p) / p : ℕ) : ℝ)
        rw [if_pos hpp.isPrimePow]
        have h := hDbound p hpp.isPrimePow
        rwa [hpp.minFac_eq] at h
      have hdiv : (((N / p) / p : ℕ) : ℝ) ≤ (N : ℝ) / (p : ℝ) ^ 2 := by
        have h1 : ((N / p) / p : ℕ) = N / (p * p) := Nat.div_div_eq_div_mul N p p
        rw [h1]
        have h2 : ((N / (p * p) : ℕ) : ℝ) ≤ (N : ℝ) / ((p * p : ℕ) : ℝ) := Nat.cast_div_le
        have h3 : ((p * p : ℕ) : ℝ) = (p : ℝ) ^ 2 := by push_cast; ring
        rw [h3] at h2
        exact h2
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlogp]
      have hW2 : ‖W p‖ ≤ 2 * ((N : ℝ) / (p : ℝ) ^ 2) := by
        have h4 := mul_le_mul_of_nonneg_left hdiv (by norm_num : (0 : ℝ) ≤ 2)
        linarith [hWp]
      have hfin : Real.log p * ‖W p‖ ≤ Real.log p * (2 * ((N : ℝ) / (p : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left hW2 hlogp
      have hid : Real.log p * (2 * ((N : ℝ) / (p : ℝ) ^ 2))
          = 2 * (N : ℝ) * (Real.log p / (p : ℝ) ^ 2) := by ring
      linarith [hfin, hid.le, hid.ge]
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.mul_sum]
    have hsub : (Finset.Icc 1 N).filter Nat.Prime ⊆ Finset.Icc 2 N := by
      intro p hp
      rw [Finset.mem_filter, Finset.mem_Icc] at hp
      rw [Finset.mem_Icc]
      exact ⟨hp.2.two_le, hp.1.2⟩
    have hnn : ∀ n ∈ Finset.Icc 2 N, n ∉ (Finset.Icc 1 N).filter Nat.Prime →
        0 ≤ Real.log (n : ℝ) / (n : ℝ) ^ 2 := by
      intro n hn _
      rw [Finset.mem_Icc] at hn
      have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast le_trans (by norm_num) hn.1
      positivity
    have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub hnn
    have hfin := sum_log_div_sq_Icc_le N
    have hNn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    nlinarith [hle, hfin, hNn]
  linarith [hhead, htail]

end

end RHTower.Sieve
