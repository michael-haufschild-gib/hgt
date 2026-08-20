import GaloisForLFunctions.RHTower.Sieve.SupportMeanSquare

/-!
# The rough count by Turán's second moment

Let `P` be a set of primes and `ω_P(n)` the number of members of `P` dividing `n`.  Its mean over
`[1, M]` is `A = ∑_{p ∈ P} 1/p` up to `|P|`, and its second moment exceeds the square of the mean by
at most the same amount, because two distinct primes dividing `n` force their product to divide `n`.
Chebyshev's inequality applied to the integers where `ω_P` vanishes then gives

```text
#{ n ≤ M : no p ∈ P divides n }  ≤  M/A + 2|P|/A ,        A = ∑_{p ∈ P} 1/p .
```

No sieve dimension, no Bombieri–Vinogradov, no Buchstab: only the exchange of two finite sums and
`⌊M/p⌋ ≥ M/p − 1`.  Since `A` diverges over a widening prime range, the rough integers have density
`o(1)`, which is exactly what a Ramaré factorisation of the Möbius polynomial needs — and the
`2|P|/A` term is what forces the prime range to stay below the length.
-/

noncomputable section

namespace RHTower.Sieve

open Finset

/-- The number of designated prime factors, as a sum of indicators. -/
theorem card_primeFactorsIn_eq_sum (P : Finset ℕ) (n : ℕ) :
    ((primeFactorsIn P n).card : ℝ) = ∑ p ∈ P, if p ∣ n then (1 : ℝ) else 0 := by
  classical
  rw [primeFactorsIn, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- The first moment of `ω_P` over `[1, M]`. -/
theorem sum_card_primeFactorsIn_Icc (P : Finset ℕ) (M : ℕ) :
    ∑ n ∈ Finset.Icc 1 M, ((primeFactorsIn P n).card : ℝ)
      = ∑ p ∈ P, ((M / p : ℕ) : ℝ) := by
  classical
  simp_rw [card_primeFactorsIn_eq_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one, card_Icc_filter_dvd]

/-- Two distinct designated primes dividing `n` force their product to divide `n`. -/
theorem sum_indicator_pair_le {P : Finset ℕ} (hPprime : ∀ p ∈ P, p.Prime) (M : ℕ)
    {p q : ℕ} (hp : p ∈ P) (hq : q ∈ P) (hpq : p ≠ q) :
    ∑ n ∈ Finset.Icc 1 M, (if p ∣ n then (1 : ℝ) else 0) * (if q ∣ n then (1 : ℝ) else 0)
      ≤ (M : ℝ) / ((p : ℝ) * (q : ℝ)) := by
  classical
  have hpP := hPprime p hp
  have hqP := hPprime q hq
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hpP hqP).2 hpq
  have hle : ∀ n ∈ Finset.Icc 1 M,
      (if p ∣ n then (1 : ℝ) else 0) * (if q ∣ n then (1 : ℝ) else 0)
        ≤ (if p * q ∣ n then (1 : ℝ) else 0) := by
    intro n _
    by_cases hpn : p ∣ n
    · by_cases hqn : q ∣ n
      · rw [if_pos hpn, if_pos hqn, if_pos (hcop.mul_dvd_of_dvd_of_dvd hpn hqn), mul_one]
      · rw [if_neg hqn, mul_zero]
        split <;> norm_num
    · rw [if_neg hpn, zero_mul]
      split <;> norm_num
  refine le_trans (Finset.sum_le_sum hle) ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one, card_Icc_filter_dvd]
  have hcast : ((M / (p * q) : ℕ) : ℝ) ≤ (M : ℝ) / ((p * q : ℕ) : ℝ) := Nat.cast_div_le
  have hpp : ((p * q : ℕ) : ℝ) = (p : ℝ) * (q : ℝ) := by push_cast; ring
  rw [hpp] at hcast
  exact hcast

/-- The second moment of `ω_P` over `[1, M]`. -/
theorem sum_sq_card_primeFactorsIn_Icc_le {P : Finset ℕ} (hPprime : ∀ p ∈ P, p.Prime) (M : ℕ) :
    ∑ n ∈ Finset.Icc 1 M, ((primeFactorsIn P n).card : ℝ) ^ 2
      ≤ (∑ p ∈ P, ((M / p : ℕ) : ℝ)) + (M : ℝ) * (∑ p ∈ P, (1 : ℝ) / (p : ℝ)) ^ 2 := by
  classical
  have hexpand : ∑ n ∈ Finset.Icc 1 M, ((primeFactorsIn P n).card : ℝ) ^ 2
      = ∑ p ∈ P, ∑ q ∈ P, ∑ n ∈ Finset.Icc 1 M,
          (if p ∣ n then (1 : ℝ) else 0) * (if q ∣ n then (1 : ℝ) else 0) := by
    have hstep : ∀ n : ℕ, ((primeFactorsIn P n).card : ℝ) ^ 2
        = ∑ p ∈ P, ∑ q ∈ P,
            (if p ∣ n then (1 : ℝ) else 0) * (if q ∣ n then (1 : ℝ) else 0) := by
      intro n
      rw [sq, card_primeFactorsIn_eq_sum, Finset.sum_mul_sum]
    simp_rw [hstep]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_comm]
  rw [hexpand]
  have hrow : ∀ p ∈ P, ∑ q ∈ P, ∑ n ∈ Finset.Icc 1 M,
      (if p ∣ n then (1 : ℝ) else 0) * (if q ∣ n then (1 : ℝ) else 0)
        ≤ ((M / p : ℕ) : ℝ) + (M : ℝ) * ((1 : ℝ) / (p : ℝ)) * (∑ q ∈ P, (1 : ℝ) / (q : ℝ)) := by
    intro p hp
    have hdiag : ∑ n ∈ Finset.Icc 1 M,
        (if p ∣ n then (1 : ℝ) else 0) * (if p ∣ n then (1 : ℝ) else 0)
          = ((M / p : ℕ) : ℝ) := by
      have hsq : ∀ n : ℕ, (if p ∣ n then (1 : ℝ) else 0) * (if p ∣ n then (1 : ℝ) else 0)
          = (if p ∣ n then (1 : ℝ) else 0) := by
        intro n
        split <;> norm_num
      simp_rw [hsq]
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one, card_Icc_filter_dvd]
    rw [← Finset.add_sum_erase P _ hp, hdiag]
    refine add_le_add le_rfl ?_
    have hoff : ∀ q ∈ P.erase p, ∑ n ∈ Finset.Icc 1 M,
        (if p ∣ n then (1 : ℝ) else 0) * (if q ∣ n then (1 : ℝ) else 0)
          ≤ (M : ℝ) * ((1 : ℝ) / (p : ℝ)) * ((1 : ℝ) / (q : ℝ)) := by
      intro q hq
      have hqP : q ∈ P := Finset.mem_of_mem_erase hq
      have hne : p ≠ q := fun h => (Finset.ne_of_mem_erase hq) h.symm
      refine le_trans (sum_indicator_pair_le hPprime M hp hqP hne) (le_of_eq ?_)
      field_simp
    refine le_trans (Finset.sum_le_sum hoff) ?_
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ ?_
    · refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset p P) fun q _ _ => ?_
      positivity
    · have : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
      positivity
  refine le_trans (Finset.sum_le_sum hrow) (le_of_eq ?_)
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
  congr 1
  rw [sq]
  ring

/-- The first moment of `ω_P` is at least `M·A − |P|`. -/
theorem sum_card_primeFactorsIn_Icc_ge {P : Finset ℕ} (hP : ∀ p ∈ P, 0 < p) (M : ℕ) :
    (M : ℝ) * (∑ p ∈ P, (1 : ℝ) / (p : ℝ)) - (P.card : ℝ)
      ≤ ∑ n ∈ Finset.Icc 1 M, ((primeFactorsIn P n).card : ℝ) := by
  classical
  rw [sum_card_primeFactorsIn_Icc, Finset.mul_sum]
  have hterm : ∀ p ∈ P, (M : ℝ) * ((1 : ℝ) / (p : ℝ)) - 1 ≤ ((M / p : ℕ) : ℝ) := by
    intro p hp
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hP p hp
    have hdm : (p : ℝ) * ((M / p : ℕ) : ℝ) + ((M % p : ℕ) : ℝ) = (M : ℝ) := by
      exact_mod_cast Nat.div_add_mod M p
    have hmod : ((M % p : ℕ) : ℝ) < (p : ℝ) := by
      exact_mod_cast Nat.mod_lt M (hP p hp)
    have hkey : (M : ℝ) ≤ (((M / p : ℕ) : ℝ) + 1) * (p : ℝ) := by nlinarith
    have hdiv : (M : ℝ) / (p : ℝ) ≤ ((M / p : ℕ) : ℝ) + 1 := by
      rw [div_le_iff₀ hp0]
      exact hkey
    have hval : (M : ℝ) * ((1 : ℝ) / (p : ℝ)) = (M : ℝ) / (p : ℝ) := by ring
    rw [hval]
    linarith
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one] at hsum
  linarith

/-- The first moment of `ω_P` is at most `M·A`. -/
theorem sum_card_primeFactorsIn_Icc_le (P : Finset ℕ) (M : ℕ) :
    ∑ n ∈ Finset.Icc 1 M, ((primeFactorsIn P n).card : ℝ)
      ≤ (M : ℝ) * (∑ p ∈ P, (1 : ℝ) / (p : ℝ)) := by
  classical
  rw [sum_card_primeFactorsIn_Icc, Finset.mul_sum]
  refine Finset.sum_le_sum fun p _ => ?_
  have hcast : ((M / p : ℕ) : ℝ) ≤ (M : ℝ) / ((p : ℕ) : ℝ) := Nat.cast_div_le
  have hval : (M : ℝ) * ((1 : ℝ) / (p : ℝ)) = (M : ℝ) / (p : ℝ) := by ring
  rw [hval]
  exact hcast

/-- **Turán's second-moment bound on the rough count.** -/
theorem card_roughSet_mul_sq_le {P : Finset ℕ} (hPprime : ∀ p ∈ P, p.Prime) (M : ℕ) :
    ((supportMeanSquareRoughSet P M).card : ℝ) * (∑ p ∈ P, (1 : ℝ) / (p : ℝ)) ^ 2
      ≤ (M : ℝ) * (∑ p ∈ P, (1 : ℝ) / (p : ℝ))
        + 2 * (P.card : ℝ) * (∑ p ∈ P, (1 : ℝ) / (p : ℝ)) := by
  classical
  set A : ℝ := ∑ p ∈ P, (1 : ℝ) / (p : ℝ) with hAdef
  have hA0 : 0 ≤ A := by
    rw [hAdef]
    exact Finset.sum_nonneg fun p _ => by positivity
  set S1 : ℝ := ∑ n ∈ Finset.Icc 1 M, ((primeFactorsIn P n).card : ℝ) with hS1def
  set S2 : ℝ := ∑ n ∈ Finset.Icc 1 M, ((primeFactorsIn P n).card : ℝ) ^ 2 with hS2def
  have hcardIcc : ((Finset.Icc 1 M).card : ℝ) = (M : ℝ) := by
    rw [Nat.card_Icc]
    norm_num
  have hvar : ∑ n ∈ Finset.Icc 1 M, (((primeFactorsIn P n).card : ℝ) - A) ^ 2
      = S2 - 2 * A * S1 + A ^ 2 * (M : ℝ) := by
    have hterm : ∀ n : ℕ, (((primeFactorsIn P n).card : ℝ) - A) ^ 2
        = ((primeFactorsIn P n).card : ℝ) ^ 2
          - 2 * A * ((primeFactorsIn P n).card : ℝ) + A ^ 2 := by
      intro n; ring
    simp_rw [hterm]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
      nsmul_eq_mul, hcardIcc, hS1def, hS2def]
    ring
  have hlow : ((supportMeanSquareRoughSet P M).card : ℝ) * A ^ 2
      ≤ ∑ n ∈ Finset.Icc 1 M, (((primeFactorsIn P n).card : ℝ) - A) ^ 2 := by
    have hsub : supportMeanSquareRoughSet P M ⊆ Finset.Icc 1 M := by
      rw [supportMeanSquareRoughSet]
      exact Finset.filter_subset _ _
    have hmono : ∑ n ∈ supportMeanSquareRoughSet P M, (((primeFactorsIn P n).card : ℝ) - A) ^ 2
        ≤ ∑ n ∈ Finset.Icc 1 M, (((primeFactorsIn P n).card : ℝ) - A) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => by positivity
    have heq : ∑ n ∈ supportMeanSquareRoughSet P M, (((primeFactorsIn P n).card : ℝ) - A) ^ 2
        = ((supportMeanSquareRoughSet P M).card : ℝ) * A ^ 2 := by
      have hz : ∀ n ∈ supportMeanSquareRoughSet P M, (((primeFactorsIn P n).card : ℝ) - A) ^ 2 = A ^ 2 := by
        intro n hn
        rw [supportMeanSquareRoughSet, Finset.mem_filter] at hn
        rw [hn.2]
        norm_num
      rw [Finset.sum_congr rfl hz, Finset.sum_const, nsmul_eq_mul]
    linarith [hmono, heq]
  have hS2 : S2 ≤ S1 + (M : ℝ) * A ^ 2 := by
    have h := sum_sq_card_primeFactorsIn_Icc_le hPprime M
    rw [← sum_card_primeFactorsIn_Icc P M] at h
    rw [hS1def, hS2def, hAdef]
    exact h
  have hS1lo : (M : ℝ) * A - (P.card : ℝ) ≤ S1 :=
    sum_card_primeFactorsIn_Icc_ge (fun p hp => (hPprime p hp).pos) M
  have hS1hi : S1 ≤ (M : ℝ) * A := sum_card_primeFactorsIn_Icc_le P M
  have hkey : S2 - 2 * A * S1 + A ^ 2 * (M : ℝ)
      ≤ (M : ℝ) * A + 2 * (P.card : ℝ) * A := by
    have hmul : 2 * A * ((M : ℝ) * A - (P.card : ℝ)) ≤ 2 * A * S1 :=
      mul_le_mul_of_nonneg_left hS1lo (by linarith)
    nlinarith [hS2, hS1hi, hmul]
  rw [hvar] at hlow
  linarith [hlow, hkey]

/-- **The rough integers have density `1/A`.**  With `A = ∑_{p ∈ P} 1/p`, the integers of `[1, M]`
divisible by no member of `P` number at most `M/A + 2|P|/A`. -/
theorem card_roughSet_le {P : Finset ℕ} (hPprime : ∀ p ∈ P, p.Prime) (M : ℕ)
    (hA : 0 < ∑ p ∈ P, (1 : ℝ) / (p : ℝ)) :
    ((supportMeanSquareRoughSet P M).card : ℝ)
      ≤ (M : ℝ) / (∑ p ∈ P, (1 : ℝ) / (p : ℝ))
        + 2 * (P.card : ℝ) / (∑ p ∈ P, (1 : ℝ) / (p : ℝ)) := by
  set A : ℝ := ∑ p ∈ P, (1 : ℝ) / (p : ℝ) with hAdef
  have hbase := card_roughSet_mul_sq_le hPprime M
  rw [← hAdef] at hbase
  have hA2 : 0 < A ^ 2 := by positivity
  have hcomb : (M : ℝ) / A + 2 * (P.card : ℝ) / A = ((M : ℝ) + 2 * (P.card : ℝ)) / A := by
    field_simp
  rw [hcomb, le_div_iff₀ hA]
  have hstep : ((supportMeanSquareRoughSet P M).card : ℝ) * A * A ≤ ((M : ℝ) + 2 * (P.card : ℝ)) * A := by
    nlinarith [hbase]
  exact le_of_mul_le_mul_right hstep hA

/-- **The rough Möbius polynomial is inside the Matomäki–Radziwiłł budget.**  Once the designated
primes carry harmonic mass `A ≥ 15e/(2ε)` and number at most `M`, the mean square of the rough part
is below `2·W·M + ε·M²` at every height `W ≥ 1` — the diagonal is untouched and the height-free part
is `o(M²)`.  Nothing beyond Turán's second moment and the mean value theorem enters. -/
theorem integral_Icc_normSq_roughPoly_le_budget {P : Finset ℕ} (hPprime : ∀ p ∈ P, p.Prime)
    (M : ℕ) {W ε : ℝ} (hW : 1 ≤ W) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hPM : (P.card : ℝ) ≤ (M : ℝ))
    (hA : 15 * Real.exp 1 / (2 * ε) ≤ ∑ p ∈ P, (1 : ℝ) / (p : ℝ)) :
    (∫ w in Set.Icc (-W) W,
      ‖logPoly (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) (supportMeanSquareRoughSet P M) w‖ ^ 2)
      ≤ 2 * W * (M : ℝ) + ε * (M : ℝ) ^ 2 := by
  have hexp1 : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hpi : Real.pi ≤ 4 := Real.pi_le_four
  have hA0 : 0 < ∑ p ∈ P, (1 : ℝ) / (p : ℝ) := by
    have : (0 : ℝ) < 15 * Real.exp 1 / (2 * ε) := by positivity
    linarith
  set A : ℝ := ∑ p ∈ P, (1 : ℝ) / (p : ℝ) with hAdef
  have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
  have hW0 : (0 : ℝ) < W := lt_of_lt_of_le zero_lt_one hW
  -- the rough count
  have hcount : ((supportMeanSquareRoughSet P M).card : ℝ) ≤ 3 * (M : ℝ) / A := by
    refine le_trans (card_roughSet_le hPprime M hA0) ?_
    have h1 : 2 * (P.card : ℝ) / A ≤ 2 * (M : ℝ) / A := by
      refine div_le_div_of_nonneg_right (by linarith) hA0.le
    have h2 : (M : ℝ) / A + 2 * (M : ℝ) / A = 3 * (M : ℝ) / A := by ring
    linarith
  -- the mean square
  have hcoef0 : (0 : ℝ) ≤ 5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * (M : ℝ) := by
    have := Real.pi_pos
    have := (Real.exp_pos 1).le
    positivity
  have hms := integral_Icc_normSq_roughPoly_le P M hW
  have hstep : (5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * (M : ℝ))
      * ((supportMeanSquareRoughSet P M).card : ℝ)
      ≤ (5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * (M : ℝ)) * (3 * (M : ℝ) / A) :=
    mul_le_mul_of_nonneg_left hcount hcoef0
  -- the harmonic mass converts the count into the budget
  have hinvA : 1 / A ≤ 2 * ε / (15 * Real.exp 1) := by
    rw [div_le_div_iff₀ hA0 (by positivity)]
    have hle : 15 * Real.exp 1 / (2 * ε) ≤ A := hA
    rw [div_le_iff₀ (by positivity)] at hle
    linarith
  have hval : (5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * (M : ℝ)) * (3 * (M : ℝ) / A)
      = (15 * Real.pi / 2 * W * (M : ℝ) + 15 * Real.exp 1 / 2 * (M : ℝ) ^ 2) * (1 / A) := by
    field_simp
    ring
  have hpos : (0 : ℝ) ≤ 15 * Real.pi / 2 * W * (M : ℝ) + 15 * Real.exp 1 / 2 * (M : ℝ) ^ 2 := by
    have := Real.pi_pos
    have := (Real.exp_pos 1).le
    positivity
  have hlast : (15 * Real.pi / 2 * W * (M : ℝ) + 15 * Real.exp 1 / 2 * (M : ℝ) ^ 2) * (1 / A)
      ≤ (15 * Real.pi / 2 * W * (M : ℝ) + 15 * Real.exp 1 / 2 * (M : ℝ) ^ 2)
          * (2 * ε / (15 * Real.exp 1)) := mul_le_mul_of_nonneg_left hinvA hpos
  have hfinal : (15 * Real.pi / 2 * W * (M : ℝ) + 15 * Real.exp 1 / 2 * (M : ℝ) ^ 2)
      * (2 * ε / (15 * Real.exp 1))
      ≤ 2 * W * (M : ℝ) + ε * (M : ℝ) ^ 2 := by
    have hE : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
    have hsplit : (15 * Real.pi / 2 * W * (M : ℝ) + 15 * Real.exp 1 / 2 * (M : ℝ) ^ 2)
        * (2 * ε / (15 * Real.exp 1))
        = (Real.pi * ε / Real.exp 1) * (W * (M : ℝ)) + ε * (M : ℝ) ^ 2 := by
      field_simp
    rw [hsplit]
    have hcoef : Real.pi * ε / Real.exp 1 ≤ 2 := by
      rw [div_le_iff₀ hE]
      nlinarith [hpi, hexp1, hε, hε1]
    have hWM : (0 : ℝ) ≤ W * (M : ℝ) := by positivity
    nlinarith [hcoef, hWM]
  linarith [hms, hstep, hval, hlast, hfinal]

end RHTower.Sieve

end
