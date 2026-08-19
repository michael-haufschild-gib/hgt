import GaloisForLFunctions.RHTower.Sieve.RoughCountTuran

/-!
# Turán–Kubilius for a product of two prime counts

Matomäki–Radziwiłł's argument in Soundararajan's exposé §4 weights the Möbius function by
`ω_P(n)·ω_Q(n)` for two disjoint prime sets, and needs

```text
  ∑_{n ≤ M} (ω_P(n)ω_Q(n) − W(P)W(Q))² ≪ M·W(P)W(Q)(W(P) + W(Q) + 1) + (prime counts) .
```

The mechanism is that a product of four prime-divisibility indicators is the indicator of a single
modulus — the product of the two pair lcms — so the fourth moment factorises as
`(W(P)² + W(P))(W(Q)² + W(Q))`.
-/

namespace RHTower.Sieve

open Finset

/-- The lcm of two primes. -/
def lcmPair (a b : ℕ) : ℕ := if a = b then a else a * b

theorem lcmPair_pos {a b : ℕ} (ha : 0 < a) (hb : 0 < b) : 0 < lcmPair a b := by
  rw [lcmPair]
  split
  · exact ha
  · exact Nat.mul_pos ha hb

theorem dvd_left_of_lcmPair (a b : ℕ) : a ∣ lcmPair a b := by
  rw [lcmPair]
  by_cases h : a = b
  · rw [if_pos h]
  · rw [if_neg h]; exact Dvd.intro b rfl

theorem dvd_right_of_lcmPair (a b : ℕ) : b ∣ lcmPair a b := by
  rw [lcmPair]
  by_cases h : a = b
  · rw [if_pos h, h]
  · rw [if_neg h]; exact Dvd.intro_left a rfl

theorem lcmPair_dvd {a b n : ℕ} (hap : a.Prime) (hbp : b.Prime) (ha : a ∣ n) (hb : b ∣ n) :
    lcmPair a b ∣ n := by
  rw [lcmPair]
  by_cases h : a = b
  · rw [if_pos h]; exact ha
  · rw [if_neg h]
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd ((Nat.coprime_primes hap hbp).2 h) ha hb

theorem inv_lcmPair (a b : ℕ) :
    (1 : ℝ) / ((lcmPair a b : ℕ) : ℝ)
      = if a = b then (1 : ℝ) / (a : ℝ) else (1 : ℝ) / ((a : ℝ) * (b : ℝ)) := by
  rw [lcmPair]
  by_cases h : a = b
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]
    push_cast
    rfl

/-- **The pair sum of inverse lcms.** -/
theorem sum_inv_lcmPair_le {P : Finset ℕ} (hP : ∀ p ∈ P, 0 < p) :
    ∑ a ∈ P, ∑ b ∈ P, (1 : ℝ) / ((lcmPair a b : ℕ) : ℝ)
      ≤ (∑ p ∈ P, (1 : ℝ) / (p : ℝ)) ^ 2 + ∑ p ∈ P, (1 : ℝ) / (p : ℝ) := by
  classical
  have hsplit : ∀ a ∈ P, ∑ b ∈ P, (1 : ℝ) / ((lcmPair a b : ℕ) : ℝ)
      ≤ (1 : ℝ) / (a : ℝ) + (1 : ℝ) / (a : ℝ) * ∑ p ∈ P, (1 : ℝ) / (p : ℝ) := by
    intro a ha
    have ha0 : (0 : ℝ) < (a : ℝ) := by exact_mod_cast hP a ha
    have hterm : ∀ b ∈ P, (1 : ℝ) / ((lcmPair a b : ℕ) : ℝ)
        ≤ (if b = a then (1 : ℝ) / (a : ℝ) else 0) + (1 : ℝ) / (a : ℝ) * ((1 : ℝ) / (b : ℝ)) := by
      intro b hb
      have hb0 : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hP b hb
      rw [inv_lcmPair a b]
      by_cases hab : a = b
      · rw [if_pos hab, if_pos hab.symm, hab]
        have hpos : (0 : ℝ) ≤ (1 : ℝ) / (b : ℝ) * ((1 : ℝ) / (b : ℝ)) := by positivity
        linarith
      · rw [if_neg hab, if_neg (fun hc : b = a => hab hc.symm)]
        have hval : (1 : ℝ) / ((a : ℝ) * (b : ℝ))
            = (1 : ℝ) / (a : ℝ) * ((1 : ℝ) / (b : ℝ)) := by field_simp
        linarith [hval]
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    have hdiag : ∑ b ∈ P, (if b = a then (1 : ℝ) / (a : ℝ) else 0) = (1 : ℝ) / (a : ℝ) := by
      rw [Finset.sum_ite_eq' P a (fun _ => (1 : ℝ) / (a : ℝ)), if_pos ha]
    rw [hdiag]
  refine le_trans (Finset.sum_le_sum hsplit) ?_
  rw [Finset.sum_add_distrib, ← Finset.sum_mul]
  have hsq : (∑ p ∈ P, (1 : ℝ) / (p : ℝ)) * (∑ p ∈ P, (1 : ℝ) / (p : ℝ))
      = (∑ p ∈ P, (1 : ℝ) / (p : ℝ)) ^ 2 := by ring
  linarith [hsq]

/-- The modulus attached to a quadruple of primes drawn from two disjoint sets. -/
def quadModulus (p₁ p₂ q₁ q₂ : ℕ) : ℕ := lcmPair p₁ p₂ * lcmPair q₁ q₂

theorem coprime_lcmPair {p₁ p₂ q₁ q₂ : ℕ} (hp₁ : p₁.Prime) (hp₂ : p₂.Prime)
    (hq₁ : q₁.Prime) (hq₂ : q₂.Prime) (h₁₁ : p₁ ≠ q₁) (h₁₂ : p₁ ≠ q₂) (h₂₁ : p₂ ≠ q₁)
    (h₂₂ : p₂ ≠ q₂) : Nat.Coprime (lcmPair p₁ p₂) (lcmPair q₁ q₂) := by
  have c11 : Nat.Coprime p₁ q₁ := (Nat.coprime_primes hp₁ hq₁).2 h₁₁
  have c12 : Nat.Coprime p₁ q₂ := (Nat.coprime_primes hp₁ hq₂).2 h₁₂
  have c21 : Nat.Coprime p₂ q₁ := (Nat.coprime_primes hp₂ hq₁).2 h₂₁
  have c22 : Nat.Coprime p₂ q₂ := (Nat.coprime_primes hp₂ hq₂).2 h₂₂
  rw [lcmPair, lcmPair]
  by_cases hp : p₁ = p₂
  · rw [if_pos hp]
    by_cases hq : q₁ = q₂
    · rw [if_pos hq]; exact c11
    · rw [if_neg hq]; exact Nat.Coprime.mul_right c11 c12
  · rw [if_neg hp]
    by_cases hq : q₁ = q₂
    · rw [if_pos hq]; exact Nat.Coprime.mul_left c11 c21
    · rw [if_neg hq]
      exact Nat.Coprime.mul_left (Nat.Coprime.mul_right c11 c12)
        (Nat.Coprime.mul_right c21 c22)

/-- **A product of four prime-divisibility indicators is the indicator of one modulus.** -/
theorem indicator_quad_le {p₁ p₂ q₁ q₂ n : ℕ} (hp₁ : p₁.Prime) (hp₂ : p₂.Prime)
    (hq₁ : q₁.Prime) (hq₂ : q₂.Prime) (h₁₁ : p₁ ≠ q₁) (h₁₂ : p₁ ≠ q₂) (h₂₁ : p₂ ≠ q₁)
    (h₂₂ : p₂ ≠ q₂) :
    ((if p₁ ∣ n then (1 : ℝ) else 0) * (if p₂ ∣ n then (1 : ℝ) else 0))
        * ((if q₁ ∣ n then (1 : ℝ) else 0) * (if q₂ ∣ n then (1 : ℝ) else 0))
      ≤ (if quadModulus p₁ p₂ q₁ q₂ ∣ n then (1 : ℝ) else 0) := by
  by_cases h1 : p₁ ∣ n
  · by_cases h2 : p₂ ∣ n
    · by_cases h3 : q₁ ∣ n
      · by_cases h4 : q₂ ∣ n
        · have hd : quadModulus p₁ p₂ q₁ q₂ ∣ n :=
            Nat.Coprime.mul_dvd_of_dvd_of_dvd
              (coprime_lcmPair hp₁ hp₂ hq₁ hq₂ h₁₁ h₁₂ h₂₁ h₂₂)
              (lcmPair_dvd hp₁ hp₂ h1 h2) (lcmPair_dvd hq₁ hq₂ h3 h4)
          rw [if_pos h1, if_pos h2, if_pos h3, if_pos h4, if_pos hd]
          norm_num
        · rw [if_neg h4, mul_zero, mul_zero]
          split <;> norm_num
      · rw [if_neg h3, zero_mul, mul_zero]
        split <;> norm_num
    · rw [if_neg h2, mul_zero, zero_mul]
      split <;> norm_num
  · rw [if_neg h1, zero_mul, zero_mul]
    split <;> norm_num

theorem sum_indicator_dvd_le (L M : ℕ) :
    ∑ n ∈ Finset.Icc 1 M, (if L ∣ n then (1 : ℝ) else 0) ≤ (M : ℝ) / (L : ℝ) := by
  classical
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one, card_Icc_filter_dvd]
  exact Nat.cast_div_le

/-- **The joint fourth moment of two disjoint prime counts.** -/
theorem sum_sq_mul_sq_primeFactorsIn_le {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (hQ : ∀ q ∈ Q, q.Prime) (hPQ : Disjoint P Q) (M : ℕ) :
    ∑ n ∈ Finset.Icc 1 M,
        ((primeFactorsIn P n).card : ℝ) ^ 2 * ((primeFactorsIn Q n).card : ℝ) ^ 2
      ≤ (M : ℝ) * ((∑ p ∈ P, (1 : ℝ) / (p : ℝ)) ^ 2 + ∑ p ∈ P, (1 : ℝ) / (p : ℝ))
          * ((∑ q ∈ Q, (1 : ℝ) / (q : ℝ)) ^ 2 + ∑ q ∈ Q, (1 : ℝ) / (q : ℝ)) := by
  classical
  have hne : ∀ p ∈ P, ∀ q ∈ Q, p ≠ q := by
    intro p hp q hq hpq
    subst hpq
    exact (Finset.disjoint_left.1 hPQ hp) hq
  -- expand the fourth power as a quadruple sum
  have hexp : ∀ n : ℕ,
      ((primeFactorsIn P n).card : ℝ) ^ 2 * ((primeFactorsIn Q n).card : ℝ) ^ 2
        = ∑ p₁ ∈ P, ∑ p₂ ∈ P, ∑ q₁ ∈ Q, ∑ q₂ ∈ Q,
            ((if p₁ ∣ n then (1 : ℝ) else 0) * (if p₂ ∣ n then (1 : ℝ) else 0))
              * ((if q₁ ∣ n then (1 : ℝ) else 0) * (if q₂ ∣ n then (1 : ℝ) else 0)) := by
    intro n
    rw [card_primeFactorsIn_eq_sum, card_primeFactorsIn_eq_sum, sq, sq,
      Finset.sum_mul_sum, Finset.sum_mul_sum]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun p₁ _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun p₂ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q₁ _ => ?_
    rw [Finset.mul_sum]
  calc ∑ n ∈ Finset.Icc 1 M,
        ((primeFactorsIn P n).card : ℝ) ^ 2 * ((primeFactorsIn Q n).card : ℝ) ^ 2
      = ∑ n ∈ Finset.Icc 1 M, ∑ p₁ ∈ P, ∑ p₂ ∈ P, ∑ q₁ ∈ Q, ∑ q₂ ∈ Q,
          ((if p₁ ∣ n then (1 : ℝ) else 0) * (if p₂ ∣ n then (1 : ℝ) else 0))
            * ((if q₁ ∣ n then (1 : ℝ) else 0) * (if q₂ ∣ n then (1 : ℝ) else 0)) :=
        Finset.sum_congr rfl fun n _ => hexp n
    _ = ∑ p₁ ∈ P, ∑ p₂ ∈ P, ∑ q₁ ∈ Q, ∑ q₂ ∈ Q, ∑ n ∈ Finset.Icc 1 M,
          ((if p₁ ∣ n then (1 : ℝ) else 0) * (if p₂ ∣ n then (1 : ℝ) else 0))
            * ((if q₁ ∣ n then (1 : ℝ) else 0) * (if q₂ ∣ n then (1 : ℝ) else 0)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun p₁ _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun p₂ _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun q₁ _ => ?_
        rw [Finset.sum_comm]
    _ ≤ ∑ p₁ ∈ P, ∑ p₂ ∈ P, ∑ q₁ ∈ Q, ∑ q₂ ∈ Q,
          (M : ℝ) * ((1 : ℝ) / ((lcmPair p₁ p₂ : ℕ) : ℝ))
            * ((1 : ℝ) / ((lcmPair q₁ q₂ : ℕ) : ℝ)) := by
        refine Finset.sum_le_sum fun p₁ hp₁ => Finset.sum_le_sum fun p₂ hp₂ =>
          Finset.sum_le_sum fun q₁ hq₁ => Finset.sum_le_sum fun q₂ hq₂ => ?_
        have hL : 0 < quadModulus p₁ p₂ q₁ q₂ :=
          Nat.mul_pos (lcmPair_pos (hP p₁ hp₁).pos (hP p₂ hp₂).pos)
            (lcmPair_pos (hQ q₁ hq₁).pos (hQ q₂ hq₂).pos)
        refine le_trans (Finset.sum_le_sum fun n _ =>
          indicator_quad_le (hP p₁ hp₁) (hP p₂ hp₂) (hQ q₁ hq₁) (hQ q₂ hq₂)
            (hne p₁ hp₁ q₁ hq₁) (hne p₁ hp₁ q₂ hq₂) (hne p₂ hp₂ q₁ hq₁)
            (hne p₂ hp₂ q₂ hq₂)) ?_
        refine le_trans (sum_indicator_dvd_le _ M) (le_of_eq ?_)
        rw [quadModulus]
        push_cast
        field_simp
    _ = (M : ℝ) * (∑ p₁ ∈ P, ∑ p₂ ∈ P, (1 : ℝ) / ((lcmPair p₁ p₂ : ℕ) : ℝ))
          * (∑ q₁ ∈ Q, ∑ q₂ ∈ Q, (1 : ℝ) / ((lcmPair q₁ q₂ : ℕ) : ℝ)) := by
        have hinner : ∀ p₁ p₂ : ℕ,
            (∑ q₁ ∈ Q, ∑ q₂ ∈ Q, (M : ℝ) * ((1 : ℝ) / ((lcmPair p₁ p₂ : ℕ) : ℝ))
                * ((1 : ℝ) / ((lcmPair q₁ q₂ : ℕ) : ℝ)))
              = ((M : ℝ) * ((1 : ℝ) / ((lcmPair p₁ p₂ : ℕ) : ℝ)))
                * (∑ q₁ ∈ Q, ∑ q₂ ∈ Q, (1 : ℝ) / ((lcmPair q₁ q₂ : ℕ) : ℝ)) := by
          intro p₁ p₂
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun q₁ _ => ?_
          rw [Finset.mul_sum]
        have hstep1 : (∑ p₁ ∈ P, ∑ p₂ ∈ P, ∑ q₁ ∈ Q, ∑ q₂ ∈ Q,
              (M : ℝ) * ((1 : ℝ) / ((lcmPair p₁ p₂ : ℕ) : ℝ))
                * ((1 : ℝ) / ((lcmPair q₁ q₂ : ℕ) : ℝ)))
            = ∑ p₁ ∈ P, ∑ p₂ ∈ P, ((M : ℝ) * ((1 : ℝ) / ((lcmPair p₁ p₂ : ℕ) : ℝ)))
                * (∑ q₁ ∈ Q, ∑ q₂ ∈ Q, (1 : ℝ) / ((lcmPair q₁ q₂ : ℕ) : ℝ)) :=
          Finset.sum_congr rfl fun p₁ _ => Finset.sum_congr rfl fun p₂ _ => hinner p₁ p₂
        have hstep2 : (∑ p₁ ∈ P, ∑ p₂ ∈ P, ((M : ℝ) * ((1 : ℝ) / ((lcmPair p₁ p₂ : ℕ) : ℝ)))
                * (∑ q₁ ∈ Q, ∑ q₂ ∈ Q, (1 : ℝ) / ((lcmPair q₁ q₂ : ℕ) : ℝ)))
            = (∑ p₁ ∈ P, ∑ p₂ ∈ P, (M : ℝ) * ((1 : ℝ) / ((lcmPair p₁ p₂ : ℕ) : ℝ)))
                * (∑ q₁ ∈ Q, ∑ q₂ ∈ Q, (1 : ℝ) / ((lcmPair q₁ q₂ : ℕ) : ℝ)) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun p₁ _ => ?_
          rw [Finset.sum_mul]
        have hstep3 : (∑ p₁ ∈ P, ∑ p₂ ∈ P, (M : ℝ) * ((1 : ℝ) / ((lcmPair p₁ p₂ : ℕ) : ℝ)))
            = (M : ℝ) * ∑ p₁ ∈ P, ∑ p₂ ∈ P, (1 : ℝ) / ((lcmPair p₁ p₂ : ℕ) : ℝ) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun p₁ _ => ?_
          rw [Finset.mul_sum]
        rw [hstep1, hstep2, hstep3]
    _ ≤ (M : ℝ) * ((∑ p ∈ P, (1 : ℝ) / (p : ℝ)) ^ 2 + ∑ p ∈ P, (1 : ℝ) / (p : ℝ))
          * ((∑ q ∈ Q, (1 : ℝ) / (q : ℝ)) ^ 2 + ∑ q ∈ Q, (1 : ℝ) / (q : ℝ)) := by
        have hPb := sum_inv_lcmPair_le (P := P) fun p hp => (hP p hp).pos
        have hQb := sum_inv_lcmPair_le (P := Q) fun q hq => (hQ q hq).pos
        have hPnn : (0 : ℝ) ≤ ∑ p₁ ∈ P, ∑ p₂ ∈ P, (1 : ℝ) / ((lcmPair p₁ p₂ : ℕ) : ℝ) :=
          Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
        have hQnn : (0 : ℝ) ≤ ∑ q₁ ∈ Q, ∑ q₂ ∈ Q, (1 : ℝ) / ((lcmPair q₁ q₂ : ℕ) : ℝ) :=
          Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
        have hM : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg _
        have hQ0 : (0 : ℝ) ≤ (∑ q ∈ Q, (1 : ℝ) / (q : ℝ)) ^ 2 + ∑ q ∈ Q, (1 : ℝ) / (q : ℝ) := by
          have : (0 : ℝ) ≤ ∑ q ∈ Q, (1 : ℝ) / (q : ℝ) :=
            Finset.sum_nonneg fun _ _ => by positivity
          positivity
        have h1 : (M : ℝ) * (∑ p₁ ∈ P, ∑ p₂ ∈ P, (1 : ℝ) / ((lcmPair p₁ p₂ : ℕ) : ℝ))
            ≤ (M : ℝ) * ((∑ p ∈ P, (1 : ℝ) / (p : ℝ)) ^ 2 + ∑ p ∈ P, (1 : ℝ) / (p : ℝ)) :=
          mul_le_mul_of_nonneg_left hPb hM
        exact mul_le_mul h1 hQb hQnn (by positivity)

theorem cast_div_sub_one_le (M L : ℕ) (hL : 0 < L) :
    (M : ℝ) / (L : ℝ) - 1 ≤ ((M / L : ℕ) : ℝ) := by
  have hLR : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hlt : M < (M / L + 1) * L := (Nat.div_lt_iff_lt_mul hL).1 (Nat.lt_succ_self _)
  have hltR : (M : ℝ) < (((M / L : ℕ) : ℝ) + 1) * (L : ℝ) := by exact_mod_cast hlt
  rw [sub_le_iff_le_add, div_le_iff₀ hLR]
  linarith [hltR]

/-- **The joint first moment of two disjoint prime counts, from below.** -/
theorem sum_mul_card_primeFactorsIn_ge {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (hQ : ∀ q ∈ Q, q.Prime) (hPQ : Disjoint P Q) (M : ℕ) :
    (M : ℝ) * (∑ p ∈ P, (1 : ℝ) / (p : ℝ)) * (∑ q ∈ Q, (1 : ℝ) / (q : ℝ))
        - (P.card : ℝ) * (Q.card : ℝ)
      ≤ ∑ n ∈ Finset.Icc 1 M,
          ((primeFactorsIn P n).card : ℝ) * ((primeFactorsIn Q n).card : ℝ) := by
  classical
  have hne : ∀ p ∈ P, ∀ q ∈ Q, p ≠ q := by
    intro p hp q hq hpq
    subst hpq
    exact (Finset.disjoint_left.1 hPQ hp) hq
  have hexp : ∀ n : ℕ,
      ((primeFactorsIn P n).card : ℝ) * ((primeFactorsIn Q n).card : ℝ)
        = ∑ p ∈ P, ∑ q ∈ Q,
            (if p ∣ n then (1 : ℝ) else 0) * (if q ∣ n then (1 : ℝ) else 0) := by
    intro n
    rw [card_primeFactorsIn_eq_sum, card_primeFactorsIn_eq_sum, Finset.sum_mul_sum]
  have hswap : ∑ n ∈ Finset.Icc 1 M,
        ((primeFactorsIn P n).card : ℝ) * ((primeFactorsIn Q n).card : ℝ)
      = ∑ p ∈ P, ∑ q ∈ Q, ∑ n ∈ Finset.Icc 1 M,
          (if p ∣ n then (1 : ℝ) else 0) * (if q ∣ n then (1 : ℝ) else 0) := by
    rw [Finset.sum_congr rfl fun n _ => hexp n, Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_comm]
  rw [hswap]
  have hterm : ∀ p ∈ P, ∀ q ∈ Q,
      (M : ℝ) * ((1 : ℝ) / (p : ℝ)) * ((1 : ℝ) / (q : ℝ)) - 1
        ≤ ∑ n ∈ Finset.Icc 1 M,
            (if p ∣ n then (1 : ℝ) else 0) * (if q ∣ n then (1 : ℝ) else 0) := by
    intro p hp q hq
    have hcop : Nat.Coprime p q := (Nat.coprime_primes (hP p hp) (hQ q hq)).2 (hne p hp q hq)
    have heq : ∀ n : ℕ, (if p ∣ n then (1 : ℝ) else 0) * (if q ∣ n then (1 : ℝ) else 0)
        = (if p * q ∣ n then (1 : ℝ) else 0) := by
      intro n
      by_cases hpn : p ∣ n
      · by_cases hqn : q ∣ n
        · rw [if_pos hpn, if_pos hqn, if_pos (hcop.mul_dvd_of_dvd_of_dvd hpn hqn), mul_one]
        · rw [if_neg hqn, mul_zero, if_neg (fun hc => hqn (dvd_trans (Dvd.intro_left p rfl) hc))]
      · rw [if_neg hpn, zero_mul, if_neg (fun hc => hpn (dvd_trans (Dvd.intro q rfl) hc))]
    rw [Finset.sum_congr rfl fun n _ => heq n, ← Finset.sum_filter, Finset.sum_const,
      nsmul_eq_mul, mul_one, card_Icc_filter_dvd]
    have hpq : 0 < p * q := Nat.mul_pos (hP p hp).pos (hQ q hq).pos
    have hbase := cast_div_sub_one_le M (p * q) hpq
    have hcast : ((p * q : ℕ) : ℝ) = (p : ℝ) * (q : ℝ) := by push_cast; ring
    rw [hcast] at hbase
    have hval : (M : ℝ) * ((1 : ℝ) / (p : ℝ)) * ((1 : ℝ) / (q : ℝ))
        = (M : ℝ) / ((p : ℝ) * (q : ℝ)) := by
      field_simp
    rw [hval]
    exact hbase
  refine le_trans (le_of_eq ?_) (Finset.sum_le_sum fun p hp => Finset.sum_le_sum (hterm p hp))
  have hsum : ∑ p ∈ P, ∑ q ∈ Q, ((M : ℝ) * ((1 : ℝ) / (p : ℝ)) * ((1 : ℝ) / (q : ℝ)) - 1)
      = (M : ℝ) * (∑ p ∈ P, (1 : ℝ) / (p : ℝ)) * (∑ q ∈ Q, (1 : ℝ) / (q : ℝ))
        - (P.card : ℝ) * (Q.card : ℝ) := by
    have hinner : ∀ p : ℕ, ∑ q ∈ Q, ((M : ℝ) * ((1 : ℝ) / (p : ℝ)) * ((1 : ℝ) / (q : ℝ)) - 1)
        = (M : ℝ) * ((1 : ℝ) / (p : ℝ)) * (∑ q ∈ Q, (1 : ℝ) / (q : ℝ)) - (Q.card : ℝ) := by
      intro p
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, Finset.mul_sum]
    have hfac : ∑ p ∈ P, (M : ℝ) * ((1 : ℝ) / (p : ℝ))
        = (M : ℝ) * ∑ p ∈ P, (1 : ℝ) / (p : ℝ) := by rw [Finset.mul_sum]
    rw [Finset.sum_congr rfl fun p _ => hinner p, Finset.sum_sub_distrib, Finset.sum_const,
      nsmul_eq_mul, ← Finset.sum_mul, hfac]
  exact hsum.symm

/-- **Turán–Kubilius for the product of two disjoint prime counts.** -/
theorem sum_sq_joint_deviation_le {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (hQ : ∀ q ∈ Q, q.Prime) (hPQ : Disjoint P Q) (M : ℕ) :
    ∑ n ∈ Finset.Icc 1 M,
        (((primeFactorsIn P n).card : ℝ) * ((primeFactorsIn Q n).card : ℝ)
          - (∑ p ∈ P, (1 : ℝ) / (p : ℝ)) * (∑ q ∈ Q, (1 : ℝ) / (q : ℝ))) ^ 2
      ≤ (M : ℝ) * ((∑ p ∈ P, (1 : ℝ) / (p : ℝ)) * (∑ q ∈ Q, (1 : ℝ) / (q : ℝ)))
          * ((∑ p ∈ P, (1 : ℝ) / (p : ℝ)) + (∑ q ∈ Q, (1 : ℝ) / (q : ℝ)) + 1)
        + 2 * ((∑ p ∈ P, (1 : ℝ) / (p : ℝ)) * (∑ q ∈ Q, (1 : ℝ) / (q : ℝ)))
            * (P.card : ℝ) * (Q.card : ℝ) := by
  classical
  set WP : ℝ := ∑ p ∈ P, (1 : ℝ) / (p : ℝ) with hWP
  set WQ : ℝ := ∑ q ∈ Q, (1 : ℝ) / (q : ℝ) with hWQ
  have hWP0 : (0 : ℝ) ≤ WP := by rw [hWP]; exact Finset.sum_nonneg fun _ _ => by positivity
  have hWQ0 : (0 : ℝ) ≤ WQ := by rw [hWQ]; exact Finset.sum_nonneg fun _ _ => by positivity
  have hexpand : ∀ n : ℕ,
      (((primeFactorsIn P n).card : ℝ) * ((primeFactorsIn Q n).card : ℝ) - WP * WQ) ^ 2
        = ((primeFactorsIn P n).card : ℝ) ^ 2 * ((primeFactorsIn Q n).card : ℝ) ^ 2
          - 2 * (WP * WQ)
            * (((primeFactorsIn P n).card : ℝ) * ((primeFactorsIn Q n).card : ℝ))
          + (WP * WQ) ^ 2 := by
    intro n; ring
  rw [Finset.sum_congr rfl fun n _ => hexpand n, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_const, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel]
  have hfourth := sum_sq_mul_sq_primeFactorsIn_le hP hQ hPQ M
  have hfirst := sum_mul_card_primeFactorsIn_ge hP hQ hPQ M
  have hmul : ∑ n ∈ Finset.Icc 1 M, 2 * (WP * WQ)
        * (((primeFactorsIn P n).card : ℝ) * ((primeFactorsIn Q n).card : ℝ))
      = 2 * (WP * WQ) * ∑ n ∈ Finset.Icc 1 M,
          ((primeFactorsIn P n).card : ℝ) * ((primeFactorsIn Q n).card : ℝ) :=
    (Finset.mul_sum (Finset.Icc 1 M)
      (fun n => ((primeFactorsIn P n).card : ℝ) * ((primeFactorsIn Q n).card : ℝ))
      (2 * (WP * WQ))).symm
  rw [hmul]
  have hWnn : (0 : ℝ) ≤ 2 * (WP * WQ) := by positivity
  have hlow := mul_le_mul_of_nonneg_left hfirst hWnn
  rw [← hWP, ← hWQ] at hfourth hfirst
  nlinarith [hfourth, hlow, hWP0, hWQ0]

end RHTower.Sieve
