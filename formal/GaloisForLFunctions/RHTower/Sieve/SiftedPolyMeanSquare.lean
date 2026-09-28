import GaloisForLFunctions.RHTower.Sieve.PrimePairAverageSharp
import GaloisForLFunctions.RHTower.Sieve.ImprovedMeanValue
import GaloisForLFunctions.RHTower.Sieve.HarmanMinorant

/-!
# The mean square of a sifted Dirichlet polynomial

A Dirichlet polynomial whose support avoids every prime of a range `(P₁, h]` has mean square
bounded by the diagonal plus the shifted pairs of the support, and the two-dimensional pair sieve
bounds those pairs with the full two-logarithm saving (Rankin level `h^{18} ≤ √z`):

```text
∫_{-W}^{W} |∑_{n ∈ s} a_n n^{2πiw}|² dw
   ≤ (5/(4δ)) B² ( |s| + 2(2e·K·N/E² + K·(sieve remainder)) ),     E = exp(mertensS h − mertensS P₁),
```

for `‖a_n‖ ≤ B`, `s ⊆ [1, N]`, `2πδW ≤ 1`, `K ≥ 3Nδ`.  This is the non-`U` estimate of
Matomäki–Teräväinen §5, applied to Harman's minorant, whose support is `z`-rough and whose values
are bounded by `1 + K + K² + K³` in the number `K` of prime factors above `z`.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- **Rough pairs averaged over the shift, at a fixed level ratio.** -/
theorem sum_card_roughPair_le_sharp (Y : ℝ) {P₁ : ℕ} (hP₁ : 2 ≤ P₁) {h : ℕ} (K : ℕ) {z : ℝ}
    (hz : 1 ≤ z) (hY : 0 ≤ Y) (hh2 : 2 ≤ h) (hP₁h : P₁ ≤ h)
    (hlev : ((h : ℝ)) ^ (18 : ℝ) ≤ Real.sqrt z)
    (hlog : 20 * mertensFirstConst ≤ Real.log h) :
    ∑ d ∈ Finset.Icc 1 K,
        ((((Finset.Icc 1 ⌊Y⌋₊).filter
            (fun m => (∀ p ∈ rangePrimes P₁ h, ¬ p ∣ m)
              ∧ ∀ p ∈ rangePrimes P₁ h, ¬ p ∣ (m + d))).card : ℕ) : ℝ)
      ≤ 2 * Real.exp 1 * (K : ℝ) * Y / (Real.exp (mertensS h - mertensS P₁)) ^ (2 : ℕ)
        + (K : ℝ) * ∑ e ∈ (rangePrimorial P₁ h).divisors,
            (if ((e : ℕ) : ℝ) ≤ z then 2 * 6 ^ e.primeFactors.card else 0) := by
  classical
  set E : ℝ := Real.exp (mertensS h - mertensS P₁) with hE
  set R : ℝ := ∑ e ∈ (rangePrimorial P₁ h).divisors,
      (if ((e : ℕ) : ℝ) ≤ z then 2 * 6 ^ e.primeFactors.card else 0) with hR
  have hE0 : (0 : ℝ) < E := Real.exp_pos _
  have hp3 : ∀ p ∈ rangePrimes P₁ h, (3 : ℝ) ≤ (p : ℝ) := by
    intro p hp
    rw [rangePrimes, Finset.mem_filter, Finset.mem_Icc] at hp
    have : 3 ≤ p := by omega
    exact_mod_cast this
  have hC0 : ∀ d : ℕ, (0 : ℝ)
      < ∏ p ∈ (rangePrimes P₁ h).filter (fun p => p ∣ d), (((p : ℝ) - 1) / (p : ℝ)) := by
    intro d
    refine Finset.prod_pos fun p hp => ?_
    have h3 := hp3 p (Finset.mem_filter.1 hp).1
    have hnum : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    have hden : (0 : ℝ) < (p : ℝ) := by linarith
    positivity
  have hterm : ∀ d : ℕ,
      ((((Finset.Icc 1 ⌊Y⌋₊).filter
            (fun m => (∀ p ∈ rangePrimes P₁ h, ¬ p ∣ m)
              ∧ ∀ p ∈ rangePrimes P₁ h, ¬ p ∣ (m + d))).card : ℕ) : ℝ)
        ≤ (2 * Y / E ^ (2 : ℕ))
            * (∏ p ∈ (rangePrimes P₁ h).filter (fun p => p ∣ d), ((p : ℝ) / ((p : ℝ) - 1)))
          + R := by
    intro d
    refine le_trans (card_roughPair_le_sharp Y hP₁ d hz hY hh2 hP₁h hlev hlog) ?_
    have hCd := hC0 d
    have hinv : (∏ p ∈ (rangePrimes P₁ h).filter (fun p => p ∣ d), ((p : ℝ) / ((p : ℝ) - 1)))
        = (∏ p ∈ (rangePrimes P₁ h).filter (fun p => p ∣ d), (((p : ℝ) - 1) / (p : ℝ)))⁻¹ := by
      rw [← Finset.prod_inv_distrib]
      refine Finset.prod_congr rfl fun p hp => ?_
      rw [inv_div]
    refine add_le_add ?_ le_rfl
    rw [hinv]
    have hval : Y / ((1 / 2) * (E ^ (2 : ℕ)
          * ∏ p ∈ (rangePrimes P₁ h).filter (fun p => p ∣ d), (((p : ℝ) - 1) / (p : ℝ))))
        = (2 * Y / E ^ (2 : ℕ))
          * (∏ p ∈ (rangePrimes P₁ h).filter (fun p => p ∣ d),
              (((p : ℝ) - 1) / (p : ℝ)))⁻¹ := by
      field_simp
    rw [hval]
  refine le_trans (Finset.sum_le_sum fun d _ => hterm d) ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
  have hK : ((K + 1 - 1 : ℕ) : ℝ) = (K : ℝ) := by
    congr 1
  rw [hK]
  refine add_le_add ?_ le_rfl
  rw [← Finset.mul_sum]
  have hbound : ∑ d ∈ Finset.Icc 1 K,
      (∏ p ∈ (rangePrimes P₁ h).filter (fun p => p ∣ d), ((p : ℝ) / ((p : ℝ) - 1)))
      ≤ Real.exp 1 * (K : ℝ) := sum_inv_shiftCorrection_le hP₁ h K
  have hcoef : (0 : ℝ) ≤ 2 * Y / E ^ (2 : ℕ) := by positivity
  calc (2 * Y / E ^ (2 : ℕ)) * ∑ d ∈ Finset.Icc 1 K,
        (∏ p ∈ (rangePrimes P₁ h).filter (fun p => p ∣ d), ((p : ℝ) / ((p : ℝ) - 1)))
      ≤ (2 * Y / E ^ (2 : ℕ)) * (Real.exp 1 * (K : ℝ)) := mul_le_mul_of_nonneg_left hbound hcoef
    _ = 2 * Real.exp 1 * (K : ℝ) * Y / E ^ (2 : ℕ) := by ring

/-- **The improved mean value theorem for a sifted support.** -/
theorem integral_normSq_logPoly_sifted_le (a : ℕ → ℂ) (s : Finset ℕ) {N h K P₁ : ℕ}
    {B δ W z : ℝ}
    (hs : ∀ n ∈ s, 1 ≤ n ∧ n ≤ N ∧ ∀ p ∈ rangePrimes P₁ h, ¬ p ∣ n)
    (ha : ∀ n ∈ s, ‖a n‖ ≤ B) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hWδ : 2 * Real.pi * δ * W ≤ 1) (hK : 3 * (N : ℝ) * δ ≤ (K : ℝ))
    (hP₁ : 2 ≤ P₁) (hz : 1 ≤ z) (hh2 : 2 ≤ h) (hP₁h : P₁ ≤ h)
    (hlev : ((h : ℝ)) ^ (18 : ℝ) ≤ Real.sqrt z)
    (hlog : 20 * mertensFirstConst ≤ Real.log h) :
    (∫ w in Set.Icc (-W) W, ‖logPoly a s w‖ ^ (2 : ℕ))
      ≤ (5 / (4 * δ)) * B ^ 2 * ((s.card : ℝ)
          + 2 * (2 * Real.exp 1 * (K : ℝ) * (N : ℝ)
                  / (Real.exp (mertensS h - mertensS P₁)) ^ (2 : ℕ)
                + (K : ℝ) * ∑ e ∈ (rangePrimorial P₁ h).divisors,
                    (if ((e : ℕ) : ℝ) ≤ z then 2 * 6 ^ e.primeFactors.card else 0))) := by
  classical
  have hbase := integral_Icc_normSq_logPoly_le_count a s hδ0 hWδ
  have hB0 : 0 ≤ B ∨ s = ∅ := by
    rcases Finset.eq_empty_or_nonempty s with h0 | ⟨n, hn⟩
    · exact Or.inr h0
    · exact Or.inl ((norm_nonneg _).trans (ha n hn))
  rcases hB0 with hB0 | hempty
  swap
  · subst hempty
    simp [logPoly]
    positivity
  have hweight : ∑ n ∈ s, (logNeighbourCount s δ n : ℝ) * ‖a n‖ ^ (2 : ℕ)
      ≤ B ^ 2 * ∑ n ∈ s, (logNeighbourCount s δ n : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun n hn => ?_
    have hc0 : (0 : ℝ) ≤ (logNeighbourCount s δ n : ℝ) := Nat.cast_nonneg _
    have hsq : ‖a n‖ ^ (2 : ℕ) ≤ B ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (ha n hn) 2
    nlinarith
  have hneigh : ∑ n ∈ s, (logNeighbourCount s δ n : ℝ)
      ≤ (s.card : ℝ) + 2 * ∑ d ∈ Finset.Icc 1 K, (#(s.filter (fun n => n + d ∈ s)) : ℝ) := by
    have := sum_card_neighbour_le s K (fun n m => |Real.log (n : ℝ) - Real.log (m : ℝ)| < δ)
      (fun n hn m hm hnm => le_add_of_log_close_range hδ0 hδ1 hK
        ⟨(hs n hn).1, (hs n hn).2.1⟩ ⟨(hs m hm).1, (hs m hm).2.1⟩ hnm)
    exact le_of_eq_of_le (Finset.sum_congr rfl fun n _ => rfl) this
  have hsub : ∀ d, (#(s.filter (fun n => n + d ∈ s)) : ℝ)
      ≤ ((((Finset.Icc 1 ⌊(N : ℝ)⌋₊).filter
            (fun m => (∀ p ∈ rangePrimes P₁ h, ¬ p ∣ m)
              ∧ ∀ p ∈ rangePrimes P₁ h, ¬ p ∣ (m + d))).card : ℕ) : ℝ) := by
    intro d
    refine Nat.cast_le.2 (Finset.card_le_card fun n hn => ?_)
    obtain ⟨hns, hnd⟩ := Finset.mem_filter.1 hn
    rw [Nat.floor_natCast]
    exact Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨(hs n hns).1, (hs n hns).2.1⟩,
      (hs n hns).2.2, (hs (n + d) hnd).2.2⟩
  have hpairs := sum_card_roughPair_le_sharp (N : ℝ) hP₁ K hz (Nat.cast_nonneg _) hh2 hP₁h hlev
    hlog
  have hsum := Finset.sum_le_sum fun d (_ : d ∈ Finset.Icc 1 K) => hsub d
  have hpos : (0 : ℝ) ≤ 5 / (4 * δ) := by positivity
  calc (∫ w in Set.Icc (-W) W, ‖logPoly a s w‖ ^ (2 : ℕ))
      ≤ (5 / (4 * δ)) * ∑ n ∈ s, (logNeighbourCount s δ n : ℝ) * ‖a n‖ ^ (2 : ℕ) := hbase
    _ ≤ (5 / (4 * δ)) * (B ^ 2 * ∑ n ∈ s, (logNeighbourCount s δ n : ℝ)) :=
        mul_le_mul_of_nonneg_left hweight hpos
    _ ≤ (5 / (4 * δ)) * (B ^ 2 * ((s.card : ℝ)
          + 2 * (2 * Real.exp 1 * (K : ℝ) * (N : ℝ)
                  / (Real.exp (mertensS h - mertensS P₁)) ^ (2 : ℕ)
                + (K : ℝ) * ∑ e ∈ (rangePrimorial P₁ h).divisors,
                    (if ((e : ℕ) : ℝ) ≤ z then 2 * 6 ^ e.primeFactors.card else 0)))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (sq_nonneg B)) hpos
        refine hneigh.trans ?_
        have := hsum.trans hpairs
        linarith
    _ = _ := by ring

/-- A small prime divisor survives division by a larger prime divisor. -/
theorem dvd_div_of_prime_lt {p q m : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (hpm : p ∣ m) (hqm : q ∣ m) : p ∣ m / q := by
  have hm : m = q * (m / q) := (Nat.mul_div_cancel' hqm).symm
  rw [hm] at hpm
  rcases (Nat.Prime.dvd_mul hp).1 hpm with h | h
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hp hq).1 h) (ne_of_lt hpq)
  · exact h

theorem rho_eq_zero_of_dvd {p m z : ℕ} (hp : p.Prime) (hpm : p ∣ m) (hpz : p < z) :
    rho m z = 0 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [rho]
  · exact rho_eq_zero_of_lt (Nat.mem_primeFactors.2 ⟨hp, hpm, hm.ne'⟩) hpz

/-- Harman's minorant vanishes off the `z`-rough integers. -/
theorem rhoMinus_eq_zero_of_dvd {z Q D E n p : ℕ} (hp : p.Prime) (hpn : p ∣ n) (hpz : p < z) :
    rhoMinus z Q D E n = 0 := by
  have h0 : rho n z = 0 := rho_eq_zero_of_dvd hp hpn hpz
  have hstep : ∀ m q, p ∣ m → (z ≤ q ∧ q.Prime ∧ q ∣ m) → p ∣ m / q := fun m q hpm hq =>
    dvd_div_of_prime_lt hp hq.2.1 (lt_of_lt_of_le hpz hq.1) hpm hq.2.2
  have hwin : ∀ m a b q, q ∈ primeWindow m a b → z ≤ a → z ≤ q ∧ q.Prime ∧ q ∣ m := by
    intro m a b q hq hza
    rw [mem_primeWindow] at hq
    exact ⟨hza.trans hq.1.1, hq.2⟩
  have h1 : harmanS1 z Q n = 0 := by
    rw [harmanS1]
    refine Finset.sum_eq_zero fun q hq => ?_
    exact rho_eq_zero_of_dvd hp (hstep n q hpn (hwin n z Q q hq le_rfl)) hpz
  have h2 : harmanS2 z D E n = 0 := by
    rw [harmanS2]
    refine Finset.sum_eq_zero fun q₁ hq₁ => Finset.sum_eq_zero fun q₂ hq₂ => ?_
    have hd1 := hstep n q₁ hpn (hwin n z D q₁ hq₁ le_rfl)
    have hq₂' := hwin (n / q₁) z q₁ q₂ (Finset.mem_of_mem_filter _ hq₂) le_rfl
    exact rho_eq_zero_of_dvd hp (hstep _ q₂ hd1 hq₂') hpz
  have h3 : harmanS3 z D E n = 0 := by
    rw [harmanS3]
    refine Finset.sum_eq_zero fun q₁ hq₁ => Finset.sum_eq_zero fun q₂ hq₂ =>
      Finset.sum_eq_zero fun q₃ hq₃ => ?_
    have hd1 := hstep n q₁ hpn (hwin n z D q₁ hq₁ le_rfl)
    have hq₂' := hwin (n / q₁) z q₁ q₂ (Finset.mem_of_mem_filter _ hq₂) le_rfl
    have hd2 := hstep _ q₂ hd1 hq₂'
    have hq₃' := hwin (n / q₁ / q₂) z q₂ q₃ hq₃ le_rfl
    exact rho_eq_zero_of_dvd hp (hstep _ q₃ hd2 hq₃') hpz
  rw [rhoMinus, h0, h1, h2, h3]
  simp

/-- A `z`-rough integer below `z^6` has at most five prime factors above `z`, so Harman's
minorant is bounded by `1 + 5 + 25 + 125`. -/
theorem abs_rhoMinus_le_of_lt_pow {z Q D E n : ℕ} (hz : 2 ≤ z) (hn : 0 < n) (hnz : n < z ^ 6) :
    |rhoMinus z Q D E n| ≤ 156 := by
  have hK : largePrimeCount n z ≤ 5 := by
    by_contra hK
    push Not at hK
    set S := n.primeFactors.filter (fun p => z ≤ p) with hS
    have hprod : ∏ p ∈ S, p ∣ n := by
      refine Finset.prod_primes_dvd n (fun p hp => ?_) (fun p hp => ?_)
      · exact (Nat.prime_iff.1 (Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hp).1))
      · exact Nat.dvd_of_mem_primeFactors (Finset.mem_filter.1 hp).1
    have hle : z ^ S.card ≤ ∏ p ∈ S, p := by
      rw [← Finset.prod_const]
      exact Finset.prod_le_prod' fun p hp => (Finset.mem_filter.1 hp).2
    have hcard : 6 ≤ S.card := hK
    have h6 : z ^ 6 ≤ z ^ S.card := Nat.pow_le_pow_right (by omega) hcard
    have := Nat.le_of_dvd hn hprod
    omega
  have hbound := abs_rhoMinus_le (z := z) (Q := Q) (D := D) (E := E) hn
  have hK' : (largePrimeCount n z : ℤ) ≤ 5 := by exact_mod_cast hK
  have hK0 : (0 : ℤ) ≤ (largePrimeCount n z : ℤ) := Int.natCast_nonneg _
  nlinarith [mul_le_mul hK' hK' hK0 (by norm_num : (0 : ℤ) ≤ 5)]

end

end RHTower.Sieve
