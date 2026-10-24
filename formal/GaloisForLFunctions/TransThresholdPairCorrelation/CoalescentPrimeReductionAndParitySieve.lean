import GaloisForLFunctions.TransThresholdPairCorrelation.SmoothWeightedCertificateAtFourThirds
import GaloisForLFunctions.RHTower.Sieve.PrimePairAverageSharp

/-!
# Exact Coalescent Prime Reduction, 2-Isolation, and the Parity-Halved Shift-Unrestricted Pair Sieve

This module resolves Open Problem 1 and the arithmetic sieve half of Open Problem 2 of
`TransThresholdPairCorrelation` (`SmoothWeightedCertificateAtFourThirds`):

1. **Sub-Nyquist Vanishing of `coalSum` (`log_sub_log_ge_sub_div`,
   `abs_log_sub_log_gt_of_lt_inv`, `coalSum_term_eq_zero_of_lt_inv`,
   `coalSum_odd_term_eq_zero_of_lt_two_div`):**
   For `1 ≤ m < n`, concavity of the logarithm yields `((n : ℝ) − m) / n ≤ log n − log m`.
   Consequently, every off-diagonal pair `(n, m)` with `max(n, m) < θ₀⁻¹` satisfies
   `|log n − log m| > θ₀` and vanishes identically in `coalSum Ω g X θ₀`, while every pair of
   distinct odd integers `(n, m)` with `max(n, m) < 2 / θ₀` satisfies `|log n − log m| > θ₀` and
   vanishes identically.

2. **Complete Isolation of the Even Prime `2` and Pure Odd-Prime Even-Shift Reduction
   (`log_sub_log_two_ge_one_third`, `primeCoalSum`, `oddEvenShiftPrimeCoalSum`,
   `primeCoalSum_eq_oddEvenShiftPrimeCoalSum`):**
   Every integer `q ≥ 3` satisfies `log q − log 2 ≥ (q − 2)/q ≥ 1/3`. Thus for any coalescent
   aperture `θ₀ < 1/3`, the even prime `2` has **zero** prime partners in the coalescent band, and
   `primeCoalSum Ω g X θ₀` equals `oddEvenShiftPrimeCoalSum Ω g X θ₀` identically: every
   contributing prime pair `(p, q)` consists of two odd primes `3 ≤ p, q ≤ X` separated by a
   non-zero even shift `p % 2 = q % 2` with `max(p, q) ≥ 2 / θ₀`.

3. **Unconditional Prime-Power Elimination in the Coalescent Band
   (`abs_coalSum_sub_primeCoalSum_le`, `primeCoalescentSurplus`,
   `eventually_abs_coalescentSurplus_sub_primeCoalescentSurplus_le`,
   `coalescentSurplusAtMost_iff_primeCoalescentSurplusAtMost`):**
   For `0 < θ₀ ≤ 1/2`, every coalescent partner `m ≠ n` of `n` lies in
   `Ico (n − ⌊2θ₀n⌋₊) n ∪ Ioc n (n + ⌊2θ₀n⌋₊)` (at most `4θ₀n` partners) and satisfies `n < 2m`,
   so `a_n a_m ≤ (√2 log X / n) Λ(n)`. The factor `n` cancels identically across the partner count,
   and Mathlib's `Chebyshev.psi_sub_theta_le` bounds the non-prime von Mangoldt sum by
   `2 √X log X`, yielding the explicit finite-height bound
   `|coalSum Ω g X θ₀ − primeCoalSum Ω g X θ₀| ≤ (16√2 / π) L M₀ (log X)² θ₀ √X`.
   At bandwidth `λ = 4/3` (`√X ≤ T^{2/3}`) and `θ₀ = T^{−1+η}` (`η < 1/3`), proper prime powers
   contribute `O(T^{−1/3+η} log T) = o(N(T, 2T))`, making `CoalescentSurplusAtMost β`
   unconditionally equivalent to `PrimeCoalescentSurplusAtMost β`.

4. **Parity-Halved Shift-Unrestricted 2D Selberg Prime-Pair Sieve
   (`primePair_filter_odd_eq_empty`, `sum_inv_shiftCorrection_even_le`,
   `sum_card_primePair_le_parity_unrestricted`,
   `sum_card_shift_bigPrimeSet_le_parity_unrestricted`):**
   Because every prime above `h ≥ 2` is odd, the shifted prime-pair set for odd `d` is empty.
   Restricting to even shifts `d = 2r` (`1 ≤ r ≤ K/2`) and using that every sifting prime in
   `rangePrimes P₁ h` (`P₁ ≥ 2`) is odd (`p ∣ 2r ↔ p ∣ r`) cuts both the main term and the
   remainder of `RHTower.Sieve.sum_card_primePair_le_sharp` in half while holds for **all** `K`
   with no restriction `K ≤ P₁^P₁`.
-/

open MeasureTheory Real Set Finset Filter Topology
open scoped BigOperators ArithmeticFunction

open Zeta23 Zeta23.PrimeSide RHTower RHTower.Sieve

noncomputable section

namespace GaloisForLFunctions.TransThresholdPairCorrelation

/-! ## §1. Sub-Nyquist Vanishing of the Coalescent Sum -/

/-- For `1 ≤ m < n`, the logarithmic gap satisfies `((n : ℝ) - m) / n ≤ log n - log m`. -/
theorem log_sub_log_ge_sub_div {m n : ℕ} (hm : 1 ≤ m) (hmn : m < n) :
    ((n : ℝ) - m) / n ≤ Real.log n - Real.log m := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hn0 : (0 : ℝ) < n := by exact_mod_cast ( lt_of_le_of_lt hm hmn )
  have hdiv : (0 : ℝ) < (m : ℝ) / n := div_pos hm0 hn0
  have hexp : (m : ℝ) / n ≤ Real.exp ((m : ℝ) / n - 1) := by
    have h := Real.add_one_le_exp ((m : ℝ) / n - 1)
    linarith
  have hlog := Real.log_le_log hdiv hexp
  rw [Real.log_exp, Real.log_div hm0.ne' hn0.ne'] at hlog
  have hrew : (1 : ℝ) - (m : ℝ) / n = ((n : ℝ) - m) / n := by
    field_simp
  linarith

/-- Symmetric lower bound on `|log n - log m|` for distinct positive integers `m, n`. -/
theorem abs_log_sub_log_ge_abs_sub_div_max {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    |(n : ℝ) - m| / max (n : ℝ) (m : ℝ) ≤ |Real.log n - Real.log m| := by
  rcases lt_trichotomy m n with hlt | rfl | hgt
  · have hmn : (m : ℝ) < n := by exact_mod_cast hlt
    have hlog : 0 ≤ Real.log n - Real.log m :=
      sub_nonneg.mpr (Real.log_le_log (by exact_mod_cast hm) hmn.le)
    rw [abs_of_pos (sub_pos.mpr hmn), max_eq_left hmn.le, abs_of_nonneg hlog]
    exact log_sub_log_ge_sub_div hm hlt
  · simp
  · have hnm : (n : ℝ) < m := by exact_mod_cast hgt
    have hlog : 0 ≤ Real.log m - Real.log n :=
      sub_nonneg.mpr (Real.log_le_log (by exact_mod_cast hn) hnm.le)
    rw [abs_sub_comm (n : ℝ) (m : ℝ), abs_of_pos (sub_pos.mpr hnm),
      max_eq_right hnm.le, abs_sub_comm (Real.log n) (Real.log m), abs_of_nonneg hlog]
    exact log_sub_log_ge_sub_div hn hgt

/-- Sub-Nyquist gap lower bound: if `1 ≤ m, n`, `n ≠ m`, and `max(n, m) < θ₀⁻¹` (`θ₀ > 0`),
then `|log n - log m| > θ₀`. -/
theorem abs_log_sub_log_gt_of_lt_inv {m n : ℕ} {θ₀ : ℝ}
    (hm : 1 ≤ m) (hn : 1 ≤ n) (hne : n ≠ m) (hθ₀ : 0 < θ₀)
    (hmax : max (n : ℝ) (m : ℝ) < θ₀⁻¹) :
    θ₀ < |Real.log n - Real.log m| := by
  have h1 : (1 : ℝ) ≤ |(n : ℝ) - m| := by
    have hne' : (n : ℤ) ≠ m := by exact_mod_cast hne
    have h1z : (1 : ℤ) ≤ |(n : ℤ) - m| := Int.one_le_abs (sub_ne_zero.mpr hne')
    exact_mod_cast h1z
  have hmax0 : (0 : ℝ) < max (n : ℝ) (m : ℝ) :=
    lt_of_lt_of_le (by exact_mod_cast hm) (le_max_right _ _)
  have hθmax : θ₀ < 1 / max (n : ℝ) (m : ℝ) := by
    rw [lt_div_iff₀ hmax0, ← lt_inv_iff₀ hθ₀]
    simpa [mul_comm] using hmax
  have hdiv : 1 / max (n : ℝ) (m : ℝ) ≤ |(n : ℝ) - m| / max (n : ℝ) (m : ℝ) :=
    div_le_div_of_nonneg_right h1 hmax0.le
  exact (hθmax.trans_le hdiv).trans (abs_log_sub_log_ge_abs_sub_div_max hm hn)

/-- Sub-Nyquist vanishing for odd pairs: if `1 ≤ m, n` are distinct odd integers and
`max(n, m) < 2 / θ₀` (`θ₀ > 0`), then `|log n - log m| > θ₀`. -/
theorem abs_log_sub_log_gt_of_odd_lt_two_div {m n : ℕ} {θ₀ : ℝ}
    (hm : 1 ≤ m) (hn : 1 ≤ n) (hne : n ≠ m)
    (hpar : n % 2 = m % 2) (hθ₀ : 0 < θ₀)
    (hmax : max (n : ℝ) (m : ℝ) < 2 / θ₀) :
    θ₀ < |Real.log n - Real.log m| := by
  have h2 : (2 : ℝ) ≤ |(n : ℝ) - m| := by
    have h2z : (2 : ℤ) ≤ |(n : ℤ) - m| := by omega
    exact_mod_cast h2z
  have hmax0 : (0 : ℝ) < max (n : ℝ) (m : ℝ) :=
    lt_of_lt_of_le (by exact_mod_cast hm) (le_max_right _ _)
  have hθmax : θ₀ < 2 / max (n : ℝ) (m : ℝ) := by
    rw [lt_div_iff₀ hmax0]
    rw [lt_div_iff₀ hθ₀] at hmax
    linarith
  have hdiv : 2 / max (n : ℝ) (m : ℝ) ≤ |(n : ℝ) - m| / max (n : ℝ) (m : ℝ) :=
    div_le_div_of_nonneg_right h2 hmax0.le
  exact (hθmax.trans_le hdiv).trans (abs_log_sub_log_ge_abs_sub_div_max hm hn)

/-- Every summand of `coalSum` with `max(n, m) < θ₀⁻¹` vanishes identically. -/
theorem coalSum_term_eq_zero_of_lt_inv (Ω g : ℝ → ℝ) {m n : ℕ} {θ₀ : ℝ}
    (hm : 1 ≤ m) (hn : 1 ≤ n) (hθ₀ : 0 < θ₀) (hmax : max (n : ℝ) (m : ℝ) < θ₀⁻¹) :
    (if n ≠ m ∧ |Real.log n - Real.log m| ≤ θ₀
      then acoef n * acoef m * g (Real.log m) * cosTransform Ω (Real.log n - Real.log m)
      else 0) = 0 := by
  split_ifs with h
  · exfalso
    exact (not_lt_of_ge h.2) (abs_log_sub_log_gt_of_lt_inv hm hn h.1 hθ₀ hmax)
  · rfl

/-- Every same-parity summand of `coalSum` with `max(n, m) < 2 / θ₀` vanishes identically. -/
theorem coalSum_odd_term_eq_zero_of_lt_two_div (Ω g : ℝ → ℝ) {m n : ℕ} {θ₀ : ℝ}
    (hm : 1 ≤ m) (hn : 1 ≤ n) (hpar : n % 2 = m % 2) (hθ₀ : 0 < θ₀)
    (hmax : max (n : ℝ) (m : ℝ) < 2 / θ₀) :
    (if n ≠ m ∧ |Real.log n - Real.log m| ≤ θ₀
      then acoef n * acoef m * g (Real.log m) * cosTransform Ω (Real.log n - Real.log m)
      else 0) = 0 := by
  split_ifs with h
  · exfalso
    exact (not_lt_of_ge h.2) (abs_log_sub_log_gt_of_odd_lt_two_div hm hn h.1 hpar hθ₀ hmax)
  · rfl

/-! ## §2. Complete Isolation of `p = 2` and Pure Odd-Prime Even-Shift Reduction -/

/-- Every integer `q ≥ 3` satisfies `log q - log 2 ≥ 1 / 3`. -/
theorem log_sub_log_two_ge_one_third {q : ℕ} (hq : 3 ≤ q) :
    (1 / 3 : ℝ) ≤ Real.log q - Real.log 2 := by
  have h2 : 1 ≤ (2 : ℕ) := by norm_num
  have hlt : 2 < q := by omega
  have hge := log_sub_log_ge_sub_div h2 hlt
  have hq3 : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hfrac : (1 / 3 : ℝ) ≤ ((q : ℝ) - 2) / q := by
    rw [div_le_div_iff₀ (by norm_num) (by linarith)]
    linarith
  simpa using hfrac.trans hge

/-- For `θ₀ < 1/3`, any two distinct primes `p, q` with `|log p - log q| ≤ θ₀` are both odd primes
`≥ 3` of equal parity (`p % 2 = q % 2`). -/
theorem odd_and_even_gap_of_prime_coalescent {p q : ℕ} {θ₀ : ℝ}
    (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (hgap : |Real.log p - Real.log q| ≤ θ₀) (hθ₀ : θ₀ < 1 / 3) :
    3 ≤ p ∧ 3 ≤ q ∧ p % 2 = 1 ∧ q % 2 = 1 ∧ p % 2 = q % 2 := by
  have hp2 : 2 ≤ p := hp.two_le
  have hq2 : 2 ≤ q := hq.two_le
  have hp_ne2 : p ≠ 2 := by
    rintro rfl
    have hq3 : 3 ≤ q := by omega
    have h13 := log_sub_log_two_ge_one_third hq3
    have habs : Real.log q - Real.log 2 ≤ |Real.log (2 : ℕ) - Real.log q| := by
      rw [abs_sub_comm]; exact le_abs_self _
    linarith
  have hq_ne2 : q ≠ 2 := by
    rintro rfl
    have hp3 : 3 ≤ p := by omega
    have h13 := log_sub_log_two_ge_one_third hp3
    have habs : Real.log p - Real.log 2 ≤ |Real.log p - Real.log (2 : ℕ)| := le_abs_self _
    linarith
  have hp3 : 3 ≤ p := by omega
  have hq3 : 3 ≤ q := by omega
  have hp_odd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left hp_ne2
  have hq_odd : q % 2 = 1 := hq.eq_two_or_odd.resolve_left hq_ne2
  exact ⟨hp3, hq3, hp_odd, hq_odd, hp_odd.trans hq_odd.symm⟩

/-- **The prime-only coalescent pair sum**: `coalSum` restricted to pairs of primes `(p, q)`. -/
def primeCoalSum (Ω g : ℝ → ℝ) (X θ₀ : ℝ) : ℝ :=
  (1 / π) * ∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
    if n.Prime ∧ m.Prime ∧ n ≠ m ∧ |Real.log n - Real.log m| ≤ θ₀
    then acoef n * acoef m * g (Real.log m) * cosTransform Ω (Real.log n - Real.log m)
    else 0

/-- **The odd-prime even-shift coalescent pair sum**: `primeCoalSum` restricted to odd primes
`3 ≤ p, q` with even difference `p % 2 = q % 2`. -/
def oddEvenShiftPrimeCoalSum (Ω g : ℝ → ℝ) (X θ₀ : ℝ) : ℝ :=
  (1 / π) * ∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
    if n.Prime ∧ m.Prime ∧ 3 ≤ n ∧ 3 ≤ m ∧ n % 2 = m % 2 ∧
      n ≠ m ∧ |Real.log n - Real.log m| ≤ θ₀
    then acoef n * acoef m * g (Real.log m) * cosTransform Ω (Real.log n - Real.log m)
    else 0

/-- **Exact 2-Isolation and Even-Shift Reduction of `primeCoalSum`.**
For every aperture `θ₀ < 1/3`, `primeCoalSum Ω g X θ₀ = oddEvenShiftPrimeCoalSum Ω g X θ₀`
identically: the prime `2` contributes zero pairs, and every coalescent prime pair consists of
two odd primes `≥ 3` separated by a non-zero even shift. -/
theorem primeCoalSum_eq_oddEvenShiftPrimeCoalSum (Ω g : ℝ → ℝ) (X : ℝ) {θ₀ : ℝ}
    (hθ₀ : θ₀ < 1 / 3) :
    primeCoalSum Ω g X θ₀ = oddEvenShiftPrimeCoalSum Ω g X θ₀ := by
  unfold primeCoalSum oddEvenShiftPrimeCoalSum
  congr 1
  refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
  have hiff : (n.Prime ∧ m.Prime ∧ n ≠ m ∧ |Real.log n - Real.log m| ≤ θ₀) ↔
      (n.Prime ∧ m.Prime ∧ 3 ≤ n ∧ 3 ≤ m ∧ n % 2 = m % 2 ∧
        n ≠ m ∧ |Real.log n - Real.log m| ≤ θ₀) := by
    constructor
    · rintro ⟨hn, hm, hne, hgap⟩
      obtain ⟨hn3, hm3, _, _, hpar⟩ := odd_and_even_gap_of_prime_coalescent hn hm hne hgap hθ₀
      exact ⟨hn, hm, hn3, hm3, hpar, hne, hgap⟩
    · rintro ⟨hn, hm, _, _, _, hne, hgap⟩
      exact ⟨hn, hm, hne, hgap⟩
  by_cases h : n.Prime ∧ m.Prime ∧ n ≠ m ∧ |Real.log n - Real.log m| ≤ θ₀
  · rw [if_pos h, if_pos (hiff.mp h)]
  · rw [if_neg h, if_neg (mt hiff.mpr h)]

/-! ## §3. Unconditional Prime-Power Elimination in the Coalescent Band -/

/-- For `1 ≤ m, n` and `|log n - log m| ≤ θ₀ ≤ 1/2`, we have `n < 2 * m`, `m < 2 * n`, and
`|(m : ℝ) - n| ≤ 2 * θ₀ * n`. -/
theorem coalescent_partner_Window_bounds {m n : ℕ} {θ₀ : ℝ}
    (hm : 1 ≤ m) (hn : 1 ≤ n) (hgap : |Real.log n - Real.log m| ≤ θ₀) (hθ : θ₀ ≤ 1 / 2) :
    (n : ℝ) < 2 * m ∧ (m : ℝ) < 2 * n ∧ |(m : ℝ) - n| ≤ 2 * θ₀ * n := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have h1 : Real.log ((n : ℝ) / m) < Real.log 2 := by
    rw [Real.log_div hn0.ne' hm0.ne']
    have := (le_abs_self (Real.log n - Real.log m)).trans hgap
    linarith
  have h2 : Real.log ((m : ℝ) / n) < Real.log 2 := by
    rw [Real.log_div hm0.ne' hn0.ne']
    have := (neg_le_abs (Real.log n - Real.log m)).trans hgap
    linarith
  have hn2m : (n : ℝ) < 2 * m := by
    have hlt := (Real.log_lt_log_iff (div_pos hn0 hm0) (by norm_num)).mp h1
    rwa [div_lt_iff₀ hm0] at hlt
  have hm2n : (m : ℝ) < 2 * n := by
    have hlt := (Real.log_lt_log_iff (div_pos hm0 hn0) (by norm_num)).mp h2
    rwa [div_lt_iff₀ hn0] at hlt
  have hmax : max (n : ℝ) (m : ℝ) ≤ 2 * n :=
    max_le (by linarith) hm2n.le
  have hθ0 : 0 ≤ θ₀ := (abs_nonneg _).trans hgap
  have hmax0 : 0 < max (n : ℝ) (m : ℝ) := lt_of_lt_of_le hn0 (le_max_left _ _)
  have hlow := abs_log_sub_log_ge_abs_sub_div_max hm hn
  have hle : |(n : ℝ) - m| ≤ max (n : ℝ) (m : ℝ) * θ₀ := by
    rw [← div_le_iff₀ hmax0]
    exact hlow.trans hgap
  have h3 : |(m : ℝ) - n| ≤ 2 * θ₀ * n := by
    rw [abs_sub_comm]
    calc |(n : ℝ) - m| ≤ max (n : ℝ) (m : ℝ) * θ₀ := hle
      _ ≤ (2 * n) * θ₀ := mul_le_mul_of_nonneg_right hmax hθ0
      _ = 2 * θ₀ * n := by ring
  exact ⟨hn2m, hm2n, h3⟩

/-- For any `X, θ₀ : ℝ` (`0 ≤ θ₀`) and `n : ℕ`, the set of `m ∈ primeRange X` with `m ≠ n` and
`|(m : ℝ) - n| ≤ 2 * θ₀ * n` has cardinality at most `4 * θ₀ * n`. -/
theorem card_coalescent_partners_le (X : ℝ) {θ₀ : ℝ} (hθ₀ : 0 ≤ θ₀) (n : ℕ) :
    (((primeRange X).filter (fun m => m ≠ n ∧ |(m : ℝ) - n| ≤ 2 * θ₀ * n)).card : ℝ)
      ≤ 4 * θ₀ * n := by
  classical
  set K : ℕ := ⌊2 * θ₀ * (n : ℝ)⌋₊ with hKdef
  have hsub : (primeRange X).filter (fun m => m ≠ n ∧ |(m : ℝ) - n| ≤ 2 * θ₀ * n)
      ⊆ Finset.Ico (n - K) n ∪ Finset.Ioc n (n + K) := by
    intro m hm
    rw [Finset.mem_filter] at hm
    obtain ⟨_, hne, habs⟩ := hm
    rw [Finset.mem_union, Finset.mem_Ico, Finset.mem_Ioc]
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · left
      have hsub_le : ((n - m : ℕ) : ℝ) ≤ 2 * θ₀ * n := by
        rw [Nat.cast_sub hlt.le, ← abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hlt.le)),
          abs_sub_comm]
        exact habs
      have hK : n - m ≤ K := Nat.le_floor hsub_le
      omega
    · right
      have hsub_le : ((m - n : ℕ) : ℝ) ≤ 2 * θ₀ * n := by
        rw [Nat.cast_sub hgt.le, ← abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hgt.le))]
        exact habs
      have hK : m - n ≤ K := Nat.le_floor hsub_le
      omega
  have hcard_nat : ((primeRange X).filter (fun m => m ≠ n ∧ |(m : ℝ) - n| ≤ 2 * θ₀ * n)).card
      ≤ 2 * K := by
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le (Finset.Ico (n - K) n) (Finset.Ioc n (n + K))
    rw [Nat.card_Ico, Nat.card_Ioc] at h2
    omega
  have hcard_real : (((primeRange X).filter
      (fun m => m ≠ n ∧ |(m : ℝ) - n| ≤ 2 * θ₀ * n)).card : ℝ) ≤ 2 * (K : ℝ) := by
    exact_mod_cast hcard_nat
  have hK_le : (K : ℝ) ≤ 2 * θ₀ * n := Nat.floor_le (by positivity)
  linarith

/-- For `n, m ∈ primeRange X` (`1 ≤ X`) with `|log n - log m| ≤ θ₀ ≤ 1/2`, the product
`acoef n * acoef m` is at most `(Real.sqrt 2 * Real.log X / n) * (Λ n : ℝ)`. -/
theorem acoef_mul_acoef_le_of_coalescent {X θ₀ : ℝ} {n m : ℕ}
    (hX : 1 ≤ X) (hn : n ∈ primeRange X) (hm : m ∈ primeRange X)
    (hgap : |Real.log n - Real.log m| ≤ θ₀) (hθ : θ₀ ≤ 1 / 2) :
    acoef n * acoef m ≤ Real.sqrt 2 * Real.log X * (Λ n : ℝ) / n := by
  have hn1 : 1 ≤ n := (Finset.mem_Ioc.mp hn).1
  have hm1 : 1 ≤ m := (Finset.mem_Ioc.mp hm).1
  have hmX : (m : ℝ) ≤ X :=
    (Nat.cast_le.mpr (Finset.mem_Ioc.mp hm).2).trans (Nat.floor_le (by linarith))
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  obtain ⟨hn2m, _, _⟩ := coalescent_partner_Window_bounds hm1 hn1 hgap hθ
  have hsqrt : Real.sqrt n ≤ Real.sqrt 2 * Real.sqrt m := by
    rw [← Real.sqrt_mul (by norm_num)]
    exact Real.sqrt_le_sqrt hn2m.le
  have hΛm : (Λ m : ℝ) ≤ Real.log X :=
    ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log hm0 hmX)
  have hΛn0 : (0 : ℝ) ≤ (Λ n : ℝ) := ArithmeticFunction.vonMangoldt_nonneg
  have hΛm0 : (0 : ℝ) ≤ (Λ m : ℝ) := ArithmeticFunction.vonMangoldt_nonneg
  have hlogX0 : 0 ≤ Real.log X := Real.log_nonneg hX
  unfold acoef
  have hdiv : (Λ m : ℝ) / Real.sqrt m ≤ Real.sqrt 2 * Real.log X / Real.sqrt n := by
    rw [div_le_div_iff₀ (Real.sqrt_pos.mpr hm0) (Real.sqrt_pos.mpr hn0)]
    calc (Λ m : ℝ) * Real.sqrt n ≤ Real.log X * Real.sqrt n :=
          mul_le_mul_of_nonneg_right hΛm (Real.sqrt_nonneg _)
      _ ≤ Real.log X * (Real.sqrt 2 * Real.sqrt m) :=
          mul_le_mul_of_nonneg_left hsqrt hlogX0
      _ = Real.sqrt 2 * Real.log X * Real.sqrt m := by ring
  calc (Λ n : ℝ) / Real.sqrt n * ((Λ m : ℝ) / Real.sqrt m)
      ≤ (Λ n : ℝ) / Real.sqrt n * (Real.sqrt 2 * Real.log X / Real.sqrt n) :=
        mul_le_mul_of_nonneg_left hdiv (div_nonneg hΛn0 (Real.sqrt_nonneg _))
    _ = Real.sqrt 2 * Real.log X * (Λ n : ℝ) / (Real.sqrt n * Real.sqrt n) := by ring
    _ = Real.sqrt 2 * Real.log X * (Λ n : ℝ) / n := by rw [Real.mul_self_sqrt hn0.le]

/-- Single-index partner sum bound: for any `n ∈ primeRange X` (`1 ≤ X`) and `0 ≤ θ₀ ≤ 1/2`,
`∑_{m ∈ primeRange X, m ≠ n, |log n - log m| ≤ θ₀} a_n a_m ≤ 4 √2 (log X) θ₀ Λ(n)`. -/
theorem sum_coalescent_partners_acoef_le {X θ₀ : ℝ} {n : ℕ}
    (hX : 1 ≤ X) (hθ0 : 0 ≤ θ₀) (hθ : θ₀ ≤ 1 / 2) (hn : n ∈ primeRange X) :
    ∑ m ∈ (primeRange X).filter (fun m => n ≠ m ∧ |Real.log n - Real.log m| ≤ θ₀),
        acoef n * acoef m
      ≤ 4 * Real.sqrt 2 * Real.log X * θ₀ * (Λ n : ℝ) := by
  classical
  have hn1 : 1 ≤ n := (Finset.mem_Ioc.mp hn).1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have h1 : ∑ m ∈ (primeRange X).filter (fun m => n ≠ m ∧ |Real.log n - Real.log m| ≤ θ₀),
        acoef n * acoef m
      ≤ ∑ m ∈ (primeRange X).filter (fun m => n ≠ m ∧ |Real.log n - Real.log m| ≤ θ₀),
        (Real.sqrt 2 * Real.log X * (Λ n : ℝ) / n) := by
    refine Finset.sum_le_sum fun m hm => ?_
    rw [Finset.mem_filter] at hm
    exact acoef_mul_acoef_le_of_coalescent hX hn hm.1 hm.2.2 hθ
  rw [Finset.sum_const, nsmul_eq_mul] at h1
  have hsub : (primeRange X).filter (fun m => n ≠ m ∧ |Real.log n - Real.log m| ≤ θ₀)
      ⊆ (primeRange X).filter (fun m => m ≠ n ∧ |(m : ℝ) - n| ≤ 2 * θ₀ * n) := by
    intro m hm
    rw [Finset.mem_filter] at hm ⊢
    have hm1 : 1 ≤ m := (Finset.mem_Ioc.mp hm.1).1
    obtain ⟨_, _, h3⟩ := coalescent_partner_Window_bounds hm1 hn1 hm.2.2 hθ
    exact ⟨hm.1, hm.2.1.symm, h3⟩
  have hcard : (((primeRange X).filter
      (fun m => n ≠ m ∧ |Real.log n - Real.log m| ≤ θ₀)).card : ℝ) ≤ 4 * θ₀ * n := by
    have hle : (((primeRange X).filter
        (fun m => n ≠ m ∧ |Real.log n - Real.log m| ≤ θ₀)).card : ℝ)
        ≤ (((primeRange X).filter (fun m => m ≠ n ∧ |(m : ℝ) - n| ≤ 2 * θ₀ * n)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    exact hle.trans (card_coalescent_partners_le X hθ0 n)
  have hconst0 : 0 ≤ Real.sqrt 2 * Real.log X * (Λ n : ℝ) / n := by
    have := Real.log_nonneg hX
    have := ArithmeticFunction.vonMangoldt_nonneg (n := n)
    positivity
  calc ∑ m ∈ (primeRange X).filter (fun m => n ≠ m ∧ |Real.log n - Real.log m| ≤ θ₀),
        acoef n * acoef m
      ≤ (((primeRange X).filter
          (fun m => n ≠ m ∧ |Real.log n - Real.log m| ≤ θ₀)).card : ℝ)
          * (Real.sqrt 2 * Real.log X * (Λ n : ℝ) / n) := h1
    _ ≤ (4 * θ₀ * n) * (Real.sqrt 2 * Real.log X * (Λ n : ℝ) / n) :=
        mul_le_mul_of_nonneg_right hcard hconst0
    _ = 4 * Real.sqrt 2 * Real.log X * θ₀ * (Λ n : ℝ) := by
        field_simp; ring

/-- **Explicit Finite-Height Prime-Power Elimination Bound in the Coalescent Band.**
For `1 ≤ X`, `0 ≤ θ₀ ≤ 1/2`, `|g y| ≤ L`, and `|cosTransform Ω θ| ≤ M₀`, the difference between
`coalSum Ω g X θ₀` and its prime-only restriction `primeCoalSum Ω g X θ₀` satisfies
`|coalSum Ω g X θ₀ − primeCoalSum Ω g X θ₀| ≤ (16√2 / π) L M₀ (log X)² θ₀ √X`. -/
theorem abs_coalSum_sub_primeCoalSum_le {Ω g : ℝ → ℝ} {X θ₀ L M₀ : ℝ}
    (hX : 1 ≤ X) (hθ0 : 0 ≤ θ₀) (hθ : θ₀ ≤ 1 / 2)
    (hL0 : 0 ≤ L) (hg : ∀ y, |g y| ≤ L)
    (hM0 : 0 ≤ M₀) (hΩ : ∀ θ, |cosTransform Ω θ| ≤ M₀) :
    |coalSum Ω g X θ₀ - primeCoalSum Ω g X θ₀| ≤
      (16 * Real.sqrt 2 / π) * L * M₀ * Real.log X ^ 2 * θ₀ * Real.sqrt X := by
  classical
  have hπ : 0 < π := Real.pi_pos
  have hlogX0 : 0 ≤ Real.log X := Real.log_nonneg hX
  have hdiff : coalSum Ω g X θ₀ - primeCoalSum Ω g X θ₀ =
      (1 / π) * ∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
        if (¬ n.Prime ∨ ¬ m.Prime) ∧ n ≠ m ∧ |Real.log n - Real.log m| ≤ θ₀
        then acoef n * acoef m * g (Real.log m) * cosTransform Ω (Real.log n - Real.log m)
        else 0 := by
    unfold coalSum primeCoalSum
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    by_cases hcoal : n ≠ m ∧ |Real.log n - Real.log m| ≤ θ₀
    · by_cases hp : n.Prime ∧ m.Prime
      · have hnot : ¬ (¬ n.Prime ∨ ¬ m.Prime) := by tauto
        simp [hcoal, hp, hnot]
      · have hor : ¬ n.Prime ∨ ¬ m.Prime := not_and_or.mp hp
        simp [hcoal, hp, hor]
    · simp [hcoal]
  rw [hdiff, abs_mul, abs_of_pos (one_div_pos.mpr hπ)]
  have hterm : ∀ n ∈ primeRange X, ∀ m ∈ primeRange X,
      |(if (¬ n.Prime ∨ ¬ m.Prime) ∧ n ≠ m ∧ |Real.log n - Real.log m| ≤ θ₀
        then acoef n * acoef m * g (Real.log m) * cosTransform Ω (Real.log n - Real.log m)
        else 0)|
      ≤ L * M₀ * ((if ¬ n.Prime ∧ n ≠ m ∧ |Real.log n - Real.log m| ≤ θ₀
            then acoef n * acoef m else 0)
          + (if ¬ m.Prime ∧ m ≠ n ∧ |Real.log m - Real.log n| ≤ θ₀
            then acoef m * acoef n else 0)) := by
    intro n _ m _
    have ha0 : 0 ≤ acoef n * acoef m := mul_nonneg (acoef_nonneg n) (acoef_nonneg m)
    by_cases hcoal : n ≠ m ∧ |Real.log n - Real.log m| ≤ θ₀
    · have hcoal' : m ≠ n ∧ |Real.log m - Real.log n| ≤ θ₀ := by
        rw [abs_sub_comm]; exact ⟨hcoal.1.symm, hcoal.2⟩
      by_cases hor : ¬ n.Prime ∨ ¬ m.Prime
      · rw [if_pos ⟨hor, hcoal⟩, abs_mul, abs_mul, abs_of_nonneg ha0]
        have hgm : |g (Real.log m)| * |cosTransform Ω (Real.log n - Real.log m)| ≤ L * M₀ :=
          mul_le_mul (hg _) (hΩ _) (abs_nonneg _) hL0
        have h1 : acoef n * acoef m * (|g (Real.log m)| * |cosTransform Ω (Real.log n - Real.log m)|)
            ≤ L * M₀ * (acoef n * acoef m) := by
          calc acoef n * acoef m * (|g (Real.log m)| * |cosTransform Ω (Real.log n - Real.log m)|)
              ≤ acoef n * acoef m * (L * M₀) := mul_le_mul_of_nonneg_left hgm ha0
            _ = L * M₀ * (acoef n * acoef m) := by ring
        have h2 : acoef n * acoef m ≤
            (if ¬ n.Prime ∧ n ≠ m ∧ |Real.log n - Real.log m| ≤ θ₀ then acoef n * acoef m else 0)
            + (if ¬ m.Prime ∧ m ≠ n ∧ |Real.log m - Real.log n| ≤ θ₀ then acoef m * acoef n else 0) := by
          rcases hor with hnP | hmP
          · rw [if_pos ⟨hnP, hcoal⟩]
            have : 0 ≤ (if ¬ m.Prime ∧ m ≠ n ∧ |Real.log m - Real.log n| ≤ θ₀
                then acoef m * acoef n else 0) := by split_ifs <;> linarith
            linarith
          · rw [if_pos ⟨hmP, hcoal'⟩, mul_comm (acoef m)]
            have : 0 ≤ (if ¬ n.Prime ∧ n ≠ m ∧ |Real.log n - Real.log m| ≤ θ₀
                then acoef n * acoef m else 0) := by split_ifs <;> linarith
            linarith
        calc acoef n * acoef m * |g (Real.log m)| * |cosTransform Ω (Real.log n - Real.log m)|
            = acoef n * acoef m * (|g (Real.log m)| * |cosTransform Ω (Real.log n - Real.log m)|) := by ring
          _ ≤ L * M₀ * (acoef n * acoef m) := h1
          _ ≤ L * M₀ * ((if ¬ n.Prime ∧ n ≠ m ∧ |Real.log n - Real.log m| ≤ θ₀
                then acoef n * acoef m else 0)
              + (if ¬ m.Prime ∧ m ≠ n ∧ |Real.log m - Real.log n| ≤ θ₀
                then acoef m * acoef n else 0)) :=
            mul_le_mul_of_nonneg_left h2 (mul_nonneg hL0 hM0)
      · rw [if_neg (by tauto), abs_zero]
        refine mul_nonneg (mul_nonneg hL0 hM0) (add_nonneg ?_ ?_) <;>
          (split_ifs <;> [linarith; exact le_rfl])
    · have hcoal' : ¬ (m ≠ n ∧ |Real.log m - Real.log n| ≤ θ₀) := by
        rw [abs_sub_comm]; tauto
      simp [hcoal, hcoal']
  have hsum_abs : |∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
        if (¬ n.Prime ∨ ¬ m.Prime) ∧ n ≠ m ∧ |Real.log n - Real.log m| ≤ θ₀
        then acoef n * acoef m * g (Real.log m) * cosTransform Ω (Real.log n - Real.log m)
        else 0|
      ≤ L * M₀ * (2 * ∑ n ∈ (primeRange X).filter (fun n => ¬ n.Prime),
          ∑ m ∈ (primeRange X).filter (fun m => n ≠ m ∧ |Real.log n - Real.log m| ≤ θ₀),
            acoef n * acoef m) := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun n hn => (abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun m hm => hterm n hn m hm)).trans ?_
    simp_rw [← Finset.mul_sum, Finset.sum_add_distrib]
    rw [Finset.sum_comm (s := primeRange X) (t := primeRange X)
      (f := fun n m => if ¬ m.Prime ∧ m ≠ n ∧ |Real.log m - Real.log n| ≤ θ₀
        then acoef m * acoef n else 0)]
    have hsplit : (∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
          if ¬ n.Prime ∧ n ≠ m ∧ |Real.log n - Real.log m| ≤ θ₀ then acoef n * acoef m else 0)
        = ∑ n ∈ (primeRange X).filter (fun n => ¬ n.Prime),
          ∑ m ∈ (primeRange X).filter (fun m => n ≠ m ∧ |Real.log n - Real.log m| ≤ θ₀),
            acoef n * acoef m := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun n _ => ?_
      by_cases hnP : ¬ n.Prime
      · simp [hnP, Finset.sum_filter]
      · simp [hnP]
    rw [hsplit]
    exact le_of_eq (by ring)
  have hpartner_sum : ∑ n ∈ (primeRange X).filter (fun n => ¬ n.Prime),
        ∑ m ∈ (primeRange X).filter (fun m => n ≠ m ∧ |Real.log n - Real.log m| ≤ θ₀),
          acoef n * acoef m
      ≤ 8 * Real.sqrt 2 * Real.log X ^ 2 * θ₀ * Real.sqrt X := by
    have h1 : ∑ n ∈ (primeRange X).filter (fun n => ¬ n.Prime),
          ∑ m ∈ (primeRange X).filter (fun m => n ≠ m ∧ |Real.log n - Real.log m| ≤ θ₀),
            acoef n * acoef m
        ≤ ∑ n ∈ (primeRange X).filter (fun n => ¬ n.Prime),
          4 * Real.sqrt 2 * Real.log X * θ₀ * (Λ n : ℝ) := by
      refine Finset.sum_le_sum fun n hn => ?_
      exact sum_coalescent_partners_acoef_le hX hθ0 hθ (Finset.mem_filter.mp hn).1
    rw [← Finset.mul_sum] at h1
    have hcheb : ∑ n ∈ (primeRange X).filter (fun n => ¬ n.Prime), (Λ n : ℝ)
        ≤ 2 * Real.sqrt X * Real.log X := by
      unfold primeRange
      rw [← Chebyshev.psi_sub_theta_eq_sum_not_prime X]
      exact Chebyshev.psi_sub_theta_le hX
    calc ∑ n ∈ (primeRange X).filter (fun n => ¬ n.Prime),
          ∑ m ∈ (primeRange X).filter (fun m => n ≠ m ∧ |Real.log n - Real.log m| ≤ θ₀),
            acoef n * acoef m
        ≤ 4 * Real.sqrt 2 * Real.log X * θ₀ *
            ∑ n ∈ (primeRange X).filter (fun n => ¬ n.Prime), (Λ n : ℝ) := h1
      _ ≤ 4 * Real.sqrt 2 * Real.log X * θ₀ * (2 * Real.sqrt X * Real.log X) :=
          mul_le_mul_of_nonneg_left hcheb (by positivity)
      _ = 8 * Real.sqrt 2 * Real.log X ^ 2 * θ₀ * Real.sqrt X := by ring
  calc 1 / π * |∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
        if (¬ n.Prime ∨ ¬ m.Prime) ∧ n ≠ m ∧ |Real.log n - Real.log m| ≤ θ₀
        then acoef n * acoef m * g (Real.log m) * cosTransform Ω (Real.log n - Real.log m)
        else 0|
      ≤ 1 / π * (L * M₀ * (2 * (8 * Real.sqrt 2 * Real.log X ^ 2 * θ₀ * Real.sqrt X))) := by
        refine mul_le_mul_of_nonneg_left (hsum_abs.trans ?_) (by positivity)
        exact mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hL0 hM0)
    _ = (16 * Real.sqrt 2 / π) * L * M₀ * Real.log X ^ 2 * θ₀ * Real.sqrt X := by ring

/-- **The prime-only coalescent surplus** at height `T`: `primeCoalSum` at bandwidth `4/3`
and aperture `T^{−1+η}`, normalised by `(aL)²`. -/
def primeCoalescentSurplus (u : ℝ → ℝ) (η T : ℝ) : ℝ :=
  primeCoalSum (profileΩ u T) (params43.localFun T).g (params43.X T) (T ^ (-1 + η))
    / (params43.a T * params43.L T) ^ 2

/-- **The odd-prime even-shift coalescent surplus** at height `T`. -/
def oddEvenShiftPrimeCoalescentSurplus (u : ℝ → ℝ) (η T : ℝ) : ℝ :=
  oddEvenShiftPrimeCoalSum (profileΩ u T) (params43.localFun T).g (params43.X T) (T ^ (-1 + η))
    / (params43.a T * params43.L T) ^ 2

/-- For every `η < 1`, `primeCoalescentSurplus u η T = oddEvenShiftPrimeCoalescentSurplus u η T`
for all `T ≥ 3^{1/(1−η)}`. -/
theorem eventually_primeCoalescentSurplus_eq_oddEvenShift (u : ℝ → ℝ) {η : ℝ} (hη : η < 1) :
    ∀ᶠ T in atTop, primeCoalescentSurplus u η T = oddEvenShiftPrimeCoalescentSurplus u η T := by
  have hneg : -1 + η < 0 := by linarith
  have htend : Tendsto (fun T : ℝ => T ^ (-1 + η)) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by linarith : 0 < -( -1 + η ))
      |>.congr' (Eventually.of_forall fun T => by rw [neg_neg])
  filter_upwards [htend.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 3))] with T hT
  unfold primeCoalescentSurplus oddEvenShiftPrimeCoalescentSurplus
  rw [primeCoalSum_eq_oddEvenShiftPrimeCoalSum _ _ _ hT]

/-- **Unconditional Prime-Power Negligibility at Bandwidth `4/3`.**
For any window profile `u` and any `0 < η < 1/3`, the difference between the full von Mangoldt
`coalescentSurplus u η T` and the pure prime `primeCoalescentSurplus u η T` is bounded by
`(128 √2 / π) (log T) T^{−1/3+η}` for all large `T`, hence is `o(1)` (and `o(N(T, 2T))`). -/
theorem eventually_abs_coalescentSurplus_sub_primeCoalescentSurplus_le
    (hu : WindowProfile ε₁ u) {η : ℝ} (hη1 : η < 1) :
    ∀ᶠ T in atTop,
      |coalescentSurplus u η T - primeCoalescentSurplus u η T| ≤
        (128 * Real.sqrt 2 / π) * Real.log T * T ^ (-1 / 3 + η) := by
  have hP := paramsValidFam_params43
  obtain ⟨TL, hTL⟩ := localHypsCoreW_eventually_fam hP
  have hneg : -1 + η < 0 := by linarith
  have htend : Tendsto (fun T : ℝ => T ^ (-1 + η)) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by linarith : 0 < -(-1 + η))
      |>.congr' (Eventually.of_forall fun T => by rw [neg_neg])
  filter_upwards [eventually_ge_atTop (max TL 4096), eventually_l_bounds,
    htend.eventually (le_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))]
    with T hTmax ⟨hlog1, hl1, hlo, hhi⟩ hθhalf
  have hTLT : TL ≤ T := (le_max_left _ _).trans hTmax
  have hT4096 : (4096 : ℝ) ≤ T := (le_max_right _ _).trans hTmax
  have hT0 : 0 < T := by linarith
  have hF := hTL T hTLT
  have hL8 : 8 ≤ params43.L T := hF.eight_le_L
  have ha2 : 1 / 2 ≤ params43.a T := hF.b_ge_half.trans hF.b_le_a
  have hXL : params43.X T = Real.exp (params43.L T) := rfl
  have hlogX : Real.log (params43.X T) = params43.L T := by rw [hXL, Real.log_exp]
  have hX1 : 1 ≤ params43.X T := by
    rw [hXL]; exact Real.one_le_exp (by linarith)
  have hθ0 : 0 < T ^ (-1 + η) := Real.rpow_pos_of_pos hT0 _
  have hg : ∀ y, |(params43.localFun T).g y| ≤ params43.L T := fun y =>
    abs_g_le_L hF y
  have hΩ : ∀ θ, |cosTransform (profileΩ u T) θ| ≤ T := fun θ =>
    (abs_cosTransform_le (profileΩ_integrable hu hT0.le) (fun τ => profileΩ_nonneg hu τ) θ).trans
      (integral_profileΩ_le hu hT0.le)
  have hdiff := abs_coalSum_sub_primeCoalSum_le hX1 hθ0.le hθhalf (by linarith) hg hT0.le hΩ
  rw [hlogX] at hdiff
  obtain ⟨_, _, hsX, _⟩ := scale_facts hT4096 hhi
  have hsX' : Real.sqrt (params43.X T) ≤ T ^ (2 / 3 : ℝ) := by
    refine hsX.trans (le_of_eq ?_)
    rw [← Real.rpow_natCast, ← Real.rpow_mul hT0.le]
    norm_num
  have hL_le : params43.L T ≤ 2 * Real.log T := by
    have : params43.L T = 4 / 3 * Zeta23.l T := rfl
    linarith
  have ha2_sq : (1 / 4 : ℝ) * params43.L T ^ 2 ≤ (params43.a T * params43.L T) ^ 2 := by
    have h1 : 1 / 2 * params43.L T ≤ params43.a T * params43.L T :=
      mul_le_mul_of_nonneg_right ha2 (by linarith)
    nlinarith
  have hden0 : 0 < (params43.a T * params43.L T) ^ 2 := by positivity
  unfold coalescentSurplus primeCoalescentSurplus
  rw [← sub_div, abs_div, abs_of_pos hden0]
  have hπ : 0 < π := Real.pi_pos
  have hnum : |coalSum (profileΩ u T) (params43.localFun T).g (params43.X T) (T ^ (-1 + η)) -
        primeCoalSum (profileΩ u T) (params43.localFun T).g (params43.X T) (T ^ (-1 + η))|
      ≤ (16 * Real.sqrt 2 / π) * params43.L T ^ 3 * (T * T ^ (-1 + η) * T ^ (2 / 3 : ℝ)) := by
    calc _ ≤ (16 * Real.sqrt 2 / π) * params43.L T * T * params43.L T ^ 2
            * T ^ (-1 + η) * Real.sqrt (params43.X T) := hdiff
      _ ≤ (16 * Real.sqrt 2 / π) * params43.L T * T * params43.L T ^ 2
            * T ^ (-1 + η) * T ^ (2 / 3 : ℝ) :=
          mul_le_mul_of_nonneg_left hsX' (by positivity)
      _ = (16 * Real.sqrt 2 / π) * params43.L T ^ 3 * (T * T ^ (-1 + η) * T ^ (2 / 3 : ℝ)) := by
          ring
  have hrpow : T * T ^ (-1 + η) * T ^ (2 / 3 : ℝ) = T ^ (-1 / 3 + η) := by
    have h1 : T * T ^ (-1 + η) = T ^ η := by
      rw [← Real.rpow_one_add' hT0.le (by linarith)]
      ring_nf
    rw [h1, ← Real.rpow_add hT0]
    ring_nf
  rw [hrpow] at hnum
  rw [div_le_iff₀ hden0]
  calc |coalSum (profileΩ u T) (params43.localFun T).g (params43.X T) (T ^ (-1 + η)) -
        primeCoalSum (profileΩ u T) (params43.localFun T).g (params43.X T) (T ^ (-1 + η))|
      ≤ (16 * Real.sqrt 2 / π) * params43.L T ^ 3 * T ^ (-1 / 3 + η) := hnum
    _ = (64 * Real.sqrt 2 / π) * params43.L T * T ^ (-1 / 3 + η)
          * ((1 / 4 : ℝ) * params43.L T ^ 2) := by ring
    _ ≤ (64 * Real.sqrt 2 / π) * (2 * Real.log T) * T ^ (-1 / 3 + η)
          * (params43.a T * params43.L T) ^ 2 := by
        refine mul_le_mul ?_ ha2_sq (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hL_le (by positivity)) (by positivity)
    _ = (128 * Real.sqrt 2 / π) * Real.log T * T ^ (-1 / 3 + η)
          * (params43.a T * params43.L T) ^ 2 := by ring

/-- **The Smooth-Window Coalescent Surplus Hypothesis at Budget `β`** (with `0 < η < 1/3`). -/
def CoalescentSurplusAtMost (β : ℝ) : Prop :=
  ∀ ε > 0, ∃ (η : ℝ) (u : ℝ → ℝ) (ε₁ : ℝ),
    0 < η ∧ η < 1 / 3 ∧ WindowProfile ε₁ u ∧
    ∀ᶠ T in atTop,
      (29 / 36 - ε) * (Ncount T (2 * T) : ℝ) - coalescentSurplus u η T ≤
        (N0star T (2 * T) : ℝ) ∧
      coalescentSurplus u η T ≤ (β + ε) * (Ncount T (2 * T) : ℝ)

/-- **The Pure Odd-Prime Coalescent Surplus Hypothesis at Budget `β`.** -/
def PrimeCoalescentSurplusAtMost (β : ℝ) : Prop :=
  ∀ ε > 0, ∃ (η : ℝ) (u : ℝ → ℝ) (ε₁ : ℝ),
    0 < η ∧ η < 1 / 3 ∧ WindowProfile ε₁ u ∧
    ∀ᶠ T in atTop,
      (29 / 36 - ε) * (Ncount T (2 * T) : ℝ) - primeCoalescentSurplus u η T ≤
        (N0star T (2 * T) : ℝ) ∧
      primeCoalescentSurplus u η T ≤ (β + ε) * (Ncount T (2 * T) : ℝ)

/-- Eventually `T * log T / (8 * π) ≤ N(T, 2T)`. -/
theorem eventually_T_mul_log_div_eight_pi_le_Ncount :
    ∀ᶠ T in atTop, T * Real.log T / (8 * π) ≤ (Ncount T (2 * T) : ℝ) := by
  obtain ⟨CR, TR, hRvM⟩ := paperInputs_zeta.RvM.main
  have hπ := Real.pi_pos
  filter_upwards [eventually_ge_atTop (max TR (8 * π * |CR|)), eventually_l_bounds]
    with T hTmax ⟨hlog1, _, hlo, _⟩
  have hTR : TR ≤ T := (le_max_left _ _).trans hTmax
  have hTCR : 8 * π * |CR| ≤ T := (le_max_right _ _).trans hTmax
  have hT0 : 0 < T := lt_of_lt_of_le (by positivity) hTCR
  have hRv0 := hRvM T hTR
  have hc₀ : 0 ≤ 2 * Real.log 2 - 1 := by have := Real.log_two_gt_d9; linarith
  have hMlow : T * Real.log T / (4 * π) ≤ T / (2 * π) * ell1 T := by
    have h1 : Real.log T ≤ 2 * ell1 T := by unfold ell1; linarith
    rw [div_le_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ T / (2 * π))
    nlinarith
  have hCR : |CR| * Zeta23.l T ≤ T * Real.log T / (8 * π) := by
    have hl : Zeta23.l T ≤ Real.log T := by
      unfold Zeta23.l
      exact Real.log_le_log (by positivity) (div_le_self hT0.le (by linarith [Real.pi_gt_three]))
    have h1 : |CR| * Zeta23.l T ≤ |CR| * Real.log T :=
      mul_le_mul_of_nonneg_left hl (abs_nonneg _)
    have h2 : |CR| * Real.log T ≤ T / (8 * π) * Real.log T := by
      refine mul_le_mul_of_nonneg_right ?_ (by linarith)
      rwa [le_div_iff₀ (by positivity)]
    linarith [show T / (8 * π) * Real.log T = T * Real.log T / (8 * π) by ring]
  have hlow := (abs_le.mp hRv0).1
  rw [zetaZeroConfig_N] at hlow
  linarith

/-- **Unconditional Equivalence of Full and Prime-Only Coalescent Surplus Hypotheses.**
Because proper prime powers in the coalescent band `0 < |log(n/m)| ≤ T^{−1+η}` (`η < 1/3`)
contribute `O(T^{−1/3+η} log T) = o(N(T, 2T))`, `CoalescentSurplusAtMost β` is unconditionally
equivalent to `PrimeCoalescentSurplusAtMost β`. -/
theorem coalescentSurplusAtMost_iff_primeCoalescentSurplusAtMost (β : ℝ) :
    CoalescentSurplusAtMost β ↔ PrimeCoalescentSurplusAtMost β := by
  have hπ := Real.pi_pos
  have hstep : ∀ {u : ℝ → ℝ} {ε₁ η δ : ℝ},
      WindowProfile ε₁ u → η < 1 / 3 → 0 < δ →
      ∀ᶠ T in atTop,
        |coalescentSurplus u η T - primeCoalescentSurplus u η T| ≤
          δ * (Ncount T (2 * T) : ℝ) := by
    intro u ε₁ η δ hu hη3 hδ
    have hexp : -1 / 3 + η < 1 := by linarith
    have hK : 0 ≤ 128 * Real.sqrt 2 / π := by positivity
    have hrate := eventually_log_pow_rpow_le 1 hexp hK (by positivity : (0 : ℝ) < δ / (8 * π))
    filter_upwards [eventually_abs_coalescentSurplus_sub_primeCoalescentSurplus_le hu (by linarith),
      eventually_T_mul_log_div_eight_pi_le_Ncount, hrate, eventually_l_bounds]
      with T hdiff hNlow hrt ⟨hlog1, _, _, _⟩
    have hrt' : (128 * Real.sqrt 2 / π) * Real.log T * T ^ (-1 / 3 + η) ≤ δ / (8 * π) * T := by
      simpa [pow_one, mul_assoc] using hrt
    have h1 : δ / (8 * π) * T ≤ δ * (T * Real.log T / (8 * π)) := by
      have hmul : δ / (8 * π) * T * 1 ≤ δ / (8 * π) * T * Real.log T :=
        mul_le_mul_of_nonneg_left hlog1 (by positivity)
      linarith [show δ / (8 * π) * T * Real.log T = δ * (T * Real.log T / (8 * π)) by ring]
    have h2 : δ * (T * Real.log T / (8 * π)) ≤ δ * (Ncount T (2 * T) : ℝ) :=
      mul_le_mul_of_nonneg_left hNlow hδ.le
    exact hdiff.trans (hrt'.trans (h1.trans h2))
  constructor
  · intro hfull ε hε
    obtain ⟨η, u, ε₁, hη0, hη3, hu, hev⟩ := hfull (ε / 2) (by linarith)
    refine ⟨η, u, ε₁, hη0, hη3, hu, ?_⟩
    filter_upwards [hev, hstep hu hη3 (by positivity : (0 : ℝ) < ε / 2)]
      with T ⟨hcert, hsurp⟩ hdiff
    obtain ⟨hlo, hhi⟩ := abs_le.mp hdiff
    constructor <;> linarith
  · intro hprime ε hε
    obtain ⟨η, u, ε₁, hη0, hη3, hu, hev⟩ := hprime (ε / 2) (by linarith)
    refine ⟨η, u, ε₁, hη0, hη3, hu, ?_⟩
    filter_upwards [hev, hstep hu hη3 (by positivity : (0 : ℝ) < ε / 2)]
      with T ⟨hcert, hsurp⟩ hdiff
    obtain ⟨hlo, hhi⟩ := abs_le.mp hdiff
    constructor <;> linarith

/-! ## §4. Parity-Halved Shift-Unrestricted 2D Selberg Prime-Pair Sieve -/

/-- For any `h ≥ 2` and any odd shift `d` (`d % 2 = 1`), the set of primes `m > h` with `m + d`
also prime is empty: both `m` and `m + d` exceed `2` and are prime, hence both are odd, which
contradicts `d` being odd. -/
theorem primePair_filter_odd_eq_empty (Y : ℝ) {h d : ℕ} (hh2 : 2 ≤ h) (hd : d % 2 = 1) :
    (Finset.Icc 1 ⌊Y⌋₊).filter (fun m => m.Prime ∧ (m + d).Prime ∧ h < m) = ∅ := by
  rw [Finset.filter_eq_empty_iff]
  intro m _ ⟨hmP, hmdP, hhm⟩
  have hm_ne2 : m ≠ 2 := by omega
  have hmd_ne2 : m + d ≠ 2 := by omega
  have hm_odd : m % 2 = 1 := hmP.eq_two_or_odd.resolve_left hm_ne2
  have hmd_odd : (m + d) % 2 = 1 := hmdP.eq_two_or_odd.resolve_left hmd_ne2
  omega

/-- Every sifting prime in `rangePrimes P₁ h` (`2 ≤ P₁`) is at least `3`, hence odd, so
`p ∣ 2 * r ↔ p ∣ r`. -/
theorem rangePrimes_filter_dvd_two_mul {P₁ : ℕ} (hP₁ : 2 ≤ P₁) (h r : ℕ) :
    (rangePrimes P₁ h).filter (fun p => p ∣ 2 * r) =
      (rangePrimes P₁ h).filter (fun p => p ∣ r) := by
  ext p
  simp only [Finset.mem_filter]
  refine and_congr_right fun hp => ⟨fun hdvd => ?_, fun hdvd => dvd_mul_of_dvd_right hdvd 2⟩
  have hpP : p.Prime := rangePrimes_prime hp
  rcases hpP.dvd_mul.mp hdvd with hp2 | hpr
  · rw [rangePrimes, Finset.mem_filter, Finset.mem_Icc] at hp
    have : p ≤ 2 := Nat.le_of_dvd (by norm_num) hp2
    omega
  · exact hpr

/-- If `f d = 0` for every odd `d ∈ Icc 1 K`, then `∑_{d ∈ Icc 1 K} f d = ∑_{r ∈ Icc 1 (K/2)} f (2r)`. -/
theorem sum_Icc_eq_sum_even_shifts (K : ℕ) (f : ℕ → ℝ)
    (hodd : ∀ d ∈ Finset.Icc 1 K, d % 2 = 1 → f d = 0) :
    ∑ d ∈ Finset.Icc 1 K, f d = ∑ r ∈ Finset.Icc 1 (K / 2), f (2 * r) := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 K) (fun d => d % 2 = 0) f]
  have hodd_zero : ∑ d ∈ (Finset.Icc 1 K).filter (fun d => ¬ d % 2 = 0), f d = 0 := by
    refine Finset.sum_eq_zero fun d hd => ?_
    rw [Finset.mem_filter] at hd
    exact hodd d hd.1 (by omega)
  rw [hodd_zero, add_zero]
  refine (Finset.sum_nbij (fun r => 2 * r) ?_ ?_ ?_ (fun _ _ => rfl)).symm
  · intro r hr
    rw [Finset.mem_Icc] at hr
    rw [Finset.mem_filter, Finset.mem_Icc]
    omega
  · intro r₁ _ r₂ _ h
    omega
  · intro d hd
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hd
    refine ⟨d / 2, ?_, by omega⟩
    simp only [Finset.mem_coe, Finset.mem_Icc]
    omega

/-- **Even-Shift Singular-Series Average Bound.**
Averaged over the even shifts `2r` (`1 ≤ r ≤ K / 2`), the reciprocal shift correction of the
2D Selberg sieve is bounded by `e * ⌊K/2⌋ ≤ e * K / 2`, saving a full factor of `2` over the
parity-blind shift sum. -/
theorem sum_inv_shiftCorrection_even_le {P₁ : ℕ} (hP₁ : 2 ≤ P₁) (h K : ℕ) :
    ∑ r ∈ Finset.Icc 1 (K / 2),
        (∏ p ∈ (rangePrimes P₁ h).filter (fun p => p ∣ 2 * r), ((p : ℝ) / ((p : ℝ) - 1)))
      ≤ Real.exp 1 * ((K / 2 : ℕ) : ℝ) ∧
    Real.exp 1 * ((K / 2 : ℕ) : ℝ) ≤ Real.exp 1 * (K : ℝ) / 2 := by
  have heq : ∑ r ∈ Finset.Icc 1 (K / 2),
        (∏ p ∈ (rangePrimes P₁ h).filter (fun p => p ∣ 2 * r), ((p : ℝ) / ((p : ℝ) - 1)))
      = ∑ r ∈ Finset.Icc 1 (K / 2),
        (∏ p ∈ (rangePrimes P₁ h).filter (fun p => p ∣ r), ((p : ℝ) / ((p : ℝ) - 1))) := by
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [rangePrimes_filter_dvd_two_mul hP₁ h r]
  refine ⟨heq ▸ sum_inv_shiftCorrection_le hP₁ h (K / 2), ?_⟩
  have hdiv : ((K / 2 : ℕ) : ℝ) ≤ (K : ℝ) / 2 := by
    have : 2 * (K / 2) ≤ K := Nat.mul_div_le K 2
    have hcast : (2 : ℝ) * ((K / 2 : ℕ) : ℝ) ≤ (K : ℝ) := by exact_mod_cast this
    linarith
  have hexp : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
  calc Real.exp 1 * ((K / 2 : ℕ) : ℝ) ≤ Real.exp 1 * ((K : ℝ) / 2) :=
        mul_le_mul_of_nonneg_left hdiv hexp
    _ = Real.exp 1 * (K : ℝ) / 2 := by ring

/-- **Parity-Halved Shift-Unrestricted 2D Selberg Prime-Pair Sieve.**
For **every** `K : ℕ` (with no restriction `K ≤ P₁^P₁`), eliminating the empty odd shifts `d` and
using `p ∣ 2r ↔ p ∣ r` on the odd sifting primes `P₁ < p ≤ h` (`P₁ ≥ 2`) cuts both the main term
and the remainder of `RHTower.Sieve.sum_card_primePair_le_sharp` in half:
`∑_{1 ≤ d ≤ K} #{m ≤ Y : m, m+d prime, m > h} ≤ e K Y / exp(S(h) − S(P₁))² + (K/2) R`. -/
theorem sum_card_primePair_le_parity_unrestricted (Y : ℝ) {P₁ : ℕ} (hP₁ : 2 ≤ P₁) {h : ℕ}
    (K : ℕ) {z : ℝ} (hz : 1 ≤ z) (hY : 0 ≤ Y) (hh2 : 2 ≤ h) (hP₁h : P₁ ≤ h)
    (hlev : ((h : ℝ)) ^ (18 : ℝ) ≤ Real.sqrt z)
    (hlog : 20 * mertensFirstConst ≤ Real.log h) :
    ∑ d ∈ Finset.Icc 1 K,
        ((((Finset.Icc 1 ⌊Y⌋₊).filter
            (fun m => m.Prime ∧ (m + d).Prime ∧ h < m)).card : ℕ) : ℝ)
      ≤ Real.exp 1 * (K : ℝ) * Y / (Real.exp (mertensS h - mertensS P₁)) ^ (2 : ℕ)
        + ((K : ℝ) / 2) * ∑ e ∈ (rangePrimorial P₁ h).divisors,
            (if ((e : ℕ) : ℝ) ≤ z then 2 * 6 ^ e.primeFactors.card else 0) := by
  classical
  set E : ℝ := Real.exp (mertensS h - mertensS P₁) with hE
  set R : ℝ := ∑ e ∈ (rangePrimorial P₁ h).divisors,
      (if ((e : ℕ) : ℝ) ≤ z then 2 * 6 ^ e.primeFactors.card else 0) with hR
  have hE0 : (0 : ℝ) < E := Real.exp_pos _
  have hR0 : 0 ≤ R := by
    refine Finset.sum_nonneg fun e _ => ?_
    split_ifs <;> positivity
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
            (fun m => m.Prime ∧ (m + d).Prime ∧ h < m)).card : ℕ) : ℝ)
        ≤ (2 * Y / E ^ (2 : ℕ))
            * (∏ p ∈ (rangePrimes P₁ h).filter (fun p => p ∣ d), ((p : ℝ) / ((p : ℝ) - 1)))
          + R := by
    intro d
    refine le_trans (card_primePair_le_sharp Y hP₁ d hz hY hh2 hP₁h hlev hlog) ?_
    have hinv : (∏ p ∈ (rangePrimes P₁ h).filter (fun p => p ∣ d), ((p : ℝ) / ((p : ℝ) - 1)))
        = (∏ p ∈ (rangePrimes P₁ h).filter (fun p => p ∣ d), (((p : ℝ) - 1) / (p : ℝ)))⁻¹ := by
      rw [← Finset.prod_inv_distrib]
      refine Finset.prod_congr rfl fun p _ => ?_
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
  have heven := sum_Icc_eq_sum_even_shifts K
    (fun d => ((((Finset.Icc 1 ⌊Y⌋₊).filter
      (fun m => m.Prime ∧ (m + d).Prime ∧ h < m)).card : ℕ) : ℝ))
    (fun d _ hd => by rw [primePair_filter_odd_eq_empty Y hh2 hd]; simp)
  rw [heven]
  refine (Finset.sum_le_sum fun r _ => hterm (2 * r)).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
  have hK2 : (((K / 2) + 1 - 1 : ℕ) : ℝ) = ((K / 2 : ℕ) : ℝ) := by congr 1
  rw [hK2, ← Finset.mul_sum]
  obtain ⟨hshift1, hshift2⟩ := sum_inv_shiftCorrection_even_le hP₁ h K
  have hshift := hshift1.trans hshift2
  have hdiv : ((K / 2 : ℕ) : ℝ) ≤ (K : ℝ) / 2 := by
    have : 2 * (K / 2) ≤ K := Nat.mul_div_le K 2
    have hcast : (2 : ℝ) * ((K / 2 : ℕ) : ℝ) ≤ (K : ℝ) := by exact_mod_cast this
    linarith
  refine add_le_add ?_ (mul_le_mul_of_nonneg_right hdiv hR0)
  have hcoef : (0 : ℝ) ≤ 2 * Y / E ^ (2 : ℕ) := by positivity
  calc (2 * Y / E ^ (2 : ℕ)) * ∑ r ∈ Finset.Icc 1 (K / 2),
        (∏ p ∈ (rangePrimes P₁ h).filter (fun p => p ∣ 2 * r), ((p : ℝ) / ((p : ℝ) - 1)))
      ≤ (2 * Y / E ^ (2 : ℕ)) * (Real.exp 1 * (K : ℝ) / 2) :=
        mul_le_mul_of_nonneg_left hshift hcoef
    _ = Real.exp 1 * (K : ℝ) * Y / E ^ (2 : ℕ) := by ring

/-- **Parity-Halved Shift-Unrestricted Marker-Block Prime-Pair Budget.**
For any marker block `bigPrimeSet M₀ b` with `2 ≤ P₁ ≤ h ≤ M₀` and **any** `K : ℕ`,
`∑_{1 ≤ d ≤ K} #{p ∈ bigPrimeSet M₀ b : p + d ∈ bigPrimeSet M₀ b} ≤ e K b / exp(S(h) − S(P₁))² + (K/2) R`. -/
theorem sum_card_shift_bigPrimeSet_le_parity_unrestricted {M₀ b : ℕ} {P₁ : ℕ} (hP₁ : 2 ≤ P₁)
    {h : ℕ} (K : ℕ) {z : ℝ} (hz : 1 ≤ z) (hh2 : 2 ≤ h) (hP₁h : P₁ ≤ h) (hhM : h ≤ M₀)
    (hlev : ((h : ℝ)) ^ (18 : ℝ) ≤ Real.sqrt z)
    (hlog : 20 * mertensFirstConst ≤ Real.log h) :
    ∑ d ∈ Finset.Icc 1 K,
        ((((bigPrimeSet M₀ b).filter
          (fun p => p + d ∈ bigPrimeSet M₀ b)).card : ℕ) : ℝ)
      ≤ Real.exp 1 * (K : ℝ) * (b : ℝ) / (Real.exp (mertensS h - mertensS P₁)) ^ (2 : ℕ)
        + ((K : ℝ) / 2) * ∑ e ∈ (rangePrimorial P₁ h).divisors,
            (if ((e : ℕ) : ℝ) ≤ z then 2 * 6 ^ e.primeFactors.card else 0) := by
  classical
  have hfloor : ⌊((b : ℕ) : ℝ)⌋₊ = b := Nat.floor_natCast _
  have hsieve := sum_card_primePair_le_parity_unrestricted ((b : ℕ) : ℝ) hP₁ K hz
    (Nat.cast_nonneg b) hh2 hP₁h hlev hlog
  rw [hfloor] at hsieve
  exact le_trans (sum_card_shift_bigPrimeSet_le hhM K) hsieve

end GaloisForLFunctions.TransThresholdPairCorrelation

