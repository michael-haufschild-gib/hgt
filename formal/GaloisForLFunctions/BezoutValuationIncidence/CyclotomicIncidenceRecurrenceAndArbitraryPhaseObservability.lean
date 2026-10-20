import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import GaloisForLFunctions.BezoutValuationIncidence.TranslatedWindowStrideAnnihilationAndLcmReturnObservability

/-!
# The cyclotomic incidence recurrence and arbitrary-phase observability

Let `E` be the unit shift on sequences and `Q_N = ∏_{q ≤ N} Φ_q` the product of the first `N`
cyclotomic polynomials, of degree `Φ(N) = Σ_{q ≤ N} φ(q)`. Each divisibility indicator
`k ↦ [d ∣ k]` is `d`-periodic, so `E^d - 1 = ∏_{q ∣ d} Φ_q` kills it; hence

* every level-`N` response `s(k) = Σ_{d ≤ N, d ∣ k} c(d)` and every prefix discrepancy satisfy the
  same linear recurrence `Q_N(E) s = 0`, whatever the row;
* `Q_N` is the shortest universal recurrence: a polynomial annihilating all level-`N` responses is
  divisible by `Q_N`, because the shifts of `[d ∣ ·]` are the `d` residue-class indicators.

A monic recurrence propagates vanishing forward, and responses are `N!`-periodic. So at **every**
phase, `Φ(N)` consecutive values of the response determine the row on `[1, N]`, and `Φ(N)`
consecutive values of the discrepancy decide whether the variance vanishes. The horizon
`Φ(N) ≤ N(N+1)/2` is quadratic without logarithm, against the exponential `lcm(1..N) + N + 1`
window and the window-sandwich horizon of order `N² log N`. It is not the sharp horizon: at common
returns `2N - 3` discrepancy samples already suffice.
-/

open Finset Polynomial GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
set_option autoImplicit false

/-! ## §1. The shift calculus -/

/-- The unit shift `(E s)(n) = s(n + 1)`. -/
def sequenceUnitShift : Module.End ℝ (ℕ → ℝ) := LinearMap.funLeft ℝ ℝ (· + 1)

theorem sequenceUnitShift_pow_apply (i : ℕ) (s : ℕ → ℝ) (n : ℕ) :
    (sequenceUnitShift ^ i) s n = s (n + i) := by
  induction i generalizing n s with
  | zero => rfl
  | succ i ih =>
    rw [pow_succ, Module.End.mul_apply, ih]
    rfl

/-- `p(E)` acts by coefficient convolution, over any range beyond the degree. -/
theorem aeval_sequenceUnitShift_apply' {p : ℝ[X]} {m : ℕ} (hm : p.natDegree < m)
    (s : ℕ → ℝ) (n : ℕ) :
    aeval sequenceUnitShift p s n = ∑ i ∈ range m, p.coeff i * s (n + i) := by
  rw [aeval_eq_sum_range' hm, LinearMap.sum_apply, Finset.sum_apply]
  refine sum_congr rfl fun i _ => ?_
  rw [LinearMap.smul_apply, Pi.smul_apply, sequenceUnitShift_pow_apply, smul_eq_mul]

theorem aeval_sequenceUnitShift_apply (p : ℝ[X]) (s : ℕ → ℝ) (n : ℕ) :
    aeval sequenceUnitShift p s n = ∑ i ∈ range (p.natDegree + 1), p.coeff i * s (n + i) :=
  aeval_sequenceUnitShift_apply' (Nat.lt_succ_self _) s n

/-- `E^d - 1` kills every `d`-periodic sequence. -/
theorem aeval_X_pow_sub_one_of_periodic {d : ℕ} {s : ℕ → ℝ} (hs : ∀ n, s (n + d) = s n) :
    aeval sequenceUnitShift (X ^ d - 1 : ℝ[X]) s = 0 := by
  funext n
  rw [map_sub, map_pow, aeval_X, map_one, LinearMap.sub_apply, Pi.sub_apply,
    sequenceUnitShift_pow_apply, Module.End.one_apply, hs, sub_self, Pi.zero_apply]

/-- Annihilation passes to multiples. -/
theorem aeval_eq_zero_of_dvd {p q : ℝ[X]} (hpq : p ∣ q) {s : ℕ → ℝ}
    (hs : aeval sequenceUnitShift p s = 0) : aeval sequenceUnitShift q s = 0 := by
  obtain ⟨r, rfl⟩ := hpq
  rw [mul_comm, aeval_mul, Module.End.mul_apply, hs, map_zero]

/-- **Forward propagation.** A sequence killed by a monic `p(E)` and vanishing on `deg p`
consecutive integers vanishes from there on. -/
theorem eq_zero_of_aeval_monic {p : ℝ[X]} (hp : p.Monic) {s : ℕ → ℝ}
    (hs : aeval sequenceUnitShift p s = 0) {A : ℕ}
    (hwin : ∀ n ∈ Ico A (A + p.natDegree), s n = 0) : ∀ n, A ≤ n → s n = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hAn
    by_cases hn : n < A + p.natDegree
    · exact hwin n (mem_Ico.mpr ⟨hAn, hn⟩)
    · obtain ⟨n0, rfl⟩ : ∃ n0, n = n0 + p.natDegree := ⟨n - p.natDegree, by omega⟩
      have h := congrFun hs n0
      rw [aeval_sequenceUnitShift_apply, Pi.zero_apply, Finset.sum_range_succ, hp.coeff_natDegree,
        one_mul] at h
      have hrest : ∑ i ∈ range p.natDegree, p.coeff i * s (n0 + i) = 0 :=
        sum_eq_zero fun i hi => by
          have := mem_range.mp hi
          rw [ih (n0 + i) (by omega) (by omega), mul_zero]
      rwa [hrest, zero_add] at h

/-! ## §2. The cyclotomic incidence polynomial -/

/-- `Q_N = ∏_{q ≤ N} Φ_q`. -/
def cyclotomicIncidencePolynomial (N : ℕ) : ℝ[X] := ∏ q ∈ Icc 1 N, cyclotomic q ℝ

/-- The order `Φ(N) = Σ_{q ≤ N} φ(q)` of the cyclotomic incidence recurrence. -/
def cyclotomicIncidenceOrder (N : ℕ) : ℕ := ∑ q ∈ Icc 1 N, q.totient

theorem cyclotomicIncidencePolynomial_monic (N : ℕ) : (cyclotomicIncidencePolynomial N).Monic :=
  monic_prod_of_monic _ _ fun q _ => cyclotomic.monic q ℝ

theorem natDegree_cyclotomicIncidencePolynomial (N : ℕ) :
    (cyclotomicIncidencePolynomial N).natDegree = cyclotomicIncidenceOrder N := by
  rw [cyclotomicIncidencePolynomial, natDegree_prod_of_monic _ _ fun q _ => cyclotomic.monic q ℝ]
  exact sum_congr rfl fun q _ => natDegree_cyclotomic q ℝ

theorem X_pow_sub_one_dvd_cyclotomicIncidencePolynomial {N d : ℕ} (hd : d ∈ Icc 1 N) :
    (X ^ d - 1 : ℝ[X]) ∣ cyclotomicIncidencePolynomial N := by
  rw [← prod_cyclotomic_eq_X_pow_sub_one (mem_Icc.mp hd).1]
  exact prod_dvd_prod_of_subset _ _ _ fun e he =>
    mem_Icc.mpr ⟨Nat.pos_of_mem_divisors he, (Nat.divisor_le he).trans (mem_Icc.mp hd).2⟩

/-- `2 Φ(N) ≤ N (N + 1)`. -/
theorem two_mul_cyclotomicIncidenceOrder_le (N : ℕ) :
    2 * cyclotomicIncidenceOrder N ≤ N * (N + 1) := by
  induction N with
  | zero => simp [cyclotomicIncidenceOrder]
  | succ N ih =>
    rw [cyclotomicIncidenceOrder, sum_Icc_succ_top (by omega), mul_add, ← cyclotomicIncidenceOrder]
    have := Nat.totient_le (N + 1)
    nlinarith

/-! ## §3. The universal recurrence of responses and discrepancies -/

/-- The divisibility indicator `k ↦ [d ∣ k]`. -/
def divisibilityIndicatorSeq (d : ℕ) : ℕ → ℝ := fun k => if d ∣ k then 1 else 0

theorem divisibilityIndicatorSeq_periodic (d n : ℕ) :
    divisibilityIndicatorSeq d (n + d) = divisibilityIndicatorSeq d n := by
  simp only [divisibilityIndicatorSeq, Nat.dvd_add_self_right]

theorem sieveSeq_eq_sum_smul_indicator (N : ℕ) (c : ℕ → ℝ) :
    sieveSeq N c = ∑ d ∈ Icc 1 N, c d • divisibilityIndicatorSeq d := by
  funext k
  rw [sieveSeq, sum_filter, Finset.sum_apply]
  refine sum_congr rfl fun d _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, divisibilityIndicatorSeq]
  split_ifs <;> simp

/-- **Universal cyclotomic recurrence of responses.** `Q_N(E)` kills every level-`N` response. -/
theorem aeval_cyclotomicIncidencePolynomial_sieveSeq (N : ℕ) (c : ℕ → ℝ) :
    aeval sequenceUnitShift (cyclotomicIncidencePolynomial N) (sieveSeq N c) = 0 := by
  rw [sieveSeq_eq_sum_smul_indicator, map_sum]
  refine sum_eq_zero fun d hd => ?_
  rw [map_smul, aeval_eq_zero_of_dvd (X_pow_sub_one_dvd_cyclotomicIncidencePolynomial hd)
    (aeval_X_pow_sub_one_of_periodic (divisibilityIndicatorSeq_periodic d)), smul_zero]

/-- The recurrence written out: `s(n + Φ(N)) = -Σ_{i < Φ(N)} Q_{N,i} s(n + i)`. -/
theorem sieveSeq_cyclotomic_recurrence (N : ℕ) (c : ℕ → ℝ) (n : ℕ) :
    sieveSeq N c (n + cyclotomicIncidenceOrder N) =
      -∑ i ∈ range (cyclotomicIncidenceOrder N),
        (cyclotomicIncidencePolynomial N).coeff i * sieveSeq N c (n + i) := by
  have h := congrFun (aeval_cyclotomicIncidencePolynomial_sieveSeq N c) n
  rw [aeval_sequenceUnitShift_apply, Pi.zero_apply, Finset.sum_range_succ,
    (cyclotomicIncidencePolynomial_monic N).coeff_natDegree, one_mul,
    natDegree_cyclotomicIncidencePolynomial] at h
  linarith

theorem fractDivSeq_periodic {d : ℕ} (hd : 0 < d) (n : ℕ) :
    fractDivSeq d (n + d) = fractDivSeq d n := by
  unfold fractDivSeq
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [Nat.cast_add, add_div, div_self hd', Int.fract_add_one]

/-- The discrepancy obeys the same recurrence: it is a combination of `d`-periodic sawtooth
phases with `d ≤ N`. -/
theorem aeval_cyclotomicIncidencePolynomial_discrepancy (N : ℕ) (c : ℕ → ℝ) :
    aeval sequenceUnitShift (cyclotomicIncidencePolynomial N)
      (fun M => sievePrefixDiscrepancy N M c) = 0 := by
  have hD : (fun M => sievePrefixDiscrepancy N M c) =
      ∑ d ∈ Icc 1 N, (-c d) • fractDivSeq d := by
    funext M
    rw [sievePrefixDiscrepancy_eq_neg_sievedFractSum, sievedFractSum, Finset.sum_apply,
      ← sum_neg_distrib]
    exact sum_congr rfl fun d _ => by simp
  rw [hD, map_sum]
  refine sum_eq_zero fun d hd => ?_
  rw [map_smul, aeval_eq_zero_of_dvd (X_pow_sub_one_dvd_cyclotomicIncidencePolynomial hd)
    (aeval_X_pow_sub_one_of_periodic (fractDivSeq_periodic (mem_Icc.mp hd).1)), smul_zero]

/-! ## §4. Observability at every phase -/

theorem sieveSeq_add_mul_factorial (N : ℕ) (c : ℕ → ℝ) (k j : ℕ) :
    sieveSeq N c (k + j * N.factorial) = sieveSeq N c k := by
  unfold sieveSeq
  refine sum_congr (filter_congr fun d hd => ?_) fun _ _ => rfl
  exact Nat.dvd_add_left
    ((Nat.dvd_factorial (mem_Icc.mp hd).1 (mem_Icc.mp hd).2).mul_left j)

/-- The response on `[1, N]` determines the row there. -/
theorem eq_zero_of_sieveSeq_initial {N : ℕ} {c : ℕ → ℝ}
    (h : ∀ k ∈ Icc 1 N, sieveSeq N c k = 0) : ∀ d ∈ Icc 1 N, c d = 0 := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro hd
    have h0 := h d hd
    have hmem : d ∈ (Icc 1 N).filter (fun e => e ∣ d) := mem_filter.mpr ⟨hd, dvd_refl d⟩
    unfold sieveSeq at h0
    rwa [sum_eq_single_of_mem d hmem fun e he hne => ih e
      (lt_of_le_of_ne (Nat.le_of_dvd (mem_Icc.mp hd).1 (mem_filter.mp he).2) hne)
      (mem_filter.mp he).1] at h0

/-- **Arbitrary-phase response observability.** At every phase `A`, the response vanishes on the
`Φ(N)` integers `A, …, A + Φ(N) - 1` only for the zero row on `[1, N]`. -/
theorem sieveSeq_window_eq_zero_iff (N A : ℕ) (c : ℕ → ℝ) :
    (∀ k ∈ Ico A (A + cyclotomicIncidenceOrder N), sieveSeq N c k = 0) ↔
      ∀ d ∈ Icc 1 N, c d = 0 := by
  constructor
  · intro hwin
    have hprop := eq_zero_of_aeval_monic (cyclotomicIncidencePolynomial_monic N)
      (aeval_cyclotomicIncidencePolynomial_sieveSeq N c)
      (by rwa [natDegree_cyclotomicIncidencePolynomial])
    refine eq_zero_of_sieveSeq_initial fun k _ => ?_
    rw [← sieveSeq_add_mul_factorial N c k A]
    exact hprop _ (le_add_left (Nat.le_mul_of_pos_right A (Nat.factorial_pos N)))
  · intro hc k _
    exact sum_eq_zero fun d hd => hc d (mem_filter.mp hd).1

/-- **Arbitrary-phase discrepancy observability.** At every phase `A`, the discrepancy vanishes on
`Φ(N)` consecutive integers exactly when the row has zero variance. -/
theorem sievePrefixDiscrepancy_window_eq_zero_iff (N A : ℕ) (c : ℕ → ℝ) :
    (∀ M ∈ Ico A (A + cyclotomicIncidenceOrder N), sievePrefixDiscrepancy N M c = 0) ↔
      sieveVariance N c = 0 := by
  constructor
  · intro hwin
    have hprop := eq_zero_of_aeval_monic (s := fun M => sievePrefixDiscrepancy N M c)
      (cyclotomicIncidencePolynomial_monic N) (aeval_cyclotomicIncidencePolynomial_discrepancy N c)
      (by rwa [natDegree_cyclotomicIncidencePolynomial])
    exact (sievePrefixDiscrepancy_arbitrary_phase_lcm_window_zero_iff N A c).mp
      fun M hM => hprop M (mem_Icc.mp hM).1
  · intro hV M _
    rw [sieveVariance_eq_zero_iff_tail_zero] at hV
    rw [sievePrefixDiscrepancy_eq_neg_sievedFractSum, sievedFractSum, neg_eq_zero]
    refine sum_eq_zero fun d hd => ?_
    rcases (mem_Icc.mp hd).1.eq_or_lt with rfl | h2
    · simp [fractDivSeq]
    · rw [hV d (mem_Icc.mpr ⟨h2, (mem_Icc.mp hd).2⟩), zero_mul]

/-! ## §5. `Q_N` is the shortest universal recurrence -/

/-- A recurrence killing `[d ∣ ·]` is a multiple of `X^d - 1`: the shifts of the indicator are the
`d` residue-class indicators, which are independent. -/
theorem X_pow_sub_one_dvd_of_aeval_indicator {d : ℕ} (hd : 0 < d) {p : ℝ[X]}
    (hp : aeval sequenceUnitShift p (divisibilityIndicatorSeq d) = 0) :
    (X ^ d - 1 : ℝ[X]) ∣ p := by
  have hmon : (X ^ d - 1 : ℝ[X]).Monic := by simpa using monic_X_pow_sub_C (1 : ℝ) hd.ne'
  have hnd : (X ^ d - 1 : ℝ[X]).natDegree = d := by
    simpa using natDegree_X_pow_sub_C (n := d) (r := (1 : ℝ))
  have hne1 : (X ^ d - 1 : ℝ[X]) ≠ 1 := fun h => by
    rw [h, natDegree_one] at hnd
    omega
  have hlt : (p %ₘ (X ^ d - 1)).natDegree < d := by
    have := natDegree_modByMonic_lt p hmon hne1
    rwa [hnd] at this
  have hr : aeval sequenceUnitShift (p %ₘ (X ^ d - 1)) (divisibilityIndicatorSeq d) = 0 := by
    have hsplit := modByMonic_add_div p (X ^ d - 1)
    have hq : aeval sequenceUnitShift ((X ^ d - 1) * (p /ₘ (X ^ d - 1)))
        (divisibilityIndicatorSeq d) = 0 :=
      aeval_eq_zero_of_dvd (dvd_mul_right _ _)
        (aeval_X_pow_sub_one_of_periodic (divisibilityIndicatorSeq_periodic d))
    have := congrArg (fun q => aeval sequenceUnitShift q (divisibilityIndicatorSeq d)) hsplit
    simp only [map_add, LinearMap.add_apply] at this
    rw [hq, add_zero] at this
    rw [this, hp]
  refine (modByMonic_eq_zero_iff_dvd hmon).mp (Polynomial.ext fun i => ?_)
  rw [coeff_zero]
  by_cases hi : i < d
  · have h := congrFun hr (d - i)
    rw [aeval_sequenceUnitShift_apply' hlt, Pi.zero_apply,
      sum_eq_single_of_mem i (mem_range.mpr hi) fun j hj hji => ?_] at h
    · simpa [divisibilityIndicatorSeq, show d - i + i = d by omega] using h
    · have hj' := mem_range.mp hj
      have hndvd : ¬ d ∣ d - i + j := fun hdvd => hji (by
        have := Nat.eq_of_dvd_of_lt_two_mul (by omega) hdvd (by omega)
        omega)
      simp [divisibilityIndicatorSeq, hndvd]
  · exact coeff_eq_zero_of_natDegree_lt (by omega)

theorem isCoprime_cyclotomic_real {q q' : ℕ} (h : q ≠ q') :
    IsCoprime (cyclotomic q ℝ) (cyclotomic q' ℝ) := by
  simpa [coe_mapRingHom, map_cyclotomic] using
    (cyclotomic.isCoprime_rat h).map (mapRingHom (algebraMap ℚ ℝ))

/-- **Minimality.** Every polynomial annihilating all level-`N` responses is a multiple of `Q_N`. -/
theorem cyclotomicIncidencePolynomial_dvd_of_annihilates {N : ℕ} {p : ℝ[X]}
    (hp : ∀ c : ℕ → ℝ, aeval sequenceUnitShift p (sieveSeq N c) = 0) :
    cyclotomicIncidencePolynomial N ∣ p := by
  classical
  refine prod_dvd_of_coprime (fun q _ q' _ hqq' => isCoprime_cyclotomic_real hqq')
    fun q hq => (cyclotomic.dvd_X_pow_sub_one q ℝ).trans
      (X_pow_sub_one_dvd_of_aeval_indicator (mem_Icc.mp hq).1 ?_)
  have hs : sieveSeq N (fun e => if e = q then 1 else 0) = divisibilityIndicatorSeq q := by
    rw [sieveSeq_eq_sum_smul_indicator, sum_eq_single_of_mem q hq fun e _ he => by simp [he]]
    simp
  rw [← hs]
  exact hp _

/-- The order `Φ(N)` cannot be lowered: a nonzero universal recurrence has degree `≥ Φ(N)`. -/
theorem cyclotomicIncidenceOrder_le_natDegree {N : ℕ} {p : ℝ[X]} (hp0 : p ≠ 0)
    (hp : ∀ c : ℕ → ℝ, aeval sequenceUnitShift p (sieveSeq N c) = 0) :
    cyclotomicIncidenceOrder N ≤ p.natDegree := by
  rw [← natDegree_cyclotomicIncidencePolynomial]
  exact natDegree_le_of_dvd (cyclotomicIncidencePolynomial_dvd_of_annihilates hp) hp0

end

end GaloisForLFunctions.BezoutValuationIncidence
