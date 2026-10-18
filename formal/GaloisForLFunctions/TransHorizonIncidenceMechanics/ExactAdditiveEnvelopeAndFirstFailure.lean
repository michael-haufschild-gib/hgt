import GaloisForLFunctions.TransHorizonIncidenceMechanics.FourthBandEnvelopeAndSharpFiveHorizonBoundary

/-!
# Exact additive boundary of the damped unit envelope

Classical baseline: integer Dirichlet-hyperbola truncation, multiplicative Möbius
deletion, radical invariance, and discrete polarization. The truncated sum is
exactly D(n;a) of Helfgott–Thompson, Proposition 3.2:
https://doi.org/10.1007/s40993-022-00408-8. Observation and finite shifted-correlation
baselines: [TH10] https://arxiv.org/abs/1009.5281 and
[CMS16] https://arxiv.org/abs/1612.03136.

Equivalent classical formulation: for ε≥0, |Σ_{d∣k,d≤N} μ(d)d^(-ε)|≤1 whenever
2≤k<5(N+1). An omitted divisor is at least N+1, so the four-channel tail formula
extends through 5N+4. Positive unit residuals are covered exactly: one-prime
deletion at u=1 equals zero, and two-prime deletion equals one.

The universal real additive buffer b after 5N is admissible exactly when b<5;
for natural buffers this is b≤4. The existing cofinal response-two family at
5N+5 now realizes the first unit-envelope failure at each of its horizons.
Radical/power transport yields 2D≤-E≤0 on the extended certified families,
including zero horizon. Any response exceeding one requires radical≥5(N+1).

Classification: New formulation, with standard constituents labeled below.
No external novelty claim. The sharp boundary concerns endpoint envelopes,
not a positive-defect obstruction or a fixed-positive-damping classification.
-/

open Finset ArithmeticFunction
open GaloisForLFunctions.BiScaleUncertainty GaloisForLFunctions.BezoutValuationIncidence
open RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius
namespace GaloisForLFunctions.TransHorizonIncidenceMechanics
noncomputable section
set_option autoImplicit false

/-- [Known] The least omitted divisor N+1 gives the exact integer quotient cutoff. -/
theorem complementary_quotient_le_of_lt_succ_mul {N B k q : ℕ}
    (hk : k < (B + 1) * (N + 1)) (hq_dvd : q ∣ k) (hq_gt : N < k / q) :
    1 ≤ q ∧ q ≤ B := by
  have hk_pos : 0 < k := by
    by_contra h
    have hk0 : k = 0 := by omega
    subst k
    simp at hq_gt
  have hq_pos : 0 < q := Nat.pos_of_dvd_of_pos hq_dvd hk_pos
  have hmul : q * (k / q) = k := Nat.mul_div_cancel' hq_dvd
  refine ⟨hq_pos, ?_⟩
  by_contra hqB
  have hq : B + 1 ≤ q := by omega
  have hd : N + 1 ≤ k / q := by omega
  nlinarith

/-- [Known] Integer hyperbola truncation confines the tail to its small quotient channels. -/
theorem complementaryQuotientTail_eq_sum_Icc_of_lt_succ_mul {N B k : ℕ}
    (hk : k < (B + 1) * (N + 1)) (c : ℕ → ℝ) :
    complementaryQuotientTail N c k =
      ∑ q ∈ (Icc 1 B).filter (fun q => q ∣ k ∧ N < k / q), c (k / q) := by
  unfold complementaryQuotientTail
  congr 1
  ext q
  simp only [mem_filter, Nat.mem_divisors, mem_Icc]
  constructor
  · rintro ⟨⟨hqk, _⟩, hqN⟩
    exact ⟨complementary_quotient_le_of_lt_succ_mul hk hqk hqN, hqk, hqN⟩
  · rintro ⟨⟨_, _⟩, hqk, hqN⟩
    have hk0 : k ≠ 0 := by
      intro h0
      subst k
      simp at hqN
    exact ⟨⟨hqk, hk0⟩, hqN⟩

/-- [New formulation] The full band normal form extends through the integer buffer before the next channel opens. -/
theorem sieveSeq_integer_band_eq_sum_divisors_sub_quotients {B N k : ℕ}
    (hlo : B * N < k) (hhi : k < (B + 1) * (N + 1)) (c : ℕ → ℝ) :
    sieveSeq N c k = (∑ d ∈ k.divisors, c d) -
      ∑ q ∈ Icc 1 B, if q ∣ k then c (k / q) else 0 := by
  rw [sieveSeq_eq_sum_divisors_sub_complementaryQuotientTail N (by omega) c,
    complementaryQuotientTail_eq_sum_Icc_of_lt_succ_mul hhi c,
    filter_Icc_complementary_quotients_of_band hlo, sum_filter]

private theorem Icc_one_four : Icc (1 : ℕ) 4 = {1, 2, 3, 4} := by
  ext q
  simp only [mem_Icc, mem_insert, mem_singleton]
  omega

/-- [Corollary] Only quotient channels one through four occur before 5(N+1). -/
theorem sieveSeq_fourth_integer_band_eq_sum_divisors_sub {N k : ℕ}
    (hlo : 4 * N < k) (hhi : k < 5 * (N + 1)) (c : ℕ → ℝ) :
    sieveSeq N c k = (∑ d ∈ k.divisors, c d) - c k -
      (if 2 ∣ k then c (k / 2) else 0) - (if 3 ∣ k then c (k / 3) else 0) -
      (if 4 ∣ k then c (k / 4) else 0) := by
  rw [sieveSeq_integer_band_eq_sum_divisors_sub_quotients hlo hhi c, Icc_one_four]
  simp only [mem_insert, mem_singleton, OfNat.one_ne_ofNat, Nat.reduceEqDiff,
    or_self, not_false_eq_true, sum_insert, sum_singleton, one_dvd, ↓reduceIte, Nat.div_one]
  ring

private theorem damped_weight_one (ε : ℝ) : pmPowerDampedRealWeight ε 1 = 1 := by
  simp [pmPowerDampedRealWeight, moebiusReal]

/-- [Corollary] Prime deletion contracts every positive residual, including the exact zero response at one. -/
theorem abs_pmPowerDamped_prime_deleted_response_le_one_of_pos {ε : ℝ}
    (hε : 0 ≤ ε) {p u : ℕ} (hp : p.Prime) (hu : 1 ≤ u) :
    |pmPowerDampedDivisorCoeff ε (p * u) - pmPowerDampedRealWeight ε (p * u) -
      pmPowerDampedRealWeight ε u| ≤ 1 := by
  by_cases h1 : u = 1
  · subst u
    rw [pmPowerDamped_prime_deleted_response ε hp 1,
      pmPowerDampedDivisorCoeff_one, damped_weight_one, sub_self, mul_zero, abs_zero]
    exact zero_le_one
  · exact abs_pmPowerDamped_prime_deleted_response_le_one hε hp (by omega)

/-- [Corollary] Two-prime deletion contracts every positive residual, including the exact unit response at one. -/
theorem abs_pmPowerDamped_two_prime_deleted_response_le_one_of_pos {ε : ℝ}
    (hε : 0 ≤ ε) {p q u : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hu : 1 ≤ u) :
    |pmPowerDampedDivisorCoeff ε (p * (q * u)) -
        pmPowerDampedRealWeight ε (p * (q * u)) -
        pmPowerDampedRealWeight ε (q * u) - pmPowerDampedRealWeight ε (p * u)| ≤ 1 := by
  by_cases h1 : u = 1
  · subst u
    rw [pmPowerDamped_two_prime_deleted_response ε hp hq hpq 1,
      pmPowerDampedDivisorCoeff_one, damped_weight_one, mul_one, mul_one]
    rw [show dampedPrimeDeletionFactor ε p 1 * dampedPrimeDeletionFactor ε q 1 +
      (1 - dampedPrimeDeletionFactor ε p 1 * dampedPrimeDeletionFactor ε q 1) = 1 by ring]
    simp only [abs_one, le_refl]
  · exact abs_pmPowerDamped_two_prime_deleted_response_le_one hε hp hq hpq (by omega)

/-- [Corollary] Without a square factor four, only the terminal, two, and three channels remain. -/
theorem sieveSeq_pmPowerDampedRealWeight_fourth_integer_band_of_not_four_dvd (ε : ℝ)
    {N k : ℕ} (hlo : 4 * N < k) (hhi : k < 5 * (N + 1)) (h4 : ¬ 4 ∣ k) :
    sieveSeq N (pmPowerDampedRealWeight ε) k =
      pmPowerDampedDivisorCoeff ε k - pmPowerDampedRealWeight ε k -
        (if 2 ∣ k then pmPowerDampedRealWeight ε (k / 2) else 0) -
        (if 3 ∣ k then pmPowerDampedRealWeight ε (k / 3) else 0) := by
  rw [sieveSeq_fourth_integer_band_eq_sum_divisors_sub hlo hhi, if_neg h4, sub_zero]
  rfl

/-- [New formulation] Radical absorption and positive-residual deletion control the entire enlarged fourth band. -/
theorem abs_sieveSeq_pmPowerDampedRealWeight_fourth_integer_band_le_one {ε : ℝ}
    (hε : 0 ≤ ε) {N k : ℕ} (hlo : 4 * N < k) (hhi : k < 5 * (N + 1)) :
    |sieveSeq N (pmPowerDampedRealWeight ε) k| ≤ 1 := by
  by_cases hN : N = 0
  · subst N
    simp [sieveSeq]
  by_cases h4 : 4 ∣ k
  · obtain ⟨u, rfl⟩ := h4
    rw [show 4 * u = 2 * (2 * u) by ring,
      sieveSeq_pmPowerDampedRealWeight_mul_of_dvd ε N (dvd_mul_right 2 u)]
    exact abs_sieveSeq_pmPowerDampedRealWeight_le_one_of_le_five_mul hε (by omega) (by omega)
  · by_cases h2 : 2 ∣ k
    · by_cases h3 : 3 ∣ k
      · obtain ⟨v, rfl⟩ := h2
        have hv : 3 ∣ v := by
          rcases Nat.prime_three.dvd_mul.mp h3 with h | h
          · have : ¬ (3 : ℕ) ∣ 2 := by omega
            exact (this h).elim
          · exact h
        obtain ⟨u, rfl⟩ := hv
        have h3' : 3 ∣ 2 * (3 * u) := ⟨2 * u, by ring⟩
        have hdiv3 : 2 * (3 * u) / 3 = 2 * u := by
          rw [show 2 * (3 * u) = 3 * (2 * u) by ring,
            Nat.mul_div_cancel_left (2 * u) (by omega : 0 < 3)]
        rw [sieveSeq_pmPowerDampedRealWeight_fourth_integer_band_of_not_four_dvd ε hlo hhi h4,
          if_pos (dvd_mul_right 2 (3 * u)), if_pos h3',
          Nat.mul_div_cancel_left (3 * u) (by omega : 0 < 2), hdiv3]
        exact abs_pmPowerDamped_two_prime_deleted_response_le_one_of_pos hε
          Nat.prime_two Nat.prime_three (by omega) (by omega)
      · obtain ⟨u, rfl⟩ := h2
        rw [sieveSeq_pmPowerDampedRealWeight_fourth_integer_band_of_not_four_dvd ε hlo hhi h4,
          if_pos (dvd_mul_right 2 u), if_neg h3, sub_zero,
          Nat.mul_div_cancel_left u (by omega : 0 < 2)]
        exact abs_pmPowerDamped_prime_deleted_response_le_one_of_pos hε Nat.prime_two (by omega)
    · by_cases h3 : 3 ∣ k
      · obtain ⟨u, rfl⟩ := h3
        rw [sieveSeq_pmPowerDampedRealWeight_fourth_integer_band_of_not_four_dvd ε hlo hhi h4,
          if_neg h2, if_pos (dvd_mul_right 3 u), sub_zero,
          Nat.mul_div_cancel_left u (by omega : 0 < 3)]
        exact abs_pmPowerDamped_prime_deleted_response_le_one_of_pos hε Nat.prime_three (by omega)
      · rw [sieveSeq_pmPowerDampedRealWeight_fourth_integer_band_of_not_four_dvd ε hlo hhi h4,
          if_neg h2, if_neg h3, sub_zero, sub_zero]
        exact abs_pmPowerDampedDivisorCoeff_sub_weight_le_one hε (by omega)

/-- [New formulation] The damped unit envelope holds at every integer endpoint strictly before 5(N+1). -/
theorem abs_sieveSeq_pmPowerDampedRealWeight_le_one_of_lt_five_succ {ε : ℝ}
    (hε : 0 ≤ ε) {N k : ℕ} (hk : 2 ≤ k) (hhi : k < 5 * (N + 1)) :
    |sieveSeq N (pmPowerDampedRealWeight ε) k| ≤ 1 := by
  by_cases hlo : k ≤ 5 * N
  · exact abs_sieveSeq_pmPowerDampedRealWeight_le_one_of_le_five_mul hε hk hlo
  · exact abs_sieveSeq_pmPowerDampedRealWeight_fourth_integer_band_le_one hε (by omega) hhi

private theorem zero_damping_weight : pmPowerDampedRealWeight 0 = moebiusReal := by
  funext d
  simp [pmPowerDampedRealWeight]

/-- [Corollary] Literal Möbius weights inherit the sharp integer envelope. -/
theorem abs_sieveSeq_moebiusReal_le_one_of_lt_five_succ {N k : ℕ}
    (hk : 2 ≤ k) (hhi : k < 5 * (N + 1)) : |sieveSeq N moebiusReal k| ≤ 1 := by
  simpa only [zero_damping_weight] using
    abs_sieveSeq_pmPowerDampedRealWeight_le_one_of_lt_five_succ (le_refl 0) hk hhi

/-- [Corollary] The four-integer additive buffer is included explicitly. -/
theorem abs_sieveSeq_pmPowerDampedRealWeight_le_one_of_le_five_add_four {ε : ℝ}
    (hε : 0 ≤ ε) {N k : ℕ} (hk : 2 ≤ k) (hhi : k ≤ 5 * N + 4) :
    |sieveSeq N (pmPowerDampedRealWeight ε) k| ≤ 1 :=
  abs_sieveSeq_pmPowerDampedRealWeight_le_one_of_lt_five_succ hε hk (by omega)

/-- [New formulation] A real additive buffer after 5N is universally admissible exactly when it is less than five. -/
theorem forall_moebiusReal_unit_envelope_iff_additive_lt_five (b : ℝ) :
    (∀ N k : ℕ, 2 ≤ k → (k : ℝ) ≤ 5 * N + b → |sieveSeq N moebiusReal k| ≤ 1) ↔
      b < 5 := by
  constructor
  · intro h
    by_contra hb
    have hb5 : 5 ≤ b := by linarith
    obtain ⟨N, k, _, hk, hs⟩ := exists_ge_five_horizon_counterexample 0
    have hkR : (k : ℝ) = 5 * N + 5 := by exact_mod_cast hk
    have he := h N k (by omega) (by linarith)
    rw [hs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2)] at he
    linarith
  · intro hb N k hk hhi
    apply abs_sieveSeq_moebiusReal_le_one_of_lt_five_succ hk
    have hr : (k : ℝ) < 5 * ((N : ℝ) + 1) := by linarith
    exact_mod_cast hr

/-- [New formulation] The same exact additive classification holds uniformly over all nonnegative damping exponents. -/
theorem forall_pmPowerDamped_unit_envelope_iff_additive_lt_five (b : ℝ) :
    (∀ ε : ℝ, 0 ≤ ε → ∀ N k : ℕ, 2 ≤ k → (k : ℝ) ≤ 5 * N + b →
      |sieveSeq N (pmPowerDampedRealWeight ε) k| ≤ 1) ↔ b < 5 := by
  constructor
  · intro h
    apply (forall_moebiusReal_unit_envelope_iff_additive_lt_five b).mp
    simpa only [zero_damping_weight] using h 0 (le_refl 0)
  · intro hb ε hε N k hk hhi
    apply abs_sieveSeq_pmPowerDampedRealWeight_le_one_of_lt_five_succ hε hk
    have hr : (k : ℝ) < 5 * ((N : ℝ) + 1) := by linarith
    exact_mod_cast hr

/-- [Corollary] Four is the largest universal natural additive buffer for Möbius responses. -/
theorem forall_moebiusReal_unit_envelope_iff_nat_buffer_le_four (b : ℕ) :
    (∀ N k : ℕ, 2 ≤ k → k ≤ 5 * N + b → |sieveSeq N moebiusReal k| ≤ 1) ↔
      b ≤ 4 := by
  constructor
  · intro h
    by_contra hb
    obtain ⟨N, k, _, hk, hs⟩ := exists_ge_five_horizon_counterexample 0
    have he := h N k (by omega) (by omega)
    rw [hs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2)] at he
    linarith
  · intro hb N k hk hhi
    exact abs_sieveSeq_moebiusReal_le_one_of_lt_five_succ hk (by omega)

/-- [Corollary] Four is the largest universal natural buffer for the whole damped family. -/
theorem forall_pmPowerDamped_unit_envelope_iff_nat_buffer_le_four (b : ℕ) :
    (∀ ε : ℝ, 0 ≤ ε → ∀ N k : ℕ, 2 ≤ k → k ≤ 5 * N + b →
      |sieveSeq N (pmPowerDampedRealWeight ε) k| ≤ 1) ↔ b ≤ 4 := by
  constructor
  · intro h
    apply (forall_moebiusReal_unit_envelope_iff_nat_buffer_le_four b).mp
    simpa only [zero_damping_weight] using h 0 (le_refl 0)
  · intro hb ε hε N k hk hhi
    exact abs_sieveSeq_pmPowerDampedRealWeight_le_one_of_lt_five_succ hε hk (by omega)

/-- [New formulation] Each symbolic prime-family counterexample is the first offending endpoint at its horizon. -/
theorem moebiusReal_counterfamily_first_unit_envelope_failure {p : ℕ}
    (hp : p.Prime) (h5 : 5 < p) :
    (∀ k : ℕ, 2 ≤ k → k < 30 * p → |sieveSeq (6 * p - 1) moebiusReal k| ≤ 1) ∧
      sieveSeq (6 * p - 1) moebiusReal (30 * p) = 2 := by
  refine ⟨?_, sieveSeq_moebiusReal_five_horizon_counterfamily hp h5⟩
  intro k hk hkp
  exact abs_sieveSeq_moebiusReal_le_one_of_lt_five_succ hk (by omega)

/-- [New formulation] Arbitrarily large horizons attain the earliest possible unit-envelope failure. -/
theorem exists_ge_first_unit_envelope_failure_at_five_succ (B : ℕ) :
    ∃ N k : ℕ, B ≤ N ∧ k = 5 * (N + 1) ∧ sieveSeq N moebiusReal k = 2 ∧
      ∀ j : ℕ, 2 ≤ j → j < k → |sieveSeq N moebiusReal j| ≤ 1 := by
  obtain ⟨N, k, hN, hk, hs⟩ := exists_ge_five_horizon_counterexample B
  refine ⟨N, k, hN, by omega, hs, ?_⟩
  intro j hj hjk
  exact abs_sieveSeq_moebiusReal_le_one_of_lt_five_succ hj (by omega)

/-- [Corollary] The sharp integer envelope certifies entire radical fibers, including zero horizon. -/
theorem abs_sieveSeq_pmPowerDampedRealWeight_le_one_of_radical_lt_five_succ
    {ε : ℝ} (hε : 0 ≤ ε) {N k : ℕ}
    (hrN : horizonRadicalState N k < 5 * (N + 1)) :
    |sieveSeq N (pmPowerDampedRealWeight ε) k| ≤ 1 := by
  by_cases hN : N = 0
  · subst N
    simp [sieveSeq]
  rw [← sieveSeq_horizonRadicalState N k
    (pmPowerDampedRealWeight_eq_zero_of_not_squarefree ε)]
  have hr := horizonRadicalState_pos N k
  by_cases hr1 : horizonRadicalState N k = 1
  · rw [hr1, sieveSeq_pmPowerDampedRealWeight_eq_pmPowerDampedDivisorCoeff
      le_rfl (by omega : 1 ≤ N), pmPowerDampedDivisorCoeff_one, abs_one]
  · exact abs_sieveSeq_pmPowerDampedRealWeight_le_one_of_lt_five_succ hε (by omega) hrN

/-- [New formulation] Any response beyond the unit envelope needs a radical state of size at least 5(N+1). -/
theorem five_succ_le_radical_of_pmPowerDamped_response_gt_one
    {ε : ℝ} (hε : 0 ≤ ε) {N k : ℕ}
    (h : 1 < |sieveSeq N (pmPowerDampedRealWeight ε) k|) :
    5 * (N + 1) ≤ horizonRadicalState N k := by
  by_contra hn
  have he := abs_sieveSeq_pmPowerDampedRealWeight_le_one_of_radical_lt_five_succ
    hε (by omega : horizonRadicalState N k < 5 * (N + 1))
  linarith

/-- [Corollary] All positive powers of bases in the sharpened interval retain the unit envelope. -/
theorem abs_sieveSeq_pmPowerDampedRealWeight_pow_lt_five_succ {ε : ℝ}
    (hε : 0 ≤ ε) {N k m : ℕ} (hk : 2 ≤ k) (hhi : k < 5 * (N + 1)) (hm : 1 ≤ m) :
    |sieveSeq N (pmPowerDampedRealWeight ε) (k ^ m)| ≤ 1 := by
  rw [sieveSeq_pmPowerDampedRealWeight_pow ε N k hm]
  exact abs_sieveSeq_pmPowerDampedRealWeight_le_one_of_lt_five_succ hε hk hhi

/-- [New formulation] Rough-start windows dissipate on every radical fiber certified by the sharp integer cutoff. -/
theorem shortWindowRenormalizedDefect_pmPowerDampedRealWeight_rough_start_radical_five_succ
    {ε : ℝ} (hε : 0 ≤ ε) {N M₀ M : ℕ}
    (hstart : IsTransHorizonRough N (M₀ + 1))
    (hrN : horizonRadicalState N (M₀ + M + 1) < 5 * (N + 1)) :
    2 * shortWindowRenormalizedDefect N M₀ M (pmPowerDampedRealWeight ε) ≤
        -shortWindowDirichletEnergy N M₀ M (pmPowerDampedRealWeight ε) ∧
      shortWindowRenormalizedDefect N M₀ M (pmPowerDampedRealWeight ε) ≤ 0 := by
  by_cases hN : N = 0
  · subst N
    simp [shortWindowRenormalizedDefect, shortWindowDirichletEnergy,
      sieveRenormalizedPrefixDefect_eq_sum_mul_addDiff, sieveSeq]
  have hpol := two_mul_shortWindowRenormalizedDefect_eq N M₀ M (pmPowerDampedRealWeight ε)
  have hinit : sieveSeq N (pmPowerDampedRealWeight ε) (M₀ + 1) = 1 := by
    rw [sieveSeq_of_isTransHorizonRough hstart,
      sieveSeq_pmPowerDampedRealWeight_eq_pmPowerDampedDivisorCoeff
        le_rfl (by omega : 1 ≤ N), pmPowerDampedDivisorCoeff_one]
  have hsq := (sq_le_one_iff_abs_le_one _).mpr
    (abs_sieveSeq_pmPowerDampedRealWeight_le_one_of_radical_lt_five_succ hε hrN)
  rw [hinit, one_pow] at hpol
  have henergy : 0 ≤ shortWindowDirichletEnergy N M₀ M (pmPowerDampedRealWeight ε) :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  exact ⟨by linarith, by linarith⟩

/-- [Corollary] Every rough-start window ending before 5(N+1) has the quantitative energy bound. -/
theorem shortWindowRenormalizedDefect_pmPowerDampedRealWeight_rough_start_five_succ
    {ε : ℝ} (hε : 0 ≤ ε) {N M₀ M : ℕ}
    (hstart : IsTransHorizonRough N (M₀ + 1)) (hhi : M₀ + M + 1 < 5 * (N + 1)) :
    2 * shortWindowRenormalizedDefect N M₀ M (pmPowerDampedRealWeight ε) ≤
        -shortWindowDirichletEnergy N M₀ M (pmPowerDampedRealWeight ε) ∧
      shortWindowRenormalizedDefect N M₀ M (pmPowerDampedRealWeight ε) ≤ 0 := by
  exact shortWindowRenormalizedDefect_pmPowerDampedRealWeight_rough_start_radical_five_succ
    hε hstart (lt_of_le_of_lt (Nat.le_of_dvd (by omega)
      (horizonRadicalState_dvd N (M₀ + M + 1))) hhi)

/-- [Corollary] Every certified radical prefix dissipates, including zero horizon and zero-length prefixes. -/
theorem sieveRenormalizedPrefixDefect_pmPowerDampedRealWeight_radical_five_succ_bound
    {ε : ℝ} (hε : 0 ≤ ε) {N M : ℕ}
    (hrN : horizonRadicalState N (M + 1) < 5 * (N + 1)) :
    2 * sieveRenormalizedPrefixDefect N M (pmPowerDampedRealWeight ε) ≤
        -(∑ k ∈ Icc 1 M, (sieveSeq N (pmPowerDampedRealWeight ε) (k + 1) -
          sieveSeq N (pmPowerDampedRealWeight ε) k) ^ (2 : ℕ)) ∧
      sieveRenormalizedPrefixDefect N M (pmPowerDampedRealWeight ε) ≤ 0 := by
  have h := shortWindowRenormalizedDefect_pmPowerDampedRealWeight_rough_start_radical_five_succ
    (M₀ := 0) (M := M) hε (isTransHorizonRough_one N) (by simpa using hrN)
  have hz : sieveRenormalizedPrefixDefect N 0 (pmPowerDampedRealWeight ε) = 0 := by
    simp [sieveRenormalizedPrefixDefect_eq_sum_mul_addDiff]
  simpa only [shortWindowRenormalizedDefect, shortWindowDirichletEnergy,
    zero_add, hz, sub_zero] using h

/-- [Corollary] The whole sharpened prefix interval satisfies 2D≤-E≤0. -/
theorem sieveRenormalizedPrefixDefect_pmPowerDampedRealWeight_five_succ_bound
    {ε : ℝ} (hε : 0 ≤ ε) {N M : ℕ} (hhi : M + 1 < 5 * (N + 1)) :
    2 * sieveRenormalizedPrefixDefect N M (pmPowerDampedRealWeight ε) ≤
        -(∑ k ∈ Icc 1 M, (sieveSeq N (pmPowerDampedRealWeight ε) (k + 1) -
          sieveSeq N (pmPowerDampedRealWeight ε) k) ^ (2 : ℕ)) ∧
      sieveRenormalizedPrefixDefect N M (pmPowerDampedRealWeight ε) ≤ 0 := by
  exact sieveRenormalizedPrefixDefect_pmPowerDampedRealWeight_radical_five_succ_bound
    hε (lt_of_le_of_lt (Nat.le_of_dvd (by omega) (horizonRadicalState_dvd N (M + 1))) hhi)

/-- [Corollary] The sharp base interval generates arbitrarily distant dissipative power checkpoints. -/
theorem sieveRenormalizedPrefixDefect_pmPowerDampedRealWeight_pow_five_succ_bound
    {ε : ℝ} (hε : 0 ≤ ε) {N k m : ℕ} (hk : 2 ≤ k)
    (hhi : k < 5 * (N + 1)) (hm : 1 ≤ m) :
    2 * sieveRenormalizedPrefixDefect N (k ^ m - 1) (pmPowerDampedRealWeight ε) ≤
        -(∑ j ∈ Icc 1 (k ^ m - 1), (sieveSeq N (pmPowerDampedRealWeight ε) (j + 1) -
          sieveSeq N (pmPowerDampedRealWeight ε) j) ^ (2 : ℕ)) ∧
      sieveRenormalizedPrefixDefect N (k ^ m - 1) (pmPowerDampedRealWeight ε) ≤ 0 := by
  have hkm : k ≤ k ^ m := by simpa using pow_le_pow_right₀ (by omega : 1 ≤ k) hm
  apply sieveRenormalizedPrefixDefect_pmPowerDampedRealWeight_radical_five_succ_bound hε
  rw [Nat.sub_add_cancel (by omega : 1 ≤ k ^ m), horizonRadicalState_pow N k hm]
  exact lt_of_le_of_lt (Nat.le_of_dvd (by omega) (horizonRadicalState_dvd N k)) hhi

/-- [Corollary] Literal Möbius prefixes are nonpositive before the sharp integer cutoff. -/
theorem sieveRenormalizedPrefixDefect_moebiusReal_five_succ_nonpos {N M : ℕ}
    (hhi : M + 1 < 5 * (N + 1)) : sieveRenormalizedPrefixDefect N M moebiusReal ≤ 0 := by
  simpa only [zero_damping_weight] using
    (sieveRenormalizedPrefixDefect_pmPowerDampedRealWeight_five_succ_bound (le_refl 0) hhi).2

/-- [Corollary] Literal Möbius weights inherit all certified power checkpoints. -/
theorem sieveRenormalizedPrefixDefect_moebiusReal_pow_five_succ_nonpos {N k m : ℕ}
    (hk : 2 ≤ k) (hhi : k < 5 * (N + 1)) (hm : 1 ≤ m) :
    sieveRenormalizedPrefixDefect N (k ^ m - 1) moebiusReal ≤ 0 := by
  simpa only [zero_damping_weight] using
    (sieveRenormalizedPrefixDefect_pmPowerDampedRealWeight_pow_five_succ_bound
      (le_refl 0) hk hhi hm).2

/-- [Corollary] Literal Möbius defects are nonpositive on every newly certified radical fiber. -/
theorem sieveRenormalizedPrefixDefect_moebiusReal_radical_five_succ_nonpos {N M : ℕ}
    (hrN : horizonRadicalState N (M + 1) < 5 * (N + 1)) :
    sieveRenormalizedPrefixDefect N M moebiusReal ≤ 0 := by
  simpa only [zero_damping_weight] using
    (sieveRenormalizedPrefixDefect_pmPowerDampedRealWeight_radical_five_succ_bound
      (le_refl 0) hrN).2

end
end GaloisForLFunctions.TransHorizonIncidenceMechanics
