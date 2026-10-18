import GaloisForLFunctions.TransHorizonIncidenceMechanics.TwoPrimeDeletionAndFullThirdBandEnvelope

/-!
# Complete fourth band and sharp universal five-horizon boundary

Classical baseline: complementary-divisor splitting, squarefree radical invariance,
prime-factor deletion of Möbius divisor sums, and discrete polarization.
The truncated sum is exactly D(n;a) of Helfgott–Thompson, Proposition 3.2:
https://doi.org/10.1007/s40993-022-00408-8. The divisor-observation and finite
shifted-correlation frameworks are [TH10] https://arxiv.org/abs/1009.5281 and
[CMS16] https://arxiv.org/abs/1612.03136.

Equivalent classical formulation: for every ε≥0, |Σ_{d∣k,d≤N} μ(d)d^(-ε)|≤1
whenever 2≤k≤5N. In the fourth band, square-factor-four endpoints compress to
half-sized observations; the remaining endpoints use two-prime convex deletion.
The uniform complementary-quotient formula applies to every horizon band.

For every prime p>5, N=6p-1 and k=30p=5N+5 give the literal Möbius response 2.
Unbounded primes prove that the universal unit envelope on 2≤k≤C N holds exactly
for real C≤5, both for Möbius weights and uniformly over all ε≥0.
This is an obstruction to the endpoint-unit-envelope method, not a claim of
positive renormalized defects beyond 5N. The positive survivor is the complete
5N envelope, together with its radical/power and rough-start energy certificates.

Classification: New formulation; constituent standard consequences are labeled.
No external novelty or exhaustive literature-priority claim.
-/

open Finset ArithmeticFunction
open GaloisForLFunctions.BiScaleUncertainty GaloisForLFunctions.BezoutValuationIncidence
open RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics
noncomputable section
set_option autoImplicit false

/-- [Known] In a complete horizon band, every visible complementary quotient is active. -/
theorem filter_Icc_complementary_quotients_of_band {B N k : ℕ} (hlo : B * N < k) :
    (Icc 1 B).filter (fun q => q ∣ k ∧ N < k / q) =
      (Icc 1 B).filter (fun q => q ∣ k) := by
  ext q
  simp only [mem_filter, mem_Icc]
  constructor
  · rintro ⟨hq, hqk, _⟩
    exact ⟨hq, hqk⟩
  · rintro ⟨⟨hq1, hqB⟩, hqk⟩
    refine ⟨⟨hq1, hqB⟩, hqk, ?_⟩
    obtain ⟨d, hkd⟩ := hqk
    rw [hkd, Nat.mul_div_cancel_left d (by omega : 0 < q)]
    nlinarith

/-- [New formulation] A uniform finite-band normal form for arbitrary weights. -/
theorem sieveSeq_band_eq_sum_divisors_sub_quotients {B N k : ℕ}
    (hlo : B * N < k) (hhi : k ≤ (B + 1) * N) (c : ℕ → ℝ) :
    sieveSeq N c k = (∑ d ∈ k.divisors, c d) -
      ∑ q ∈ Icc 1 B, if q ∣ k then c (k / q) else 0 := by
  rw [sieveSeq_eq_sum_divisors_sub_complementaryQuotientTail N (by omega) c,
    complementaryQuotientTail_eq_sum_Icc_of_le_mul hhi c,
    filter_Icc_complementary_quotients_of_band hlo, sum_filter]

private theorem Icc_one_four : Icc (1 : ℕ) 4 = {1, 2, 3, 4} := by
  ext q
  simp only [mem_Icc, mem_insert, mem_singleton]
  omega

private theorem Icc_one_five : Icc (1 : ℕ) 5 = {1, 2, 3, 4, 5} := by
  ext q
  simp only [mem_Icc, mem_insert, mem_singleton]
  omega

/-- [Corollary] The fourth band contains exactly the four small quotient channels. -/
theorem sieveSeq_fourth_band_eq_sum_divisors_sub {N k : ℕ}
    (hlo : 4 * N < k) (hhi : k ≤ 5 * N) (c : ℕ → ℝ) :
    sieveSeq N c k = (∑ d ∈ k.divisors, c d) - c k -
      (if 2 ∣ k then c (k / 2) else 0) - (if 3 ∣ k then c (k / 3) else 0) -
      (if 4 ∣ k then c (k / 4) else 0) := by
  rw [sieveSeq_band_eq_sum_divisors_sub_quotients hlo hhi c, Icc_one_four]
  simp only [mem_insert, mem_singleton, OfNat.one_ne_ofNat, Nat.reduceEqDiff,
    or_self, not_false_eq_true, sum_insert, sum_singleton, one_dvd, ↓reduceIte, Nat.div_one]
  ring

/-- [Corollary] The fifth band adds the prime-five quotient channel. -/
theorem sieveSeq_fifth_band_eq_sum_divisors_sub {N k : ℕ}
    (hlo : 5 * N < k) (hhi : k ≤ 6 * N) (c : ℕ → ℝ) :
    sieveSeq N c k = (∑ d ∈ k.divisors, c d) - c k -
      (if 2 ∣ k then c (k / 2) else 0) - (if 3 ∣ k then c (k / 3) else 0) -
      (if 4 ∣ k then c (k / 4) else 0) - (if 5 ∣ k then c (k / 5) else 0) := by
  rw [sieveSeq_band_eq_sum_divisors_sub_quotients hlo hhi c, Icc_one_five]
  simp only [mem_insert, mem_singleton, OfNat.one_ne_ofNat, Nat.reduceEqDiff,
    or_self, not_false_eq_true, sum_insert, sum_singleton, one_dvd, ↓reduceIte, Nat.div_one]
  ring

/-- [Corollary] Without a square factor four, the fourth-band response has the
same three deletion channels as the third band. -/
theorem sieveSeq_pmPowerDampedRealWeight_fourth_band_of_not_four_dvd (ε : ℝ)
    {N k : ℕ} (hlo : 4 * N < k) (hhi : k ≤ 5 * N) (h4 : ¬ 4 ∣ k) :
    sieveSeq N (pmPowerDampedRealWeight ε) k =
      pmPowerDampedDivisorCoeff ε k - pmPowerDampedRealWeight ε k -
        (if 2 ∣ k then pmPowerDampedRealWeight ε (k / 2) else 0) -
        (if 3 ∣ k then pmPowerDampedRealWeight ε (k / 3) else 0) := by
  rw [sieveSeq_fourth_band_eq_sum_divisors_sub hlo hhi, if_neg h4, sub_zero]
  rfl

/-- [New formulation] Divisor absorption and two-prime convexity close every
endpoint in the fourth band. -/
theorem abs_sieveSeq_pmPowerDampedRealWeight_fourth_band_le_one {ε : ℝ}
    (hε : 0 ≤ ε) {N k : ℕ} (hlo : 4 * N < k) (hhi : k ≤ 5 * N) :
    |sieveSeq N (pmPowerDampedRealWeight ε) k| ≤ 1 := by
  by_cases h4 : 4 ∣ k
  · obtain ⟨u, rfl⟩ := h4
    rw [show 4 * u = 2 * (2 * u) by ring,
      sieveSeq_pmPowerDampedRealWeight_mul_of_dvd ε N (dvd_mul_right 2 u)]
    exact abs_sieveSeq_pmPowerDampedRealWeight_le_one_of_le_four_mul hε (by omega) (by omega)
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
        rw [sieveSeq_pmPowerDampedRealWeight_fourth_band_of_not_four_dvd ε hlo hhi h4,
          if_pos (dvd_mul_right 2 (3 * u)), if_pos h3',
          Nat.mul_div_cancel_left (3 * u) (by omega : 0 < 2), hdiv3]
        exact abs_pmPowerDamped_two_prime_deleted_response_le_one hε
          Nat.prime_two Nat.prime_three (by omega) (by omega)
      · obtain ⟨u, rfl⟩ := h2
        rw [sieveSeq_pmPowerDampedRealWeight_fourth_band_of_not_four_dvd ε hlo hhi h4,
          if_pos (dvd_mul_right 2 u), if_neg h3, sub_zero,
          Nat.mul_div_cancel_left u (by omega : 0 < 2)]
        exact abs_pmPowerDamped_prime_deleted_response_le_one hε Nat.prime_two (by omega)
    · by_cases h3 : 3 ∣ k
      · obtain ⟨u, rfl⟩ := h3
        rw [sieveSeq_pmPowerDampedRealWeight_fourth_band_of_not_four_dvd ε hlo hhi h4,
          if_neg h2, if_pos (dvd_mul_right 3 u), sub_zero,
          Nat.mul_div_cancel_left u (by omega : 0 < 3)]
        exact abs_pmPowerDamped_prime_deleted_response_le_one hε Nat.prime_three (by omega)
      · rw [sieveSeq_pmPowerDampedRealWeight_fourth_band_of_not_four_dvd ε hlo hhi h4,
          if_neg h2, if_neg h3, sub_zero, sub_zero]
        exact abs_pmPowerDampedDivisorCoeff_sub_weight_le_one hε (by omega)

/-- [New formulation] The universal damped unit envelope extends through 5N. -/
theorem abs_sieveSeq_pmPowerDampedRealWeight_le_one_of_le_five_mul {ε : ℝ}
    (hε : 0 ≤ ε) {N k : ℕ} (hk : 2 ≤ k) (hhi : k ≤ 5 * N) :
    |sieveSeq N (pmPowerDampedRealWeight ε) k| ≤ 1 := by
  by_cases hlo : k ≤ 4 * N
  · exact abs_sieveSeq_pmPowerDampedRealWeight_le_one_of_le_four_mul hε hk hlo
  · exact abs_sieveSeq_pmPowerDampedRealWeight_fourth_band_le_one hε (by omega) hhi


private theorem zero_damping_weight : pmPowerDampedRealWeight 0 = moebiusReal := by
  funext d
  simp [pmPowerDampedRealWeight]

private theorem moebius_prime_mul_of_not_dvd {p u : ℕ} (hp : p.Prime) (hu : ¬ p ∣ u) :
    moebiusReal (p * u) = -moebiusReal u := by
  have h := pmPowerDampedRealWeight_prime_mul_switch 0 hp u
  simpa [zero_damping_weight, hu] using h

/-- [Corollary] Literal Möbius weights satisfy the full 5N envelope. -/
theorem abs_sieveSeq_moebiusReal_le_one_of_le_five_mul {N k : ℕ}
    (hk : 2 ≤ k) (hhi : k ≤ 5 * N) : |sieveSeq N moebiusReal k| ≤ 1 := by
  simpa only [zero_damping_weight] using
    abs_sieveSeq_pmPowerDampedRealWeight_le_one_of_le_five_mul (le_refl 0) hk hhi

/-- [New formulation] A symbolic four-prime family has response two only five
integer steps past 5N; no numerical search or fixed-horizon evaluation is used. -/
theorem sieveSeq_moebiusReal_five_horizon_counterfamily {p : ℕ}
    (hp : p.Prime) (h5 : 5 < p) :
    sieveSeq (6 * p - 1) moebiusReal (30 * p) = 2 := by
  have h2p : ¬ 2 ∣ p := by
    intro h
    rcases (Nat.dvd_prime hp).mp h with h | h <;> omega
  have h3p : ¬ 3 ∣ p := by
    intro h
    rcases (Nat.dvd_prime hp).mp h with h | h <;> omega
  have h5p : ¬ 5 ∣ p := by
    intro h
    rcases (Nat.dvd_prime hp).mp h with h | h <;> omega
  have h23 : ¬ (2 : ℕ) ∣ 3 := by omega
  have h25 : ¬ (2 : ℕ) ∣ 5 := by omega
  have h35 : ¬ (3 : ℕ) ∣ 5 := by omega
  have h2_3p : ¬ 2 ∣ 3 * p := by simpa only [Nat.prime_two.dvd_mul, h23, false_or] using h2p
  have h2_5p : ¬ 2 ∣ 5 * p := by simpa only [Nat.prime_two.dvd_mul, h25, false_or] using h2p
  have h3_5p : ¬ 3 ∣ 5 * p := by simpa only [Nat.prime_three.dvd_mul, h35, false_or] using h3p
  have h2_15p : ¬ 2 ∣ 3 * (5 * p) := by
    simpa only [Nat.prime_two.dvd_mul, h23, false_or] using h2_5p
  have hpμ : moebiusReal p = -1 := by simp [moebiusReal, moebius_apply_prime hp]
  have h5μ : moebiusReal (5 * p) = 1 := by
    rw [moebius_prime_mul_of_not_dvd Nat.prime_five h5p, hpμ]
    ring
  have h3μ : moebiusReal (3 * p) = 1 := by
    rw [moebius_prime_mul_of_not_dvd Nat.prime_three h3p, hpμ]
    ring
  have h15μ : moebiusReal (15 * p) = -1 := by
    rw [show 15 * p = 3 * (5 * p) by ring,
      moebius_prime_mul_of_not_dvd Nat.prime_three h3_5p, h5μ]
  have h10μ : moebiusReal (10 * p) = -1 := by
    rw [show 10 * p = 2 * (5 * p) by ring,
      moebius_prime_mul_of_not_dvd Nat.prime_two h2_5p, h5μ]
  have h6μ : moebiusReal (6 * p) = -1 := by
    rw [show 6 * p = 2 * (3 * p) by ring,
      moebius_prime_mul_of_not_dvd Nat.prime_two h2_3p, h3μ]
  have h30μ : moebiusReal (30 * p) = 1 := by
    rw [show 30 * p = 2 * (3 * (5 * p)) by ring,
      moebius_prime_mul_of_not_dvd Nat.prime_two h2_15p,
      ← show 15 * p = 3 * (5 * p) by ring, h15μ]
    ring
  have h2 : 2 ∣ 30 * p := ⟨15 * p, by ring⟩
  have h3 : 3 ∣ 30 * p := ⟨10 * p, by ring⟩
  have h4 : ¬ 4 ∣ 30 * p := by omega
  have h5d : 5 ∣ 30 * p := ⟨6 * p, by ring⟩
  rw [sieveSeq_fifth_band_eq_sum_divisors_sub (by omega) (by omega),
    sum_divisors_moebiusReal_eq_ite_one (by omega), if_neg (by omega : 30 * p ≠ 1),
    if_pos h2, if_pos h3, if_neg h4, if_pos h5d,
    show 30 * p / 2 = 15 * p by omega, show 30 * p / 3 = 10 * p by omega,
    show 30 * p / 5 = 6 * p by omega, h30μ, h15μ, h10μ, h6μ]
  ring

/-- [Corollary] Every positive power of a counterfamily endpoint retains response two. -/
theorem sieveSeq_moebiusReal_five_horizon_counterfamily_pow {p m : ℕ}
    (hp : p.Prime) (h5 : 5 < p) (hm : 1 ≤ m) :
    sieveSeq (6 * p - 1) moebiusReal ((30 * p) ^ m) = 2 := by
  rw [sieveSeq_moebiusReal_pow _ _ hm,
    sieveSeq_moebiusReal_five_horizon_counterfamily hp h5]

/-- [New formulation] The obstruction occurs at arbitrarily large horizons,
always at the exact additive offset k=5N+5. -/
theorem exists_ge_five_horizon_counterexample (B : ℕ) :
    ∃ N k : ℕ, B ≤ N ∧ k = 5 * N + 5 ∧ sieveSeq N moebiusReal k = 2 := by
  obtain ⟨p, hBp, hp⟩ := Nat.exists_infinite_primes (B + 6)
  exact ⟨6 * p - 1, 30 * p, by omega, by omega,
    sieveSeq_moebiusReal_five_horizon_counterfamily hp (by omega)⟩

/-- [New formulation] Five is exactly the largest universal real horizon ratio
for the unit envelope of truncated Möbius divisor sums. -/
theorem forall_moebiusReal_unit_envelope_iff_ratio_le_five (C : ℝ) :
    (∀ N k : ℕ, 2 ≤ k → (k : ℝ) ≤ C * N → |sieveSeq N moebiusReal k| ≤ 1) ↔ C ≤ 5 := by
  constructor
  · intro h
    by_contra hC
    have hpos : 0 < C - 5 := by linarith
    obtain ⟨B, hB⟩ := exists_nat_gt (5 / (C - 5))
    obtain ⟨N, k, hN, hk, hs⟩ := exists_ge_five_horizon_counterexample B
    have hBN : (B : ℝ) ≤ N := by exact_mod_cast hN
    have hprod : 5 < (C - 5) * N := by
      have := (div_lt_iff₀ hpos).mp (lt_of_lt_of_le hB hBN)
      nlinarith
    have hkR : (k : ℝ) = 5 * N + 5 := by exact_mod_cast hk
    have hb := h N k (by omega) (by nlinarith)
    rw [hs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2)] at hb
    linarith
  · intro hC N k hk hhi
    have hkR : (k : ℝ) ≤ 5 * N :=
      hhi.trans (mul_le_mul_of_nonneg_right hC (Nat.cast_nonneg N))
    exact abs_sieveSeq_moebiusReal_le_one_of_le_five_mul hk (by exact_mod_cast hkR)

/-- [New formulation] The same sharp ratio classifies the entire family of
nonnegative damping parameters, with zero damping supplying necessity. -/
theorem forall_pmPowerDamped_unit_envelope_iff_ratio_le_five (C : ℝ) :
    (∀ (ε : ℝ) (N k : ℕ), 0 ≤ ε → 2 ≤ k → (k : ℝ) ≤ C * N →
      |sieveSeq N (pmPowerDampedRealWeight ε) k| ≤ 1) ↔ C ≤ 5 := by
  constructor
  · intro h
    apply (forall_moebiusReal_unit_envelope_iff_ratio_le_five C).mp
    intro N k hk hhi
    simpa only [zero_damping_weight] using h 0 N k (le_refl 0) hk hhi
  · intro hC ε N k hε hk hhi
    have hkR : (k : ℝ) ≤ 5 * N :=
      hhi.trans (mul_le_mul_of_nonneg_right hC (Nat.cast_nonneg N))
    exact abs_sieveSeq_pmPowerDampedRealWeight_le_one_of_le_five_mul hε hk
      (by exact_mod_cast hkR)


/-- [Corollary] The 5N certificate depends only on the horizon-radical state. -/
theorem abs_sieveSeq_pmPowerDampedRealWeight_le_one_of_radical_le_five_mul
    {ε : ℝ} (hε : 0 ≤ ε) {N k : ℕ}
    (hrN : horizonRadicalState N k ≤ 5 * N) :
    |sieveSeq N (pmPowerDampedRealWeight ε) k| ≤ 1 := by
  rw [← sieveSeq_horizonRadicalState N k
    (pmPowerDampedRealWeight_eq_zero_of_not_squarefree ε)]
  have hr := horizonRadicalState_pos N k
  by_cases hr1 : horizonRadicalState N k = 1
  · rw [hr1, sieveSeq_pmPowerDampedRealWeight_eq_pmPowerDampedDivisorCoeff
      le_rfl (by omega : 1 ≤ N), pmPowerDampedDivisorCoeff_one, abs_one]
  · exact abs_sieveSeq_pmPowerDampedRealWeight_le_one_of_le_five_mul hε (by omega) hrN

/-- [Corollary] All positive powers of bases in [2,5N] inherit the unit envelope. -/
theorem abs_sieveSeq_pmPowerDampedRealWeight_pow_le_five_mul {ε : ℝ}
    (hε : 0 ≤ ε) {N k m : ℕ} (hk : 2 ≤ k) (hhi : k ≤ 5 * N) (hm : 1 ≤ m) :
    |sieveSeq N (pmPowerDampedRealWeight ε) (k ^ m)| ≤ 1 := by
  rw [sieveSeq_pmPowerDampedRealWeight_pow ε N k hm]
  exact abs_sieveSeq_pmPowerDampedRealWeight_le_one_of_le_five_mul hε hk hhi

/-- [New formulation] Rough-start windows dissipate whenever the right endpoint's
radical representative belongs to the complete 5N envelope. -/
theorem shortWindowRenormalizedDefect_pmPowerDampedRealWeight_rough_start_radical_five_mul
    {ε : ℝ} (hε : 0 ≤ ε) {N M₀ M : ℕ}
    (hstart : IsTransHorizonRough N (M₀ + 1))
    (hrN : horizonRadicalState N (M₀ + M + 1) ≤ 5 * N) :
    2 * shortWindowRenormalizedDefect N M₀ M (pmPowerDampedRealWeight ε) ≤
        -shortWindowDirichletEnergy N M₀ M (pmPowerDampedRealWeight ε) ∧
      shortWindowRenormalizedDefect N M₀ M (pmPowerDampedRealWeight ε) ≤ 0 := by
  have hr := horizonRadicalState_pos N (M₀ + M + 1)
  have hpol := two_mul_shortWindowRenormalizedDefect_eq N M₀ M (pmPowerDampedRealWeight ε)
  have hinit : sieveSeq N (pmPowerDampedRealWeight ε) (M₀ + 1) = 1 := by
    rw [sieveSeq_of_isTransHorizonRough hstart,
      sieveSeq_pmPowerDampedRealWeight_eq_pmPowerDampedDivisorCoeff
        le_rfl (by omega : 1 ≤ N), pmPowerDampedDivisorCoeff_one]
  have hsq := (sq_le_one_iff_abs_le_one _).mpr
    (abs_sieveSeq_pmPowerDampedRealWeight_le_one_of_radical_le_five_mul hε hrN)
  rw [hinit, one_pow] at hpol
  have henergy : 0 ≤ shortWindowDirichletEnergy N M₀ M (pmPowerDampedRealWeight ε) :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  exact ⟨by linarith, by linarith⟩

/-- [Corollary] Every rough-start short window ending by 5N has nonpositive defect. -/
theorem shortWindowRenormalizedDefect_pmPowerDampedRealWeight_rough_start_full_five_mul
    {ε : ℝ} (hε : 0 ≤ ε) {N M₀ M : ℕ}
    (hstart : IsTransHorizonRough N (M₀ + 1)) (hhi : M₀ + M + 1 ≤ 5 * N) :
    2 * shortWindowRenormalizedDefect N M₀ M (pmPowerDampedRealWeight ε) ≤
        -shortWindowDirichletEnergy N M₀ M (pmPowerDampedRealWeight ε) ∧
      shortWindowRenormalizedDefect N M₀ M (pmPowerDampedRealWeight ε) ≤ 0 := by
  exact shortWindowRenormalizedDefect_pmPowerDampedRealWeight_rough_start_radical_five_mul
    hε hstart ((Nat.le_of_dvd (by omega)
      (horizonRadicalState_dvd N (M₀ + M + 1))).trans hhi)

/-- [New formulation] Every certified radical prefix has the full energy bound,
including the zero-length prefix. -/
theorem sieveRenormalizedPrefixDefect_pmPowerDampedRealWeight_radical_five_mul_bound
    {ε : ℝ} (hε : 0 ≤ ε) {N M : ℕ}
    (hrN : horizonRadicalState N (M + 1) ≤ 5 * N) :
    2 * sieveRenormalizedPrefixDefect N M (pmPowerDampedRealWeight ε) ≤
        -(∑ k ∈ Icc 1 M, (sieveSeq N (pmPowerDampedRealWeight ε) (k + 1) -
          sieveSeq N (pmPowerDampedRealWeight ε) k) ^ (2 : ℕ)) ∧
      sieveRenormalizedPrefixDefect N M (pmPowerDampedRealWeight ε) ≤ 0 := by
  have h := shortWindowRenormalizedDefect_pmPowerDampedRealWeight_rough_start_radical_five_mul
    (M₀ := 0) (M := M) hε (isTransHorizonRough_one N) (by simpa using hrN)
  have hz : sieveRenormalizedPrefixDefect N 0 (pmPowerDampedRealWeight ε) = 0 := by
    simp [sieveRenormalizedPrefixDefect_eq_sum_mul_addDiff]
  simpa only [shortWindowRenormalizedDefect, shortWindowDirichletEnergy,
    zero_add, hz, sub_zero] using h

/-- [Corollary] The entire prefix range through 5N has quantitative dissipation. -/
theorem sieveRenormalizedPrefixDefect_pmPowerDampedRealWeight_full_five_mul_bound
    {ε : ℝ} (hε : 0 ≤ ε) {N M : ℕ} (hhi : M + 1 ≤ 5 * N) :
    2 * sieveRenormalizedPrefixDefect N M (pmPowerDampedRealWeight ε) ≤
        -(∑ k ∈ Icc 1 M, (sieveSeq N (pmPowerDampedRealWeight ε) (k + 1) -
          sieveSeq N (pmPowerDampedRealWeight ε) k) ^ (2 : ℕ)) ∧
      sieveRenormalizedPrefixDefect N M (pmPowerDampedRealWeight ε) ≤ 0 := by
  exact sieveRenormalizedPrefixDefect_pmPowerDampedRealWeight_radical_five_mul_bound
    hε ((Nat.le_of_dvd (by omega) (horizonRadicalState_dvd N (M + 1))).trans hhi)

/-- [Corollary] The sharp base range generates arbitrarily distant dissipative
power checkpoints, with the full Dirichlet-energy term retained. -/
theorem sieveRenormalizedPrefixDefect_pmPowerDampedRealWeight_pow_five_mul_bound
    {ε : ℝ} (hε : 0 ≤ ε) {N k m : ℕ} (hk : 2 ≤ k) (hhi : k ≤ 5 * N) (hm : 1 ≤ m) :
    2 * sieveRenormalizedPrefixDefect N (k ^ m - 1) (pmPowerDampedRealWeight ε) ≤
        -(∑ j ∈ Icc 1 (k ^ m - 1), (sieveSeq N (pmPowerDampedRealWeight ε) (j + 1) -
          sieveSeq N (pmPowerDampedRealWeight ε) j) ^ (2 : ℕ)) ∧
      sieveRenormalizedPrefixDefect N (k ^ m - 1) (pmPowerDampedRealWeight ε) ≤ 0 := by
  have hkm : k ≤ k ^ m := by simpa using pow_le_pow_right₀ (by omega : 1 ≤ k) hm
  apply sieveRenormalizedPrefixDefect_pmPowerDampedRealWeight_radical_five_mul_bound hε
  rw [Nat.sub_add_cancel (by omega : 1 ≤ k ^ m), horizonRadicalState_pow N k hm]
  exact (Nat.le_of_dvd (by omega) (horizonRadicalState_dvd N k)).trans hhi

/-- [Corollary] Literal Möbius prefixes through 5N are nonpositive. -/
theorem sieveRenormalizedPrefixDefect_moebiusReal_full_five_mul_nonpos {N M : ℕ}
    (hhi : M + 1 ≤ 5 * N) : sieveRenormalizedPrefixDefect N M moebiusReal ≤ 0 := by
  simpa only [zero_damping_weight] using
    (sieveRenormalizedPrefixDefect_pmPowerDampedRealWeight_full_five_mul_bound
      (le_refl 0) hhi).2

/-- [Corollary] Literal Möbius weights inherit every certified power checkpoint. -/
theorem sieveRenormalizedPrefixDefect_moebiusReal_pow_five_mul_nonpos {N k m : ℕ}
    (hk : 2 ≤ k) (hhi : k ≤ 5 * N) (hm : 1 ≤ m) :
    sieveRenormalizedPrefixDefect N (k ^ m - 1) moebiusReal ≤ 0 := by
  simpa only [zero_damping_weight] using
    (sieveRenormalizedPrefixDefect_pmPowerDampedRealWeight_pow_five_mul_bound
      (le_refl 0) hk hhi hm).2

/-- [Corollary] Literal Möbius defects are nonpositive on all certified radical fibers. -/
theorem sieveRenormalizedPrefixDefect_moebiusReal_radical_five_mul_nonpos {N M : ℕ}
    (hrN : horizonRadicalState N (M + 1) ≤ 5 * N) :
    sieveRenormalizedPrefixDefect N M moebiusReal ≤ 0 := by
  simpa only [zero_damping_weight] using
    (sieveRenormalizedPrefixDefect_pmPowerDampedRealWeight_radical_five_mul_bound
      (le_refl 0) hrN).2

end
end GaloisForLFunctions.TransHorizonIncidenceMechanics
