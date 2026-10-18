import GaloisForLFunctions.TransHorizonIncidenceMechanics.ComplementaryQuotientAndSecondOctaveLaw
import GaloisForLFunctions.TransHorizonIncidenceMechanics.AllHorizonRadicalSawtoothAndDefectReduction
import GaloisForLFunctions.BezoutValuationIncidence.RadicalInvariancePrimePowerAbsorptionAndSubHorizonFermiEvaluation

/-!
# Renormalized defects across the second and third horizon bands

The endpoint envelope controls the renormalized defect through Dirichlet polarization.
Rough complementary quotients extend the unit envelope beyond the initial octave.
Deleting a prime quotient gives a contraction of a smaller endpoint response, so the
second band needs no parity restriction. The same law treats third-band endpoints
when at least one of the primes two and three is absent.

For Möbius weights, the response is zero below the horizon and minus the terminal
weight above it in the odd and six-coprime ranges. The horizon distinction is necessary
even though the defect remains nonpositive on the whole stated range.
-/

open Finset ArithmeticFunction
open GaloisForLFunctions.BiScaleUncertainty GaloisForLFunctions.BezoutValuationIncidence
open RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

private theorem zero_damping_weight : pmPowerDampedRealWeight 0 = moebiusReal := by
  funext d
  simp [pmPowerDampedRealWeight]

/-- The full damped response minus its terminal weight has a unit envelope. -/
theorem abs_pmPowerDampedDivisorCoeff_sub_weight_le_one {ε : ℝ} (hε : 0 ≤ ε)
    {k : ℕ} (hk : 2 ≤ k) :
    |pmPowerDampedDivisorCoeff ε k - pmPowerDampedRealWeight ε k| ≤ 1 := by
  calc
    _ ≤ |pmPowerDampedDivisorCoeff ε k| + |pmPowerDampedRealWeight ε k| := abs_sub _ _
    _ = pmPowerDampedDivisorCoeff ε k + |pmPowerDampedRealWeight ε k| := by
      rw [abs_of_nonneg (pmPowerDampedDivisorCoeff_nonneg hε k)]
    _ ≤ 1 := pmPowerDampedDivisorCoeff_add_abs_weight_le_one hε hk

/-- Rough complementary quotients extend the damped unit envelope to arbitrary bands. -/
theorem abs_sieveSeq_pmPowerDampedRealWeight_rough_band_le_one {ε : ℝ}
    (hε : 0 ≤ ε) {N B k : ℕ} (hk : 2 ≤ k)
    (hrough : ∀ d : ℕ, d ∣ k → d ≤ B → d = 1) (hband : k ≤ (B + 1) * N) :
    |sieveSeq N (pmPowerDampedRealWeight ε) k| ≤ 1 := by
  by_cases hsub : k ≤ N
  · rw [sieveSeq_pmPowerDampedRealWeight_eq_pmPowerDampedDivisorCoeff (by omega) hsub,
      abs_of_nonneg (pmPowerDampedDivisorCoeff_nonneg hε k)]
    exact pmPowerDampedDivisorCoeff_le_one hε k
  · rw [sieveSeq_rough_band_eq_sum_divisors_sub_self hrough (by omega) hband]
    exact abs_pmPowerDampedDivisorCoeff_sub_weight_le_one hε hk

private theorem damped_defect_bound_of_endpoint {ε : ℝ} {N M : ℕ}
    (hN : 1 ≤ N) (hM : 1 ≤ M)
    (hb : |sieveSeq N (pmPowerDampedRealWeight ε) (M + 1)| ≤ 1) :
    2 * sieveRenormalizedPrefixDefect N M (pmPowerDampedRealWeight ε) ≤
        -(∑ k ∈ Icc 1 M, (sieveSeq N (pmPowerDampedRealWeight ε) (k + 1) -
          sieveSeq N (pmPowerDampedRealWeight ε) k) ^ (2 : ℕ)) ∧
      sieveRenormalizedPrefixDefect N M (pmPowerDampedRealWeight ε) ≤ 0 := by
  have hpol := two_mul_sieveRenormalizedPrefixDefect_eq_neg_dirichlet_add_boundary
    N hM (pmPowerDampedRealWeight ε)
  rw [sieveSeq_pmPowerDampedRealWeight_eq_pmPowerDampedDivisorCoeff le_rfl hN,
    pmPowerDampedDivisorCoeff_one, one_pow] at hpol
  have hsq : sieveSeq N (pmPowerDampedRealWeight ε) (M + 1) ^ (2 : ℕ) ≤ 1 := by
    rwa [sq_le_one_iff_abs_le_one]
  have henergy : 0 ≤ ∑ k ∈ Icc 1 M,
      (sieveSeq N (pmPowerDampedRealWeight ε) (k + 1) -
        sieveSeq N (pmPowerDampedRealWeight ε) k) ^ (2 : ℕ) :=
    sum_nonneg fun _ _ => sq_nonneg _
  constructor <;> linarith

/-- A rough endpoint forces the defect below minus half its full Dirichlet energy. -/
theorem sieveRenormalizedPrefixDefect_pmPowerDampedRealWeight_rough_band_nonpos
    {ε : ℝ} (hε : 0 ≤ ε) {N B M : ℕ} (hM : 1 ≤ M)
    (hrough : ∀ d : ℕ, d ∣ M + 1 → d ≤ B → d = 1)
    (hband : M + 1 ≤ (B + 1) * N) :
    2 * sieveRenormalizedPrefixDefect N M (pmPowerDampedRealWeight ε) ≤
        -(∑ k ∈ Icc 1 M, (sieveSeq N (pmPowerDampedRealWeight ε) (k + 1) -
          sieveSeq N (pmPowerDampedRealWeight ε) k) ^ (2 : ℕ)) ∧
      sieveRenormalizedPrefixDefect N M (pmPowerDampedRealWeight ε) ≤ 0 := by
  have hN : 1 ≤ N := by
    by_contra hn
    have : N = 0 := by omega
    simp [this] at hband
  exact damped_defect_bound_of_endpoint hN hM
    (abs_sieveSeq_pmPowerDampedRealWeight_rough_band_le_one hε (by omega) hrough hband)

/-- Every even checkpoint through the second band has nonpositive damped defect. -/
theorem sieveRenormalizedPrefixDefect_pmPowerDampedRealWeight_even_nonpos
    {ε : ℝ} (hε : 0 ≤ ε) {N m : ℕ} (hm : 1 ≤ 2 * m) (hband : 2 * m + 1 ≤ 3 * N) :
    sieveRenormalizedPrefixDefect N (2 * m) (pmPowerDampedRealWeight ε) ≤ 0 := by
  exact (sieveRenormalizedPrefixDefect_pmPowerDampedRealWeight_rough_band_nonpos hε hm
    (rough_two_of_not_two_dvd (by omega) (by omega : ¬ 2 ∣ 2 * m + 1))
    (by omega : 2 * m + 1 ≤ (2 + 1) * N)).2

/-- Six-coprime endpoints through the third band have nonpositive damped defect. -/
theorem sieveRenormalizedPrefixDefect_pmPowerDampedRealWeight_coprime_six_nonpos
    {ε : ℝ} (hε : 0 ≤ ε) {N M : ℕ} (hM : 1 ≤ M)
    (h2 : ¬ 2 ∣ M + 1) (h3 : ¬ 3 ∣ M + 1) (hband : M + 1 ≤ 4 * N) :
    sieveRenormalizedPrefixDefect N M (pmPowerDampedRealWeight ε) ≤ 0 := by
  exact (sieveRenormalizedPrefixDefect_pmPowerDampedRealWeight_rough_band_nonpos hε hM
    (rough_three_of_not_two_three_dvd (by omega) h2 h3)
    (by omega : M + 1 ≤ (3 + 1) * N)).2

/-- Odd Möbius responses through `3N`, with the necessary horizon split. -/
theorem sieveSeq_moebiusReal_odd_through_three_mul {N k : ℕ} (hk : 2 ≤ k)
    (hodd : ¬ 2 ∣ k) (hband : k ≤ 3 * N) :
    sieveSeq N moebiusReal k = if k ≤ N then 0 else -moebiusReal k := by
  split_ifs with hsub
  · rw [sieveSeq_moebiusReal_eq_ite_of_le (by omega) hsub, if_neg (by omega : k ≠ 1)]
  · rw [sieveSeq_odd_le_three_mul_eq_sum_divisors_sub_self hodd (by omega) hband,
      sum_divisors_moebiusReal_eq_zero hk, zero_sub]

/-- Six-coprime Möbius responses through `4N`, including the sub-horizon branch. -/
theorem sieveSeq_moebiusReal_coprime_six_through_four_mul {N k : ℕ} (hk : 2 ≤ k)
    (h2 : ¬ 2 ∣ k) (h3 : ¬ 3 ∣ k) (hband : k ≤ 4 * N) :
    sieveSeq N moebiusReal k = if k ≤ N then 0 else -moebiusReal k := by
  split_ifs with hsub
  · rw [sieveSeq_moebiusReal_eq_ite_of_le (by omega) hsub, if_neg (by omega : k ≠ 1)]
  · rw [sieveSeq_coprime_six_le_four_mul_eq_sum_divisors_sub_self h2 h3 (by omega) hband,
      sum_divisors_moebiusReal_eq_zero hk, zero_sub]

/-- Above the horizon the odd response is exactly the negative terminal Möbius weight. -/
theorem sieveSeq_moebiusReal_odd_trans_horizon {N k : ℕ} (hk : 2 ≤ k)
    (hodd : ¬ 2 ∣ k) (hN : N < k) (hband : k ≤ 3 * N) :
    sieveSeq N moebiusReal k = -moebiusReal k := by
  rw [sieveSeq_moebiusReal_odd_through_three_mul hk hodd hband, if_neg (by omega)]

/-- Above the horizon the six-coprime response is exactly the negative terminal weight. -/
theorem sieveSeq_moebiusReal_coprime_six_trans_horizon {N k : ℕ} (hk : 2 ≤ k)
    (h2 : ¬ 2 ∣ k) (h3 : ¬ 3 ∣ k) (hN : N < k) (hband : k ≤ 4 * N) :
    sieveSeq N moebiusReal k = -moebiusReal k := by
  rw [sieveSeq_moebiusReal_coprime_six_through_four_mul hk h2 h3 hband, if_neg (by omega)]

/-- Every odd response in the full range is one of minus one, zero, and one. -/
theorem sieveSeq_moebiusReal_odd_three_valued {N k : ℕ} (hk : 2 ≤ k)
    (hodd : ¬ 2 ∣ k) (hband : k ≤ 3 * N) :
    sieveSeq N moebiusReal k = -1 ∨ sieveSeq N moebiusReal k = 0 ∨
      sieveSeq N moebiusReal k = 1 := by
  rw [sieveSeq_moebiusReal_odd_through_three_mul hk hodd hband]
  split_ifs
  · simp
  · rcases moebius_eq_or k with h | h | h <;> simp [moebiusReal, h]

/-- The squarefree sub-horizon family obstructs extending the negative-weight identity
across the horizon. This obstruction leaves the unit envelope intact. -/
theorem sieveSeq_moebiusReal_ne_neg_of_squarefree_subhorizon {N k : ℕ}
    (hk : 2 ≤ k) (hkN : k ≤ N) (hsq : Squarefree k) :
    sieveSeq N moebiusReal k ≠ -moebiusReal k := by
  rw [sieveSeq_moebiusReal_eq_ite_of_le (by omega) hkN, if_neg (by omega : k ≠ 1)]
  have hmu : moebiusReal k ≠ 0 := by
    simpa only [moebiusReal, ne_eq, Int.cast_eq_zero] using
      (moebius_ne_zero_iff_squarefree.mpr hsq)
  intro h
  exact hmu (by linarith)

/-- Möbius specialization of the full even-checkpoint nonpositivity range. -/
theorem sieveRenormalizedPrefixDefect_moebiusReal_even_nonpos {N m : ℕ}
    (hm : 1 ≤ 2 * m) (hband : 2 * m + 1 ≤ 3 * N) :
    sieveRenormalizedPrefixDefect N (2 * m) moebiusReal ≤ 0 := by
  simpa only [zero_damping_weight] using
    sieveRenormalizedPrefixDefect_pmPowerDampedRealWeight_even_nonpos (le_refl 0) hm hband

/-- Möbius defect nonpositivity throughout the full six-coprime third-band range. -/
theorem sieveRenormalizedPrefixDefect_moebiusReal_coprime_six_nonpos {N M : ℕ}
    (hM : 1 ≤ M) (h2 : ¬ 2 ∣ M + 1) (h3 : ¬ 3 ∣ M + 1) (hband : M + 1 ≤ 4 * N) :
    sieveRenormalizedPrefixDefect N M moebiusReal ≤ 0 := by
  simpa only [zero_damping_weight] using
    sieveRenormalizedPrefixDefect_pmPowerDampedRealWeight_coprime_six_nonpos
      (le_refl 0) hM h2 h3 hband

/-- Prime multiplication switches the terminal damped weight off precisely when
the prime is already present, and otherwise introduces its negative local factor. -/
theorem pmPowerDampedRealWeight_prime_mul_switch (ε : ℝ) {p : ℕ}
    (hp : p.Prime) (u : ℕ) :
    pmPowerDampedRealWeight ε (p * u) =
      if p ∣ u then 0 else -(p : ℝ) ^ (-ε) * pmPowerDampedRealWeight ε u := by
  by_cases hpu : p ∣ u
  · have hs : ¬ Squarefree (p * u) := by
      intro h
      exact (hp.coprime_iff_not_dvd.mp (Nat.coprime_of_squarefree_mul h)) hpu
    simp [if_pos hpu, pmPowerDampedRealWeight, moebiusReal,
      moebius_eq_zero_of_not_squarefree hs]
  · rw [if_neg hpu]
    unfold pmPowerDampedRealWeight moebiusReal
    rw [isMultiplicative_moebius.map_mul_of_coprime (hp.coprime_iff_not_dvd.mpr hpu),
      moebius_apply_prime hp, Nat.cast_mul,
      Real.mul_rpow (Nat.cast_nonneg p) (Nat.cast_nonneg u)]
    push_cast
    ring

/-- Deleting one prime quotient contracts a smaller terminal-deleted response. -/
theorem pmPowerDamped_prime_deleted_response (ε : ℝ) {p : ℕ}
    (hp : p.Prime) (u : ℕ) :
    pmPowerDampedDivisorCoeff ε (p * u) - pmPowerDampedRealWeight ε (p * u) -
        pmPowerDampedRealWeight ε u =
      (if p ∣ u then 1 else 1 - (p : ℝ) ^ (-ε)) *
        (pmPowerDampedDivisorCoeff ε u - pmPowerDampedRealWeight ε u) := by
  rw [pmPowerDampedDivisorCoeff_prime_mul ε hp u, pmPowerDampedRealWeight_prime_mul_switch ε hp u]
  split_ifs <;> ring

/-- The prime-deletion operator preserves the unit envelope under nonnegative damping. -/
theorem abs_pmPowerDamped_prime_deleted_response_le_one {ε : ℝ} (hε : 0 ≤ ε)
    {p u : ℕ} (hp : p.Prime) (hu : 2 ≤ u) :
    |pmPowerDampedDivisorCoeff ε (p * u) - pmPowerDampedRealWeight ε (p * u) -
      pmPowerDampedRealWeight ε u| ≤ 1 := by
  rw [pmPowerDamped_prime_deleted_response ε hp u, abs_mul]
  have hpow0 := Real.rpow_nonneg (Nat.cast_nonneg p) (-ε)
  have hpow1 : (p : ℝ) ^ (-ε) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hp.one_lt.le) (by linarith)
  have hf : 0 ≤ (if p ∣ u then 1 else 1 - (p : ℝ) ^ (-ε)) ∧
      (if p ∣ u then 1 else 1 - (p : ℝ) ^ (-ε)) ≤ 1 := by
    split_ifs <;> constructor <;> linarith
  rw [abs_of_nonneg hf.1]
  calc
    _ ≤ (if p ∣ u then 1 else 1 - (p : ℝ) ^ (-ε)) * 1 :=
      mul_le_mul_of_nonneg_left (abs_pmPowerDampedDivisorCoeff_sub_weight_le_one hε hu) hf.1
    _ ≤ 1 := by simpa only [mul_one] using hf.2

/-- Every point in the second band satisfies the unit envelope, including even points. -/
theorem abs_sieveSeq_pmPowerDampedRealWeight_second_band_le_one {ε : ℝ}
    (hε : 0 ≤ ε) {N k : ℕ} (hlo : 2 * N + 1 ≤ k) (hhi : k ≤ 3 * N) :
    |sieveSeq N (pmPowerDampedRealWeight ε) k| ≤ 1 := by
  by_cases h2 : 2 ∣ k
  · obtain ⟨u, rfl⟩ := h2
    rw [sieveSeq_pmPowerDampedRealWeight_second_octave_eq ε hlo hhi,
      if_pos (dvd_mul_right 2 u), Nat.mul_div_cancel_left u (by omega : 0 < 2)]
    exact abs_pmPowerDamped_prime_deleted_response_le_one hε Nat.prime_two (by omega)
  · rw [sieveSeq_pmPowerDampedRealWeight_second_octave_eq ε hlo hhi, if_neg h2, sub_zero]
    exact abs_pmPowerDampedDivisorCoeff_sub_weight_le_one hε (by omega)

/-- The complete initial range through `3N` has a unit damped response envelope. -/
theorem abs_sieveSeq_pmPowerDampedRealWeight_le_one_of_le_three_mul {ε : ℝ}
    (hε : 0 ≤ ε) {N k : ℕ} (hk : 2 ≤ k) (hhi : k ≤ 3 * N) :
    |sieveSeq N (pmPowerDampedRealWeight ε) k| ≤ 1 := by
  by_cases hlo : k ≤ 2 * N
  · exact abs_sieveSeq_pmPowerDampedRealWeight_le_one_of_le_two_mul hε hk hlo
  · exact abs_sieveSeq_pmPowerDampedRealWeight_second_band_le_one hε (by omega) hhi

/-- Every Möbius endpoint through `3N` has square bounded by the initial square, which is one. -/
theorem sieveSeq_moebiusReal_sq_le_initial_sq_of_le_three_mul {N k : ℕ}
    (hk : 2 ≤ k) (hhi : k ≤ 3 * N) :
    sieveSeq N moebiusReal k ^ (2 : ℕ) ≤ sieveSeq N moebiusReal 1 ^ (2 : ℕ) ∧
      sieveSeq N moebiusReal 1 ^ (2 : ℕ) = 1 := by
  have hb : |sieveSeq N moebiusReal k| ≤ 1 := by
    simpa only [zero_damping_weight] using
      abs_sieveSeq_pmPowerDampedRealWeight_le_one_of_le_three_mul (le_refl 0) hk hhi
  rw [sieveSeq_moebiusReal_eq_ite_of_le le_rfl (by omega : 1 ≤ N), if_pos rfl, one_pow]
  exact ⟨(sq_le_one_iff_abs_le_one _).mpr hb, rfl⟩

/-- Every checkpoint through the second band, without parity restrictions, has
nonpositive damped defect and a quantitative Dirichlet-energy bound. -/
theorem sieveRenormalizedPrefixDefect_pmPowerDampedRealWeight_three_mul_nonpos
    {ε : ℝ} (hε : 0 ≤ ε) {N M : ℕ} (hM : 1 ≤ M) (hhi : M + 1 ≤ 3 * N) :
    2 * sieveRenormalizedPrefixDefect N M (pmPowerDampedRealWeight ε) ≤
        -(∑ k ∈ Icc 1 M, (sieveSeq N (pmPowerDampedRealWeight ε) (k + 1) -
          sieveSeq N (pmPowerDampedRealWeight ε) k) ^ (2 : ℕ)) ∧
      sieveRenormalizedPrefixDefect N M (pmPowerDampedRealWeight ε) ≤ 0 := by
  exact damped_defect_bound_of_endpoint (by omega) hM
    (abs_sieveSeq_pmPowerDampedRealWeight_le_one_of_le_three_mul hε (by omega) hhi)

/-- Möbius defects are nonpositive at every checkpoint through the second band. -/
theorem sieveRenormalizedPrefixDefect_moebiusReal_three_mul_nonpos {N M : ℕ}
    (hM : 1 ≤ M) (hhi : M + 1 ≤ 3 * N) :
    sieveRenormalizedPrefixDefect N M moebiusReal ≤ 0 := by
  simpa only [zero_damping_weight] using
    (sieveRenormalizedPrefixDefect_pmPowerDampedRealWeight_three_mul_nonpos
      (le_refl 0) hM hhi).2

/-- Exact damped third-band response, including both possible prime quotient deletions. -/
theorem sieveSeq_pmPowerDampedRealWeight_third_band_eq (ε : ℝ) {N k : ℕ}
    (hlo : 3 * N + 1 ≤ k) (hhi : k ≤ 4 * N) :
    sieveSeq N (pmPowerDampedRealWeight ε) k =
      pmPowerDampedDivisorCoeff ε k - pmPowerDampedRealWeight ε k -
        (if 2 ∣ k then pmPowerDampedRealWeight ε (k / 2) else 0) -
        (if 3 ∣ k then pmPowerDampedRealWeight ε (k / 3) else 0) := by
  rw [sieveSeq_third_band_eq_sum_divisors_sub hlo hhi]
  rfl

/-- In the third band, either missing small prime leaves at most one deleted quotient. -/
theorem abs_sieveSeq_pmPowerDampedRealWeight_third_band_le_one {ε : ℝ}
    (hε : 0 ≤ ε) {N k : ℕ} (hlo : 3 * N + 1 ≤ k) (hhi : k ≤ 4 * N)
    (hmiss : ¬ 2 ∣ k ∨ ¬ 3 ∣ k) :
    |sieveSeq N (pmPowerDampedRealWeight ε) k| ≤ 1 := by
  rcases hmiss with h2 | h3
  · by_cases h3 : 3 ∣ k
    · obtain ⟨u, rfl⟩ := h3
      rw [sieveSeq_pmPowerDampedRealWeight_third_band_eq ε hlo hhi,
        if_neg h2, if_pos (dvd_mul_right 3 u), sub_zero,
        Nat.mul_div_cancel_left u (by omega : 0 < 3)]
      exact abs_pmPowerDamped_prime_deleted_response_le_one hε Nat.prime_three (by omega)
    · rw [sieveSeq_pmPowerDampedRealWeight_third_band_eq ε hlo hhi,
        if_neg h2, if_neg h3, sub_zero, sub_zero]
      exact abs_pmPowerDampedDivisorCoeff_sub_weight_le_one hε (by omega)
  · by_cases h2 : 2 ∣ k
    · obtain ⟨u, rfl⟩ := h2
      rw [sieveSeq_pmPowerDampedRealWeight_third_band_eq ε hlo hhi,
        if_pos (dvd_mul_right 2 u), if_neg h3, sub_zero,
        Nat.mul_div_cancel_left u (by omega : 0 < 2)]
      exact abs_pmPowerDamped_prime_deleted_response_le_one hε Nat.prime_two (by omega)
    · rw [sieveSeq_pmPowerDampedRealWeight_third_band_eq ε hlo hhi,
        if_neg h2, if_neg h3, sub_zero, sub_zero]
      exact abs_pmPowerDampedDivisorCoeff_sub_weight_le_one hε (by omega)

/-- Missing either two or three is enough for defect nonpositivity throughout `4N`. -/
theorem sieveRenormalizedPrefixDefect_pmPowerDampedRealWeight_four_mul_nonpos
    {ε : ℝ} (hε : 0 ≤ ε) {N M : ℕ} (hM : 1 ≤ M) (hhi : M + 1 ≤ 4 * N)
    (hmiss : ¬ 2 ∣ M + 1 ∨ ¬ 3 ∣ M + 1) :
    sieveRenormalizedPrefixDefect N M (pmPowerDampedRealWeight ε) ≤ 0 := by
  apply (damped_defect_bound_of_endpoint (ε := ε) (by omega : 1 ≤ N) hM ?_).2
  by_cases hlo : M + 1 ≤ 3 * N
  · exact abs_sieveSeq_pmPowerDampedRealWeight_le_one_of_le_three_mul hε (by omega) hlo
  · exact abs_sieveSeq_pmPowerDampedRealWeight_third_band_le_one hε (by omega) hhi hmiss

/-- The expanded third-band checkpoint range also holds for the literal Möbius weight. -/
theorem sieveRenormalizedPrefixDefect_moebiusReal_four_mul_nonpos {N M : ℕ}
    (hM : 1 ≤ M) (hhi : M + 1 ≤ 4 * N) (hmiss : ¬ 2 ∣ M + 1 ∨ ¬ 3 ∣ M + 1) :
    sieveRenormalizedPrefixDefect N M moebiusReal ≤ 0 := by
  simpa only [zero_damping_weight] using sieveRenormalizedPrefixDefect_pmPowerDampedRealWeight_four_mul_nonpos
    (le_refl 0) hM hhi hmiss

/-- Every prime above three gives a six-coprime sub-horizon obstruction to the
unsplit negative-weight identity, at every horizon containing that prime. -/
theorem sieveSeq_moebiusReal_coprime_six_subhorizon_counterfamily {N p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hpN : p ≤ N) :
    ¬ 2 ∣ p ∧ ¬ 3 ∣ p ∧ sieveSeq N moebiusReal p ≠ -moebiusReal p := by
  have h2 : ¬ 2 ∣ p := by
    intro h
    have := (Nat.dvd_prime hp).mp h
    omega
  have h3 : ¬ 3 ∣ p := by
    intro h
    have := (Nat.dvd_prime hp).mp h
    omega
  refine ⟨h2, h3, ?_⟩
  rw [sieveSeq_moebiusReal_eq_ite_of_le (by omega) hpN, if_neg hp.ne_one]
  simp [moebiusReal, moebius_apply_prime hp]

end
end GaloisForLFunctions.TransHorizonIncidenceMechanics
