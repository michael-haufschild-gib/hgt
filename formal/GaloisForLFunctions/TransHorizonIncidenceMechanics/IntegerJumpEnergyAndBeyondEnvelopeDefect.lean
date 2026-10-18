import GaloisForLFunctions.TransHorizonIncidenceMechanics.ExactAdditiveEnvelopeAndFirstFailure

/-!
# Integer jump energy beyond the unit-envelope boundary

Classical baseline: integer z²≥|z|, triangle inequality, discrete polarization,
Möbius divisor cancellation, and complementary-divisor splitting. The truncated
sum is exactly D(n;a) in Helfgott–Thompson, Proposition 3.2:
https://doi.org/10.1007/s40993-022-00408-8. Observation and finite shifted-correlation
baselines: [TH10] https://arxiv.org/abs/1009.5281 and
[CMS16] https://arxiv.org/abs/1612.03136.

Equivalent classical formulation: for the integer path
s_N(k)=Σ_{d∣k,d≤N}μ(d), N≥2 and M≥1, the prefix jump energy satisfies
E_N(M)≥1+|s_N(M+1)|. Exact polarization gives
2D_N(M)≤s_N(M+1)²−|s_N(M+1)|−2. Thus endpoint magnitude at most two
certifies nonpositive Möbius defect, beyond the unit-envelope method.

Prime deletion and squarefree absorption give |s_N(c_ε,k)|≤2 for every ε≥0
and 2≤k<6(N+1). At ε=0, the integer-energy criterion certifies all these
prefixes, their radical fibers and positive-power checkpoints. In particular,
the symbolic response-two family N=6p−1, k=30p and all its positive powers
have nonpositive defects: the unit-envelope obstruction is not a sign obstruction.

Classification: New formulation, with elementary known constituents labeled.
No external novelty claim, global all-endpoint sign theorem, or integer-energy
claim for positive damping. N≤1 and empty prefixes are covered explicitly.
-/

open Finset ArithmeticFunction
open GaloisForLFunctions.BiScaleUncertainty GaloisForLFunctions.BezoutValuationIncidence
open RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius
namespace GaloisForLFunctions.TransHorizonIncidenceMechanics
noncomputable section
set_option autoImplicit false

/-- [Known] Integer squared jumps dominate their absolute size. -/
theorem abs_intCast_le_sq (z : ℤ) : |(z : ℝ)| ≤ (z : ℝ) ^ (2 : ℕ) := by
  have h : z ≤ -1 ∨ z = 0 ∨ 1 ≤ z := by omega
  rcases h with h | rfl | h
  · have hr : (z : ℝ) ≤ -1 := by exact_mod_cast h
    rw [abs_of_nonpos (by linarith)]
    nlinarith
  · simp
  · have hr : (1 : ℝ) ≤ z := by exact_mod_cast h
    rw [abs_of_nonneg (by linarith)]
    nlinarith

/-- [Known] Integer path energy controls displacement without a length factor. -/
theorem integer_path_abs_sub_le_sum_sq (f : ℕ → ℤ) (a L : ℕ) :
    |(f (a + L) : ℝ) - f a| ≤
      ∑ j ∈ range L, ((f (a + j + 1) : ℝ) - f (a + j)) ^ (2 : ℕ) := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Finset.sum_range_succ]
    have hj := abs_intCast_le_sq (f (a + L + 1) - f (a + L))
    push_cast at hj
    have ht := abs_add_le ((f (a + L) : ℝ) - f a)
      ((f (a + L + 1) : ℝ) - f (a + L))
    have he : (f (a + L) : ℝ) - f a + (f (a + L + 1) - f (a + L)) =
        f (a + L + 1) - f a := by ring
    rw [he] at ht
    simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using (ht.trans (add_le_add ih hj))

/-- [Known] A first step from one to zero pays one plus terminal magnitude. -/
theorem integer_prefix_energy_of_first_zero (f : ℕ → ℤ)
    (h1 : f 1 = 1) (h2 : f 2 = 0) {M : ℕ} (hM : 1 ≤ M) :
    1 + |(f (M + 1) : ℝ)| ≤
      ∑ k ∈ Icc 1 M, ((f (k + 1) : ℝ) - f k) ^ (2 : ℕ) := by
  cases M with
  | zero => omega
  | succ L =>
    clear hM
    induction L with
    | zero => simp [h1, h2]
    | succ L ih =>
      rw [sum_Icc_succ_top (by omega)]
      have hj := abs_intCast_le_sq (f (L + 1 + 1 + 1) - f (L + 1 + 1))
      push_cast at hj
      have ht := abs_add_le (f (L + 1 + 1) : ℝ)
        ((f (L + 1 + 1 + 1) : ℝ) - f (L + 1 + 1))
      have he : (f (L + 1 + 1) : ℝ) + (f (L + 1 + 1 + 1) - f (L + 1 + 1)) =
          f (L + 1 + 1 + 1) := by ring
      rw [he] at ht
      linarith

/-- [Known] The truncated Möbius response is an integer-valued path. -/
theorem sieveSeq_moebiusReal_eq_intCast (N k : ℕ) :
    sieveSeq N moebiusReal k =
      ((∑ d ∈ (Icc 1 N).filter (fun d => d ∣ k), μ d : ℤ) : ℝ) := by
  simp only [Int.cast_sum, sieveSeq, moebiusReal]

/-- [Corollary] Möbius path displacement is bounded by local jump energy. -/
theorem sieveSeq_moebiusReal_abs_sub_le_dirichlet (N a L : ℕ) :
    |sieveSeq N moebiusReal (a + L) - sieveSeq N moebiusReal a| ≤
      ∑ j ∈ range L, (sieveSeq N moebiusReal (a + j + 1) -
        sieveSeq N moebiusReal (a + j)) ^ (2 : ℕ) := by
  simpa only [sieveSeq_moebiusReal_eq_intCast] using
    integer_path_abs_sub_le_sum_sq
      (fun k => ∑ d ∈ (Icc 1 N).filter (fun d => d ∣ k), μ d) a L

/-- [New formulation] The initial Möbius zero strengthens every nonempty prefix energy bound. -/
theorem moebius_prefix_energy_ge_one_add_abs {N M : ℕ} (hN : 2 ≤ N) (hM : 1 ≤ M) :
    1 + |sieveSeq N moebiusReal (M + 1)| ≤
      ∑ k ∈ Icc 1 M, (sieveSeq N moebiusReal (k + 1) -
        sieveSeq N moebiusReal k) ^ (2 : ℕ) := by
  let f : ℕ → ℤ := fun k => ∑ d ∈ (Icc 1 N).filter (fun d => d ∣ k), μ d
  have hf (k : ℕ) : (f k : ℝ) = sieveSeq N moebiusReal k :=
    (sieveSeq_moebiusReal_eq_intCast N k).symm
  have h1 : (f 1 : ℝ) = 1 := by
    rw [hf, sieveSeq_moebiusReal_eq_ite_of_le (by omega) (by omega), if_pos rfl]
  have h2 : (f 2 : ℝ) = 0 := by
    rw [hf, sieveSeq_moebiusReal_eq_ite_of_le (by omega) hN, if_neg (by omega)]
  simpa only [hf] using integer_prefix_energy_of_first_zero f
    (by exact_mod_cast h1) (by exact_mod_cast h2) hM

/-- [New formulation] Integer energy turns polarization into an endpoint-only quadratic budget. -/
theorem two_mul_moebius_prefix_defect_le_endpoint_integer_budget {N M : ℕ}
    (hN : 2 ≤ N) (hM : 1 ≤ M) :
    2 * sieveRenormalizedPrefixDefect N M moebiusReal ≤
      sieveSeq N moebiusReal (M + 1) ^ (2 : ℕ) -
        |sieveSeq N moebiusReal (M + 1)| - 2 := by
  have he := moebius_prefix_energy_ge_one_add_abs hN hM
  have hp := two_mul_sieveRenormalizedPrefixDefect_eq_neg_dirichlet_add_boundary N hM moebiusReal
  rw [sieveSeq_moebiusReal_eq_ite_of_le (by omega : 1 ≤ 1) (by omega : 1 ≤ N),
    if_pos rfl, one_pow] at hp
  linarith

/-- [Corollary] Unit-envelope endpoints have a strict negative defect margin. -/
theorem moebius_prefix_defect_le_neg_one_of_abs_le_one {N M : ℕ}
    (hN : 2 ≤ N) (hM : 1 ≤ M) (hb : |sieveSeq N moebiusReal (M + 1)| ≤ 1) :
    sieveRenormalizedPrefixDefect N M moebiusReal ≤ -1 := by
  have h := two_mul_moebius_prefix_defect_le_endpoint_integer_budget hN hM
  have hprod := mul_nonneg (abs_nonneg (sieveSeq N moebiusReal (M + 1)))
    (sub_nonneg.mpr hb)
  nlinarith [sq_abs (sieveSeq N moebiusReal (M + 1))]

/-- [New formulation] Endpoint magnitude two is admissible at every horizon. -/
theorem moebius_prefix_defect_nonpos_of_abs_le_two {N M : ℕ}
    (hb : |sieveSeq N moebiusReal (M + 1)| ≤ 2) :
    sieveRenormalizedPrefixDefect N M moebiusReal ≤ 0 := by
  by_cases hM : M = 0
  · subst M
    simp [sieveRenormalizedPrefixDefect_eq_sum_mul_addDiff]
  by_cases hN : 2 ≤ N
  · have h := two_mul_moebius_prefix_defect_le_endpoint_integer_budget hN (M := M) (by omega)
    have hprod := mul_nonneg (abs_nonneg (sieveSeq N moebiusReal (M + 1)))
      (sub_nonneg.mpr hb)
    nlinarith [sq_abs (sieveSeq N moebiusReal (M + 1))]
  · have hcases : N = 0 ∨ N = 1 := by omega
    rcases hcases with rfl | rfl <;>
      simp [sieveRenormalizedPrefixDefect_eq_sum_mul_addDiff, sieveSeq, Finset.sum_filter, moebiusReal]


private theorem Icc_one_five : Icc (1 : ℕ) 5 = {1, 2, 3, 4, 5} := by
  ext q
  simp only [mem_Icc, mem_insert, mem_singleton]
  omega

/-- [Corollary] The fifth integer band has exactly five possible quotient channels. -/
theorem sieveSeq_fifth_integer_band_eq_sum_divisors_sub {N k : ℕ}
    (hlo : 5 * N < k) (hhi : k < 6 * (N + 1)) (c : ℕ → ℝ) :
    sieveSeq N c k = (∑ d ∈ k.divisors, c d) - c k -
      (if 2 ∣ k then c (k / 2) else 0) - (if 3 ∣ k then c (k / 3) else 0) -
      (if 4 ∣ k then c (k / 4) else 0) - (if 5 ∣ k then c (k / 5) else 0) := by
  rw [sieveSeq_integer_band_eq_sum_divisors_sub_quotients hlo hhi c, Icc_one_five]
  simp only [mem_insert, mem_singleton, OfNat.one_ne_ofNat, Nat.reduceEqDiff,
    or_self, not_false_eq_true, sum_insert, sum_singleton, one_dvd, ↓reduceIte, Nat.div_one]
  ring

/-- [Corollary] Deleting the two and three channels contracts every endpoint at least two. -/
theorem abs_pmPowerDamped_two_three_deleted_le_one {ε : ℝ}
    (hε : 0 ≤ ε) {k : ℕ} (hk : 2 ≤ k) :
    |pmPowerDampedDivisorCoeff ε k - pmPowerDampedRealWeight ε k -
      (if 2 ∣ k then pmPowerDampedRealWeight ε (k / 2) else 0) -
      (if 3 ∣ k then pmPowerDampedRealWeight ε (k / 3) else 0)| ≤ 1 := by
  by_cases h2 : 2 ∣ k
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
      rw [if_pos (dvd_mul_right 2 (3 * u)), if_pos h3',
        Nat.mul_div_cancel_left (3 * u) (by omega : 0 < 2), hdiv3]
      exact abs_pmPowerDamped_two_prime_deleted_response_le_one_of_pos hε
        Nat.prime_two Nat.prime_three (by omega) (by omega)
    · obtain ⟨u, rfl⟩ := h2
      rw [if_pos (dvd_mul_right 2 u), if_neg h3, sub_zero,
        Nat.mul_div_cancel_left u (by omega : 0 < 2)]
      exact abs_pmPowerDamped_prime_deleted_response_le_one_of_pos hε Nat.prime_two (by omega)
  · by_cases h3 : 3 ∣ k
    · obtain ⟨u, rfl⟩ := h3
      rw [if_neg h2, if_pos (dvd_mul_right 3 u), sub_zero,
        Nat.mul_div_cancel_left u (by omega : 0 < 3)]
      exact abs_pmPowerDamped_prime_deleted_response_le_one_of_pos hε Nat.prime_three (by omega)
    · rw [if_neg h2, if_neg h3, sub_zero, sub_zero]
      exact abs_pmPowerDampedDivisorCoeff_sub_weight_le_one hε hk

/-- [Corollary] Every nonnegatively damped Möbius coefficient has magnitude at most one. -/
theorem abs_pmPowerDampedRealWeight_le_one {ε : ℝ} (hε : 0 ≤ ε) (k : ℕ) :
    |pmPowerDampedRealWeight ε k| ≤ 1 := by
  by_cases hk : 2 ≤ k
  · have h := pmPowerDampedDivisorCoeff_add_abs_weight_le_one hε hk
    linarith [pmPowerDampedDivisorCoeff_nonneg hε k]
  · have hcases : k = 0 ∨ k = 1 := by omega
    rcases hcases with rfl | rfl <;> simp [pmPowerDampedRealWeight, moebiusReal]

/-- [New formulation] The fifth integer band has a uniform response bound of two. -/
theorem abs_sieveSeq_pmPowerDampedRealWeight_fifth_integer_band_le_two {ε : ℝ}
    (hε : 0 ≤ ε) {N k : ℕ} (hk : 2 ≤ k)
    (hlo : 5 * N < k) (hhi : k < 6 * (N + 1)) :
    |sieveSeq N (pmPowerDampedRealWeight ε) k| ≤ 2 := by
  by_cases h4 : 4 ∣ k
  · obtain ⟨u, rfl⟩ := h4
    rw [show 4 * u = 2 * (2 * u) by ring,
      sieveSeq_pmPowerDampedRealWeight_mul_of_dvd ε N (dvd_mul_right 2 u)]
    exact (abs_sieveSeq_pmPowerDampedRealWeight_le_one_of_lt_five_succ
      hε (by omega) (by omega)).trans (by norm_num)
  · rw [sieveSeq_fifth_integer_band_eq_sum_divisors_sub hlo hhi, if_neg h4, sub_zero]
    change |pmPowerDampedDivisorCoeff ε k - pmPowerDampedRealWeight ε k -
      (if 2 ∣ k then pmPowerDampedRealWeight ε (k / 2) else 0) -
      (if 3 ∣ k then pmPowerDampedRealWeight ε (k / 3) else 0) -
      (if 5 ∣ k then pmPowerDampedRealWeight ε (k / 5) else 0)| ≤ 2
    have hbase := abs_pmPowerDamped_two_three_deleted_le_one hε hk
    have h5 : |if 5 ∣ k then pmPowerDampedRealWeight ε (k / 5) else 0| ≤ 1 := by
      split_ifs
      · exact abs_pmPowerDampedRealWeight_le_one hε _
      · norm_num
    rw [sub_eq_add_neg]
    exact (abs_add_le _ _).trans (by rw [abs_neg]; linarith)

/-- [New formulation] All nonnegative damping exponents satisfy the six-horizon response envelope. -/
theorem abs_sieveSeq_pmPowerDampedRealWeight_le_two_of_lt_six_succ {ε : ℝ}
    (hε : 0 ≤ ε) {N k : ℕ} (hk : 2 ≤ k) (hhi : k < 6 * (N + 1)) :
    |sieveSeq N (pmPowerDampedRealWeight ε) k| ≤ 2 := by
  by_cases h5 : k < 5 * (N + 1)
  · exact (abs_sieveSeq_pmPowerDampedRealWeight_le_one_of_lt_five_succ hε hk h5).trans
      (by norm_num)
  · exact abs_sieveSeq_pmPowerDampedRealWeight_fifth_integer_band_le_two hε hk (by omega) hhi

private theorem zero_damping_weight : pmPowerDampedRealWeight 0 = moebiusReal := by
  funext d
  simp [pmPowerDampedRealWeight]

/-- [Corollary] The undamped response also satisfies the six-horizon envelope. -/
theorem abs_sieveSeq_moebiusReal_le_two_of_lt_six_succ {N k : ℕ}
    (hk : 2 ≤ k) (hhi : k < 6 * (N + 1)) : |sieveSeq N moebiusReal k| ≤ 2 := by
  simpa only [zero_damping_weight] using
    abs_sieveSeq_pmPowerDampedRealWeight_le_two_of_lt_six_succ (le_refl 0) hk hhi

/-- [Corollary] The response bound certifies entire horizon-radical fibers. -/
theorem abs_sieveSeq_pmPowerDampedRealWeight_le_two_of_radical_lt_six_succ
    {ε : ℝ} (hε : 0 ≤ ε) {N k : ℕ}
    (hrN : horizonRadicalState N k < 6 * (N + 1)) :
    |sieveSeq N (pmPowerDampedRealWeight ε) k| ≤ 2 := by
  by_cases hN : N = 0
  · subst N
    simp [sieveSeq]
  rw [← sieveSeq_horizonRadicalState N k
    (pmPowerDampedRealWeight_eq_zero_of_not_squarefree ε)]
  have hr := horizonRadicalState_pos N k
  by_cases hr1 : horizonRadicalState N k = 1
  · rw [hr1, sieveSeq_pmPowerDampedRealWeight_eq_pmPowerDampedDivisorCoeff
      le_rfl (by omega : 1 ≤ N), pmPowerDampedDivisorCoeff_one, abs_one]
    norm_num
  · exact abs_sieveSeq_pmPowerDampedRealWeight_le_two_of_lt_six_succ hε (by omega) hrN

/-- [New formulation] Integer energy certifies every endpoint in the enlarged radical range. -/
theorem moebius_prefix_defect_nonpos_of_radical_lt_six_succ {N M : ℕ}
    (hrN : horizonRadicalState N (M + 1) < 6 * (N + 1)) :
    sieveRenormalizedPrefixDefect N M moebiusReal ≤ 0 := by
  apply moebius_prefix_defect_nonpos_of_abs_le_two
  simpa only [zero_damping_weight] using
    abs_sieveSeq_pmPowerDampedRealWeight_le_two_of_radical_lt_six_succ (le_refl 0) hrN

/-- [New formulation] Möbius prefix defects are nonpositive before 6(N+1). -/
theorem moebius_prefix_defect_nonpos_of_lt_six_succ {N M : ℕ}
    (hhi : M + 1 < 6 * (N + 1)) :
    sieveRenormalizedPrefixDefect N M moebiusReal ≤ 0 := by
  by_cases hM : M = 0
  · subst M
    simp [sieveRenormalizedPrefixDefect_eq_sum_mul_addDiff]
  · exact moebius_prefix_defect_nonpos_of_abs_le_two
      (abs_sieveSeq_moebiusReal_le_two_of_lt_six_succ (by omega) hhi)

/-- [Corollary] Positive powers of every certified base retain defect nonpositivity. -/
theorem moebius_power_checkpoint_defect_nonpos_of_lt_six_succ {N k m : ℕ}
    (hk : 2 ≤ k) (hhi : k < 6 * (N + 1)) (hm : 1 ≤ m) :
    sieveRenormalizedPrefixDefect N (k ^ m - 1) moebiusReal ≤ 0 := by
  have hkm : k ≤ k ^ m := by simpa using pow_le_pow_right₀ (by omega : 1 ≤ k) hm
  apply moebius_prefix_defect_nonpos_of_abs_le_two
  rw [Nat.sub_add_cancel (by omega : 1 ≤ k ^ m)]
  have hpow := sieveSeq_pmPowerDampedRealWeight_pow 0 N k hm
  rw [zero_damping_weight] at hpow
  rw [hpow]
  exact abs_sieveSeq_moebiusReal_le_two_of_lt_six_succ hk hhi

/-- [New formulation] Every power of the unit-envelope counterfamily has nonpositive defect. -/
theorem moebius_five_boundary_counterfamily_power_defect_nonpos {p m : ℕ}
    (hp : p.Prime) (h5 : 5 < p) (hm : 1 ≤ m) :
    sieveRenormalizedPrefixDefect (6 * p - 1) ((30 * p) ^ m - 1) moebiusReal ≤ 0 := by
  have hkm : 30 * p ≤ (30 * p) ^ m := by
    simpa using pow_le_pow_right₀ (by omega : 1 ≤ 30 * p) hm
  apply moebius_prefix_defect_nonpos_of_abs_le_two
  rw [Nat.sub_add_cancel (by omega : 1 ≤ (30 * p) ^ m),
    sieveSeq_moebiusReal_five_horizon_counterfamily_pow hp h5 hm]
  norm_num

/-- [Corollary] The first unit-envelope failures are still nonpositive-defect checkpoints. -/
theorem moebius_five_boundary_counterfamily_defect_nonpos {p : ℕ}
    (hp : p.Prime) (h5 : 5 < p) :
    sieveRenormalizedPrefixDefect (6 * p - 1) (30 * p - 1) moebiusReal ≤ 0 := by
  simpa only [pow_one] using moebius_five_boundary_counterfamily_power_defect_nonpos hp h5
    (le_refl 1)

/-- [Corollary] Any positive Möbius defect must have horizon radical at least 6(N+1). -/
theorem moebius_positive_defect_requires_large_radical {N M : ℕ}
    (h : 0 < sieveRenormalizedPrefixDefect N M moebiusReal) :
    6 * (N + 1) ≤ horizonRadicalState N (M + 1) := by
  by_contra hn
  have he := moebius_prefix_defect_nonpos_of_radical_lt_six_succ
    (by omega : horizonRadicalState N (M + 1) < 6 * (N + 1))
  linarith

end
end GaloisForLFunctions.TransHorizonIncidenceMechanics
