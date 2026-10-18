import GaloisForLFunctions.TransHorizonIncidenceMechanics.ShortWindowCorrelationDefectAndIsoStateClassification

/-!
# Two-prime deletion and the complete third-band envelope

Classical baseline: multiplicativity of μ(n)n^(-ε), the divisor-product identity
τ_ε(n) = ∏_{p ∣ n}(1-p^(-ε)), complementary-divisor splitting, and discrete polarization.
The divisor-observation and shifted-correlation frameworks are those of [TH10]
(https://arxiv.org/abs/1009.5281) and [CMS16] (https://arxiv.org/abs/1612.03136).

Equivalent classical formulation: for distinct primes p,q, put
F_p(u)=1 if p∣u and F_p(u)=1-p^(-ε) otherwise, and A=F_p(u)F_q(u). Then
τ(pqu)-c(pqu)-c(qu)-c(pu)=Aτ(u)+(1-A)c(u).
For ε≥0 and u≥2, its absolute value is at most max(A,1-A)≤1.

This convex identity closes the missing two-and-three-divisible case in 3N<k≤4N.
Consequently |s_N(c_ε,k)|≤1 for every 2≤k≤4N, with no parity/coprimality exclusion.
Radical invariance transports the certificate to arbitrary positive powers and
entire certified radical fibers. Prefix and rough-start short-window defects then
satisfy 2D≤-E≤0. Zero damping gives literal Möbius-weight corollaries.

Classification: New formulation, with Known/Corollary constituents labeled below.
No external novelty claim; no conclusion for unbounded radical representatives.
-/

open Finset ArithmeticFunction
open GaloisForLFunctions.BiScaleUncertainty GaloisForLFunctions.BezoutValuationIncidence
open RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-- [Known] Local Euler factor created by adjoining a prime already present or absent. -/
def dampedPrimeDeletionFactor (ε : ℝ) (p u : ℕ) : ℝ :=
  if p ∣ u then 1 else 1 - (p : ℝ) ^ (-ε)

/-- [Corollary] Under nonnegative damping the local factor belongs to the unit interval. -/
theorem dampedPrimeDeletionFactor_mem_unit {ε : ℝ} (hε : 0 ≤ ε)
    {p : ℕ} (hp : p.Prime) (u : ℕ) :
    0 ≤ dampedPrimeDeletionFactor ε p u ∧ dampedPrimeDeletionFactor ε p u ≤ 1 := by
  have h0 := Real.rpow_nonneg (Nat.cast_nonneg p) (-ε)
  have h1 : (p : ℝ) ^ (-ε) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hp.one_lt.le) (by linarith)
  unfold dampedPrimeDeletionFactor
  split_ifs <;> constructor <;> linarith

/-- [Known] The prime Euler factor also controls the signed terminal coefficient. -/
theorem pmPowerDampedRealWeight_prime_mul_eq_factor_sub_one (ε : ℝ) {p : ℕ}
    (hp : p.Prime) (u : ℕ) :
    pmPowerDampedRealWeight ε (p * u) =
      (dampedPrimeDeletionFactor ε p u - 1) * pmPowerDampedRealWeight ε u := by
  rw [pmPowerDampedRealWeight_prime_mul_switch ε hp u]
  unfold dampedPrimeDeletionFactor
  split_ifs <;> ring

/-- [Known] A distinct prime does not alter the presence test defining the factor. -/
theorem dampedPrimeDeletionFactor_mul_distinct_prime (ε : ℝ) {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (u : ℕ) :
    dampedPrimeDeletionFactor ε p (q * u) = dampedPrimeDeletionFactor ε p u := by
  have hn : ¬ p ∣ q := by
    intro h
    rcases (Nat.dvd_prime hq).mp h with h | h
    · exact hp.ne_one h
    · exact hpq h
  simp only [dampedPrimeDeletionFactor, hp.dvd_mul, hn, false_or]

/-- [New formulation] Deleting the three nonempty two-prime coefficient channels
leaves a convex combination of the full response and terminal coefficient at u. -/
theorem pmPowerDamped_two_prime_deleted_response (ε : ℝ) {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (u : ℕ) :
    pmPowerDampedDivisorCoeff ε (p * (q * u)) -
        pmPowerDampedRealWeight ε (p * (q * u)) -
        pmPowerDampedRealWeight ε (q * u) - pmPowerDampedRealWeight ε (p * u) =
      (dampedPrimeDeletionFactor ε p u * dampedPrimeDeletionFactor ε q u) *
        pmPowerDampedDivisorCoeff ε u +
      (1 - dampedPrimeDeletionFactor ε p u * dampedPrimeDeletionFactor ε q u) *
        pmPowerDampedRealWeight ε u := by
  rw [pmPowerDampedDivisorCoeff_prime_mul ε hp (q * u),
    pmPowerDampedDivisorCoeff_prime_mul ε hq u]
  change dampedPrimeDeletionFactor ε p (q * u) *
      (dampedPrimeDeletionFactor ε q u * pmPowerDampedDivisorCoeff ε u) - _ - _ - _ = _
  rw [pmPowerDampedRealWeight_prime_mul_eq_factor_sub_one ε hp (q * u),
    dampedPrimeDeletionFactor_mul_distinct_prime ε hp hq hpq u,
    pmPowerDampedRealWeight_prime_mul_eq_factor_sub_one ε hq u,
    pmPowerDampedRealWeight_prime_mul_eq_factor_sub_one ε hp u]
  ring

/-- [Corollary] The two-prime mixing parameter is between zero and one. -/
theorem dampedPrimeDeletionFactor_mul_mem_unit {ε : ℝ} (hε : 0 ≤ ε)
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (u : ℕ) :
    0 ≤ dampedPrimeDeletionFactor ε p u * dampedPrimeDeletionFactor ε q u ∧
      dampedPrimeDeletionFactor ε p u * dampedPrimeDeletionFactor ε q u ≤ 1 := by
  obtain ⟨hp0, hp1⟩ := dampedPrimeDeletionFactor_mem_unit hε hp u
  obtain ⟨hq0, hq1⟩ := dampedPrimeDeletionFactor_mem_unit hε hq u
  exact ⟨mul_nonneg hp0 hq0, (mul_le_mul_of_nonneg_right hp1 hq0).trans (by simpa)⟩

/-- [New formulation] The joint deletion obeys the stronger max-factor bound
inherited from the full-response/terminal-coefficient mass budget. -/
theorem abs_pmPowerDamped_two_prime_deleted_response_le_max {ε : ℝ} (hε : 0 ≤ ε)
    {p q u : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hu : 2 ≤ u) :
    |pmPowerDampedDivisorCoeff ε (p * (q * u)) -
        pmPowerDampedRealWeight ε (p * (q * u)) -
        pmPowerDampedRealWeight ε (q * u) - pmPowerDampedRealWeight ε (p * u)| ≤
      max (dampedPrimeDeletionFactor ε p u * dampedPrimeDeletionFactor ε q u)
        (1 - dampedPrimeDeletionFactor ε p u * dampedPrimeDeletionFactor ε q u) := by
  rw [pmPowerDamped_two_prime_deleted_response ε hp hq hpq u]
  let A := dampedPrimeDeletionFactor ε p u * dampedPrimeDeletionFactor ε q u
  obtain ⟨hA0, hA1⟩ := dampedPrimeDeletionFactor_mul_mem_unit hε hp hq u
  have hτ := pmPowerDampedDivisorCoeff_nonneg hε u
  have hmass := pmPowerDampedDivisorCoeff_add_abs_weight_le_one hε hu
  have hmax : 0 ≤ max A (1 - A) := le_trans hA0 (le_max_left _ _)
  calc
    _ ≤ |A * pmPowerDampedDivisorCoeff ε u| +
        |(1 - A) * pmPowerDampedRealWeight ε u| := abs_add_le _ _
    _ = A * pmPowerDampedDivisorCoeff ε u +
        (1 - A) * |pmPowerDampedRealWeight ε u| := by
      rw [abs_mul A, abs_mul (1 - A), abs_of_nonneg hA0,
        abs_of_nonneg (sub_nonneg.mpr hA1), abs_of_nonneg hτ]
    _ ≤ max A (1 - A) * (pmPowerDampedDivisorCoeff ε u +
        |pmPowerDampedRealWeight ε u|) := by
      have hleft := mul_le_mul_of_nonneg_right (le_max_left A (1 - A)) hτ
      have hright := mul_le_mul_of_nonneg_right (le_max_right A (1 - A))
        (abs_nonneg (pmPowerDampedRealWeight ε u))
      nlinarith
    _ ≤ max A (1 - A) := by
      simpa using mul_le_mul_of_nonneg_left hmass hmax

/-- [Corollary] The two-prime deletion preserves the unit envelope. -/
theorem abs_pmPowerDamped_two_prime_deleted_response_le_one {ε : ℝ} (hε : 0 ≤ ε)
    {p q u : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hu : 2 ≤ u) :
    |pmPowerDampedDivisorCoeff ε (p * (q * u)) -
        pmPowerDampedRealWeight ε (p * (q * u)) -
        pmPowerDampedRealWeight ε (q * u) - pmPowerDampedRealWeight ε (p * u)| ≤ 1 := by
  apply (abs_pmPowerDamped_two_prime_deleted_response_le_max hε hp hq hpq hu).trans
  obtain ⟨hA0, hA1⟩ := dampedPrimeDeletionFactor_mul_mem_unit hε hp hq u
  exact max_le hA1 (by linarith)

/-- [New formulation] The complete third band has a unit envelope; no small-prime
exclusion is needed, including endpoints divisible by both two and three. -/
theorem abs_sieveSeq_pmPowerDampedRealWeight_full_third_band_le_one {ε : ℝ}
    (hε : 0 ≤ ε) {N k : ℕ} (hlo : 3 * N + 1 ≤ k) (hhi : k ≤ 4 * N) :
    |sieveSeq N (pmPowerDampedRealWeight ε) k| ≤ 1 := by
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
      rw [sieveSeq_pmPowerDampedRealWeight_third_band_eq ε hlo hhi,
        if_pos (dvd_mul_right 2 (3 * u)), if_pos h3',
        Nat.mul_div_cancel_left (3 * u) (by omega : 0 < 2), hdiv3]
      exact abs_pmPowerDamped_two_prime_deleted_response_le_one hε
        Nat.prime_two Nat.prime_three (by omega) (by omega)
    · exact abs_sieveSeq_pmPowerDampedRealWeight_third_band_le_one hε hlo hhi (Or.inr h3)
  · exact abs_sieveSeq_pmPowerDampedRealWeight_third_band_le_one hε hlo hhi (Or.inl h2)

/-- [New formulation] The full initial range through 4N has a unit damped envelope. -/
theorem abs_sieveSeq_pmPowerDampedRealWeight_le_one_of_le_four_mul {ε : ℝ}
    (hε : 0 ≤ ε) {N k : ℕ} (hk : 2 ≤ k) (hhi : k ≤ 4 * N) :
    |sieveSeq N (pmPowerDampedRealWeight ε) k| ≤ 1 := by
  by_cases hlo : k ≤ 3 * N
  · exact abs_sieveSeq_pmPowerDampedRealWeight_le_one_of_le_three_mul hε hk hlo
  · exact abs_sieveSeq_pmPowerDampedRealWeight_full_third_band_le_one hε (by omega) hhi


/-- [Corollary] The entire radical fiber inherits the 4N certificate, regardless
of the size of the observation integer. -/
theorem abs_sieveSeq_pmPowerDampedRealWeight_le_one_of_radical_le_four_mul
    {ε : ℝ} (hε : 0 ≤ ε) {N k : ℕ}
    (hrN : horizonRadicalState N k ≤ 4 * N) :
    |sieveSeq N (pmPowerDampedRealWeight ε) k| ≤ 1 := by
  rw [← sieveSeq_horizonRadicalState N k
    (pmPowerDampedRealWeight_eq_zero_of_not_squarefree ε)]
  have hr := horizonRadicalState_pos N k
  by_cases hr1 : horizonRadicalState N k = 1
  · rw [hr1, sieveSeq_pmPowerDampedRealWeight_eq_pmPowerDampedDivisorCoeff
      le_rfl (by omega : 1 ≤ N), pmPowerDampedDivisorCoeff_one, abs_one]
  · exact abs_sieveSeq_pmPowerDampedRealWeight_le_one_of_le_four_mul hε (by omega) hrN

/-- [Corollary] Every positive power of every base in [2,4N] has a unit response. -/
theorem abs_sieveSeq_pmPowerDampedRealWeight_pow_le_four_mul {ε : ℝ}
    (hε : 0 ≤ ε) {N k m : ℕ} (hk : 2 ≤ k) (hhi : k ≤ 4 * N) (hm : 1 ≤ m) :
    |sieveSeq N (pmPowerDampedRealWeight ε) (k ^ m)| ≤ 1 := by
  rw [sieveSeq_pmPowerDampedRealWeight_pow ε N k hm]
  exact abs_sieveSeq_pmPowerDampedRealWeight_le_one_of_le_four_mul hε hk hhi

/-- [New formulation] A radical representative at most 4N certifies prefix
dissipation with the complete Dirichlet-energy term. -/
theorem sieveRenormalizedPrefixDefect_pmPowerDampedRealWeight_radical_four_mul_bound
    {ε : ℝ} (hε : 0 ≤ ε) {N M : ℕ} (hM : 1 ≤ M)
    (hrN : horizonRadicalState N (M + 1) ≤ 4 * N) :
    2 * sieveRenormalizedPrefixDefect N M (pmPowerDampedRealWeight ε) ≤
        -(∑ k ∈ Icc 1 M, (sieveSeq N (pmPowerDampedRealWeight ε) (k + 1) -
          sieveSeq N (pmPowerDampedRealWeight ε) k) ^ (2 : ℕ)) ∧
      sieveRenormalizedPrefixDefect N M (pmPowerDampedRealWeight ε) ≤ 0 := by
  have hr := horizonRadicalState_pos N (M + 1)
  have hpol := two_mul_sieveRenormalizedPrefixDefect_eq_neg_dirichlet_add_boundary
    N hM (pmPowerDampedRealWeight ε)
  rw [sieveSeq_pmPowerDampedRealWeight_eq_pmPowerDampedDivisorCoeff
    le_rfl (by omega : 1 ≤ N), pmPowerDampedDivisorCoeff_one, one_pow] at hpol
  have hsq := (sq_le_one_iff_abs_le_one _).mpr
    (abs_sieveSeq_pmPowerDampedRealWeight_le_one_of_radical_le_four_mul hε hrN)
  have henergy : 0 ≤ ∑ k ∈ Icc 1 M,
      (sieveSeq N (pmPowerDampedRealWeight ε) (k + 1) -
        sieveSeq N (pmPowerDampedRealWeight ε) k) ^ (2 : ℕ) :=
    sum_nonneg fun _ _ => sq_nonneg _
  exact ⟨by linarith, by linarith⟩

/-- [Corollary] Every prefix with successor at most 4N dissipates, without parity
or coprimality exclusions. -/
theorem sieveRenormalizedPrefixDefect_pmPowerDampedRealWeight_full_four_mul_bound
    {ε : ℝ} (hε : 0 ≤ ε) {N M : ℕ} (hM : 1 ≤ M) (hhi : M + 1 ≤ 4 * N) :
    2 * sieveRenormalizedPrefixDefect N M (pmPowerDampedRealWeight ε) ≤
        -(∑ k ∈ Icc 1 M, (sieveSeq N (pmPowerDampedRealWeight ε) (k + 1) -
          sieveSeq N (pmPowerDampedRealWeight ε) k) ^ (2 : ℕ)) ∧
      sieveRenormalizedPrefixDefect N M (pmPowerDampedRealWeight ε) ≤ 0 := by
  exact sieveRenormalizedPrefixDefect_pmPowerDampedRealWeight_radical_four_mul_bound
    hε hM ((Nat.le_of_dvd (by omega) (horizonRadicalState_dvd N (M + 1))).trans hhi)

/-- [Corollary] The complete 4N base range gives arbitrarily distant power
checkpoints with the same quantitative dissipation guarantee. -/
theorem sieveRenormalizedPrefixDefect_pmPowerDampedRealWeight_pow_four_mul_bound
    {ε : ℝ} (hε : 0 ≤ ε) {N k m : ℕ} (hk : 2 ≤ k) (hhi : k ≤ 4 * N) (hm : 1 ≤ m) :
    2 * sieveRenormalizedPrefixDefect N (k ^ m - 1) (pmPowerDampedRealWeight ε) ≤
        -(∑ j ∈ Icc 1 (k ^ m - 1), (sieveSeq N (pmPowerDampedRealWeight ε) (j + 1) -
          sieveSeq N (pmPowerDampedRealWeight ε) j) ^ (2 : ℕ)) ∧
      sieveRenormalizedPrefixDefect N (k ^ m - 1) (pmPowerDampedRealWeight ε) ≤ 0 := by
  have hkm : k ≤ k ^ m := by simpa using pow_le_pow_right₀ (by omega : 1 ≤ k) hm
  apply sieveRenormalizedPrefixDefect_pmPowerDampedRealWeight_radical_four_mul_bound
    hε (by omega : 1 ≤ k ^ m - 1)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ k ^ m), horizonRadicalState_pow N k hm]
  exact (Nat.le_of_dvd (by omega) (horizonRadicalState_dvd N k)).trans hhi

private theorem zero_damping_weight : pmPowerDampedRealWeight 0 = moebiusReal := by
  funext d
  simp [pmPowerDampedRealWeight]

/-- [Corollary] Literal Möbius weights have nonpositive defects throughout 4N. -/
theorem sieveRenormalizedPrefixDefect_moebiusReal_full_four_mul_nonpos {N M : ℕ}
    (hM : 1 ≤ M) (hhi : M + 1 ≤ 4 * N) :
    sieveRenormalizedPrefixDefect N M moebiusReal ≤ 0 := by
  simpa only [zero_damping_weight] using
    (sieveRenormalizedPrefixDefect_pmPowerDampedRealWeight_full_four_mul_bound
      (le_refl 0) hM hhi).2

/-- [Corollary] Literal Möbius weights inherit the complete 4N power certificate. -/
theorem sieveRenormalizedPrefixDefect_moebiusReal_pow_four_mul_nonpos {N k m : ℕ}
    (hk : 2 ≤ k) (hhi : k ≤ 4 * N) (hm : 1 ≤ m) :
    sieveRenormalizedPrefixDefect N (k ^ m - 1) moebiusReal ≤ 0 := by
  simpa only [zero_damping_weight] using
    (sieveRenormalizedPrefixDefect_pmPowerDampedRealWeight_pow_four_mul_bound
      (le_refl 0) hk hhi hm).2

/-- [Corollary] Literal Möbius defects are nonpositive on every certified radical fiber. -/
theorem sieveRenormalizedPrefixDefect_moebiusReal_radical_four_mul_nonpos {N M : ℕ}
    (hM : 1 ≤ M) (hrN : horizonRadicalState N (M + 1) ≤ 4 * N) :
    sieveRenormalizedPrefixDefect N M moebiusReal ≤ 0 := by
  simpa only [zero_damping_weight] using
    (sieveRenormalizedPrefixDefect_pmPowerDampedRealWeight_radical_four_mul_bound
      (le_refl 0) hM hrN).2

/-- [New formulation] Rough-start short windows dissipate whenever the right
endpoint belongs to a radical fiber certified by the full 4N envelope. -/
theorem shortWindowRenormalizedDefect_pmPowerDampedRealWeight_rough_start_radical_four_mul
    {ε : ℝ} (hε : 0 ≤ ε) {N M₀ M : ℕ}
    (hstart : IsTransHorizonRough N (M₀ + 1))
    (hrN : horizonRadicalState N (M₀ + M + 1) ≤ 4 * N) :
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
    (abs_sieveSeq_pmPowerDampedRealWeight_le_one_of_radical_le_four_mul hε hrN)
  rw [hinit, one_pow] at hpol
  have henergy : 0 ≤ shortWindowDirichletEnergy N M₀ M (pmPowerDampedRealWeight ε) :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  exact ⟨by linarith, by linarith⟩

/-- [Corollary] The full 4N short-window theorem has no small-prime exclusions. -/
theorem shortWindowRenormalizedDefect_pmPowerDampedRealWeight_rough_start_full_four_mul
    {ε : ℝ} (hε : 0 ≤ ε) {N M₀ M : ℕ}
    (hstart : IsTransHorizonRough N (M₀ + 1)) (hhi : M₀ + M + 1 ≤ 4 * N) :
    2 * shortWindowRenormalizedDefect N M₀ M (pmPowerDampedRealWeight ε) ≤
        -shortWindowDirichletEnergy N M₀ M (pmPowerDampedRealWeight ε) ∧
      shortWindowRenormalizedDefect N M₀ M (pmPowerDampedRealWeight ε) ≤ 0 := by
  exact shortWindowRenormalizedDefect_pmPowerDampedRealWeight_rough_start_radical_four_mul
    hε hstart ((Nat.le_of_dvd (by omega)
      (horizonRadicalState_dvd N (M₀ + M + 1))).trans hhi)

end
end GaloisForLFunctions.TransHorizonIncidenceMechanics
