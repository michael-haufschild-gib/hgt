import GaloisForLFunctions.TransHorizonIncidenceMechanics.TransHorizonGramMatrixAndRadicalProjection
import GaloisForLFunctions.TransHorizonIncidenceMechanics.InterCheckpointSawtoothExcursionAndPronicSandwich
import GaloisForLFunctions.BezoutValuationIncidence.PostStepInactivePrefixAndSixDivisibilityPronicDefect

/-!
# Radical sawtooth invariance and defect dissipation at every horizon

Harmonic division preserves squarefree support, so both active sawtooth endpoints inherit
all-horizon divisor-multiplication and power invariance. The prefix defect instead remembers
additive Dirichlet energy: between ordered equal-response endpoints its change is exactly
minus half the intervening energy.

For nonnegative damping, the divisor coefficient and the absolute terminal weight have sum
at most one at every integer greater than one. First-octave reciprocity then bounds every
sieve response with base in `[2, 2N]` by one. Radical invariance transports this envelope to
all positive powers, proving nonpositive defects at arbitrarily large checkpoints.
-/

open Finset ArithmeticFunction
open GaloisForLFunctions.BezoutValuationIncidence RHTower
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-- Harmonic division preserves support on squarefree integers, including at zero. -/
theorem squarefree_support_harmonic {c : ℕ → ℝ}
    (hc : ∀ s : ℕ, ¬ Squarefree s → c s = 0) :
    ∀ s : ℕ, ¬ Squarefree s → c s / (s : ℝ) = 0 := by
  intro s hs
  rw [hc s hs, zero_div]

/-- Both active endpoints are invariant under multiplication by a positive divisor. -/
theorem activeCenteredSawtoothSum_mul_of_dvd_of_squarefree_support (N : ℕ) {c : ℕ → ℝ}
    (hc : ∀ s : ℕ, ¬ Squarefree s → c s = 0) {d k : ℕ}
    (hd : 1 ≤ d) (hk : 1 ≤ k) (hdk : d ∣ k) :
    activeCenteredSawtoothSum N c (d * k) (d * k - 1) =
        activeCenteredSawtoothSum N c k (k - 1) ∧
      activeCenteredSawtoothSum N c (d * k) (d * k) =
        activeCenteredSawtoothSum N c k k := by
  have hmul : d * k - 1 + 1 = d * k := Nat.sub_add_cancel (Nat.mul_pos hd hk)
  have hpred : k - 1 + 1 = k := Nat.sub_add_cancel hk
  constructor
  · have h₁ := activeCenteredSawtoothSum_at_pred_eq_half_sieveSeq_sub N c (d * k - 1)
    have h₂ := activeCenteredSawtoothSum_at_pred_eq_half_sieveSeq_sub N c (k - 1)
    rw [hmul, sieveSeq_mul_of_dvd_of_squarefree_support N hc hdk,
      sieveSeq_mul_of_dvd_of_squarefree_support N (squarefree_support_harmonic hc) hdk] at h₁
    rw [hpred] at h₂
    exact h₁.trans h₂.symm
  · have h₁ := activeCenteredSawtoothSum_at_self_eq_half_sieveSeq_sub N c (d * k - 1)
    have h₂ := activeCenteredSawtoothSum_at_self_eq_half_sieveSeq_sub N c (k - 1)
    rw [hmul, sieveSeq_mul_of_dvd_of_squarefree_support N hc hdk,
      sieveSeq_mul_of_dvd_of_squarefree_support N (squarefree_support_harmonic hc) hdk] at h₁
    rw [hpred] at h₂
    exact h₁.trans h₂.symm

/-- Both active endpoints are invariant under every positive power, at every horizon. -/
theorem activeCenteredSawtoothSum_pow_of_squarefree_support (N : ℕ) {c : ℕ → ℝ}
    (hc : ∀ s : ℕ, ¬ Squarefree s → c s = 0) {k m : ℕ} (hk : 1 ≤ k) (hm : 1 ≤ m) :
    activeCenteredSawtoothSum N c (k ^ m) (k ^ m - 1) =
        activeCenteredSawtoothSum N c k (k - 1) ∧
      activeCenteredSawtoothSum N c (k ^ m) (k ^ m) =
        activeCenteredSawtoothSum N c k k := by
  have hpow : k ^ m - 1 + 1 = k ^ m :=
    Nat.sub_add_cancel (show 0 < k ^ m from pow_pos hk m)
  have hpred : k - 1 + 1 = k := Nat.sub_add_cancel hk
  constructor
  · have h₁ := activeCenteredSawtoothSum_at_pred_eq_half_sieveSeq_sub N c (k ^ m - 1)
    have h₂ := activeCenteredSawtoothSum_at_pred_eq_half_sieveSeq_sub N c (k - 1)
    rw [hpow, sieveSeq_pow_of_squarefree_support N hc k hm,
      sieveSeq_pow_of_squarefree_support N (squarefree_support_harmonic hc) k hm] at h₁
    rw [hpred] at h₂
    exact h₁.trans h₂.symm
  · have h₁ := activeCenteredSawtoothSum_at_self_eq_half_sieveSeq_sub N c (k ^ m - 1)
    have h₂ := activeCenteredSawtoothSum_at_self_eq_half_sieveSeq_sub N c (k - 1)
    rw [hpow, sieveSeq_pow_of_squarefree_support N hc k hm,
      sieveSeq_pow_of_squarefree_support N (squarefree_support_harmonic hc) k hm] at h₁
    rw [hpred] at h₂
    exact h₁.trans h₂.symm

/-- Equal endpoint responses leave exactly the negative intervening Dirichlet energy. -/
theorem two_mul_sieveRenormalizedPrefixDefect_sub_of_sieveSeq_eq
    (N : ℕ) (c : ℕ → ℝ) {k l : ℕ} (hk : 2 ≤ k) (hkl : k ≤ l)
    (heq : sieveSeq N c l = sieveSeq N c k) :
    2 * (sieveRenormalizedPrefixDefect N (l - 1) c -
        sieveRenormalizedPrefixDefect N (k - 1) c) =
      -(∑ j ∈ Finset.Icc k (l - 1),
        (sieveSeq N c (j + 1) - sieveSeq N c j) ^ (2 : ℕ)) := by
  have h₁ := two_mul_sieveRenormalizedPrefixDefect_eq_neg_dirichlet_add_boundary
    N (by omega : 1 ≤ l - 1) c
  have h₂ := two_mul_sieveRenormalizedPrefixDefect_eq_neg_dirichlet_add_boundary
    N (by omega : 1 ≤ k - 1) c
  obtain ⟨hsplit, hdisj⟩ := Icc_one_split_at_rough hk (by omega : k - 1 ≤ l - 1)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ l), heq, hsplit, Finset.sum_union hdisj] at h₁
  rw [Nat.sub_add_cancel (by omega : 1 ≤ k)] at h₂
  linarith

/-- The defect is nonincreasing along ordered equal-response endpoints. -/
theorem sieveRenormalizedPrefixDefect_le_of_sieveSeq_eq
    (N : ℕ) (c : ℕ → ℝ) {k l : ℕ} (hk : 2 ≤ k) (hkl : k ≤ l)
    (heq : sieveSeq N c l = sieveSeq N c k) :
    sieveRenormalizedPrefixDefect N (l - 1) c ≤
      sieveRenormalizedPrefixDefect N (k - 1) c := by
  have h := two_mul_sieveRenormalizedPrefixDefect_sub_of_sieveSeq_eq N c hk hkl heq
  have hnonneg : 0 ≤ ∑ j ∈ Finset.Icc k (l - 1),
      (sieveSeq N c (j + 1) - sieveSeq N c j) ^ (2 : ℕ) :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  linarith

/-- Positive powers preserve the boundary response and expose the exact energy loss. -/
theorem two_mul_sieveRenormalizedPrefixDefect_pow_sub (N : ℕ) {c : ℕ → ℝ}
    (hc : ∀ s : ℕ, ¬ Squarefree s → c s = 0) {k m : ℕ} (hk : 2 ≤ k) (hm : 1 ≤ m) :
    2 * (sieveRenormalizedPrefixDefect N (k ^ m - 1) c -
        sieveRenormalizedPrefixDefect N (k - 1) c) =
      -(∑ j ∈ Finset.Icc k (k ^ m - 1),
        (sieveSeq N c (j + 1) - sieveSeq N c j) ^ (2 : ℕ)) := by
  have hkm : k ≤ k ^ m := by simpa using pow_le_pow_right₀ (by omega : 1 ≤ k) hm
  exact two_mul_sieveRenormalizedPrefixDefect_sub_of_sieveSeq_eq N c hk hkm
    (sieveSeq_pow_of_squarefree_support N hc k hm)

/-- Along positive exponents the defect decreases, with no restriction on the sieve horizon. -/
theorem sieveRenormalizedPrefixDefect_pow_antitone (N : ℕ) {c : ℕ → ℝ}
    (hc : ∀ s : ℕ, ¬ Squarefree s → c s = 0) {k a b : ℕ}
    (hk : 2 ≤ k) (ha : 1 ≤ a) (hab : a ≤ b) :
    sieveRenormalizedPrefixDefect N (k ^ b - 1) c ≤
      sieveRenormalizedPrefixDefect N (k ^ a - 1) c := by
  have hka : k ≤ k ^ a := by simpa using pow_le_pow_right₀ (by omega : 1 ≤ k) ha
  apply sieveRenormalizedPrefixDefect_le_of_sieveSeq_eq N c (hk.trans hka)
    (pow_le_pow_right₀ (by omega : 1 ≤ k) hab)
  rw [sieveSeq_pow_of_squarefree_support N hc k (ha.trans hab),
    sieveSeq_pow_of_squarefree_support N hc k ha]

/-- Nonnegative damping couples the full divisor response and the terminal weight inside
one unit of mass. A prime divisor bounds both complementary terms. -/
theorem pmPowerDampedDivisorCoeff_add_abs_weight_le_one {ε : ℝ} (hε : 0 ≤ ε)
    {k : ℕ} (hk : 2 ≤ k) :
    pmPowerDampedDivisorCoeff ε k + |pmPowerDampedRealWeight ε k| ≤ 1 := by
  obtain ⟨p, hp, hpk⟩ := Nat.exists_prime_and_dvd (by omega : k ≠ 1)
  have hτ := pmPowerDampedDivisorCoeff_le_of_dvd hε hpk (by omega : k ≠ 0)
  rw [pmPowerDampedDivisorCoeff_eq_prod ε hp.ne_zero, hp.primeFactors,
    Finset.prod_singleton] at hτ
  have hμ : |moebiusReal k| ≤ 1 := by
    unfold moebiusReal
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := k))
  have hw : |pmPowerDampedRealWeight ε k| ≤ (k : ℝ) ^ (-ε) := by
    simpa only [pmPowerDampedRealWeight, abs_mul,
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg k) (-ε)), one_mul] using
      mul_le_mul_of_nonneg_right hμ (Real.rpow_nonneg (Nat.cast_nonneg k) (-ε))
  have hpow : (k : ℝ) ^ (-ε) ≤ (p : ℝ) ^ (-ε) :=
    Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hp.pos)
      (by exact_mod_cast Nat.le_of_dvd (by omega : 0 < k) hpk) (by linarith)
  linarith

/-- The whole initial octave, including its trans-horizon half, has a unit response envelope. -/
theorem abs_sieveSeq_pmPowerDampedRealWeight_le_one_of_le_two_mul {ε : ℝ}
    (hε : 0 ≤ ε) {N k : ℕ} (hk : 2 ≤ k) (hkN : k ≤ 2 * N) :
    |sieveSeq N (pmPowerDampedRealWeight ε) k| ≤ 1 := by
  by_cases hsub : k ≤ N
  · rw [sieveSeq_pmPowerDampedRealWeight_eq_pmPowerDampedDivisorCoeff (by omega) hsub,
      abs_of_nonneg (pmPowerDampedDivisorCoeff_nonneg hε k)]
    exact pmPowerDampedDivisorCoeff_le_one hε k
  · have hfirst : sieveSeq N (pmPowerDampedRealWeight ε) k =
        pmPowerDampedDivisorCoeff ε k - pmPowerDampedRealWeight ε k :=
      sieveSeq_pmPowerDampedRealWeight_first_octave (by omega) hkN
    rw [hfirst]
    calc
      |pmPowerDampedDivisorCoeff ε k - pmPowerDampedRealWeight ε k| ≤
          |pmPowerDampedDivisorCoeff ε k| + |pmPowerDampedRealWeight ε k| := abs_sub _ _
      _ = pmPowerDampedDivisorCoeff ε k + |pmPowerDampedRealWeight ε k| := by
        rw [abs_of_nonneg (pmPowerDampedDivisorCoeff_nonneg hε k)]
      _ ≤ 1 := pmPowerDampedDivisorCoeff_add_abs_weight_le_one hε hk

/-- The base envelope propagates to every positive power, however far beyond the horizon. -/
theorem sieveSeq_pmPowerDampedRealWeight_pow_sq_le_one {ε : ℝ} (hε : 0 ≤ ε)
    {N k m : ℕ} (hk : 2 ≤ k) (hkN : k ≤ 2 * N) (hm : 1 ≤ m) :
    sieveSeq N (pmPowerDampedRealWeight ε) (k ^ m) ^ (2 : ℕ) ≤ 1 := by
  rw [sieveSeq_pmPowerDampedRealWeight_pow ε N k hm, sq_le_one_iff_abs_le_one]
  exact abs_sieveSeq_pmPowerDampedRealWeight_le_one_of_le_two_mul hε hk hkN

/-- Every positive power of a base in `[2,2N]` is a nonpositive damped-defect checkpoint. -/
theorem sieveRenormalizedPrefixDefect_pmPowerDampedRealWeight_pow_nonpos {ε : ℝ}
    (hε : 0 ≤ ε) {N k m : ℕ} (hk : 2 ≤ k) (hkN : k ≤ 2 * N) (hm : 1 ≤ m) :
    sieveRenormalizedPrefixDefect N (k ^ m - 1) (pmPowerDampedRealWeight ε) ≤ 0 := by
  have hkm : k ≤ k ^ m := by simpa using pow_le_pow_right₀ (by omega : 1 ≤ k) hm
  have hpol := two_mul_sieveRenormalizedPrefixDefect_eq_neg_dirichlet_add_boundary
    N (by omega : 1 ≤ k ^ m - 1) (pmPowerDampedRealWeight ε)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ k ^ m),
    sieveSeq_pmPowerDampedRealWeight_eq_pmPowerDampedDivisorCoeff le_rfl (by omega : 1 ≤ N),
    pmPowerDampedDivisorCoeff_one, one_pow] at hpol
  have hbnd := sieveSeq_pmPowerDampedRealWeight_pow_sq_le_one hε hk hkN hm
  have henergy : 0 ≤ ∑ j ∈ Finset.Icc 1 (k ^ m - 1),
      (sieveSeq N (pmPowerDampedRealWeight ε) (j + 1) -
        sieveSeq N (pmPowerDampedRealWeight ε) j) ^ (2 : ℕ) :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  linarith

/-- Möbius weights are the zero-damping case of the all-power checkpoint theorem. -/
theorem sieveRenormalizedPrefixDefect_moebiusReal_pow_nonpos {N k m : ℕ}
    (hk : 2 ≤ k) (hkN : k ≤ 2 * N) (hm : 1 ≤ m) :
    sieveRenormalizedPrefixDefect N (k ^ m - 1) moebiusReal ≤ 0 := by
  have hw : pmPowerDampedRealWeight 0 = moebiusReal := by
    funext d
    simp [pmPowerDampedRealWeight]
  simpa only [hw] using
    sieveRenormalizedPrefixDefect_pmPowerDampedRealWeight_pow_nonpos (le_refl 0) hk hkN hm

/-- When a rough checkpoint precedes the power, its already nonpositive defect is an
upper bound for the new checkpoint. -/
theorem sieveRenormalizedPrefixDefect_pmPowerDampedRealWeight_pow_le_rough_checkpoint
    {ε : ℝ} (hε : 0 ≤ ε) {N k m r : ℕ} (hk : 2 ≤ k) (hkN : k ≤ 2 * N)
    (hm : 1 ≤ m) (hr : 2 ≤ r) (hrough : ∀ d : ℕ, d ∣ r → d ≤ N → d = 1)
    (hrpow : r ≤ k ^ m) :
    sieveRenormalizedPrefixDefect N (k ^ m - 1) (pmPowerDampedRealWeight ε) ≤
        sieveRenormalizedPrefixDefect N (r - 1) (pmPowerDampedRealWeight ε) ∧
      sieveRenormalizedPrefixDefect N (k ^ m - 1) (pmPowerDampedRealWeight ε) ≤ 0 := by
  apply sieveRenormalizedPrefixDefect_le_rough_checkpoint_of_sq_le
    N (pmPowerDampedRealWeight ε) hr hrough (by omega)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ k ^ m),
    sieveSeq_pmPowerDampedRealWeight_eq_pmPowerDampedDivisorCoeff le_rfl (by omega : 1 ≤ N),
    pmPowerDampedDivisorCoeff_one, one_pow]
  exact sieveSeq_pmPowerDampedRealWeight_pow_sq_le_one hε hk hkN hm

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
