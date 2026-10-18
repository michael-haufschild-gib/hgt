import GaloisForLFunctions.BezoutValuationIncidence.ActiveDeletedMartingaleAndShiftedEulerConvergence
import GaloisForLFunctions.BezoutValuationIncidence.PrimeTailCalibrationAndMobiusDefect

/-!
# Pillar V: Trans-Horizon Martingale Variance Telescope & Prime Checkpoint Laws (`TransHorizonMartingaleTelescopeAndPrimeCheckpoints`)

In `BezoutValuationIncidence` (`ActiveDeletedMartingaleAndShiftedEulerConvergence`), the
**Active-Deleted Martingale Identity**
$$W_{N,c}(n + 1)^2 - W_{N,c}(n)^2 =
  \bigl(s_{N,c}(n + 1) - Y_{N,c}(1)\bigr)\bigl(s_{N, c/d}(n + 1) - Y_{N,c}(1)\bigr) +
  2\bigl(s_{N,c}(n + 1) - Y_{N,c}(1)\bigr)\,I_{N,c}(n + 1, n)$$
was evaluated step-by-step and specialized to the sub-horizon regime `n + 1 ≤ N`.

In this fifth foundational pillar of **Trans-Horizon Arithmetic–Archimedean Incidence Mechanics**,
we establish the global trans-horizon martingale telescope for arbitrary `M ≥ 1` and prove the
exact **Prime Checkpoint Laws** across every trans-horizon prime step `p - 1 ↦ p` (`p > N`):

## Core Main Theorems (100% Unconditional)

1. **Global Trans-Horizon Active-Deleted Martingale Telescope & Variance Floor
   (`weightedCenteredSawtoothSum_sq_sub_one_eq_active_deleted_add_inactive`,
   `active_deleted_add_inactive_martingale_ge_neg_initial_sq`)**:
   For every cutoff `N : ℕ`, weight `c : ℕ → ℝ`, and prefix `M ≥ 1`:
   $$W_{N,c}(M)^2 - W_{N,c}(1)^2 =
     \sum_{n=1}^{M-1} \bigl(s_{N,c}(n + 1) - Y_{N,c}(1)\bigr)\bigl(s_{N,c/d}(n + 1) - Y_{N,c}(1)\bigr) +
     2 \sum_{n=1}^{M-1} \bigl(s_{N,c}(n + 1) - Y_{N,c}(1)\bigr)\,I_{N,c}(n + 1, n),$$
   and consequently the combined active-deleted diagonal + inactive martingale sum is bounded below
   by `-W_{N,c}(1)²` at **every** trans-horizon scale `M ≥ 1`.

2. **Trans-Horizon Prime Step Invariance (`sieveSeq_harmonic_prime_of_gt`,
   `activeCenteredSawtoothSum_prime_of_gt_eq_zero`,
   `inactiveCenteredSawtoothSum_prime_of_gt_eq_weighted`)**:
   For every prime `p > N` and weight `c : ℕ → ℝ`:
   - Both `sieveSeq N c p` and `sieveSeq N (fun d => c d / d) p` equal `sieveSeq N c 1`.
   - The active sawtooth components `activeCenteredSawtoothSum N c p (p - 1)` and
     `activeCenteredSawtoothSum N c p p` vanish identically.
   - Therefore, at every trans-horizon prime `p > N`, the full sawtooth state is **100% inactive**:
     $$I_{N,c}(p, p - 1) = W_{N,c}(p - 1) \quad\text{and}\quad I_{N,c}(p, p) = W_{N,c}(p).$$

3. **Pure-Square Active-Deleted Diagonal & Constant Drift Across Trans-Horizon Primes
   (`weightedCenteredSawtoothSum_prime_sub_pred_of_gt`,
   `weightedCenteredSawtoothSum_prime_sq_sub_pred_sq_of_gt`)**:
   Across every trans-horizon prime step `p - 1 ↦ p` (`p > N`):
   - The forward increment is constant across all primes `p > N`:
     $$W_{N,c}(p) - W_{N,c}(p - 1) = s_{N,c}(1) - Y_{N,c}(1).$$
   - The active-deleted diagonal term is the exact non-negative square `(s_{N,c}(1) - Y_{N,c}(1))²`,
     and the square increment reduces to:
     $$W_{N,c}(p)^2 - W_{N,c}(p - 1)^2 =
       \bigl(s_{N,c}(1) - Y_{N,c}(1)\bigr)^2 +
       2\bigl(s_{N,c}(1) - Y_{N,c}(1)\bigr)\,W_{N,c}(p - 1).$$
-/

open Finset ArithmeticFunction
open GaloisForLFunctions.BiScaleUncertainty GaloisForLFunctions.BezoutValuationIncidence
open RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ## §1. Global Trans-Horizon Active-Deleted Martingale Telescope & Variance Floor -/

/-- Telescoping sum on `Finset.Icc 1 K` (`K : ℕ`, possibly `0`):
`∑ n ∈ Icc 1 K, (f (n + 1) - f n) = f (K + 1) - f 1`. -/
theorem sum_Icc_one_telescope (K : ℕ) (f : ℕ → ℝ) :
    (∑ n ∈ Finset.Icc 1 K, (f (n + 1) - f n)) = f (K + 1) - f 1 := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ K + 1), ih]
    ring

/-- **Global Trans-Horizon Active-Deleted Martingale Telescope
(`weightedCenteredSawtoothSum_sq_sub_one_eq_active_deleted_add_inactive`):**
For every cutoff `N : ℕ`, weight `c : ℕ → ℝ`, and `M ≥ 1`:
`W_{N,c}(M)² - W_{N,c}(1)²` equals the sum over `n ∈ [1, M - 1]` of the active-deleted shifted
diagonal product plus twice the purely inactive predictable martingale product. -/
theorem weightedCenteredSawtoothSum_sq_sub_one_eq_active_deleted_add_inactive
    (N : ℕ) (c : ℕ → ℝ) {M : ℕ} (hM : 1 ≤ M) :
    weightedCenteredSawtoothSum N c M ^ (2 : ℕ) -
      weightedCenteredSawtoothSum N c 1 ^ (2 : ℕ) =
      (∑ n ∈ Finset.Icc 1 (M - 1),
        (sieveSeq N c (n + 1) - selbergMultiplesCoord N c 1) *
          (sieveSeq N (fun d => c d / (d : ℝ)) (n + 1) - selbergMultiplesCoord N c 1)) +
      2 * ∑ n ∈ Finset.Icc 1 (M - 1),
        (sieveSeq N c (n + 1) - selbergMultiplesCoord N c 1) *
          inactiveCenteredSawtoothSum N c (n + 1) n := by
  have htel := sum_Icc_one_telescope (M - 1)
    (fun n => weightedCenteredSawtoothSum N c n ^ (2 : ℕ))
  rw [Nat.sub_add_cancel hM] at htel
  rw [← htel, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [weightedCenteredSawtoothSum_succ_sq_sub_sq_eq_shifted_diagonal_add_inactive_martingale]
  ring

/-- **Universal Trans-Horizon Variance Floor
(`active_deleted_add_inactive_martingale_ge_neg_initial_sq`):**
For every `N : ℕ`, weight `c : ℕ → ℝ`, and `M ≥ 1`, because `W_{N,c}(M)² ≥ 0`, the cumulative sum
of the active-deleted shifted diagonal and twice the inactive martingale increment is bounded below
by `-W_{N,c}(1)²`. -/
theorem active_deleted_add_inactive_martingale_ge_neg_initial_sq
    (N : ℕ) (c : ℕ → ℝ) {M : ℕ} (hM : 1 ≤ M) :
    -(weightedCenteredSawtoothSum N c 1 ^ (2 : ℕ)) ≤
      (∑ n ∈ Finset.Icc 1 (M - 1),
        (sieveSeq N c (n + 1) - selbergMultiplesCoord N c 1) *
          (sieveSeq N (fun d => c d / (d : ℝ)) (n + 1) - selbergMultiplesCoord N c 1)) +
      2 * ∑ n ∈ Finset.Icc 1 (M - 1),
        (sieveSeq N c (n + 1) - selbergMultiplesCoord N c 1) *
          inactiveCenteredSawtoothSum N c (n + 1) n := by
  have htel := weightedCenteredSawtoothSum_sq_sub_one_eq_active_deleted_add_inactive N c hM
  have hsq : 0 ≤ weightedCenteredSawtoothSum N c M ^ (2 : ℕ) := sq_nonneg _
  linarith

/-! ## §2. Trans-Horizon Prime Step Invariance & Purely Inactive Sawtooth State -/

/-- For every prime `p > N`, the sub-horizon divisors of `p` in `Icc 1 N` coincide with those of `1`. -/
theorem filter_dvd_prime_of_gt {N p : ℕ} (hp : p.Prime) (hpN : N < p) :
    (Finset.Icc 1 N).filter (fun d => d ∣ p) =
      (Finset.Icc 1 N).filter (fun d => d ∣ 1) := by
  ext d
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hd1, hdN⟩, hdp⟩
    rcases (Nat.dvd_prime hp).mp hdp with rfl | rfl
    · exact ⟨⟨hd1, hdN⟩, dvd_refl 1⟩
    · omega
  · rintro ⟨⟨hd1, hdN⟩, hd1'⟩
    exact ⟨⟨hd1, hdN⟩, hd1'.trans (one_dvd p)⟩

/-- For every prime `p > N` and weight `c : ℕ → ℝ`, both `sieveSeq N c p` and the harmonic-divided
sieve `sieveSeq N (fun d => c d / d) p` equal `sieveSeq N c 1`. -/
theorem sieveSeq_and_harmonic_prime_of_gt {N p : ℕ} (hp : p.Prime) (hpN : N < p)
    (c : ℕ → ℝ) :
    sieveSeq N c p = sieveSeq N c 1 ∧
      sieveSeq N (fun d => c d / (d : ℝ)) p = sieveSeq N c 1 := by
  unfold sieveSeq
  rw [filter_dvd_prime_of_gt hp hpN]
  refine ⟨rfl, Finset.sum_congr rfl fun d hd => ?_⟩
  have hd1 : d = 1 := Nat.eq_one_of_dvd_one (Finset.mem_filter.mp hd).2
  subst hd1
  simp

/-- **Active Sawtooth Annihilation at Every Trans-Horizon Prime (`activeCenteredSawtoothSum_prime_of_gt_eq_zero`):**
For every prime `p > N` and weight `c : ℕ → ℝ`:
`activeCenteredSawtoothSum N c p (p - 1) = 0` and `activeCenteredSawtoothSum N c p p = 0`. -/
theorem activeCenteredSawtoothSum_prime_of_gt_eq_zero {N p : ℕ} (hp : p.Prime) (hpN : N < p)
    (c : ℕ → ℝ) :
    activeCenteredSawtoothSum N c p (p - 1) = 0 ∧
      activeCenteredSawtoothSum N c p p = 0 := by
  have hp_eq : p - 1 + 1 = p := Nat.sub_add_cancel hp.pos
  have h1 := activeCenteredSawtoothSum_at_pred_eq_half_sieveSeq_sub N c (p - 1)
  have h2 := activeCenteredSawtoothSum_at_self_eq_half_sieveSeq_sub N c (p - 1)
  obtain ⟨hs1, hs2⟩ := sieveSeq_and_harmonic_prime_of_gt hp hpN c
  rw [hp_eq, hs1, hs2, sub_self, mul_zero] at h1 h2
  exact ⟨h1, h2⟩

/-- **100% Inactive Sawtooth State at Every Trans-Horizon Prime
(`inactiveCenteredSawtoothSum_prime_of_gt_eq_weighted`):**
For every prime `p > N` and weight `c : ℕ → ℝ`:
`inactiveCenteredSawtoothSum N c p (p - 1) = weightedCenteredSawtoothSum N c (p - 1)` and
`inactiveCenteredSawtoothSum N c p p = weightedCenteredSawtoothSum N c p`. -/
theorem inactiveCenteredSawtoothSum_prime_of_gt_eq_weighted {N p : ℕ} (hp : p.Prime)
    (hpN : N < p) (c : ℕ → ℝ) :
    inactiveCenteredSawtoothSum N c p (p - 1) = weightedCenteredSawtoothSum N c (p - 1) ∧
      inactiveCenteredSawtoothSum N c p p = weightedCenteredSawtoothSum N c p := by
  have hw1 := weightedCenteredSawtoothSum_eq_active_add_inactive N c p (p - 1)
  have hw2 := weightedCenteredSawtoothSum_eq_active_add_inactive N c p p
  obtain ⟨ha1, ha2⟩ := activeCenteredSawtoothSum_prime_of_gt_eq_zero hp hpN c
  exact ⟨by linarith, by linarith⟩

/-! ## §3. Pure-Square Active-Deleted Diagonal & Constant Drift Across Trans-Horizon Primes -/

/-- **Constant Forward Drift of `weightedCenteredSawtoothSum` Across Any Trans-Horizon Prime Step
(`weightedCenteredSawtoothSum_prime_sub_pred_of_gt`):**
For every prime `p > N` and weight `c : ℕ → ℝ`:
`weightedCenteredSawtoothSum N c p - weightedCenteredSawtoothSum N c (p - 1) = sieveSeq N c 1 - selbergMultiplesCoord N c 1`. -/
theorem weightedCenteredSawtoothSum_prime_sub_pred_of_gt {N p : ℕ} (hp : p.Prime)
    (hpN : N < p) (c : ℕ → ℝ) :
    weightedCenteredSawtoothSum N c p - weightedCenteredSawtoothSum N c (p - 1) =
      sieveSeq N c 1 - selbergMultiplesCoord N c 1 := by
  have hp_eq : p - 1 + 1 = p := Nat.sub_add_cancel hp.pos
  have hw := weightedCenteredSawtoothSum_succ_sub_eq N c (p - 1)
  rw [hp_eq, (sieveSeq_and_harmonic_prime_of_gt hp hpN c).1] at hw
  exact hw

/-- **Pure-Square Active-Deleted Martingale Step at Every Trans-Horizon Prime
(`weightedCenteredSawtoothSum_prime_sq_sub_pred_sq_of_gt`):**
For every prime `p > N` and weight `c : ℕ → ℝ`, at the prime step `p - 1 ↦ p`, the active-deleted
shifted-diagonal product is the non-negative square `(sieveSeq N c 1 - selbergMultiplesCoord N c 1)²`
and the inactive martingale factor is `weightedCenteredSawtoothSum N c (p - 1)`:
`W_{N,c}(p)² - W_{N,c}(p - 1)² = (s_{N,c}(1) - Y_{N,c}(1))² + 2 * (s_{N,c}(1) - Y_{N,c}(1)) * W_{N,c}(p - 1)`. -/
theorem weightedCenteredSawtoothSum_prime_sq_sub_pred_sq_of_gt {N p : ℕ} (hp : p.Prime)
    (hpN : N < p) (c : ℕ → ℝ) :
    weightedCenteredSawtoothSum N c p ^ (2 : ℕ) -
      weightedCenteredSawtoothSum N c (p - 1) ^ (2 : ℕ) =
      (sieveSeq N c 1 - selbergMultiplesCoord N c 1) ^ (2 : ℕ) +
        2 * (sieveSeq N c 1 - selbergMultiplesCoord N c 1) *
          weightedCenteredSawtoothSum N c (p - 1) := by
  have hp_eq : p - 1 + 1 = p := Nat.sub_add_cancel hp.pos
  have hstep :=
    weightedCenteredSawtoothSum_succ_sq_sub_sq_eq_shifted_diagonal_add_inactive_martingale
      N c (p - 1)
  obtain ⟨hs1, hs2⟩ := sieveSeq_and_harmonic_prime_of_gt hp hpN c
  have hinact := (inactiveCenteredSawtoothSum_prime_of_gt_eq_weighted hp hpN c).1
  rw [hp_eq, hs1, hs2, hinact] at hstep
  linarith [hstep, sq (sieveSeq N c 1 - selbergMultiplesCoord N c 1)]

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
