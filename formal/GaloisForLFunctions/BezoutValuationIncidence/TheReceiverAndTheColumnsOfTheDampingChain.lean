import GaloisForLFunctions.BezoutValuationIncidence.TheReceiverEquivalenceAndZeroWidthLaw
import GaloisForLFunctions.SignedArithmeticEnergyIncidence.TheReceiverIsTheChainOrbitOfTheReciprocal
import GaloisForLFunctions.SignedArithmeticEnergyIncidence.ResidueModesAndBackwardContinuation

/-!
# The Receiver and the Columns of the Centered Arithmetic Damping Chain

In `SignedArithmeticEnergyIncidence.TheReceiverIsTheChainOrbitOfTheReciprocal`, it was shown that
the uncentered transition matrix `P_η(n+1, k+1)` has first column `P_η(n+1, 1) → e_η(1) > 0`, which
is never square-summable (`not_summable_transition_first_column`), while the centered operator
`C_η = P_η − e_η` maps the reciprocal observable `r(k) = 1/(k+1)` to the normalized centered
divisor prefix `(C_η r)(n) = A_η(n+1)/(n+1)`.

This module establishes an exact structural identity and two-sided quantitative `ℓ²` comparison
between the receiver energy `E_T(η)` and the **individual columns** `n ↦ C_η(n, k)` of the
centered damping chain:

1. **Exact Dilated-State Telescoping of Every Column (`arithmeticDampingCenteredRow_eq_dilatedState_diff`):**
   Define the dilated state
   `X_η(d, n) = d^{−η} (A_η(⌊(n+1)/d⌋)/(n+1) + ρ_η v_d(n))`,
   where `ρ_η = Re(1/ζ(1+η))` and `v_d(n) = ⌊(n+1)/d⌋/(n+1) − 1/d` is the `d`-th residue mode.
   Then `X_η(1, n) = A_η(n+1)/(n+1) = (C_η r)(n)` (`arithmeticDampingDilatedState_one`), and every
   entry of the centered damping matrix is the exact discrete difference
   `C_η(n, k) = (k + 1) (X_η(k + 1, n) − X_η(k + 2, n))`.

2. **Exact Contraction of Dilated Sums (`sum_range_dilated_div_sq_le`):**
   For any nonnegative sequence `a : ℕ → ℝ` with `a 0 = 0`, any dilation factor `r ≥ 1`, and any
   horizon `T ∈ ℕ`,
   `∑_{n < T} a(⌊(n+1)/r⌋)/(n+1)² ≤ (1/r) ∑_{m < T} a(m+1)/(m+1)²`.

3. **Universal Upper Bound on Every Column (`sum_range_arithmeticDampingCenteredRow_sq_le`):**
   For every `η ≥ 0`, column index `k ∈ ℕ`, and horizon `T ∈ ℕ`,
   `∑_{n < T} C_η(n, k)² ≤ 16 (E_T(η) + ρ_η²) (k + 1)^{1 − 2η}`.

4. **Coercive Lower Bound from the First Column Alone (`pmPowerDampedDivisorDiscreteEnergy_le_first_column_sum`):**
   At `r = 2`, the dilated sum contracts by `1/2 < 1`, which allows the dyadic term `X_η(2, n)` to
   be absorbed into `X_η(1, n)`. Consequently, the **first column** `k = 0` alone bounds the entire
   receiver energy at every horizon `T ∈ ℕ` and every `η ≥ 0`:
   `E_T(η) ≤ ∑_{n < T} (A_η(n+1)/(n+1))² ≤ 24 ∑_{n < T} C_η(n, 0)² + 24 ρ_η²`.

5. **Five-Way Column/Operator Characterization of Receiver Admission & Zero-Width Corollary:**
   For every `η > 0`, the following are equivalent:
   - `η ∈ receiverDampings` (bounded discrete energy `E_T(η)`);
   - `η ∈ interiorReceiverDampings` (bounded pure-interior pronic energy `E_T^int(η)`);
   - the single first column `n ↦ C_η(n, 0)` lies in `ℓ²(ℕ)` (`mem_receiverDampings_iff_summable_first_column`);
   - every column `n ↦ C_η(n, k)` (`k ∈ ℕ`) lies in `ℓ²(ℕ)` (`mem_receiverDampings_iff_forall_column_summable`);
   - for every finitely supported `b ∈ C₀(ℕ, ℝ)`, `C_η b ∈ ℓ²(ℕ)`.
   In particular, all five hold unconditionally for every `η > Θ − 1/2`, and their validity at
   arbitrarily small `η > 0` is equivalent to `RiemannHypothesis`.
-/

open Finset Filter Topology Real RHTower
open scoped BigOperators ZeroAtInfty
open GaloisForLFunctions.BiScaleUncertainty
open GaloisForLFunctions.SignedArithmeticEnergyIncidence
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. Exact Dilated-State Decomposition of Every Centered Damping Column -/

/-- The raw divisor prefix equals the centered divisor prefix plus the linear density term. -/
theorem arithmeticDampingPrefix_eq_centered_add (η : ℝ) (q : ℕ) :
    arithmeticDampingPrefix η q =
      pmPowerDampedCenteredDivisorPrefix η q + (pmPowerDampedDivisorDensity η).re * (q : ℝ) := by
  rw [pmPowerDampedCenteredDivisorPrefix_eq]
  unfold arithmeticDampingPrefix
  ring

/-- The `d`-dilated state at damping `η` and row index `n` (corresponding to positive integer
`n + 1`):
`X_η(d, n) = d^{−η} (A_η(⌊(n+1)/d⌋)/(n+1) + Re(1/ζ(1+η)) · v_d(n))`. -/
def arithmeticDampingDilatedState (η : ℝ) (d n : ℕ) : ℝ :=
  (d : ℝ) ^ (-η) *
    (pmPowerDampedCenteredDivisorPrefix η ((n + 1) / d) / ((n : ℝ) + 1) +
      (pmPowerDampedDivisorDensity η).re * normalizedResidueProfile d n)

/-- At `d = 1`, the dilated state is the normalized centered divisor prefix `A_η(n+1)/(n+1)`
(the chain orbit `(C_η r)(n)` of the reciprocal observable). -/
@[simp] theorem arithmeticDampingDilatedState_one (η : ℝ) (n : ℕ) :
    arithmeticDampingDilatedState η 1 n =
      pmPowerDampedCenteredDivisorPrefix η (n + 1) / ((n : ℝ) + 1) := by
  have hv1 : normalizedResidueProfile 1 n = 0 := by
    have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
    simp [normalizedResidueProfile, div_self hn1]
  simp [arithmeticDampingDilatedState, hv1]

/-- Key relation connecting the raw transition term and the entrance term at divisor `d ≥ 1` to
`arithmeticDampingDilatedState η d n`. -/
theorem arithmeticDampingDilatedState_eq_prefix_sub_density (η : ℝ) {d : ℕ} (hd : 0 < d) (n : ℕ) :
    arithmeticDampingDilatedState η d n =
      (d : ℝ) ^ (-η) * arithmeticDampingPrefix η ((n + 1) / d) / ((n : ℝ) + 1) -
        (pmPowerDampedDivisorDensity η).re * (d : ℝ) ^ (-1 - η) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hpow : (d : ℝ) ^ (-1 - η) = (d : ℝ) ^ (-η) / (d : ℝ) := by
    rw [show -1 - η = -η - 1 by ring, Real.rpow_sub hd0, Real.rpow_one]
  have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  unfold arithmeticDampingDilatedState normalizedResidueProfile
  rw [arithmeticDampingPrefix_eq_centered_add, hpow, hcast]
  field_simp [hd0.ne', hn1.ne']
  ring

/-- **Exact Dilated-State Telescoping of the Centered Damping Chain:**
Every entry `C_η(n, k)` of the centered damping matrix is `(k + 1)` times the discrete difference
of `arithmeticDampingDilatedState` between `d = k + 1` and `d = k + 2`. -/
theorem arithmeticDampingCenteredRow_eq_dilatedState_diff (η : ℝ) (n k : ℕ) :
    arithmeticDampingCenteredRow η n k =
      ((k : ℝ) + 1) *
        (arithmeticDampingDilatedState η (k + 1) n - arithmeticDampingDilatedState η (k + 2) n) := by
  rw [arithmeticDampingDilatedState_eq_prefix_sub_density η (show 0 < k + 1 by omega) n,
    arithmeticDampingDilatedState_eq_prefix_sub_density η (show 0 < k + 2 by omega) n]
  unfold arithmeticDampingCenteredRow arithmeticDampingTransition arithmeticDampingEntrance
  have hn1 : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  have hk1 : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
  have hk2' : ((k + 2 : ℕ) : ℝ) = (k : ℝ) + 2 := by push_cast; ring
  rw [show k + 1 + 1 = k + 2 by omega]
  rw [hn1, hk1, hk2']
  ring

/-! ## §2. Exact Contraction of Dilated Prefix Sums -/

private theorem sum_range_dilated_div_sq_le_block {a : ℕ → ℝ} (ha0 : a 0 = 0)
    (ha : ∀ m, 0 ≤ a m) {r : ℕ} (hr : 0 < r) (K : ℕ) :
    ∑ n ∈ range (K * r + (r - 1)), a ((n + 1) / r) / ((n : ℝ) + 1) ^ 2 ≤
      1 / (r : ℝ) * ∑ m ∈ range K, a (m + 1) / ((m : ℝ) + 1) ^ 2 := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  induction K with
  | zero =>
    simp only [zero_mul, zero_add, range_zero, sum_empty, mul_zero]
    refine le_of_eq (sum_eq_zero fun n hn => ?_)
    have hnr : n + 1 < r := by rw [mem_range] at hn; omega
    rw [Nat.div_eq_of_lt hnr, ha0, zero_div]
  | succ K ih =>
    have hlen : (K + 1) * r + (r - 1) = (K * r + (r - 1)) + r := by
      calc (K + 1) * r + (r - 1) = K * r + r + (r - 1) := by ring
        _ = (K * r + (r - 1)) + r := by omega
    rw [hlen, Finset.sum_range_add,
      Finset.sum_range_succ (f := fun m => a (m + 1) / ((m : ℝ) + 1) ^ 2) K, mul_add]
    refine add_le_add ih ?_
    have hstep : ∀ j ∈ range r,
        a ((K * r + (r - 1) + j + 1) / r) / (((K * r + (r - 1) + j : ℕ) : ℝ) + 1) ^ 2 ≤
          a (K + 1) / (((K : ℝ) + 1) * (r : ℝ)) ^ 2 := by
      intro j hj
      have hjr : j < r := mem_range.mp hj
      have hnum : K * r + (r - 1) + j + 1 = j + (K + 1) * r := by
        calc K * r + (r - 1) + j + 1 = K * r + ((r - 1) + 1) + j := by omega
          _ = K * r + r + j := by rw [Nat.sub_add_cancel hr]
          _ = j + (K + 1) * r := by ring
      have hdiv : (K * r + (r - 1) + j + 1) / r = K + 1 := by
        rw [hnum, Nat.add_mul_div_right j (K + 1) hr, Nat.div_eq_of_lt hjr, zero_add]
      rw [hdiv]
      have hle_nat : (K + 1) * r ≤ K * r + (r - 1) + j + 1 := by omega
      have hle_real : ((K : ℝ) + 1) * (r : ℝ) ≤ ((K * r + (r - 1) + j : ℕ) : ℝ) + 1 := by
        exact_mod_cast hle_nat
      exact div_le_div_of_nonneg_left (ha (K + 1)) (by positivity)
        (pow_le_pow_left₀ (by positivity) hle_real 2)
    calc ∑ j ∈ range r,
          a ((K * r + (r - 1) + j + 1) / r) / (((K * r + (r - 1) + j : ℕ) : ℝ) + 1) ^ 2
        ≤ ∑ _j ∈ range r, a (K + 1) / (((K : ℝ) + 1) * (r : ℝ)) ^ 2 := sum_le_sum hstep
      _ = (r : ℝ) * (a (K + 1) / (((K : ℝ) + 1) * (r : ℝ)) ^ 2) := by
          simp [sum_const, card_range, nsmul_eq_mul]
      _ = 1 / (r : ℝ) * (a (K + 1) / ((K : ℝ) + 1) ^ 2) := by
          field_simp [hr0.ne']

/-- **Exact Contraction of Dilated Sums:**
For any nonnegative sequence `a : ℕ → ℝ` vanishing at `0`, any dilation factor `r ≥ 1`, and any
horizon `T ∈ ℕ`,
`∑_{n < T} a(⌊(n+1)/r⌋)/(n+1)² ≤ (1/r) ∑_{m < T} a(m+1)/(m+1)²`. -/
theorem sum_range_dilated_div_sq_le {a : ℕ → ℝ} (ha0 : a 0 = 0) (ha : ∀ m, 0 ≤ a m)
    {r : ℕ} (hr : 0 < r) (T : ℕ) :
    ∑ n ∈ range T, a ((n + 1) / r) / ((n : ℝ) + 1) ^ 2 ≤
      1 / (r : ℝ) * ∑ m ∈ range T, a (m + 1) / ((m : ℝ) + 1) ^ 2 := by
  have hdiv := Nat.div_add_mod T r
  have hmod := Nat.mod_lt T hr
  have hT_le : T ≤ (T / r) * r + (r - 1) := by
    have : r * (T / r) = (T / r) * r := mul_comm r (T / r)
    omega
  have hTr_le : T / r ≤ T := Nat.div_le_self T r
  calc ∑ n ∈ range T, a ((n + 1) / r) / ((n : ℝ) + 1) ^ 2
      ≤ ∑ n ∈ range ((T / r) * r + (r - 1)), a ((n + 1) / r) / ((n : ℝ) + 1) ^ 2 :=
        sum_le_sum_of_subset_of_nonneg (range_mono hT_le) fun n _ _ =>
          div_nonneg (ha _) (sq_nonneg _)
    _ ≤ 1 / (r : ℝ) * ∑ m ∈ range (T / r), a (m + 1) / ((m : ℝ) + 1) ^ 2 :=
        sum_range_dilated_div_sq_le_block ha0 ha hr (T / r)
    _ ≤ 1 / (r : ℝ) * ∑ m ∈ range T, a (m + 1) / ((m : ℝ) + 1) ^ 2 := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact sum_le_sum_of_subset_of_nonneg (range_mono hTr_le) fun m _ _ =>
          div_nonneg (ha _) (sq_nonneg _)

/-- The unweighted prefix sum `∑_{m < T} (A_η(m+1)/(m+1))²` lies between `E_T(η)` and `2 E_T(η)`. -/
theorem pmPowerDampedDivisorDiscreteEnergy_le_sum_range_div_sq (η : ℝ) (T : ℕ) :
    pmPowerDampedDivisorDiscreteEnergy η T ≤
      ∑ m ∈ range T, (pmPowerDampedCenteredDivisorPrefix η (m + 1) / ((m : ℝ) + 1)) ^ 2 := by
  unfold pmPowerDampedDivisorDiscreteEnergy
  rw [RHTower.sum_Icc_eq_sum_range_shift]
  refine sum_le_sum fun m _ => ?_
  rw [div_pow]
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hle : ((m : ℝ) + 1) ^ 2 ≤ ((m + 1 : ℕ) : ℝ) * (((m + 1 : ℕ) : ℝ) + 1) := by
    push_cast; nlinarith
  exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hle

theorem sum_range_div_sq_le_two_mul_pmPowerDampedDivisorDiscreteEnergy (η : ℝ) (T : ℕ) :
    ∑ m ∈ range T, (pmPowerDampedCenteredDivisorPrefix η (m + 1) / ((m : ℝ) + 1)) ^ 2 ≤
      2 * pmPowerDampedDivisorDiscreteEnergy η T := by
  unfold pmPowerDampedDivisorDiscreteEnergy
  rw [RHTower.sum_Icc_eq_sum_range_shift, mul_sum]
  refine sum_le_sum fun m _ => ?_
  rw [div_pow]
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hm2 : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) * (((m + 1 : ℕ) : ℝ) + 1) := by positivity
  rw [← mul_div_assoc, div_le_div_iff₀ (sq_pos_of_pos hm1) hm2]
  have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
  rw [hcast]
  have hsq : 0 ≤ pmPowerDampedCenteredDivisorPrefix η (m + 1) ^ 2 := sq_nonneg _
  have hle : ((m : ℝ) + 1) * ((m : ℝ) + 1 + 1) ≤ 2 * ((m : ℝ) + 1) ^ 2 := by nlinarith
  exact (mul_le_mul_of_nonneg_left hle hsq).trans (le_of_eq (by ring))

/-! ## §3. Universal Upper Bound on Every Column and Coercive First-Column Lower Bound -/

/-- Partial `ℓ²` bound for the `d`-th residue mode: `∑_{n < T} v_d(n)² ≤ 2/d`. -/
theorem sum_range_sq_normalizedResidueProfile_le {d : ℕ} (hd : 0 < d) (T : ℕ) :
    ∑ n ∈ range T, normalizedResidueProfile d n ^ 2 ≤ 2 / (d : ℝ) :=
  ((summable_sq_normalizedResidueProfile d).sum_le_tsum (range T) fun _ _ => sq_nonneg _).trans
    (tsum_sq_normalizedResidueProfile_le hd)

/-- Partial `ℓ²` bound for the dilated state `X_η(d, n)`:
`∑_{n < T} X_η(d, n)² ≤ 4 d^{−1−2η} (E_T(η) + ρ_η²)`. -/
theorem sum_range_arithmeticDampingDilatedState_sq_le (η : ℝ) {d : ℕ} (hd : 0 < d) (T : ℕ) :
    ∑ n ∈ range T, arithmeticDampingDilatedState η d n ^ 2 ≤
      4 * (d : ℝ) ^ (-1 - 2 * η) *
        (pmPowerDampedDivisorDiscreteEnergy η T + (pmPowerDampedDivisorDensity η).re ^ 2) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hstep : ∀ n : ℕ, arithmeticDampingDilatedState η d n ^ 2 ≤
      2 * ((d : ℝ) ^ (-η)) ^ 2 *
        ((pmPowerDampedCenteredDivisorPrefix η ((n + 1) / d) / ((n : ℝ) + 1)) ^ 2 +
          (pmPowerDampedDivisorDensity η).re ^ 2 * normalizedResidueProfile d n ^ 2) := by
    intro n
    unfold arithmeticDampingDilatedState
    rw [mul_pow]
    have h2 : ∀ u v : ℝ, (u + v) ^ 2 ≤ 2 * (u ^ 2 + v ^ 2) := fun u v => by
      nlinarith [sq_nonneg (u - v)]
    have := mul_le_mul_of_nonneg_left
      (h2 (pmPowerDampedCenteredDivisorPrefix η ((n + 1) / d) / ((n : ℝ) + 1))
        ((pmPowerDampedDivisorDensity η).re * normalizedResidueProfile d n))
      (sq_nonneg ((d : ℝ) ^ (-η)))
    linarith [show ((pmPowerDampedDivisorDensity η).re * normalizedResidueProfile d n) ^ 2 =
      (pmPowerDampedDivisorDensity η).re ^ 2 * normalizedResidueProfile d n ^ 2 by ring]
  have hdil : ∑ n ∈ range T,
        (pmPowerDampedCenteredDivisorPrefix η ((n + 1) / d) / ((n : ℝ) + 1)) ^ 2 ≤
      2 / (d : ℝ) * pmPowerDampedDivisorDiscreteEnergy η T := by
    have h1 := sum_range_dilated_div_sq_le
      (a := fun q => pmPowerDampedCenteredDivisorPrefix η q ^ 2)
      (by simp) (fun _ => sq_nonneg _) hd T
    simp_rw [← div_pow] at h1
    have h2 := sum_range_div_sq_le_two_mul_pmPowerDampedDivisorDiscreteEnergy η T
    calc ∑ n ∈ range T, (pmPowerDampedCenteredDivisorPrefix η ((n + 1) / d) / ((n : ℝ) + 1)) ^ 2
        ≤ 1 / (d : ℝ) * ∑ m ∈ range T,
            (pmPowerDampedCenteredDivisorPrefix η (m + 1) / ((m : ℝ) + 1)) ^ 2 := h1
      _ ≤ 1 / (d : ℝ) * (2 * pmPowerDampedDivisorDiscreteEnergy η T) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 2 / (d : ℝ) * pmPowerDampedDivisorDiscreteEnergy η T := by ring
  have hres := sum_range_sq_normalizedResidueProfile_le hd T
  have hpow : 2 * ((d : ℝ) ^ (-η)) ^ 2 * (2 / (d : ℝ)) = 4 * (d : ℝ) ^ (-1 - 2 * η) := by
    have h1 : ((d : ℝ) ^ (-η)) ^ 2 = (d : ℝ) ^ (-2 * η) := by
      rw [← Real.rpow_natCast ((d : ℝ) ^ (-η)) 2, ← Real.rpow_mul hd0.le]
      congr 1; push_cast; ring
    have h2 : (d : ℝ) ^ (-1 - 2 * η) = (d : ℝ) ^ (-2 * η) / (d : ℝ) := by
      rw [show -1 - 2 * η = -2 * η - 1 by ring, Real.rpow_sub hd0, Real.rpow_one]
    rw [h1, h2]; ring
  calc ∑ n ∈ range T, arithmeticDampingDilatedState η d n ^ 2
      ≤ ∑ n ∈ range T, 2 * ((d : ℝ) ^ (-η)) ^ 2 *
          ((pmPowerDampedCenteredDivisorPrefix η ((n + 1) / d) / ((n : ℝ) + 1)) ^ 2 +
            (pmPowerDampedDivisorDensity η).re ^ 2 * normalizedResidueProfile d n ^ 2) :=
        sum_le_sum fun n _ => hstep n
    _ = 2 * ((d : ℝ) ^ (-η)) ^ 2 *
          ((∑ n ∈ range T,
              (pmPowerDampedCenteredDivisorPrefix η ((n + 1) / d) / ((n : ℝ) + 1)) ^ 2) +
            (pmPowerDampedDivisorDensity η).re ^ 2 *
              ∑ n ∈ range T, normalizedResidueProfile d n ^ 2) := by
        rw [← mul_sum, sum_add_distrib, ← mul_sum]
    _ ≤ 2 * ((d : ℝ) ^ (-η)) ^ 2 *
          (2 / (d : ℝ) * pmPowerDampedDivisorDiscreteEnergy η T +
            (pmPowerDampedDivisorDensity η).re ^ 2 * (2 / (d : ℝ))) := by
        refine mul_le_mul_of_nonneg_left (add_le_add hdil ?_) (by positivity)
        exact mul_le_mul_of_nonneg_left hres (sq_nonneg _)
    _ = (2 * ((d : ℝ) ^ (-η)) ^ 2 * (2 / (d : ℝ))) *
          (pmPowerDampedDivisorDiscreteEnergy η T + (pmPowerDampedDivisorDensity η).re ^ 2) := by
        ring
    _ = 4 * (d : ℝ) ^ (-1 - 2 * η) *
          (pmPowerDampedDivisorDiscreteEnergy η T + (pmPowerDampedDivisorDensity η).re ^ 2) := by
        rw [hpow]

/-- **Universal Upper Bound on Every Column of the Centered Damping Chain:**
For every `η ≥ 0`, column index `k ∈ ℕ`, and horizon `T ∈ ℕ`,
`∑_{n < T} C_η(n, k)² ≤ 16 (E_T(η) + ρ_η²) (k + 1)^{1 − 2η}`. -/
theorem sum_range_arithmeticDampingCenteredRow_sq_le {η : ℝ} (hη : 0 ≤ η) (k T : ℕ) :
    ∑ n ∈ range T, arithmeticDampingCenteredRow η n k ^ 2 ≤
      16 * (pmPowerDampedDivisorDiscreteEnergy η T + (pmPowerDampedDivisorDensity η).re ^ 2) *
        ((k : ℝ) + 1) ^ (1 - 2 * η) := by
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hstep : ∀ n : ℕ, arithmeticDampingCenteredRow η n k ^ 2 ≤
      2 * ((k : ℝ) + 1) ^ 2 *
        (arithmeticDampingDilatedState η (k + 1) n ^ 2 +
          arithmeticDampingDilatedState η (k + 2) n ^ 2) := by
    intro n
    rw [arithmeticDampingCenteredRow_eq_dilatedState_diff, mul_pow]
    have h2 : ∀ u v : ℝ, (u - v) ^ 2 ≤ 2 * (u ^ 2 + v ^ 2) := fun u v => by
      nlinarith [sq_nonneg (u + v)]
    have := mul_le_mul_of_nonneg_left
      (h2 (arithmeticDampingDilatedState η (k + 1) n)
        (arithmeticDampingDilatedState η (k + 2) n))
      (sq_nonneg ((k : ℝ) + 1))
    linarith
  have hd1 := sum_range_arithmeticDampingDilatedState_sq_le η (show 0 < k + 1 by omega) T
  have hd2 := sum_range_arithmeticDampingDilatedState_sq_le η (show 0 < k + 2 by omega) T
  have hmono : ((k + 2 : ℕ) : ℝ) ^ (-1 - 2 * η) ≤ ((k + 1 : ℕ) : ℝ) ^ (-1 - 2 * η) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by exact_mod_cast (show k + 1 ≤ k + 2 by omega))
      (by linarith)
  have hE0 : 0 ≤ pmPowerDampedDivisorDiscreteEnergy η T +
      (pmPowerDampedDivisorDensity η).re ^ 2 :=
    add_nonneg (pmPowerDampedDivisorDiscreteEnergy_nonneg η T) (sq_nonneg _)
  have hd2' : ∑ n ∈ range T, arithmeticDampingDilatedState η (k + 2) n ^ 2 ≤
      4 * ((k + 1 : ℕ) : ℝ) ^ (-1 - 2 * η) *
        (pmPowerDampedDivisorDiscreteEnergy η T + (pmPowerDampedDivisorDensity η).re ^ 2) :=
    hd2.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmono (by norm_num)) hE0)
  have hpow : ((k : ℝ) + 1) ^ 2 * ((k + 1 : ℕ) : ℝ) ^ (-1 - 2 * η) =
      ((k : ℝ) + 1) ^ (1 - 2 * η) := by
    have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    rw [hcast, ← Real.rpow_natCast ((k : ℝ) + 1) 2, ← Real.rpow_add hk1]
    congr 1; push_cast; ring
  calc ∑ n ∈ range T, arithmeticDampingCenteredRow η n k ^ 2
      ≤ ∑ n ∈ range T, 2 * ((k : ℝ) + 1) ^ 2 *
          (arithmeticDampingDilatedState η (k + 1) n ^ 2 +
            arithmeticDampingDilatedState η (k + 2) n ^ 2) :=
        sum_le_sum fun n _ => hstep n
    _ = 2 * ((k : ℝ) + 1) ^ 2 *
          ((∑ n ∈ range T, arithmeticDampingDilatedState η (k + 1) n ^ 2) +
            ∑ n ∈ range T, arithmeticDampingDilatedState η (k + 2) n ^ 2) := by
        rw [← mul_sum, sum_add_distrib]
    _ ≤ 2 * ((k : ℝ) + 1) ^ 2 *
          (8 * ((k + 1 : ℕ) : ℝ) ^ (-1 - 2 * η) *
            (pmPowerDampedDivisorDiscreteEnergy η T + (pmPowerDampedDivisorDensity η).re ^ 2)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        linarith
    _ = 16 * (pmPowerDampedDivisorDiscreteEnergy η T + (pmPowerDampedDivisorDensity η).re ^ 2) *
          (((k : ℝ) + 1) ^ 2 * ((k + 1 : ℕ) : ℝ) ^ (-1 - 2 * η)) := by ring
    _ = 16 * (pmPowerDampedDivisorDiscreteEnergy η T + (pmPowerDampedDivisorDensity η).re ^ 2) *
          ((k : ℝ) + 1) ^ (1 - 2 * η) := by rw [hpow]

/-- **Coercive Lower Bound from the First Column Alone:**
For every `η ≥ 0` and horizon `T ∈ ℕ`, the partial `ℓ²` sum of the **first column**
`C_η(n, 0)` bounds the entire discrete receiver energy `E_T(η)`:
`E_T(η) ≤ ∑_{n < T} (A_η(n+1)/(n+1))² ≤ 24 ∑_{n < T} C_η(n, 0)² + 24 ρ_η²`. -/
theorem sum_range_div_sq_le_first_column_sum {η : ℝ} (hη : 0 ≤ η) (T : ℕ) :
    ∑ n ∈ range T, (pmPowerDampedCenteredDivisorPrefix η (n + 1) / ((n : ℝ) + 1)) ^ 2 ≤
      24 * (∑ n ∈ range T, arithmeticDampingCenteredRow η n 0 ^ 2) +
        24 * (pmPowerDampedDivisorDensity η).re ^ 2 := by
  have h2pow : ((2 : ℝ) ^ (-η)) ^ 2 ≤ 1 := by
    have hle : (2 : ℝ) ^ (-η) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    have h0 : 0 ≤ (2 : ℝ) ^ (-η) := Real.rpow_nonneg (by norm_num) _
    nlinarith
  have hpt : ∀ n : ℕ, (pmPowerDampedCenteredDivisorPrefix η (n + 1) / ((n : ℝ) + 1)) ^ 2 ≤
      (3 / 2 : ℝ) * (pmPowerDampedCenteredDivisorPrefix η ((n + 1) / 2) / ((n : ℝ) + 1)) ^ 2 +
        6 * arithmeticDampingCenteredRow η n 0 ^ 2 +
          6 * (pmPowerDampedDivisorDensity η).re ^ 2 * normalizedResidueProfile 2 n ^ 2 := by
    intro n
    have hrow := arithmeticDampingCenteredRow_eq_dilatedState_diff η n 0
    simp only [Nat.cast_zero, zero_add, one_mul, arithmeticDampingDilatedState_one] at hrow
    unfold arithmeticDampingDilatedState at hrow
    set u := pmPowerDampedCenteredDivisorPrefix η (n + 1) / ((n : ℝ) + 1)
    set y := (2 : ℝ) ^ (-η) * (pmPowerDampedCenteredDivisorPrefix η ((n + 1) / 2) / ((n : ℝ) + 1))
    set z := (2 : ℝ) ^ (-η) * ((pmPowerDampedDivisorDensity η).re * normalizedResidueProfile 2 n)
    set x := arithmeticDampingCenteredRow η n 0
    have hu : u = y + x + z := by
      change u = (2 : ℝ) ^ (-η) *
        (pmPowerDampedCenteredDivisorPrefix η ((n + 1) / 2) / ((n : ℝ) + 1)) + x +
        (2 : ℝ) ^ (-η) * ((pmPowerDampedDivisorDensity η).re * normalizedResidueProfile 2 n)
      linarith [hrow]
    have hineq : (y + x + z) ^ 2 ≤ (3 / 2 : ℝ) * y ^ 2 + 6 * x ^ 2 + 6 * z ^ 2 := by
      have h1 : 0 ≤ (y / 2 - (x + z)) ^ 2 := sq_nonneg _
      have h2 : 0 ≤ (x - z) ^ 2 := sq_nonneg _
      nlinarith
    have hy2 : y ^ 2 ≤ (pmPowerDampedCenteredDivisorPrefix η ((n + 1) / 2) / ((n : ℝ) + 1)) ^ 2 := by
      change ((2 : ℝ) ^ (-η) * _) ^ 2 ≤ _
      rw [mul_pow]
      exact mul_le_of_le_one_left (sq_nonneg _) h2pow
    have hz2 : z ^ 2 ≤
        (pmPowerDampedDivisorDensity η).re ^ 2 * normalizedResidueProfile 2 n ^ 2 := by
      change ((2 : ℝ) ^ (-η) * (_ * _)) ^ 2 ≤ _
      rw [mul_pow, mul_pow]
      exact mul_le_of_le_one_left (mul_nonneg (sq_nonneg _) (sq_nonneg _)) h2pow
    rw [hu]
    linarith
  have hdil2 : ∑ n ∈ range T,
        (pmPowerDampedCenteredDivisorPrefix η ((n + 1) / 2) / ((n : ℝ) + 1)) ^ 2 ≤
      1 / 2 * ∑ n ∈ range T,
        (pmPowerDampedCenteredDivisorPrefix η (n + 1) / ((n : ℝ) + 1)) ^ 2 := by
    have h := sum_range_dilated_div_sq_le
      (a := fun q => pmPowerDampedCenteredDivisorPrefix η q ^ 2)
      (by simp) (fun _ => sq_nonneg _) two_pos T
    simp_rw [← div_pow] at h
    norm_num at h
    exact h
  have hres2 : ∑ n ∈ range T, normalizedResidueProfile 2 n ^ 2 ≤ 1 := by
    have h := sum_range_sq_normalizedResidueProfile_le two_pos T
    norm_num at h
    exact h
  have hsum := sum_le_sum fun n (_ : n ∈ range T) => hpt n
  rw [sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum, ← mul_sum] at hsum
  have hres2' : 6 * (pmPowerDampedDivisorDensity η).re ^ 2 *
      ∑ n ∈ range T, normalizedResidueProfile 2 n ^ 2 ≤
      6 * (pmPowerDampedDivisorDensity η).re ^ 2 :=
    mul_le_of_le_one_right (by positivity) hres2
  linarith

theorem pmPowerDampedDivisorDiscreteEnergy_le_first_column_sum {η : ℝ} (hη : 0 ≤ η) (T : ℕ) :
    pmPowerDampedDivisorDiscreteEnergy η T ≤
      24 * (∑ n ∈ range T, arithmeticDampingCenteredRow η n 0 ^ 2) +
        24 * (pmPowerDampedDivisorDensity η).re ^ 2 :=
  (pmPowerDampedDivisorDiscreteEnergy_le_sum_range_div_sq η T).trans
    (sum_range_div_sq_le_first_column_sum hη T)

/-! ## §4. Column & Finitely-Supported Characterization of Receiver Admission -/

/-- **First-Column Characterization of the Receiver:**
For `η > 0`, `η` belongs to `receiverDampings` if and only if the single first column
`n ↦ C_η(n, 0)` of the centered damping chain is square-summable. -/
theorem mem_receiverDampings_iff_summable_first_column {η : ℝ} (hη : 0 < η) :
    η ∈ receiverDampings ↔ Summable (fun n : ℕ => arithmeticDampingCenteredRow η n 0 ^ 2) := by
  simp only [receiverDampings, Set.mem_setOf_eq, hη, true_and]
  constructor
  · rintro ⟨B, hB⟩
    refine summable_of_sum_range_le
      (c := 16 * (B + (pmPowerDampedDivisorDensity η).re ^ 2))
      (fun n => sq_nonneg _) fun T => ?_
    have h := sum_range_arithmeticDampingCenteredRow_sq_le hη.le 0 T
    simp only [Nat.cast_zero, zero_add, Real.one_rpow, mul_one] at h
    exact h.trans (by linarith [hB T])
  · intro hs
    refine ⟨24 * (∑' n : ℕ, arithmeticDampingCenteredRow η n 0 ^ 2) +
      24 * (pmPowerDampedDivisorDensity η).re ^ 2, fun T => ?_⟩
    have h1 := pmPowerDampedDivisorDiscreteEnergy_le_first_column_sum hη.le T
    have h2 := hs.sum_le_tsum (range T) fun _ _ => sq_nonneg _
    linarith

/-- **All-Columns Characterization of the Receiver:**
For `η > 0`, `η` belongs to `receiverDampings` if and only if **every** column `n ↦ C_η(n, k)`
(`k ∈ ℕ`) of the centered damping chain is square-summable. -/
theorem mem_receiverDampings_iff_forall_column_summable {η : ℝ} (hη : 0 < η) :
    η ∈ receiverDampings ↔
      ∀ k : ℕ, Summable (fun n : ℕ => arithmeticDampingCenteredRow η n k ^ 2) := by
  constructor
  · rintro ⟨_, B, hB⟩ k
    refine summable_of_sum_range_le
      (c := 16 * (B + (pmPowerDampedDivisorDensity η).re ^ 2) * ((k : ℝ) + 1) ^ (1 - 2 * η))
      (fun n => sq_nonneg _) fun T => ?_
    exact (sum_range_arithmeticDampingCenteredRow_sq_le hη.le k T).trans
      (mul_le_mul_of_nonneg_right (by linarith [hB T]) (Real.rpow_nonneg (by positivity) _))
  · intro hk
    exact (mem_receiverDampings_iff_summable_first_column hη).mpr (hk 0)

/-- For any `c₀` vector `b` supported on `range N`, `(C_η b)(n)` is a finite linear combination
of the first `N` columns of `C_η`, with `((C_η b)(n))² ≤ N ∑_{k < N} (C_η(n, k) b(k))²`. -/
theorem arithmeticDampingCenteredOperator_apply_of_support {η : ℝ} (hη : 0 < η)
    (b : C₀(ℕ, ℝ)) (N : ℕ) (hb : ∀ k, N ≤ k → b k = 0) (n : ℕ) :
    arithmeticDampingCenteredOperator hη b n =
      ∑ k ∈ range N, arithmeticDampingCenteredRow η n k * b k := by
  rw [arithmeticDampingCenteredOperator_apply]
  exact tsum_eq_sum fun k hk => by
    rw [hb k (not_lt.mp (mem_range.not.mp hk)), mul_zero]

/-- **Finitely-Supported `c₀` Characterization of the Receiver:**
For `η > 0`, `η ∈ receiverDampings` if and only if `C_η b ∈ ℓ²(ℕ)` for every finitely supported
sequence `b ∈ C₀(ℕ, ℝ)`. -/
theorem mem_receiverDampings_iff_finitelySupported_image_summable {η : ℝ} (hη : 0 < η) :
    η ∈ receiverDampings ↔
      ∀ b : C₀(ℕ, ℝ), (∃ N : ℕ, ∀ k, N ≤ k → b k = 0) →
        Summable (fun n : ℕ => arithmeticDampingCenteredOperator hη b n ^ 2) := by
  rw [mem_receiverDampings_iff_forall_column_summable hη]
  constructor
  · intro hcol b ⟨N, hb⟩
    have hle : ∀ n : ℕ, arithmeticDampingCenteredOperator hη b n ^ 2 ≤
        (N : ℝ) * ∑ k ∈ range N, b k ^ 2 * arithmeticDampingCenteredRow η n k ^ 2 := by
      intro n
      rw [arithmeticDampingCenteredOperator_apply_of_support hη b N hb n]
      have hcs := sum_mul_sq_le_sq_mul_sq (range N)
        (fun k => arithmeticDampingCenteredRow η n k * b k) (fun _ => (1 : ℝ))
      simp only [mul_one, one_pow, sum_const, card_range, nsmul_eq_mul] at hcs
      refine hcs.trans (le_of_eq ?_)
      rw [mul_comm (N : ℝ)]
      congr 1
      exact sum_congr rfl fun k _ => by ring
    have hsum : Summable (fun n : ℕ =>
        (N : ℝ) * ∑ k ∈ range N, b k ^ 2 * arithmeticDampingCenteredRow η n k ^ 2) :=
      (summable_sum fun k _ => (hcol k).mul_left (b k ^ 2)).mul_left (N : ℝ)
    exact Summable.of_nonneg_of_le (fun _ => sq_nonneg _) hle hsum
  · intro hb k
    let e_k : C₀(ℕ, ℝ) :=
      c0OfTendsto (fun j => if j = k then 1 else 0) (by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_ge_atTop (k + 1)] with j hj
        simp [show j ≠ k by omega])
    have hsupp : ∃ N : ℕ, ∀ j, N ≤ j → e_k j = 0 :=
      ⟨k + 1, fun j hj => by simp [e_k, show j ≠ k by omega]⟩
    have himg := hb e_k hsupp
    refine himg.congr fun n => ?_
    rw [arithmeticDampingCenteredOperator_apply_of_support hη e_k (k + 1)
      (fun j hj => by simp [e_k, show j ≠ k by omega]) n]
    simp [e_k]

/-! ## §5. Unconditional Column Square-Summability Above `Θ − 1/2` & RH Equivalence -/

/-- **Unconditional Column Square-Summability Above `Θ − 1/2`:**
While the uncentered first column `n ↦ P_η(n+1, 1)` is never square-summable
(`not_summable_transition_first_column`), **every** column `n ↦ C_η(n, k)` of the centered
damping chain `C_η` is square-summable for all `η > Θ − 1/2`, with total `ℓ²` mass at most
`O_η((k + 1)^{1 − 2η})`. -/
theorem summable_arithmeticDampingCenteredRow_sq_of_zetaZeroAbscissa_lt {η : ℝ}
    (hΘ : zetaZeroAbscissa < 1 / 2 + η) (k : ℕ) :
    Summable (fun n : ℕ => arithmeticDampingCenteredRow η n k ^ 2) := by
  have hmem := mem_receiverDampings_of_zetaZeroAbscissa_lt hΘ
  exact (mem_receiverDampings_iff_forall_column_summable hmem.1).mp hmem k

theorem exists_tsum_arithmeticDampingCenteredRow_sq_bound_of_zetaZeroAbscissa_lt {η : ℝ}
    (hΘ : zetaZeroAbscissa < 1 / 2 + η) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ k : ℕ,
      (∑' n : ℕ, arithmeticDampingCenteredRow η n k ^ 2) ≤
        K * ((k : ℝ) + 1) ^ (1 - 2 * η) := by
  have hmem := mem_receiverDampings_of_zetaZeroAbscissa_lt hΘ
  have hη0 : 0 < η := hmem.1
  obtain ⟨B, hB⟩ := hmem.2
  have hB0 : 0 ≤ B := le_trans (pmPowerDampedDivisorDiscreteEnergy_nonneg η 0) (hB 0)
  refine ⟨16 * (B + (pmPowerDampedDivisorDensity η).re ^ 2), by positivity, fun k => ?_⟩
  refine Real.tsum_le_of_sum_range_le (fun _ => sq_nonneg _) fun T => ?_
  exact (sum_range_arithmeticDampingCenteredRow_sq_le hη0.le k T).trans
    (mul_le_mul_of_nonneg_right (by linarith [hB T]) (Real.rpow_nonneg (by positivity) _))

/-- **Riemann Hypothesis Equivalence with First-Column Square-Summability:**
`RiemannHypothesis` holds if and only if the first column `n ↦ C_η(n, 0)` of the centered
arithmetic damping chain lies in `ℓ²(ℕ)` for every `η > 0` (or cofinally as `η → 0⁺`). -/
theorem riemannHypothesis_iff_forall_pos_first_column_summable :
    RiemannHypothesis ↔
      ∀ η : ℝ, 0 < η → Summable (fun n : ℕ => arithmeticDampingCenteredRow η n 0 ^ 2) := by
  constructor
  · intro hRH η hη
    have hΘ : zetaZeroAbscissa = 1 / 2 := zetaZeroAbscissa_eq_half_iff_riemannHypothesis.mpr hRH
    exact summable_arithmeticDampingCenteredRow_sq_of_zetaZeroAbscissa_lt (by linarith) 0
  · intro h
    rw [riemannHypothesis_iff_cofinal_budget]
    intro δ hδ
    have hmem := (mem_receiverDampings_iff_summable_first_column (by linarith : 0 < δ / 2)).mpr
      (h (δ / 2) (by linarith))
    obtain ⟨B, hB⟩ := hmem.2
    exact ⟨δ / 2, by linarith, by linarith, B, hB⟩

theorem riemannHypothesis_iff_cofinal_first_column_summable :
    RiemannHypothesis ↔
      ∀ δ : ℝ, 0 < δ → ∃ η : ℝ, 0 < η ∧ η < δ ∧
        Summable (fun n : ℕ => arithmeticDampingCenteredRow η n 0 ^ 2) := by
  rw [riemannHypothesis_iff_cofinal_budget]
  constructor
  · intro h δ hδ
    obtain ⟨η, hη, hηδ, B, hB⟩ := h δ hδ
    exact ⟨η, hη, hηδ, (mem_receiverDampings_iff_summable_first_column hη).mp ⟨hη, B, hB⟩⟩
  · intro h δ hδ
    obtain ⟨η, hη, hηδ, hs⟩ := h δ hδ
    obtain ⟨_, B, hB⟩ := (mem_receiverDampings_iff_summable_first_column hη).mpr hs
    exact ⟨η, hη, hηδ, B, hB⟩

end

end GaloisForLFunctions.BezoutValuationIncidence
