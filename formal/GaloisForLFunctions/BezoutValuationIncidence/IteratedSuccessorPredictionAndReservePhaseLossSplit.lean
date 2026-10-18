import GaloisForLFunctions.BezoutValuationIncidence.SharpSuccessorPhaseLossAndClosureClassification
import GaloisForLFunctions.BezoutValuationIncidence.PrimeTailCalibrationAndMobiusDefect

open Finset ArithmeticFunction GaloisForLFunctions.BiScaleUncertainty RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-!
# Pillar XX: Iterated Successor Prediction Contraction & Reserve–Phase-Loss Degeneracy Splitting

This module extends the optimal successor prediction and phase-loss theory
(`CoprimalitySuccessorPredictorAndSquarefreeInformation`,
`OptimalSuccessorPredictionAndExactPhaseLoss`,
`SharpSuccessorPhaseLossAndClosureClassification`) in two directions:

1. **Exact Variance–Phase-Loss Conservation, Parity Sign-Flip Involution, & Geometric $4^{-m}$
   Contraction Under Iterated Prediction
   (`selbergMultiplesCoord_successorPredictor_one_and_two`,
   `selbergMultiplesCoord_two_step_successorPredictor_one_and_two`,
   `sieveVarianceAboveParity_successorPredictor_add_phaseLoss`,
   `sieveVariance_successorPredictor_add_phaseLoss`,
   `selbergTotientDiagonalForm_successorPredictor_add_phaseLoss`,
   `sieveVarianceAboveParity_successorPredictor_bounds`,
   `sieveVarianceAboveParity_iterated_successorPredictor_le`):**
   - At $q = 1$, $\mathcal{K}_N = \text{sieveSuccessorPredictor}(N)$ preserves the harmonic pole
     coordinate $Y_{N,\mathcal{K}_N c}(1) = Y_{N,c}(1)$; at $q = 2$, it flips the parity sign
     $Y_{N,\mathcal{K}_N c}(2) = -Y_{N,c}(2)$, so two steps $\mathcal{K}_N^2$ act as the exact
     identity on both $q = 1$ and $q = 2$.
   - The Selberg quadratic form, total variance, and above-parity variance satisfy the exact
     Pythagorean conservation laws:
     $$\text{sieveVarianceAboveParity}(N, \mathcal{K}_N c) + \text{successorPhaseLoss}(N, c)
       = \text{sieveVarianceAboveParity}(N, c),$$
     $$\text{sieveVariance}(N, \mathcal{K}_N c) + \text{successorPhaseLoss}(N, c)
       = \text{sieveVariance}(N, c),$$
     $$\mathcal{Q}_{\text{Sel}}(N, \mathcal{K}_N c) + \text{successorPhaseLoss}(N, c)
       = \mathcal{Q}_{\text{Sel}}(N, c).$$
   - Combining this conservation law with `successorPhaseLoss_bounds` proves that $\mathcal{K}_N$
     is a sharp $1/4$-contraction on `sieveVarianceAboveParity`:
     $$0 \le \text{sieveVarianceAboveParity}(N, \mathcal{K}_N c)
       \le \frac{1}{4}\,\text{sieveVarianceAboveParity}(N, c),$$
     and under $m$ iterations:
     $$\text{sieveVarianceAboveParity}\big(N, \mathcal{K}_N^{[m]} c\big)
       \le \left(\frac{1}{4}\right)^m \text{sieveVarianceAboveParity}(N, c).$$

2. **Exact Splitting of the $\{3, 6\}$ Phase-Loss Degeneracy via `sieveSuccessorReserveAboveParity`
   (`sieveSuccessorReserve_eq_parity_add_aboveParity`,
   `successorPhaseLoss_reserveAboveParity_bounds`,
   `successorPhaseLoss_le_three_halves_successorReserve`,
   `successorPhaseLoss_eq_half_reserveAboveParity_iff`,
   `successorPhaseLoss_eq_three_halves_reserveAboveParity_iff`):**
   When `successorPhaseLoss` is compared against `sieveVarianceAboveParity`, modes $q = 3$ and
   $q = 6$ are degenerate at the lower endpoint $3/4$ because $\varphi(3) = \varphi(6) = 2$ and
   $\mu(3)^2 = \mu(6)^2 = 1$. Comparing `successorPhaseLoss` instead against the above-parity
   successor reserve
   $$\text{sieveSuccessorReserveAboveParity}(N, c)
     = \sum_{q=3}^N \big(\varphi(q) - \mu(q)\big) Y_{N,c}(q)^2$$
   completely splits the $\{3, 6\}$ tie into the two opposite extremal endpoints:
   $$\frac{1}{2}\,\text{sieveSuccessorReserveAboveParity}(N, c)
     \le \text{successorPhaseLoss}(N, c)
     \le \frac{3}{2}\,\text{sieveSuccessorReserveAboveParity}(N, c)
     \le \frac{3}{2}\,\text{sieveSuccessorReserve}(N, c),$$
   where:
   - Equality at the lower bound $1/2$ holds **if and only if** $Y_{N,c}(q) = 0$ for all
     $q \in [3, N] \setminus \{3\}$ (uniquely the $q = 3$ mode, where $\mu(3) = -1$),
   - Equality at the upper bound $3/2$ holds **if and only if** $Y_{N,c}(q) = 0$ for all
     $q \in [3, N] \setminus \{6\}$ (uniquely the Wall 11 mode $q = 6$, where $\mu(6) = +1$).
-/

/-! ## §1. Variance–Phase-Loss Conservation, Parity Involution, & Iterated $4^{-m}$ Contraction -/

/-- **Harmonic Preservation and Parity Sign-Flip of `sieveSuccessorPredictor`
(`selbergMultiplesCoord_successorPredictor_one_and_two`):**
At $q = 1$, `sieveSuccessorPredictor N` preserves the Selberg coordinate; at $q = 2$, it negates
the Selberg coordinate. -/
theorem selbergMultiplesCoord_successorPredictor_one_and_two (N : ℕ) (c : ℕ → ℝ) :
    selbergMultiplesCoord N (sieveSuccessorPredictor N c) 1 = selbergMultiplesCoord N c 1 ∧
      selbergMultiplesCoord N (sieveSuccessorPredictor N c) 2 = -selbergMultiplesCoord N c 2 := by
  constructor
  · rw [selbergMultiplesCoord_successorPredictor]
    norm_num [moebiusReal]
  · rw [selbergMultiplesCoord_successorPredictor]
    norm_num [moebiusReal, ArithmeticFunction.moebius_apply_prime Nat.prime_two]

/-- **Two-Step Involution on Constant and Parity Modes
(`selbergMultiplesCoord_two_step_successorPredictor_one_and_two`):**
Applying `sieveSuccessorPredictor N` twice restores both the $q = 1$ and $q = 2$ Selberg
coordinates identically. -/
theorem selbergMultiplesCoord_two_step_successorPredictor_one_and_two (N : ℕ) (c : ℕ → ℝ) :
    selbergMultiplesCoord N (sieveSuccessorPredictor N (sieveSuccessorPredictor N c)) 1 =
        selbergMultiplesCoord N c 1 ∧
      selbergMultiplesCoord N (sieveSuccessorPredictor N (sieveSuccessorPredictor N c)) 2 =
        selbergMultiplesCoord N c 2 := by
  obtain ⟨h1a, h2a⟩ := selbergMultiplesCoord_successorPredictor_one_and_two N
    (sieveSuccessorPredictor N c)
  obtain ⟨h1b, h2b⟩ := selbergMultiplesCoord_successorPredictor_one_and_two N c
  exact ⟨h1a.trans h1b, by linarith⟩

/-- **Exact Above-Parity Variance Conservation Law
(`sieveVarianceAboveParity_successorPredictor_add_phaseLoss`):**
For every cutoff `N : ℕ` and weight `c : ℕ → ℝ`:
`sieveVarianceAboveParity N (sieveSuccessorPredictor N c) + successorPhaseLoss N c = sieveVarianceAboveParity N c`. -/
theorem sieveVarianceAboveParity_successorPredictor_add_phaseLoss (N : ℕ) (c : ℕ → ℝ) :
    sieveVarianceAboveParity N (sieveSuccessorPredictor N c) + successorPhaseLoss N c =
      sieveVarianceAboveParity N c := by
  rw [successorPhaseLoss_eq_above_parity]
  unfold sieveVarianceAboveParity
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [selbergMultiplesCoord_successorPredictor]
  have hφ : (q.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (by have := (Finset.mem_Icc.mp hq).1; omega)).ne'
  field_simp
  ring

/-- **Exact Total Variance Conservation Law
(`sieveVariance_successorPredictor_add_phaseLoss`):**
For every cutoff `N : ℕ` and weight `c : ℕ → ℝ`:
`sieveVariance N (sieveSuccessorPredictor N c) + successorPhaseLoss N c = sieveVariance N c`. -/
theorem sieveVariance_successorPredictor_add_phaseLoss (N : ℕ) (c : ℕ → ℝ) :
    sieveVariance N (sieveSuccessorPredictor N c) + successorPhaseLoss N c =
      sieveVariance N c := by
  have hsplit : ∀ b : ℕ → ℝ,
      sieveVariance N b =
        (if 2 ≤ N then (selbergMultiplesCoord N b 2) ^ (2 : ℕ) else 0) +
          sieveVarianceAboveParity N b := by
    intro b
    unfold sieveVariance sieveVarianceAboveParity
    by_cases hN2 : 2 ≤ N
    · rw [if_pos hN2]
      have hIcc : Finset.Icc 2 N = insert 2 (Finset.Icc 3 N) := by
        ext q
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      have hnot : (2 : ℕ) ∉ Finset.Icc 3 N := by simp
      rw [hIcc, Finset.sum_insert hnot]
      norm_num
    · rw [if_neg hN2]
      have hemp1 : Finset.Icc 2 N = ∅ := Finset.Icc_eq_empty hN2
      have hemp2 : Finset.Icc 3 N = ∅ := Finset.Icc_eq_empty (by omega)
      simp [hemp1, hemp2]
  rw [hsplit (sieveSuccessorPredictor N c), hsplit c]
  have h2 := (selbergMultiplesCoord_successorPredictor_one_and_two N c).2
  have h2sq : (if 2 ≤ N then (selbergMultiplesCoord N (sieveSuccessorPredictor N c) 2) ^ (2 : ℕ) else 0) =
      if 2 ≤ N then (selbergMultiplesCoord N c 2) ^ (2 : ℕ) else 0 := by
    rw [h2, neg_sq]
  linarith [sieveVarianceAboveParity_successorPredictor_add_phaseLoss N c]

/-- **Exact Selberg Diagonal Form Conservation Law
(`selbergTotientDiagonalForm_successorPredictor_add_phaseLoss`):**
For every cutoff `N : ℕ` and weight `c : ℕ → ℝ`:
`selbergTotientDiagonalForm N (sieveSuccessorPredictor N c) + successorPhaseLoss N c = selbergTotientDiagonalForm N c`. -/
theorem selbergTotientDiagonalForm_successorPredictor_add_phaseLoss (N : ℕ) (c : ℕ → ℝ) :
    selbergTotientDiagonalForm N (sieveSuccessorPredictor N c) + successorPhaseLoss N c =
      selbergTotientDiagonalForm N c := by
  unfold selbergTotientDiagonalForm successorPhaseLoss
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [selbergMultiplesCoord_successorPredictor]
  have hφ : (q.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Finset.mem_Icc.mp hq).1).ne'
  field_simp
  ring

/-- **Sharp One-Step $1/4$-Contraction on `sieveVarianceAboveParity`
(`sieveVarianceAboveParity_successorPredictor_bounds`):**
For every cutoff `N : ℕ` and weight `c : ℕ → ℝ`:
`0 ≤ sieveVarianceAboveParity N (sieveSuccessorPredictor N c) ≤ (1 / 4) * sieveVarianceAboveParity N c`. -/
theorem sieveVarianceAboveParity_successorPredictor_bounds (N : ℕ) (c : ℕ → ℝ) :
    0 ≤ sieveVarianceAboveParity N (sieveSuccessorPredictor N c) ∧
      sieveVarianceAboveParity N (sieveSuccessorPredictor N c) ≤
        (1 / 4 : ℝ) * sieveVarianceAboveParity N c := by
  have hcons := sieveVarianceAboveParity_successorPredictor_add_phaseLoss N c
  have hloss := successorPhaseLoss_bounds N c
  constructor <;> linarith

/-- **Geometric $4^{-m}$ Contraction of Iterated Successor Prediction
(`sieveVarianceAboveParity_iterated_successorPredictor_le`):**
For every cutoff `N : ℕ`, weight `c : ℕ → ℝ`, and iteration count `m : ℕ`:
`sieveVarianceAboveParity N ((sieveSuccessorPredictor N)^[m] c) ≤ (1 / 4) ^ m * sieveVarianceAboveParity N c`. -/
theorem sieveVarianceAboveParity_iterated_successorPredictor_le (N : ℕ) (c : ℕ → ℝ) (m : ℕ) :
    sieveVarianceAboveParity N ((sieveSuccessorPredictor N)^[m] c) ≤
      (1 / 4 : ℝ) ^ m * sieveVarianceAboveParity N c := by
  induction m generalizing c with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply, pow_succ']
    have h1 := (sieveVarianceAboveParity_successorPredictor_bounds N c).2
    have h2 := ih (sieveSuccessorPredictor N c)
    have hpos : (0 : ℝ) ≤ (1 / 4 : ℝ) ^ m := by positivity
    calc
      sieveVarianceAboveParity N ((sieveSuccessorPredictor N)^[m] (sieveSuccessorPredictor N c))
        ≤ (1 / 4 : ℝ) ^ m * sieveVarianceAboveParity N (sieveSuccessorPredictor N c) := h2
      _ ≤ (1 / 4 : ℝ) ^ m * ((1 / 4 : ℝ) * sieveVarianceAboveParity N c) :=
        mul_le_mul_of_nonneg_left h1 hpos
      _ = (1 / 4 : ℝ) * (1 / 4 : ℝ) ^ m * sieveVarianceAboveParity N c := by ring

/-! ## §2. Reserve–Phase-Loss Bounds & Exact Splitting of the $\{3, 6\}$ Degeneracy -/

/-- The successor reserve carried by modes $q \ge 3$ above the parity mode $q = 2$:
`sieveSuccessorReserveAboveParity N c = ∑ q ∈ Icc 3 N, (φ(q) - μ(q)) * Y_{N,c}(q)²`. -/
def sieveSuccessorReserveAboveParity (N : ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ q ∈ Finset.Icc 3 N,
    ((q.totient : ℝ) - moebiusReal q) * (selbergMultiplesCoord N c q) ^ (2 : ℕ)

/-- **Decomposition of `sieveSuccessorReserve` into Parity and Above-Parity Components
(`sieveSuccessorReserve_eq_parity_add_aboveParity`):**
For every `N ≥ 2` and weight `c : ℕ → ℝ`:
`sieveSuccessorReserve N c = 2 * (selbergMultiplesCoord N c 2) ^ 2 + sieveSuccessorReserveAboveParity N c`. -/
theorem sieveSuccessorReserve_eq_parity_add_aboveParity {N : ℕ} (hN : 2 ≤ N) (c : ℕ → ℝ) :
    sieveSuccessorReserve N c =
      2 * (selbergMultiplesCoord N c 2) ^ (2 : ℕ) + sieveSuccessorReserveAboveParity N c := by
  unfold sieveSuccessorReserve sieveSuccessorReserveAboveParity
  rw [selbergSubBezoutQuadraticForm_eq_Icc_two (by omega) c]
  have hIcc : Finset.Icc 2 N = insert 2 (Finset.Icc 3 N) := by
    ext q
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hnot : (2 : ℕ) ∉ Finset.Icc 3 N := by simp
  rw [hIcc, Finset.sum_insert hnot]
  norm_num [moebiusReal, ArithmeticFunction.moebius_apply_prime Nat.prime_two]

private theorem reserve_phase_totient_ge_two {q : ℕ} (hq : 3 ≤ q) : (2 : ℝ) ≤ q.totient := by
  have hp := Nat.totient_pos.mpr (show 0 < q by omega)
  have hd := even_iff_two_dvd.mp (Nat.totient_even hq)
  exact_mod_cast Nat.le_of_dvd hp hd

private theorem reserve_phase_small_values :
    Nat.totient 4 = 2 ∧ moebiusReal 4 = 0 ∧ Nat.totient 6 = 2 ∧ moebiusReal 6 = 1 := by
  obtain ⟨h4, h6, hm4, hm6⟩ := wall11_totient_degeneracy_broken_by_bezout
  rw [h4] at hm4
  rw [h6] at hm6
  refine ⟨h4, ?_, h6, ?_⟩ <;> norm_num at hm4 hm6 ⊢ <;> linarith

private theorem phase_reserve_weight_bounds {q : ℕ} (hq : 3 ≤ q) :
    (1 / 2 : ℝ) * ((q.totient : ℝ) - moebiusReal q) ≤
        (q.totient : ℝ) - (moebiusReal q) ^ (2 : ℕ) / (q.totient : ℝ) ∧
      (q.totient : ℝ) - (moebiusReal q) ^ (2 : ℕ) / (q.totient : ℝ) ≤
        (3 / 2 : ℝ) * ((q.totient : ℝ) - moebiusReal q) := by
  have ht := reserve_phase_totient_ge_two hq
  have hp : (0 : ℝ) < q.totient := by linarith
  have hcases : moebiusReal q = -1 ∨ moebiusReal q = 0 ∨ moebiusReal q = 1 := by
    unfold moebiusReal
    rcases ArithmeticFunction.moebius_eq_or q with h | h | h <;> simp [h]
  rcases hcases with hm | hm | hm
  · rw [hm]
    constructor
    · rw [← sub_nonneg]
      have hid : (q.totient : ℝ) - (-1 : ℝ) ^ (2 : ℕ) / (q.totient : ℝ) -
          (1 / 2 : ℝ) * ((q.totient : ℝ) - -1) =
          ((q.totient : ℝ) - 2) * ((q.totient : ℝ) + 1) / (2 * (q.totient : ℝ)) := by
        field_simp [hp.ne']
        ring
      rw [hid]
      exact div_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
    · rw [← sub_nonneg]
      have hid : (3 / 2 : ℝ) * ((q.totient : ℝ) - -1) -
          ((q.totient : ℝ) - (-1 : ℝ) ^ (2 : ℕ) / (q.totient : ℝ)) =
          ((q.totient : ℝ) + 1) * ((q.totient : ℝ) + 2) / (2 * (q.totient : ℝ)) := by
        field_simp [hp.ne']
        ring
      rw [hid]
      exact div_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  · rw [hm]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, sub_zero]
    constructor <;> linarith
  · rw [hm]
    constructor
    · rw [← sub_nonneg]
      have hid : (q.totient : ℝ) - (1 : ℝ) ^ (2 : ℕ) / (q.totient : ℝ) -
          (1 / 2 : ℝ) * ((q.totient : ℝ) - 1) =
          ((q.totient : ℝ) - 1) * ((q.totient : ℝ) + 2) / (2 * (q.totient : ℝ)) := by
        field_simp [hp.ne']
        ring
      rw [hid]
      exact div_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
    · rw [← sub_nonneg]
      have hid : (3 / 2 : ℝ) * ((q.totient : ℝ) - 1) -
          ((q.totient : ℝ) - (1 : ℝ) ^ (2 : ℕ) / (q.totient : ℝ)) =
          ((q.totient : ℝ) - 1) * ((q.totient : ℝ) - 2) / (2 * (q.totient : ℝ)) := by
        field_simp [hp.ne']
        ring
      rw [hid]
      exact div_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)

private theorem phase_reserve_weight_lower_eq_iff {q : ℕ} (hq : 3 ≤ q) :
    (q.totient : ℝ) - (moebiusReal q) ^ (2 : ℕ) / (q.totient : ℝ) =
      (1 / 2 : ℝ) * ((q.totient : ℝ) - moebiusReal q) ↔ q = 3 := by
  constructor
  · intro h
    have ht := reserve_phase_totient_ge_two hq
    have hp : (q.totient : ℝ) ≠ 0 := by linarith
    have hcases : moebiusReal q = -1 ∨ moebiusReal q = 0 ∨ moebiusReal q = 1 := by
      unfold moebiusReal
      rcases ArithmeticFunction.moebius_eq_or q with hm | hm | hm <;> simp [hm]
    have ht2 : (q.totient : ℝ) ≤ 2 ∧ moebiusReal q = -1 := by
      rcases hcases with hm | hm | hm
      · refine ⟨?_, hm⟩
        rw [hm] at h
        field_simp [hp] at h
        nlinarith
      · rw [hm] at h
        norm_num at h
        linarith
      · rw [hm] at h
        field_simp [hp] at h
        nlinarith
    have hn : q.totient ≤ 2 := by exact_mod_cast ht2.1
    rcases (GaloisForLFunctions.HTGeometry.totient_le_two_iff (by omega)).mp hn with
      h1 | h2 | h3 | h4 | h6
    · omega
    · omega
    · exact h3
    · subst q
      rw [reserve_phase_small_values.2.1] at ht2
      norm_num at ht2
    · subst q
      rw [reserve_phase_small_values.2.2.2] at ht2
      norm_num at ht2
  · rintro rfl
    norm_num [Nat.totient_prime Nat.prime_three, moebiusReal,
      ArithmeticFunction.moebius_apply_prime Nat.prime_three]

private theorem phase_reserve_weight_upper_eq_iff {q : ℕ} (hq : 3 ≤ q) :
    (q.totient : ℝ) - (moebiusReal q) ^ (2 : ℕ) / (q.totient : ℝ) =
      (3 / 2 : ℝ) * ((q.totient : ℝ) - moebiusReal q) ↔ q = 6 := by
  constructor
  · intro h
    have ht := reserve_phase_totient_ge_two hq
    have hp : (q.totient : ℝ) ≠ 0 := by linarith
    have hcases : moebiusReal q = -1 ∨ moebiusReal q = 0 ∨ moebiusReal q = 1 := by
      unfold moebiusReal
      rcases ArithmeticFunction.moebius_eq_or q with hm | hm | hm <;> simp [hm]
    have ht2 : (q.totient : ℝ) ≤ 2 ∧ moebiusReal q = 1 := by
      rcases hcases with hm | hm | hm
      · rw [hm] at h
        field_simp [hp] at h
        nlinarith
      · rw [hm] at h
        norm_num at h
        linarith
      · refine ⟨?_, hm⟩
        rw [hm] at h
        field_simp [hp] at h
        nlinarith
    have hn : q.totient ≤ 2 := by exact_mod_cast ht2.1
    rcases (GaloisForLFunctions.HTGeometry.totient_le_two_iff (by omega)).mp hn with
      h1 | h2 | h3 | h4 | h6
    · omega
    · omega
    · subst q
      have hm3 : moebiusReal 3 = -1 := by
        norm_num [moebiusReal, ArithmeticFunction.moebius_apply_prime Nat.prime_three]
      linarith [ht2.2, hm3]
    · subst q
      rw [reserve_phase_small_values.2.1] at ht2
      norm_num at ht2
    · exact h6
  · rintro rfl
    rw [reserve_phase_small_values.2.2.1, reserve_phase_small_values.2.2.2]
    norm_num

/-- **Sharp Two-Sided Reserve–Phase-Loss Envelope Above Parity
(`successorPhaseLoss_reserveAboveParity_bounds`):**
For every cutoff `N : ℕ` and weight `c : ℕ → ℝ`:
`(1 / 2) * sieveSuccessorReserveAboveParity N c ≤ successorPhaseLoss N c ≤ (3 / 2) * sieveSuccessorReserveAboveParity N c`. -/
theorem successorPhaseLoss_reserveAboveParity_bounds (N : ℕ) (c : ℕ → ℝ) :
    (1 / 2 : ℝ) * sieveSuccessorReserveAboveParity N c ≤ successorPhaseLoss N c ∧
      successorPhaseLoss N c ≤ (3 / 2 : ℝ) * sieveSuccessorReserveAboveParity N c := by
  rw [successorPhaseLoss_eq_above_parity]
  unfold sieveSuccessorReserveAboveParity
  rw [Finset.mul_sum, Finset.mul_sum]
  constructor
  · refine Finset.sum_le_sum fun q hq => ?_
    have h := mul_le_mul_of_nonneg_right
      (phase_reserve_weight_bounds (Finset.mem_Icc.mp hq).1).1
      (sq_nonneg (selbergMultiplesCoord N c q))
    simpa only [mul_assoc] using h
  · refine Finset.sum_le_sum fun q hq => ?_
    have h := mul_le_mul_of_nonneg_right
      (phase_reserve_weight_bounds (Finset.mem_Icc.mp hq).1).2
      (sq_nonneg (selbergMultiplesCoord N c q))
    simpa only [mul_assoc] using h

/-- **Global Upper Bound of `successorPhaseLoss` by `3 / 2` of `sieveSuccessorReserve`
(`successorPhaseLoss_le_three_halves_successorReserve`):**
For every `N : ℕ` and `c : ℕ → ℝ`:
`successorPhaseLoss N c ≤ (3 / 2) * sieveSuccessorReserve N c`. -/
theorem successorPhaseLoss_le_three_halves_successorReserve (N : ℕ) (c : ℕ → ℝ) :
    successorPhaseLoss N c ≤ (3 / 2 : ℝ) * sieveSuccessorReserve N c := by
  by_cases hN : 2 ≤ N
  · rw [sieveSuccessorReserve_eq_parity_add_aboveParity hN c]
    have hup := (successorPhaseLoss_reserveAboveParity_bounds N c).2
    have h2 : 0 ≤ (selbergMultiplesCoord N c 2) ^ (2 : ℕ) := sq_nonneg _
    linarith
  · have hemp : Finset.Icc 3 N = ∅ := Finset.Icc_eq_empty (by omega)
    have hloss0 : successorPhaseLoss N c = 0 := by
      rw [successorPhaseLoss_eq_above_parity, hemp, Finset.sum_empty]
    have hres0 : 0 ≤ sieveSuccessorReserve N c := by
      rcases N with _ | N
      · simp [sieveSuccessorReserve, selbergTotientDiagonalForm, bezoutCoprimeQuadraticForm]
      · have hN1 : N + 1 = 1 := by omega
        rw [hN1]
        unfold sieveSuccessorReserve
        rw [selbergSubBezoutQuadraticForm_eq_Icc_two le_rfl c]
        simp
    linarith

/-- **Unique Mode-3 Characterization at the Lower Reserve–Phase-Loss Endpoint
(`successorPhaseLoss_eq_half_reserveAboveParity_iff`):**
`successorPhaseLoss N c = (1 / 2) * sieveSuccessorReserveAboveParity N c` if and only if every
above-parity Selberg coordinate outside $q = 3$ vanishes (`∀ q ∈ Icc 3 N, q ≠ 3 → Y_{N,c}(q) = 0`),
splitting $q = 3$ cleanly from $q = 6$. -/
theorem successorPhaseLoss_eq_half_reserveAboveParity_iff (N : ℕ) (c : ℕ → ℝ) :
    successorPhaseLoss N c = (1 / 2 : ℝ) * sieveSuccessorReserveAboveParity N c ↔
      ∀ q ∈ Finset.Icc 3 N, q ≠ 3 → selbergMultiplesCoord N c q = 0 := by
  have he : successorPhaseLoss N c - (1 / 2 : ℝ) * sieveSuccessorReserveAboveParity N c =
      ∑ q ∈ Finset.Icc 3 N,
        ((q.totient : ℝ) - (moebiusReal q) ^ (2 : ℕ) / (q.totient : ℝ) -
          (1 / 2 : ℝ) * ((q.totient : ℝ) - moebiusReal q)) *
          (selbergMultiplesCoord N c q) ^ (2 : ℕ) := by
    rw [successorPhaseLoss_eq_above_parity, sieveSuccessorReserveAboveParity,
      Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun q _ => by ring
  rw [← sub_eq_zero, he, Finset.sum_eq_zero_iff_of_nonneg (fun q hq =>
    mul_nonneg (sub_nonneg.mpr (phase_reserve_weight_bounds (Finset.mem_Icc.mp hq).1).1)
      (sq_nonneg _))]
  constructor
  · intro h q hq hq3
    have hn : (q.totient : ℝ) - (moebiusReal q) ^ (2 : ℕ) / (q.totient : ℝ) -
        (1 / 2 : ℝ) * ((q.totient : ℝ) - moebiusReal q) ≠ 0 := by
      intro hz
      exact hq3 ((phase_reserve_weight_lower_eq_iff (Finset.mem_Icc.mp hq).1).mp (sub_eq_zero.mp hz))
    exact sq_eq_zero_iff.mp ((mul_eq_zero.mp (h q hq)).resolve_left hn)
  · intro h q hq
    by_cases hq3 : q = 3
    · rw [(phase_reserve_weight_lower_eq_iff (Finset.mem_Icc.mp hq).1).mpr hq3]
      ring
    · rw [h q hq hq3]
      ring

/-- **Unique Wall 11 Mode-6 Characterization at the Upper Reserve–Phase-Loss Endpoint
(`successorPhaseLoss_eq_three_halves_reserveAboveParity_iff`):**
`successorPhaseLoss N c = (3 / 2) * sieveSuccessorReserveAboveParity N c` if and only if every
above-parity Selberg coordinate outside the Wall 11 mode $q = 6$ vanishes
(`∀ q ∈ Icc 3 N, q ≠ 6 → Y_{N,c}(q) = 0`), splitting $q = 6$ cleanly from $q = 3$. -/
theorem successorPhaseLoss_eq_three_halves_reserveAboveParity_iff (N : ℕ) (c : ℕ → ℝ) :
    successorPhaseLoss N c = (3 / 2 : ℝ) * sieveSuccessorReserveAboveParity N c ↔
      ∀ q ∈ Finset.Icc 3 N, q ≠ 6 → selbergMultiplesCoord N c q = 0 := by
  have he : (3 / 2 : ℝ) * sieveSuccessorReserveAboveParity N c - successorPhaseLoss N c =
      ∑ q ∈ Finset.Icc 3 N,
        ((3 / 2 : ℝ) * ((q.totient : ℝ) - moebiusReal q) -
          ((q.totient : ℝ) - (moebiusReal q) ^ (2 : ℕ) / (q.totient : ℝ))) *
          (selbergMultiplesCoord N c q) ^ (2 : ℕ) := by
    rw [successorPhaseLoss_eq_above_parity, sieveSuccessorReserveAboveParity,
      Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun q _ => by ring
  rw [eq_comm, ← sub_eq_zero, he, Finset.sum_eq_zero_iff_of_nonneg (fun q hq =>
    mul_nonneg (sub_nonneg.mpr (phase_reserve_weight_bounds (Finset.mem_Icc.mp hq).1).2)
      (sq_nonneg _))]
  constructor
  · intro h q hq hq6
    have hn : (3 / 2 : ℝ) * ((q.totient : ℝ) - moebiusReal q) -
        ((q.totient : ℝ) - (moebiusReal q) ^ (2 : ℕ) / (q.totient : ℝ)) ≠ 0 := by
      intro hz
      exact hq6 ((phase_reserve_weight_upper_eq_iff (Finset.mem_Icc.mp hq).1).mp (sub_eq_zero.mp hz).symm)
    exact sq_eq_zero_iff.mp ((mul_eq_zero.mp (h q hq)).resolve_left hn)
  · intro h q hq
    by_cases hq6 : q = 6
    · rw [(phase_reserve_weight_upper_eq_iff (Finset.mem_Icc.mp hq).1).mpr hq6]
      ring
    · rw [h q hq hq6]
      ring

end

end GaloisForLFunctions.BezoutValuationIncidence
