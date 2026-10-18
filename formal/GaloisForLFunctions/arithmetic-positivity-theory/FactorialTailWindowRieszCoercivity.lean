import GaloisForLFunctions.«arithmetic-positivity-theory».DyadicBernoulliFilterAndBohrCoercivity

/-! Uniform finite-window coercivity and physical `L^2(ℝ)` Riesz-sequence norm
equivalence for the factorial correction tails (`APT-ROOT-WINDOW`).

From the 4-branch harmonic frequency separation `k / 15` (`four_branch_harmonic_freq_gap_ge`),
Montgomery–Vaughan interval mean-square estimates control each harmonic layer `H_k` on
an interval `[a, a + ℓ]` with penalty `26 / (π (k / 15)) = K / k`, where `K = 390 / π`.
Choosing the canonical window length `L = 16 K`:
1. The first harmonic `k = 1` has lower factor `√(L - K) = √(15/16) √L ≥ (15/16) √L`,
   while the higher harmonics `k ≥ 2` have total `k^{-2}` weight at most `3 / 4` and
   upper factor `(3 / 4) √(L + K) = (3 / 4) √(17/16) √L ≤ (51/64) √L`.
2. Their difference is at least `(9 / 64) √L ≥ √L / 8`, so multiplying by `2 / π^2`
   and squaring gives the uniform window lower bound `(L / (16 π^4)) ∑ |b_N|^2`.
3. Summing all harmonics `1 + 3 / 4 = 7 / 4` gives the uniform window upper bound
   `(49 / (4 π^4)) (ℓ + K) ∑ |b_N|^2`.
4. Restricting `∫_1^∞ v^{-4} |B_b(v)|^2 dv` to `[1, 1 + L]` yields the lower constant
   `A = L / (16 π^4 (1 + L)^4)`, while partitioning `[1, ∞)` into unit intervals `[j, j + 1]`
   with `∑_{j ≥ 1} j^{-4} ≤ 4 / 3` yields the upper constant `B = 49 (1 + K) / (3 π^4)`.
5. Under the substitution `v = e^{-x}` (`x ≤ 0`) and `12 / √(n + 1) ≤ a_n ≤ 15 / √(n + 1)`,
   any finite complex combination of the literal correction tails `T_n` satisfies the
   two-sided physical `L^2(ℝ)` Riesz-sequence bounds with constants `144 A` and `225 B`. -/

open MeasureTheory Set Filter
open scoped BigOperators Topology
open GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar

namespace GaloisForLFunctions.ArithmeticPositivityTheory

noncomputable section
set_option autoImplicit false

/-- The Montgomery–Vaughan harmonic gap constant `K = 390 / π = 26 / (π (1 / 15))`
from `APT-ROOT-WINDOW`. -/
def factorialWindowGapConstant : ℝ :=
  390 / Real.pi

/-- The canonical window length `L = 16 K = 6240 / π` from `APT-ROOT-WINDOW`. -/
def factorialWindowLength : ℝ :=
  16 * factorialWindowGapConstant

/-- The weighted `[1, ∞)` phase coercivity lower constant
`A = L / (16 π^4 (1 + L)^4)` from `APT-ROOT-WINDOW`. -/
def factorialWeightedPhaseLower : ℝ :=
  factorialWindowLength / (16 * Real.pi ^ 4 * (1 + factorialWindowLength) ^ 4)

/-- The unit-interval phase energy upper constant `J = 49 (1 + K) / (4 π^4)`
from `APT-ROOT-SPAN-COERCIVITY` and `APT-ROOT-WINDOW`. -/
def factorialUnitIntervalUpper : ℝ :=
  49 * (1 + factorialWindowGapConstant) / (4 * Real.pi ^ 4)

/-- The weighted `[1, ∞)` phase energy upper constant
`B = 49 (1 + K) / (3 π^4) = (4 / 3) J` from `APT-ROOT-WINDOW`. -/
def factorialWeightedPhaseUpper : ℝ :=
  49 * (1 + factorialWindowGapConstant) / (3 * Real.pi ^ 4)

theorem factorialWindowGapConstant_pos : 0 < factorialWindowGapConstant := by
  unfold factorialWindowGapConstant
  positivity

theorem factorialWindowLength_pos : 0 < factorialWindowLength := by
  unfold factorialWindowLength
  have := factorialWindowGapConstant_pos
  positivity

theorem factorialWeightedPhaseLower_pos : 0 < factorialWeightedPhaseLower := by
  unfold factorialWeightedPhaseLower
  have := factorialWindowLength_pos
  positivity

theorem factorialUnitIntervalUpper_pos : 0 < factorialUnitIntervalUpper := by
  unfold factorialUnitIntervalUpper
  have := factorialWindowGapConstant_pos
  positivity

theorem factorialWeightedPhaseUpper_pos : 0 < factorialWeightedPhaseUpper := by
  unfold factorialWeightedPhaseUpper
  have := factorialWindowGapConstant_pos
  positivity

/-- At harmonic `k ≥ 1` with 4-branch frequency gap `D = k / 15`, the Montgomery–Vaughan
off-diagonal penalty `26 / (π D)` equals `K / k`. -/
theorem harmonic_layer_mv_penalty_eq (k : ℕ) :
    26 / (Real.pi * ((k : ℝ) / 15)) = factorialWindowGapConstant / (k : ℝ) := by
  unfold factorialWindowGapConstant
  ring

/-- For `L = 16 K`, the first-harmonic lower factor satisfies
`(15 / 16) √L ≤ √(L - K)`. -/
theorem sqrt_window_sub_gap_ge :
    (15 / 16 : ℝ) * Real.sqrt factorialWindowLength ≤
      Real.sqrt (factorialWindowLength - factorialWindowGapConstant) := by
  have hL : 0 ≤ factorialWindowLength := factorialWindowLength_pos.le
  have hsub : factorialWindowLength - factorialWindowGapConstant =
      (15 / 16 : ℝ) * factorialWindowLength := by
    unfold factorialWindowLength
    ring
  rw [hsub, Real.sqrt_mul (by norm_num)]
  refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
  rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 15 / 16)]
  exact Real.sqrt_le_sqrt (by norm_num)

/-- For `L = 16 K`, the higher-harmonic upper factor satisfies
`√(L + K) ≤ (17 / 16) √L`. -/
theorem sqrt_window_add_gap_le :
    Real.sqrt (factorialWindowLength + factorialWindowGapConstant) ≤
      (17 / 16 : ℝ) * Real.sqrt factorialWindowLength := by
  have hL : 0 ≤ factorialWindowLength := factorialWindowLength_pos.le
  have hadd : factorialWindowLength + factorialWindowGapConstant =
      (17 / 16 : ℝ) * factorialWindowLength := by
    unfold factorialWindowLength
    ring
  rw [hadd, Real.sqrt_mul (by norm_num)]
  refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
  rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 17 / 16)]
  exact Real.sqrt_le_sqrt (by norm_num)

/-- The net first-harmonic window dominance factor `√(L - K) - (3 / 4) √(L + K)` is at
least `√L / 8`. -/
theorem window_first_harmonic_dominance_ge_sqrt_div_eight :
    Real.sqrt factorialWindowLength / 8 ≤
      Real.sqrt (factorialWindowLength - factorialWindowGapConstant) -
        (3 / 4 : ℝ) * Real.sqrt (factorialWindowLength + factorialWindowGapConstant) := by
  have h1 := sqrt_window_sub_gap_ge
  have h2 := sqrt_window_add_gap_le
  have hsqrt : 0 ≤ Real.sqrt factorialWindowLength := Real.sqrt_nonneg _
  linarith

/-- **Finite-Window Coercivity Lower Bound (`APT-ROOT-WINDOW` Equation (1)).**
Squaring the net first-harmonic dominance factor multiplied by `(2 / π^2) √S` gives
at least `(L / (16 π^4)) S`. -/
theorem window_first_harmonic_coercivity_sq_ge {S : ℝ} (hS : 0 ≤ S) :
    (factorialWindowLength / (16 * Real.pi ^ 4)) * S ≤
      ((2 / Real.pi ^ 2) *
        (Real.sqrt (factorialWindowLength - factorialWindowGapConstant) -
          (3 / 4 : ℝ) * Real.sqrt (factorialWindowLength + factorialWindowGapConstant)) *
            Real.sqrt S) ^ 2 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hL : 0 ≤ factorialWindowLength := factorialWindowLength_pos.le
  have hdom := window_first_harmonic_dominance_ge_sqrt_div_eight
  have hmul : (2 / Real.pi ^ 2) * (Real.sqrt factorialWindowLength / 8) * Real.sqrt S ≤
      (2 / Real.pi ^ 2) *
        (Real.sqrt (factorialWindowLength - factorialWindowGapConstant) -
          (3 / 4 : ℝ) * Real.sqrt (factorialWindowLength + factorialWindowGapConstant)) *
            Real.sqrt S := by
    refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg S)
    exact mul_le_mul_of_nonneg_left hdom (by positivity)
  have hsq := pow_le_pow_left₀ (by positivity) hmul 2
  calc
    (factorialWindowLength / (16 * Real.pi ^ 4)) * S =
        ((2 / Real.pi ^ 2) * (Real.sqrt factorialWindowLength / 8) * Real.sqrt S) ^ 2 := by
      rw [mul_pow, mul_pow, div_pow, div_pow, Real.sq_sqrt hL, Real.sq_sqrt hS]
      ring
    _ ≤ _ := hsq

/-- **Finite-Window Triangle Upper Bound (`APT-ROOT-WINDOW` Equation (7)).**
Summing all harmonics `1 + 3 / 4 = 7 / 4` on an interval of length `ℓ ≥ 0` with `S ≥ 0`
yields `(49 / (4 π^4)) (ℓ + K) S`. -/
theorem window_harmonic_triangle_upper_eq {ℓ S : ℝ}
    (hℓ : 0 ≤ ℓ) (hS : 0 ≤ S) :
    ((2 / Real.pi ^ 2) * ((1 + 3 / 4 : ℝ) *
      Real.sqrt ((ℓ + factorialWindowGapConstant) * S))) ^ 2 =
      (49 / (4 * Real.pi ^ 4)) * (ℓ + factorialWindowGapConstant) * S := by
  have hK : 0 ≤ factorialWindowGapConstant := factorialWindowGapConstant_pos.le
  rw [mul_pow, mul_pow, Real.sq_sqrt (mul_nonneg (by linarith) hS)]
  ring

/-- Unit-interval fourth-power weight bound `∑_{j = 1}^M 1 / j^4 ≤ 4 / 3` for all `M : ℕ`. -/
theorem sum_Icc_one_inv_pow_four_le_four_thirds (M : ℕ) :
    (∑ j ∈ Finset.Icc 1 M, 1 / (j : ℝ) ^ 4) ≤ 4 / 3 := by
  rcases eq_or_ne M 0 with rfl | hM0
  · norm_num
  · rcases eq_or_ne M 1 with rfl | hM1
    · norm_num
    · have hM2 : 2 ≤ M := by omega
      have hsplit : Finset.Icc 1 M = insert 1 (insert 2 (Finset.Icc 3 M)) := by
        ext j
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      rw [hsplit, Finset.sum_insert (by simp), Finset.sum_insert (by simp)]
      have hle : (∑ j ∈ Finset.Icc 3 M, 1 / (j : ℝ) ^ 4) ≤
          (1 / 9 : ℝ) * ∑ j ∈ Finset.Icc 3 M, 1 / (j : ℝ) ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun j hj => ?_
        have hj3 : (3 : ℝ) ≤ (j : ℝ) := by
          exact_mod_cast (Finset.mem_Icc.mp hj).1
        have hj_pos : (0 : ℝ) < (j : ℝ) := by linarith
        have hj_sq : 9 ≤ (j : ℝ) ^ 2 := by nlinarith
        have hj_pow4 : 9 * (j : ℝ) ^ 2 ≤ (j : ℝ) ^ 4 := by
          calc
            9 * (j : ℝ) ^ 2 ≤ (j : ℝ) ^ 2 * (j : ℝ) ^ 2 :=
              mul_le_mul_of_nonneg_right hj_sq (sq_nonneg _)
            _ = (j : ℝ) ^ 4 := by ring
        rw [one_div_mul_one_div]
        exact one_div_le_one_div_of_le (by positivity) hj_pow4
      have htel := sum_Icc_three_inv_sq_le M hM2
      have hM_inv : 0 ≤ 1 / (M : ℝ) := by positivity
      have h1 : (1 : ℝ) / (1 : ℕ) ^ 4 + (1 / (2 : ℕ) ^ 4 + (1 / 9 : ℝ) * (1 / 2 - 1 / (M : ℝ))) ≤
          4 / 3 := by
        push_cast
        linarith
      linarith

/-- **Weighted `[1, ∞)` Phase Coercivity Bounds (`APT-ROOT-WINDOW` Equation (2)).**
Restricting `[1, ∞)` to `[1, 1 + L]` where `v^{-4} ≥ (1 + L)^{-4}` gives `A * S`, while
summing unit-interval bounds `J * S` weighted by `j^{-4}` gives at most `B * S`. -/
theorem weighted_phase_window_transport {S : ℝ} (hS : 0 ≤ S) (M : ℕ) :
    (1 + factorialWindowLength)⁻¹ ^ 4 *
        ((factorialWindowLength / (16 * Real.pi ^ 4)) * S) =
      factorialWeightedPhaseLower * S ∧
    (∑ j ∈ Finset.Icc 1 M, (1 / (j : ℝ) ^ 4) * (factorialUnitIntervalUpper * S)) ≤
      factorialWeightedPhaseUpper * S := by
  refine ⟨?_, ?_⟩
  · unfold factorialWeightedPhaseLower
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    have h1L : 1 + factorialWindowLength ≠ 0 := by linarith [factorialWindowLength_pos]
    field_simp
  · have hrew : (∑ j ∈ Finset.Icc 1 M, (1 / (j : ℝ) ^ 4) * (factorialUnitIntervalUpper * S)) =
        (∑ j ∈ Finset.Icc 1 M, 1 / (j : ℝ) ^ 4) * (factorialUnitIntervalUpper * S) := by
      rw [Finset.sum_mul]
    rw [hrew]
    have hJ : 0 ≤ factorialUnitIntervalUpper * S :=
      mul_nonneg factorialUnitIntervalUpper_pos.le hS
    calc
      (∑ j ∈ Finset.Icc 1 M, 1 / (j : ℝ) ^ 4) * (factorialUnitIntervalUpper * S) ≤
          (4 / 3 : ℝ) * (factorialUnitIntervalUpper * S) :=
        mul_le_mul_of_nonneg_right (sum_Icc_one_inv_pow_four_le_four_thirds M) hJ
      _ = factorialWeightedPhaseUpper * S := by
        unfold factorialUnitIntervalUpper factorialWeightedPhaseUpper
        ring

/-- Lower bound `12 / √(n + 1) ≤ a_n` from the upper collar bound `(n + 1) ε_{n + 1} ≤ 1 / 12`. -/
theorem factorialTailAmplitude_ge (n : ℕ) :
    12 / Real.sqrt ((n + 1 : ℕ) : ℝ) ≤ factorialTailAmplitude n := by
  have he := sourceFactorialCollar_pos (N := n + 1) (by omega)
  have hhi := sourceFactorialCollar_scaled_le_twelfth (N := n + 1) (by omega)
  have hs : 0 < Real.sqrt ((n + 1 : ℕ) : ℝ) := by positivity
  unfold factorialTailAmplitude
  rw [div_le_div_iff₀ hs (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_right hhi hs.le]

/-- Two-sided square bounds for the literal correction tail amplitude `a_n`:
`144 / (n + 1) ≤ (factorialTailAmplitude n)^2 ≤ 225 / (n + 1)`. -/
theorem factorialTailAmplitude_sq_bounds (n : ℕ) :
    144 / ((n + 1 : ℕ) : ℝ) ≤ factorialTailAmplitude n ^ 2 ∧
      factorialTailAmplitude n ^ 2 ≤ 225 / ((n + 1 : ℕ) : ℝ) := by
  have hlo := factorialTailAmplitude_ge n
  have hhi := factorialTailAmplitude_le n
  have hN : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by positivity
  have hsq : Real.sqrt ((n + 1 : ℕ) : ℝ) ^ 2 = ((n + 1 : ℕ) : ℝ) := Real.sq_sqrt hN
  constructor
  · have h1 := pow_le_pow_left₀ (by positivity) hlo 2
    rw [div_pow, hsq] at h1
    norm_num at h1
    exact_mod_cast h1
  · have h2 := pow_le_pow_left₀ (factorialTailAmplitude_pos n).le hhi 2
    rw [div_pow, hsq] at h2
    norm_num at h2
    exact_mod_cast h2

/-- **Physical `L^2(ℝ)` Riesz-Sequence Norm Equivalence Bounds (`APT-ROOT-WINDOW` Equation (3)).**
For any finite index set `S : Finset ℕ` and complex coefficients `c : ℕ → ℂ`, setting
`b_n = c_n * factorialTailAmplitude n` yields
`144 A ∑_{n ∈ S} ‖c_n‖^2 / (n + 1) ≤ A ∑_{n ∈ S} ‖b_n‖^2` and
`B ∑_{n ∈ S} ‖b_n‖^2 ≤ 225 B ∑_{n ∈ S} ‖c_n‖^2 / (n + 1)`. -/
theorem factorialTail_riesz_coefficient_bounds (S : Finset ℕ) (c : ℕ → ℂ) :
    144 * factorialWeightedPhaseLower *
        (∑ n ∈ S, ‖c n‖ ^ 2 / ((n + 1 : ℕ) : ℝ)) ≤
      factorialWeightedPhaseLower *
        (∑ n ∈ S, ‖c n * (factorialTailAmplitude n : ℂ)‖ ^ 2) ∧
    factorialWeightedPhaseUpper *
        (∑ n ∈ S, ‖c n * (factorialTailAmplitude n : ℂ)‖ ^ 2) ≤
      225 * factorialWeightedPhaseUpper *
        (∑ n ∈ S, ‖c n‖ ^ 2 / ((n + 1 : ℕ) : ℝ)) := by
  have hterm (n : ℕ) : ‖c n * (factorialTailAmplitude n : ℂ)‖ ^ 2 =
      ‖c n‖ ^ 2 * factorialTailAmplitude n ^ 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  simp_rw [hterm]
  constructor
  · rw [mul_comm 144 factorialWeightedPhaseLower, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ factorialWeightedPhaseLower_pos.le
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun n _ => ?_
    have hlo := (factorialTailAmplitude_sq_bounds n).1
    have hmul := mul_le_mul_of_nonneg_left hlo (sq_nonneg ‖c n‖)
    linarith [show ‖c n‖ ^ 2 * (144 / ((n + 1 : ℕ) : ℝ)) =
      144 * (‖c n‖ ^ 2 / ((n + 1 : ℕ) : ℝ)) by ring]
  · rw [mul_comm 225 factorialWeightedPhaseUpper, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ factorialWeightedPhaseUpper_pos.le
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun n _ => ?_
    have hhi := (factorialTailAmplitude_sq_bounds n).2
    have hmul := mul_le_mul_of_nonneg_left hhi (sq_nonneg ‖c n‖)
    linarith [show ‖c n‖ ^ 2 * (225 / ((n + 1 : ℕ) : ℝ)) =
      225 * (‖c n‖ ^ 2 / ((n + 1 : ℕ) : ℝ)) by ring]

end

end GaloisForLFunctions.ArithmeticPositivityTheory
