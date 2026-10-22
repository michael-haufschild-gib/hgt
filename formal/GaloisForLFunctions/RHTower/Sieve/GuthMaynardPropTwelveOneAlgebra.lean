import GaloisForLFunctions.RHTower.Sieve.GuthMaynardKeyPropExponentAlgebra

/-!
# The algebra of Guth–Maynard Proposition 12.1

Proposition 12.1 (`prpstn:BigN`) treats `T^{5/6} ≤ N ≤ T`, `V = N^σ`, `σ ≥ 7/10`.  Its proof
combines (12.1) (`fullBound`) with the classical bound (1.2) through three facts proved here:

* **dominations** (`bigN_term_five_le`, `bigN_term_seven_le`, `bigN_term_eight_le`): for
  `N ≥ T^{5/6}`, `σ ≥ 7/10`, the 5th, 7th and 8th terms of (12.1) are at most `T^{1/2}N^{3−4σ}`;
* **the minimum** (`min_le_bigN_term_six`): `min(TN^{1−2σ}, N^{5−6σ}) ≤ T^{1/2}N^{3−4σ}`
  (the geometric mean);
* **monomial form and rescaling** (`fullBound_eq_sum_monomial`, `fullBound_le_of_rescale`): every
  term of (12.1) is `T^a N^b (N^{−σ})^c` with `a, b, c ≥ 0` and `a + b + c ≤ 13`, so replacing
  `(N, T, N^{−σ})` by quantities at most twice as large costs at most `2^{13}`.  This is how a
  bound for the plateau pieces `N_i ∈ [5N/6, 2N]` (level `V/2`, interval length `2T`) returns to
  `(N, T, σ)`.

`exists_nat_mem_interval_of_length_ge_one` is the integer choice of the explicit form: an
interval `[L, U]` with `U ≥ 1` and `U − L ≥ 1` contains a positive integer.
-/

set_option autoImplicit false

open Finset

namespace RHTower.GuthMaynard

noncomputable section

/-! ### The dominations for `N ≥ T^{5/6}` -/

/-- `T^{4/3} N^{2−4σ} ≤ T^{1/2} N^{3−4σ}` for `N ≥ T^{5/6}`. -/
theorem bigN_term_five_le {N T σ : ℝ} (hT : 0 < T) (hN : T ^ (5 / 6 : ℝ) ≤ N) :
    T ^ (4 / 3 : ℝ) * N ^ (2 - 4 * σ) ≤ T ^ (1 / 2 : ℝ) * N ^ (3 - 4 * σ) := by
  have hN0 : 0 < N := lt_of_lt_of_le (Real.rpow_pos_of_pos hT _) hN
  have e1 : T ^ (4 / 3 : ℝ) = T ^ (1 / 2 : ℝ) * T ^ (5 / 6 : ℝ) := by
    rw [← Real.rpow_add hT]; norm_num
  have e2 : N ^ (3 - 4 * σ) = N * N ^ (2 - 4 * σ) := by
    rw [show 3 - 4 * σ = 1 + (2 - 4 * σ) by ring, Real.rpow_add hN0, Real.rpow_one]
  rw [e1, e2, mul_assoc]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hN (by positivity)) (by positivity)

/-- `T^{1/2} ≤ N^{3/5}` and `T^{17/38} ≤ N^{51/95}` for `N ≥ T^{5/6}`. -/
theorem rpow_le_of_five_sixths_le {N T a : ℝ} (hT : 0 < T) (hN : T ^ (5 / 6 : ℝ) ≤ N)
    (ha : 0 ≤ a) : T ^ a ≤ N ^ (6 / 5 * a) := by
  calc T ^ a = (T ^ (5 / 6 : ℝ)) ^ (6 / 5 * a) := by
        rw [← Real.rpow_mul hT.le]; congr 1; ring
    _ ≤ N ^ (6 / 5 * a) := Real.rpow_le_rpow (Real.rpow_nonneg hT.le _) hN (by positivity)

/-- `T N^{9/2−7σ} ≤ T^{1/2} N^{3−4σ}` for `N ≥ T^{5/6}`, `N ≥ 1`, `σ ≥ 7/10`. -/
theorem bigN_term_seven_le {N T σ : ℝ} (hT : 0 < T) (hN1 : 1 ≤ N) (hN : T ^ (5 / 6 : ℝ) ≤ N)
    (hσ : 7 / 10 ≤ σ) : T * N ^ (9 / 2 - 7 * σ) ≤ T ^ (1 / 2 : ℝ) * N ^ (3 - 4 * σ) := by
  have hN0 : 0 < N := by linarith
  have h1 := rpow_le_of_five_sixths_le hT hN (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have e1 : T = T ^ (1 / 2 : ℝ) * T ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_add hT]; norm_num
  calc T * N ^ (9 / 2 - 7 * σ) = T ^ (1 / 2 : ℝ) * (T ^ (1 / 2 : ℝ) * N ^ (9 / 2 - 7 * σ)) := by
        rw [← mul_assoc, ← e1]
    _ ≤ T ^ (1 / 2 : ℝ) * (N ^ (6 / 5 * (1 / 2)) * N ^ (9 / 2 - 7 * σ)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 (by positivity)) (by positivity)
    _ = T ^ (1 / 2 : ℝ) * N ^ (6 / 5 * (1 / 2) + (9 / 2 - 7 * σ)) := by
        congr 1; exact (Real.rpow_add hN0 _ _).symm
    _ ≤ T ^ (1 / 2 : ℝ) * N ^ (3 - 4 * σ) := by
        gcongr
        linarith

/-- `T^{18/19} N^{72/19−112σ/19} ≤ T^{1/2} N^{3−4σ}` for `N ≥ T^{5/6}`, `N ≥ 1`, `σ ≥ 7/10`. -/
theorem bigN_term_eight_le {N T σ : ℝ} (hT : 0 < T) (hN1 : 1 ≤ N) (hN : T ^ (5 / 6 : ℝ) ≤ N)
    (hσ : 7 / 10 ≤ σ) :
    T ^ (18 / 19 : ℝ) * N ^ (72 / 19 - 112 * σ / 19) ≤ T ^ (1 / 2 : ℝ) * N ^ (3 - 4 * σ) := by
  have hN0 : 0 < N := by linarith
  have h1 := rpow_le_of_five_sixths_le hT hN (by norm_num : (0 : ℝ) ≤ 17 / 38)
  have e1 : T ^ (18 / 19 : ℝ) = T ^ (1 / 2 : ℝ) * T ^ (17 / 38 : ℝ) := by
    rw [← Real.rpow_add hT]; norm_num
  calc T ^ (18 / 19 : ℝ) * N ^ (72 / 19 - 112 * σ / 19)
      = T ^ (1 / 2 : ℝ) * (T ^ (17 / 38 : ℝ) * N ^ (72 / 19 - 112 * σ / 19)) := by
        rw [e1, mul_assoc]
    _ ≤ T ^ (1 / 2 : ℝ) * (N ^ (6 / 5 * (17 / 38)) * N ^ (72 / 19 - 112 * σ / 19)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 (by positivity)) (by positivity)
    _ = T ^ (1 / 2 : ℝ) * N ^ (6 / 5 * (17 / 38) + (72 / 19 - 112 * σ / 19)) := by
        congr 1; exact (Real.rpow_add hN0 _ _).symm
    _ ≤ T ^ (1 / 2 : ℝ) * N ^ (3 - 4 * σ) := by
        gcongr
        linarith

/-- **The minimum.**  `min(TN^{1−2σ}, N^{5−6σ}) ≤ T^{1/2}N^{3−4σ}`, the geometric mean. -/
theorem min_le_bigN_term_six {N T σ : ℝ} (hT : 0 < T) (hN : 0 < N) :
    min (T * N ^ (1 - 2 * σ)) (N ^ (5 - 6 * σ)) ≤ T ^ (1 / 2 : ℝ) * N ^ (3 - 4 * σ) := by
  have ha : 0 ≤ T * N ^ (1 - 2 * σ) := by positivity
  have hb : 0 ≤ N ^ (5 - 6 * σ) := by positivity
  have h1 : (T ^ (1 / 2 : ℝ)) ^ 2 = T := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hT.le]; norm_num
  have h2 : (N ^ (3 - 4 * σ)) ^ 2 = N ^ (1 - 2 * σ) * N ^ (5 - 6 * σ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le, ← Real.rpow_add hN]
    congr 1; push_cast; ring
  have hsq : (T ^ (1 / 2 : ℝ) * N ^ (3 - 4 * σ)) ^ 2 = T * N ^ (1 - 2 * σ) * N ^ (5 - 6 * σ) := by
    rw [mul_pow, h1, h2, mul_assoc]
  have hm0 : 0 ≤ min (T * N ^ (1 - 2 * σ)) (N ^ (5 - 6 * σ)) := le_min ha hb
  have hm2 : min (T * N ^ (1 - 2 * σ)) (N ^ (5 - 6 * σ)) ^ 2 ≤
      T * N ^ (1 - 2 * σ) * N ^ (5 - 6 * σ) := by
    rw [sq]; exact mul_le_mul (min_le_left _ _) (min_le_right _ _) hm0 ha
  rw [← hsq] at hm2
  exact (pow_le_pow_iff_left₀ hm0 (by positivity) two_ne_zero).mp hm2

/-! ### Monomial form of (12.1) and rescaling -/

/-- The `T`-, `N`- and `N^{−σ}`-exponents of the eight terms of `fullBound`. -/
def fullBoundTExp (j k : ℕ) : Fin 8 → ℝ :=
  ![0, 0, (j : ℝ) / (j + 1), 2 / (4 * (k : ℝ) + 3), 4 / 3, 1 / 2, 1, 18 / 19]
def fullBoundNExp (j k : ℕ) : Fin 8 → ℝ :=
  ![2, 5, 4 * ((j : ℝ) / (j + 1)), 5 * (4 * (k : ℝ) / (4 * k + 3)), 2, 3, 9 / 2, 72 / 19]
def fullBoundUExp (j k : ℕ) : Fin 8 → ℝ :=
  ![2, 6, 6 * ((j : ℝ) / (j + 1)), 6 * (4 * (k : ℝ) / (4 * k + 3)), 4, 4, 7, 112 / 19]

/-- `T^a N^b (N^{−σ})^c = T^a N^{b − σc}`. -/
theorem monomial_rpow_neg_eq {N T a b c σ : ℝ} (hN : 0 < N) :
    T ^ a * N ^ b * (N ^ (-σ)) ^ c = T ^ a * N ^ (b - σ * c) := by
  rw [← Real.rpow_mul hN.le, mul_assoc, ← Real.rpow_add hN]
  congr 2; ring

/-- **(12.1) in monomial form**: `fullBound N T σ = Σ_i T^{a_i} N^{b_i} (N^{−σ})^{c_i}`. -/
theorem fullBound_eq_sum_monomial {N T : ℝ} (hN : 0 < N) (σ : ℝ) (j k : ℕ) :
    fullBound N T σ j k =
      ∑ i, T ^ fullBoundTExp j k i * N ^ fullBoundNExp j k i * (N ^ (-σ)) ^ fullBoundUExp j k i := by
  simp only [Fin.sum_univ_eight, fullBoundTExp, fullBoundNExp, fullBoundUExp, Matrix.cons_val,
    monomial_rpow_neg_eq hN, Real.rpow_zero, one_mul, Real.rpow_one, fullBound]
  ring_nf

/-- The exponents are nonnegative and sum to at most `13`. -/
theorem fullBoundExp_bounds {j k : ℕ} (i : Fin 8) :
    0 ≤ fullBoundTExp j k i ∧ 0 ≤ fullBoundNExp j k i ∧ 0 ≤ fullBoundUExp j k i ∧
      fullBoundTExp j k i + fullBoundNExp j k i + fullBoundUExp j k i ≤ 13 := by
  have hθ0 : 0 ≤ (j : ℝ) / (j + 1) := by positivity
  have hθ1 : (j : ℝ) / (j + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  have hφ0 : 0 ≤ 4 * (k : ℝ) / (4 * k + 3) := by positivity
  have hφ1 : 4 * (k : ℝ) / (4 * k + 3) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  have hψ0 : 0 ≤ 2 / (4 * (k : ℝ) + 3) := by positivity
  have hψ1 : 2 / (4 * (k : ℝ) + 3) ≤ 1 := by
    rw [div_le_one (by positivity)]; have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith
  fin_cases i <;> simp only [fullBoundTExp, fullBoundNExp, fullBoundUExp] <;>
    refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num <;> linarith

/-- `x^a y^b z^c` is monotone and `(2x)^a (2y)^b (2z)^c ≤ 2^{13} x^a y^b z^c` when
`a, b, c ≥ 0`, `a + b + c ≤ 13`. -/
theorem monomial_le_of_le_two_mul {x y z x' y' z' a b c : ℝ} (hx : 0 ≤ x') (hy : 0 ≤ y')
    (hz : 0 ≤ z') (hxx : x' ≤ 2 * x) (hyy : y' ≤ 2 * y) (hzz : z' ≤ 2 * z) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (habc : a + b + c ≤ 13) :
    x' ^ a * y' ^ b * z' ^ c ≤ 2 ^ (13 : ℝ) * (x ^ a * y ^ b * z ^ c) := by
  have hx0 : 0 ≤ x := by linarith
  have hy0 : 0 ≤ y := by linarith
  have hz0 : 0 ≤ z := by linarith
  calc x' ^ a * y' ^ b * z' ^ c ≤ (2 * x) ^ a * (2 * y) ^ b * (2 * z) ^ c := by gcongr
    _ = 2 ^ (a + b + c) * (x ^ a * y ^ b * z ^ c) := by
        rw [Real.mul_rpow (by norm_num) hx0, Real.mul_rpow (by norm_num) hy0,
          Real.mul_rpow (by norm_num) hz0, Real.rpow_add (by norm_num), Real.rpow_add (by norm_num)]
        ring
    _ ≤ 2 ^ (13 : ℝ) * (x ^ a * y ^ b * z ^ c) := by
        gcongr
        · norm_num

/-- **Rescaling (12.1).**  If `0 < M ≤ 2N`, `0 < T' ≤ 2T` and `M^{−σ'} ≤ 2 N^{−σ}`, then
`fullBound M T' σ' ≤ 2^{13} fullBound N T σ`. -/
theorem fullBound_le_of_rescale {N T M T' σ σ' : ℝ} {j k : ℕ} (hM : 0 < M) (hN : 0 < N)
    (hT' : 0 < T') (hMN : M ≤ 2 * N) (hTT : T' ≤ 2 * T)
    (hU : M ^ (-σ') ≤ 2 * N ^ (-σ)) :
    fullBound M T' σ' j k ≤ 2 ^ (13 : ℝ) * fullBound N T σ j k := by
  rw [fullBound_eq_sum_monomial hM, fullBound_eq_sum_monomial hN, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  obtain ⟨ha, hb, hc, habc⟩ := fullBoundExp_bounds (j := j) (k := k) i
  exact monomial_le_of_le_two_mul hT'.le hM.le (Real.rpow_nonneg hM.le _) hTT hMN hU ha hb hc habc

/-! ### The integer choice of the explicit form -/

/-- An interval `[L, U]` with `1 ≤ U` and `L ≤ U − 1` contains a positive integer (`⌊U⌋`). -/
theorem exists_nat_mem_interval_of_length_ge_one {L U : ℝ} (hU : 1 ≤ U) (hLU : L ≤ U - 1) :
    ∃ k : ℕ, 1 ≤ k ∧ L ≤ k ∧ (k : ℝ) ≤ U := by
  refine ⟨⌊U⌋₊, ?_, ?_, Nat.floor_le (by linarith)⟩
  · exact Nat.one_le_floor_iff _ |>.mpr hU
  · have := Nat.lt_floor_add_one U
    linarith

end

end RHTower.GuthMaynard
