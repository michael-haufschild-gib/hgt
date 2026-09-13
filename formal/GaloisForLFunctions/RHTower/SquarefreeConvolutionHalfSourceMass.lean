import GaloisForLFunctions.RHTower.ZetaBinomialHalfFractionalPole
import GaloisForLFunctions.HTGeometry.PowerSeriesTailBound

/-!
# Strict correction-mass reserve for the actual convolution half

The actual square-supported correction has absolute Dirichlet tail mass strictly below one
at `s = 2/3`. The proof compares its undilated coefficients with the positive zeta half at
`4/3`; the comparison is strict already at the prime square `4`.

This supplies a positive reserve for a signed heat-source estimate. It constructs no analytic
root across possible zeros and makes no claim of local boundedness of root approximants.
-/

open ArithmeticFunction Complex Filter Topology
open scoped BigOperators ComplexOrder
noncomputable section
namespace RHTower

theorem abs_choose_half_le_abs_choose_neg_half (k : ℕ) :
    |Ring.choose (1 / 2 : ℝ) k| ≤ |Ring.choose (-1 / 2 : ℝ) k| := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hp := congrArg abs (GaloisForLFunctions.choose_succ_field (1 / 2) k)
    have hm := congrArg abs (GaloisForLFunctions.choose_succ_field (-1 / 2) k)
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hd : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    simp only [abs_mul, abs_of_pos hd] at hp hm
    have hf : |(1 / 2 : ℝ) - k| ≤ |(-1 / 2 : ℝ) - k| := by
      rw [abs_of_nonpos (by linarith : (-1 / 2 : ℝ) - k ≤ 0)]
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    have h := mul_le_mul ih hf (abs_nonneg _) (abs_nonneg _)
    rw [← hp, ← hm] at h
    exact (mul_le_mul_iff_right₀ hd).mp h

theorem norm_choose_half_le_norm_choose_neg_half (k : ℕ) :
    ‖Ring.choose (1 / 2 : ℂ) k‖ ≤ ‖Ring.choose (-1 / 2 : ℂ) k‖ := by
  have hp : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
  have hm : (-1 / 2 : ℂ) = ((-1 / 2 : ℝ) : ℂ) := by norm_num
  rw [hp, hm, ← Complex.ofReal_choose, ← Complex.ofReal_choose,
    Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
  exact abs_choose_half_le_abs_choose_neg_half k

/-- Complete coefficientwise domination, including nonsquarefree integers. -/
theorem norm_moebiusBinomialHalf_le_norm_zetaBinomialHalf (n : ℕ) :
    ‖moebiusBinomialHalf n‖ ≤ ‖zetaBinomialHalf n‖ := by
  by_cases hn : n = 0
  · subst n; simp
  rw [moebiusBinomialHalf_isMultiplicative.multiplicative_factorization _ hn,
    zetaBinomialHalf_isMultiplicative.multiplicative_factorization _ hn,
    Finsupp.prod, Finsupp.prod, norm_prod, norm_prod]
  apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
  intro p hp
  have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
  rw [moebiusBinomialHalf_apply_prime_pow hprime,
    zetaBinomialHalf_apply_prime_pow hprime]
  simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  exact norm_choose_half_le_norm_choose_neg_half _

/-- One prime square makes the full summable comparison strict. -/
theorem norm_moebiusBinomialHalf_four_lt :
    ‖moebiusBinomialHalf 4‖ < ‖zetaBinomialHalf 4‖ := by
  rw [show 4 = 2 ^ 2 by rfl,
    moebiusBinomialHalf_apply_prime_pow Nat.prime_two,
    zetaBinomialHalf_apply_prime_pow_eq_centralBinom Nat.prime_two]
  have hrec := GaloisForLFunctions.choose_succ_field (1 / 2) 1
  norm_num at hrec
  have hchoose : Ring.choose (1 / 2 : ℝ) 2 = -1 / 8 := by linarith
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
    ← Complex.ofReal_choose, hchoose]
  norm_num [Nat.centralBinom, Nat.choose]

theorem tsum_nat_rpow_neg_four_thirds_le_four :
    (∑' n : ℕ, (n : ℝ) ^ (-4 / 3 : ℝ)) ≤ 4 := by
  have hs : Summable (fun n : ℕ => (n : ℝ) ^ (-4 / 3 : ℝ)) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have ht : (∑' n : ℕ, ((n + 2 : ℕ) : ℝ) ^ (-4 / 3 : ℝ)) ≤ 3 := by
    apply Real.tsum_le_of_sum_range_le (fun n => Real.rpow_nonneg (by positivity) _)
    intro N
    have h := GaloisForLFunctions.sum_shift_rpow_tail_le (s := 4 / 3) (by norm_num) 0 N
    norm_num only [Nat.cast_zero, zero_add, Real.one_rpow] at h
    convert h using 1
    · apply Finset.sum_congr rfl
      intro n _
      congr 1 <;> push_cast <;> ring
  have heq := hs.sum_add_tsum_nat_add 2
  norm_num [Finset.sum_range_succ] at heq
  norm_num only [Nat.cast_add, Nat.cast_ofNat, neg_div] at ht ⊢
  linarith

theorem norm_riemannZeta_four_thirds_le_four :
    ‖riemannZeta (4 / 3 : ℂ)‖ ≤ 4 := by
  have hs : LSeriesSummable (1 : ℕ → ℂ) (4 / 3 : ℂ) :=
    LSeriesSummable_one_iff.mpr (by norm_num)
  have hterm (n : ℕ) :
      ‖LSeries.term (1 : ℕ → ℂ) (4 / 3 : ℂ) n‖ = (n : ℝ) ^ (-4 / 3 : ℝ) := by
    by_cases hn : n = 0
    · subst n; norm_num
    rw [LSeries.norm_term_eq, if_neg hn]
    rw [show (4 / 3 : ℂ).re = (4 / 3 : ℝ) by norm_num]
    simp only [Pi.one_apply, norm_one, neg_div, Real.rpow_neg (Nat.cast_nonneg n), one_div]
  rw [← LSeries_one_eq_riemannZeta (by norm_num : 1 < (4 / 3 : ℂ).re)]
  exact (norm_tsum_le_tsum_norm hs.norm).trans
    ((tsum_congr hterm).le.trans tsum_nat_rpow_neg_four_thirds_le_four)

/-- Real-axis positivity identifies the zeta-half sum with its absolute sum. -/
theorem LSeries_zetaBinomialHalf_eq_ofReal_tsum_norm (x : ℝ) :
    LSeries zetaBinomialHalf (x : ℂ) =
      ((∑' n, ‖LSeries.term zetaBinomialHalf (x : ℂ) n‖ : ℝ) : ℂ) := by
  unfold LSeries
  rw [Complex.ofReal_tsum]
  apply tsum_congr
  intro n
  exact Complex.eq_coe_norm_of_nonneg
    (LSeries.term_nonneg (zetaBinomialHalf_apply_nonneg_complex n) x)

theorem tsum_norm_zetaBinomialHalf_four_thirds_le_two :
    (∑' n, ‖LSeries.term zetaBinomialHalf (4 / 3 : ℂ) n‖) ≤ 2 := by
  let B : ℝ := ∑' n, ‖LSeries.term zetaBinomialHalf (4 / 3 : ℂ) n‖
  have hB : 0 ≤ B := tsum_nonneg (fun _ => norm_nonneg _)
  have heq := LSeries_zetaBinomialHalf_eq_ofReal_tsum_norm (4 / 3)
  rw [show ((4 / 3 : ℝ) : ℂ) = (4 / 3 : ℂ) by push_cast; rfl] at heq
  have hsq := congrArg norm (LSeries_zetaBinomialHalf_sq (s := 4 / 3) (by norm_num))
  rw [heq, norm_mul, Complex.norm_of_nonneg hB] at hsq
  have h := norm_riemannZeta_four_thirds_le_four
  change B ≤ 2
  nlinarith

theorem tsum_norm_moebiusBinomialHalf_four_thirds_lt_two :
    (∑' n, ‖LSeries.term moebiusBinomialHalf (4 / 3 : ℂ) n‖) < 2 := by
  have hc := (LSeriesSummable_moebiusBinomialHalf (s := 4 / 3) (by norm_num)).norm
  have hb := (LSeriesSummable_zetaBinomialHalf (s := 4 / 3) (by norm_num)).norm
  have hle (n : ℕ) := LSeries.norm_term_le (4 / 3 : ℂ)
    (norm_moebiusBinomialHalf_le_norm_zetaBinomialHalf n)
  have hlt : ‖LSeries.term moebiusBinomialHalf (4 / 3 : ℂ) 4‖ <
      ‖LSeries.term zetaBinomialHalf (4 / 3 : ℂ) 4‖ := by
    simp only [LSeries.norm_term_eq, if_neg (by norm_num : (4 : ℕ) ≠ 0)]
    exact div_lt_div_of_pos_right norm_moebiusBinomialHalf_four_lt (by positivity)
  exact (Summable.tsum_lt_tsum hle hlt hc hb).trans_le
    tsum_norm_zetaBinomialHalf_four_thirds_le_two

theorem tsum_norm_squareCorrection_two_thirds_lt_two :
    (∑' n, ‖LSeries.term squareDilatedMoebiusBinomialHalf (2 / 3 : ℂ) n‖) < 2 := by
  have hsupport : Function.support
      (fun n => ‖LSeries.term (mPart 2 moebiusBinomialHalf) (2 / 3 : ℂ) n‖) ⊆
      Set.range (fun k : ℕ => k ^ 2) := by
    apply Function.support_subset_iff'.mpr
    intro n hn
    by_cases hn0 : n = 0
    · subst n; simp
    rw [LSeries.term_of_ne_zero hn0,
      mPart_apply_of_forall_pow_ne 2 moebiusBinomialHalf (fun k hk => hn ⟨k, hk⟩),
      zero_div, norm_zero]
  rw [squareDilatedMoebiusBinomialHalf,
    ← (Nat.pow_left_injective two_ne_zero).tsum_eq hsupport]
  simp_rw [term_mPart_pow two_ne_zero]
  norm_num only [Nat.cast_ofNat, show (2 : ℂ) * (2 / 3) = 4 / 3 by ring]
  exact tsum_norm_moebiusBinomialHalf_four_thirds_lt_two

/-- The complete correction beyond its unit coefficient cannot cancel a full positive mass. -/
theorem squareCorrection_two_thirds_tail_mass_lt_one :
    (∑' n : ℕ, if n = 1 then 0 else
      ‖LSeries.term squareDilatedMoebiusBinomialHalf (2 / 3 : ℂ) n‖) < 1 := by
  have hs := (LSeriesSummable_squareDilatedMoebiusBinomialHalf
    (s := 2 / 3) (by norm_num)).norm
  have heq := hs.tsum_eq_add_tsum_ite 1
  simp only [LSeries.term_of_ne_zero one_ne_zero, Nat.cast_one, Complex.one_cpow,
    div_one, squareDilatedMoebiusBinomialHalf_apply_one, norm_one] at heq
  have hlt := tsum_norm_squareCorrection_two_thirds_lt_two
  linarith

end RHTower

