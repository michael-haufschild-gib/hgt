import GaloisForLFunctions.BezoutValuationIncidence.ValuationVisibilityClockAndRamanujanSupport
import GaloisForLFunctions.BezoutValuationIncidence.OptimalSuccessorPredictionAndExactPhaseLoss

/-!
# Exact compression of true integer translation

The literal complete-period pairing at every lag has Ramanujan coefficients.
The resulting coordinate multiplier is the optimal divisor-sieve predictor
of the true shifted signal. Its orthogonal error identity uses the actual
integer cycle; no iterate of one-step compression is substituted for a shift.
-/

open Finset ArithmeticFunction GaloisForLFunctions.BiScaleUncertainty RHTower RHTower.Sieve
open GaloisForLFunctions.BiScaleUncertainty.TwoLagSieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section

/-- Actual bilinear observation of an integer shift on the internal factorial cycle. -/
def sieveLagPair (N h : ℕ) (b c : ℕ → ℝ) : ℝ :=
  (∑ k ∈ Ioc 0 N.factorial, sieveSeq N b k * sieveSeq N c (k + h)) / (N.factorial : ℝ)

private theorem lag_pair_kernel (N h : ℕ) (b c : ℕ → ℝ) :
    sieveLagPair N h b c =
      ∑ a ∈ Icc 1 N, ∑ d ∈ Icc 1 N,
        b a * c d * (if Nat.gcd a d ∣ h then (Nat.gcd a d : ℝ) / ((a : ℝ) * d) else 0) := by
  classical
  have hrow (a d : ℕ) :
      (∑ k ∈ Ioc 0 N.factorial, (if a ∣ k then b a else 0) *
        (if d ∣ k + h then c d else 0)) =
      b a * c d * (((Ioc 0 N.factorial).filter (fun k => a ∣ k ∧ d ∣ k + h)).card : ℝ) := by
    calc
      _ = ∑ k ∈ Ioc 0 N.factorial, b a * c d *
          (if a ∣ k ∧ d ∣ k + h then (1 : ℝ) else 0) := by
        apply sum_congr rfl
        intro k _
        by_cases ha : a ∣ k <;> by_cases hd : d ∣ k + h <;> simp [ha, hd]
      _ = _ := by rw [← mul_sum, sum_boole]
  unfold sieveLagPair
  simp only [sieveSeq, sum_filter, sum_mul_sum]
  rw [sum_comm]
  simp_rw [sum_comm (s := Ioc 0 N.factorial), hrow]
  rw [sum_div]
  apply sum_congr rfl
  intro a ha
  rw [sum_div]
  apply sum_congr rfl
  intro d hd
  rw [mul_div_assoc]
  congr 1
  exact joint_density_complete_period (mem_Icc.mp ha).1 (mem_Icc.mp hd).1
    (Nat.lcm_dvd (Nat.dvd_factorial (mem_Icc.mp ha).1 (mem_Icc.mp ha).2)
      (Nat.dvd_factorial (mem_Icc.mp hd).1 (mem_Icc.mp hd).2)) (Nat.factorial_pos N)

/-- Exact Ramanujan diagonal of literal integer translation, at every natural level and lag. -/
theorem sieveLagPair_eq_ramanujan_diagonal (N h : ℕ) (b c : ℕ → ℝ) :
    sieveLagPair N h b c =
      ∑ q ∈ Icc 1 N, ramanujanLagCoefficient q h *
        selbergMultiplesCoord N b q * selbergMultiplesCoord N c q := by
  classical
  have hcommon (a d : ℕ) (ha : a ∈ Icc 1 N) :
      (Icc 1 N).filter (fun q => q ∣ a ∧ q ∣ d) = (Nat.gcd a d).divisors := by
    ext q
    have ha0 : a ≠ 0 := by have := (mem_Icc.mp ha).1; omega
    simp only [mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
    constructor
    · exact fun h => ⟨h.2, Nat.gcd_ne_zero_left ha0⟩
    · rintro ⟨h, _⟩
      exact ⟨mem_Icc.mpr ⟨Nat.pos_of_dvd_of_pos h.1 (mem_Icc.mp ha).1,
        (Nat.le_of_dvd (mem_Icc.mp ha).1 h.1).trans (mem_Icc.mp ha).2⟩, h⟩
  rw [lag_pair_kernel]
  calc
    _ = ∑ a ∈ Icc 1 N, ∑ d ∈ Icc 1 N, ∑ q ∈ Icc 1 N,
        if q ∣ a ∧ q ∣ d then
          ramanujanLagCoefficient q h * (b a / (a : ℝ)) * (c d / (d : ℝ)) else 0 := by
      apply sum_congr rfl
      intro a ha
      apply sum_congr rfl
      intro d _
      rw [← sum_filter, hcommon a d ha]
      calc
        _ = (b a / (a : ℝ)) * (c d / (d : ℝ)) *
            ∑ q ∈ (Nat.gcd a d).divisors, ramanujanLagCoefficient q h := by
          rw [sum_divisors_ramanujanLagCoefficient]
          split_ifs <;> simp only [div_eq_mul_inv, mul_inv_rev] <;> ring
        _ = _ := by
          rw [mul_sum]
          apply sum_congr rfl
          intro q _
          ring
    _ = ∑ q ∈ Icc 1 N, ∑ a ∈ Icc 1 N, ∑ d ∈ Icc 1 N,
        if q ∣ a ∧ q ∣ d then
          ramanujanLagCoefficient q h * (b a / (a : ℝ)) * (c d / (d : ℝ)) else 0 := by
      conv_lhs => enter [2, a]; rw [sum_comm]
      rw [sum_comm]
    _ = _ := by
      apply sum_congr rfl
      intro q _
      simp only [selbergMultiplesCoord, sum_filter, mul_sum, sum_mul]
      conv_rhs => rw [sum_comm]
      apply sum_congr rfl
      intro a _
      apply sum_congr rfl
      intro d _
      by_cases ha : q ∣ a <;> by_cases hd : q ∣ d <;> simp [ha, hd]

/-- True-lag predictor, obtained from the existing exact finite multiples inverse. -/
def sieveTranslationPredictor (N h : ℕ) (c : ℕ → ℝ) : ℕ → ℝ :=
  pmRamanujanResidueCoeff (fun q => sieveLagMultiplier q h * selbergMultiplesCoord N c q) N

/-- Exact coordinate action, with the inactive coordinates explicitly zero. -/
theorem selbergMultiplesCoord_translationPredictor (N h q : ℕ) (c : ℕ → ℝ) :
    selbergMultiplesCoord N (sieveTranslationPredictor N h c) q =
      if q ∈ Icc 1 N then sieveLagMultiplier q h * selbergMultiplesCoord N c q else 0 :=
  selbergMultiplesCoord_ramanujan_inverse N _ q

/-- Equality of the active raw coefficients is equivalent to equality of their coordinates. -/
theorem sieve_active_coefficients_eq_iff (N : ℕ) (c b : ℕ → ℝ) :
    (∀ d ∈ Icc 1 N, c d = b d) ↔
      ∀ q ∈ Icc 1 N, selbergMultiplesCoord N c q = selbergMultiplesCoord N b q := by
  simpa only [zero_add, selbergMultiplesCoord_sub, sub_eq_zero] using
    (selbergMultiplesCoord_tail_zero_iff N 0 (fun d => c d - b d)).symm

/-- Lag one is exactly the existing coprimality predictor on every active coefficient. -/
theorem sieveTranslationPredictor_one (N : ℕ) (c : ℕ → ℝ) :
    ∀ d ∈ Icc 1 N, sieveTranslationPredictor N 1 c d = sieveSuccessorPredictor N c d := by
  apply (sieve_active_coefficients_eq_iff N _ _).mpr
  intro q hq
  rw [selbergMultiplesCoord_translationPredictor, if_pos hq,
    selbergMultiplesCoord_successorPredictor, sieveLagMultiplier_eq_moebius_totient_quotient]
  simp

/-- Every literal shifted pairing equals pairing with the compressed predictor at the same node. -/
theorem sieveLagPair_eq_pair_translationPredictor (N h : ℕ) (b c : ℕ → ℝ) :
    sieveLagPair N h b c = sieveLagPair N 0 b (sieveTranslationPredictor N h c) := by
  rw [sieveLagPair_eq_ramanujan_diagonal]
  have hz := mean_sieveSeq_mul_eq_totient_pairing N b (sieveTranslationPredictor N h c)
  change _ = (∑ k ∈ Ioc 0 N.factorial,
    sieveSeq N b k * sieveSeq N (sieveTranslationPredictor N h c) (k + 0)) / _
  simp only [Nat.add_zero]
  rw [hz]
  apply sum_congr rfl
  intro q hq
  rw [selbergMultiplesCoord_translationPredictor, if_pos hq, ramanujanLagCoefficient_eq_totient_mul]
  ring

/-- Literal squared error of predicting a true shift by a divisor response at the present input. -/
def translationPredictionError (N h : ℕ) (c b : ℕ → ℝ) : ℝ :=
  (∑ k ∈ Ioc 0 N.factorial, (sieveSeq N c (k + h) - sieveSeq N b k)^2) / (N.factorial : ℝ)

private theorem translation_error_expand (N h : ℕ) (c b : ℕ → ℝ) :
    translationPredictionError N h c b =
      (∑ k ∈ Ioc 0 N.factorial, (sieveSeq N c (k + h))^2) / (N.factorial : ℝ) +
      selbergTotientDiagonalForm N b -
      2 * ∑ q ∈ Icc 1 N, ramanujanLagCoefficient q h *
        selbergMultiplesCoord N b q * selbergMultiplesCoord N c q := by
  have he : translationPredictionError N h c b =
      (∑ k ∈ Ioc 0 N.factorial, (sieveSeq N c (k + h))^2) / (N.factorial : ℝ) +
      (∑ k ∈ Ioc 0 N.factorial, sieveSeq N b k * sieveSeq N b k) / (N.factorial : ℝ) -
      2 * sieveLagPair N h b c := by
    unfold translationPredictionError sieveLagPair
    rw [← mul_div_assoc, ← add_div, ← sub_div]
    congr 1
    rw [mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
    apply sum_congr rfl
    intro k _
    ring
  rw [he, mean_sieveSeq_mul_eq_totient_pairing, sieveLagPair_eq_ramanujan_diagonal]
  simp only [selbergTotientDiagonalForm, pow_two, mul_assoc]

/-- Exact orthogonal error decomposition for every true shift, including lag zero. -/
theorem translationPredictionError_pythagoras (N h : ℕ) (c b : ℕ → ℝ) :
    translationPredictionError N h c b =
      translationPredictionError N h c (sieveTranslationPredictor N h c) +
      selbergTotientDiagonalForm N (fun d => b d - sieveTranslationPredictor N h c d) := by
  rw [translation_error_expand, translation_error_expand]
  have hd : selbergTotientDiagonalForm N b -
      2 * (∑ q ∈ Icc 1 N, ramanujanLagCoefficient q h *
        selbergMultiplesCoord N b q * selbergMultiplesCoord N c q) =
      selbergTotientDiagonalForm N (sieveTranslationPredictor N h c) -
      2 * (∑ q ∈ Icc 1 N, ramanujanLagCoefficient q h *
        selbergMultiplesCoord N (sieveTranslationPredictor N h c) q * selbergMultiplesCoord N c q) +
      selbergTotientDiagonalForm N (fun d => b d - sieveTranslationPredictor N h c d) := by
    simp only [selbergTotientDiagonalForm, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro q hq
    rw [selbergMultiplesCoord_sub, selbergMultiplesCoord_translationPredictor, if_pos hq,
      ramanujanLagCoefficient_eq_totient_mul]
    ring
  linarith

/-- The arithmetic predictor minimizes actual squared error at every lag. -/
theorem translationPredictionError_minimal (N h : ℕ) (c b : ℕ → ℝ) :
    translationPredictionError N h c (sieveTranslationPredictor N h c) ≤
      translationPredictionError N h c b := by
  rw [translationPredictionError_pythagoras N h c b]
  exact le_add_of_nonneg_right (selbergTotientDiagonalForm_nonneg N _)

/-- Every minimizer has exactly the predictor's active coefficients. -/
theorem translationPredictionError_eq_minimum_iff (N h : ℕ) (c b : ℕ → ℝ) :
    translationPredictionError N h c b =
      translationPredictionError N h c (sieveTranslationPredictor N h c) ↔
      ∀ d ∈ Icc 1 N, b d = sieveTranslationPredictor N h c d := by
  rw [translationPredictionError_pythagoras N h c b, add_eq_left]
  have hz : selbergTotientDiagonalForm N (fun d => b d - sieveTranslationPredictor N h c d) = 0 ↔
      ∀ q ∈ Icc 1 N, selbergMultiplesCoord N (fun d => b d - sieveTranslationPredictor N h c d) q = 0 := by
    unfold selbergTotientDiagonalForm
    rw [sum_eq_zero_iff_of_nonneg (fun q _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))]
    constructor
    · intro hz q hq
      have hφ : (q.totient : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.totient_pos.mpr (mem_Icc.mp hq).1).ne'
      exact sq_eq_zero_iff.mp ((mul_eq_zero.mp (hz q hq)).resolve_left hφ)
    · intro hz q hq
      rw [hz q hq]
      ring
  rw [hz, selbergMultiplesCoord_tail_zero_iff N 0]
  simp only [zero_add, sub_eq_zero]

end
end GaloisForLFunctions.BezoutValuationIncidence
