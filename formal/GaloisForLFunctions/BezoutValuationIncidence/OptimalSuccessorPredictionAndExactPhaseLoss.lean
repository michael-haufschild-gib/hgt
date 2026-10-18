import GaloisForLFunctions.BezoutValuationIncidence.CoprimalitySuccessorPredictorAndSquarefreeInformation
import GaloisForLFunctions.BezoutValuationIncidence.GcdOrbitProjectionAndExactTranslationPeriods
import GaloisForLFunctions.BiScaleUncertainty.TwoLagMomentCone

/-!
# Optimal prediction of the actual successor signal

On the internal factorial cycle, the explicit coprimality predictor minimizes
the squared error of predicting `S_c(k+1)` by a divisor response at `k`.
The residual is orthogonal to every such response. The exact Pythagorean error
identity gives uniqueness on all active coefficients and its arithmetic loss.
-/

open Finset ArithmeticFunction GaloisForLFunctions.BiScaleUncertainty RHTower RHTower.Sieve
open GaloisForLFunctions.BiScaleUncertainty.TwoLagSieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section

private def predictionPair (N h : ℕ) (c b : ℕ → ℝ) : ℝ :=
  (∑ k ∈ Ioc 0 N.factorial, sieveSeq N c k * sieveSeq N b (k + h)) / (N.factorial : ℝ)

private theorem predictionPair_kernel (N h : ℕ) (c b : ℕ → ℝ) :
    predictionPair N h c b =
      ∑ a ∈ Icc 1 N, ∑ d ∈ Icc 1 N,
        c a * b d * (if Nat.gcd a d ∣ h then (Nat.gcd a d : ℝ) / ((a : ℝ) * d) else 0) := by
  classical
  have hrow (a d : ℕ) :
      (∑ k ∈ Ioc 0 N.factorial, (if a ∣ k then c a else 0) *
        (if d ∣ k + h then b d else 0)) =
      c a * b d * (((Ioc 0 N.factorial).filter (fun k => a ∣ k ∧ d ∣ k + h)).card : ℝ) := by
    calc
      _ = ∑ k ∈ Ioc 0 N.factorial, c a * b d *
          (if a ∣ k ∧ d ∣ k + h then (1 : ℝ) else 0) := by
        apply sum_congr rfl
        intro k _
        by_cases ha : a ∣ k <;> by_cases hd : d ∣ k + h <;> simp [ha, hd]
      _ = _ := by rw [← mul_sum, sum_boole]
  unfold predictionPair
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

private theorem predictionPair_symm (N h : ℕ) (c b : ℕ → ℝ) :
    predictionPair N h c b = predictionPair N h b c := by
  rw [predictionPair_kernel, predictionPair_kernel, sum_comm]
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro d _
  rw [Nat.gcd_comm d a]
  simp only [mul_comm]

private theorem prediction_seq_add (N k : ℕ) (c b : ℕ → ℝ) :
    sieveSeq N (fun d => c d + b d) k = sieveSeq N c k + sieveSeq N b k := by
  simp only [sieveSeq, sum_add_distrib]

private theorem prediction_coord_add (N q : ℕ) (c b : ℕ → ℝ) :
    selbergMultiplesCoord N (fun d => c d + b d) q =
      selbergMultiplesCoord N c q + selbergMultiplesCoord N b q := by
  simp only [selbergMultiplesCoord, add_div, sum_add_distrib]

private theorem predictionPair_polarize (N h : ℕ) (c b : ℕ → ℝ) :
    predictionPair N h (fun d => c d + b d) (fun d => c d + b d) =
      predictionPair N h c c + 2 * predictionPair N h c b + predictionPair N h b b := by
  have he : predictionPair N h (fun d => c d + b d) (fun d => c d + b d) =
      predictionPair N h c c + predictionPair N h c b +
        predictionPair N h b c + predictionPair N h b b := by
    simp only [predictionPair, prediction_seq_add, add_mul, mul_add,
      sum_add_distrib, add_div]
    ring
  rw [he, predictionPair_symm N h b c]
  ring

private theorem predictionPair_self (N h : ℕ) (c : ℕ → ℝ) :
    predictionPair N h c c = periodCovariance N c h + (finiteHarmonicSum N c)^2 := by
  have hs0 := sum_sieveSeq_complete_period N 0 c
  simp only [Nat.add_zero] at hs0
  have hs1 := sum_sieveSeq_complete_period N h c
  have hP : (N.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero N
  unfold periodCovariance predictionPair
  simp only [sub_mul, mul_sub, sum_sub_distrib, ← sum_mul, ← mul_sum,
    sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul]
  rw [hs0, hs1]
  field_simp
  ring

private theorem predictionPair_self_zero (N : ℕ) (c : ℕ → ℝ) :
    predictionPair N 0 c c = selbergTotientDiagonalForm N c := by
  rw [predictionPair_self, periodCovariance_zero, selberg_eq_harmonic_sq_add_variance]
  ring

private theorem predictionPair_self_one (N : ℕ) (c : ℕ → ℝ) :
    predictionPair N 1 c c = bezoutCoprimeQuadraticForm N c := by
  rw [predictionPair_self, periodCovariance_one]
  ring

private theorem prediction_diagonal_polarize (N : ℕ) (w c b : ℕ → ℝ) :
    (∑ q ∈ Icc 1 N, w q * (selbergMultiplesCoord N (fun d => c d + b d) q)^2) =
      (∑ q ∈ Icc 1 N, w q * (selbergMultiplesCoord N c q)^2) +
      2 * (∑ q ∈ Icc 1 N, w q * selbergMultiplesCoord N c q * selbergMultiplesCoord N b q) +
      (∑ q ∈ Icc 1 N, w q * (selbergMultiplesCoord N b q)^2) := by
  rw [mul_sum, ← sum_add_distrib, ← sum_add_distrib]
  apply sum_congr rfl
  intro q _
  rw [prediction_coord_add]
  ring

/-- Complete-period same-node bilinear pairing in the common Selberg coordinates. -/
theorem mean_sieveSeq_mul_eq_totient_pairing (N : ℕ) (c b : ℕ → ℝ) :
    (∑ k ∈ Ioc 0 N.factorial, sieveSeq N c k * sieveSeq N b k) / (N.factorial : ℝ) =
      ∑ q ∈ Icc 1 N, (q.totient : ℝ) * selbergMultiplesCoord N c q * selbergMultiplesCoord N b q := by
  have hp := predictionPair_polarize N 0 c b
  rw [predictionPair_self_zero, predictionPair_self_zero, predictionPair_self_zero] at hp
  unfold selbergTotientDiagonalForm at hp
  rw [prediction_diagonal_polarize] at hp
  have he : predictionPair N 0 c b =
      (∑ k ∈ Ioc 0 N.factorial, sieveSeq N c k * sieveSeq N b k) / (N.factorial : ℝ) := by
    simp only [predictionPair, Nat.add_zero]
  rw [he] at hp
  linarith

/-- Actual successor pairing: Möbius weights arise from integer CRT compatibility. -/
theorem mean_sieveSeq_mul_succ_eq_moebius_pairing (N : ℕ) (c b : ℕ → ℝ) :
    (∑ k ∈ Ioc 0 N.factorial, sieveSeq N c k * sieveSeq N b (k + 1)) / (N.factorial : ℝ) =
      ∑ q ∈ Icc 1 N, moebiusReal q * selbergMultiplesCoord N c q * selbergMultiplesCoord N b q := by
  have hp := predictionPair_polarize N 1 c b
  rw [predictionPair_self_one, predictionPair_self_one, predictionPair_self_one,
    bezoutCoprimeQuadraticForm_eq_moebius_diagonal,
    bezoutCoprimeQuadraticForm_eq_moebius_diagonal,
    bezoutCoprimeQuadraticForm_eq_moebius_diagonal, prediction_diagonal_polarize] at hp
  change predictionPair N 1 c b = _
  linarith

private theorem prediction_period (N : ℕ) (c : ℕ → ℝ) :
    Function.Periodic (sieveSeq N c) N.factorial :=
  (sieveSeq_periodic_iff_active_divisors N N.factorial c).mpr
    (fun _d hd _ => Nat.dvd_factorial (mem_Icc.mp hd).1 (mem_Icc.mp hd).2)

private theorem prediction_shift_norm (N : ℕ) (c : ℕ → ℝ) :
    (∑ k ∈ Ioc 0 N.factorial, (sieveSeq N c (k + 1))^2) / (N.factorial : ℝ) =
      selbergTotientDiagonalForm N c := by
  have ht := sum_Icc_one_succ_sub (Nat.factorial_pos N) (fun k => (sieveSeq N c k)^2)
  have hs : Icc 1 N.factorial = Ioc 0 N.factorial := by ext k; simp only [mem_Icc, mem_Ioc]; omega
  rw [hs, sum_sub_distrib] at ht
  have hb := prediction_period N c 1
  rw [Nat.add_comm 1] at hb
  rw [hb, sub_self] at ht
  rw [sub_eq_zero.mp ht]
  simpa only [pow_two, selbergTotientDiagonalForm, mul_assoc] using
    mean_sieveSeq_mul_eq_totient_pairing N c c

/-- Literal one-step squared prediction error on the internal factorial cycle. -/
def successorPredictionError (N : ℕ) (c b : ℕ → ℝ) : ℝ :=
  (∑ k ∈ Ioc 0 N.factorial, (sieveSeq N c (k + 1) - sieveSeq N b k)^2) / (N.factorial : ℝ)

/-- The irreducible arithmetic phase loss; its constant and parity terms vanish. -/
def successorPhaseLoss (N : ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ q ∈ Icc 1 N, ((q.totient : ℝ) - (moebiusReal q)^2 / (q.totient : ℝ)) *
    (selbergMultiplesCoord N c q)^2

private theorem prediction_error_expand (N : ℕ) (c b : ℕ → ℝ) :
    successorPredictionError N c b = selbergTotientDiagonalForm N c +
      selbergTotientDiagonalForm N b -
      2 * ∑ q ∈ Icc 1 N, moebiusReal q * selbergMultiplesCoord N b q * selbergMultiplesCoord N c q := by
  have he : successorPredictionError N c b =
      (∑ k ∈ Ioc 0 N.factorial, (sieveSeq N c (k + 1))^2) / (N.factorial : ℝ) +
      (∑ k ∈ Ioc 0 N.factorial, sieveSeq N b k * sieveSeq N b k) / (N.factorial : ℝ) -
      2 * ((∑ k ∈ Ioc 0 N.factorial, sieveSeq N b k * sieveSeq N c (k + 1)) / (N.factorial : ℝ)) := by
    unfold successorPredictionError
    rw [← mul_div_assoc, ← add_div, ← sub_div]
    congr 1
    rw [mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
    apply sum_congr rfl
    intro k _
    ring
  rw [he, prediction_shift_norm, mean_sieveSeq_mul_eq_totient_pairing,
    mean_sieveSeq_mul_succ_eq_moebius_pairing]
  simp only [selbergTotientDiagonalForm, pow_two, mul_assoc]

/-- Exact physical error decomposition around the arithmetic coprimality predictor. -/
theorem successorPredictionError_pythagoras (N : ℕ) (c b : ℕ → ℝ) :
    successorPredictionError N c b = successorPhaseLoss N c +
      selbergTotientDiagonalForm N (fun d => b d - sieveSuccessorPredictor N c d) := by
  rw [prediction_error_expand]
  unfold successorPhaseLoss selbergTotientDiagonalForm
  rw [mul_sum, ← sum_add_distrib, ← sum_sub_distrib, ← sum_add_distrib]
  apply sum_congr rfl
  intro q hq
  rw [selbergMultiplesCoord_sub, selbergMultiplesCoord_successorPredictor]
  have hφ : (q.totient : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr (mem_Icc.mp hq).1).ne'
  field_simp
  ring

/-- Minimum error equals the explicit arithmetic phase loss at every level. -/
theorem successorPredictionError_optimal_value (N : ℕ) (c : ℕ → ℝ) :
    successorPredictionError N c (sieveSuccessorPredictor N c) = successorPhaseLoss N c := by
  rw [successorPredictionError_pythagoras]
  simp [selbergTotientDiagonalForm, selbergMultiplesCoord]

/-- The explicit predictor minimizes the literal successor error for arbitrary real weights. -/
theorem successorPredictionError_minimal (N : ℕ) (c b : ℕ → ℝ) :
    successorPredictionError N c (sieveSuccessorPredictor N c) ≤ successorPredictionError N c b := by
  rw [successorPredictionError_optimal_value, successorPredictionError_pythagoras]
  exact le_add_of_nonneg_right (selbergTotientDiagonalForm_nonneg N _)

/-- Every minimizer has exactly the same active raw coefficients as the coprimality predictor. -/
theorem successorPredictionError_eq_minimum_iff (N : ℕ) (c b : ℕ → ℝ) :
    successorPredictionError N c b = successorPhaseLoss N c ↔
      ∀ d ∈ Icc 1 N, b d = sieveSuccessorPredictor N c d := by
  rw [successorPredictionError_pythagoras, add_eq_left]
  have hz : selbergTotientDiagonalForm N (fun d => b d - sieveSuccessorPredictor N c d) = 0 ↔
      ∀ q ∈ Icc 1 N, selbergMultiplesCoord N (fun d => b d - sieveSuccessorPredictor N c d) q = 0 := by
    unfold selbergTotientDiagonalForm
    rw [sum_eq_zero_iff_of_nonneg (fun q _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))]
    constructor
    · intro h q hq
      have hφ : (q.totient : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr (mem_Icc.mp hq).1).ne'
      exact sq_eq_zero_iff.mp ((mul_eq_zero.mp (h q hq)).resolve_left hφ)
    · intro h q hq
      rw [h q hq]
      ring
  rw [hz, selbergMultiplesCoord_tail_zero_iff N 0]
  simp only [zero_add, sub_eq_zero]

/-- Zero error on the internal cycle is equivalent to exact prediction at every natural input. -/
theorem successorPredictionError_eq_zero_iff (N : ℕ) (c b : ℕ → ℝ) :
    successorPredictionError N c b = 0 ↔
      ∀ k, sieveSeq N c (k + 1) = sieveSeq N b k := by
  constructor
  · intro h
    have hP : (N.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero N
    have hz := (div_eq_zero_iff.mp h).resolve_right hP
    have hs := (sum_eq_zero_iff_of_nonneg
      (fun k (_ : k ∈ Ioc 0 N.factorial) => sq_nonneg (sieveSeq N c (k + 1) - sieveSeq N b k))).mp hz
    let f := fun k => sieveSeq N c (k + 1) - sieveSeq N b k
    have hf : Function.Periodic f N.factorial := by
      intro k
      dsimp only [f]
      rw [show k + N.factorial + 1 = (k + 1) + N.factorial by omega,
        prediction_period N c (k + 1), prediction_period N b k]
    have hf0 : f 0 = 0 := by
      have hper := hf 0
      simp only [Nat.zero_add] at hper
      rw [← hper]
      exact sq_eq_zero_iff.mp (hs N.factorial (mem_Ioc.mpr ⟨Nat.factorial_pos N, le_rfl⟩))
    intro k
    have hm : f (k % N.factorial) = 0 := by
      by_cases hk : k % N.factorial = 0
      · rw [hk, hf0]
      · exact sq_eq_zero_iff.mp (hs (k % N.factorial)
          (mem_Ioc.mpr ⟨Nat.pos_of_ne_zero hk, (Nat.mod_lt k (Nat.factorial_pos N)).le⟩))
    rw [hf.map_mod_nat] at hm
    exact sub_eq_zero.mp hm
  · intro h
    unfold successorPredictionError
    simp only [h, sub_self, zero_pow (by omega : 2 ≠ 0), sum_const_zero, zero_div]

end
end GaloisForLFunctions.BezoutValuationIncidence
