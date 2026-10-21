import GaloisForLFunctions.BezoutValuationIncidence.DampedChebyshevTangentFormOfTheReceiver
import GaloisForLFunctions.RHTower.PMPowerDampedMobiusLogConvolution

/-!
# Damping work as arithmetic Markov boundary flux

The literal damped divisor prefix, divided by its cutoff, evolves under a
damping-independent finite downward-jump generator. Its rates are von Mangoldt
divisor rates and logarithmic adjacent-prefix rates. Centering leaves the exact
density derivative as a constant forcing. The pronic energy identity retains
the signed counting-measure flux, the nonnegative jump energy, and this forcing.
Flux and jump energy must remain paired: even finite-support inputs can make
both grow linearly with the cutoff while cancelling exactly. No cutoff-uniform
estimate for their combined work is asserted.
-/

open Finset ArithmeticFunction RHTower

namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
set_option autoImplicit false

private def awCoeff (η : ℝ) : ArithmeticFunction ℝ where
  toFun n := (moebius n : ℝ) * (n : ℝ) ^ (-η)
  map_zero' := by simp

private theorem awCoeff_zeta (η : ℝ) (n : ℕ) :
    (awCoeff η * ((zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ)) n =
      pmPowerDampedDivisorCoeff η n := by
  rw [coe_mul_zeta_apply]
  rfl

private theorem awCoeff_tangent (η : ℝ) (n : ℕ) :
    (-(awCoeff η).pmul ArithmeticFunction.log *
      ((zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ)) n =
      dampedVonMangoldt η n := by
  rw [coe_mul_zeta_apply]
  unfold dampedVonMangoldt
  rw [← sum_neg_distrib]
  apply sum_congr rfl
  intro d _
  simp only [ArithmeticFunction.neg_apply, pmul_apply, log_apply]
  change -((moebius d : ℝ) * (d : ℝ) ^ (-η) * Real.log d) =
    -((moebius d : ℝ) * Real.log d * (d : ℝ) ^ (-η))
  ring

/-- Differentiation and multiplication by `log n` combine into the undamped
Mangoldt convolution. This identity holds for the actual Möbius source. -/
theorem dampedVonMangoldt_add_divisorCoeff_log (η : ℝ) (n : ℕ) :
    dampedVonMangoldt η n + pmPowerDampedDivisorCoeff η n * Real.log n =
      ∑ d ∈ n.divisors, vonMangoldt d * pmPowerDampedDivisorCoeff η (n / d) := by
  have h : -(awCoeff η).pmul ArithmeticFunction.log *
      ((zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ) +
      (awCoeff η * ((zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ)).pmul
        ArithmeticFunction.log =
      vonMangoldt * (awCoeff η * ((zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ)) := by
    rw [pmul_log_mul, zeta_pmul_log, ← vonMangoldt_mul_zeta]
    ring
  have he := congrArg (fun f : ArithmeticFunction ℝ => f n) h
  change (-(awCoeff η).pmul ArithmeticFunction.log *
      ((zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ)) n +
      (awCoeff η * ((zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ)) n * Real.log n =
      (vonMangoldt * (awCoeff η *
        ((zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ))) n at he
  rw [awCoeff_tangent, awCoeff_zeta, ArithmeticFunction.mul_apply] at he
  simp_rw [awCoeff_zeta] at he
  rw [Nat.sum_divisorsAntidiagonal
    (f := fun a b => vonMangoldt a * pmPowerDampedDivisorCoeff η b)] at he
  exact he

private def awPrefix (f : ℕ → ℝ) (n : ℕ) : ℝ := ∑ k ∈ Icc 1 n, f k

private theorem awAbel (f : ℕ → ℝ) (n : ℕ) :
    (∑ k ∈ Icc 1 n, f k * Real.log k) =
      awPrefix f n * Real.log n -
        ∑ k ∈ range n, awPrefix f k * (Real.log (k + 1) - Real.log k) := by
  induction n with
  | zero => simp [awPrefix]
  | succ n ih =>
    have hs : awPrefix f (n + 1) = awPrefix f n + f (n + 1) :=
      sum_Icc_succ_top (by omega) _
    rw [sum_Icc_succ_top (by omega), Finset.sum_range_succ, hs, ih]
    push_cast
    ring

/-- The raw finite divisor prefix. -/
def arithmeticDampingPrefix (η : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Icc 1 n, pmPowerDampedDivisorCoeff η k

/-- The exact finite prefix evolution before normalization or centering. -/
theorem arithmeticDampingPrefix_tangent (η : ℝ) (n : ℕ) :
    (∑ k ∈ Icc 1 n, dampedVonMangoldt η k) =
      (∑ d ∈ Icc 1 n, vonMangoldt d * arithmeticDampingPrefix η (n / d)) +
      (∑ k ∈ range n, arithmeticDampingPrefix η k *
        (Real.log (k + 1) - Real.log k)) -
      Real.log n * arithmeticDampingPrefix η n := by
  have h := sum_congr (s₁ := Icc 1 n) rfl
    (fun k _ => dampedVonMangoldt_add_divisorCoeff_log η k)
  rw [sum_add_distrib, awAbel, Sieve.sum_divisors_swap n
    (fun d k => vonMangoldt d * pmPowerDampedDivisorCoeff η k)] at h
  simp only [← mul_sum] at h
  change (∑ k ∈ Icc 1 n, dampedVonMangoldt η k) +
    (arithmeticDampingPrefix η n * Real.log n -
      ∑ k ∈ range n, arithmeticDampingPrefix η k *
        (Real.log (k + 1) - Real.log k)) =
    ∑ d ∈ Icc 1 n, vonMangoldt d * arithmeticDampingPrefix η (n / d) at h
  linarith

/-- The row-sum identity for the arithmetic jump rates. It is finite and exact. -/
theorem arithmeticDamping_row_sum (n : ℕ) :
    (∑ d ∈ Icc 1 n, vonMangoldt d * (n / d : ℕ)) +
      (∑ k ∈ range n, (k : ℝ) * (Real.log (k + 1) - Real.log k)) =
      (n : ℝ) * Real.log n := by
  have h := sum_congr (s₁ := Icc 1 n) rfl
    (fun k _ => (vonMangoldt_sum (n := k)))
  rw [Sieve.sum_divisors_swap n (fun d _ => vonMangoldt d)] at h
  simp only [sum_const, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel] at h
  have ha := awAbel (fun _ => 1) n
  have hp (k : ℕ) : awPrefix (fun _ => 1) k = (k : ℝ) := by
    simp [awPrefix]
  simp only [one_mul, hp] at ha
  have hh : (∑ d ∈ Icc 1 n, vonMangoldt d * (n / d : ℕ)) =
      ∑ k ∈ Icc 1 n, Real.log k := by
    simpa only [mul_comm] using h
  linarith

/-- A downward-jump generator on positive integer states. State zero has zero
weight; its value never contributes to any positive-state equation. -/
def arithmeticDampingGenerator (v : ℕ → ℝ) (n : ℕ) : ℝ :=
  ((∑ d ∈ Icc 1 n, vonMangoldt d * (n / d : ℕ) * (v (n / d) - v n)) +
    ∑ k ∈ range n, (k : ℝ) * (Real.log (k + 1) - Real.log k) * (v k - v n)) / n

theorem arithmeticDampingGenerator_const (c : ℝ) (n : ℕ) :
    arithmeticDampingGenerator (fun _ => c) n = 0 := by
  simp [arithmeticDampingGenerator]

theorem arithmeticDampingGenerator_sub_const (v : ℕ → ℝ) (c : ℝ) (n : ℕ) :
    arithmeticDampingGenerator (fun k => v k - c) n =
      arithmeticDampingGenerator v n := by
  unfold arithmeticDampingGenerator
  congr 1
  congr 1
  · exact sum_congr rfl fun k _ => by ring
  · exact sum_congr rfl fun k _ => by ring

theorem arithmeticDampingGenerator_one (v : ℕ → ℝ) :
    arithmeticDampingGenerator v 1 = 0 := by
  simp [arithmeticDampingGenerator]

/-- Explicit diagonal form: total departure rate is `log n`. -/
theorem arithmeticDampingGenerator_eq (v : ℕ → ℝ) {n : ℕ} (hn : 0 < n) :
    arithmeticDampingGenerator v n =
      ((∑ d ∈ Icc 1 n, vonMangoldt d * (n / d : ℕ) * v (n / d)) +
        ∑ k ∈ range n, (k : ℝ) * (Real.log (k + 1) - Real.log k) * v k) / n -
      Real.log n * v n := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold arithmeticDampingGenerator
  simp_rw [mul_sub]
  rw [sum_sub_distrib, sum_sub_distrib, ← sum_mul, ← sum_mul]
  have h := arithmeticDamping_row_sum n
  field_simp
  nlinarith [congrArg (fun x : ℝ => x * v n) h]

/-- The normalized raw divisor prefix, with harmless value zero at state zero. -/
def arithmeticDampingMean (η : ℝ) (n : ℕ) : ℝ := arithmeticDampingPrefix η n / n

private theorem awMean_mul (η : ℝ) (n : ℕ) :
    (n : ℝ) * arithmeticDampingMean η n = arithmeticDampingPrefix η n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [arithmeticDampingMean, arithmeticDampingPrefix]
  · unfold arithmeticDampingMean
    exact mul_div_cancel₀ _ (by exact_mod_cast hn)

/-- The literal arithmetic source follows the finite Markov generator. -/
theorem hasDerivAt_arithmeticDampingMean (η : ℝ) {n : ℕ} (hn : 0 < n) :
    HasDerivAt (fun x => arithmeticDampingMean x n)
      (arithmeticDampingGenerator (arithmeticDampingMean η) n) η := by
  have h := (HasDerivAt.fun_sum (u := Icc 1 n)
    (fun k _ => hasDerivAt_pmPowerDampedDivisorCoeff η k)).div_const (n : ℝ)
  change HasDerivAt (fun x => arithmeticDampingMean x n)
    ((∑ k ∈ Icc 1 n, dampedVonMangoldt η k) / n) η at h
  apply h.congr_deriv
  rw [arithmeticDampingGenerator_eq _ hn, arithmeticDampingPrefix_tangent]
  have hm (k : ℕ) : (k : ℝ) * (Real.log (k + 1) - Real.log k) *
      arithmeticDampingMean η k =
      arithmeticDampingPrefix η k * (Real.log (k + 1) - Real.log k) := by
    rw [mul_right_comm, awMean_mul]
  simp_rw [hm, mul_assoc, awMean_mul]
  unfold arithmeticDampingMean
  ring

/-- Centering is performed at every state before taking the work. At positive
states this is exactly `A_η(n)/n`; its state-zero value has zero jump weight. -/
def arithmeticDampingCenteredMean (η : ℝ) (n : ℕ) : ℝ :=
  arithmeticDampingMean η n - (pmPowerDampedDivisorDensity η).re

theorem arithmeticDampingCenteredMean_eq (η : ℝ) {n : ℕ} (hn : 0 < n) :
    arithmeticDampingCenteredMean η n = pmPowerDampedCenteredDivisorPrefix η n / n := by
  rw [pmPowerDampedCenteredDivisorPrefix_eq]
  unfold arithmeticDampingCenteredMean arithmeticDampingMean arithmeticDampingPrefix
  field_simp

/-- The full centering term survives in the exact finite evolution. -/
theorem hasDerivAt_arithmeticDampingCenteredMean {η : ℝ} (hη : 0 < η)
    {n : ℕ} (hn : 0 < n) :
    HasDerivAt (fun x => arithmeticDampingCenteredMean x n)
      (arithmeticDampingGenerator (arithmeticDampingCenteredMean η) n - dampedReadout η) η := by
  have h := (hasDerivAt_arithmeticDampingMean η hn).sub
    (hasDerivAt_pmPowerDampedDivisorDensity_re hη)
  change HasDerivAt (fun x => arithmeticDampingMean x n - (pmPowerDampedDivisorDensity x).re)
    (arithmeticDampingGenerator
      (fun k => arithmeticDampingMean η k - (pmPowerDampedDivisorDensity η).re) n -
      dampedReadout η) η
  rw [arithmeticDampingGenerator_sub_const]
  exact h

/-- The nonnegative square-jump term of the same arithmetic generator. -/
def arithmeticDampingJumpEnergy (v : ℕ → ℝ) (n : ℕ) : ℝ :=
  ((∑ d ∈ Icc 1 n, vonMangoldt d * (n / d : ℕ) * (v (n / d) - v n) ^ 2) +
    ∑ k ∈ range n, (k : ℝ) * (Real.log (k + 1) - Real.log k) * (v k - v n) ^ 2) / n

private theorem awLogStep_nonneg (k : ℕ) : 0 ≤ Real.log (k + 1) - Real.log k := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  · apply sub_nonneg.mpr
    exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hk) (by linarith)

theorem arithmeticDampingJumpEnergy_nonneg (v : ℕ → ℝ) (n : ℕ) :
    0 ≤ arithmeticDampingJumpEnergy v n := by
  unfold arithmeticDampingJumpEnergy
  apply div_nonneg _ (Nat.cast_nonneg n)
  apply add_nonneg
  · exact sum_nonneg fun d _ => mul_nonneg
      (mul_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _)) (sq_nonneg _)
  · exact sum_nonneg fun k _ => mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (awLogStep_nonneg _)) (sq_nonneg _)

/-- The finite Markov square identity; no stationary measure is presumed. -/
theorem arithmeticDampingGenerator_square (v : ℕ → ℝ) (n : ℕ) :
    2 * v n * arithmeticDampingGenerator v n =
      arithmeticDampingGenerator (fun k => (v k) ^ 2) n -
        arithmeticDampingJumpEnergy v n := by
  unfold arithmeticDampingGenerator arithmeticDampingJumpEnergy
  rw [← mul_div_assoc, ← sub_div]
  congr 1
  rw [mul_add, mul_sum, mul_sum]
  have h₁ : (∑ d ∈ Icc 1 n, 2 * v n *
      (vonMangoldt d * (n / d : ℕ) * (v (n / d) - v n))) =
      (∑ d ∈ Icc 1 n, vonMangoldt d * (n / d : ℕ) * ((v (n / d)) ^ 2 - (v n) ^ 2)) -
        ∑ d ∈ Icc 1 n, vonMangoldt d * (n / d : ℕ) * (v (n / d) - v n) ^ 2 := by
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun d _ => by ring
  have h₂ : (∑ k ∈ range n, 2 * v n *
      ((k : ℝ) * (Real.log (k + 1) - Real.log k) * (v k - v n))) =
      (∑ k ∈ range n, (k : ℝ) * (Real.log (k + 1) - Real.log k) * ((v k) ^ 2 - (v n) ^ 2)) -
        ∑ k ∈ range n, (k : ℝ) * (Real.log (k + 1) - Real.log k) * (v k - v n) ^ 2 := by
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun k _ => by ring
  rw [h₁, h₂]
  ring

/-- Counting-measure boundary flux with the original pronic weight. It has no
automatic sign: the arithmetic chain does not preserve this measure. -/
def arithmeticDampingBoundaryFlux (v : ℕ → ℝ) (T : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 T, ((n : ℝ) / (n + 1)) *
    arithmeticDampingGenerator (fun k => (v k) ^ 2) n

def arithmeticDampingTotalJumpEnergy (v : ℕ → ℝ) (T : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 T, ((n : ℝ) / (n + 1)) * arithmeticDampingJumpEnergy v n

theorem arithmeticDampingTotalJumpEnergy_nonneg (v : ℕ → ℝ) (T : ℕ) :
    0 ≤ arithmeticDampingTotalJumpEnergy v T :=
  sum_nonneg fun n _ => mul_nonneg (by positivity)
    (arithmeticDampingJumpEnergy_nonneg v n)

/-- The Markov weight is exactly the original pronic energy, not a replacement norm. -/
theorem pmPowerDampedDivisorDiscreteEnergy_eq_markov (η : ℝ) (T : ℕ) :
    pmPowerDampedDivisorDiscreteEnergy η T =
      ∑ n ∈ Icc 1 T, ((n : ℝ) / (n + 1)) * (arithmeticDampingCenteredMean η n) ^ 2 := by
  unfold pmPowerDampedDivisorDiscreteEnergy
  apply sum_congr rfl
  intro n hn
  have hnpos : 0 < n := Nat.lt_of_lt_of_le Nat.zero_lt_one (mem_Icc.mp hn).1
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hnpos.ne'
  rw [arithmeticDampingCenteredMean_eq η hnpos]
  field_simp

/-- Exact pronic energy balance for the literal arithmetic source. The density
forcing remains coupled to the signed centered prefix. -/
theorem hasDerivAt_pmPowerDampedDivisorDiscreteEnergy_markov {η : ℝ} (hη : 0 < η)
    (T : ℕ) :
    HasDerivAt (fun x => pmPowerDampedDivisorDiscreteEnergy x T)
      (arithmeticDampingBoundaryFlux (arithmeticDampingCenteredMean η) T -
        arithmeticDampingTotalJumpEnergy (arithmeticDampingCenteredMean η) T -
        2 * dampedReadout η *
          ∑ n ∈ Icc 1 T, ((n : ℝ) / (n + 1)) * arithmeticDampingCenteredMean η n) η := by
  have h := HasDerivAt.fun_sum (u := Icc 1 T)
    (fun n hn => ((hasDerivAt_arithmeticDampingCenteredMean (n := n) hη
      (by have := (mem_Icc.mp hn).1; omega)).pow 2).const_mul ((n : ℝ) / (n + 1)))
  have hf : (fun x => pmPowerDampedDivisorDiscreteEnergy x T) =
      fun x => ∑ n ∈ Icc 1 T, ((n : ℝ) / (n + 1)) *
        (arithmeticDampingCenteredMean x n) ^ 2 := by
    funext x
    exact pmPowerDampedDivisorDiscreteEnergy_eq_markov x T
  rw [hf]
  apply h.congr_deriv
  unfold arithmeticDampingBoundaryFlux arithmeticDampingTotalJumpEnergy
  rw [← sum_sub_distrib, mul_sum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro n _
  have hs := arithmeticDampingGenerator_square (arithmeticDampingCenteredMean η) n
  simp only [Nat.cast_ofNat]
  nlinarith [congrArg (fun x : ℝ => ((n : ℝ) / (n + 1)) * x) hs]

end

end GaloisForLFunctions.BezoutValuationIncidence
