import GaloisForLFunctions.ArithmeticIndexDescent.EveryEvenPrimeLagHasGammaSmallMixedTails
import GaloisForLFunctions.BezoutValuationIncidence.EnergyMeanOfThePowerDampedSourceTendsToOne
import GaloisForLFunctions.RHTower.HeatRemainderDerivative

/-!
# Gamma-small tails for the entire prime-two Euler mixed source

Every power of two has the even-lag full-profile payment. Its literal critical
coefficients form a summable Euler factor. The original Gamma energy therefore
pays the whole infinite mixed sum, and high-detail tails have arbitrarily small
relative bound at every horizon. The pure coarse Euler term is separate.
-/

noncomputable section

open MeasureTheory
open RHTower

namespace GaloisForLFunctions.ArithmeticIndexDescent

open ArithmeticCastelnuovoSeveri.LogCells BiarithmeticGaugeGeometry HTGeometry

/-- Literal critical prime coefficient at the successive powers of two. -/
def primeTwoPowerWeight (k : ℕ) : ℝ :=
  2 * ArithmeticFunction.vonMangoldt (2 ^ (k + 1)) / Real.sqrt ((2 ^ (k + 1) : ℕ) : ℝ)

def primeTwoEulerWeightTotal : ℝ := 2 * Real.log 2 / (Real.sqrt 2 - 1)

/-- The complete Euler coefficient sum, with no power cutoff. -/
theorem hasSum_primeTwoPowerWeight : HasSum primeTwoPowerWeight primeTwoEulerWeightTotal := by
  let p : Nat.Primes := ⟨2, Nat.prime_two⟩
  have hs0 := BezoutValuationIncidence.hasSum_prime_power_vonMangoldt (s := (1 / 2 : ℝ))
    (by norm_num) p
  change HasSum (fun k : ℕ => ArithmeticFunction.vonMangoldt (2 ^ (k + 1)) *
      (((2 ^ (k + 1) : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))))
    (Real.log 2 / ((2 : ℝ) ^ (1 / 2 : ℝ) - 1)) at hs0
  have hs := hs0.mul_left 2
  rw [← Real.sqrt_eq_rpow] at hs
  have hs' : HasSum (fun k : ℕ => 2 * (ArithmeticFunction.vonMangoldt (2 ^ (k + 1)) *
      (((2 ^ (k + 1) : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))))) primeTwoEulerWeightTotal := by
    simpa only [mul_div_assoc, primeTwoEulerWeightTotal] using hs
  refine hs'.congr_fun fun k => ?_
  rw [Real.rpow_neg (Nat.cast_nonneg _), ← Real.sqrt_eq_rpow]
  unfold primeTwoPowerWeight
  ring

theorem primeTwoPowerWeight_nonneg (k : ℕ) : 0 ≤ primeTwoPowerWeight k :=
  div_nonneg (mul_nonneg (by norm_num) ArithmeticFunction.vonMangoldt_nonneg) (Real.sqrt_nonneg _)

theorem primeTwoEulerWeightTotal_nonneg : 0 ≤ primeTwoEulerWeightTotal := by
  rw [← hasSum_primeTwoPowerWeight.tsum_eq]
  exact tsum_nonneg primeTwoPowerWeight_nonneg

private theorem twoPow_even (k : ℕ) : Even (2 ^ (k + 1)) := by
  refine ⟨2 ^ k, ?_⟩
  rw [pow_succ]
  omega

private theorem twoPow_ge_two (k : ℕ) : 2 ≤ 2 ^ (k + 1) := by
  have h : 1 < (2 : ℕ) ^ (k + 1) := one_lt_pow₀ (by norm_num) (by omega)
  omega

/-- The entire literal prime-two Euler mixed contribution on complete cells. -/
def primeTwoEulerMixedSource (d q : ℕ → ℝ) (X : ℕ) : ℝ :=
  ∑' k : ℕ, integerMixedSource (2 ^ (k + 1)) d q X X

/-- Every actual mixed Euler series is absolutely convergent in the original source. -/
theorem summable_norm_primeTwoEulerMixed (d q : ℕ → ℝ) (X : ℕ) :
    Summable (fun k : ℕ => ‖integerMixedSource (2 ^ (k + 1)) d q X X‖) := by
  apply Summable.of_nonneg_of_le (fun k => norm_nonneg _)
    (fun k => ?_) (hasSum_primeTwoPowerWeight.summable.mul_right
      (levyEnergy (completePairProfile q d X) / cellGammaWeight 1))
  simpa only [Real.norm_eq_abs, primeTwoPowerWeight] using
    abs_evenMixed_le_gamma d q (twoPow_ge_two k) (twoPow_even k) X

theorem summable_primeTwoEulerMixed (d q : ℕ → ℝ) (X : ℕ) :
    Summable (fun k : ℕ => integerMixedSource (2 ^ (k + 1)) d q X X) :=
  (summable_norm_primeTwoEulerMixed d q X).of_norm

/-- The full infinite mixed Euler factor is Gamma-bounded uniformly in the horizon. -/
theorem abs_primeTwoEulerMixed_le_gamma (d q : ℕ → ℝ) (X : ℕ) :
    |primeTwoEulerMixedSource d q X| ≤ primeTwoEulerWeightTotal *
      (levyEnergy (completePairProfile q d X) / cellGammaWeight 1) := by
  have h := RHTower.abs_tsum_le_tsum_of_abs_le
    (hasSum_primeTwoPowerWeight.summable.mul_right
      (levyEnergy (completePairProfile q d X) / cellGammaWeight 1))
    (fun k => abs_evenMixed_le_gamma d q (twoPow_ge_two k) (twoPow_even k) X)
  rw [tsum_mul_right, hasSum_primeTwoPowerWeight.tsum_eq] at h
  exact h

/-- The entire Euler tail is paid by the untruncated original Gamma profile. -/
theorem abs_primeTwoEulerMixed_tail_le_gamma (d q : ℕ → ℝ) {A : ℕ}
    (hA : 1 ≤ A) (X : ℕ) :
    |primeTwoEulerMixedSource (fun a => if A ≤ a then d a else 0) q X| ≤
      primeTwoEulerWeightTotal * (levyEnergy (completePairProfile q d X) / cellGammaWeight A) := by
  have h := RHTower.abs_tsum_le_tsum_of_abs_le
    (hasSum_primeTwoPowerWeight.summable.mul_right
      (levyEnergy (completePairProfile q d X) / cellGammaWeight A))
    (fun k => abs_evenMixed_tail_le_gamma_div_weight d q hA (twoPow_ge_two k) (twoPow_even k) X)
  rw [tsum_mul_right, hasSum_primeTwoPowerWeight.tsum_eq] at h
  exact h

/-- Finite-head subtraction commutes with the absolutely convergent original Euler sum. -/
theorem primeTwoEulerMixedSource_sub_head (d q : ℕ → ℝ) (A X : ℕ) :
    primeTwoEulerMixedSource d q X -
      primeTwoEulerMixedSource (fun a => if a < A then d a else 0) q X =
        primeTwoEulerMixedSource (fun a => if A ≤ a then d a else 0) q X := by
  unfold primeTwoEulerMixedSource
  rw [← (summable_primeTwoEulerMixed d q X).tsum_sub
    (summable_primeTwoEulerMixed (fun a => if a < A then d a else 0) q X)]
  apply tsum_congr
  intro k
  exact integerMixedSource_sub_head (2 ^ (k + 1)) d q A X X

/-- One fixed detail cutoff makes the entire mixed Euler factor arbitrarily Gamma-small. -/
theorem exists_primeTwoEuler_gamma_small_tail {δ : ℝ} (hδ : 0 < δ) :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ (d q : ℕ → ℝ) (X : ℕ),
      |primeTwoEulerMixedSource (fun a => if A ≤ a then d a else 0) q X| ≤
        δ * levyEnergy (completePairProfile q d X) := by
  obtain ⟨A, hA⟩ := exists_nat_gt (Real.exp (primeTwoEulerWeightTotal / δ))
  have hA1 : 1 ≤ A := by
    have hp : (0 : ℝ) < A := (Real.exp_pos _).trans hA
    exact Nat.one_le_iff_ne_zero.mpr (Nat.cast_ne_zero.mp hp.ne')
  have hlog : primeTwoEulerWeightTotal / δ < Real.log (A : ℝ) := by
    have h := Real.log_lt_log (Real.exp_pos _) hA
    rwa [Real.log_exp] at h
  have hcoef : primeTwoEulerWeightTotal / cellGammaWeight A ≤ δ := by
    apply (div_le_iff₀ (cellGammaWeight_pos hA1)).mpr
    calc
      _ ≤ δ * Real.log (A : ℝ) := by
        simpa only [mul_comm] using (div_le_iff₀ hδ).mp hlog.le
      _ ≤ _ := mul_le_mul_of_nonneg_left (log_le_cellGammaWeight hA1) hδ.le
  refine ⟨A, hA1, ?_⟩
  intro d q X
  have hE := levyEnergy_nonneg_bv (completePairProfile_bv q d X) (completePairProfile_compact q d X)
  calc
    _ ≤ _ := abs_primeTwoEulerMixed_tail_le_gamma d q hA1 X
    _ = (primeTwoEulerWeightTotal / cellGammaWeight A) * levyEnergy (completePairProfile q d X) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hcoef hE

/-- Finitely many detail readings approximate the entire original Euler mixed source. -/
theorem exists_primeTwoEuler_finite_detail_approximation {δ : ℝ} (hδ : 0 < δ) :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ (d q : ℕ → ℝ) (X : ℕ),
      |primeTwoEulerMixedSource d q X -
        primeTwoEulerMixedSource (fun a => if a < A then d a else 0) q X| ≤
          δ * levyEnergy (completePairProfile q d X) := by
  obtain ⟨A, hA, hpay⟩ := exists_primeTwoEuler_gamma_small_tail hδ
  refine ⟨A, hA, ?_⟩
  intro d q X
  rw [primeTwoEulerMixedSource_sub_head]
  exact hpay d q X

end GaloisForLFunctions.ArithmeticIndexDescent

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.hasSum_primeTwoPowerWeight
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.summable_norm_primeTwoEulerMixed
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.abs_primeTwoEulerMixed_tail_le_gamma
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.exists_primeTwoEuler_gamma_small_tail
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.exists_primeTwoEuler_finite_detail_approximation
