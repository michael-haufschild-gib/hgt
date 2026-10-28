import GaloisForLFunctions.ArithmeticIndexDescent.EveryIntegerPrimeLagHasGammaSmallMixedTails
import GaloisForLFunctions.BezoutValuationIncidence.EnergyMeanOfThePowerDampedSourceTendsToOne
import GaloisForLFunctions.RHTower.HeatRemainderDerivative

/-!
# Gamma-small detail tails for every fixed Euler mixed source

The entire sequence of powers of any prime has summable critical weights.
The integer-lag estimate sums in the original complete-profile Gamma energy,
including the odd-prime detail correction. Any fixed finite set of Euler
factors therefore has one horizon-independent finite detail approximation.
-/

noncomputable section

open MeasureTheory Finset
open RHTower

namespace GaloisForLFunctions.ArithmeticIndexDescent

open ArithmeticCastelnuovoSeveri.LogCells BiarithmeticGaugeGeometry HTGeometry

/-- The literal critical coefficient of a successive prime power. -/
def primePowerMixedWeight (p : Nat.Primes) (k : ℕ) : ℝ :=
  2 * ArithmeticFunction.vonMangoldt ((p : ℕ) ^ (k + 1)) /
    Real.sqrt (((p : ℕ) ^ (k + 1) : ℕ) : ℝ)

def primeEulerMixedWeightTotal (p : Nat.Primes) : ℝ :=
  2 * Real.log (p : ℝ) / (Real.sqrt (p : ℝ) - 1)

/-- Exact coefficient sum for the entire fixed Euler factor. -/
theorem hasSum_primePowerMixedWeight (p : Nat.Primes) :
    HasSum (primePowerMixedWeight p) (primeEulerMixedWeightTotal p) := by
  have hs0 := BezoutValuationIncidence.hasSum_prime_power_vonMangoldt (s := (1 / 2 : ℝ))
    (by norm_num) p
  have hs := hs0.mul_left 2
  rw [← Real.sqrt_eq_rpow] at hs
  have hs' : HasSum (fun k : ℕ => 2 * (ArithmeticFunction.vonMangoldt ((p : ℕ) ^ (k + 1)) *
      ((((p : ℕ) ^ (k + 1) : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))))) (primeEulerMixedWeightTotal p) := by
    simpa only [mul_div_assoc, primeEulerMixedWeightTotal] using hs
  refine hs'.congr_fun fun k => ?_
  rw [Real.rpow_neg (Nat.cast_nonneg _), ← Real.sqrt_eq_rpow]
  unfold primePowerMixedWeight
  ring

theorem primePowerMixedWeight_nonneg (p : Nat.Primes) (k : ℕ) : 0 ≤ primePowerMixedWeight p k :=
  div_nonneg (mul_nonneg (by norm_num) ArithmeticFunction.vonMangoldt_nonneg) (Real.sqrt_nonneg _)

theorem primeEulerMixedWeightTotal_nonneg (p : Nat.Primes) : 0 ≤ primeEulerMixedWeightTotal p := by
  rw [← (hasSum_primePowerMixedWeight p).tsum_eq]
  exact tsum_nonneg (primePowerMixedWeight_nonneg p)

private theorem primePower_ge_two (p : Nat.Primes) (k : ℕ) : 2 ≤ (p : ℕ) ^ (k + 1) := by
  have h : 1 < (p : ℕ) ^ (k + 1) := one_lt_pow₀ (by have := p.property.two_le; omega) (by omega)
  omega

/-- The entire literal mixed Euler source of one prime, with all its powers. -/
def primeEulerMixedSource (p : Nat.Primes) (d q : ℕ → ℝ) (X : ℕ) : ℝ :=
  ∑' k : ℕ, integerMixedSource ((p : ℕ) ^ (k + 1)) d q X X

/-- The actual mixed Euler series is absolutely convergent for every original complete profile. -/
theorem summable_norm_primeEulerMixed (p : Nat.Primes) (d q : ℕ → ℝ) (X : ℕ) :
    Summable (fun k : ℕ => ‖integerMixedSource ((p : ℕ) ^ (k + 1)) d q X X‖) := by
  apply Summable.of_nonneg_of_le (fun k => norm_nonneg _)
    (fun k => ?_) (((hasSum_primePowerMixedWeight p).summable.mul_left 2).mul_right
      (levyEnergy (completePairProfile q d X) / cellGammaWeight 1))
  simpa only [Real.norm_eq_abs, primePowerMixedWeight] using
    abs_integerMixed_le_gamma d q (primePower_ge_two p k) X

theorem summable_primeEulerMixed (p : Nat.Primes) (d q : ℕ → ℝ) (X : ℕ) :
    Summable (fun k : ℕ => integerMixedSource ((p : ℕ) ^ (k + 1)) d q X X) :=
  (summable_norm_primeEulerMixed p d q X).of_norm

/-- Every prime's entire mixed Euler tail is paid by the original untruncated Gamma energy. -/
theorem abs_primeEulerMixed_tail_le_gamma (p : Nat.Primes) (d q : ℕ → ℝ) {A : ℕ}
    (hA : 1 ≤ A) (X : ℕ) :
    |primeEulerMixedSource p (fun a => if A ≤ a then d a else 0) q X| ≤
      (2 * primeEulerMixedWeightTotal p) *
        (levyEnergy (completePairProfile q d X) / cellGammaWeight A) := by
  have h := RHTower.abs_tsum_le_tsum_of_abs_le
    (((hasSum_primePowerMixedWeight p).summable.mul_left 2).mul_right
      (levyEnergy (completePairProfile q d X) / cellGammaWeight A))
    (fun k => abs_integerMixed_tail_le_gamma_div_weight d q hA (primePower_ge_two p k) X)
  rw [tsum_mul_right, tsum_mul_left, (hasSum_primePowerMixedWeight p).tsum_eq] at h
  exact h

/-- Exact head subtraction in the original absolutely convergent Euler source. -/
theorem primeEulerMixedSource_sub_head (p : Nat.Primes) (d q : ℕ → ℝ) (A X : ℕ) :
    primeEulerMixedSource p d q X -
      primeEulerMixedSource p (fun a => if a < A then d a else 0) q X =
        primeEulerMixedSource p (fun a => if A ≤ a then d a else 0) q X := by
  unfold primeEulerMixedSource
  rw [← (summable_primeEulerMixed p d q X).tsum_sub
    (summable_primeEulerMixed p (fun a => if a < A then d a else 0) q X)]
  apply tsum_congr
  intro k
  exact integerMixedSource_sub_head ((p : ℕ) ^ (k + 1)) d q A X X

/-- All powers of every prime in a fixed finite set, evaluated on the original mixed vectors. -/
def finiteEulerMixedSource (P : Finset Nat.Primes) (d q : ℕ → ℝ) (X : ℕ) : ℝ :=
  ∑ p ∈ P, primeEulerMixedSource p d q X

def finiteEulerMixedGammaCost (P : Finset Nat.Primes) : ℝ :=
  ∑ p ∈ P, 2 * primeEulerMixedWeightTotal p

/-- A fixed finite set of full Euler factors has a quantitative common Gamma-tail budget. -/
theorem abs_finiteEulerMixed_tail_le_gamma (P : Finset Nat.Primes) (d q : ℕ → ℝ) {A : ℕ}
    (hA : 1 ≤ A) (X : ℕ) :
    |finiteEulerMixedSource P (fun a => if A ≤ a then d a else 0) q X| ≤
      finiteEulerMixedGammaCost P * (levyEnergy (completePairProfile q d X) / cellGammaWeight A) := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ p ∈ P, (2 * primeEulerMixedWeightTotal p) *
        (levyEnergy (completePairProfile q d X) / cellGammaWeight A) :=
      Finset.sum_le_sum fun p _ => abs_primeEulerMixed_tail_le_gamma p d q hA X
    _ = _ := (Finset.sum_mul _ _ _).symm

theorem finiteEulerMixedSource_sub_head (P : Finset Nat.Primes) (d q : ℕ → ℝ) (A X : ℕ) :
    finiteEulerMixedSource P d q X -
      finiteEulerMixedSource P (fun a => if a < A then d a else 0) q X =
        finiteEulerMixedSource P (fun a => if A ≤ a then d a else 0) q X := by
  unfold finiteEulerMixedSource
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun p _ => primeEulerMixedSource_sub_head p d q A X

/-- A single finite detail cutoff pays any fixed finite collection of complete Euler factors. -/
theorem exists_finiteEuler_gamma_small_tail (P : Finset Nat.Primes) {δ : ℝ} (hδ : 0 < δ) :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ (d q : ℕ → ℝ) (X : ℕ),
      |finiteEulerMixedSource P (fun a => if A ≤ a then d a else 0) q X| ≤
        δ * levyEnergy (completePairProfile q d X) := by
  obtain ⟨A, hA⟩ := exists_nat_gt (Real.exp (finiteEulerMixedGammaCost P / δ))
  have hA1 : 1 ≤ A := by
    have hp : (0 : ℝ) < A := (Real.exp_pos _).trans hA
    exact Nat.one_le_iff_ne_zero.mpr (Nat.cast_ne_zero.mp hp.ne')
  have hlog : finiteEulerMixedGammaCost P / δ < Real.log (A : ℝ) := by
    have h := Real.log_lt_log (Real.exp_pos _) hA
    rwa [Real.log_exp] at h
  have hcoef : finiteEulerMixedGammaCost P / cellGammaWeight A ≤ δ := by
    apply (div_le_iff₀ (cellGammaWeight_pos hA1)).mpr
    calc
      _ ≤ δ * Real.log (A : ℝ) := by
        simpa only [mul_comm] using (div_le_iff₀ hδ).mp hlog.le
      _ ≤ _ := mul_le_mul_of_nonneg_left (log_le_cellGammaWeight hA1) hδ.le
  refine ⟨A, hA1, ?_⟩
  intro d q X
  have hE := levyEnergy_nonneg_bv (completePairProfile_bv q d X) (completePairProfile_compact q d X)
  calc
    _ ≤ _ := abs_finiteEulerMixed_tail_le_gamma P d q hA1 X
    _ = (finiteEulerMixedGammaCost P / cellGammaWeight A) * levyEnergy (completePairProfile q d X) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hcoef hE

/-- A finite detail head approximates these entire Euler factors uniformly at every cell horizon. -/
theorem exists_finiteEuler_finite_detail_approximation (P : Finset Nat.Primes) {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ (d q : ℕ → ℝ) (X : ℕ),
      |finiteEulerMixedSource P d q X -
        finiteEulerMixedSource P (fun a => if a < A then d a else 0) q X| ≤
          δ * levyEnergy (completePairProfile q d X) := by
  obtain ⟨A, hA, hpay⟩ := exists_finiteEuler_gamma_small_tail P hδ
  refine ⟨A, hA, ?_⟩
  intro d q X
  rw [finiteEulerMixedSource_sub_head]
  exact hpay d q X

end GaloisForLFunctions.ArithmeticIndexDescent

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.hasSum_primePowerMixedWeight
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.summable_norm_primeEulerMixed
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.abs_primeEulerMixed_tail_le_gamma
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.exists_finiteEuler_gamma_small_tail
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.exists_finiteEuler_finite_detail_approximation
