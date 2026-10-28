import GaloisForLFunctions.ArithmeticIndexDescent.EveryIntegerPrimeLagHasGammaSmallMixedTails
import GaloisForLFunctions.RHTower.XiMassPrimePowerVerticalIdeal
import GaloisForLFunctions.RHTower.HeatRemainderDerivative

/-!
# Gamma-small mixed source for all cubes and higher prime powers

Critical coefficients are summable over every prime and every exponent at
least three. The actual integer-lag estimate therefore pays this entire
infinite-prime mixed source in the original Gamma energy. The critical prime
and prime-square layers are separate and are not included in this bound.
-/

noncomputable section

open MeasureTheory
open RHTower

namespace GaloisForLFunctions.ArithmeticIndexDescent

open ArithmeticCastelnuovoSeveri.LogCells BiarithmeticGaugeGeometry HTGeometry

/-- Exact conversion between the literal prime coefficient and the existing critical weight. -/
theorem primePower_coefficient_eq_twice_criticalWeight (p : Nat.Primes) (k : ℕ) :
    2 * ArithmeticFunction.vonMangoldt ((p : ℕ) ^ (k + 1)) /
      Real.sqrt (((p : ℕ) ^ (k + 1) : ℕ) : ℝ) =
        2 * xiMassPrimePowerCriticalWeight p k := by
  have hp : 0 < (p : ℕ) ^ (k + 1) := pow_pos p.property.pos _
  have hh : (1 / 2 : ℂ).re = (1 / 2 : ℝ) := by norm_num
  rw [xiMassPrimePowerCriticalWeight, LSeries.norm_term_eq, if_neg hp.ne']
  simp only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  rw [hh, ← Real.sqrt_eq_rpow]
  ring

/-- Each index labels one prime power of exponent at least three. -/
def higherPrimePowerIndex (pk : Nat.Primes × ℕ) : ℕ := (pk.1 : ℕ) ^ (pk.2 + 3)

theorem higherPrimePowerIndex_injective : Function.Injective higherPrimePowerIndex := by
  rintro ⟨p, k⟩ ⟨q, l⟩ h
  obtain ⟨hpq, hkl⟩ := Nat.Prime.pow_inj p.property q.property h
  exact Prod.ext (Subtype.ext hpq) (by omega)

theorem two_le_higherPrimePowerIndex (pk : Nat.Primes × ℕ) : 2 ≤ higherPrimePowerIndex pk := by
  have h : 1 < (pk.1 : ℕ) ^ (pk.2 + 3) :=
    one_lt_pow₀ (by have := pk.1.property.two_le; omega) (by omega)
  exact h

/-- The Gamma cost includes the original coefficient and the possible odd-detail correction. -/
def higherPrimePowerGammaWeight (pk : Nat.Primes × ℕ) : ℝ :=
  4 * xiMassPrimePowerCriticalWeight pk.1 (pk.2 + 2)

theorem higherPrimePowerGammaWeight_eq (pk : Nat.Primes × ℕ) :
    higherPrimePowerGammaWeight pk =
      2 * (2 * ArithmeticFunction.vonMangoldt (higherPrimePowerIndex pk) /
        Real.sqrt (higherPrimePowerIndex pk)) := by
  have h := primePower_coefficient_eq_twice_criticalWeight pk.1 (pk.2 + 2)
  rw [show pk.2 + 2 + 1 = pk.2 + 3 by omega] at h
  change 4 * xiMassPrimePowerCriticalWeight pk.1 (pk.2 + 2) = _
  rw [higherPrimePowerIndex, h]
  ring

/-- The entire higher-power Gamma budget is finite across all primes. -/
theorem summable_higherPrimePowerGammaWeight : Summable higherPrimePowerGammaWeight :=
  summable_xiMassPrimePowerCriticalWeight_high.mul_left 4

def higherPrimePowerGammaCost : ℝ := ∑' pk : Nat.Primes × ℕ, higherPrimePowerGammaWeight pk

/-- The literal mixed contribution of every prime power of exponent at least three. -/
def higherPrimePowerMixedSource (d q : ℕ → ℝ) (X : ℕ) : ℝ :=
  ∑' pk : Nat.Primes × ℕ, integerMixedSource (higherPrimePowerIndex pk) d q X X

theorem summable_norm_higherPrimePowerMixed (d q : ℕ → ℝ) (X : ℕ) :
    Summable (fun pk : Nat.Primes × ℕ =>
      ‖integerMixedSource (higherPrimePowerIndex pk) d q X X‖) := by
  apply Summable.of_nonneg_of_le (fun pk => norm_nonneg _)
    (fun pk => ?_) (summable_higherPrimePowerGammaWeight.mul_right
      (levyEnergy (completePairProfile q d X) / cellGammaWeight 1))
  rw [Real.norm_eq_abs, higherPrimePowerGammaWeight_eq]
  exact abs_integerMixed_le_gamma d q (two_le_higherPrimePowerIndex pk) X

theorem summable_higherPrimePowerMixed (d q : ℕ → ℝ) (X : ℕ) :
    Summable (fun pk : Nat.Primes × ℕ => integerMixedSource (higherPrimePowerIndex pk) d q X X) :=
  (summable_norm_higherPrimePowerMixed d q X).of_norm

/-- One original Gamma energy pays the whole higher-power mixed tail, across infinitely many primes. -/
theorem abs_higherPrimePowerMixed_tail_le_gamma (d q : ℕ → ℝ) {A : ℕ}
    (hA : 1 ≤ A) (X : ℕ) :
    |higherPrimePowerMixedSource (fun a => if A ≤ a then d a else 0) q X| ≤
      higherPrimePowerGammaCost * (levyEnergy (completePairProfile q d X) / cellGammaWeight A) := by
  have hp (pk : Nat.Primes × ℕ) :
      |integerMixedSource (higherPrimePowerIndex pk) (fun a => if A ≤ a then d a else 0) q X X| ≤
        higherPrimePowerGammaWeight pk *
          (levyEnergy (completePairProfile q d X) / cellGammaWeight A) := by
    rw [higherPrimePowerGammaWeight_eq]
    exact abs_integerMixed_tail_le_gamma_div_weight d q hA (two_le_higherPrimePowerIndex pk) X
  have h := RHTower.abs_tsum_le_tsum_of_abs_le
    (summable_higherPrimePowerGammaWeight.mul_right
      (levyEnergy (completePairProfile q d X) / cellGammaWeight A)) hp
  rw [tsum_mul_right] at h
  exact h

/-- The finite-head error is the actual tail of the absolutely convergent higher-power source. -/
theorem higherPrimePowerMixedSource_sub_head (d q : ℕ → ℝ) (A X : ℕ) :
    higherPrimePowerMixedSource d q X -
      higherPrimePowerMixedSource (fun a => if a < A then d a else 0) q X =
        higherPrimePowerMixedSource (fun a => if A ≤ a then d a else 0) q X := by
  unfold higherPrimePowerMixedSource
  rw [← (summable_higherPrimePowerMixed d q X).tsum_sub
    (summable_higherPrimePowerMixed (fun a => if a < A then d a else 0) q X)]
  apply tsum_congr
  intro pk
  exact integerMixedSource_sub_head (higherPrimePowerIndex pk) d q A X X

/-- A fixed detail cutoff makes all cubes and higher prime powers arbitrarily Gamma-small. -/
theorem exists_higherPrimePower_gamma_small_tail {δ : ℝ} (hδ : 0 < δ) :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ (d q : ℕ → ℝ) (X : ℕ),
      |higherPrimePowerMixedSource (fun a => if A ≤ a then d a else 0) q X| ≤
        δ * levyEnergy (completePairProfile q d X) := by
  obtain ⟨A, hA⟩ := exists_nat_gt (Real.exp (higherPrimePowerGammaCost / δ))
  have hA1 : 1 ≤ A := by
    have hp : (0 : ℝ) < A := (Real.exp_pos _).trans hA
    exact Nat.one_le_iff_ne_zero.mpr (Nat.cast_ne_zero.mp hp.ne')
  have hlog : higherPrimePowerGammaCost / δ < Real.log (A : ℝ) := by
    have h := Real.log_lt_log (Real.exp_pos _) hA
    rwa [Real.log_exp] at h
  have hcoef : higherPrimePowerGammaCost / cellGammaWeight A ≤ δ := by
    apply (div_le_iff₀ (cellGammaWeight_pos hA1)).mpr
    calc
      _ ≤ δ * Real.log (A : ℝ) := by
        simpa only [mul_comm] using (div_le_iff₀ hδ).mp hlog.le
      _ ≤ _ := mul_le_mul_of_nonneg_left (log_le_cellGammaWeight hA1) hδ.le
  refine ⟨A, hA1, ?_⟩
  intro d q X
  have hE := levyEnergy_nonneg_bv (completePairProfile_bv q d X) (completePairProfile_compact q d X)
  calc
    _ ≤ _ := abs_higherPrimePowerMixed_tail_le_gamma d q hA1 X
    _ = (higherPrimePowerGammaCost / cellGammaWeight A) * levyEnergy (completePairProfile q d X) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hcoef hE

/-- The original infinite-prime higher-power mixed source has a uniform finite-detail approximation. -/
theorem exists_higherPrimePower_finite_detail_approximation {δ : ℝ} (hδ : 0 < δ) :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ (d q : ℕ → ℝ) (X : ℕ),
      |higherPrimePowerMixedSource d q X -
        higherPrimePowerMixedSource (fun a => if a < A then d a else 0) q X| ≤
          δ * levyEnergy (completePairProfile q d X) := by
  obtain ⟨A, hA, hpay⟩ := exists_higherPrimePower_gamma_small_tail hδ
  refine ⟨A, hA, ?_⟩
  intro d q X
  rw [higherPrimePowerMixedSource_sub_head]
  exact hpay d q X

end GaloisForLFunctions.ArithmeticIndexDescent

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.higherPrimePowerIndex_injective
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.summable_norm_higherPrimePowerMixed
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.abs_higherPrimePowerMixed_tail_le_gamma
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.exists_higherPrimePower_gamma_small_tail
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.exists_higherPrimePower_finite_detail_approximation
