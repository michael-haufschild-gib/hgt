import GaloisForLFunctions.CriticalScaleArithmeticRigidity.PrimeGeneratorPole
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheRamanujanModesAreValuationSteps

/-!
# Coprime transport of the literal prime source

A Mangoldt-weighted dilation changes at most one of two coprime conductor
factors. Summing this exact product rule gives the same derivation law for
the complete normalized generator. Adjunction weights add over the same
coprime factorization.
-/

noncomputable section

open Finset ArithmeticFunction
open scoped Classical

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open RenormalizedArithmeticPotentialTheory SuccessorShellArithmetic
  ArithmeticIntersectionTheory BezoutValuationIncidence CriticalArithmeticCorrelationTheory

/-- The complete arithmetic generator applied to one normalized conductor mode. -/
def normalizedPrimeModeSource (m n : ℕ) : ℝ :=
  ramanujanLogDivisorJet m n / Real.sqrt (m.totient : ℝ) -
    (Real.log m + tameDifferent m) * normalizedRamanujanMode m n

theorem arithmeticPrimeGenerator_eq_modeSource (Q : ℕ) (a : ℕ → ℝ) (n : ℕ) :
    arithmeticPrimeGenerator Q a n = ∑ m ∈ Icc 1 Q, a m * normalizedPrimeModeSource m n :=
  arithmeticPrimeGenerator_eq_jet Q a n

/-- Every normalized source mode is the actual convergent Mangoldt-weighted dilation sum. -/
theorem hasSum_normalizedPrimeModeSource {m : ℕ} (hm : 0 < m) (n : ℕ) :
    HasSum (fun k : ℕ => vonMangoldt k / (k : ℝ) *
      (normalizedRamanujanMode m (k * n) - normalizedRamanujanMode m n))
      (normalizedPrimeModeSource m n) := by
  have h := hasSum_normalizedRamanujanPacket_up m (fun r => if r = m then 1 else 0) n
  simpa only [ite_mul, one_mul, zero_mul, sum_ite_eq',
    if_pos (mem_Icc.mpr ⟨hm, le_rfl⟩), normalizedPrimeModeSource] using h

/-- Normalizing the exact arithmetic product rule preserves every Mangoldt weight. -/
theorem normalizedPrimeJump_mul_of_coprime {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b) (k n : ℕ) :
    vonMangoldt k / (k : ℝ) *
        (normalizedRamanujanMode (a * b) (k * n) - normalizedRamanujanMode (a * b) n) =
      normalizedRamanujanMode b n * (vonMangoldt k / (k : ℝ) *
        (normalizedRamanujanMode a (k * n) - normalizedRamanujanMode a n)) +
      normalizedRamanujanMode a n * (vonMangoldt k / (k : ℝ) *
        (normalizedRamanujanMode b (k * n) - normalizedRamanujanMode b n)) := by
  have h := congrArg
    (fun x : ℝ => x / ((k : ℝ) * Real.sqrt (a.totient : ℝ) * Real.sqrt (b.totient : ℝ)))
    (ramanujanCoefficient_up_difference_mul hab n k)
  simp only [normalizedRamanujanMode_eq_coefficient (Nat.mul_pos ha hb),
    normalizedRamanujanMode_eq_coefficient ha, normalizedRamanujanMode_eq_coefficient hb,
    Nat.totient_mul hab, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _)]
  simp only [Nat.mul_comm n k, div_eq_mul_inv, mul_inv_rev] at h ⊢
  linear_combination h

/-- The complete literal generator is a derivation across coprime conductor factors. -/
theorem normalizedPrimeModeSource_mul_of_coprime {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b) (n : ℕ) :
    normalizedPrimeModeSource (a * b) n =
      normalizedRamanujanMode b n * normalizedPrimeModeSource a n +
        normalizedRamanujanMode a n * normalizedPrimeModeSource b n := by
  have h := ((hasSum_normalizedPrimeModeSource ha n).mul_left (normalizedRamanujanMode b n)).add
    ((hasSum_normalizedPrimeModeSource hb n).mul_left (normalizedRamanujanMode a n))
  apply (hasSum_normalizedPrimeModeSource (Nat.mul_pos ha hb) n).unique
  apply h.congr_fun
  intro k
  exact normalizedPrimeJump_mul_of_coprime ha hb hab k n

/-- The exact square-energy weight adds under the same coprime conductor product. -/
theorem adjunctionWeight_mul_of_coprime {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b) :
    Real.log (a * b : ℕ) + tameDifferent (a * b) =
      (Real.log a + tameDifferent a) + (Real.log b + tameDifferent b) := by
  rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast ha.ne') (by exact_mod_cast hb.ne'),
    tameDifferent_mul hab]
  ring

#print axioms hasSum_normalizedPrimeModeSource
#print axioms normalizedPrimeJump_mul_of_coprime
#print axioms normalizedPrimeModeSource_mul_of_coprime
#print axioms adjunctionWeight_mul_of_coprime

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
