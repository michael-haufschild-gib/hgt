/-
# Translated level-four/odd quadratic-character windows

The level-four/odd second moment is invariant under finite residue translation.
This gives the dyadic-window geometry without a support premise.
-/
import GaloisForLFunctions.RHTower.DirichletCharacterTwoAdicSecondMomentDivisorBound

open Finset

noncomputable section

namespace RHTower
namespace OddPrimeFamily

variable {I : Type*} [Fintype I]

/-- Level-four/odd quadratic-character shift sum over `A + {1, …, M}`. -/
def fourOddQuadraticWindowShiftSum [DecidableEq I] (P : OddPrimeFamily I)
    (A M : ℕ) (b : ℕ → ℂ) (x : ZMod (fourOddModulus P)) : ℂ :=
  ∑ n ∈ Finset.Icc 1 M,
    b n * fourOddQuadraticCharacter P (x + ((A + n : ℕ) : ZMod (fourOddModulus P)))

/-- A translated level-four/odd window is a residue translate of the prefix sum. -/
theorem fourOddQuadraticWindowShiftSum_eq_intervalShiftSum [DecidableEq I]
    (P : OddPrimeFamily I) (A M : ℕ) (b : ℕ → ℂ) (x : ZMod (fourOddModulus P)) :
    fourOddQuadraticWindowShiftSum P A M b x =
      fourOddQuadraticIntervalShiftSum P M b (x + ((A : ℤ) : ZMod (fourOddModulus P))) := by
  unfold fourOddQuadraticWindowShiftSum fourOddQuadraticIntervalShiftSum
  apply Finset.sum_congr rfl
  intro n hn
  congr 2
  push_cast
  ring

/-- Translation-invariance of the complete level-four/odd finite second moment. -/
theorem fourOdd_quadratic_windowShiftSum_normSq_eq_interval [DecidableEq I]
    (P : OddPrimeFamily I) (A M : ℕ) (b : ℕ → ℂ) :
    ∑ x : ZMod (fourOddModulus P), Complex.normSq (fourOddQuadraticWindowShiftSum P A M b x) =
      ∑ x : ZMod (fourOddModulus P),
        Complex.normSq (fourOddQuadraticIntervalShiftSum P M b x) := by
  simp_rw [fourOddQuadraticWindowShiftSum_eq_intervalShiftSum]
  exact Equiv.sum_comp (Equiv.addRight ((A : ℤ) : ZMod (fourOddModulus P)))
    (fun x : ZMod (fourOddModulus P) => Complex.normSq (fourOddQuadraticIntervalShiftSum P M b x))

/-- Divisor-power second-moment estimate on every translated level-four/odd finite window. -/
theorem fourOdd_quadratic_windowShiftSum_normSq_le_divisorRpow [DecidableEq I]
    (P : OddPrimeFamily I) (A M : ℕ) (b : ℕ → ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∑ x : ZMod (fourOddModulus P), Complex.normSq (fourOddQuadraticWindowShiftSum P A M b x) ≤
      4 * (((M : ℝ) * (Sieve.divisorBoundConst ε * (fourOddModulus P : ℝ) ^ ε) +
        (fourOddModulus P : ℝ)) * ∑ n ∈ Finset.Icc 1 M, ‖b n‖ ^ 2) := by
  rw [fourOdd_quadratic_windowShiftSum_normSq_eq_interval]
  exact fourOdd_quadratic_intervalShiftSum_normSq_le_divisorRpow P M b hε

end OddPrimeFamily
end RHTower
