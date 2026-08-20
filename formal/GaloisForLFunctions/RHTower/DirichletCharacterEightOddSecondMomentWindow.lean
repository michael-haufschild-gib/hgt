/-
# Translated conductor-eight/odd quadratic-character windows

Finite residue translation packages the dyadic-window form of the closed
second-moment bounds for both explicit conductor-eight CRT characters.
-/
import GaloisForLFunctions.RHTower.DirichletCharacterEightOddSecondMoment

open Finset

noncomputable section

namespace RHTower
namespace OddPrimeFamily

variable {I : Type*} [Fintype I]

/-- Selected conductor-eight/odd quadratic-character sum over `A + {1, …, M}`. -/
def eightOddQuadraticWindowShiftSum [DecidableEq I] (κ : EightQuadraticKind)
    (P : OddPrimeFamily I) (A M : ℕ) (b : ℕ → ℂ) (x : ZMod (eightOddModulus P)) : ℂ :=
  ∑ n ∈ Finset.Icc 1 M,
    b n * eightOddQuadraticCharacterOfKind κ P
      (x + ((A + n : ℕ) : ZMod (eightOddModulus P)))

/-- A translated conductor-eight/odd window is a residue translate of its prefix sum. -/
theorem eightOddQuadraticWindowShiftSum_eq_intervalShiftSum [DecidableEq I]
    (κ : EightQuadraticKind) (P : OddPrimeFamily I) (A M : ℕ) (b : ℕ → ℂ)
    (x : ZMod (eightOddModulus P)) :
    eightOddQuadraticWindowShiftSum κ P A M b x =
      eightOddQuadraticIntervalShiftSum κ P M b
        (x + ((A : ℤ) : ZMod (eightOddModulus P))) := by
  unfold eightOddQuadraticWindowShiftSum eightOddQuadraticIntervalShiftSum
  apply Finset.sum_congr rfl
  intro n hn
  congr 2
  push_cast
  ring

/-- Translation-invariance of the complete finite second moment for either conductor-eight kind. -/
theorem eightOdd_quadratic_windowShiftSum_normSq_eq_interval [DecidableEq I]
    (κ : EightQuadraticKind) (P : OddPrimeFamily I) (A M : ℕ) (b : ℕ → ℂ) :
    ∑ x : ZMod (eightOddModulus P),
      Complex.normSq (eightOddQuadraticWindowShiftSum κ P A M b x) =
      ∑ x : ZMod (eightOddModulus P),
        Complex.normSq (eightOddQuadraticIntervalShiftSum κ P M b x) := by
  simp_rw [eightOddQuadraticWindowShiftSum_eq_intervalShiftSum]
  exact Equiv.sum_comp (Equiv.addRight ((A : ℤ) : ZMod (eightOddModulus P)))
    (fun x : ZMod (eightOddModulus P) =>
      Complex.normSq (eightOddQuadraticIntervalShiftSum κ P M b x))

/-- Divisor-power finite second-moment estimate on every selected conductor-eight/odd window. -/
theorem eightOdd_quadratic_windowShiftSum_normSq_le_divisorRpow [DecidableEq I]
    (κ : EightQuadraticKind) (P : OddPrimeFamily I) (A M : ℕ) (b : ℕ → ℂ)
    {ε : ℝ} (hε : 0 < ε) :
    ∑ x : ZMod (eightOddModulus P),
      Complex.normSq (eightOddQuadraticWindowShiftSum κ P A M b x) ≤
      8 * (((M : ℝ) * (Sieve.divisorBoundConst ε * (eightOddModulus P : ℝ) ^ ε) +
        (eightOddModulus P : ℝ)) * ∑ n ∈ Finset.Icc 1 M, ‖b n‖ ^ 2) := by
  rw [eightOdd_quadratic_windowShiftSum_normSq_eq_interval]
  exact eightOdd_quadratic_intervalShiftSum_normSq_le_divisorRpow κ P M b hε

end OddPrimeFamily
end RHTower
