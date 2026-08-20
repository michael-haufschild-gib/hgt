/-
# Translated finite windows for quadratic-character second moments

The finite prefix estimate is invariant under translating the coefficient
window, because residue translation permutes a finite `ZMod` ring.  This
packages the dyadic-window shape needed in the quadratic-character portion of
Bondarenko--Heap Lemma 8 without adding a support assumption.
-/
import GaloisForLFunctions.RHTower.DirichletCharacterSecondMomentDivisorBound

open Finset

noncomputable section

namespace RHTower
namespace OddPrimeFamily

variable {I : Type*} [Fintype I]

/-- Quadratic-character shift sum over the translated finite window
`A + {1, …, M}`. -/
def quadraticWindowShiftSum [DecidableEq I] (P : OddPrimeFamily I)
    (A M : ℕ) (b : ℕ → ℂ) (x : ZMod P.modulus) : ℂ :=
  ∑ n ∈ Finset.Icc 1 M,
    b n * quadraticCharacter P (x + ((A + n : ℕ) : ZMod P.modulus))

/-- A translated coefficient window is the prefix shift sum evaluated at the translated residue. -/
theorem quadraticWindowShiftSum_eq_intervalShiftSum [DecidableEq I]
    (P : OddPrimeFamily I) (A M : ℕ) (b : ℕ → ℂ) (x : ZMod P.modulus) :
    quadraticWindowShiftSum P A M b x =
      quadraticIntervalShiftSum P M b (x + ((A : ℤ) : ZMod P.modulus)) := by
  unfold quadraticWindowShiftSum quadraticIntervalShiftSum
  apply Finset.sum_congr rfl
  intro n hn
  congr 2
  push_cast
  ring

/-- Translation-invariance of the complete finite second moment. -/
theorem quadratic_windowShiftSum_normSq_eq_interval [DecidableEq I]
    (P : OddPrimeFamily I) (A M : ℕ) (b : ℕ → ℂ) :
    ∑ x : ZMod P.modulus, Complex.normSq (quadraticWindowShiftSum P A M b x) =
      ∑ x : ZMod P.modulus, Complex.normSq (quadraticIntervalShiftSum P M b x) := by
  simp_rw [quadraticWindowShiftSum_eq_intervalShiftSum]
  exact Equiv.sum_comp (Equiv.addRight ((A : ℤ) : ZMod P.modulus))
    (fun x : ZMod P.modulus => Complex.normSq (quadraticIntervalShiftSum P M b x))

/-- Divisor-power second-moment estimate on every translated finite window. -/
theorem quadratic_windowShiftSum_normSq_le_divisorRpow [DecidableEq I]
    (P : OddPrimeFamily I) (A M : ℕ) (b : ℕ → ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∑ x : ZMod P.modulus, Complex.normSq (quadraticWindowShiftSum P A M b x) ≤
      ((M : ℝ) * (Sieve.divisorBoundConst ε * (P.modulus : ℝ) ^ ε) +
        (P.modulus : ℝ)) * ∑ n ∈ Finset.Icc 1 M, ‖b n‖ ^ 2 := by
  rw [quadratic_windowShiftSum_normSq_eq_interval]
  exact quadratic_intervalShiftSum_normSq_le_divisorRpow P M b hε

end OddPrimeFamily
end RHTower
