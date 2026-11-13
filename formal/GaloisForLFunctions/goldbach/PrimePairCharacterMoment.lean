import GaloisForLFunctions.goldbach.OddCharacterProjection
import GaloisForLFunctions.goldbach.ReducedResidueAntidiagonal
import GaloisForLFunctions.goldbach.CoprimePrimePairCorrection

/-!
# Prime pairs as odd-character moments

Reduced residues modulo `N` parametrize the coprime antidiagonal `p+q=N`
by negation. The odd-character projection therefore gives an exact formula
for the existing prime-pair weight, including its central diagonal.
-/

namespace GaloisForLFunctions.Goldbach

open Finset
open scoped Classical

noncomputable section

/-- The reduced prime-pair count is a literal correlation of the existing prime weight. -/
theorem coprimePrimePairWeight_eq_unit_correlation (N : ℕ) :
    coprimePrimePairWeight (N + 2) =
      ∑ u : (ZMod (N + 2))ˣ,
        primeLogWeight ((-u : (ZMod (N + 2))ˣ) : ZMod (N + 2)).val *
          primeLogWeight (u : ZMod (N + 2)).val := by
  rw [← sum_units_eq_coprime_antidiagonal N
    (fun p q => primeLogWeight p * primeLogWeight q)]
  exact sum_congr rfl fun u _ => mul_comm _ _

/-- Exact character-moment formula for the character-visible prime pairs. -/
theorem coprimePrimePairWeight_odd_character_identity (N : ℕ) :
    ((N + 2).totient : ℝ) * coprimePrimePairWeight (N + 2) =
      ((N + 2).totient : ℝ) *
        (∑ u : (ZMod (N + 2))ˣ, primeLogWeight (u : ZMod (N + 2)).val ^ 2) -
      2 * ∑ χ : DirichletCharacter ℂ (N + 2) with χ.Odd,
        ‖unitCharacterSum (N + 1)
          (fun u => (primeLogWeight (u : ZMod (N + 2)).val : ℂ)) χ‖ ^ 2 := by
  have h := twice_sum_odd_norm_sq_unitCharacterSum (N + 1)
    (fun u => primeLogWeight (u : ZMod (N + 2)).val)
  rw [coprimePrimePairWeight_eq_unit_correlation]
  linarith only [h]

/-- The full prime-pair count includes the diagonal omitted by Dirichlet characters. -/
theorem primePairWeight_odd_character_identity (N : ℕ) :
    ((N + 2).totient : ℝ) * primePairWeight (N + 2) =
      ((N + 2).totient : ℝ) *
        ((∑ u : (ZMod (N + 2))ˣ, primeLogWeight (u : ZMod (N + 2)).val ^ 2) +
          if (N + 2) % 2 = 0 then primeLogWeight ((N + 2) / 2) ^ 2 else 0) -
      2 * ∑ χ : DirichletCharacter ℂ (N + 2) with χ.Odd,
        ‖unitCharacterSum (N + 1)
          (fun u => (primeLogWeight (u : ZMod (N + 2)).val : ℂ)) χ‖ ^ 2 := by
  rw [primePairWeight_eq_coprime_add_diagonal, mul_add,
    coprimePrimePairWeight_odd_character_identity]
  ring

end GaloisForLFunctions.Goldbach
