import GaloisForLFunctions.RHTower.FZZCigarParityDelaySourceContinuation
import GaloisForLFunctions.RHTower.FermiMellinObserver
import GaloisForLFunctions.RHTower.BornSuperKMSCovariance

/-!
# Diagonal super-KMS cannot orient the FZZ parity divisor

The source-first FZZ parity delay is the graded charge supertrace. A tempting orientation principle
is therefore diagonal KMS/passivity at the critical physical inverse temperature `beta = 1`, which
corresponds to `Re s = 1/2` in the half-dilated gauge.

This file proves the sharp no-go. For every `beta > 0`:

* the graded charge series is summable;
* the actual FZZ parity Mellin mass at `s = beta/2` is a strictly positive real;
* every positive integer dilation obeys the exact super-KMS covariance law.

In particular `beta = 2` is fully admissible, so these diagonal laws cannot select `beta = 1`.
The positive survivor is a temperature-universal, source-exact graded KMS phase. Any remaining FZZ
orientation must use off-diagonal, interacting, nonlinear, or singular information absent from
diagonal charge weights and dilation covariance.
-/

namespace RHTower

noncomputable section

/-- Real values of the source-first FZZ parity Mellin transform are exactly the Fermi Mellin
normalizer. -/
theorem fzzCigarParityMellin_ofReal_eq_fermiMellinNormalizer (sigma : ℝ) :
    fzzCigarParityMellin (sigma : ℂ) =
      ((fermiMellinNormalizer sigma : ℝ) : ℂ) := by
  rw [fzzCigarParityMellin_eq_salemFermiMellin]
  exact (ofReal_fermiMellinNormalizer sigma).symm

/-- At every positive real Mellin grade, the actual FZZ parity source has strictly positive mass. -/
theorem fzzCigarParityMellin_ofReal_pos
    {sigma : ℝ} (hsigma : 0 < sigma) :
    ∃ Z : ℝ, 0 < Z ∧
      fzzCigarParityMellin (sigma : ℂ) = (Z : ℂ) := by
  exact ⟨fermiMellinNormalizer sigma, fermiMellinNormalizer_pos hsigma,
    fzzCigarParityMellin_ofReal_eq_fermiMellinNormalizer sigma⟩

/-- Exact diagonal data visible to graded KMS/passivity at inverse temperature `beta`. -/
def FZZCigarParityDiagonalSuperKMSAdmissible (beta : ℝ) : Prop :=
  Summable (bornSupertraceTerm beta) ∧
    (∃ Z : ℝ, 0 < Z ∧
      fzzCigarParityMellin (((beta / 2 : ℝ) : ℂ)) = (Z : ℂ)) ∧
    ∀ k : ℕ, 0 < k →
      ∑' n : ℕ, dilatedBornSupertraceTerm k beta n =
        (k : ℝ) ^ (-(beta / 2)) * bornSupertrace beta

/-- Every positive inverse temperature is admitted by the exact diagonal FZZ super-KMS data. -/
theorem fzzCigarParityDiagonalSuperKMSAdmissible_of_pos
    {beta : ℝ} (hbeta : 0 < beta) :
    FZZCigarParityDiagonalSuperKMSAdmissible beta := by
  refine ⟨summable_bornSupertraceTerm hbeta, ?_, ?_⟩
  · exact fzzCigarParityMellin_ofReal_pos (by linarith : 0 < beta / 2)
  · intro k hk
    exact tsum_dilatedBornSupertraceTerm hk beta

/-- Diagonal FZZ super-KMS admissibility would select the critical temperature if every admitted
positive inverse temperature were forced to equal `1`. -/
def FZZCigarParityDiagonalSuperKMSSelectsCritical : Prop :=
  ∀ beta : ℝ, 0 < beta → FZZCigarParityDiagonalSuperKMSAdmissible beta → beta = 1

theorem exists_fzzCigarParityDiagonalSuperKMSAdmissible_ne_one :
    ∃ beta : ℝ, beta ≠ 1 ∧ FZZCigarParityDiagonalSuperKMSAdmissible beta := by
  refine ⟨2, by norm_num, ?_⟩
  exact fzzCigarParityDiagonalSuperKMSAdmissible_of_pos (by norm_num)

/-- **Diagonal super-KMS orientation no-go.** Exact positivity, graded summability, and all-dilation
covariance of the literal FZZ parity source do not select the critical inverse temperature. -/
theorem not_fzzCigarParityDiagonalSuperKMSSelectsCritical :
    ¬ FZZCigarParityDiagonalSuperKMSSelectsCritical := by
  intro hselect
  have hadmissible : FZZCigarParityDiagonalSuperKMSAdmissible 2 :=
    fzzCigarParityDiagonalSuperKMSAdmissible_of_pos (by norm_num)
  have htwo := hselect 2 (by norm_num) hadmissible
  norm_num at htwo

end

end RHTower
