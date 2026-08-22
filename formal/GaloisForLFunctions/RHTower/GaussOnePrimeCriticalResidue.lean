import GaloisForLFunctions.RHTower.GaussDiagonalLogResidue

/-!
# One-prime Gauss critical residue

This module records the depth-one specialization of the Gauss-channel residue in the literal
form used by the one-prime quasi-inner card.  The operator result here concerns the explicit
critical diagonal realization.  The separate identification of that realization with the full
Connes--Consani defect remains an obligation of the card.
-/

namespace RHTower

open GaloisForLFunctions.RHTower

noncomputable section

/-- The depth-one Gauss-channel residue in its literal one-prime form. -/
theorem gaussChannelResidue_one (p : Nat.Primes) :
    gaussChannelResidue 1 p =
      2 * ((p : ℝ) - 1) ^ 4 / ((p : ℝ) ^ 2 * Real.log (p : ℝ)) := by
  norm_num [gaussChannelResidue]
  ring

/-- The explicit one-prime critical realization lies in the weak trace ideal. -/
theorem memWeakSchattenClass_gaussOnePrimeCriticalPowerOperator (p : Nat.Primes) :
    MemWeakSchattenClass 1 (gaussComponentCriticalPowerOperator (le_refl 1) p) :=
  memWeakSchattenClass_gaussComponentCriticalPowerOperator (le_refl 1) p

/-- The explicit one-prime critical realization has the literal arithmetic logarithmic residue. -/
theorem hasSchattenLogResidue_gaussOnePrimeCriticalPowerOperator (p : Nat.Primes) :
    HasSchattenLogResidue 1 (gaussComponentCriticalPowerOperator (le_refl 1) p)
      (2 * ((p : ℝ) - 1) ^ 4 / ((p : ℝ) ^ 2 * Real.log (p : ℝ))) := by
  rw [← gaussChannelResidue_one]
  exact hasSchattenLogResidue_gaussComponentCriticalPowerOperator (le_refl 1) p

end

end RHTower
