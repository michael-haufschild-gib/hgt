import GaloisForLFunctions.RHTower.FZZCigarParityExternalBRSTReverseNeutralIntegral

/-!
# FZZ external-BRST neutral branch symmetrization no-go

The two cyclic chambers of a neutral pair of literal external-BRST branch
factors carry equal and opposite compact currents. Any unoriented sum over
both chambers is exactly zero. A surviving FZZ-P branch source therefore
requires a physical branch-sheet or chamber-selection law.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- **Unordered-neutral branch-pair route kill.** Summing both cyclic
chambers cancels the literal compact current exactly. -/
theorem fzzCigarExternalBRSTNeutralAngularSymmetrization_eq_zero
    (k : ℝ) (j : ℂ) (p ν : ℤ) (hp : p ≠ 0) :
    fzzCigarExternalBRSTOrderedNeutralAngularIntegral k j p ν +
      fzzCigarExternalBRSTReverseNeutralAngularIntegral k j p ν = 0 := by
  rw [fzzCigarExternalBRSTOrderedNeutralAngularIntegral_eq_inv_frequency k j p ν hp,
    fzzCigarExternalBRSTReverseNeutralAngularIntegral_eq_neg_inv_frequency k j p ν hp]
  ring

end

end GaloisForLFunctions.RHTower
