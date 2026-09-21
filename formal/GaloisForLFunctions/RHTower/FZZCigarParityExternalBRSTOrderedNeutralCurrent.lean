import GaloisForLFunctions.RHTower.FZZCigarParityExternalBRSTOrderedNeutralIntegral

/-!
# FZZ external-BRST cyclic ordered neutral current

The exact cyclically ordered neutral branch coefficient is non-real at every
nonzero compact charge. Thus literal branch ordering supplies an
anti-Hermitian compact current which same-angle neutralization removes.

Proof-chain role:
`ordered W+W- branch kernel -> non-real compact source coefficient ->
ordered cross-depth Ward current -> FZZ-P`. It remains to derive this cyclic
order from the complete torus worldsheet functional and couple it to the
all-depth mixed Ward source.
-/

open Complex

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- The literal ordered neutral branch coefficient has nonzero imaginary part
at every nonzero compact charge. -/
theorem fzzCigarExternalBRSTOrderedNeutralAngularIntegral_im_ne_zero
    (k : ℝ) (j : ℂ) (p ν : ℤ) (hp : p ≠ 0) :
    (fzzCigarExternalBRSTOrderedNeutralAngularIntegral k j p ν).im ≠ 0 := by
  rw [fzzCigarExternalBRSTOrderedNeutralAngularIntegral_eq_inv_frequency k j p ν hp]
  let c : ℂ := fzzCigarExternalBRSTAngularFrequency p
  change (c⁻¹).im ≠ 0
  intro him
  have hc : c ≠ 0 := by
    dsimp only [c]
    unfold fzzCigarExternalBRSTAngularFrequency
    apply mul_ne_zero
    · exact Complex.ofReal_ne_zero.mpr
        (mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) (by exact_mod_cast hp))
    · exact Complex.I_ne_zero
  have hprod : c * c⁻¹ = 1 := mul_inv_cancel₀ hc
  have hre := congrArg Complex.re hprod
  change c.re * (c⁻¹).re - c.im * (c⁻¹).im = 1 at hre
  have hcRe : c.re = 0 := by
    dsimp only [c]
    simp [fzzCigarExternalBRSTAngularFrequency]
  rw [hcRe, him] at hre
  norm_num at hre

end

end GaloisForLFunctions.RHTower
