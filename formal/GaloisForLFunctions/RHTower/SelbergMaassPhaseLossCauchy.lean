import GaloisForLFunctions.RHTower.SelbergMaassPhaseStress

/-!
# Sharp Cauchy bound for the original mixed phase loss

The unresolved top-boundary term is the real polarization of the positive
inversion-loss quadratic form.  This file proves its sharp Cauchy--Schwarz
bound directly from the proved nonnegative transfer loss, without replacing
that term by an unrelated trace average.
-/

open Complex
namespace GaloisForLFunctions.RHTower.SelbergMaassPhaseStress

open SelbergMaassCongruenceTrace SelbergMaassMixedLoss SelbergMaassCharacterSeamFlux
open GaloisForLFunctions.HTGeometry

noncomputable section

variable (N : ℕ) (r s : ZMod (N + 1))

private theorem lossEnergy_real_smul (t : ℝ) (v : EuclideanSpace ℂ (Deck N)) :
    lossEnergy N r s ((t : ℂ) • v) = t ^ (2 : ℕ) * lossEnergy N r s v := by
  simp only [lossEnergy, map_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow,
    sq_abs]
  ring

private theorem lossPair_real_smul_right (t : ℝ) (v w : EuclideanSpace ℂ (Deck N)) :
    lossPair N r s v ((t : ℂ) • w) = t * lossPair N r s v w := by
  simp only [lossPair, map_smul, inner_smul_right, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  ring

/-- The physical mixed loss is bounded sharply by its two diagonal inversion losses. -/
theorem lossPair_sq_le_lossEnergy_mul (v w : EuclideanSpace ℂ (Deck N)) :
    lossPair N r s v w ^ (2 : ℕ) ≤ lossEnergy N r s v * lossEnergy N r s w := by
  have hquad (t : ℝ) : 0 ≤ lossEnergy N r s v +
      2 * (-lossPair N r s v w) * t + lossEnergy N r s w * t ^ (2 : ℕ) := by
    have h := lossEnergy_nonneg N r s (v + ((-t : ℝ) : ℂ) • w)
    rw [lossEnergy_add, lossEnergy_real_smul, lossPair_real_smul_right] at h
    nlinarith
  have h := sq_le_mul_of_quadratic_nonneg (lossEnergy_nonneg N r s w) hquad
  rw [neg_sq] at h
  nlinarith

variable {lam : ℝ}
  (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)

/-- Sharp pointwise control of the exact mixed phase stress by the two source derivative losses. -/
theorem phaseStressXY_sq_le_derivative_losses (z : UpperHalfPlane) :
    phaseStressXY N r s f (z : ℂ) ^ (2 : ℕ) ≤
      4 * lossEnergy N r s (sourceDerivative N f 1 z) *
        lossEnergy N r s (sourceDerivative N f Complex.I z) := by
  rw [phaseStressXY_eq]
  nlinarith [lossPair_sq_le_lossEnergy_mul N r s
    (sourceDerivative N f 1 z) (sourceDerivative N f Complex.I z)]

end
end GaloisForLFunctions.RHTower.SelbergMaassPhaseStress
