import GaloisForLFunctions.RHTower.GammaConductorSchurStrictDefiniteness

/-!
# Gaussian heat diagonal cannot be the Gamma-conductor Schur residual

For the unfiltered Gaussian heat probe, the one-frequency projective minor has the exact profile

`pi * (t - xi^(2 : ℕ)) / (2 * t^(4 : ℕ)) * exp (-xi^(2 : ℕ) / (2*t))`.

It is strictly negative beyond the parabolic aperture `xi^(2 : ℕ) = t`.  The Gamma-conductor Schur
residual is strictly positive on every positive diagonal frequency.  Hence no real diagonal
congruence can identify these two kernels.  Any viable completion must retain mixed polar--Gamma
and cross-prime covariance terms.
-/

namespace RHTower

noncomputable section

/-- Exact one-prime diagonal projective curvature of the unfiltered Gaussian heat probe. -/
def gaussianHeatPrimeDiagonalCurvature (t ξ : ℝ) : ℝ :=
  Real.pi * (t - ξ ^ (2 : ℕ)) / (2 * t ^ (4 : ℕ)) * Real.exp (-ξ ^ (2 : ℕ) / (2 * t))

/-- The Gaussian one-prime curvature is negative outside its parabolic aperture. -/
theorem gaussianHeatPrimeDiagonalCurvature_neg
    {t ξ : ℝ} (ht : 0 < t) (haperture : t < ξ ^ (2 : ℕ)) :
    gaussianHeatPrimeDiagonalCurvature t ξ < 0 := by
  have hnum : Real.pi * (t - ξ ^ (2 : ℕ)) < 0 :=
    mul_neg_of_pos_of_neg Real.pi_pos (sub_neg.mpr haperture)
  have hden : 0 < 2 * t ^ (4 : ℕ) := by positivity
  have hquot : Real.pi * (t - ξ ^ (2 : ℕ)) / (2 * t ^ (4 : ℕ)) < 0 :=
    div_neg_of_neg_of_pos hnum hden
  exact mul_neg_of_neg_of_pos hquot (Real.exp_pos _)

/-- **Signature obstruction.** Beyond the Gaussian aperture, no real diagonal rescaling can turn
the strictly positive Gamma-conductor Schur diagonal into the Gaussian heat curvature. -/
theorem gaussianHeatPrimeDiagonalCurvature_ne_sq_mul_gammaConductorResidual
    {t ξ : ℝ} (ht : 0 < t) (hξ : 0 < ξ) (haperture : t < ξ ^ (2 : ℕ)) (a : ℝ) :
    gaussianHeatPrimeDiagonalCurvature t ξ ≠
      a ^ (2 : ℕ) * gammaConductorModeSchurResidual ξ ξ := by
  have hgauss := gaussianHeatPrimeDiagonalCurvature_neg ht haperture
  have hgamma := gammaConductorModeSchurResidual_pos hξ hξ
  have hnonneg : 0 ≤ a ^ (2 : ℕ) * gammaConductorModeSchurResidual ξ ξ :=
    mul_nonneg (sq_nonneg a) hgamma.le
  linarith

/-- Existential form: a direct diagonal-congruence identification is impossible. -/
theorem not_exists_gaussianHeatPrimeDiagonalCurvature_eq_sq_mul_gammaConductorResidual
    {t ξ : ℝ} (ht : 0 < t) (hξ : 0 < ξ) (haperture : t < ξ ^ (2 : ℕ)) :
    ¬ ∃ a : ℝ,
      gaussianHeatPrimeDiagonalCurvature t ξ =
        a ^ (2 : ℕ) * gammaConductorModeSchurResidual ξ ξ := by
  rintro ⟨a, ha⟩
  exact gaussianHeatPrimeDiagonalCurvature_ne_sq_mul_gammaConductorResidual
    ht hξ haperture a ha

end

end RHTower
