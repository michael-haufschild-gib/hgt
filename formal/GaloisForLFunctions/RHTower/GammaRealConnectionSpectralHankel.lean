import GaloisForLFunctions.HTGeometry.GammaBoseSpectralHankel
import GaloisForLFunctions.RHTower.ArchimedeanGamma
import GaloisForLFunctions.RHTower.XiCollapseDirichletLeg

/-!
# The central archimedean Gamma connection as a positive quarter-shift spectral clock

The Deligne real-Gamma logarithmic connection is

`Omega_infty(s) = -log(pi)/2 + digamma(s/2)/2`.

At the functional-equation center `s=1/2`, every positive-order connection derivative is therefore
an explicit scalar multiple of the quarter-shift polygamma value.  Removing its chain-rule,
alternating, and factorial factors gives exactly the positive infinite-support moment sequence

`sum_j (j+1/4)^(-m-2)`.

This is a source-level archimedean value relation inside RHTower.  It isolates a positive spectral
component of the completed prime--Gamma connection without claiming that the coupled prime
residual is positive.
-/

namespace RHTower

noncomputable section

/-- Positive-order derivatives of the real-Gamma logarithmic connection reduce to half-argument
polygamma derivatives with the exact chain-rule factor. -/
theorem iteratedDeriv_gammaRealLogConnection_succ (m : ℕ) (s : ℂ)
    (hs : ∀ p : ℕ, s / 2 ≠ -(p : ℂ)) :
    iteratedDeriv (m + 1) GaloisForLFunctions.gammaRealLogConnection s =
      (1 / 2 : ℂ) ^ (m + 2) *
        iteratedDeriv (m + 1) Complex.digamma (s / 2) := by
  unfold GaloisForLFunctions.gammaRealLogConnection
  rw [iteratedDeriv_const_add (by omega)]
  rw [iteratedDeriv_div_const]
  rw [iteratedDeriv_half_digamma (m + 1) s hs]
  rw [show m + 2 = (m + 1) + 1 by omega, pow_succ]
  ring

/-- At `s=1/2`, the archimedean connection jet is exactly the quarter-shift positive spectral
moment, with all chain-rule and polygamma factors displayed. -/
theorem iteratedDeriv_gammaRealLogConnection_half_eq_quarterMoment (m : ℕ) :
    iteratedDeriv (m + 1) GaloisForLFunctions.gammaRealLogConnection (1 / 2 : ℂ) =
      (1 / 2 : ℂ) ^ (m + 2) *
        ((-1 : ℂ) ^ (m + 2) * ((m + 1).factorial : ℂ) *
          (HTGeometry.gammaBoseMoment (1 / 4) m : ℂ)) := by
  rw [iteratedDeriv_gammaRealLogConnection_succ m (1 / 2 : ℂ) (by
    intro p hp
    have hre := congrArg Complex.re hp
    norm_num [Complex.div_re] at hre
    have hpnonneg : (0 : ℝ) ≤ p := Nat.cast_nonneg p
    linarith)]
  have hquarter : (1 / 2 : ℂ) / 2 = ((1 / 4 : ℝ) : ℂ) := by
    norm_num
  rw [hquarter]
  rw [HTGeometry.iteratedDeriv_digamma_eq_gammaBoseMoment (by norm_num) m]

/-- The central real-Gamma connection jet after removing the half-argument, sign, and factorial
scales. -/
def normalizedGammaRealConnectionJet (m : ℕ) : ℝ :=
  (((2 : ℂ) ^ (m + 2) * (-1 : ℂ) ^ (m + 2) *
      iteratedDeriv (m + 1) GaloisForLFunctions.gammaRealLogConnection (1 / 2 : ℂ)) /
    ((m + 1).factorial : ℂ)).re

/-- The normalized central archimedean connection jet is exactly the quarter-shift positive
spectral moment clock. -/
theorem normalizedGammaRealConnectionJet_eq_quarterMoment (m : ℕ) :
    normalizedGammaRealConnectionJet m =
      HTGeometry.gammaBoseMoment (1 / 4) m := by
  rw [normalizedGammaRealConnectionJet,
    iteratedDeriv_gammaRealLogConnection_half_eq_quarterMoment]
  have hfac : ((m + 1).factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (m + 1)
  field_simp
  have htwo : (2 : ℂ) ^ (m + 2) * (1 / 2 : ℂ) ^ (m + 2) = 1 := by
    rw [← mul_pow]
    norm_num
  have hsign : ((-1 : ℂ) ^ (m + 2)) ^ 2 = 1 := by
    rw [← pow_mul]
    norm_num
  rw [hsign]
  simp only [mul_one]
  rw [htwo]
  simp

/-- Every finite Hankel block of the normalized central Gamma-connection jet is positive
definite. -/
theorem normalizedGammaRealConnectionJet_hankel_posDef (n : ℕ) :
    (HTGeometry.momentHankelMatrix normalizedGammaRealConnectionJet n).PosDef := by
  have hseq : normalizedGammaRealConnectionJet =
      HTGeometry.gammaBoseMoment (1 / 4) := by
    funext m
    exact normalizedGammaRealConnectionJet_eq_quarterMoment m
  rw [hseq]
  exact HTGeometry.gammaBoseHankel_posDef (by norm_num) n

/-- Every finite Hankel determinant of the normalized central Gamma-connection jet is strictly
positive. -/
theorem det_normalizedGammaRealConnectionJet_hankel_pos (n : ℕ) :
    0 < (HTGeometry.momentHankelMatrix normalizedGammaRealConnectionJet n).det :=
  (normalizedGammaRealConnectionJet_hankel_posDef n).det_pos

/-- No fixed finite spectral width can reproduce arbitrarily long central Gamma-connection jet
windows. -/
theorem normalizedGammaRealConnectionJet_not_fixedSpectralWidthLocalClosure (d : ℕ) :
    ¬ HTGeometry.FixedSpectralWidthLocalClosure d normalizedGammaRealConnectionJet := by
  apply HTGeometry.not_fixedSpectralWidthLocalClosure_of_det_ne_zero
  exact ne_of_gt (det_normalizedGammaRealConnectionJet_hankel_pos (d + 1))

/-- No fixed-dimensional linear hidden-state model can reproduce arbitrarily long central
Gamma-connection jet windows. -/
theorem normalizedGammaRealConnectionJet_not_fixedStateSpaceDimensionLocalClosure (d : ℕ) :
    ¬ HTGeometry.FixedStateSpaceDimensionLocalClosure d normalizedGammaRealConnectionJet := by
  apply HTGeometry.not_fixedStateSpaceDimensionLocalClosure_of_det_ne_zero
  exact ne_of_gt (det_normalizedGammaRealConnectionJet_hankel_pos (d + 1))

/-- The normalized central Gamma-connection jet satisfies no positive-order real linear
recurrence. -/
theorem normalizedGammaRealConnectionJet_not_linearRecurrence
    (E : LinearRecurrence ℝ) (horder : E.order ≠ 0) :
    ¬ E.IsSolution normalizedGammaRealConnectionJet := by
  intro hsolution
  have hzero := HTGeometry.det_algebraicHankelMatrix_succ_eq_zero_of_linearRecurrence
    E hsolution horder
  exact (ne_of_gt
    (det_normalizedGammaRealConnectionJet_hankel_pos (E.order + 1))) (by
      simpa [HTGeometry.algebraicHankelMatrix, HTGeometry.momentHankelMatrix] using! hzero)

end

end RHTower
