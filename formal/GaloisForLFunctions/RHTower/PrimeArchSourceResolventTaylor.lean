import GaloisForLFunctions.RHTower.PrimeArchBernsteinMobiusPullbackSource
import GaloisForLFunctions.RHTower.PrimeArchThetaAllOrderCumulant
import GaloisForLFunctions.HTGeometry.HilbertSchmidtFourthJet

/-!
# Taylor data of the Euler-deleted prime--archimedean source

The exact source identity
`continuedPrimeArchSourceRelativeTrace z = -z * normalizedPrimeArchMomentGerm z`
turns the all-order theta-cusp formula for `z * normalizedPrimeArchMomentGerm` into
the odd Taylor coefficients of the Euler-deleted source.  This is the source half of
the K-RVM reflected-resolvent comparison: degree `2n+1` carries precisely the moment
`-normalizedPrimeArchMoment n`.
-/

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

/-- Every odd Taylor coefficient of the Euler-deleted prime--archimedean source is
the negative matching normalized moment. -/
theorem taylorCoeff_continuedPrimeArchSourceRelativeTrace_odd (n : ℕ) :
    taylorCoeff continuedPrimeArchSourceRelativeTrace (2 * n + 1) =
      -(normalizedPrimeArchMoment n : ℂ) := by
  have hsourcefun : continuedPrimeArchSourceRelativeTrace =
      fun z : ℂ => -(z * normalizedPrimeArchMomentGerm z) := by
    funext z
    rw [continuedPrimeArchSourceRelativeTrace_eq]
    ring
  rw [taylorCoeff, hsourcefun]
  change ((Nat.factorial (2 * n + 1) : ℂ)⁻¹) *
      iteratedDeriv (2 * n + 1)
        (-(fun z : ℂ => z * normalizedPrimeArchMomentGerm z)) 0 =
      -(normalizedPrimeArchMoment n : ℂ)
  rw [iteratedDeriv_neg,
    iteratedDeriv_id_mul_normalizedPrimeArchMomentGerm_zero]
  have hodd : Odd (2 * n + 1) := ⟨n, by omega⟩
  have hindex : (2 * n + 1 - 1) / 2 = n := by omega
  rw [thetaCuspPrimeArchProductJet, if_pos hodd, hindex]
  have hfac : (((2 * n + 1).factorial : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (2 * n + 1)
  field_simp [hfac]

end

end RHTower
