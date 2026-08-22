import GaloisForLFunctions.HTGeometry.AbeExponentialDampingJetPolynomial
import GaloisForLFunctions.HTGeometry.QuasiAbelianPoincareSeries

/-!
# Exact all-order expansion of a damped Poincaré summand

For a literal Poincaré summand, damping its seed by Abe's multiplier is exactly the same as
damping the undamped summand by the translated profile.  Thus every directional jet is one
translated exponential multiplier times a finite source-valued polynomial in the damping time.
This is a summand-level identity only: normal summation of its coefficient sources remains a
separate analytic obligation.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Translation commutes exactly with Abe's exponential multiplier, while translating its profile.
-/
theorem multivariateEntireTranslate_abeExponentialDampingMultiplier {d : ℕ} (t : ℂ)
    (Θ : MultivariateEntire d) (γ : Fin d → ℂ) :
    multivariateEntireTranslate (abeExponentialDampingMultiplier t Θ) γ =
      abeExponentialDampingMultiplier t (multivariateEntireTranslate Θ γ) := by
  ext x
  rw [multivariateEntireTranslate_apply, abeExponentialDampingMultiplier_apply,
    abeExponentialDampingMultiplier_apply, multivariateEntireTranslate_apply]

/-- Damping a seed before periodization is exactly damping the associated Poincaré summand by the
translated profile. -/
theorem poincareTermEntire_abeExponentialDampingSeed_eq {d : ℕ}
    {Γ : AddSubgroup (Fin d → ℂ)} (ψ : AutomorphicFactor d Γ)
    (Θ seed : MultivariateEntire d) (t : ℂ) (γ : Γ) :
    poincareTermEntire ψ (abeExponentialDampingMultiplier t Θ * seed) γ =
      abeExponentialDampingMultiplier t (multivariateEntireTranslate Θ γ.1) *
        poincareTermEntire ψ seed γ := by
  ext x
  change ((ψ.factor γ).1 x)⁻¹ *
      ((abeExponentialDampingMultiplier t Θ * seed).1 (x + γ.1)) =
    (abeExponentialDampingMultiplier t (multivariateEntireTranslate Θ γ.1)).1 x *
      (poincareTermEntire ψ seed γ).1 x
  rw [multivariateEntire_mul_apply, abeExponentialDampingMultiplier_apply,
    abeExponentialDampingMultiplier_apply]
  change ((ψ.factor γ).1 x)⁻¹ *
      (Complex.exp (t * (Θ.1 (x + γ.1) - 1)) * seed.1 (x + γ.1)) =
    Complex.exp (t * ((multivariateEntireTranslate Θ γ.1).1 x - 1)) *
      (((ψ.factor γ).1 x)⁻¹ * seed.1 (x + γ.1))
  rw [multivariateEntireTranslate_apply]
  ring

/-- Every directional jet of a literally damped Poincaré summand is the translated multiplier
times its exact finite recursive source factor. -/
theorem iteratedPartialDerivEntire_poincareTermEntire_abeExponentialDampingSeed {d : ℕ}
    {Γ : AddSubgroup (Fin d → ℂ)} (ψ : AutomorphicFactor d Γ) (v : Fin d → ℂ)
    (Θ seed : MultivariateEntire d) (t : ℂ) (γ : Γ) (n : ℕ) :
    iteratedPartialDerivEntire v n
      (poincareTermEntire ψ (abeExponentialDampingMultiplier t Θ * seed) γ) =
      abeExponentialDampingMultiplier t (multivariateEntireTranslate Θ γ.1) *
        abeExponentialDampingSeedJetFactor v t (multivariateEntireTranslate Θ γ.1)
          (poincareTermEntire ψ seed γ) n := by
  rw [poincareTermEntire_abeExponentialDampingSeed_eq]
  exact iteratedPartialDerivEntire_abeExponentialDampingMultiplier_mul v t
    (multivariateEntireTranslate Θ γ.1) (poincareTermEntire ψ seed γ) n

/-- The source factor in a damped Poincaré-summand jet is a finite polynomial in the damping
time. -/
theorem hasFiniteDampingPolynomial_poincareTermEntire_abeExponentialDampingSeedJetFactor
    {d : ℕ} {Γ : AddSubgroup (Fin d → ℂ)} (ψ : AutomorphicFactor d Γ)
    (v : Fin d → ℂ) (Θ seed : MultivariateEntire d) (γ : Γ) (n : ℕ) :
    HasFiniteDampingPolynomial (fun t ↦
      abeExponentialDampingSeedJetFactor v t (multivariateEntireTranslate Θ γ.1)
        (poincareTermEntire ψ seed γ) n) :=
  hasFiniteDampingPolynomial_abeExponentialDampingSeedJetFactor v
    (multivariateEntireTranslate Θ γ.1) (poincareTermEntire ψ seed γ) n

end

end GaloisForLFunctions.HTGeometry
