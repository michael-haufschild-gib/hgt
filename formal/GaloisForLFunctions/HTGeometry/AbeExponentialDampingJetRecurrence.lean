import GaloisForLFunctions.HTGeometry.AbeExponentialDampingMultiplier

/-!
# All-order directional jets of Abe's exponential multiplier

Repeated differentiation of `exp (t * (Θ - 1))` has a finite polynomial dependence on the
damping time `t`.  This file records the exact recursive factorization inside the entire-source
algebra.  It is the algebraic half of the finite polynomial-exponential expansion required for the
graded Poincare argument; no growth or summability input is assumed here.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Repeated differentiation of an entire source in one fixed complex direction. -/
def iteratedPartialDerivEntire {d : ℕ} (v : Fin d → ℂ) :
    ℕ → MultivariateEntire d → MultivariateEntire d
  | 0, g => g
  | n + 1, g => partialDerivEntire v (iteratedPartialDerivEntire v n g)

/-- The finite recursive factor left after repeatedly differentiating Abe's multiplier.  Its
recurrence is polynomial in `t`: differentiation only affects previous coefficients, while the
new first term contributes one factor of `t`. -/
def abeExponentialDampingJetFactor {d : ℕ} (v : Fin d → ℂ) (t : ℂ)
    (Θ : MultivariateEntire d) : ℕ → MultivariateEntire d
  | 0 => 1
  | n + 1 =>
      (t • partialDerivEntire v Θ) * abeExponentialDampingJetFactor v t Θ n +
        partialDerivEntire v (abeExponentialDampingJetFactor v t Θ n)

/-- Source-level form of the first directional derivative identity. -/
theorem partialDerivEntire_abeExponentialDampingMultiplier_eq {d : ℕ} (v : Fin d → ℂ)
    (t : ℂ) (Θ : MultivariateEntire d) :
    partialDerivEntire v (abeExponentialDampingMultiplier t Θ) =
      abeExponentialDampingMultiplier t Θ * (t • partialDerivEntire v Θ) := by
  ext x
  rw [multivariateEntire_mul_apply]
  change (partialDerivEntire v (abeExponentialDampingMultiplier t Θ)).1 x =
    (abeExponentialDampingMultiplier t Θ).1 x * (t * (partialDerivEntire v Θ).1 x)
  exact partialDerivEntire_abeExponentialDampingMultiplier v t Θ x

/-- Every repeated directional derivative of Abe's multiplier is the multiplier times its finite
jet factor. -/
theorem iteratedPartialDerivEntire_abeExponentialDampingMultiplier {d : ℕ}
    (v : Fin d → ℂ) (t : ℂ) (Θ : MultivariateEntire d) (n : ℕ) :
    iteratedPartialDerivEntire v n (abeExponentialDampingMultiplier t Θ) =
      abeExponentialDampingMultiplier t Θ * abeExponentialDampingJetFactor v t Θ n := by
  induction n with
  | zero =>
      simp only [iteratedPartialDerivEntire, abeExponentialDampingJetFactor, mul_one]
  | succ n ih =>
      rw [iteratedPartialDerivEntire, ih, partialDerivEntire_mul,
        partialDerivEntire_abeExponentialDampingMultiplier_eq, abeExponentialDampingJetFactor]
      ext x
      change
        ((abeExponentialDampingMultiplier t Θ).1 x * (t * (partialDerivEntire v Θ).1 x)) *
            (abeExponentialDampingJetFactor v t Θ n).1 x +
          (abeExponentialDampingMultiplier t Θ).1 x *
            (partialDerivEntire v (abeExponentialDampingJetFactor v t Θ n)).1 x =
          (abeExponentialDampingMultiplier t Θ).1 x *
            ((t * (partialDerivEntire v Θ).1 x) *
              (abeExponentialDampingJetFactor v t Θ n).1 x +
              (partialDerivEntire v (abeExponentialDampingJetFactor v t Θ n)).1 x)
      ring

/-- The finite factor left after repeatedly differentiating an Abe-damped seed. -/
def abeExponentialDampingSeedJetFactor {d : ℕ} (v : Fin d → ℂ) (t : ℂ)
    (Θ seed : MultivariateEntire d) : ℕ → MultivariateEntire d
  | 0 => seed
  | n + 1 =>
      (t • partialDerivEntire v Θ) * abeExponentialDampingSeedJetFactor v t Θ seed n +
        partialDerivEntire v (abeExponentialDampingSeedJetFactor v t Θ seed n)

/-- Every repeated directional derivative of an Abe-damped seed is the multiplier times its finite
seed-jet factor. -/
theorem iteratedPartialDerivEntire_abeExponentialDampingMultiplier_mul {d : ℕ}
    (v : Fin d → ℂ) (t : ℂ) (Θ seed : MultivariateEntire d) (n : ℕ) :
    iteratedPartialDerivEntire v n (abeExponentialDampingMultiplier t Θ * seed) =
      abeExponentialDampingMultiplier t Θ * abeExponentialDampingSeedJetFactor v t Θ seed n := by
  induction n with
  | zero =>
      simp only [iteratedPartialDerivEntire, abeExponentialDampingSeedJetFactor]
  | succ n ih =>
      rw [iteratedPartialDerivEntire, ih, partialDerivEntire_mul,
        partialDerivEntire_abeExponentialDampingMultiplier_eq,
        abeExponentialDampingSeedJetFactor]
      ext x
      change
        ((abeExponentialDampingMultiplier t Θ).1 x * (t * (partialDerivEntire v Θ).1 x)) *
            (abeExponentialDampingSeedJetFactor v t Θ seed n).1 x +
          (abeExponentialDampingMultiplier t Θ).1 x *
            (partialDerivEntire v (abeExponentialDampingSeedJetFactor v t Θ seed n)).1 x =
          (abeExponentialDampingMultiplier t Θ).1 x *
            ((t * (partialDerivEntire v Θ).1 x) *
              (abeExponentialDampingSeedJetFactor v t Θ seed n).1 x +
              (partialDerivEntire v (abeExponentialDampingSeedJetFactor v t Θ seed n)).1 x)
      ring

end

end GaloisForLFunctions.HTGeometry
