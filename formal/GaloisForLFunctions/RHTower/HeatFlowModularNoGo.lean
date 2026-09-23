import GaloisForLFunctions.RHTower.BornTemperatureFactorType

/-!
# Heat flow is not modular flow

Tomita modular time acts by algebra automorphisms.  The de Bruijn--Newman deformation is a heat
flow and already fails multiplicativity on the quadratic polynomial sector at every nonzero time.
Thus Born inverse temperature, modular time, and heat time cannot literally be one clock.
-/

namespace RHTower

noncomputable section

open Polynomial

/-- The exact heat operator `exp(t * D²)` on the polynomial sector of degree at most two.  On that
sector the exponential truncates after its linear term. -/
def quadraticPolynomialHeat (t : ℂ) (P : Polynomial ℂ) : Polynomial ℂ :=
  P + C t * derivative (derivative P)

@[simp]
theorem quadraticPolynomialHeat_X (t : ℂ) : quadraticPolynomialHeat t X = X := by
  simp [quadraticPolynomialHeat]

@[simp]
theorem quadraticPolynomialHeat_X_sq (t : ℂ) :
    quadraticPolynomialHeat t (X ^ (2 : ℕ)) = X ^ (2 : ℕ) + C t * 2 := by
  simp [quadraticPolynomialHeat]
  norm_num

/-- **Heat/modular no-go.** At nonzero time the quadratic heat operator is not multiplicative,
whereas every modular automorphism is.  The failure is the carré-du-champ cross term `2t`. -/
theorem quadraticPolynomialHeat_not_multiplicative {t : ℂ} (ht : t ≠ 0) :
    quadraticPolynomialHeat t (X * X) ≠
      quadraticPolynomialHeat t X * quadraticPolynomialHeat t X := by
  rw [show X * X = X ^ (2 : ℕ) by ring, quadraticPolynomialHeat_X_sq,
    quadraticPolynomialHeat_X]
  intro h
  have hcoeff := congrArg (fun P : Polynomial ℂ => P.coeff 0) h
  simp at hcoeff
  exact ht hcoeff

/-- If the quadratic heat operator is multiplicative even on the single test `X * X`, its time is
zero.  This is the positive rigidity statement left by the no-go. -/
theorem quadraticPolynomialHeat_mul_X_eq_iff (t : ℂ) :
    quadraticPolynomialHeat t (X * X) =
      quadraticPolynomialHeat t X * quadraticPolynomialHeat t X ↔ t = 0 := by
  constructor
  · contrapose!
    exact quadraticPolynomialHeat_not_multiplicative
  · rintro rfl
    simp [quadraticPolynomialHeat]

end
end RHTower
