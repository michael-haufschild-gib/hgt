import GaloisForLFunctions.RHTower.XiMassBesselStateClosure

/-!
# The coefficient ring of the height states

The coefficients produced by iterating the Bessel height system all lie in

`{ (P(w) + Q(w)·Z(w)) / R(w)^j : P, Q ∈ ℂ[X], j ∈ ℕ }`,  `R(w) = τ² + w²`,  `Z² = R`,

and this ring is closed under `∂_w`: since `Z′ = w/Z = wZ/R`,

`∂_w (P + Q·Z)/R^j = ( (P′R − 2jwP) + (Q′R + (1−2j)wQ)·Z ) / R^{j+1}`.

The derivative is therefore a *polynomial* operation on the coefficient data, with no analytic side
condition beyond `Re R > 0`.  That is what makes the caustic-null jet hierarchy an induction rather
than an asymptotic expansion: each application of `4a⁴ − ∂_w²` is a fixed polynomial map on
`(P, Q, j)`.
-/

open Complex Polynomial

namespace RHTower

noncomputable section

/-- The propagation polynomial `R(w) = τ² + w²`. -/
def xiMassRadiusPoly (τ : ℂ) : Polynomial ℂ := Polynomial.C (τ ^ (2 : ℕ)) + Polynomial.X ^ (2 : ℕ)

theorem xiMassRadiusPoly_eval (τ w : ℂ) : (xiMassRadiusPoly τ).eval w = τ ^ (2 : ℕ) + w ^ (2 : ℕ) := by
  simp [xiMassRadiusPoly]

theorem xiMassHeightRadius_sq {τ w : ℂ} (hw : 0 < (τ ^ (2 : ℕ) + w ^ (2 : ℕ)).re) :
    xiMassHeightRadius τ w ^ (2 : ℕ) = τ ^ (2 : ℕ) + w ^ (2 : ℕ) :=
  HTGeometry.csqrt_sq hw

/-- A coefficient of the height ring: `(P(w) + Q(w)·Z(w)) / R(w)^j`. -/
def xiHeightCoeff (τ : ℂ) (P Q : Polynomial ℂ) (j : ℕ) (w : ℂ) : ℂ :=
  (P.eval w + Q.eval w * xiMassHeightRadius τ w) / (τ ^ (2 : ℕ) + w ^ (2 : ℕ)) ^ j

/-- The even half of the formal derivative. -/
def xiHeightCoeffDerivFst (τ : ℂ) (P : Polynomial ℂ) (j : ℕ) : Polynomial ℂ :=
  P.derivative * xiMassRadiusPoly τ - Polynomial.C (2 * (j : ℂ)) * (Polynomial.X * P)

/-- The odd half of the formal derivative. -/
def xiHeightCoeffDerivSnd (τ : ℂ) (Q : Polynomial ℂ) (j : ℕ) : Polynomial ℂ :=
  Q.derivative * xiMassRadiusPoly τ + Polynomial.C (1 - 2 * (j : ℂ)) * (Polynomial.X * Q)

theorem xiHeightCoeffDerivFst_eval (τ : ℂ) (P : Polynomial ℂ) (j : ℕ) (w : ℂ) :
    (xiHeightCoeffDerivFst τ P j).eval w
      = P.derivative.eval w * (τ ^ (2 : ℕ) + w ^ (2 : ℕ)) - 2 * (j : ℂ) * (w * P.eval w) := by
  rw [xiHeightCoeffDerivFst]
  simp [xiMassRadiusPoly_eval]

theorem xiHeightCoeffDerivSnd_eval (τ : ℂ) (Q : Polynomial ℂ) (j : ℕ) (w : ℂ) :
    (xiHeightCoeffDerivSnd τ Q j).eval w
      = Q.derivative.eval w * (τ ^ (2 : ℕ) + w ^ (2 : ℕ)) + (1 - 2 * (j : ℂ)) * (w * Q.eval w) := by
  rw [xiHeightCoeffDerivSnd]
  simp [xiMassRadiusPoly_eval]

/-- **The height ring is closed under differentiation.**  The derivative is the polynomial map
`(P, Q, j) ↦ (P′R − 2jwP, Q′R + (1−2j)wQ, j+1)`. -/
theorem hasDerivAt_xiHeightCoeff {τ w : ℂ} (P Q : Polynomial ℂ) (j : ℕ)
    (hw : 0 < (τ ^ (2 : ℕ) + w ^ (2 : ℕ)).re) :
    HasDerivAt (xiHeightCoeff τ P Q j)
      (xiHeightCoeff τ (xiHeightCoeffDerivFst τ P j) (xiHeightCoeffDerivSnd τ Q j) (j + 1) w) w := by
  have hRne : (τ ^ (2 : ℕ) + w ^ (2 : ℕ)) ≠ 0 := by
    intro hcon
    rw [hcon] at hw
    simp at hw
  have hZne : xiMassHeightRadius τ w ≠ 0 := xiMassHeightRadius_ne_zero hw
  have hZ2 : xiMassHeightRadius τ w ^ (2 : ℕ) = τ ^ (2 : ℕ) + w ^ (2 : ℕ) := xiMassHeightRadius_sq hw
  have hZ : HasDerivAt (xiMassHeightRadius τ) (w / xiMassHeightRadius τ w) w :=
    hasDerivAt_xiMassHeightRadius hw
  have hP : HasDerivAt (fun v : ℂ => P.eval v) (P.derivative.eval w) w := P.hasDerivAt w
  have hQ : HasDerivAt (fun v : ℂ => Q.eval v) (Q.derivative.eval w) w := Q.hasDerivAt w
  have hnum : HasDerivAt (fun v : ℂ => P.eval v + Q.eval v * xiMassHeightRadius τ v)
      (P.derivative.eval w
        + (Q.derivative.eval w * xiMassHeightRadius τ w
          + Q.eval w * (w / xiMassHeightRadius τ w))) w := hP.add (hQ.mul hZ)
  have hR : HasDerivAt (fun v : ℂ => τ ^ (2 : ℕ) + v ^ (2 : ℕ)) (2 * w) w := by
    have h1 := (hasDerivAt_pow 2 w).const_add (τ ^ (2 : ℕ))
    simpa using h1
  have hden : HasDerivAt (fun v : ℂ => (τ ^ (2 : ℕ) + v ^ (2 : ℕ)) ^ j)
      ((j : ℂ) * (τ ^ (2 : ℕ) + w ^ (2 : ℕ)) ^ (j - 1) * (2 * w)) w := hR.pow j
  have hdenne : ((τ ^ (2 : ℕ) + w ^ (2 : ℕ)) ^ j) ≠ 0 := pow_ne_zero _ hRne
  have hdiv := hnum.div hden hdenne
  have hval : xiHeightCoeff τ (xiHeightCoeffDerivFst τ P j) (xiHeightCoeffDerivSnd τ Q j) (j + 1) w
      = ((P.derivative.eval w
            + (Q.derivative.eval w * xiMassHeightRadius τ w
              + Q.eval w * (w / xiMassHeightRadius τ w))) * (τ ^ (2 : ℕ) + w ^ (2 : ℕ)) ^ j
          - (P.eval w + Q.eval w * xiMassHeightRadius τ w)
            * ((j : ℂ) * (τ ^ (2 : ℕ) + w ^ (2 : ℕ)) ^ (j - 1) * (2 * w))) / ((τ ^ (2 : ℕ) + w ^ (2 : ℕ)) ^ j) ^ (2 : ℕ) := by
    rw [xiHeightCoeff, xiHeightCoeffDerivFst_eval, xiHeightCoeffDerivSnd_eval, ← hZ2]
    rcases j with _ | k
    · simp only [Nat.cast_zero, pow_zero, Nat.zero_sub, mul_zero, zero_mul, sub_zero,
        one_pow, mul_one, div_one]
      field_simp
      ring
    · have hsucc : (k + 1 : ℕ) - 1 = k := by omega
      rw [hsucc]
      field_simp
      ring
  rw [hval]
  exact hdiv

end

end RHTower
