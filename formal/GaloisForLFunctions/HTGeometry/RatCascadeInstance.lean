import GaloisForLFunctions.HTGeometry.RatCascadeOrder

/-!
# A rational first-order cascade outside the polynomial-coefficient family

The equation `z·h' = (z+1)·h` — that is, `h' = (1 + 1/z)·h` — has the transcendental entire solution
`c·z·e^z`.  Its coefficient `(z+1)/z` is not a polynomial, and the equation is not of the exponential
shape, so the rational family is strictly larger than the polynomial-coefficient one.

The nondegeneracy the peel needs holds here with room to spare: the leading coefficient has degree
`1 − 1 = 0` at infinity.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

/-- The entire solution of `z·h' = (z+1)·h`. -/
noncomputable def ratExample (c : ℂ) : ℂ → ℂ := fun z => c * (z * Complex.exp z)

theorem differentiable_ratExample (c : ℂ) : Differentiable ℂ (ratExample c) := by
  intro z
  exact (((hasDerivAt_id' z).mul (Complex.hasDerivAt_exp z)).const_mul c).differentiableAt

theorem deriv_ratExample (c : ℂ) (z : ℂ) :
    deriv (ratExample c) z = c * (1 * Complex.exp z + z * Complex.exp z) :=
  (((hasDerivAt_id' z).mul (Complex.hasDerivAt_exp z)).const_mul c).deriv

/-- **The cleared equation.** -/
theorem ode_ratExample (c : ℂ) (z : ℂ) :
    ((Polynomial.X : Polynomial ℂ) * 1).eval z * deriv (ratExample c) z
      = ((Polynomial.X + 1 : Polynomial ℂ) * 1).eval z * ratExample c z
        + ((0 : Polynomial ℂ) * Polynomial.X).eval z := by
  rw [deriv_ratExample, ratExample]
  simp only [Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_X,
    Polynomial.eval_zero, mul_one, zero_mul]
  ring

/-- **The solution is transcendental entire.**  A polynomial solution would force
`(X+1)·p = X·p'`, which raises the degree on the left and lowers it on the right. -/
theorem transcendentalEntire_ratExample {c : ℂ} (hc : c ≠ 0) :
    TranscendentalEntire (ratExample c) := by
  refine ⟨differentiable_ratExample c, ?_⟩
  rintro ⟨p, hp⟩
  have hderiv : ∀ z : ℂ, c * (1 * Complex.exp z + z * Complex.exp z) = p.derivative.eval z := by
    intro z
    have hfun : ratExample c = fun w => p.eval w := funext hp
    have h1 : deriv (ratExample c) z = deriv (fun w => p.eval w) z := by rw [hfun]
    rw [deriv_ratExample] at h1
    rw [h1, (p.hasDerivAt z).deriv]
  have hpoly : ∀ z : ℂ, ((Polynomial.X + 1 : Polynomial ℂ) * p).eval z
      = ((Polynomial.X : Polynomial ℂ) * p.derivative).eval z := by
    intro z
    have h1 := hp z
    have h2 := hderiv z
    simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_X]
    rw [← h1, ← h2, ratExample]
    ring
  have heq : (Polynomial.X + 1 : Polynomial ℂ) * p = (Polynomial.X : Polynomial ℂ) * p.derivative :=
    Polynomial.funext hpoly
  rcases eq_or_ne p 0 with rfl | hp0
  · have h1 := hp 1
    rw [ratExample] at h1
    simp only [Polynomial.eval_zero, one_mul] at h1
    exact (mul_ne_zero hc (Complex.exp_ne_zero 1)) h1
  · have hX1 : (Polynomial.X + 1 : Polynomial ℂ) ≠ 0 := by
      intro h0
      have := congrArg (fun q : Polynomial ℂ => q.eval 0) h0
      simp at this
    have hdegL : ((Polynomial.X + 1 : Polynomial ℂ) * p).natDegree = 1 + p.natDegree := by
      rw [Polynomial.natDegree_mul hX1 hp0]
      have : (Polynomial.X + 1 : Polynomial ℂ).natDegree = 1 := by
        simpa using Polynomial.natDegree_X_add_C (1 : ℂ)
      rw [this]
    have hdegR : ((Polynomial.X : Polynomial ℂ) * p.derivative).natDegree ≤ p.natDegree := by
      rcases eq_or_ne p.derivative 0 with hd | hd
      · rw [hd, mul_zero, Polynomial.natDegree_zero]
        omega
      · have h1 := Polynomial.natDegree_mul_le (p := (Polynomial.X : Polynomial ℂ))
          (q := p.derivative)
        have h2 := Polynomial.natDegree_derivative_le p
        have h3 : (Polynomial.X : Polynomial ℂ).natDegree = 1 := Polynomial.natDegree_X
        have h4 : 1 ≤ p.natDegree := by
          by_contra hcon
          have hp00 : p.natDegree = 0 := by omega
          obtain ⟨a, ha⟩ := Polynomial.natDegree_eq_zero.mp hp00
          exact hd (by rw [← ha, Polynomial.derivative_C])
        omega
    rw [heq] at hdegL
    omega

/-- The rational data of the example. -/
noncomputable def ratExampleFam : RatAffineFam where
  ln := fun _ => Polynomial.X + 1
  ld := fun _ => Polynomial.X
  cn := fun _ => 0
  cd := fun _ => 1
  ln_ne_zero := fun _ => by
    intro h0
    have := congrArg (fun q : Polynomial ℂ => q.eval 0) h0
    simp at this
  ld_ne_zero := fun _ => Polynomial.X_ne_zero
  cd_ne_zero := fun _ => one_ne_zero

/-- **The card's law for a cascade outside the polynomial-coefficient family.** -/
theorem exactDifferentialOrder_ratExampleCascade {c : ℂ} (hc : c ≠ 0) (m : ℕ) :
    ExactDifferentialOrder (entireCascade (fun _ => ratExample c) (m + 1)) (m + 1) := by
  refine ratExampleFam.exactDifferentialOrder_ratCascade
    (fun _ => transcendentalEntire_ratExample hc) (fun _ z => ode_ratExample c z) (fun _ => ?_) m
  have h1 : (Polynomial.X : Polynomial ℂ).natDegree = 1 := Polynomial.natDegree_X
  have h2 : (Polynomial.X + 1 : Polynomial ℂ).natDegree = 1 := by
    simpa using Polynomial.natDegree_X_add_C (1 : ℂ)
  show (Polynomial.X : Polynomial ℂ).natDegree ≤ (Polynomial.X + 1 : Polynomial ℂ).natDegree
  omega

/-- **The coefficient is not a polynomial.**  There is no `p` with `X + 1 = p·X`. -/
theorem ratExample_coefficient_not_polynomial (p : Polynomial ℂ) :
    (Polynomial.X + 1 : Polynomial ℂ) ≠ p * Polynomial.X := by
  intro h0
  have := congrArg (fun q : Polynomial ℂ => q.eval 0) h0
  simp at this

end GaloisForLFunctions.HTGeometry
