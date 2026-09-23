import GaloisForLFunctions.HTGeometry.DigammaGammaLocalHypertranscendence

/-!
# The order-one boundary of the multiple sine hierarchy

The multiple sine hierarchy bottoms out at order one, where

```text
S_1(z; ω) = 2 sin(π z / ω),        L_1(z) = (log S_1)'(z) = (π/ω) cot(π z / ω).
```

Two facts about this boundary carry the whole all-order descent.

* **It is differentially algebraic.**  `L_1` satisfies the constant-coefficient Riccati equation

  ```text
  L_1' + L_1² + (π/ω)² = 0,
  ```

  an explicit order-one algebraic differential equation, on the complement of the zero set of
  `sin(π z / ω)`.  This is why every squarefree monomial of degree `N-1` lies in the differential
  annihilator of the order-`N` logarithmic derivative: the face of codimension one *is* the
  cotangent boundary.

* **It is period-invariant.**  `L_1(z + ω) = L_1(z)`, which is the multiple-sine difference
  equation `(T_j - 1) L_A = -L_{A∖{j}}` at `|A| = 1`, where the deeper face is the constant `0`.
  The sine itself only changes sign, `S_1(z + ω) = -S_1(z)`, which is the harmless global sign of
  the reciprocal convention.

Everything here is unconditional; `Complex.cot` has no derivative API in mathlib, so the
derivative and the addition law are proved from `Complex.sin` and `Complex.cos`.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex MvPolynomial

noncomputable section

/-! ### The cotangent: derivative and period -/

/-- The cotangent has period `π`. -/
theorem cot_add_pi (w : ℂ) : Complex.cot (w + Real.pi) = Complex.cot w := by
  rw [Complex.cot_eq_cos_div_sin, Complex.cot_eq_cos_div_sin,
    Complex.cos_add_pi, Complex.sin_add_pi, neg_div_neg_eq]

/-- **Derivative of the cotangent.**  Off the zeros of the sine, `cot' = -1/sin²`. -/
theorem hasDerivAt_cot {w : ℂ} (hw : Complex.sin w ≠ 0) :
    HasDerivAt Complex.cot (-(1 / Complex.sin w ^ (2 : ℕ))) w := by
  have hderiv :
      HasDerivAt (fun x => Complex.cos x / Complex.sin x)
        ((-Complex.sin w * Complex.sin w - Complex.cos w * Complex.cos w) /
          Complex.sin w ^ (2 : ℕ)) w :=
    (Complex.hasDerivAt_cos w).div (Complex.hasDerivAt_sin w) hw
  have hval :
      (-Complex.sin w * Complex.sin w - Complex.cos w * Complex.cos w) /
          Complex.sin w ^ (2 : ℕ) = -(1 / Complex.sin w ^ (2 : ℕ)) := by
    have hpyth := Complex.sin_sq_add_cos_sq w
    field_simp
    linear_combination -hpyth
  rw [hval] at hderiv
  refine hderiv.congr_deriv rfl |>.congr_of_eventuallyEq ?_
  filter_upwards with x
  exact (Complex.cot_eq_cos_div_sin x).symm

/-! ### The order-one multiple sine -/

variable (ω : ℝ)

/-- Order-one multiple sine `S_1(z; ω) = 2 sin(π z / ω)`. -/
def multipleSineOne (z : ℂ) : ℂ := 2 * Complex.sin ((Real.pi : ℂ) * z / (ω : ℂ))

/-- Its logarithmic derivative `L_1(z) = (π/ω) cot(π z / ω)`. -/
def multipleSineOneLogDeriv (z : ℂ) : ℂ :=
  ((Real.pi : ℂ) / (ω : ℂ)) * Complex.cot ((Real.pi : ℂ) * z / (ω : ℂ))

/-- Points at which the order-one boundary is regular. -/
def multipleSineOneRegularSet : Set ℂ :=
  {z : ℂ | Complex.sin ((Real.pi : ℂ) * z / (ω : ℂ)) ≠ 0}

variable {ω}

/-! ### The difference equation at order one -/

/-- The order-one sine changes sign under its period: the harmless global sign of the reciprocal
convention. -/
theorem multipleSineOne_add_period (hω : (ω : ℂ) ≠ 0) (z : ℂ) :
    multipleSineOne ω (z + ω) = -multipleSineOne ω z := by
  unfold multipleSineOne
  have harg : (Real.pi : ℂ) * (z + (ω : ℂ)) / (ω : ℂ) =
      (Real.pi : ℂ) * z / (ω : ℂ) + (Real.pi : ℂ) := by
    field_simp
  rw [harg, Complex.sin_add_pi]
  ring

/-- **The order-one difference equation.**  `(T_ω - 1) L_1 = 0`: the deeper face of the codimension
one boundary is the constant `0`. -/
theorem multipleSineOneLogDeriv_add_period (hω : (ω : ℂ) ≠ 0) (z : ℂ) :
    multipleSineOneLogDeriv ω (z + ω) = multipleSineOneLogDeriv ω z := by
  unfold multipleSineOneLogDeriv
  have harg : (Real.pi : ℂ) * (z + (ω : ℂ)) / (ω : ℂ) =
      (Real.pi : ℂ) * z / (ω : ℂ) + (Real.pi : ℂ) := by
    field_simp
  rw [harg, cot_add_pi]

/-! ### `L_1` is the logarithmic derivative of `S_1` -/

theorem hasDerivAt_multipleSineOne (z : ℂ) :
    HasDerivAt (multipleSineOne ω)
      (2 * ((Real.pi : ℂ) / (ω : ℂ)) *
        Complex.cos ((Real.pi : ℂ) * z / (ω : ℂ))) z := by
  have hlin : HasDerivAt (fun x : ℂ => (Real.pi : ℂ) * x / (ω : ℂ))
      ((Real.pi : ℂ) / (ω : ℂ)) z := by
    simpa [mul_comm, mul_div_assoc] using
      (((hasDerivAt_id z).const_mul (Real.pi : ℂ)).div_const (ω : ℂ))
  have hsin := (Complex.hasDerivAt_sin ((Real.pi : ℂ) * z / (ω : ℂ))).comp z hlin
  refine (hsin.const_mul (2 : ℂ)).congr_deriv ?_
  ring

/-- **The order-one boundary is a logarithmic derivative.** -/
theorem logDeriv_multipleSineOne (hω : (ω : ℂ) ≠ 0) {z : ℂ}
    (hz : z ∈ multipleSineOneRegularSet ω) :
    logDeriv (multipleSineOne ω) z = multipleSineOneLogDeriv ω z := by
  have hsin : Complex.sin ((Real.pi : ℂ) * z / (ω : ℂ)) ≠ 0 := hz
  rw [logDeriv_apply, (hasDerivAt_multipleSineOne z).deriv]
  unfold multipleSineOne multipleSineOneLogDeriv
  rw [Complex.cot_eq_cos_div_sin]
  field_simp

/-! ### The order-one sine itself is globally differentially algebraic -/

theorem deriv_multipleSineOne :
    deriv (multipleSineOne ω) =
      fun z => 2 * ((Real.pi : ℂ) / (ω : ℂ)) *
        Complex.cos ((Real.pi : ℂ) * z / (ω : ℂ)) := by
  funext z
  exact (hasDerivAt_multipleSineOne z).deriv

theorem hasDerivAt_deriv_multipleSineOne (z : ℂ) :
    HasDerivAt (deriv (multipleSineOne ω))
      (-(((Real.pi : ℂ) / (ω : ℂ)) ^ (2 : ℕ)) * multipleSineOne ω z) z := by
  rw [deriv_multipleSineOne]
  have hlin : HasDerivAt (fun x : ℂ => (Real.pi : ℂ) * x / (ω : ℂ))
      ((Real.pi : ℂ) / (ω : ℂ)) z := by
    simpa [mul_comm, mul_div_assoc] using
      (((hasDerivAt_id z).const_mul (Real.pi : ℂ)).div_const (ω : ℂ))
  have hcos := (Complex.hasDerivAt_cos ((Real.pi : ℂ) * z / (ω : ℂ))).comp z hlin
  refine (hcos.const_mul (2 * ((Real.pi : ℂ) / (ω : ℂ)))).congr_deriv ?_
  unfold multipleSineOne
  ring

/-- **The order-one sine solves the harmonic equation** `S_1'' + (π/ω)² S_1 = 0`, everywhere. -/
theorem multipleSineOne_secondOrder (z : ℂ) :
    deriv (deriv (multipleSineOne ω)) z +
      ((Real.pi : ℂ) / (ω : ℂ)) ^ (2 : ℕ) * multipleSineOne ω z = 0 := by
  rw [(hasDerivAt_deriv_multipleSineOne z).deriv]
  ring

/-- The harmonic differential polynomial `y₂ + (π/ω)² y₀` in the jet variables `(s, y₀, y₁, y₂)`. -/
def harmonicJetPolynomial (ω : ℝ) : MvPolynomial (Fin 4) ℂ :=
  X 3 + C (((Real.pi : ℂ) / (ω : ℂ)) ^ (2 : ℕ)) * X 1

theorem harmonicJetPolynomial_ne_zero (ω : ℝ) : harmonicJetPolynomial ω ≠ 0 := by
  intro h
  have hev := congrArg
    (MvPolynomial.eval (fun i : Fin 4 => if i = 3 then (1 : ℂ) else 0)) h
  simp [harmonicJetPolynomial] at hev

/-- **The order-one multiple sine is differentially algebraic**, globally on `ℂ`: it is an entire
solution of an explicit constant-coefficient second-order equation. -/
theorem differentiallyAlgebraic_multipleSineOne :
    DifferentiallyAlgebraic (multipleSineOne ω) := by
  refine ⟨2, harmonicJetPolynomial ω, harmonicJetPolynomial_ne_zero ω, ?_⟩
  intro z
  have hsecond := multipleSineOne_secondOrder (ω := ω) z
  have h0 : iteratedDeriv 0 (multipleSineOne ω) z = multipleSineOne ω z := by
    rw [iteratedDeriv_zero]
  have h2 : iteratedDeriv 2 (multipleSineOne ω) z =
      deriv (deriv (multipleSineOne ω)) z := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  have e1 : (Fin.cons z (fun j : Fin 3 => iteratedDeriv (j : ℕ)
      (multipleSineOne ω) z) : Fin 4 → ℂ) 1 = multipleSineOne ω z := by
    show iteratedDeriv ((0 : Fin 3) : ℕ) (multipleSineOne ω) z = _
    exact h0
  have e3 : (Fin.cons z (fun j : Fin 3 => iteratedDeriv (j : ℕ)
      (multipleSineOne ω) z) : Fin 4 → ℂ) 3 =
      deriv (deriv (multipleSineOne ω)) z := by
    show iteratedDeriv ((2 : Fin 3) : ℕ) (multipleSineOne ω) z = _
    exact h2
  simp only [harmonicJetPolynomial, map_add, map_mul, MvPolynomial.eval_X,
    MvPolynomial.eval_C, e1, e3]
  linear_combination hsecond

/-! ### The Riccati equation of the order-one boundary -/

/-- **Derivative of the order-one boundary.** -/
theorem hasDerivAt_multipleSineOneLogDeriv (hω : (ω : ℂ) ≠ 0) {z : ℂ}
    (hz : z ∈ multipleSineOneRegularSet ω) :
    HasDerivAt (multipleSineOneLogDeriv ω)
      (-(multipleSineOneLogDeriv ω z) ^ (2 : ℕ) - ((Real.pi : ℂ) / (ω : ℂ)) ^ (2 : ℕ)) z := by
  have hsin : Complex.sin ((Real.pi : ℂ) * z / (ω : ℂ)) ≠ 0 := hz
  have hlin : HasDerivAt (fun x : ℂ => (Real.pi : ℂ) * x / (ω : ℂ))
      ((Real.pi : ℂ) / (ω : ℂ)) z := by
    simpa [mul_comm, mul_div_assoc] using
      (((hasDerivAt_id z).const_mul (Real.pi : ℂ)).div_const (ω : ℂ))
  have hcot := (hasDerivAt_cot hsin).comp z hlin
  refine (hcot.const_mul ((Real.pi : ℂ) / (ω : ℂ))).congr_deriv ?_
  unfold multipleSineOneLogDeriv
  rw [Complex.cot_eq_cos_div_sin]
  have hpyth := Complex.sin_sq_add_cos_sq ((Real.pi : ℂ) * z / (ω : ℂ))
  field_simp
  linear_combination hpyth

/-- **The order-one Riccati equation.**  `L_1' + L_1² + (π/ω)² = 0` on the regular set. -/
theorem multipleSineOneLogDeriv_riccati (hω : (ω : ℂ) ≠ 0) {z : ℂ}
    (hz : z ∈ multipleSineOneRegularSet ω) :
    deriv (multipleSineOneLogDeriv ω) z + (multipleSineOneLogDeriv ω z) ^ (2 : ℕ) +
      ((Real.pi : ℂ) / (ω : ℂ)) ^ (2 : ℕ) = 0 := by
  rw [(hasDerivAt_multipleSineOneLogDeriv hω hz).deriv]
  ring

/-! ### Differential algebraicity of the boundary -/

/-- The order-one Riccati differential polynomial `y₁ + y₀² + (π/ω)²` in the jet variables
`(s, y₀, y₁)`. -/
def riccatiJetPolynomial (ω : ℝ) : MvPolynomial (Fin 3) ℂ :=
  X 2 + X 1 ^ (2 : ℕ) + C (((Real.pi : ℂ) / (ω : ℂ)) ^ (2 : ℕ))

theorem riccatiJetPolynomial_ne_zero (ω : ℝ) : riccatiJetPolynomial ω ≠ 0 := by
  intro h
  have hev := congrArg (MvPolynomial.eval
    (fun i : Fin 3 => if i = 2 then 1 - ((Real.pi : ℂ) / (ω : ℂ)) ^ (2 : ℕ) else 0)) h
  simp [riccatiJetPolynomial] at hev

/-- **The order-one boundary is differentially algebraic.**  It satisfies the explicit
constant-coefficient order-one Riccati relation on its regular set, so the codimension-one face of
the multiple-sine complex is a DA face. -/
theorem differentiallyAlgebraicOn_multipleSineOneLogDeriv (hω : (ω : ℂ) ≠ 0) :
    DifferentiallyAlgebraicOn (multipleSineOneLogDeriv ω)
      (multipleSineOneRegularSet ω) := by
  refine ⟨1, riccatiJetPolynomial ω, riccatiJetPolynomial_ne_zero ω, ?_⟩
  intro z hz
  have hriccati := multipleSineOneLogDeriv_riccati hω hz
  have h0 : iteratedDeriv 0 (multipleSineOneLogDeriv ω) z =
      multipleSineOneLogDeriv ω z := by
    rw [iteratedDeriv_zero]
  have h1 : iteratedDeriv 1 (multipleSineOneLogDeriv ω) z =
      deriv (multipleSineOneLogDeriv ω) z := by
    rw [iteratedDeriv_one]
  have e1 : (Fin.cons z (fun j : Fin 2 => iteratedDeriv (j : ℕ)
      (multipleSineOneLogDeriv ω) z) : Fin 3 → ℂ) 1 =
      multipleSineOneLogDeriv ω z := by
    show iteratedDeriv ((0 : Fin 2) : ℕ) (multipleSineOneLogDeriv ω) z = _
    exact h0
  have e2 : (Fin.cons z (fun j : Fin 2 => iteratedDeriv (j : ℕ)
      (multipleSineOneLogDeriv ω) z) : Fin 3 → ℂ) 2 =
      deriv (multipleSineOneLogDeriv ω) z := by
    show iteratedDeriv ((1 : Fin 2) : ℕ) (multipleSineOneLogDeriv ω) z = _
    exact h1
  simp only [riccatiJetPolynomial, map_add, map_pow, MvPolynomial.eval_X,
    MvPolynomial.eval_C, e1, e2]
  linear_combination hriccati

/-- **The order-one boundary law.**  The bottom face of the multiple-sine hierarchy is
period-invariant and differentially algebraic, with the explicit Riccati witness. -/
theorem multipleSine_orderOne_boundary_law (hω : (ω : ℂ) ≠ 0) :
    (∀ z : ℂ, multipleSineOne ω (z + ω) = -multipleSineOne ω z) ∧
    (∀ z : ℂ, multipleSineOneLogDeriv ω (z + ω) = multipleSineOneLogDeriv ω z) ∧
    (∀ z ∈ multipleSineOneRegularSet ω,
      logDeriv (multipleSineOne ω) z = multipleSineOneLogDeriv ω z) ∧
    (∀ z ∈ multipleSineOneRegularSet ω,
      deriv (multipleSineOneLogDeriv ω) z + (multipleSineOneLogDeriv ω z) ^ (2 : ℕ) +
        ((Real.pi : ℂ) / (ω : ℂ)) ^ (2 : ℕ) = 0) ∧
    DifferentiallyAlgebraicOn (multipleSineOneLogDeriv ω)
      (multipleSineOneRegularSet ω) :=
  ⟨multipleSineOne_add_period hω, multipleSineOneLogDeriv_add_period hω,
    fun _ hz => logDeriv_multipleSineOne hω hz,
    fun _ hz => multipleSineOneLogDeriv_riccati hω hz,
    differentiallyAlgebraicOn_multipleSineOneLogDeriv hω⟩

end

end GaloisForLFunctions.HTGeometry
