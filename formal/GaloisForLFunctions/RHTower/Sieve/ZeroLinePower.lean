import GaloisForLFunctions.RHTower.Sieve.DirichletLipschitz

/-!
# The zero-line power and its antiderivative

The Gram entries of Dirichlet rows are the sums `∑_{n ≤ N} n^{iv}`, so estimating them by comparison
with an integral needs the function

`x ↦ x^{iv} = exp(iv log x)`

together with its antiderivative `x^{1+iv}/(1+iv)`.  Both are assembled here, with the facts an
Euler–Maclaurin comparison consumes: the modulus of the power is `1`, the modulus of the
antiderivative is `x/‖1+iv‖`, the derivative of the antiderivative is the power, and the power is
continuous and interval-integrable away from the origin.

The corresponding objects on the abscissa `Re s = 1` are `HTGeometry/DirichletLinePartialSum.lean`;
the difference is the size of the antiderivative, which there is the constant `1/|α|` and here grows
like `x`.  That growth is why the zero-line sum is of size `N/‖1+iv‖` rather than `O(1)`.
-/

namespace RHTower.Sieve

open Complex

/-- The zero-line power `x^{iv}`. -/
noncomputable def zpow0 (v : ℝ) (x : ℝ) : ℂ :=
  Complex.exp ((v * Complex.I) * (Real.log x : ℂ))

/-- Its antiderivative `x^{1+iv}/(1+iv)`. -/
noncomputable def Zpow0 (v : ℝ) (x : ℝ) : ℂ :=
  Complex.exp ((1 + v * Complex.I) * (Real.log x : ℂ)) / (1 + v * Complex.I)

/-- The denominator never vanishes: its real part is `1`. -/
theorem one_add_mul_I_ne_zero (v : ℝ) : (1 : ℂ) + (v : ℂ) * Complex.I ≠ 0 := by
  intro hcon
  have hre : ((1 : ℂ) + (v : ℂ) * Complex.I).re = 0 := by rw [hcon]; simp
  simp at hre

/-- The zero-line power in phase form. -/
theorem zpow0_eq (v x : ℝ) :
    zpow0 v x = Complex.exp (((v * Real.log x : ℝ) : ℂ) * Complex.I) := by
  rw [zpow0]
  congr 1
  push_cast
  ring

/-- The zero-line power is unimodular. -/
theorem norm_zpow0 (v x : ℝ) : ‖zpow0 v x‖ = 1 := by
  rw [zpow0_eq]
  exact Complex.norm_exp_ofReal_mul_I _

/-- The numerator of the antiderivative factors through the power. -/
theorem exp_one_add_mul_log (v : ℝ) {x : ℝ} (hx : 0 < x) :
    Complex.exp ((1 + (v : ℂ) * Complex.I) * (Real.log x : ℂ)) = (x : ℂ) * zpow0 v x := by
  have hsplit : (1 + (v : ℂ) * Complex.I) * (Real.log x : ℂ)
      = ((Real.log x : ℝ) : ℂ) + (v : ℂ) * Complex.I * (Real.log x : ℂ) := by ring
  rw [hsplit, Complex.exp_add, zpow0]
  congr 1
  rw [← Complex.ofReal_exp, Real.exp_log hx]

/-- The modulus of the antiderivative. -/
theorem norm_Zpow0 (v : ℝ) {x : ℝ} (hx : 0 < x) :
    ‖Zpow0 v x‖ = x / ‖(1 : ℂ) + (v : ℂ) * Complex.I‖ := by
  rw [Zpow0, norm_div, exp_one_add_mul_log v hx, norm_mul, norm_zpow0, mul_one,
    Complex.norm_real, Real.norm_of_nonneg hx.le]

/-- The derivative of the zero-line power. -/
theorem hasDerivAt_zpow0 (v : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (zpow0 v) (zpow0 v x * ((v : ℂ) * Complex.I) / x) x := by
  have hlog := (Real.hasDerivAt_log hx.ne').ofReal_comp
  have hg := (hlog.const_mul ((v : ℂ) * Complex.I)).cexp
  have hcast : (((x⁻¹ : ℝ)) : ℂ) = (x : ℂ)⁻¹ := Complex.ofReal_inv x
  have hrw : Complex.exp ((v : ℂ) * Complex.I * (Real.log x : ℂ))
      * ((v : ℂ) * Complex.I * ((x⁻¹ : ℝ) : ℂ))
      = zpow0 v x * ((v : ℂ) * Complex.I) / x := by
    rw [zpow0, hcast]
    ring
  rw [← hrw]
  exact hg

/-- **The antiderivative differentiates to the power.** -/
theorem hasDerivAt_Zpow0 (v : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (Zpow0 v) (zpow0 v x) x := by
  have hlog := (Real.hasDerivAt_log hx.ne').ofReal_comp
  have hg := (hlog.const_mul ((1 : ℂ) + (v : ℂ) * Complex.I)).cexp
  have hdiv := hg.div_const ((1 : ℂ) + (v : ℂ) * Complex.I)
  have hcast : (((x⁻¹ : ℝ)) : ℂ) = (x : ℂ)⁻¹ := Complex.ofReal_inv x
  have hxne : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hvne : (1 : ℂ) + (v : ℂ) * Complex.I ≠ 0 := one_add_mul_I_ne_zero v
  have hrw : Complex.exp ((1 + (v : ℂ) * Complex.I) * (Real.log x : ℂ))
      * ((1 + (v : ℂ) * Complex.I) * ((x⁻¹ : ℝ) : ℂ)) / (1 + (v : ℂ) * Complex.I)
      = zpow0 v x := by
    rw [exp_one_add_mul_log v hx, hcast]
    field_simp
  rw [← hrw]
  exact hdiv

/-- The zero-line power is continuous away from the origin. -/
theorem continuousOn_zpow0 (v : ℝ) : ContinuousOn (zpow0 v) (Set.Ioi 0) :=
  fun _ hx => ((hasDerivAt_zpow0 v hx).continuousAt).continuousWithinAt

/-- It is interval-integrable on any interval away from the origin. -/
theorem intervalIntegrable_zpow0 (v : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (zpow0 v) MeasureTheory.volume a b := by
  refine ContinuousOn.intervalIntegrable ((continuousOn_zpow0 v).mono ?_)
  rw [Set.uIcc_of_le hab]
  exact fun x hx => lt_of_lt_of_le ha hx.1

end RHTower.Sieve
