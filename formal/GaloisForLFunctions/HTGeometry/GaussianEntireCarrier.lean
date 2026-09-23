import GaloisForLFunctions.HTGeometry.BoundedRandomEntireSeries
import GaloisForLFunctions.HTGeometry.GaussianCoefficientTail
import GaloisForLFunctions.HTGeometry.MaximumTermLogarithmicDerivative

/-!
# The planar Gaussian entire function

On the almost-sure event that the coefficients are polynomially bounded, the series
`∑ₙ xₙ zⁿ / √(n!)` has entire coefficients, so it is an entire function.  Off that event the source
is set to zero, which makes the construction total without changing anything almost surely.
-/

open Filter MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The coefficient of the planar Gaussian entire series. -/
def gafCoeff (x : ℕ → ℂ) (n : ℕ) : ℂ :=
  x n / ((Real.sqrt ((Nat.factorial n : ℕ) : ℝ) : ℝ) : ℂ)

theorem norm_gafCoeff (x : ℕ → ℂ) (n : ℕ) :
    ‖gafCoeff x n‖ = ‖x n‖ / Real.sqrt ((Nat.factorial n : ℕ) : ℝ) := by
  rw [gafCoeff, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]

/-- The almost-sure polynomial-growth event. -/
def GoodGaussianCoefficients (x : ℕ → ℂ) : Prop := ∀ᶠ n : ℕ in atTop, ‖x n‖ < (n : ℝ)

theorem measurableSet_goodGaussianCoefficients :
    MeasurableSet {x : ℕ → ℂ | GoodGaussianCoefficients x} := by
  have hset : {x : ℕ → ℂ | GoodGaussianCoefficients x}
      = ⋃ N : ℕ, ⋂ n : {m : ℕ // N ≤ m}, {x : ℕ → ℂ | ‖x (n : ℕ)‖ < ((n : ℕ) : ℝ)} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_iInter, GoodGaussianCoefficients,
      eventually_atTop]
    constructor
    · rintro ⟨N, hN⟩
      exact ⟨N, fun n => hN (n : ℕ) n.2⟩
    · rintro ⟨N, hN⟩
      exact ⟨N, fun n hn => hN ⟨n, hn⟩⟩
  rw [hset]
  refine MeasurableSet.iUnion fun N => MeasurableSet.iInter fun n => ?_
  exact measurableSet_lt ((measurable_pi_apply (X := fun _ : ℕ => ℂ) (n : ℕ)).norm)
    measurable_const

theorem tendsto_pow_div_sqrt_factorial (t : ℝ) (ht : 0 ≤ t) :
    Tendsto (fun n : ℕ => t ^ n / Real.sqrt ((Nat.factorial n : ℕ) : ℝ)) atTop (nhds 0) := by
  have hsq : ∀ n : ℕ, t ^ n / Real.sqrt ((Nat.factorial n : ℕ) : ℝ)
      = Real.sqrt ((t ^ (2 : ℕ)) ^ n / ((Nat.factorial n : ℕ) : ℝ)) := by
    intro n
    have h1 : ((t ^ (2 : ℕ)) ^ n : ℝ) = (t ^ n) ^ (2 : ℕ) := by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    rw [h1, Real.sqrt_div (by positivity), Real.sqrt_sq (pow_nonneg ht n)]
  have hlim : Tendsto (fun n : ℕ => (t ^ (2 : ℕ)) ^ n / ((Nat.factorial n : ℕ) : ℝ)) atTop (nhds 0) :=
    FloorSemiring.tendsto_pow_div_factorial_atTop (t ^ (2 : ℕ))
  have hcomp := (Real.continuous_sqrt.tendsto 0).comp hlim
  rw [Real.sqrt_zero] at hcomp
  exact hcomp.congr fun n => (hsq n).symm

/-- Polynomially bounded coefficients with a `√(n!)` normalization are entire coefficients. -/
theorem entireCoeffs_of_eventually_norm_le_index {b : ℕ → ℂ}
    (hb : ∀ᶠ n : ℕ in atTop,
      ‖b n‖ ≤ (n : ℝ) / Real.sqrt ((Nat.factorial n : ℕ) : ℝ)) :
    EntireCoeffs b := by
  intro r hr
  refine squeeze_zero' (Eventually.of_forall fun n => by positivity) ?_
    (tendsto_pow_div_sqrt_factorial (2 * r) (by positivity))
  filter_upwards [hb] with n hn
  have hfac : (0 : ℝ) < Real.sqrt ((Nat.factorial n : ℕ) : ℝ) := by
    refine Real.sqrt_pos.2 ?_
    exact_mod_cast Nat.factorial_pos n
  have hn2 : (n : ℝ) ≤ 2 ^ n := by
    have hlt := Nat.lt_two_pow_self (n := n)
    have h2 : ((n : ℕ) : ℝ) < ((2 ^ n : ℕ) : ℝ) := by exact_mod_cast hlt
    push_cast at h2
    linarith
  calc ‖b n‖ * r ^ n ≤ ((n : ℝ) / Real.sqrt ((Nat.factorial n : ℕ) : ℝ)) * r ^ n :=
        mul_le_mul_of_nonneg_right hn (by positivity)
    _ ≤ ((2 : ℝ) ^ n / Real.sqrt ((Nat.factorial n : ℕ) : ℝ)) * r ^ n := by
        gcongr
    _ = (2 * r) ^ n / Real.sqrt ((Nat.factorial n : ℕ) : ℝ) := by
        rw [mul_pow]
        field_simp

/-- On the polynomial-growth event the Gaussian coefficients are entire coefficients. -/
theorem entireCoeffs_gafCoeff {x : ℕ → ℂ} (hx : GoodGaussianCoefficients x) :
    EntireCoeffs (gafCoeff x) := by
  refine entireCoeffs_of_eventually_norm_le_index ?_
  filter_upwards [hx] with n hn
  rw [norm_gafCoeff]
  have hfac : (0 : ℝ) < Real.sqrt ((Nat.factorial n : ℕ) : ℝ) := by
    refine Real.sqrt_pos.2 ?_
    exact_mod_cast Nat.factorial_pos n
  gcongr

open Classical in
/-- The planar Gaussian entire source: the series where it converges, and zero elsewhere. -/
def gaussianEntireSource (x : ℕ → ℂ) : MultivariateEntire 1 :=
  if h : GoodGaussianCoefficients x then
    oneDimMultivariateEntireOfDifferentiable (coeffFun (gafCoeff x))
      (differentiable_coeffFun (entireCoeffs_gafCoeff h))
  else 0

open Classical in
theorem gaussianEntireSource_of_good {x : ℕ → ℂ} (hx : GoodGaussianCoefficients x) :
    gaussianEntireSource x
      = oneDimMultivariateEntireOfDifferentiable (coeffFun (gafCoeff x))
        (differentiable_coeffFun (entireCoeffs_gafCoeff hx)) := by
  rw [gaussianEntireSource, dif_pos hx]

open Classical in
theorem gaussianEntireSource_of_not_good {x : ℕ → ℂ} (hx : ¬ GoodGaussianCoefficients x) :
    gaussianEntireSource x = 0 := by
  rw [gaussianEntireSource, dif_neg hx]

end

end GaloisForLFunctions.HTGeometry
