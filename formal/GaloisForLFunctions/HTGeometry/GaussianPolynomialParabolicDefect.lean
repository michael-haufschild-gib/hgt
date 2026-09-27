import GaloisForLFunctions.HTGeometry.GaussianPolynomialPhaseDefect

/-!
# Degree-uniform relative Gaussian error at the inverse square-root scale

Rescaling the imaginary displacement by the square root of degree plus one
removes degree from the relative error bound. The resulting continuous-energy
margin is uniform over every real polynomial, with all coefficient cross terms.
-/

open scoped Real SchwartzMap
open Complex MeasureTheory Filter Topology
noncomputable section

namespace GaloisForLFunctions

/-- A degree-independent envelope for the entire Gaussian translation defect. -/
def parabolicGaussianDefect (ε : ℝ) : ℝ :=
  Real.exp (π * ε ^ 2) *
    (Real.exp (|ε| * Real.sqrt (4 * π)) + |ε| * Real.sqrt (4 * π)) - 1

/-- Inverse-square-root degree scaling controls every component of the Gaussian defect. -/
theorem verticalPolynomialGaussianDefect_parabolic_le (d : ℕ) (ε : ℝ) :
    verticalPolynomialGaussianDefect d (ε / Real.sqrt ((d : ℝ) + 1)) ≤
      parabolicGaussianDefect ε := by
  let r := Real.sqrt ((d : ℝ) + 1)
  have hr : 0 < r := Real.sqrt_pos.mpr (by positivity)
  have hr1 : 1 ≤ r := Real.one_le_sqrt.mpr (by
    have hn := Nat.cast_nonneg (α := ℝ) d
    linarith only [hn])
  have habs : |ε / r| = |ε| / r := by rw [abs_div, abs_of_pos hr]
  have hv : |ε / r| * Real.sqrt (4 * π * ((d : ℝ) + 1)) =
      |ε| * Real.sqrt (4 * π) := by
    rw [habs, Real.sqrt_mul (by positivity : 0 ≤ 4 * π)]
    change |ε| / r * (Real.sqrt (4 * π) * r) = _
    field_simp
  have hu : |ε / r| * Real.sqrt (4 * π * (d : ℝ)) ≤
      |ε| * Real.sqrt (4 * π) := by
    rw [← hv]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    apply Real.sqrt_le_sqrt
    nlinarith only [Real.pi_pos]
  have hsq : (ε / r) ^ 2 ≤ ε ^ 2 := by
    rw [div_pow]
    exact div_le_self (sq_nonneg ε) (by nlinarith only [hr1])
  have hc := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsq Real.pi_pos.le)
  have hu' := Real.exp_le_exp.mpr hu
  have hnonneg : 0 ≤ Real.exp (|ε / r| * Real.sqrt (4 * π * (d : ℝ))) +
      |ε| * Real.sqrt (4 * π) := by positivity
  have hmul := mul_le_mul hc
    (add_le_add hu' le_rfl) hnonneg (Real.exp_pos (π * ε ^ 2)).le
  unfold verticalPolynomialGaussianDefect parabolicGaussianDefect
  change Real.exp (π * (ε / r) ^ 2) *
    (Real.exp (|ε / r| * Real.sqrt (4 * π * d)) - 1 +
      |ε / r| * Real.sqrt (4 * π * ((d : ℝ) + 1))) +
      (Real.exp (π * (ε / r) ^ 2) - 1) ≤ _
  rw [hv]
  nlinarith only [hmul]

/-- The complete Gaussian translation error is uniform in polynomial degree after scaling. -/
theorem norm_verticalPolynomialGaussianLp_parabolic_sub_le (P : Polynomial ℝ) (ε : ℝ) :
    ‖verticalPolynomialGaussianLp P (ε / Real.sqrt ((P.natDegree : ℝ) + 1)) -
        (polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)‖ ≤
      parabolicGaussianDefect ε *
        ‖(polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)‖ :=
  (norm_verticalPolynomialGaussianLp_sub_le P _).trans
    (mul_le_mul_of_nonneg_right (verticalPolynomialGaussianDefect_parabolic_le _ ε)
      (norm_nonneg _))

/-- The degree-independent error tends to zero as the scaled displacement vanishes. -/
theorem parabolicGaussianDefect_tendsto_zero :
    Tendsto parabolicGaussianDefect (𝓝 0) (𝓝 0) := by
  have h : Continuous parabolicGaussianDefect := by unfold parabolicGaussianDefect; fun_prop
  simpa [parabolicGaussianDefect] using h.tendsto 0

/-- One neighborhood gives a half-norm floor for every polynomial degree and coefficient vector. -/
theorem eventually_forall_verticalPolynomialGaussianLp_parabolic_lower :
    ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ P : Polynomial ℝ,
      (1 / 2 : ℝ) * ‖(polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)‖ ≤
        ‖verticalPolynomialGaussianLp P (ε / Real.sqrt ((P.natDegree : ℝ) + 1))‖ := by
  have he := parabolicGaussianDefect_tendsto_zero.eventually
    (eventually_lt_nhds (by positivity : (0 : ℝ) < 1 / 2))
  filter_upwards [he] with ε hε P
  have h := norm_verticalPolynomialGaussianLp_parabolic_sub_le P ε
  have ht := norm_le_norm_add_norm_sub
    (verticalPolynomialGaussianLp P (ε / Real.sqrt ((P.natDegree : ℝ) + 1)))
    ((polyGaussSchwartz P).toLp 2 (volume : Measure ℝ))
  have hm := mul_le_mul_of_nonneg_right hε.le
    (norm_nonneg ((polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)))
  linarith only [h, ht, hm]

end GaloisForLFunctions
