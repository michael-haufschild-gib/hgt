import GaloisForLFunctions.RHTower.XiGlobalMeixnerShapeLandau

/-!
# The Xi Gamma-shape trace is completely monotone on its safe interval

The nonnegative Xi prime-seam trace is a general Dirichlet series with nonnegative coefficients and
nonnegative frequencies.  On its safe shape interval every alternating derivative is the
corresponding nonnegative frequency moment, and the radial Hankel kernel is a Gram kernel of
exponential vectors.

Complete monotonicity is strictly stronger than plain Hankel positivity: the kernel
`K(s,t) = exp (s + t)` is a rank-one Gram kernel, yet the real exponential is not completely
monotone because its generator frequency is negative.
-/

open Complex

namespace RHTower

noncomputable section

/-- **Complete monotonicity on the safe shape interval.**  Every alternating derivative of the
global Gamma-shape trace is the corresponding nonnegative frequency moment. -/
theorem xiGammaShapeTrace_completelyMonotone {θ : ℝ} (hθ : 1 < θ) (k : ℕ) :
    ((-1) ^ k * iteratedDeriv k xiGammaShapeTrace ((θ : ℝ) : ℂ)) =
      ((GaloisForLFunctions.HTGeometry.gdMoment
        xiGammaShapeCoefficient xiGammaShapeFrequency θ k : ℝ) : ℂ) := by
  set σ₁ : ℝ := (1 + θ) / 2 with hσ₁
  have hσ₁gt : 1 < σ₁ := by rw [hσ₁]; linarith
  have hh : 0 < θ - σ₁ := by rw [hσ₁]; linarith
  have hsplit : σ₁ + (θ - σ₁) = θ := by ring
  have h := GaloisForLFunctions.HTGeometry.gdSeries_completelyMonotone
    xiGammaShapeCoefficient_nonneg xiGammaShapeFrequency_nonneg
    (summable_xiGammaShapeTwist hσ₁gt) hh k
  rw [hsplit] at h
  exact h

/-- The alternating derivatives are nonnegative reals. -/
theorem xiGammaShapeTrace_alternating_nonneg {θ : ℝ} (hθ : 1 < θ) (k : ℕ) :
    0 ≤ ((-1) ^ k * iteratedDeriv k xiGammaShapeTrace ((θ : ℝ) : ℂ)).re := by
  rw [xiGammaShapeTrace_completelyMonotone hθ k, Complex.ofReal_re]
  exact GaloisForLFunctions.HTGeometry.gdMoment_nonneg
    xiGammaShapeCoefficient_nonneg xiGammaShapeFrequency_nonneg θ k

/-- The real Gamma-shape trace on the safe interval. -/
def xiGammaShapeRealTrace (θ : ℝ) : ℝ :=
  GaloisForLFunctions.HTGeometry.gdRealSeries
    xiGammaShapeCoefficient xiGammaShapeFrequency θ

/-- **Radial Hankel positivity.**  On the safe shape interval the Hankel kernel of the global
Gamma-shape trace is a Gram kernel of exponential vectors, hence positive semidefinite. -/
theorem xiGammaShapeRealTrace_hankel_nonneg {n : ℕ} (θ c : Fin n → ℝ)
    (hθ : ∀ i, 1 < θ i) :
    0 ≤ ∑ i, ∑ j, c i * xiGammaShapeRealTrace (θ i + θ j) * c j := by
  refine GaloisForLFunctions.HTGeometry.gdRealSeries_hankel_nonneg
    xiGammaShapeCoefficient_nonneg xiGammaShapeFrequency_nonneg
    (summable_xiGammaShapeTwist (by norm_num : (1 : ℝ) < 3 / 2)) θ c (fun i => ?_)
  linarith [hθ i]

/-! ## Plain Hankel positivity is strictly weaker -/

/-- The exponential kernel is a rank-one Gram kernel, hence positive semidefinite. -/
theorem exp_hankel_nonneg {n : ℕ} (θ c : Fin n → ℝ) :
    0 ≤ ∑ i, ∑ j, c i * Real.exp (θ i + θ j) * c j := by
  have hkey : ∑ i, ∑ j, c i * Real.exp (θ i + θ j) * c j =
      (∑ i, c i * Real.exp (θ i)) ^ (2 : ℕ) := by
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Real.exp_add]
    ring
  rw [hkey]
  exact sq_nonneg _

/-- The exponential is not completely monotone: its first alternating derivative is negative.
Positive semidefiniteness of the Hankel kernel therefore does not imply complete monotonicity. -/
theorem exp_not_completelyMonotone (θ : ℝ) :
    (-1 : ℝ) ^ (1 : ℕ) * iteratedDeriv 1 Real.exp θ < 0 := by
  have hderiv : iteratedDeriv 1 Real.exp θ = Real.exp θ := by
    rw [iteratedDeriv_one, Real.deriv_exp]
  rw [hderiv]
  simp only [pow_one]
  nlinarith [Real.exp_pos θ]

end

end RHTower
