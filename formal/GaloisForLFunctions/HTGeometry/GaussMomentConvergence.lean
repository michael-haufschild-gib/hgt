import GaloisForLFunctions.HTGeometry.GaussMomentLimit
import GaloisForLFunctions.HTGeometry.MomentConvergence

/-!
# Instantiating moment convergence at the Gauss family

The general theorem of `MomentConvergence.lean` needs three inputs for the Gauss family: the Bochner
moments of the approximating measures, weak convergence in integral form, and integrability.

All three are immediate here.  The moments come from the quadrature theorem, since
`integral_gaussMeasure` is already stated for the Bochner integral — no `lintegral` bridge is needed
on the approximant side.  Weak convergence in integral form is
`ProbabilityMeasure.tendsto_iff_forall_integral_tendsto`.  Integrability is unconditional, because a
finite weighted sum of point masses integrates everything.
-/

open scoped BigOperators
open MeasureTheory Filter

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- Every function is integrable against the normalised Gauss measure. -/
theorem integrable_gaussProb (h : PositiveMomentForm s) (n : ℕ) (f : ℝ → ℝ) :
    Integrable f (gaussProb s n) := by
  rw [gaussProb]
  refine (integrable_gaussMeasure n f).smul_measure (ENNReal.inv_ne_top.mpr ?_)
  simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
  exact moment_zero_pos h

/-- **The Bochner moments of the normalised Gauss measure.** -/
theorem integral_pow_gaussProb (h : PositiveMomentForm s) (n k : ℕ) (hk : k ≤ 2 * n + 1) :
    ∫ x, x ^ k ∂(gaussProb s n) = (s 0)⁻¹ * s k := by
  rw [gaussProb, integral_smul_measure, integral_gaussMeasure h n fun x => x ^ k,
    gaussSum_pow h n k hk, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (moment_zero_pos h).le, smul_eq_mul]

/-- Weak convergence of the extracted subsequence, in integral form. -/
theorem tendsto_integral_gaussProb (h : PositiveMomentForm s) {μ : ProbabilityMeasure ℝ}
    {φ : ℕ → ℕ} (hlim : Tendsto (fun i => gaussProbMeasure h (φ i + 1)) atTop (nhds μ))
    (f : BoundedContinuousFunction ℝ ℝ) :
    Tendsto (fun i => ∫ x, f x ∂(gaussProb s (φ i + 1))) atTop
      (nhds (∫ x, f x ∂(μ : Measure ℝ))) :=
  ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim f

/-- The even moments of the Gauss family are uniformly bounded along any subsequence, once the level
is high enough for the quadrature to reach that order. -/
theorem integral_even_pow_gaussProb_le (h : PositiveMomentForm s) (k : ℕ) {φ : ℕ → ℕ}
    (hφ : StrictMono φ) {i : ℕ} (hi : k ≤ i) :
    ∫ x, x ^ (2 * k) ∂(gaussProb s (φ i + 1)) = (s 0)⁻¹ * s (2 * k) := by
  have hle : i ≤ φ i := hφ.le_apply
  exact integral_pow_gaussProb h (φ i + 1) (2 * k) (by omega)

end HTGeometry
