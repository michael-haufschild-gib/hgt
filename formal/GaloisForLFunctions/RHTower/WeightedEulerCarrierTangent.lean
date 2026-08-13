import GaloisForLFunctions.RHTower.CompactCarrierLambert
import GaloisForLFunctions.HTGeometry.ContinuousMapCauchyTransform
import GaloisForLFunctions.HTGeometry.QuadrantRestrictionSchwarz

/-!
# The compact Euler tangent of the coordinate is the Euler tangent itself

On a compact subset of the right half plane the exponential test at a prime logarithm is
contractive, so the compact-carrier Euler unit tangent of the coordinate function is the
continuous function `z ↦ (log p) p^{-z}/(1 - p^{-z})²`.

* `RHTower.compactPrimeEulerUnitTangent_coordMap`.
-/

noncomputable section

open Complex

namespace RHTower

open GaloisForLFunctions.HTGeometry

variable {K : Set ℂ} [CompactSpace K]

theorem norm_compactExponentialTest_coordMap_lt_one {α : ℝ} (hα : 0 < α)
    (hre : ∀ z ∈ K, α ≤ z.re) {p : ℕ} (hp : 2 ≤ p) :
    ‖compactExponentialTest (coordMap K) (Real.log p)‖ < 1 := by
  have hlog : 0 < Real.log p := Real.log_pos (by exact_mod_cast lt_of_lt_of_le one_lt_two hp)
  refine norm_compactExponentialTest_lt_one_of_re_pos (coordMap K) (Real.log p)
    (Real.log p * α) (by positivity) ?_
  intro k
  have hval : (((Real.log p : ℝ) : ℂ) * coordMap K k).re = Real.log p * ((k : ℂ)).re := by
    simp only [coordMap_apply, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero]
  rw [hval]
  exact mul_le_mul_of_nonneg_left (hre (k : ℂ) k.2) hlog.le

/-- **The compact Euler unit tangent of the coordinate is the Euler tangent.** -/
theorem compactPrimeEulerUnitTangent_coordMap {α : ℝ} (hα : 0 < α)
    (hre : ∀ z ∈ K, α ≤ z.re) {p : ℕ} (hp : 2 ≤ p) (k : K) :
    compactPrimeEulerUnitTangent (coordMap K) p k = primeEulerUnitTangent p (k : ℂ) := by
  rw [compactPrimeEulerUnitTangent_apply (coordMap K) hp k
    (norm_compactExponentialTest_coordMap_lt_one hα hre hp)]
  rfl

/-- The two names for the prime Euler tangent agree. -/
theorem primeEulerUnitTangent_eq_eulerTangent (p : ℕ) (s : ℂ) :
    primeEulerUnitTangent p s = _root_.HTGeometry.eulerTangent p s := rfl

/-- The two names for the symmetrised prime Euler tangent agree. -/
theorem primeEulerUnitFETangent_eq_feEulerTangent (p : ℕ) (s : ℂ) :
    primeEulerUnitFETangent p s = _root_.HTGeometry.feEulerTangent p s := rfl

end RHTower
