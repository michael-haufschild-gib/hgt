import GaloisForLFunctions.HTGeometry.LocalExponentialTestClosure
import Mathlib.Probability.Distributions.Gaussian.Real

/-! A quadratic exponential controls every mixed monomial; every centered Gaussian power is integrable. -/

open MeasureTheory ProbabilityTheory Filter

namespace GaloisForLFunctions.HTGeometry

theorem mixed_monomial_sq_le_quadratic_exponential (p q : ℕ) (x y : ℝ)
    {η : ℝ} (hη : 0 < η) :
    (x ^ p * y ^ q) ^ 2 ≤ ((p + q).factorial : ℝ) / η ^ (p + q) *
      Real.exp (η * (x ^ 2 + y ^ 2)) := by
  have hx : (x ^ 2) ^ p ≤ (x ^ 2 + y ^ 2) ^ p :=
    pow_le_pow_left₀ (sq_nonneg x) (le_add_of_nonneg_right (sq_nonneg y)) p
  have hy : (y ^ 2) ^ q ≤ (x ^ 2 + y ^ 2) ^ q :=
    pow_le_pow_left₀ (sq_nonneg y) (le_add_of_nonneg_left (sq_nonneg x)) q
  have hpoly : (x ^ p * y ^ q) ^ 2 ≤ (x ^ 2 + y ^ 2) ^ (p + q) := by
    calc
      _ = (x ^ 2) ^ p * (y ^ 2) ^ q := by simp only [mul_pow, ← pow_mul, Nat.mul_comm]
      _ ≤ (x ^ 2 + y ^ 2) ^ p * (x ^ 2 + y ^ 2) ^ q :=
        mul_le_mul hx hy (pow_nonneg (sq_nonneg y) q)
          (pow_nonneg (add_nonneg (sq_nonneg x) (sq_nonneg y)) p)
      _ = _ := (pow_add _ p q).symm
  apply hpoly.trans
  have h := _root_.HTGeometry.abs_pow_le_const_mul_exp hη (p + q) (x ^ 2 + y ^ 2)
  have hnn : (0 : ℝ) ≤ x ^ 2 + y ^ 2 := add_nonneg (sq_nonneg x) (sq_nonneg y)
  rw [abs_of_nonneg hnn] at h
  exact h

theorem gaussianZero_integrable_abs_nat_pow (v : NNReal) (p : ℕ) :
    Integrable (fun x : ℝ => |x| ^ p) (gaussianReal 0 v) := by
  by_cases hp : p = 0
  · subst p
    simpa only [pow_zero] using
      (integrable_const (1 : ℝ) : Integrable (fun _ : ℝ => (1 : ℝ)) (gaussianReal 0 v))
  have hmem : MemLp (id : ℝ → ℝ) (p : ENNReal) (gaussianReal 0 v) := by
    simpa using (memLp_id_gaussianReal (μ := 0) (v := v) (p : NNReal))
  simpa only [id_eq, Real.norm_eq_abs] using hmem.integrable_norm_pow hp

theorem gaussianZero_integrable_nat_pow (v : NNReal) (p : ℕ) :
    Integrable (fun x : ℝ => x ^ p) (gaussianReal 0 v) := by
  apply (gaussianZero_integrable_abs_nat_pow v p).mono' (continuous_pow p).aestronglyMeasurable
  exact Eventually.of_forall fun x => by simp only [Real.norm_eq_abs, abs_pow, le_refl]

theorem gaussianZero_integral_sq (v : NNReal) :
    (∫ x : ℝ, x ^ 2 ∂(gaussianReal 0 v)) = (v : ℝ) := by
  have h := variance_fun_id_gaussianReal (μ := 0) (v := v)
  rw [variance_eq_integral measurable_id'.aemeasurable] at h
  simpa only [integral_id_gaussianReal, sub_zero] using h

end GaloisForLFunctions.HTGeometry
