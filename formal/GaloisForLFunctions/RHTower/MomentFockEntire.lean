import GaloisForLFunctions.RHTower.MomentFockKernel
import GaloisForLFunctions.HTGeometry.MaximumTermLogarithmicDerivative

/-!
# Entire realization of radial moment Fock carriers

Every coefficient vector in a `MomentFockData` carrier defines an entire function.  The proof uses
only the square-summability of point kernels: kernel coordinates tend to zero at every radius, while
each carrier coordinate is bounded by the Hilbert norm.  The resulting entire power-series value is
exactly the bounded evaluation already constructed in `MomentFockKernel`.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-- Taylor coefficient represented by a vector in a radial moment carrier. -/
def momentFockCoefficient (d : MomentFockData) (f : MomentFock) (n : ℕ) : ℂ :=
  f n / Real.sqrt (d.weight n)

theorem entireCoeffs_momentFockCoefficient
    (d : MomentFockData) (f : MomentFock) :
    GaloisForLFunctions.HTGeometry.EntireCoeffs (momentFockCoefficient d f) := by
  intro r hr
  let k : ℕ → ℝ := fun n => ‖momentFockKernelCoeff d.weight (r : ℂ) n‖
  have hsq : Tendsto (fun n => k n ^ (2 : ℝ)) atTop (nhds 0) :=
    (d.kernel_summable (r : ℂ)).tendsto_atTop_zero
  have hk : Tendsto k atTop (nhds 0) := by
    have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hsq
    change Tendsto (fun n => Real.sqrt (k n ^ (2 : ℝ))) atTop
      (nhds (Real.sqrt 0)) at hsqrt
    have hfun : (fun n => Real.sqrt (k n ^ (2 : ℝ))) = k := by
      funext n
      rw [Real.rpow_two, Real.sqrt_sq]
      dsimp [k]
      positivity
    rw [hfun] at hsqrt
    simpa using hsqrt
  have hupperlim : Tendsto (fun n => ‖f‖ * k n) atTop (nhds 0) := by
    simpa using hk.const_mul ‖f‖
  refine squeeze_zero ?_ ?_ hupperlim
  · intro n
    positivity
  · intro n
    have hf := lp.norm_apply_le_norm (by norm_num) f n
    have hsqrt : 0 < Real.sqrt (d.weight n) := Real.sqrt_pos.2 (d.weight_pos n)
    have hkformula : k n = r ^ n / Real.sqrt (d.weight n) := by
      dsimp [k]
      simp [momentFockKernelCoeff, abs_of_pos hr, abs_of_pos hsqrt]
    rw [momentFockCoefficient, norm_div, Complex.norm_real,
      Real.norm_of_nonneg hsqrt.le]
    calc
      ‖f n‖ / Real.sqrt (d.weight n) * r ^ n =
          ‖f n‖ * (r ^ n / Real.sqrt (d.weight n)) := by ring
      _ ≤ ‖f‖ * (r ^ n / Real.sqrt (d.weight n)) :=
        mul_le_mul_of_nonneg_right hf (by positivity)
      _ = ‖f‖ * k n := by rw [hkformula]

/-- Entire function represented by a radial moment carrier vector. -/
def momentFockFunction (d : MomentFockData) (f : MomentFock) : ℂ → ℂ :=
  GaloisForLFunctions.HTGeometry.coeffFun (momentFockCoefficient d f)

theorem differentiable_momentFockFunction
    (d : MomentFockData) (f : MomentFock) :
    Differentiable ℂ (momentFockFunction d f) :=
  GaloisForLFunctions.HTGeometry.differentiable_coeffFun
    (entireCoeffs_momentFockCoefficient d f)

/-- Coefficient-series realization agrees exactly with the bounded RKHS evaluation. -/
theorem momentFockFunction_eq_evaluation
    (d : MomentFockData) (f : MomentFock) (z : ℂ) :
    momentFockFunction d f z = momentFockEvaluation d z f := by
  rw [momentFockFunction, GaloisForLFunctions.HTGeometry.coeffFun_eq_tsum,
    momentFockEvaluation_eq_tsum]
  apply tsum_congr
  intro n
  rw [momentFockCoefficient]
  ring

theorem momentFockFunction_one (d : MomentFockData) (z : ℂ) :
    momentFockFunction d (momentFockOne d) z = 1 := by
  rw [momentFockFunction_eq_evaluation]
  exact momentFockEvaluation_one d z

end

end RHTower
