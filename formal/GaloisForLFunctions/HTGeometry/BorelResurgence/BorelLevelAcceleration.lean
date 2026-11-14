import GaloisForLFunctions.HTGeometry.BorelResurgence.GaussianAcceleration
import GaloisForLFunctions.HTGeometry.BorelSeriesConvolution
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# Exact acceleration of Borel polynomials

Gaussian acceleration sends the ordinary Borel basis `x^n/n!` to
`t^(n/2)/Γ(n/2+1)`. The Gamma duplication formula cancels the ordinary factorial.
Finite Borel transforms therefore change level exactly, with no asymptotic or summability
assumption on their coefficients.
-/

open MeasureTheory Set
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- All polynomial moments of the positive-time acceleration kernel are integrable. -/
theorem integrable_gaussianAcceleration_monomial (s : ℝ) (n : ℕ) :
    IntegrableOn (fun x => gaussianAccelerationKernel (Real.exp s) x * x ^ n) (Ioi 0) := by
  have h := (integrable_rpow_mul_exp_neg_mul_sq
    (by positivity : 0 < (4 * Real.exp s)⁻¹)
    (lt_of_lt_of_le (by norm_num : (-1 : ℝ) < 0) (Nat.cast_nonneg n))).integrableOn.const_mul
      (Real.sqrt (Real.pi * Real.exp s))⁻¹
  simpa only [gaussianAccelerationKernel, Real.rpow_natCast, mul_left_comm, mul_comm,
    mul_assoc] using h

/-- The exact half-Gaussian moment with its time dependence separated. -/
theorem gaussianAcceleration_monomial (s : ℝ) (n : ℕ) :
    gaussianAcceleration (fun x => x ^ n) (Real.exp s) =
      2 ^ n * Real.exp (s * (n : ℝ) / 2) * Real.Gamma (((n : ℝ) + 1) / 2) /
        Real.sqrt Real.pi := by
  have hi := integral_rpow_mul_exp_neg_mul_rpow
    (p := 2) (q := (n : ℝ)) (b := (4 * Real.exp s)⁻¹)
    (by norm_num) (lt_of_lt_of_le (by norm_num : (-1 : ℝ) < 0) (Nat.cast_nonneg n))
    (by positivity)
  have hrate : (4 * Real.exp s)⁻¹ = Real.exp (-(Real.log 4 + s)) := by
    rw [Real.exp_neg, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
  have hlog : Real.log 4 = 2 * Real.log 2 := by
    have h := Real.log_pow (2 : ℝ) 2
    norm_num at h
    exact h
  have hpower : ((4 * Real.exp s)⁻¹) ^ (-((n : ℝ) + 1) / 2) =
      2 * 2 ^ n * Real.exp (s * (n : ℝ) / 2) * Real.exp (s / 2) := by
    rw [hrate, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    rw [show -(Real.log 4 + s) * (-((n : ℝ) + 1) / 2) =
        Real.log 2 + (n : ℝ) * Real.log 2 + s * (n : ℝ) / 2 + s / 2 by
      rw [hlog]; ring]
    rw [Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_nat_mul,
      Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have hsqrt : Real.sqrt (Real.exp s) = Real.exp (s / 2) := by
    have he : Real.exp s = Real.exp (s / 2) ^ 2 := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    rw [he, Real.sqrt_sq (Real.exp_pos _).le]
  unfold gaussianAcceleration
  simp only [gaussianAccelerationKernel]
  simp_rw [mul_assoc, mul_comm (Real.exp _)]
  rw [integral_const_mul]
  simp only [Real.rpow_natCast, Real.rpow_two] at hi
  rw [hi, hpower, Real.sqrt_mul Real.pi_pos.le, hsqrt]
  field_simp [Real.exp_ne_zero, Real.sqrt_ne_zero'.mpr Real.pi_pos]
  <;> ring

/-- The Gamma duplication identity in the normalization used by the two Borel levels. -/
theorem gamma_borel_duplication (n : ℕ) :
    Real.Gamma (((n : ℝ) + 1) / 2) * Real.Gamma ((n : ℝ) / 2 + 1) =
      (n.factorial : ℝ) / 2 ^ n * Real.sqrt Real.pi := by
  have h := Real.Gamma_mul_Gamma_add_half (((n : ℝ) + 1) / 2)
  rw [show ((n : ℝ) + 1) / 2 + 1 / 2 = (n : ℝ) / 2 + 1 by ring,
    show 2 * (((n : ℝ) + 1) / 2) = (n : ℝ) + 1 by ring,
    show 1 - ((n : ℝ) + 1) = -(n : ℝ) by ring,
    Real.Gamma_nat_eq_factorial, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
    Real.rpow_natCast] at h
  simpa only [div_eq_mul_inv] using h

/-- Ordinary divided powers accelerate exactly to the level-two Borel basis. -/
theorem gaussianAcceleration_dividedPowerFn (s : ℝ) (n : ℕ) :
    gaussianAcceleration (dividedPowerFn n) (Real.exp s) =
      Real.exp (s * (n : ℝ) / 2) / Real.Gamma ((n : ℝ) / 2 + 1) := by
  have hdiv : gaussianAcceleration (dividedPowerFn n) (Real.exp s) =
      gaussianAcceleration (fun x => x ^ n) (Real.exp s) / (n.factorial : ℝ) := by
    unfold gaussianAcceleration dividedPowerFn
    simp_rw [← mul_div_assoc]
    rw [integral_div]
  rw [hdiv, gaussianAcceleration_monomial]
  have hg : Real.Gamma ((n : ℝ) / 2 + 1) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by positivity)).ne'
  have hf : (n.factorial : ℝ) ≠ 0 := by positivity
  have hp : Real.sqrt Real.pi ≠ 0 := by positivity
  have hd := gamma_borel_duplication n
  apply (eq_div_iff hg).mpr
  field_simp [hf, hp] at hd ⊢
  linear_combination Real.exp (s * (n : ℝ) / 2) * hd

/-- Every finite Borel polynomial changes level by an exact coefficient formula. -/
theorem gaussianAcceleration_finiteBorel (s : ℝ) (S : Finset ℕ) (a : ℕ → ℝ) :
    gaussianAcceleration (fun x => ∑ n ∈ S, a n * dividedPowerFn n x) (Real.exp s) =
      ∑ n ∈ S, a n *
        (Real.exp (s * (n : ℝ) / 2) / Real.Gamma ((n : ℝ) / 2 + 1)) := by
  have hint (n : ℕ) : IntegrableOn (fun x => gaussianAccelerationKernel (Real.exp s) x *
      (a n * dividedPowerFn n x)) (Ioi 0) := by
    have h := (integrable_gaussianAcceleration_monomial s n).const_mul
      (a n / (n.factorial : ℝ))
    apply h.congr
    exact ae_of_all _ fun x => by
      unfold dividedPowerFn
      ring
  unfold gaussianAcceleration
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum S (fun n _ => hint n)]
  apply Finset.sum_congr rfl
  intro n _
  simp_rw [mul_left_comm (gaussianAccelerationKernel _ _) (a n)]
  rw [integral_const_mul]
  exact congrArg (a n * ·) (gaussianAcceleration_dividedPowerFn s n)

end

end GaloisForLFunctions.HTGeometry

#print axioms GaloisForLFunctions.HTGeometry.integrable_gaussianAcceleration_monomial
#print axioms GaloisForLFunctions.HTGeometry.gaussianAcceleration_monomial
#print axioms GaloisForLFunctions.HTGeometry.gamma_borel_duplication
#print axioms GaloisForLFunctions.HTGeometry.gaussianAcceleration_dividedPowerFn
#print axioms GaloisForLFunctions.HTGeometry.gaussianAcceleration_finiteBorel
