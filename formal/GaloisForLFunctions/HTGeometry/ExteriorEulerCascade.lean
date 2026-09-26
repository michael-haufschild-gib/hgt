import GaloisForLFunctions.HTGeometry.ExteriorEulerPoissonBridge
import GaloisForLFunctions.HTGeometry.CirclePoissonOuterFactor

set_option autoImplicit false

/-!
# Finite Euler cascades and normalized Poisson outer factors

Exterior Euler products, reciprocal Blaschke cascades, and normalized
Poisson outer factors share one exact phase budget.  Every factor supplies
one half of the Euler speed; the remaining contribution is simultaneously
Poisson mass, all-pass delay, and squared outer-factor amplitude.
-/

namespace GaloisForLFunctions.HTGeometry

open _root_.Complex
open scoped BigOperators

noncomputable section

/-- Reciprocal exterior radii in the corpus's disk-parameter type. -/
def exteriorEulerDiskParameter (x : ℝ) : CirclePoissonParameter :=
  ⟨(exteriorEulerRadius x)⁻¹, by
    apply Metric.mem_ball.mpr
    simpa only [dist_zero_right] using norm_inv_exteriorEulerRadius_lt_one x⟩

/-- A finite product of exterior linear Euler factors. -/
def exteriorEulerCascade {n : ℕ} (x : Fin n → ℝ) (z : ℂ) : ℂ :=
  ∏ i, (1 - (exteriorEulerRadius (x i) : ℂ) * z)

theorem exteriorEulerCascade_ne_zero {n : ℕ} (x : Fin n → ℝ) (θ : ℝ) :
    exteriorEulerCascade x (Complex.exp (θ * Complex.I)) ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact exteriorEuler_factor_ne_zero (x i) θ

/-- The actual logarithmic derivative of an exterior product is the sum
of its individual radial speeds. -/
theorem re_mul_logDeriv_exteriorEulerCascade {n : ℕ} (x : Fin n → ℝ) (θ : ℝ) :
    (Complex.exp (θ * Complex.I) * logDeriv (exteriorEulerCascade x)
      (Complex.exp (θ * Complex.I))).re = ∑ i, exteriorEulerSpeed (x i) θ := by
  have hd (i : Fin n) : DifferentiableAt ℂ
      (fun z : ℂ => 1 - (exteriorEulerRadius (x i) : ℂ) * z)
      (Complex.exp (θ * Complex.I)) := by fun_prop
  unfold exteriorEulerCascade
  rw [logDeriv_prod (fun i _ => exteriorEuler_factor_ne_zero (x i) θ)
    (fun i _ => hd i), Finset.mul_sum, Complex.re_sum]
  exact Finset.sum_congr rfl fun i _ => re_mul_logDeriv_exteriorEulerFactor (x i) θ

/-- Exact conservation of the finite phase budget. -/
theorem exteriorEulerCascade_phase_budget {n : ℕ} (x : Fin n → ℝ) (θ : ℝ) :
    2 * (Complex.exp (θ * Complex.I) * logDeriv (exteriorEulerCascade x)
      (Complex.exp (θ * Complex.I))).re =
        n + ∑ i, exteriorEulerPoisson (x i) θ := by
  rw [re_mul_logDeriv_exteriorEulerCascade, Finset.mul_sum]
  simp_rw [exteriorEulerSpeed_eq_half_add_poisson,
    show ∀ p : ℝ, 2 * ((1 + p) / 2) = 1 + p by intro p; ring]
  simp [Finset.sum_add_distrib]

/-- Every nonempty exterior product has a quantitative positive phase rate. -/
theorem exteriorEulerCascade_phase_gt_half_degree {n : ℕ}
    (x : Fin (n + 1) → ℝ) (θ : ℝ) :
    (n + 1 : ℝ) / 2 <
      (Complex.exp (θ * Complex.I) * logDeriv (exteriorEulerCascade x)
        (Complex.exp (θ * Complex.I))).re := by
  have hsum : 0 < ∑ i, exteriorEulerPoisson (x i) θ :=
    Finset.sum_pos (fun i _ => exteriorEulerPoisson_pos (x i) θ) Finset.univ_nonempty
  have h := exteriorEulerCascade_phase_budget x θ
  push_cast at h
  linarith

/-- The finite exterior cascade's surplus is exactly the boundary delay of
the reciprocal stable all-pass cascade. -/
theorem exteriorEulerCascade_reciprocal_delay {n : ℕ}
    (x : Fin n → ℝ) (θ : ℝ) :
    2 * (Complex.exp (θ * Complex.I) * logDeriv (exteriorEulerCascade x)
      (Complex.exp (θ * Complex.I))).re = n +
      (Complex.exp (θ * Complex.I) * logDeriv
        (fun z : ℂ => ∏ i, (z - ((exteriorEulerRadius (x i))⁻¹ : ℂ)) /
          (1 - star ((exteriorEulerRadius (x i))⁻¹ : ℂ) * z))
        (Complex.exp (θ * Complex.I))).re := by
  rw [mul_logDeriv_finsetBlaschke_eq_sum_poissonKernel Finset.univ
    (fun i _ => norm_inv_exteriorEulerRadius_lt_one (x i))
    (Complex.norm_exp_ofReal_mul_I θ)]
  simp only [ofReal_re]
  simp_rw [poissonKernel_inv_exteriorEulerRadius]
  exact exteriorEulerCascade_phase_budget x θ

/-- The same surplus is the squared amplitude of the existing normalized
Poisson outer factor, pointwise on the boundary. -/
theorem exteriorEulerSpeed_outer_amplitude (x θ : ℝ) :
    2 * exteriorEulerSpeed x θ = 1 +
      ‖circlePoissonOuterFactor (exteriorEulerDiskParameter x) (Circle.exp θ)‖ ^ 2 := by
  rw [norm_sq_circlePoissonOuterFactor]
  change 2 * exteriorEulerSpeed x θ = 1 +
    poissonKernel 0 ((exteriorEulerRadius x)⁻¹ : ℂ) (Complex.exp (θ * Complex.I))
  rw [poissonKernel_inv_exteriorEulerRadius, exteriorEulerSpeed_eq_half_add_poisson]
  ring

/-- Finite factorization transfers the phase budget into a sum of positive
outer-factor energies. -/
theorem exteriorEulerCascade_outer_energy {n : ℕ} (x : Fin n → ℝ) (θ : ℝ) :
    2 * (Complex.exp (θ * Complex.I) * logDeriv (exteriorEulerCascade x)
      (Complex.exp (θ * Complex.I))).re = n +
        ∑ i, ‖circlePoissonOuterFactor (exteriorEulerDiskParameter (x i))
          (Circle.exp θ)‖ ^ 2 := by
  rw [re_mul_logDeriv_exteriorEulerCascade, Finset.mul_sum]
  simp_rw [exteriorEulerSpeed_outer_amplitude]
  simp [Finset.sum_add_distrib]

end

end GaloisForLFunctions.HTGeometry
