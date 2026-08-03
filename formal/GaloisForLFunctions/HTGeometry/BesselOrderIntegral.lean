import Mathlib

/-!
# Modified Bessel K as an entire function of its order

For `s > 0` we define the order-variable carrier directly by the Schlaefli integral

`K_s(ν) = ∫₀∞ exp (-s cosh t) cosh (ν t) dt`.

This file establishes absolute convergence, complex differentiability under the integral,
entire order dependence, and reflection in the order.  The recurrence and real positivity are
proved in the companion recurrence file.
-/

open Filter MeasureTheory Set Topology
open scoped ComplexConjugate

namespace GaloisForLFunctions
namespace HTGeometry

noncomputable section

/-- The Schlaefli integrand for modified Bessel `K`, with fixed positive real argument. -/
def besselOrderKernel (s : ℝ) (ν : ℂ) (t : ℝ) : ℂ :=
  Complex.exp (-(s : ℂ) * Complex.cosh (t : ℂ)) *
    Complex.cosh (ν * (t : ℂ))

/-- Order derivative of the Schlaefli integrand. -/
def besselOrderKernelDeriv (s : ℝ) (ν : ℂ) (t : ℝ) : ℂ :=
  Complex.exp (-(s : ℂ) * Complex.cosh (t : ℂ)) *
    ((t : ℂ) * Complex.sinh (ν * (t : ℂ)))

/-- Order-variable modified Bessel `K`, defined without an external special-function axiom. -/
def modifiedBesselKOrder (s : ℝ) (ν : ℂ) : ℂ :=
  ∫ t : ℝ in Ioi 0, besselOrderKernel s ν t

private theorem sq_div_four_le_cosh {t : ℝ} (ht : 0 ≤ t) :
    t ^ 2 / 4 ≤ Real.cosh t := by
  have h := Real.pow_div_factorial_le_exp t ht 2
  norm_num [Nat.factorial] at h
  rw [Real.cosh_eq]
  nlinarith [Real.exp_pos (-t)]

private theorem young_linear_le_quadratic (s R t : ℝ) (hs : 0 < s) :
    R * t ≤ s * t ^ 2 / 8 + 2 * R ^ 2 / s := by
  rw [← mul_le_mul_iff_left₀ hs, add_mul]
  field_simp [hs.ne']
  nlinarith [sq_nonneg (s * t - 4 * R)]

theorem bessel_exponent_bound (s R : ℝ) {t : ℝ} (hs : 0 < s) (ht : 0 ≤ t) :
    -s * Real.cosh t + R * t ≤ 2 * R ^ 2 / s - s / 8 * t ^ 2 := by
  have hc := sq_div_four_le_cosh ht
  have hy := young_linear_le_quadratic s R t hs
  nlinarith

/-- Uniform exponential bound for complex hyperbolic cosine. -/
theorem norm_complex_cosh_le_exp_norm (z : ℂ) :
    ‖Complex.cosh z‖ ≤ Real.exp ‖z‖ := by
  rw [Complex.cosh]
  calc
    ‖(Complex.exp z + Complex.exp (-z)) / 2‖ ≤
        (‖Complex.exp z‖ + ‖Complex.exp (-z)‖) / 2 := by
          rw [norm_div, show ‖(2 : ℂ)‖ = 2 by norm_num]
          exact div_le_div_of_nonneg_right (norm_add_le _ _) (by norm_num)
    _ ≤ (Real.exp ‖z‖ + Real.exp ‖-z‖) / 2 := by
      gcongr <;> exact Complex.norm_exp_le_exp_norm _
    _ = Real.exp ‖z‖ := by simp

/-- Uniform exponential bound for complex hyperbolic sine. -/
theorem norm_complex_sinh_le_exp_norm (z : ℂ) :
    ‖Complex.sinh z‖ ≤ Real.exp ‖z‖ := by
  rw [Complex.sinh]
  calc
    ‖(Complex.exp z - Complex.exp (-z)) / 2‖ ≤
        (‖Complex.exp z‖ + ‖Complex.exp (-z)‖) / 2 := by
          rw [norm_div, show ‖(2 : ℂ)‖ = 2 by norm_num]
          exact div_le_div_of_nonneg_right (norm_sub_le _ _) (by norm_num)
    _ ≤ (Real.exp ‖z‖ + Real.exp ‖-z‖) / 2 := by
      gcongr <;> exact Complex.norm_exp_le_exp_norm _
    _ = Real.exp ‖z‖ := by simp

/-- Gaussian majorant for the Schlaefli kernel on an order-norm ball. -/
theorem norm_besselOrderKernel_le
    {s R t : ℝ} {ν : ℂ} (hs : 0 < s) (ht : 0 ≤ t) (hν : ‖ν‖ ≤ R) :
    ‖besselOrderKernel s ν t‖ ≤
      Real.exp (2 * R ^ 2 / s) * Real.exp (-(s / 8) * t ^ 2) := by
  have hνt : ‖ν * (t : ℂ)‖ ≤ R * t := by
    simpa [norm_mul, abs_of_nonneg ht] using mul_le_mul_of_nonneg_right hν ht
  have hexp :
      ‖Complex.exp (-(s : ℂ) * Complex.cosh (t : ℂ))‖ =
        Real.exp (-s * Real.cosh t) := by
    rw [Complex.norm_exp]
    simp [← Complex.ofReal_cosh]
  calc
    ‖besselOrderKernel s ν t‖ =
        Real.exp (-s * Real.cosh t) * ‖Complex.cosh (ν * (t : ℂ))‖ := by
          rw [besselOrderKernel, norm_mul, hexp]
    _ ≤ Real.exp (-s * Real.cosh t) * Real.exp ‖ν * (t : ℂ)‖ :=
      mul_le_mul_of_nonneg_left (norm_complex_cosh_le_exp_norm _) (Real.exp_nonneg _)
    _ = Real.exp (-s * Real.cosh t + ‖ν * (t : ℂ)‖) := by
      rw [Real.exp_add]
    _ ≤ Real.exp (2 * R ^ 2 / s - s / 8 * t ^ 2) := by
      gcongr
      calc
        -s * Real.cosh t + ‖ν * (t : ℂ)‖ ≤
            -s * Real.cosh t + R * t := by linarith
        _ ≤ 2 * R ^ 2 / s - s / 8 * t ^ 2 :=
          bessel_exponent_bound s R hs ht
    _ = Real.exp (2 * R ^ 2 / s) * Real.exp (-(s / 8) * t ^ 2) := by
      rw [sub_eq_add_neg, neg_mul, Real.exp_add]

/-- Gaussian-times-linear majorant for the order derivative. -/
theorem norm_besselOrderKernelDeriv_le
    {s R t : ℝ} {ν : ℂ} (hs : 0 < s) (ht : 0 ≤ t) (hν : ‖ν‖ ≤ R) :
    ‖besselOrderKernelDeriv s ν t‖ ≤
      Real.exp (2 * R ^ 2 / s) *
        (|t| * Real.exp (-(s / 8) * t ^ 2)) := by
  have hνt : ‖ν * (t : ℂ)‖ ≤ R * t := by
    simpa [norm_mul, abs_of_nonneg ht] using mul_le_mul_of_nonneg_right hν ht
  have hexp :
      ‖Complex.exp (-(s : ℂ) * Complex.cosh (t : ℂ))‖ =
        Real.exp (-s * Real.cosh t) := by
    rw [Complex.norm_exp]
    simp [← Complex.ofReal_cosh]
  calc
    ‖besselOrderKernelDeriv s ν t‖ =
        Real.exp (-s * Real.cosh t) *
          (|t| * ‖Complex.sinh (ν * (t : ℂ))‖) := by
            rw [besselOrderKernelDeriv, norm_mul, norm_mul, hexp, Complex.norm_real,
              Real.norm_eq_abs]
    _ ≤ Real.exp (-s * Real.cosh t) *
          (|t| * Real.exp ‖ν * (t : ℂ)‖) := by
      gcongr
      exact norm_complex_sinh_le_exp_norm _
    _ = |t| * Real.exp (-s * Real.cosh t + ‖ν * (t : ℂ)‖) := by
      rw [Real.exp_add]
      ring
    _ ≤ |t| * Real.exp (2 * R ^ 2 / s - s / 8 * t ^ 2) := by
      gcongr
      calc
        -s * Real.cosh t + ‖ν * (t : ℂ)‖ ≤
            -s * Real.cosh t + R * t := by linarith
        _ ≤ 2 * R ^ 2 / s - s / 8 * t ^ 2 :=
          bessel_exponent_bound s R hs ht
    _ = Real.exp (2 * R ^ 2 / s) *
          (|t| * Real.exp (-(s / 8) * t ^ 2)) := by
      rw [sub_eq_add_neg, neg_mul, Real.exp_add]
      ring

theorem integrableOn_besselOrderKernel {s : ℝ} (hs : 0 < s) (ν : ℂ) :
    IntegrableOn (besselOrderKernel s ν) (Ioi 0) := by
  let B : ℝ → ℝ := fun t =>
    Real.exp (2 * ‖ν‖ ^ 2 / s) * Real.exp (-(s / 8) * t ^ 2)
  have hB : Integrable B := by
    simpa [B] using
      (integrable_exp_neg_mul_sq (div_pos hs (by norm_num : (0 : ℝ) < 8))).const_mul
        (Real.exp (2 * ‖ν‖ ^ 2 / s))
  apply hB.integrableOn.mono'
  · unfold besselOrderKernel
    fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact norm_besselOrderKernel_le hs ht.le le_rfl

private theorem integrableOn_besselOrderKernelDeriv_bound
    {s R : ℝ} (hs : 0 < s) :
    IntegrableOn (fun t : ℝ =>
      Real.exp (2 * R ^ 2 / s) *
        (|t| * Real.exp (-(s / 8) * t ^ 2))) (Ioi 0) := by
  have h := (integrable_mul_exp_neg_mul_sq
    (div_pos hs (by norm_num : (0 : ℝ) < 8))).norm.const_mul
      (Real.exp (2 * R ^ 2 / s))
  apply h.integrableOn.congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]

theorem hasDerivAt_modifiedBesselKOrder {s : ℝ} (hs : 0 < s) (ν : ℂ) :
    HasDerivAt (modifiedBesselKOrder s)
      (∫ t : ℝ in Ioi 0, besselOrderKernelDeriv s ν t) ν := by
  let R : ℝ := ‖ν‖ + 1
  let S : Set ℂ := Metric.closedBall ν 1
  let bound : ℝ → ℝ := fun t =>
    Real.exp (2 * R ^ 2 / s) *
      (|t| * Real.exp (-(s / 8) * t ^ 2))
  have hS : S ∈ 𝓝 ν :=
    Metric.closedBall_mem_nhds ν (by norm_num : (0 : ℝ) < 1)
  have hmeas : ∀ᶠ z in 𝓝 ν,
      AEStronglyMeasurable (besselOrderKernel s z) (volume.restrict (Ioi 0)) :=
    Filter.Eventually.of_forall fun _ => by
      unfold besselOrderKernel
      fun_prop
  have hint : Integrable (besselOrderKernel s ν) (volume.restrict (Ioi 0)) :=
    integrableOn_besselOrderKernel hs ν
  have hderivmeas :
      AEStronglyMeasurable (besselOrderKernelDeriv s ν) (volume.restrict (Ioi 0)) := by
    unfold besselOrderKernelDeriv
    fun_prop
  have hbound : ∀ᵐ t ∂volume.restrict (Ioi 0),
      ∀ z ∈ S, ‖besselOrderKernelDeriv s z t‖ ≤ bound t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht z hz
    have hnorm : ‖z‖ ≤ R := by
      have hdist : dist z ν ≤ 1 := hz
      have hdist' : ‖z - ν‖ ≤ 1 := by simpa [dist_eq_norm] using hdist
      calc
        ‖z‖ = ‖ν + (z - ν)‖ := by congr 1; ring
        _ ≤ ‖ν‖ + ‖z - ν‖ := norm_add_le _ _
        _ ≤ ‖ν‖ + 1 := by linarith
        _ = R := rfl
    exact norm_besselOrderKernelDeriv_le hs ht.le hnorm
  have hboundint : Integrable bound (volume.restrict (Ioi 0)) :=
    integrableOn_besselOrderKernelDeriv_bound hs
  have hdiff : ∀ᵐ t ∂volume.restrict (Ioi 0),
      ∀ z ∈ S, HasDerivAt (fun w : ℂ => besselOrderKernel s w t)
        (besselOrderKernelDeriv s z t) z := by
    filter_upwards with t z hz
    have hcosh := Complex.hasDerivAt_cosh (z * (t : ℂ))
    have hcomp := hcosh.comp z ((hasDerivAt_id z).mul_const (t : ℂ))
    simpa [besselOrderKernel, besselOrderKernelDeriv, mul_assoc, mul_comm, mul_left_comm] using
      hcomp.const_mul (Complex.exp (-(s : ℂ) * Complex.cosh (t : ℂ)))
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    hS hmeas hint hderivmeas hbound hboundint hdiff).2

theorem differentiable_modifiedBesselKOrder {s : ℝ} (hs : 0 < s) :
    Differentiable ℂ (modifiedBesselKOrder s) :=
  fun ν => (hasDerivAt_modifiedBesselKOrder hs ν).differentiableAt

/-- The Schlaefli carrier is entire in its complex order. -/
theorem analyticAt_modifiedBesselKOrder {s : ℝ} (hs : 0 < s) (ν : ℂ) :
    AnalyticAt ℂ (modifiedBesselKOrder s) ν :=
  (differentiable_modifiedBesselKOrder hs).analyticAt ν

theorem analyticOnNhd_modifiedBesselKOrder {s : ℝ} (hs : 0 < s) :
    AnalyticOnNhd ℂ (modifiedBesselKOrder s) Set.univ :=
  (differentiable_modifiedBesselKOrder hs).differentiableOn.analyticOnNhd isOpen_univ

/-- Reflection in the order, directly from evenness of `cosh`. -/
theorem modifiedBesselKOrder_neg (s : ℝ) (ν : ℂ) :
    modifiedBesselKOrder s (-ν) = modifiedBesselKOrder s ν := by
  apply integral_congr_ae
  filter_upwards with t
  simp only [besselOrderKernel, neg_mul, Complex.cosh_neg]

/-- Conjugation equivariance of the Schlaefli carrier. -/
theorem modifiedBesselKOrder_conj (s : ℝ) (ν : ℂ) :
    modifiedBesselKOrder s (conj ν) = conj (modifiedBesselKOrder s ν) := by
  rw [modifiedBesselKOrder, modifiedBesselKOrder, ← integral_conj]
  apply integral_congr_ae
  filter_upwards with t
  simp [besselOrderKernel, map_mul, ← Complex.ofReal_cosh,
    ← Complex.exp_conj, ← Complex.cosh_conj]

end

end HTGeometry
end GaloisForLFunctions
