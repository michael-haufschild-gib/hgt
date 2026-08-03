import GaloisForLFunctions.HTGeometry.BesselOrderIntegral

/-!
# Modified-Bessel order recurrence and positivity

This file completes the elementary special-function interface for the Schlaefli carrier:

* strict positivity at every real order;
* the exact complex order recurrence
  `K (ν+1) = K (ν-1) + (2ν/s) K ν`.

The recurrence is proved from the defining integral by an improper integration-by-parts
argument.  No external Bessel-function identity is assumed.
-/

open Filter MeasureTheory Set Topology

namespace GaloisForLFunctions
namespace HTGeometry

noncomputable section

/-- Real Schlaefli integrand. -/
def realBesselOrderKernel (s x t : ℝ) : ℝ :=
  Real.exp (-s * Real.cosh t) * Real.cosh (x * t)

/-- Real order-variable carrier, used to expose positivity. -/
def realModifiedBesselKOrder (s x : ℝ) : ℝ :=
  ∫ t : ℝ in Ioi 0, realBesselOrderKernel s x t

theorem integrableOn_realBesselOrderKernel {s : ℝ} (hs : 0 < s) (x : ℝ) :
    IntegrableOn (realBesselOrderKernel s x) (Ioi 0) := by
  change Integrable (realBesselOrderKernel s x) (volume.restrict (Ioi 0))
  have hc : Integrable (besselOrderKernel s (x : ℂ)) (volume.restrict (Ioi 0)) :=
    integrableOn_besselOrderKernel hs (x : ℂ)
  refine MeasureTheory.Integrable.mono hc ?_ ?_
  · unfold realBesselOrderKernel
    fun_prop
  · filter_upwards with t
    have heq :
        ((realBesselOrderKernel s x t : ℝ) : ℂ) =
          besselOrderKernel s (x : ℂ) t := by
      simp [realBesselOrderKernel, besselOrderKernel, ← Complex.ofReal_cosh,
        Complex.ofReal_exp]
      rw [← Complex.ofReal_mul, ← Complex.ofReal_cosh]
    simpa [← heq, Real.norm_eq_abs]

theorem modifiedBesselKOrder_ofReal {s : ℝ} (hs : 0 < s) (x : ℝ) :
    modifiedBesselKOrder s (x : ℂ) = (realModifiedBesselKOrder s x : ℂ) := by
  have hint := integrableOn_realBesselOrderKernel hs x
  have hmap := Complex.ofRealCLM.integral_comp_comm hint
  rw [modifiedBesselKOrder, realModifiedBesselKOrder]
  calc
    ∫ t : ℝ in Ioi 0, besselOrderKernel s (x : ℂ) t =
        ∫ t : ℝ in Ioi 0, ((realBesselOrderKernel s x t : ℝ) : ℂ) := by
          apply integral_congr_ae
          filter_upwards with t
          simp [realBesselOrderKernel, besselOrderKernel, ← Complex.ofReal_cosh,
            Complex.ofReal_exp]
          rw [← Complex.ofReal_mul, ← Complex.ofReal_cosh]
    _ = (∫ t : ℝ in Ioi 0, realBesselOrderKernel s x t : ℝ) := by
      simpa only [Complex.ofRealCLM_apply] using hmap

theorem realBesselOrderKernel_pos (s x t : ℝ) :
    0 < realBesselOrderKernel s x t :=
  mul_pos (Real.exp_pos _) (Real.cosh_pos _)

/-- Strict positivity of the real-order Schlaefli integral. -/
theorem realModifiedBesselKOrder_pos {s : ℝ} (hs : 0 < s) (x : ℝ) :
    0 < realModifiedBesselKOrder s x := by
  let f : ℝ → ℝ := realBesselOrderKernel s x
  have hfint : IntegrableOn f (Ioi 0) := integrableOn_realBesselOrderKernel hs x
  apply (setIntegral_pos_iff_support_of_nonneg_ae
    (Filter.Eventually.of_forall fun t => (realBesselOrderKernel_pos s x t).le) hfint).2
  have hsupp : Function.support f ∩ Ioi 0 = Ioi 0 := by
    ext t
    simp only [mem_inter_iff, Function.mem_support, mem_Ioi]
    constructor
    · exact fun h => h.2
    · intro ht
      exact ⟨(realBesselOrderKernel_pos s x t).ne', ht⟩
  rw [hsupp]
  simp

theorem modifiedBesselKOrder_real_pos {s : ℝ} (hs : 0 < s) (x : ℝ) :
    0 < (modifiedBesselKOrder s (x : ℂ)).re := by
  rw [modifiedBesselKOrder_ofReal hs]
  simpa using realModifiedBesselKOrder_pos hs x

/-! ## Improper integration by parts -/

/-- Cross term in the order recurrence. -/
def besselOrderCrossKernel (s : ℝ) (ν : ℂ) (t : ℝ) : ℂ :=
  Complex.exp (-(s : ℂ) * Complex.cosh (t : ℂ)) *
    (Complex.sinh (t : ℂ) * Complex.sinh (ν * (t : ℂ)))

/-- Boundary function whose derivative produces the recurrence integral. -/
def besselOrderRecurrenceBoundary (s : ℝ) (ν : ℂ) (t : ℝ) : ℂ :=
  Complex.exp (-(s : ℂ) * Complex.cosh (t : ℂ)) *
    Complex.sinh (ν * (t : ℂ))

/-- Explicit derivative of the recurrence boundary function. -/
def besselOrderRecurrenceBoundaryDeriv (s : ℝ) (ν : ℂ) (t : ℝ) : ℂ :=
  -(s : ℂ) * besselOrderCrossKernel s ν t +
    ν * besselOrderKernel s ν t

private theorem norm_besselOrderCrossKernel_le
    {s R t : ℝ} {ν : ℂ} (hs : 0 < s) (ht : 0 ≤ t)
    (hν : ‖ν‖ + 1 ≤ R) :
    ‖besselOrderCrossKernel s ν t‖ ≤
      Real.exp (2 * R ^ 2 / s) * Real.exp (-(s / 8) * t ^ 2) := by
  have htcomplex : ‖(t : ℂ)‖ = t := by simp [abs_of_nonneg ht]
  have hνt : ‖ν * (t : ℂ)‖ ≤ ‖ν‖ * t := by
    rw [norm_mul, htcomplex]
  have hsum : ‖(t : ℂ)‖ + ‖ν * (t : ℂ)‖ ≤ R * t := by
    rw [htcomplex]
    nlinarith [norm_nonneg ν]
  have hexp :
      ‖Complex.exp (-(s : ℂ) * Complex.cosh (t : ℂ))‖ =
        Real.exp (-s * Real.cosh t) := by
    rw [Complex.norm_exp]
    simp [← Complex.ofReal_cosh]
  calc
    ‖besselOrderCrossKernel s ν t‖ =
        Real.exp (-s * Real.cosh t) *
          (‖Complex.sinh (t : ℂ)‖ * ‖Complex.sinh (ν * (t : ℂ))‖) := by
            rw [besselOrderCrossKernel, norm_mul, norm_mul, hexp]
    _ ≤ Real.exp (-s * Real.cosh t) *
          (Real.exp ‖(t : ℂ)‖ * Real.exp ‖ν * (t : ℂ)‖) := by
      gcongr
      · exact norm_complex_sinh_le_exp_norm _
      · exact norm_complex_sinh_le_exp_norm _
    _ = Real.exp (-s * Real.cosh t +
          (‖(t : ℂ)‖ + ‖ν * (t : ℂ)‖)) := by
      rw [Real.exp_add, Real.exp_add]
    _ ≤ Real.exp (2 * R ^ 2 / s - s / 8 * t ^ 2) := by
      gcongr
      have hbase := bessel_exponent_bound s R hs ht
      nlinarith
    _ = Real.exp (2 * R ^ 2 / s) * Real.exp (-(s / 8) * t ^ 2) := by
      rw [sub_eq_add_neg, neg_mul, Real.exp_add]

private theorem integrableOn_besselOrderCrossKernel
    {s : ℝ} (hs : 0 < s) (ν : ℂ) :
    IntegrableOn (besselOrderCrossKernel s ν) (Ioi 0) := by
  let R : ℝ := ‖ν‖ + 1
  let B : ℝ → ℝ := fun t =>
    Real.exp (2 * R ^ 2 / s) * Real.exp (-(s / 8) * t ^ 2)
  have hB : Integrable B := by
    simpa [B] using
      (integrable_exp_neg_mul_sq (div_pos hs (by norm_num : (0 : ℝ) < 8))).const_mul
        (Real.exp (2 * R ^ 2 / s))
  apply hB.integrableOn.mono'
  · unfold besselOrderCrossKernel
    fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact norm_besselOrderCrossKernel_le hs ht.le le_rfl

section RecurrenceDerivative

local instance : NormedSpace ℝ ℂ := NormedAlgebra.toNormedSpace

private theorem hasDerivAt_besselOrderRecurrenceBoundary
    (s : ℝ) (ν : ℂ) (t : ℝ) :
    HasDerivAt (besselOrderRecurrenceBoundary s ν)
      (besselOrderRecurrenceBoundaryDeriv s ν t) t := by
  have hofReal : HasDerivAt (fun u : ℝ => (u : ℂ)) 1 t :=
    (hasDerivAt_id t).ofReal_comp
  have hcosh : HasDerivAt (fun u : ℝ => Complex.cosh (u : ℂ))
      (Complex.sinh (t : ℂ)) t := by
    simpa [Function.comp_def] using
      (Complex.hasDerivAt_cosh (t : ℂ)).comp t hofReal
  have hexp : HasDerivAt
      (fun u : ℝ => Complex.exp (-(s : ℂ) * Complex.cosh (u : ℂ)))
      (Complex.exp (-(s : ℂ) * Complex.cosh (t : ℂ)) *
        (-(s : ℂ) * Complex.sinh (t : ℂ))) t := by
    convert ((hcosh.const_mul (-(s : ℂ))).cexp) using 1 <;> ring
  have hsinh : HasDerivAt (fun u : ℝ => Complex.sinh (ν * (u : ℂ)))
      (Complex.cosh (ν * (t : ℂ)) * ν) t := by
    have hlin : HasDerivAt (fun u : ℝ => ν * (u : ℂ)) ν t := by
      simpa using hofReal.const_mul ν
    exact (Complex.hasDerivAt_sinh (ν * (t : ℂ))).comp t hlin
  have hmul : HasDerivAt (besselOrderRecurrenceBoundary s ν)
      (Complex.exp (-(s : ℂ) * Complex.cosh (t : ℂ)) *
          (-(s : ℂ) * Complex.sinh (t : ℂ)) * Complex.sinh (ν * (t : ℂ)) +
        Complex.exp (-(s : ℂ) * Complex.cosh (t : ℂ)) *
          (Complex.cosh (ν * (t : ℂ)) * ν)) t := by
    simpa only [besselOrderRecurrenceBoundary, Pi.mul_apply] using hexp.mul hsinh
  apply hmul.congr_deriv
  unfold besselOrderRecurrenceBoundaryDeriv besselOrderCrossKernel besselOrderKernel
  ring

private theorem integrableOn_besselOrderRecurrenceBoundaryDeriv
    {s : ℝ} (hs : 0 < s) (ν : ℂ) :
    IntegrableOn (besselOrderRecurrenceBoundaryDeriv s ν) (Ioi 0) := by
  apply Integrable.add
  · exact (integrableOn_besselOrderCrossKernel hs ν).const_mul _
  · exact (integrableOn_besselOrderKernel hs ν).const_mul _

private theorem norm_besselOrderRecurrenceBoundary_le
    {s R t : ℝ} {ν : ℂ} (hs : 0 < s) (ht : 0 ≤ t) (hν : ‖ν‖ ≤ R) :
    ‖besselOrderRecurrenceBoundary s ν t‖ ≤
      Real.exp (2 * R ^ 2 / s) * Real.exp (-(s / 8) * t ^ 2) := by
  have hνt : ‖ν * (t : ℂ)‖ ≤ R * t := by
    simpa [norm_mul, abs_of_nonneg ht] using mul_le_mul_of_nonneg_right hν ht
  have hexp :
      ‖Complex.exp (-(s : ℂ) * Complex.cosh (t : ℂ))‖ =
        Real.exp (-s * Real.cosh t) := by
    rw [Complex.norm_exp]
    simp [← Complex.ofReal_cosh]
  calc
    ‖besselOrderRecurrenceBoundary s ν t‖ =
        Real.exp (-s * Real.cosh t) * ‖Complex.sinh (ν * (t : ℂ))‖ := by
          rw [besselOrderRecurrenceBoundary, norm_mul, hexp]
    _ ≤ Real.exp (-s * Real.cosh t) * Real.exp ‖ν * (t : ℂ)‖ :=
      mul_le_mul_of_nonneg_left (norm_complex_sinh_le_exp_norm _) (Real.exp_nonneg _)
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

private theorem tendsto_besselOrderRecurrenceBoundary_atTop
    {s : ℝ} (hs : 0 < s) (ν : ℂ) :
    Tendsto (besselOrderRecurrenceBoundary s ν) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  let B : ℝ → ℝ := fun t =>
    Real.exp (2 * ‖ν‖ ^ 2 / s) * Real.exp (-(s / 8) * t ^ 2)
  have hB : Tendsto B atTop (𝓝 0) := by
    have hquad : Tendsto (fun t : ℝ => -(s / 8) * t ^ 2) atTop atBot :=
      (tendsto_pow_atTop (α := ℝ) two_ne_zero).const_mul_atTop_of_neg
        (neg_neg_iff_pos.mpr (div_pos hs (by norm_num)))
    simpa [B, Function.comp_def] using
      (Real.tendsto_exp_atBot.comp hquad).const_mul
        (Real.exp (2 * ‖ν‖ ^ 2 / s))
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun _ => norm_nonneg _
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact norm_besselOrderRecurrenceBoundary_le (ν := ν) (R := ‖ν‖) hs ht le_rfl
  · exact hB

private theorem integral_besselOrderRecurrenceBoundaryDeriv_eq_zero
    {s : ℝ} (hs : 0 < s) (ν : ℂ) :
    ∫ t : ℝ in Ioi 0, besselOrderRecurrenceBoundaryDeriv s ν t = 0 := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun t _ => hasDerivAt_besselOrderRecurrenceBoundary s ν t)
    (integrableOn_besselOrderRecurrenceBoundaryDeriv hs ν)
    (tendsto_besselOrderRecurrenceBoundary_atTop hs ν)
  simpa [besselOrderRecurrenceBoundary] using h

end RecurrenceDerivative

private theorem integral_besselOrderCrossKernel_eq
    {s : ℝ} (hs : 0 < s) (ν : ℂ) :
    ∫ t : ℝ in Ioi 0, besselOrderCrossKernel s ν t =
      (ν / s) * modifiedBesselKOrder s ν := by
  change (∫ t : ℝ in Ioi 0, besselOrderCrossKernel s ν t) =
    (ν / s) * ∫ t : ℝ in Ioi 0, besselOrderKernel s ν t
  have hzero := integral_besselOrderRecurrenceBoundaryDeriv_eq_zero hs ν
  have hcross := integrableOn_besselOrderCrossKernel hs ν
  have hkernel := integrableOn_besselOrderKernel hs ν
  change (∫ t : ℝ in Ioi 0,
    -(s : ℂ) * besselOrderCrossKernel s ν t +
      ν * besselOrderKernel s ν t) = 0 at hzero
  rw [integral_add (hcross.const_mul _) (hkernel.const_mul _),
    integral_const_mul, integral_const_mul] at hzero
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  field_simp [hsC]
  linear_combination -hzero

/-- **Exact order recurrence**, proved from the Schlaefli integral. -/
theorem modifiedBesselKOrder_add_one
    {s : ℝ} (hs : 0 < s) (ν : ℂ) :
    modifiedBesselKOrder s (ν + 1) =
      modifiedBesselKOrder s (ν - 1) +
        (2 * ν / s) * modifiedBesselKOrder s ν := by
  have hp := integrableOn_besselOrderKernel hs (ν + 1)
  have hm := integrableOn_besselOrderKernel hs (ν - 1)
  rw [modifiedBesselKOrder, modifiedBesselKOrder, modifiedBesselKOrder]
  apply (sub_eq_iff_eq_add').mp
  rw [← integral_sub hp hm]
  rw [show (∫ t : ℝ in Ioi 0,
      (besselOrderKernel s (ν + 1) t - besselOrderKernel s (ν - 1) t)) =
      2 * ∫ t : ℝ in Ioi 0, besselOrderCrossKernel s ν t by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with t
    simp only [besselOrderKernel, besselOrderCrossKernel]
    rw [add_mul, sub_mul, Complex.cosh_add, Complex.cosh_sub]
    simp only [one_mul]
    ring]
  rw [integral_besselOrderCrossKernel_eq hs, modifiedBesselKOrder]
  ring

end

end HTGeometry
end GaloisForLFunctions
