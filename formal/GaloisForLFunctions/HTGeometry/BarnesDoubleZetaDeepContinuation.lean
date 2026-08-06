import GaloisForLFunctions.HTGeometry.BarnesConeKernelRemainderBound
import GaloisForLFunctions.HTGeometry.BarnesDoubleZetaContinuation

/-!
# Continuation of the Barnes double zeta past `s = 0`

Subtracting one more Taylor term of the extended cone kernel,

```text
t² F(t) = 1/(omega_1 omega_2) + t A_1 + t² A_2 + t³ R(t),
```

adds the pole at `s = 0` to the two already isolated and pushes the head integral's convergence to
`Re s > -1`.  This is the range needed to reach `s = 0`, where `1/Gamma` has a simple zero that
cancels the new pole: the double zeta is regular there, and its `s`-derivative is the double gamma.
-/

open Complex Filter Set MeasureTheory
open scoped Topology BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The quadratic Taylor coefficient of the extended cone kernel: the residue of the Mellin
transform at `s = 0`. -/
def barnesConeQuadCoeff (o1 o2 x : ℂ) : ℂ :=
  analyticSlopeIter (barnesConeKernelAnalytic o1 o2 x) 0 2 0

/-- The cubic Taylor remainder of the extended cone kernel. -/
def barnesConeCubicRemainder (o1 o2 x : ℂ) : ℂ → ℂ :=
  analyticSlopeIter (barnesConeKernelAnalytic o1 o2 x) 0 3

theorem analyticAt_barnesConeCubicRemainder {o1 o2 : ℂ} (h1 : o1 ≠ 0) (h2 : o2 ≠ 0) (x : ℂ) :
    AnalyticAt ℂ (barnesConeCubicRemainder o1 o2 x) 0 :=
  analyticAt_analyticSlopeIter (analyticAt_barnesConeKernelAnalytic h1 h2 x) 3

/-- **Third-order expansion of the extended cone kernel.**  The three singular contributions to the
Mellin transform are the poles at `s = 2`, `s = 1` and `s = 0`. -/
theorem barnesConeKernelAnalytic_taylor_three (o1 o2 x z : ℂ) :
    barnesConeKernelAnalytic o1 o2 x z
      = o1⁻¹ * o2⁻¹ + z * barnesConeLinearCoeff o1 o2 x
        + z ^ 2 * barnesConeQuadCoeff o1 o2 x
        + z ^ 3 * barnesConeCubicRemainder o1 o2 x z := by
  have h := eq_taylor_add_pow_mul (barnesConeKernelAnalytic o1 o2 x) 0 z 3
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero] at h
  simp only [sub_zero, pow_zero, pow_one, one_mul, zero_add, analyticSlopeIter_zero,
    analyticSlopeIter_succ, analyticSlope_self] at h
  rw [barnesConeKernelAnalytic_zero] at h
  rw [barnesConeQuadCoeff, barnesConeCubicRemainder, barnesConeLinearCoeff]
  simp only [analyticSlopeIter_succ, analyticSlopeIter_zero, analyticSlope_self]
  linear_combination h

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem barnesConeCubicRemainder_of_ne {o1 o2 x z : ℂ} (hz : z ≠ 0) :
    barnesConeCubicRemainder o1 o2 x z
      = (barnesConeKernelAnalytic o1 o2 x z - o1⁻¹ * o2⁻¹
          - z * barnesConeLinearCoeff o1 o2 x - z ^ 2 * barnesConeQuadCoeff o1 o2 x) / z ^ 3 := by
  have hz3 : z ^ 3 ≠ 0 := pow_ne_zero 3 hz
  have h := barnesConeKernelAnalytic_taylor_three o1 o2 x z
  rw [eq_div_iff hz3]
  linear_combination -h

theorem continuousAt_barnesConeCubicRemainder_ofReal {o1 o2 : ℝ} (h1 : 0 < o1) (h2 : 0 < o2)
    (x : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    ContinuousAt (fun u : ℝ => barnesConeCubicRemainder (o1 : ℂ) (o2 : ℂ) (x : ℂ) (u : ℂ)) t := by
  have hoC1 : (o1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt h1)
  have hoC2 : (o2 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt h2)
  rcases eq_or_lt_of_le ht with h0 | h0
  · have hR : ContinuousAt (barnesConeCubicRemainder (o1 : ℂ) (o2 : ℂ) (x : ℂ))
        (((0 : ℝ) : ℂ)) := by
      rw [Complex.ofReal_zero]
      exact (analyticAt_barnesConeCubicRemainder hoC1 hoC2 (x : ℂ)).continuousAt
    have hcomp := hR.comp Complex.continuous_ofReal.continuousAt
    rw [← h0]
    simpa [Function.comp_def] using hcomp
  · have heq : (fun u : ℝ => barnesConeCubicRemainder (o1 : ℂ) (o2 : ℂ) (x : ℂ) (u : ℂ))
        =ᶠ[𝓝 t] fun u : ℝ =>
          (barnesConeKernelAnalytic (o1 : ℂ) (o2 : ℂ) (x : ℂ) (u : ℂ)
              - (o1 : ℂ)⁻¹ * (o2 : ℂ)⁻¹
              - (u : ℂ) * barnesConeLinearCoeff (o1 : ℂ) (o2 : ℂ) (x : ℂ)
              - (u : ℂ) ^ 2 * barnesConeQuadCoeff (o1 : ℂ) (o2 : ℂ) (x : ℂ)) / (u : ℂ) ^ 3 := by
      filter_upwards [Ioi_mem_nhds h0] with u hu
      exact barnesConeCubicRemainder_of_ne (Complex.ofReal_ne_zero.mpr (ne_of_gt hu))
    rw [continuousAt_congr heq]
    have hA : ContinuousAt
        (fun u : ℝ => barnesConeKernelAnalytic (o1 : ℂ) (o2 : ℂ) (x : ℂ) (u : ℂ)) t :=
      continuousAt_barnesConeKernelAnalytic_ofReal h1 h2 x ht
    refine ContinuousAt.div ?_ ((Complex.continuous_ofReal.continuousAt).pow 3)
      (pow_ne_zero 3 (Complex.ofReal_ne_zero.mpr (ne_of_gt h0)))
    exact ((hA.sub continuousAt_const).sub
      (Complex.continuous_ofReal.continuousAt.mul continuousAt_const)).sub
      (((Complex.continuous_ofReal.continuousAt).pow 2).mul continuousAt_const)

theorem continuousOn_barnesConeCubicRemainder_ofReal {o1 o2 : ℝ} (h1 : 0 < o1) (h2 : 0 < o2)
    (x : ℝ) :
    ContinuousOn (fun u : ℝ => barnesConeCubicRemainder (o1 : ℂ) (o2 : ℂ) (x : ℂ) (u : ℂ))
      (Icc 0 1) := fun _ ht =>
  (continuousAt_barnesConeCubicRemainder_ofReal h1 h2 x ht.1).continuousWithinAt

/-- **The cubic Taylor remainder of the cone kernel is bounded on the unit interval.** -/
theorem exists_bound_barnesConeCubicRemainder {o1 o2 : ℝ} (h1 : 0 < o1) (h2 : 0 < o2) (x : ℝ) :
    ∃ C : ℝ, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖barnesConeCubicRemainder (o1 : ℂ) (o2 : ℂ) (x : ℂ) (t : ℂ)‖ ≤ C :=
  isCompact_Icc.exists_bound_of_continuousOn
    (continuousOn_barnesConeCubicRemainder_ofReal h1 h2 x)

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Splitting off all three singular powers of the cone kernel.** -/
theorem barnesConeKernel_eq_three_singular {o1 o2 x : ℝ} {t : ℝ} (ht : 0 < t) :
    barnesConeKernel o1 o2 x t
      = ((o1 : ℂ)⁻¹ * (o2 : ℂ)⁻¹) * (t : ℂ) ^ (-2 : ℂ)
        + barnesConeLinearCoeff (o1 : ℂ) (o2 : ℂ) (x : ℂ) * (t : ℂ) ^ (-1 : ℂ)
        + barnesConeQuadCoeff (o1 : ℂ) (o2 : ℂ) (x : ℂ) * (t : ℂ) ^ (0 : ℂ)
        + (t : ℂ) * barnesConeCubicRemainder (o1 : ℂ) (o2 : ℂ) (x : ℂ) (t : ℂ) := by
  have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht)
  have hsq : ((t : ℂ)) ^ 2 ≠ 0 := pow_ne_zero 2 htC
  have hkey := barnesConeKernelAnalytic_ofReal o1 o2 x (ne_of_gt ht)
  have htay := barnesConeKernelAnalytic_taylor_three (o1 : ℂ) (o2 : ℂ) (x : ℂ) (t : ℂ)
  have hpow2 : ((t : ℂ)) ^ (-2 : ℂ) = (((t : ℂ)) ^ 2)⁻¹ := by
    rw [show ((-2 : ℂ)) = -(2 : ℂ) by ring, Complex.cpow_neg, Complex.cpow_two]
  have hpow1 : ((t : ℂ)) ^ (-1 : ℂ) = ((t : ℂ))⁻¹ := Complex.cpow_neg_one _
  have hpow0 : ((t : ℂ)) ^ (0 : ℂ) = 1 := Complex.cpow_zero _
  rw [hpow2, hpow1, hpow0]
  rw [hkey] at htay
  field_simp
  linear_combination htay

theorem integrableOn_cpow_mul_barnesConeCubicRemainder_Ioc {o1 o2 x : ℝ} (h1 : 0 < o1)
    (h2 : 0 < o2) {s : ℂ} (hs : -1 < s.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s + 1 - 1) *
      barnesConeCubicRemainder (o1 : ℂ) (o2 : ℂ) (x : ℂ) (t : ℂ)) (Ioc 0 1) := by
  obtain ⟨C, hC⟩ := exists_bound_barnesConeCubicRemainder h1 h2 x
  have hsub : Ioc (0 : ℝ) 1 ⊆ Ioi (0 : ℝ) := fun t ht => ht.1
  have hsubIcc : Ioc (0 : ℝ) 1 ⊆ Icc (0 : ℝ) 1 := fun t ht => ⟨ht.1.le, ht.2⟩
  have hre : (0 : ℝ) < (s + 1).re := by
    rw [Complex.add_re, Complex.one_re]
    linarith
  have hrpow : IntegrableOn (fun t : ℝ => t ^ ((s + 1).re - 1)) (Ioc 0 1) := by
    have : IntervalIntegrable (fun t : ℝ => t ^ ((s + 1).re - 1)) volume 0 1 :=
      intervalIntegral.intervalIntegrable_rpow' (by linarith)
    rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)] at this
  refine Integrable.mono' (hrpow.const_mul C)
    (aestronglyMeasurable_cpow_mul_of_continuousOn measurableSet_Ioc hsub
      ((continuousOn_barnesConeCubicRemainder_ofReal h1 h2 x).mono hsubIcc) (s + 1)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have ht0 : (0 : ℝ) < t := ht.1
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.sub_re, Complex.one_re,
    mul_comm C]
  exact mul_le_mul_of_nonneg_left (hC t (hsubIcc ht)) (Real.rpow_nonneg ht0.le _)

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

noncomputable section

set_option maxHeartbeats 800000 in
/-- **The head of the Mellin integral with all three poles made explicit.** -/
theorem integral_head_barnesConeKernel_three {o1 o2 x : ℝ} (h1 : 0 < o1) (h2 : 0 < o2)
    {s : ℂ} (hs : 2 < s.re) :
    (∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (s - 1) * barnesConeKernel o1 o2 x t)
      = ((o1 : ℂ)⁻¹ * (o2 : ℂ)⁻¹) / (s - 2)
        + barnesConeLinearCoeff (o1 : ℂ) (o2 : ℂ) (x : ℂ) / (s - 1)
        + barnesConeQuadCoeff (o1 : ℂ) (o2 : ℂ) (x : ℂ) / s
        + ∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (s + 1 - 1) *
            barnesConeCubicRemainder (o1 : ℂ) (o2 : ℂ) (x : ℂ) (t : ℂ) := by
  have hre2 : 0 < s.re + ((-2 : ℂ)).re := by simp; linarith
  have hre1 : 0 < s.re + ((-1 : ℂ)).re := by simp; linarith
  have hre0 : 0 < s.re + ((0 : ℂ)).re := by simp; linarith
  have hreR : (-1 : ℝ) < s.re := by linarith
  set A0 : ℂ := (o1 : ℂ)⁻¹ * (o2 : ℂ)⁻¹ with hA0
  set A1 : ℂ := barnesConeLinearCoeff (o1 : ℂ) (o2 : ℂ) (x : ℂ) with hA1
  set A2 : ℂ := barnesConeQuadCoeff (o1 : ℂ) (o2 : ℂ) (x : ℂ) with hA2
  have hi2 := (integrableOn_cpow_mul_cpow_Ioc (-2 : ℂ) hre2).const_mul A0
  have hi1 := (integrableOn_cpow_mul_cpow_Ioc (-1 : ℂ) hre1).const_mul A1
  have hi0 := (integrableOn_cpow_mul_cpow_Ioc (0 : ℂ) hre0).const_mul A2
  have hiR := integrableOn_cpow_mul_barnesConeCubicRemainder_Ioc (x := x) h1 h2 hreR
  have hcongr : ∀ t ∈ Ioc (0 : ℝ) 1,
      (t : ℂ) ^ (s - 1) * barnesConeKernel o1 o2 x t
        = A0 * ((t : ℂ) ^ (s - 1) * (t : ℂ) ^ (-2 : ℂ))
          + A1 * ((t : ℂ) ^ (s - 1) * (t : ℂ) ^ (-1 : ℂ))
          + A2 * ((t : ℂ) ^ (s - 1) * (t : ℂ) ^ (0 : ℂ))
          + (t : ℂ) ^ (s + 1 - 1) *
              barnesConeCubicRemainder (o1 : ℂ) (o2 : ℂ) (x : ℂ) (t : ℂ) := by
    intro t ht
    have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht.1)
    have hpow : (t : ℂ) ^ (s - 1) * (t : ℂ) = (t : ℂ) ^ (s + 1 - 1) := by
      rw [show s + 1 - 1 = (s - 1) + 1 by ring, Complex.cpow_add _ _ htC, Complex.cpow_one]
    rw [barnesConeKernel_eq_three_singular ht.1, ← hA0, ← hA1, ← hA2, ← hpow]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioc hcongr]
  have hs1 : (∫ t in Ioc (0 : ℝ) 1,
        (A0 * ((t : ℂ) ^ (s - 1) * (t : ℂ) ^ (-2 : ℂ))
            + A1 * ((t : ℂ) ^ (s - 1) * (t : ℂ) ^ (-1 : ℂ))
            + A2 * ((t : ℂ) ^ (s - 1) * (t : ℂ) ^ (0 : ℂ))
          + (t : ℂ) ^ (s + 1 - 1) *
              barnesConeCubicRemainder (o1 : ℂ) (o2 : ℂ) (x : ℂ) (t : ℂ)))
      = (∫ t in Ioc (0 : ℝ) 1,
          (A0 * ((t : ℂ) ^ (s - 1) * (t : ℂ) ^ (-2 : ℂ))
            + A1 * ((t : ℂ) ^ (s - 1) * (t : ℂ) ^ (-1 : ℂ))
            + A2 * ((t : ℂ) ^ (s - 1) * (t : ℂ) ^ (0 : ℂ))))
        + ∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (s + 1 - 1) *
            barnesConeCubicRemainder (o1 : ℂ) (o2 : ℂ) (x : ℂ) (t : ℂ) :=
    integral_add ((hi2.add hi1).add hi0) hiR
  have hs2 : (∫ t in Ioc (0 : ℝ) 1,
        (A0 * ((t : ℂ) ^ (s - 1) * (t : ℂ) ^ (-2 : ℂ))
          + A1 * ((t : ℂ) ^ (s - 1) * (t : ℂ) ^ (-1 : ℂ))
          + A2 * ((t : ℂ) ^ (s - 1) * (t : ℂ) ^ (0 : ℂ))))
      = (∫ t in Ioc (0 : ℝ) 1,
          (A0 * ((t : ℂ) ^ (s - 1) * (t : ℂ) ^ (-2 : ℂ))
            + A1 * ((t : ℂ) ^ (s - 1) * (t : ℂ) ^ (-1 : ℂ))))
        + ∫ t in Ioc (0 : ℝ) 1, A2 * ((t : ℂ) ^ (s - 1) * (t : ℂ) ^ (0 : ℂ)) :=
    integral_add (hi2.add hi1) hi0
  have hs3 : (∫ t in Ioc (0 : ℝ) 1,
        (A0 * ((t : ℂ) ^ (s - 1) * (t : ℂ) ^ (-2 : ℂ))
          + A1 * ((t : ℂ) ^ (s - 1) * (t : ℂ) ^ (-1 : ℂ))))
      = (∫ t in Ioc (0 : ℝ) 1, A0 * ((t : ℂ) ^ (s - 1) * (t : ℂ) ^ (-2 : ℂ)))
        + ∫ t in Ioc (0 : ℝ) 1, A1 * ((t : ℂ) ^ (s - 1) * (t : ℂ) ^ (-1 : ℂ)) :=
    integral_add hi2 hi1
  rw [hs1, hs2, hs3, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_cpow_mul_cpow_Ioc (-2 : ℂ) hre2, integral_cpow_mul_cpow_Ioc (-1 : ℂ) hre1,
    integral_cpow_mul_cpow_Ioc (0 : ℂ) hre0,
    show s + (-2 : ℂ) = s - 2 by ring, show s + (-1 : ℂ) = s - 1 by ring,
    show s + (0 : ℂ) = s by ring]
  ring

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

noncomputable section

set_option maxHeartbeats 800000 in
/-- **Meromorphic continuation of the Barnes double zeta past `s = 0`.**  Subtracting the three
singular powers of the cone kernel writes `Gamma(s) zeta_2(s,x)` as three explicit simple poles plus
two integrals, the head convergent for `Re s > -1` and the tail for every `Re s > 0`. -/
theorem Gamma_mul_barnesDoubleZeta_eq_continuation_three {o1 o2 x : ℝ} (h1 : 0 < o1) (h2 : 0 < o2)
    (hx : 0 < x) {s : ℂ} (hs : 2 < s.re) :
    Complex.Gamma s * barnesDoubleZeta o1 o2 s (x : ℂ)
      = ((o1 : ℂ)⁻¹ * (o2 : ℂ)⁻¹) / (s - 2)
        + barnesConeLinearCoeff (o1 : ℂ) (o2 : ℂ) (x : ℂ) / (s - 1)
        + barnesConeQuadCoeff (o1 : ℂ) (o2 : ℂ) (x : ℂ) / s
        + (∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (s + 1 - 1) *
            barnesConeCubicRemainder (o1 : ℂ) (o2 : ℂ) (x : ℂ) (t : ℂ))
        + ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (s - 1) * barnesConeKernel o1 o2 x t := by
  have hs0 : 0 < s.re := by linarith
  have hIoc := integrableOn_cpow_mul_barnesConeKernel_Ioc (x := x) h1 h2 hs
  have hIoi := integrableOn_cpow_mul_barnesConeKernel_Ioi_one h1 h2 hx hs0
  have hdisj : Disjoint (Ioc (0 : ℝ) 1) (Ioi (1 : ℝ)) :=
    Set.disjoint_left.mpr fun t ht ht' => absurd ht.2 (not_le.mpr ht')
  rw [Gamma_mul_barnesDoubleZeta_eq_mellin h1 h2 hx hs, mellin]
  simp only [smul_eq_mul]
  rw [← Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1),
    setIntegral_union hdisj measurableSet_Ioi hIoc hIoi,
    integral_head_barnesConeKernel_three h1 h2 hs]

end

end GaloisForLFunctions.HTGeometry
