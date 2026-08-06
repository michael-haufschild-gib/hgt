import GaloisForLFunctions.HTGeometry.BarnesConeKernelRemainderBound
import GaloisForLFunctions.HTGeometry.BarnesMellinRepresentation
import Mathlib.Analysis.MellinTransform

/-!
# Meromorphic continuation of the Barnes double zeta past its abscissa

Splitting the Mellin integral at `t = 1` separates the two sources of divergence.  The tail is
absolutely convergent for every `Re s > 0` because the cone kernel decays like `e^(-xt)`.  On the
head the kernel is replaced by its singular expansion

```text
F(t) = 1/(omega_1 omega_2) t^(-2) + A_1 t^(-1) + R(t),
```

whose two power terms integrate to the explicit simple poles `1/(s-2)` and `1/(s-1)` and whose
remainder is bounded, so the remaining head integral also converges for `Re s > 0`.
-/

open Complex Filter Set MeasureTheory
open scoped Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The linear Taylor coefficient of the extended cone kernel: the residue of the Mellin transform
at `s = 1`. -/
def barnesConeLinearCoeff (o1 o2 x : ℂ) : ℂ :=
  deriv (barnesConeKernelAnalytic o1 o2 x) 0

/-- **Splitting off the singular part of the cone kernel.**  On the positive reals the kernel is the
sum of its two singular powers and an analytic remainder. -/
theorem barnesConeKernel_eq_singular_add_remainder {o1 o2 x : ℝ} {t : ℝ} (ht : 0 < t) :
    barnesConeKernel o1 o2 x t
      = ((o1 : ℂ)⁻¹ * (o2 : ℂ)⁻¹) * (t : ℂ) ^ (-2 : ℂ)
        + barnesConeLinearCoeff (o1 : ℂ) (o2 : ℂ) (x : ℂ) * (t : ℂ) ^ (-1 : ℂ)
        + barnesConeKernelRemainder (o1 : ℂ) (o2 : ℂ) (x : ℂ) (t : ℂ) := by
  have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht)
  have hsq : ((t : ℂ)) ^ 2 ≠ 0 := pow_ne_zero 2 htC
  have hkey := barnesConeKernelAnalytic_ofReal o1 o2 x (ne_of_gt ht)
  have htay := barnesConeKernelAnalytic_taylor (o1 : ℂ) (o2 : ℂ) (x : ℂ) (t : ℂ)
  have hpow2 : ((t : ℂ)) ^ (-2 : ℂ) = (((t : ℂ)) ^ 2)⁻¹ := by
    rw [show ((-2 : ℂ)) = -(2 : ℂ) by ring, Complex.cpow_neg, Complex.cpow_two]
  have hpow1 : ((t : ℂ)) ^ (-1 : ℂ) = ((t : ℂ))⁻¹ := Complex.cpow_neg_one _
  rw [hpow2, hpow1, barnesConeLinearCoeff]
  rw [hkey] at htay
  field_simp
  linear_combination htay


theorem one_sub_exp_neg_mul_ofReal_pos {o t : ℝ} (ho : 0 < o) (ht : 0 < t) :
    0 < 1 - Real.exp (-o * t) := by
  have := exp_neg_mul_lt_one ho ht
  linarith

theorem norm_one_sub_exp_neg_mul_ofReal {o t : ℝ} (ho : 0 < o) (ht : 0 < t) :
    ‖(1 : ℂ) - ((Real.exp (-o * t) : ℝ) : ℂ)‖ = 1 - Real.exp (-o * t) := by
  rw [show (1 : ℂ) - ((Real.exp (-o * t) : ℝ) : ℂ) = (((1 - Real.exp (-o * t)) : ℝ) : ℂ) by
      push_cast; ring, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (one_sub_exp_neg_mul_ofReal_pos ho ht)]

/-- **Exponential decay of the cone kernel.**  Beyond `t = 1` the two geometric denominators are
bounded away from zero, so the kernel decays like `e^(-xt)`. -/
theorem norm_barnesConeKernel_le {o1 o2 x : ℝ} (h1 : 0 < o1) (h2 : 0 < o2) {t : ℝ} (ht : 1 ≤ t) :
    ‖barnesConeKernel o1 o2 x t‖
      ≤ Real.exp (-x * t) / ((1 - Real.exp (-o1)) * (1 - Real.exp (-o2))) := by
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht
  have hmono : ∀ o : ℝ, 0 < o → 0 < 1 - Real.exp (-o) ∧ 1 - Real.exp (-o) ≤ 1 - Real.exp (-o * t) := by
    intro o ho
    refine ⟨by simpa using one_sub_exp_neg_mul_ofReal_pos ho one_pos, ?_⟩
    have : Real.exp (-o * t) ≤ Real.exp (-o) := Real.exp_le_exp.mpr (by nlinarith)
    linarith
  obtain ⟨hp1, hle1⟩ := hmono o1 h1
  obtain ⟨hp2, hle2⟩ := hmono o2 h2
  rw [barnesConeKernel, norm_div, norm_mul, norm_one_sub_exp_neg_mul_ofReal h1 ht0,
    norm_one_sub_exp_neg_mul_ofReal h2 ht0, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  gcongr
  all_goals first
    | exact (Real.exp_pos _).le
    | linarith [one_sub_exp_neg_mul_ofReal_pos h1 ht0, one_sub_exp_neg_mul_ofReal_pos h2 ht0]

theorem continuousOn_barnesConeKernel {o1 o2 x : ℝ} (h1 : 0 < o1) (h2 : 0 < o2) :
    ContinuousOn (barnesConeKernel o1 o2 x) (Ioi 0) := by
  intro t ht
  have ht0 : (0 : ℝ) < t := ht
  refine ContinuousAt.continuousWithinAt ?_
  have hnum : ContinuousAt (fun u : ℝ => ((Real.exp (-x * u) : ℝ) : ℂ)) t :=
    (Complex.continuous_ofReal.comp
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))).continuousAt
  have hden : ∀ o : ℝ, ContinuousAt (fun u : ℝ => (1 : ℂ) - ((Real.exp (-o * u) : ℝ) : ℂ)) t :=
    fun o => continuousAt_const.sub ((Complex.continuous_ofReal.comp
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))).continuousAt)
  have hne : ∀ o : ℝ, 0 < o → (1 : ℂ) - ((Real.exp (-o * t) : ℝ) : ℂ) ≠ 0 := by
    intro o ho hcon
    have : ‖(1 : ℂ) - ((Real.exp (-o * t) : ℝ) : ℂ)‖ = 0 := by rw [hcon, norm_zero]
    rw [norm_one_sub_exp_neg_mul_ofReal ho ht0] at this
    linarith [one_sub_exp_neg_mul_ofReal_pos ho ht0]
  exact hnum.div ((hden o1).mul (hden o2)) (mul_ne_zero (hne o1 h1) (hne o2 h2))


theorem aestronglyMeasurable_cpow_mul_of_continuousOn {f : ℝ → ℂ} {T : Set ℝ}
    (hT : MeasurableSet T) (hTsub : T ⊆ Ioi 0) (hf : ContinuousOn f T) (s : ℂ) :
    AEStronglyMeasurable (fun t : ℝ => (t : ℂ) ^ (s - 1) * f t) (volume.restrict T) := by
  refine ContinuousOn.aestronglyMeasurable ?_ hT
  refine ContinuousOn.mul (fun t ht => ?_) hf
  exact (Complex.continuousAt_ofReal_cpow_const t (s - 1)
    (Or.inr (ne_of_gt (hTsub ht)))).continuousWithinAt

/-- **The tail of the Mellin integral is absolutely convergent for every `Re s > 0`.** -/
theorem integrableOn_cpow_mul_barnesConeKernel_Ioi_one {o1 o2 x : ℝ} (h1 : 0 < o1) (h2 : 0 < o2)
    (hx : 0 < x) {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) * barnesConeKernel o1 o2 x t) (Ioi 1) := by
  set c : ℝ := (1 - Real.exp (-o1)) * (1 - Real.exp (-o2)) with hc
  have hp1 : 0 < 1 - Real.exp (-o1) := by
    simpa using one_sub_exp_neg_mul_ofReal_pos h1 one_pos
  have hp2 : 0 < 1 - Real.exp (-o2) := by
    simpa using one_sub_exp_neg_mul_ofReal_pos h2 one_pos
  have hc0 : 0 < c := by rw [hc]; positivity
  have hsub : Ioi (1 : ℝ) ⊆ Ioi (0 : ℝ) := Ioi_subset_Ioi (by norm_num)
  have hdom : IntegrableOn
      (fun t : ℝ => c⁻¹ * (t ^ (s.re - 1) * Real.exp (-(x * t)))) (Ioi 1) :=
    ((integrableOn_rpow_mul_exp_neg_mul_Ioi (σ := s.re - 1) (a := x)
      (by linarith) hx).mono_set hsub).const_mul _
  refine Integrable.mono' hdom
    (aestronglyMeasurable_cpow_mul_of_continuousOn measurableSet_Ioi hsub
      ((continuousOn_barnesConeKernel h1 h2).mono hsub) s) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht1 : (1 : ℝ) ≤ t := le_of_lt ht
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht1
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.sub_re, Complex.one_re]
  have hbound := norm_barnesConeKernel_le (x := x) h1 h2 ht1
  calc t ^ (s.re - 1) * ‖barnesConeKernel o1 o2 x t‖
      ≤ t ^ (s.re - 1) * (Real.exp (-x * t) / c) := by
        exact mul_le_mul_of_nonneg_left hbound (Real.rpow_nonneg ht0.le _)
    _ = c⁻¹ * (t ^ (s.re - 1) * Real.exp (-(x * t))) := by
        rw [neg_mul, div_eq_mul_inv]
        ring

/-- **The subtracted head of the Mellin integral is absolutely convergent for every `Re s > 0`.** -/
theorem integrableOn_cpow_mul_barnesConeKernelRemainder_Ioc {o1 o2 x : ℝ} (h1 : 0 < o1)
    (h2 : 0 < o2) {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) *
      barnesConeKernelRemainder (o1 : ℂ) (o2 : ℂ) (x : ℂ) (t : ℂ)) (Ioc 0 1) := by
  obtain ⟨C, hC⟩ := exists_bound_barnesConeKernelRemainder h1 h2 x
  have hsub : Ioc (0 : ℝ) 1 ⊆ Ioi (0 : ℝ) := fun t ht => ht.1
  have hsubIcc : Ioc (0 : ℝ) 1 ⊆ Icc (0 : ℝ) 1 := fun t ht => ⟨ht.1.le, ht.2⟩
  have hrpow : IntegrableOn (fun t : ℝ => t ^ (s.re - 1)) (Ioc 0 1) := by
    have : IntervalIntegrable (fun t : ℝ => t ^ (s.re - 1)) volume 0 1 :=
      intervalIntegral.intervalIntegrable_rpow' (by linarith)
    rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)] at this
  have hdom : IntegrableOn (fun t : ℝ => C * t ^ (s.re - 1)) (Ioc 0 1) := hrpow.const_mul _
  refine Integrable.mono' hdom
    (aestronglyMeasurable_cpow_mul_of_continuousOn measurableSet_Ioc hsub
      ((continuousOn_barnesConeKernelRemainder_ofReal h1 h2 x).mono hsubIcc) s) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have ht0 : (0 : ℝ) < t := ht.1
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.sub_re, Complex.one_re]
  rw [mul_comm C]
  exact mul_le_mul_of_nonneg_left (hC t (hsubIcc ht)) (Real.rpow_nonneg ht0.le _)


/-- Restricting an integral over the half-line to the unit interval. -/
theorem integral_Ioi_indicator_Ioc {h : ℝ → ℂ} :
    (∫ t in Ioi (0 : ℝ), Set.indicator (Ioc (0:ℝ) 1) h t) = ∫ t in Ioc (0:ℝ) 1, h t := by
  rw [MeasureTheory.integral_indicator measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc,
    show Ioc (0:ℝ) 1 ∩ Ioi (0:ℝ) = Ioc (0:ℝ) 1 from
      Set.inter_eq_left.mpr (fun t ht => ht.1)]

/-- **The elementary head integral.**  `∫_0^1 t^(s-1) t^a dt = 1/(s+a)`. -/
theorem integral_cpow_mul_cpow_Ioc (a : ℂ) {s : ℂ} (hs : 0 < s.re + a.re) :
    (∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (s - 1) * (t : ℂ) ^ a) = 1 / (s + a) := by
  have hm := hasMellin_cpow_Ioc a hs
  have hval : mellin (Set.indicator (Ioc (0:ℝ) 1) (fun t : ℝ => (t : ℂ) ^ a)) s = 1 / (s + a) :=
    hm.2
  rw [mellin] at hval
  have hsm : ∀ t : ℝ, (t : ℂ) ^ (s - 1) • Set.indicator (Ioc (0:ℝ) 1) (fun t : ℝ => (t : ℂ) ^ a) t
      = Set.indicator (Ioc (0:ℝ) 1) (fun t : ℝ => (t : ℂ) ^ (s - 1) * (t : ℂ) ^ a) t := by
    intro t
    by_cases ht : t ∈ Ioc (0:ℝ) 1
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht, smul_eq_mul]
    · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, smul_zero]
  simp only [hsm] at hval
  rw [← hval, integral_Ioi_indicator_Ioc]

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem integrableOn_cpow_mul_cpow_Ioc (a : ℂ) {s : ℂ} (hs : 0 < s.re + a.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) * (t : ℂ) ^ a) (Ioc 0 1) := by
  have hrpow : IntegrableOn (fun t : ℝ => t ^ (s.re + a.re - 1)) (Ioc 0 1) := by
    have : IntervalIntegrable (fun t : ℝ => t ^ (s.re + a.re - 1)) volume 0 1 :=
      intervalIntegral.intervalIntegrable_rpow' (by linarith)
    rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)] at this
  have hmeas : AEStronglyMeasurable (fun t : ℝ => (t : ℂ) ^ (s - 1) * (t : ℂ) ^ a)
      (volume.restrict (Ioc (0:ℝ) 1)) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
    refine ContinuousOn.mul (fun t ht => ?_) (fun t ht => ?_)
    · exact (Complex.continuousAt_ofReal_cpow_const t (s - 1)
        (Or.inr (ne_of_gt ht.1))).continuousWithinAt
    · exact (Complex.continuousAt_ofReal_cpow_const t a
        (Or.inr (ne_of_gt ht.1))).continuousWithinAt
  refine Integrable.mono' hrpow hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have ht0 : (0 : ℝ) < t := ht.1
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0,
    Complex.norm_cpow_eq_rpow_re_of_pos ht0, ← Real.rpow_add ht0, Complex.sub_re, Complex.one_re]
  rw [show s.re - 1 + a.re = s.re + a.re - 1 by ring]

/-- **The head of the Mellin integral, with the two poles made explicit.** -/
theorem integral_head_barnesConeKernel {o1 o2 x : ℝ} (h1 : 0 < o1) (h2 : 0 < o2)
    {s : ℂ} (hs : 2 < s.re) :
    (∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (s - 1) * barnesConeKernel o1 o2 x t)
      = ((o1 : ℂ)⁻¹ * (o2 : ℂ)⁻¹) / (s - 2)
        + barnesConeLinearCoeff (o1 : ℂ) (o2 : ℂ) (x : ℂ) / (s - 1)
        + ∫ t in Ioc (0 : ℝ) 1,
            (t : ℂ) ^ (s - 1) * barnesConeKernelRemainder (o1 : ℂ) (o2 : ℂ) (x : ℂ) (t : ℂ) := by
  have hs0 : 0 < s.re := by linarith
  have hre2 : 0 < s.re + ((-2 : ℂ)).re := by simp; linarith
  have hre1 : 0 < s.re + ((-1 : ℂ)).re := by simp; linarith
  set A0 : ℂ := (o1 : ℂ)⁻¹ * (o2 : ℂ)⁻¹ with hA0
  set A1 : ℂ := barnesConeLinearCoeff (o1 : ℂ) (o2 : ℂ) (x : ℂ) with hA1
  have hi2 := (integrableOn_cpow_mul_cpow_Ioc (-2 : ℂ) hre2).const_mul A0
  have hi1 := (integrableOn_cpow_mul_cpow_Ioc (-1 : ℂ) hre1).const_mul A1
  have hiR := integrableOn_cpow_mul_barnesConeKernelRemainder_Ioc (x := x) h1 h2 hs0
  have hcongr : ∀ t ∈ Ioc (0 : ℝ) 1,
      (t : ℂ) ^ (s - 1) * barnesConeKernel o1 o2 x t
        = A0 * ((t : ℂ) ^ (s - 1) * (t : ℂ) ^ (-2 : ℂ))
          + A1 * ((t : ℂ) ^ (s - 1) * (t : ℂ) ^ (-1 : ℂ))
          + (t : ℂ) ^ (s - 1) * barnesConeKernelRemainder (o1 : ℂ) (o2 : ℂ) (x : ℂ) (t : ℂ) := by
    intro t ht
    rw [barnesConeKernel_eq_singular_add_remainder ht.1, ← hA0, ← hA1]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioc hcongr]
  have hsplit1 : (∫ t in Ioc (0 : ℝ) 1,
        (A0 * ((t : ℂ) ^ (s - 1) * (t : ℂ) ^ (-2 : ℂ))
            + A1 * ((t : ℂ) ^ (s - 1) * (t : ℂ) ^ (-1 : ℂ))
          + (t : ℂ) ^ (s - 1) * barnesConeKernelRemainder (o1 : ℂ) (o2 : ℂ) (x : ℂ) (t : ℂ)))
      = (∫ t in Ioc (0 : ℝ) 1,
          (A0 * ((t : ℂ) ^ (s - 1) * (t : ℂ) ^ (-2 : ℂ))
            + A1 * ((t : ℂ) ^ (s - 1) * (t : ℂ) ^ (-1 : ℂ))))
        + ∫ t in Ioc (0 : ℝ) 1,
            (t : ℂ) ^ (s - 1) * barnesConeKernelRemainder (o1 : ℂ) (o2 : ℂ) (x : ℂ) (t : ℂ) :=
    integral_add (hi2.add hi1) hiR
  have hsplit2 : (∫ t in Ioc (0 : ℝ) 1,
        (A0 * ((t : ℂ) ^ (s - 1) * (t : ℂ) ^ (-2 : ℂ))
          + A1 * ((t : ℂ) ^ (s - 1) * (t : ℂ) ^ (-1 : ℂ))))
      = (∫ t in Ioc (0 : ℝ) 1, A0 * ((t : ℂ) ^ (s - 1) * (t : ℂ) ^ (-2 : ℂ)))
        + ∫ t in Ioc (0 : ℝ) 1, A1 * ((t : ℂ) ^ (s - 1) * (t : ℂ) ^ (-1 : ℂ)) :=
    integral_add hi2 hi1
  rw [hsplit1, hsplit2, integral_const_mul, integral_const_mul,
    integral_cpow_mul_cpow_Ioc (-2 : ℂ) hre2, integral_cpow_mul_cpow_Ioc (-1 : ℂ) hre1,
    show s + (-2 : ℂ) = s - 2 by ring, show s + (-1 : ℂ) = s - 1 by ring]
  ring

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem integrableOn_cpow_mul_barnesConeKernel_Ioc {o1 o2 x : ℝ} (h1 : 0 < o1) (h2 : 0 < o2)
    {s : ℂ} (hs : 2 < s.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) * barnesConeKernel o1 o2 x t) (Ioc 0 1) := by
  have hs0 : 0 < s.re := by linarith
  have hre2 : 0 < s.re + ((-2 : ℂ)).re := by simp; linarith
  have hre1 : 0 < s.re + ((-1 : ℂ)).re := by simp; linarith
  have hi2 := (integrableOn_cpow_mul_cpow_Ioc (-2 : ℂ) hre2).const_mul
    ((o1 : ℂ)⁻¹ * (o2 : ℂ)⁻¹)
  have hi1 := (integrableOn_cpow_mul_cpow_Ioc (-1 : ℂ) hre1).const_mul
    (barnesConeLinearCoeff (o1 : ℂ) (o2 : ℂ) (x : ℂ))
  have hiR := integrableOn_cpow_mul_barnesConeKernelRemainder_Ioc (x := x) h1 h2 hs0
  refine MeasureTheory.IntegrableOn.congr_fun ((hi2.add hi1).add hiR)
    (fun t ht => ?_) measurableSet_Ioc
  simp only [Pi.add_apply]
  rw [barnesConeKernel_eq_singular_add_remainder ht.1]
  ring

/-- **Meromorphic continuation of the Barnes double zeta.**  Splitting at `t = 1` and subtracting
the singular part of the cone kernel writes `Gamma(s) zeta_2(s,x)` as two explicit simple poles plus
two integrals, both absolutely convergent for `Re s > 0`. -/
theorem Gamma_mul_barnesDoubleZeta_eq_continuation {o1 o2 x : ℝ} (h1 : 0 < o1) (h2 : 0 < o2)
    (hx : 0 < x) {s : ℂ} (hs : 2 < s.re) :
    Complex.Gamma s * barnesDoubleZeta o1 o2 s (x : ℂ)
      = ((o1 : ℂ)⁻¹ * (o2 : ℂ)⁻¹) / (s - 2)
        + barnesConeLinearCoeff (o1 : ℂ) (o2 : ℂ) (x : ℂ) / (s - 1)
        + (∫ t in Ioc (0 : ℝ) 1,
            (t : ℂ) ^ (s - 1) * barnesConeKernelRemainder (o1 : ℂ) (o2 : ℂ) (x : ℂ) (t : ℂ))
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
    integral_head_barnesConeKernel h1 h2 hs]

end

end GaloisForLFunctions.HTGeometry
