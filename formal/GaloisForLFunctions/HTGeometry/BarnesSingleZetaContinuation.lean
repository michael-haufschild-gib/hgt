import GaloisForLFunctions.HTGeometry.BarnesDoubleZetaHolomorphy
import GaloisForLFunctions.HTGeometry.BarnesMellinRepresentation
import Mathlib.NumberTheory.LSeries.MellinEqDirichlet

/-!
# Meromorphic continuation of the one-dimensional Barnes zeta

The ray kernel `e^(-xt)/(1 - e^(-omega t))` has a simple pole at the origin, so `t F(t)` extends
analytically and its second-order expansion

```text
t F(t) = 1/omega + t B_1 + t² R(t)
```

isolates the two singular contributions to the Mellin transform: the poles at `s = 1` and `s = 0`.
Splitting at `t = 1` and subtracting them continues `Gamma(s) zeta_1(s,x)` to `Re s > -1`.

This is the one-dimensional companion of the cone continuation; the shift equations of the double
zeta reduce to the single zeta, so both are needed to transport a functional equation to the
continued functions.
-/

open Complex Real MeasureTheory Set Filter
open scoped Topology BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **The Mellin representation of the one-dimensional Barnes zeta.**  For a positive real argument
and `Re s > 1`,

```text
Γ(s) ζ₁(s, x) = ∫_0^∞ t^(s-1) e^(-x t) / (1 - e^(-ω t)) dt.
```
-/
theorem Gamma_mul_barnesSingleZeta_eq_mellin {o x : ℝ} (ho : 0 < o) (hx : 0 < x)
    {s : ℂ} (hs : 1 < s.re) :
    Complex.Gamma s * barnesSingleZeta o s (x : ℂ) = mellin (barnesRayKernel o x) s := by
  have hs0 : 0 < s.re := by linarith
  have hsum : Summable fun n : ℕ => ‖(1 : ℂ)‖ / (x + (n : ℝ) * o) ^ s.re := by
    have := summable_lattice1_rpow ho hx hs
    refine this.congr fun n => ?_
    rw [Real.rpow_neg (by positivity)]
    simp [one_div]
  have hmain := hasSum_mellin (a := fun _ : ℕ => (1 : ℂ))
    (p := fun n : ℕ => x + (n : ℝ) * o)
    (F := barnesRayKernel o x) (s := s)
    (fun n => Or.inr (by positivity))
    hs0
    (fun t ht => hasSum_barnesRayKernel ho t ht)
    hsum
  rw [← hmain.tsum_eq, barnesSingleZeta, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  have hcast : ((x : ℂ) + (((n : ℝ) * o : ℝ) : ℂ)) = (((x + (n : ℝ) * o : ℝ)) : ℂ) := by
    push_cast
    ring
  rw [hcast, Complex.cpow_neg]
  ring

/-- The ray kernel with its simple pole removed: `t F(t)`, extended across the origin. -/
def barnesRayKernelAnalytic (o x : ℂ) (z : ℂ) : ℂ :=
  Complex.exp (-(x * z)) * cylKernelFactor o z

@[simp] theorem barnesRayKernelAnalytic_zero (o x : ℂ) :
    barnesRayKernelAnalytic o x 0 = o⁻¹ := by
  simp [barnesRayKernelAnalytic]

theorem barnesRayKernelAnalytic_ofReal (o x : ℝ) {t : ℝ} (ht : t ≠ 0) :
    barnesRayKernelAnalytic (o : ℂ) (x : ℂ) (t : ℂ) = (t : ℂ) * barnesRayKernel o x t := by
  have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  have hcast : ∀ u : ℝ, Complex.exp (-((u : ℂ) * (t : ℂ))) = ((Real.exp (-u * t) : ℝ) : ℂ) := by
    intro u
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  have key : ∀ E T D : ℂ, E * (T / D) = T * (E / D) := by
    intro E T D
    ring
  rw [barnesRayKernelAnalytic, cylKernelFactor_of_ne htC, barnesRayKernel, hcast, hcast]
  exact key _ _ _

/-- **The extended ray kernel is analytic at the origin.** -/
theorem analyticAt_barnesRayKernelAnalytic {o : ℂ} (ho : o ≠ 0) (x : ℂ) :
    AnalyticAt ℂ (barnesRayKernelAnalytic o x) 0 := by
  have hexp : AnalyticAt ℂ (fun z : ℂ => Complex.exp (-(x * z))) 0 :=
    ((analyticAt_const.mul analyticAt_id).neg).cexp'
  exact hexp.mul (analyticAt_cylKernelFactor ho)

/-- The linear Taylor coefficient of the extended ray kernel: the residue at `s = 0`. -/
def barnesRayLinearCoeff (o x : ℂ) : ℂ := deriv (barnesRayKernelAnalytic o x) 0

/-- The quadratic Taylor remainder of the extended ray kernel. -/
def barnesRayRemainder (o x : ℂ) : ℂ → ℂ :=
  analyticSlopeIter (barnesRayKernelAnalytic o x) 0 2

theorem analyticAt_barnesRayRemainder {o : ℂ} (ho : o ≠ 0) (x : ℂ) :
    AnalyticAt ℂ (barnesRayRemainder o x) 0 :=
  analyticAt_analyticSlopeIter (analyticAt_barnesRayKernelAnalytic ho x) 2

/-- **Second-order expansion of the extended ray kernel.**  The two singular contributions to the
Mellin transform are the poles at `s = 1` and `s = 0`. -/
theorem barnesRayKernelAnalytic_taylor (o x z : ℂ) :
    barnesRayKernelAnalytic o x z
      = o⁻¹ + z * barnesRayLinearCoeff o x + z ^ 2 * barnesRayRemainder o x z := by
  have h := eq_taylor_add_pow_mul (barnesRayKernelAnalytic o x) 0 z 2
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero] at h
  simp only [sub_zero, pow_zero, pow_one, one_mul, zero_add, analyticSlopeIter_zero,
    analyticSlopeIter_succ, analyticSlope_self] at h
  rw [barnesRayKernelAnalytic_zero] at h
  rw [barnesRayLinearCoeff, barnesRayRemainder]
  simp only [analyticSlopeIter_succ, analyticSlopeIter_zero]
  linear_combination h

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem continuousAt_barnesRayKernelAnalytic_ofReal {o : ℝ} (ho : 0 < o) (x : ℝ) {t : ℝ}
    (ht : 0 ≤ t) :
    ContinuousAt (fun u : ℝ => barnesRayKernelAnalytic (o : ℂ) (x : ℂ) (u : ℂ)) t := by
  have hexp : ContinuousAt (fun u : ℝ => Complex.exp (-((x : ℂ) * (u : ℂ)))) t :=
    (Complex.continuous_exp.comp
      ((continuous_const.mul Complex.continuous_ofReal).neg)).continuousAt
  have hk : ContinuousAt (fun u : ℝ => cylKernelFactor (o : ℂ) (u : ℂ)) t := by
    rcases eq_or_lt_of_le ht with h0 | h0
    · rw [← h0]
      exact continuousAt_cylKernelFactor_ofReal_zero ho
    · exact continuousAt_cylKernelFactor_ofReal_pos ho h0
  exact hexp.mul hk

theorem barnesRayRemainder_of_ne {o x z : ℂ} (hz : z ≠ 0) :
    barnesRayRemainder o x z
      = (barnesRayKernelAnalytic o x z - o⁻¹ - z * barnesRayLinearCoeff o x) / z ^ 2 := by
  have hz2 : z ^ 2 ≠ 0 := pow_ne_zero 2 hz
  have h := barnesRayKernelAnalytic_taylor o x z
  rw [eq_div_iff hz2]
  linear_combination -h

theorem continuousAt_barnesRayRemainder_ofReal {o : ℝ} (ho : 0 < o) (x : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    ContinuousAt (fun u : ℝ => barnesRayRemainder (o : ℂ) (x : ℂ) (u : ℂ)) t := by
  have hoC : (o : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ho)
  rcases eq_or_lt_of_le ht with h0 | h0
  · have hR : ContinuousAt (barnesRayRemainder (o : ℂ) (x : ℂ)) (((0 : ℝ) : ℂ)) := by
      rw [Complex.ofReal_zero]
      exact (analyticAt_barnesRayRemainder hoC (x : ℂ)).continuousAt
    have hcomp := hR.comp Complex.continuous_ofReal.continuousAt
    rw [← h0]
    simpa [Function.comp_def] using hcomp
  · have heq : (fun u : ℝ => barnesRayRemainder (o : ℂ) (x : ℂ) (u : ℂ))
        =ᶠ[𝓝 t] fun u : ℝ =>
          (barnesRayKernelAnalytic (o : ℂ) (x : ℂ) (u : ℂ) - (o : ℂ)⁻¹
            - (u : ℂ) * barnesRayLinearCoeff (o : ℂ) (x : ℂ)) / (u : ℂ) ^ 2 := by
      filter_upwards [Ioi_mem_nhds h0] with u hu
      exact barnesRayRemainder_of_ne (Complex.ofReal_ne_zero.mpr (ne_of_gt hu))
    rw [continuousAt_congr heq]
    have hA : ContinuousAt (fun u : ℝ => barnesRayKernelAnalytic (o : ℂ) (x : ℂ) (u : ℂ)) t :=
      continuousAt_barnesRayKernelAnalytic_ofReal ho x ht
    refine ContinuousAt.div ?_ ((Complex.continuous_ofReal.continuousAt).pow 2)
      (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (ne_of_gt h0)))
    exact (hA.sub continuousAt_const).sub
      (Complex.continuous_ofReal.continuousAt.mul continuousAt_const)

/-- **The Taylor remainder of the ray kernel is bounded on the unit interval.** -/
theorem exists_bound_barnesRayRemainder {o : ℝ} (ho : 0 < o) (x : ℝ) :
    ∃ C : ℝ, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖barnesRayRemainder (o : ℂ) (x : ℂ) (t : ℂ)‖ ≤ C :=
  isCompact_Icc.exists_bound_of_continuousOn
    (fun _ ht => (continuousAt_barnesRayRemainder_ofReal ho x ht.1).continuousWithinAt)

/-- **Splitting off the singular part of the ray kernel.** -/
theorem barnesRayKernel_eq_singular_add_remainder {o x : ℝ} {t : ℝ} (ht : 0 < t) :
    barnesRayKernel o x t
      = (o : ℂ)⁻¹ * (t : ℂ) ^ (-1 : ℂ)
        + barnesRayLinearCoeff (o : ℂ) (x : ℂ) * (t : ℂ) ^ (0 : ℂ)
        + (t : ℂ) * barnesRayRemainder (o : ℂ) (x : ℂ) (t : ℂ) := by
  have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht)
  have hkey := barnesRayKernelAnalytic_ofReal o x (ne_of_gt ht)
  have htay := barnesRayKernelAnalytic_taylor (o : ℂ) (x : ℂ) (t : ℂ)
  have hpow1 : ((t : ℂ)) ^ (-1 : ℂ) = ((t : ℂ))⁻¹ := Complex.cpow_neg_one _
  have hpow0 : ((t : ℂ)) ^ (0 : ℂ) = 1 := Complex.cpow_zero _
  rw [hpow1, hpow0]
  rw [hkey] at htay
  field_simp
  linear_combination htay

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem continuousOn_barnesRayKernel {o x : ℝ} (ho : 0 < o) :
    ContinuousOn (barnesRayKernel o x) (Ioi 0) := by
  intro t ht
  have ht0 : (0 : ℝ) < t := ht
  refine ContinuousAt.continuousWithinAt ?_
  have hnum : ContinuousAt (fun u : ℝ => ((Real.exp (-x * u) : ℝ) : ℂ)) t :=
    (Complex.continuous_ofReal.comp
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))).continuousAt
  have hden : ContinuousAt (fun u : ℝ => (1 : ℂ) - ((Real.exp (-o * u) : ℝ) : ℂ)) t :=
    continuousAt_const.sub ((Complex.continuous_ofReal.comp
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))).continuousAt)
  have hne : (1 : ℂ) - ((Real.exp (-o * t) : ℝ) : ℂ) ≠ 0 := by
    intro hcon
    have hz : ‖(1 : ℂ) - ((Real.exp (-o * t) : ℝ) : ℂ)‖ = 0 := by rw [hcon, norm_zero]
    rw [norm_one_sub_exp_neg_mul_ofReal ho ht0] at hz
    linarith [one_sub_exp_neg_mul_ofReal_pos ho ht0]
  exact hnum.div hden hne

theorem norm_barnesRayKernel_le {o x : ℝ} (ho : 0 < o) {t : ℝ} (ht : 1 ≤ t) :
    ‖barnesRayKernel o x t‖ ≤ Real.exp (-x * t) / (1 - Real.exp (-o)) := by
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht
  have hp : 0 < 1 - Real.exp (-o) := by
    simpa using one_sub_exp_neg_mul_ofReal_pos ho one_pos
  have hle : 1 - Real.exp (-o) ≤ 1 - Real.exp (-o * t) := by
    have : Real.exp (-o * t) ≤ Real.exp (-o) := Real.exp_le_exp.mpr (by nlinarith)
    linarith
  rw [barnesRayKernel, norm_div, norm_one_sub_exp_neg_mul_ofReal ho ht0, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  gcongr

theorem integrableOn_cpow_mul_barnesRayKernel_Ioi_one {o x : ℝ} (ho : 0 < o) (hx : 0 < x)
    {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) * barnesRayKernel o x t) (Ioi 1) := by
  have hp : 0 < 1 - Real.exp (-o) := by
    simpa using one_sub_exp_neg_mul_ofReal_pos ho one_pos
  have hsub : Ioi (1 : ℝ) ⊆ Ioi (0 : ℝ) := Ioi_subset_Ioi (by norm_num)
  have hdom : IntegrableOn
      (fun t : ℝ => (1 - Real.exp (-o))⁻¹ * (t ^ (s.re - 1) * Real.exp (-(x * t)))) (Ioi 1) :=
    ((integrableOn_rpow_mul_exp_neg_mul_Ioi (σ := s.re - 1) (a := x)
      (by linarith) hx).mono_set hsub).const_mul _
  refine Integrable.mono' hdom
    (aestronglyMeasurable_cpow_mul_of_continuousOn measurableSet_Ioi hsub
      ((continuousOn_barnesRayKernel ho).mono hsub) s) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht1 : (1 : ℝ) ≤ t := le_of_lt ht
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht1
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.sub_re, Complex.one_re]
  calc t ^ (s.re - 1) * ‖barnesRayKernel o x t‖
      ≤ t ^ (s.re - 1) * (Real.exp (-x * t) / (1 - Real.exp (-o))) :=
        mul_le_mul_of_nonneg_left (norm_barnesRayKernel_le ho ht1) (Real.rpow_nonneg ht0.le _)
    _ = (1 - Real.exp (-o))⁻¹ * (t ^ (s.re - 1) * Real.exp (-(x * t))) := by
        rw [neg_mul, div_eq_mul_inv]
        ring

theorem integrableOn_cpow_mul_barnesRayRemainder_Ioc {o x : ℝ} (ho : 0 < o)
    {s : ℂ} (hs : -1 < s.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s + 1 - 1) *
      barnesRayRemainder (o : ℂ) (x : ℂ) (t : ℂ)) (Ioc 0 1) := by
  obtain ⟨C, hC⟩ := exists_bound_barnesRayRemainder ho x
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
      (fun t ht => (continuousAt_barnesRayRemainder_ofReal ho x ht.1.le).continuousWithinAt)
      (s + 1)) ?_
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
/-- **The head of the ray Mellin integral, with its two poles made explicit.** -/
theorem integral_head_barnesRayKernel {o x : ℝ} (ho : 0 < o) {s : ℂ} (hs : 1 < s.re) :
    (∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (s - 1) * barnesRayKernel o x t)
      = (o : ℂ)⁻¹ / (s - 1) + barnesRayLinearCoeff (o : ℂ) (x : ℂ) / s
        + ∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (s + 1 - 1) *
            barnesRayRemainder (o : ℂ) (x : ℂ) (t : ℂ) := by
  have hre1 : 0 < s.re + ((-1 : ℂ)).re := by simp; linarith
  have hre0 : 0 < s.re + ((0 : ℂ)).re := by simp; linarith
  have hreR : (-1 : ℝ) < s.re := by linarith
  set B0 : ℂ := (o : ℂ)⁻¹ with hB0
  set B1 : ℂ := barnesRayLinearCoeff (o : ℂ) (x : ℂ) with hB1
  have hi1 := (integrableOn_cpow_mul_cpow_Ioc (-1 : ℂ) hre1).const_mul B0
  have hi0 := (integrableOn_cpow_mul_cpow_Ioc (0 : ℂ) hre0).const_mul B1
  have hiR := integrableOn_cpow_mul_barnesRayRemainder_Ioc (x := x) ho hreR
  have hcongr : ∀ t ∈ Ioc (0 : ℝ) 1,
      (t : ℂ) ^ (s - 1) * barnesRayKernel o x t
        = B0 * ((t : ℂ) ^ (s - 1) * (t : ℂ) ^ (-1 : ℂ))
          + B1 * ((t : ℂ) ^ (s - 1) * (t : ℂ) ^ (0 : ℂ))
          + (t : ℂ) ^ (s + 1 - 1) * barnesRayRemainder (o : ℂ) (x : ℂ) (t : ℂ) := by
    intro t ht
    have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht.1)
    have hpow : (t : ℂ) ^ (s - 1) * (t : ℂ) = (t : ℂ) ^ (s + 1 - 1) := by
      rw [show s + 1 - 1 = (s - 1) + 1 by ring, Complex.cpow_add _ _ htC, Complex.cpow_one]
    rw [barnesRayKernel_eq_singular_add_remainder ht.1, ← hB0, ← hB1, ← hpow]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioc hcongr]
  have hsp1 : (∫ t in Ioc (0 : ℝ) 1,
        (B0 * ((t : ℂ) ^ (s - 1) * (t : ℂ) ^ (-1 : ℂ))
            + B1 * ((t : ℂ) ^ (s - 1) * (t : ℂ) ^ (0 : ℂ))
          + (t : ℂ) ^ (s + 1 - 1) * barnesRayRemainder (o : ℂ) (x : ℂ) (t : ℂ)))
      = (∫ t in Ioc (0 : ℝ) 1,
          (B0 * ((t : ℂ) ^ (s - 1) * (t : ℂ) ^ (-1 : ℂ))
            + B1 * ((t : ℂ) ^ (s - 1) * (t : ℂ) ^ (0 : ℂ))))
        + ∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (s + 1 - 1) *
            barnesRayRemainder (o : ℂ) (x : ℂ) (t : ℂ) :=
    integral_add (hi1.add hi0) hiR
  have hsp2 : (∫ t in Ioc (0 : ℝ) 1,
        (B0 * ((t : ℂ) ^ (s - 1) * (t : ℂ) ^ (-1 : ℂ))
          + B1 * ((t : ℂ) ^ (s - 1) * (t : ℂ) ^ (0 : ℂ))))
      = (∫ t in Ioc (0 : ℝ) 1, B0 * ((t : ℂ) ^ (s - 1) * (t : ℂ) ^ (-1 : ℂ)))
        + ∫ t in Ioc (0 : ℝ) 1, B1 * ((t : ℂ) ^ (s - 1) * (t : ℂ) ^ (0 : ℂ)) :=
    integral_add hi1 hi0
  rw [hsp1, hsp2, integral_const_mul, integral_const_mul,
    integral_cpow_mul_cpow_Ioc (-1 : ℂ) hre1, integral_cpow_mul_cpow_Ioc (0 : ℂ) hre0,
    show s + (-1 : ℂ) = s - 1 by ring, show s + (0 : ℂ) = s by ring]
  ring

theorem integrableOn_cpow_mul_barnesRayKernel_Ioc {o x : ℝ} (ho : 0 < o) {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) * barnesRayKernel o x t) (Ioc 0 1) := by
  have hre1 : 0 < s.re + ((-1 : ℂ)).re := by simp; linarith
  have hre0 : 0 < s.re + ((0 : ℂ)).re := by simp; linarith
  have hreR : (-1 : ℝ) < s.re := by linarith
  have hi1 := (integrableOn_cpow_mul_cpow_Ioc (-1 : ℂ) hre1).const_mul ((o : ℂ)⁻¹)
  have hi0 := (integrableOn_cpow_mul_cpow_Ioc (0 : ℂ) hre0).const_mul
    (barnesRayLinearCoeff (o : ℂ) (x : ℂ))
  have hiR := integrableOn_cpow_mul_barnesRayRemainder_Ioc (x := x) ho hreR
  refine MeasureTheory.IntegrableOn.congr_fun ((hi1.add hi0).add hiR)
    (fun t ht => ?_) measurableSet_Ioc
  have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht.1)
  have hpow : (t : ℂ) ^ (s - 1) * (t : ℂ) = (t : ℂ) ^ (s + 1 - 1) := by
    rw [show s + 1 - 1 = (s - 1) + 1 by ring, Complex.cpow_add _ _ htC, Complex.cpow_one]
  simp only [Pi.add_apply]
  rw [barnesRayKernel_eq_singular_add_remainder ht.1, ← hpow]
  ring

set_option maxHeartbeats 800000 in
/-- **Meromorphic continuation of the one-dimensional Barnes zeta.**  Two explicit simple poles at
`s = 1` and `s = 0`, plus two integrals convergent for `Re s > -1` and `Re s > 0`. -/
theorem Gamma_mul_barnesSingleZeta_eq_continuation {o x : ℝ} (ho : 0 < o) (hx : 0 < x)
    {s : ℂ} (hs : 1 < s.re) :
    Complex.Gamma s * barnesSingleZeta o s (x : ℂ)
      = (o : ℂ)⁻¹ / (s - 1) + barnesRayLinearCoeff (o : ℂ) (x : ℂ) / s
        + (∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (s + 1 - 1) *
            barnesRayRemainder (o : ℂ) (x : ℂ) (t : ℂ))
        + ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (s - 1) * barnesRayKernel o x t := by
  have hs0 : 0 < s.re := by linarith
  have hIoc := integrableOn_cpow_mul_barnesRayKernel_Ioc (x := x) ho hs
  have hIoi := integrableOn_cpow_mul_barnesRayKernel_Ioi_one ho hx hs0
  have hdisj : Disjoint (Ioc (0 : ℝ) 1) (Ioi (1 : ℝ)) :=
    Set.disjoint_left.mpr fun t ht ht' => absurd ht.2 (not_le.mpr ht')
  rw [Gamma_mul_barnesSingleZeta_eq_mellin ho hx hs, mellin]
  simp only [smul_eq_mul]
  rw [← Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1),
    setIntegral_union hdisj measurableSet_Ioi hIoc hIoi,
    integral_head_barnesRayKernel ho hs]

end

end GaloisForLFunctions.HTGeometry
