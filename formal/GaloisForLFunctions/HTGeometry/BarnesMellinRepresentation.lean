import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The Euler integral behind the Mellin representation of the Barnes zeta

The meromorphic continuation of the Barnes double zeta past its abscissa of convergence goes
through the Mellin representation

```text
Γ(s) ζ₂(s, z) = ∫_0^∞ t^(s-1) e^(-z t) / ((1 - e^(-ω₁ t))(1 - e^(-ω₂ t))) dt,     Re s > 2,
```

which is obtained by summing the Euler integral of each cone term over the cone.  The term-by-term
input is the scaled Euler integral

```text
∫_0^∞ t^(s-1) e^(-w t) dt = Γ(s) w^(-s).
```

This module proves it for a positive real rate `w`, which is the case where the substitution
`t ↦ w t` is a genuine change of variables on the half-line; the complex-rate version is obtained
from it by analytic continuation in `w` over the right half-plane, where both sides are analytic and
agree on the positive reals.

Convergence itself is proved for a **complex** rate: `integrableOn_cpow_mul_exp_neg_mul_Ioi` shows
`t^(s-1) e^(-w t)` is integrable on the half-line whenever `Re s > 0` and `Re w > 0`, dominated by
the real integrand `t^(Re s - 1) e^(-(Re w) t)` of `integrableOn_rpow_mul_exp_neg_mul_Ioi`.  This is
what both the analytic continuation in the rate and the term-by-term summation over the cone need.
-/

open Complex Real MeasureTheory Set
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **The scaled Euler integral for a positive real rate.**  For `w > 0` real and `Re s > 0`,

```text
∫_0^∞ t^(s-1) e^(-w t) dt = Γ(s) w^(-s).
```

This is the base case of the Mellin representation of the Barnes zeta functions; the complex-rate
version follows from it by analytic continuation in the rate. -/
theorem integral_cpow_mul_exp_neg_real_mul_Ioi {s : ℂ} (hs : 0 < s.re) {w : ℝ} (hw : 0 < w) :
    (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) * Complex.exp (-((w : ℂ) * t)))
      = Complex.Gamma s * (w : ℂ) ^ (-s) := by
  have hwC : (w : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hw.ne'
  set g : ℝ → ℂ := fun u => ((u / w : ℝ) : ℂ) ^ (s - 1) * Complex.exp (-(u : ℂ)) with hg
  have hcomp : ∀ t : ℝ, g (w * t) = (t : ℂ) ^ (s - 1) * Complex.exp (-((w : ℂ) * t)) := by
    intro t
    have hdiv : ((w * t / w : ℝ)) = t := by
      field_simp
    rw [hg]
    simp only [hdiv]
    congr 2
    push_cast
    ring
  have hsub : (∫ t in Ioi (0 : ℝ), g (w * t)) = w⁻¹ • ∫ u in Ioi (0 : ℝ), g u := by
    have := integral_comp_mul_left_Ioi g 0 hw
    simpa using this
  have hgval : (∫ u in Ioi (0 : ℝ), g u)
      = (w : ℂ) ^ (1 - s) * Complex.Gamma s := by
    rw [Complex.Gamma_eq_integral hs, Complex.GammaIntegral]
    rw [← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    have hu0 : (0 : ℝ) < u := hu
    have harg : ((w : ℝ) : ℂ).arg ≠ Real.pi := by
      rw [Complex.arg_ofReal_of_nonneg hw.le]
      exact (Real.pi_ne_zero).symm
    have hsplit : ((u / w : ℝ) : ℂ) ^ (s - 1)
        = (u : ℂ) ^ (s - 1) * (w : ℂ) ^ (1 - s) := by
      have hmul : ((u / w : ℝ) : ℂ) = ((u : ℝ) : ℂ) * ((w⁻¹ : ℝ) : ℂ) := by
        push_cast
        ring
      rw [hmul, Complex.mul_cpow_ofReal_nonneg hu0.le (by positivity)]
      congr 1
      rw [Complex.ofReal_inv, Complex.inv_cpow _ _ harg,
        show (1 : ℂ) - s = -(s - 1) by ring, Complex.cpow_neg]
    rw [hg]
    simp only [hsplit]
    push_cast
    ring
  have hcpow : (w : ℂ) ^ (-s) = (w : ℂ)⁻¹ * (w : ℂ) ^ (1 - s) := by
    rw [show (1 : ℂ) - s = 1 + (-s) by ring, Complex.cpow_add _ _ hwC, Complex.cpow_one]
    field_simp
  calc (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) * Complex.exp (-((w : ℂ) * t)))
      = ∫ t in Ioi (0 : ℝ), g (w * t) := by
        refine setIntegral_congr_fun measurableSet_Ioi fun t _ => (hcomp t).symm
    _ = w⁻¹ • ∫ u in Ioi (0 : ℝ), g u := hsub
    _ = (w : ℂ)⁻¹ * ((w : ℂ) ^ (1 - s) * Complex.Gamma s) := by
        rw [hgval]
        simp [Complex.real_smul]
    _ = Complex.Gamma s * (w : ℂ) ^ (-s) := by
        rw [hcpow]
        ring


/-! ## Convergence of the Euler integral -/

/-- The Euler integrand with a positive real rate is integrable on the half-line. -/
theorem integrableOn_rpow_mul_exp_neg_mul_Ioi {σ a : ℝ} (hσ : -1 < σ) (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => t ^ σ * Real.exp (-(a * t))) (Ioi 0) := by
  have hbase : IntegrableOn (fun x : ℝ => Real.exp (-x) * x ^ ((σ + 1) - 1)) (Ioi 0) :=
    Real.GammaIntegral_convergent (by linarith)
  have hbase' : IntegrableOn (fun x : ℝ => x ^ σ * Real.exp (-x)) (Ioi 0) := by
    refine hbase.congr_fun (fun x _ => ?_) measurableSet_Ioi
    simp only [add_sub_cancel_right]
    ring
  have hscale := (integrableOn_Ioi_comp_mul_left_iff
    (fun x : ℝ => x ^ σ * Real.exp (-x)) 0 ha).mpr (by simpa using hbase')
  have hconst : IntegrableOn
      (fun t : ℝ => (a ^ σ)⁻¹ * ((a * t) ^ σ * Real.exp (-(a * t)))) (Ioi 0) :=
    hscale.const_mul _
  refine hconst.congr_fun (fun t ht => ?_) measurableSet_Ioi
  have ht0 : (0 : ℝ) < t := ht
  show (a ^ σ)⁻¹ * ((a * t) ^ σ * Real.exp (-(a * t))) = t ^ σ * Real.exp (-(a * t))
  rw [Real.mul_rpow ha.le ht0.le]
  field_simp

/-- **Convergence of the complex-rate Euler integral.**  For `Re s > 0` and `Re w > 0` the
integrand `t^(s-1) e^(-w t)` is integrable on the half-line. -/
theorem integrableOn_cpow_mul_exp_neg_mul_Ioi {s w : ℂ} (hs : 0 < s.re) (hw : 0 < w.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) * Complex.exp (-(w * t))) (Ioi 0) := by
  have hmeas : AEStronglyMeasurable
      (fun t : ℝ => (t : ℂ) ^ (s - 1) * Complex.exp (-(w * t))) (volume.restrict (Ioi 0)) := by
    refine ((continuousOn_of_forall_continuousAt fun t ht => ?_).aestronglyMeasurable
      measurableSet_Ioi)
    have ht0 : (0 : ℝ) < t := ht
    exact (Complex.continuousAt_ofReal_cpow_const t (s - 1) (Or.inr (ne_of_gt ht0))).mul
      ((Complex.continuous_exp.comp
        (continuous_const.mul Complex.continuous_ofReal).neg).continuousAt)
  have hdom : IntegrableOn (fun t : ℝ => t ^ (s.re - 1) * Real.exp (-(w.re * t))) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_Ioi (by linarith) hw
  refine Integrable.mono' hdom hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : (0 : ℝ) < t := ht
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
  have hexp : ‖Complex.exp (-(w * t))‖ = Real.exp (-(w.re * t)) := by
    rw [Complex.norm_exp]
    congr 1
    simp
  rw [hexp, Complex.sub_re, Complex.one_re]

end

end GaloisForLFunctions.HTGeometry
