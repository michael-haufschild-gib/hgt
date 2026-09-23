import GaloisForLFunctions.HTGeometry.PoissonKernelIntegrals

/-!
# The Riesz-mean kernel on a vertical line

The second-order Riesz mean of a Dirichlet series is represented by the contour integral of
`F(s+w) e^{λ w} / w²` along a vertical line `Re w = c > 0`.  The size of that representation is
governed entirely by the kernel, whose absolute value on the line is a Poisson profile:

```text
‖ e^{λ w} / w² ‖ = e^{λ c} / (c² + t²) ,        w = c + i t ,
```

so the normalised line integral is

```text
(2π)⁻¹ ∫ ‖e^{λ w}/w²‖ dt = e^{λ c} / (2 c) .
```

Minimising over the free abscissa `c > 0` gives `e λ / 2`, attained at `c = 1/λ`; the minimality is
the elementary inequality `x ≤ e^{x-1}`.  This is the quantitative heart of Bohr's estimate: a
Dirichlet series bounded by `M` on a half-plane has Riesz means bounded by `M e λ / 2` there, and it
is the linear growth in `λ` that eventually yields the logarithmic bound on the partial sums.
-/

noncomputable section

open MeasureTheory Real Complex

namespace GaloisForLFunctions.RHTower

/-- The Riesz-mean kernel `e^{λw}/w²` at the point `w = c + i t` of a vertical line. -/
def rieszKernel (lam c t : ℝ) : ℂ :=
  Complex.exp ((lam : ℂ) * ((c : ℂ) + (t : ℂ) * Complex.I))
    / ((c : ℂ) + (t : ℂ) * Complex.I) ^ (2 : ℕ)

/-- **The kernel has a Poisson profile on the line.** -/
theorem norm_rieszKernel {c : ℝ} (hc : 0 < c) (lam t : ℝ) :
    ‖rieszKernel lam c t‖ = Real.exp (lam * c) / (c ^ (2 : ℕ) + t ^ (2 : ℕ)) := by
  have hpos : (0 : ℝ) < c ^ (2 : ℕ) + t ^ (2 : ℕ) := by positivity
  have hnorm : ‖(c : ℂ) + (t : ℂ) * Complex.I‖ = Real.sqrt (c ^ (2 : ℕ) + t ^ (2 : ℕ)) := by
    rw [Complex.norm_eq_sqrt_sq_add_sq]
    simp
  have hsq : ‖((c : ℂ) + (t : ℂ) * Complex.I) ^ (2 : ℕ)‖ = c ^ (2 : ℕ) + t ^ (2 : ℕ) := by
    rw [norm_pow, hnorm, Real.sq_sqrt hpos.le]
  have hre : ((lam : ℂ) * ((c : ℂ) + (t : ℂ) * Complex.I)).re = lam * c := by
    simp
  rw [rieszKernel, norm_div, Complex.norm_exp, hre, hsq]

/-- The kernel profile is integrable along the line. -/
theorem integrable_norm_rieszKernel {c : ℝ} (hc : 0 < c) (lam : ℝ) :
    Integrable (fun t : ℝ => ‖rieszKernel lam c t‖) := by
  have hbase := (HTGeometry.integrable_inv_sq_add_sq hc).const_mul (Real.exp (lam * c))
  refine hbase.congr (Filter.Eventually.of_forall fun t => ?_)
  show Real.exp (lam * c) * (c ^ (2 : ℕ) + t ^ (2 : ℕ))⁻¹ = ‖rieszKernel lam c t‖
  rw [norm_rieszKernel hc lam t, div_eq_mul_inv]

/-- **The normalised line integral of the kernel.** -/
theorem integral_norm_rieszKernel {c : ℝ} (hc : 0 < c) (lam : ℝ) :
    (2 * Real.pi)⁻¹ * (∫ t : ℝ, ‖rieszKernel lam c t‖) = Real.exp (lam * c) / (2 * c) := by
  have hval : (∫ t : ℝ, ‖rieszKernel lam c t‖)
      = Real.exp (lam * c) * (Real.pi / c) := by
    have hcongr : (fun t : ℝ => ‖rieszKernel lam c t‖)
        = fun t : ℝ => Real.exp (lam * c) * (c ^ (2 : ℕ) + t ^ (2 : ℕ))⁻¹ := by
      funext t
      rw [norm_rieszKernel hc lam t, div_eq_mul_inv]
    rw [hcongr, integral_const_mul, HTGeometry.integral_inv_sq_add_sq hc]
  rw [hval]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

/-- **The optimal abscissa.**  At `c = 1/λ` the bound is `e λ / 2`. -/
theorem rieszKernel_bound_at_optimum {lam : ℝ} (hlam : 0 < lam) :
    Real.exp (lam * (1 / lam)) / (2 * (1 / lam)) = Real.exp 1 * lam / 2 := by
  have hne : lam ≠ 0 := ne_of_gt hlam
  rw [mul_one_div, div_self hne]
  field_simp

/-- **`e λ / 2` is the minimum over all admissible abscissas**, by `x ≤ e^{x-1}`. -/
theorem rieszKernel_bound_min {lam c : ℝ} (hlam : 0 < lam) (hc : 0 < c) :
    Real.exp 1 * lam / 2 ≤ Real.exp (lam * c) / (2 * c) := by
  have hx : lam * c ≤ Real.exp (lam * c - 1) + 0 := by
    have h := Real.add_one_le_exp (lam * c - 1)
    linarith
  have hstep : Real.exp 1 * (lam * c) ≤ Real.exp (lam * c) := by
    have h1 : Real.exp 1 * Real.exp (lam * c - 1) = Real.exp (lam * c) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc Real.exp 1 * (lam * c) ≤ Real.exp 1 * (Real.exp (lam * c - 1) + 0) :=
          mul_le_mul_of_nonneg_left hx (Real.exp_pos 1).le
      _ = Real.exp (lam * c) := by rw [add_zero, h1]
  have h2c : (0 : ℝ) < 2 * c := by positivity
  have key : Real.exp 1 * lam / 2 * (2 * c) ≤ Real.exp (lam * c) := by
    calc Real.exp 1 * lam / 2 * (2 * c) = Real.exp 1 * (lam * c) := by ring
      _ ≤ Real.exp (lam * c) := hstep
  calc Real.exp 1 * lam / 2
      = Real.exp 1 * lam / 2 * (2 * c) / (2 * c) := by field_simp
    _ ≤ Real.exp (lam * c) / (2 * c) := by gcongr

/-- **The Riesz-mean kernel bound.**  The normalised line integral of the kernel at the optimal
abscissa is `e λ / 2`, and no other abscissa does better. -/
theorem integral_norm_rieszKernel_optimum {lam : ℝ} (hlam : 0 < lam) :
    (2 * Real.pi)⁻¹ * (∫ t : ℝ, ‖rieszKernel lam (1 / lam) t‖) = Real.exp 1 * lam / 2 := by
  have hc : 0 < 1 / lam := by positivity
  rw [integral_norm_rieszKernel hc lam, rieszKernel_bound_at_optimum hlam]

end GaloisForLFunctions.RHTower

end
