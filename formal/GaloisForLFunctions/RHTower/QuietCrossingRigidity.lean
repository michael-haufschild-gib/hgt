/-
The smoothed Perron kernel and its Mellin inversion.

The second-order smoothing weight `g(u) = max(1 − u, 0)` has Mellin transform
`∫₀¹ (1 − u) u^{s−1} du = 1/s − 1/(s+1) = 1/(s(s+1))` on the right half-plane `Re s > 0`.
Its inverse Mellin representation is the smoothed Perron formula: for `c > 0` and `y > 0`,

    (1/2π) ∫_{t∈ℝ} y^{c+it} / ((c+it)(c+it+1)) dt = max(1 − 1/y, 0),

the vertical integral converging absolutely because the kernel `1/(s(s+1))` is `O(|t|^{-2})`
on the line `Re s = c`.  The kernel is the analytic engine of a Perron-type summation: paired
with an absolutely convergent Dirichlet series it turns the vertical-line integral of
`L(s)·x^{s+1}/(s(s+1))` into the piecewise-linear partial sum `Σ aₙ·max(x − n, 0)`.

* `perronKernelG` — the smoothing weight `u ↦ max(1 − u, 0)` as a `ℂ`-valued function.
* `perronKernel_mellin` — the closed form `mellin perronKernelG s = 1/(s(s+1))` for `Re s > 0`.
* `perronKernel_mellinConvergent` — Mellin convergence of the weight at every real abscissa
  `c > 0` (the weight is continuous and compactly supported towards `+∞`).
* `perronKernel_verticalIntegrable` — absolute convergence of the inverse-Mellin vertical
  integral: `t ↦ 1/((c+it)(c+it+1))` is integrable, dominated by `(c²+t²)⁻¹`.
* `perronKernel_inversion` — the smoothed Perron formula:
  `(1/2π)·∫_t y^{c+it}/((c+it)(c+it+1)) dt = max(1 − 1/y, 0)` for `c > 0`, `y > 0`.
-/
import Mathlib

open Complex MeasureTheory Filter Topology Asymptotics intervalIntegral Set

noncomputable section

namespace RHTower

/-- The second-order smoothing weight `g(u) = max(1 − u, 0)`, as a `ℂ`-valued function of a real
argument.  It is continuous, equals `1 − u` on `[0,1]`, and vanishes for `u ≥ 1`; its Mellin
transform is the smoothed Perron kernel `1/(s(s+1))`. -/
def perronKernelG (u : ℝ) : ℂ := ((max (1 - u) 0 : ℝ) : ℂ)

/-- The smoothing weight is continuous. -/
theorem continuous_perronKernelG : Continuous perronKernelG := by
  unfold perronKernelG; fun_prop

/-- **Mellin transform of the smoothing weight.**  For `Re s > 0`,
`mellin (u ↦ max(1 − u, 0)) s = 1/(s(s+1))`.  The weight is supported on `(0,1]`, where it equals
`1 − u`, so the Mellin integral collapses to `∫₀¹ (u^{s−1} − u^{s}) du = 1/s − 1/(s+1)`. -/
theorem perronKernel_mellin {s : ℂ} (hs : 0 < s.re) :
    mellin perronKernelG s = 1 / (s * (s + 1)) := by
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; simp at hs
  have hs1 : s + 1 ≠ 0 := by
    intro h
    have : (s + 1).re = 0 := by rw [h]; simp
    rw [Complex.add_re, Complex.one_re] at this; linarith
  rw [mellin]
  -- The integrand vanishes off `(0,1]`, so the Mellin integral collapses to `∫ over Ioc 0 1`.
  have hrestrict : ∫ t in Ioi (0:ℝ), (t:ℂ)^(s-1) • perronKernelG t
      = ∫ t in Ioc (0:ℝ) 1, (t:ℂ)^(s-1) • perronKernelG t := by
    rw [← MeasureTheory.setIntegral_eq_of_subset_of_forall_diff_eq_zero
      (t := Ioi (0:ℝ)) (s := Ioc (0:ℝ) 1) measurableSet_Ioi Ioc_subset_Ioi_self ?_]
    intro x hx
    obtain ⟨hx0, hx1⟩ := hx
    simp only [mem_Ioi] at hx0
    simp only [mem_Ioc, not_and, not_le] at hx1
    have hgt : 1 < x := hx1 hx0
    have hz : perronKernelG x = 0 := by
      simp only [perronKernelG]; rw [max_eq_right (by linarith)]; simp
    rw [hz, smul_zero]
  rw [hrestrict, ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  -- On `[0,1]` the integrand is `u^{s−1} − u^{s}`.
  have hcongr : ∫ t in (0:ℝ)..1, (t:ℂ)^(s-1) • perronKernelG t
      = ∫ t in (0:ℝ)..1, ((t:ℂ)^(s-1) - (t:ℂ)^s) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
    obtain ⟨ht0, ht1⟩ := ht
    dsimp only
    have hg : perronKernelG t = ((1 - t : ℝ) : ℂ) := by
      simp only [perronKernelG]; rw [max_eq_left (by linarith)]
    rw [hg, smul_eq_mul]
    push_cast
    rcases eq_or_lt_of_le ht0 with h0 | h0
    · rw [← h0]
      simp only [Complex.ofReal_zero, sub_zero, mul_one, Complex.zero_cpow hs0, sub_zero]
    · have htne : (t:ℂ) ≠ 0 := by exact_mod_cast ne_of_gt h0
      have hcp : (t:ℂ)^s = (t:ℂ)^(s-1) * (t:ℂ) := by
        conv_lhs => rw [show s = (s-1) + 1 by ring]
        rw [Complex.cpow_add _ _ htne, Complex.cpow_one]
      rw [mul_sub, mul_one, hcp]
  rw [hcongr]
  have hi1 : IntervalIntegrable (fun t:ℝ => (t:ℂ)^(s-1)) volume 0 1 :=
    (intervalIntegrable_cpow' (by simp only [Complex.sub_re, Complex.one_re]; linarith)).symm
  have hi2 : IntervalIntegrable (fun t:ℝ => (t:ℂ)^s) volume 0 1 :=
    (intervalIntegrable_cpow' (by linarith)).symm
  rw [intervalIntegral.integral_sub hi1 hi2,
      integral_cpow (Or.inl (by simp only [Complex.sub_re, Complex.one_re]; linarith)),
      integral_cpow (Or.inl (by linarith))]
  have e1 : s - 1 + 1 = s := by ring
  rw [e1]
  simp only [Complex.ofReal_one, Complex.one_cpow, Complex.ofReal_zero,
    Complex.zero_cpow hs0, Complex.zero_cpow hs1]
  field_simp
  ring

/-- **Mellin convergence of the smoothing weight.**  At every real abscissa `c > 0` the weight
`u ↦ max(1 − u, 0)` is Mellin convergent: it is continuous (hence locally integrable), it vanishes
identically near `+∞`, and it is bounded near `0`. -/
theorem perronKernel_mellinConvergent {c : ℝ} (hc : 0 < c) :
    MellinConvergent perronKernelG (↑c : ℂ) := by
  apply mellinConvergent_of_isBigO_rpow (a := c+1) (b := 0)
  · exact (continuous_perronKernelG.locallyIntegrable).locallyIntegrableOn _
  · have h0 : perronKernelG =ᶠ[atTop] (fun _ => (0:ℂ)) := by
      filter_upwards [eventually_ge_atTop (1:ℝ)] with x hx
      simp only [perronKernelG]; rw [max_eq_right (by linarith)]; simp
    exact h0.isBigO.trans (isBigO_zero _ _)
  · simp only [Complex.ofReal_re]; linarith
  · have h1 : (fun x:ℝ => x^(-(0:ℝ))) = (fun _ => (1:ℝ)) := by
      funext x; rw [neg_zero, Real.rpow_zero]
    rw [h1]
    exact ((continuous_perronKernelG.tendsto 0).mono_left nhdsWithin_le_nhds).isBigO_one ℝ
  · simp only [Complex.ofReal_re]; exact hc

/-- The reciprocal quadratic `t ↦ (c²+t²)⁻¹` is Lebesgue integrable for `c > 0`; it is the
`c`-scaled Cauchy profile `c⁻²·(1+(t/c)²)⁻¹`. -/
private theorem inv_quad_integrable {c : ℝ} (hc : 0 < c) :
    Integrable (fun t:ℝ => (c^2 + t^2)⁻¹) := by
  have hc0 : c⁻¹ ≠ 0 := inv_ne_zero (ne_of_gt hc)
  have h1 : Integrable (fun t:ℝ => (1 + (c⁻¹ * t)^2)⁻¹) :=
    (integrable_inv_one_add_sq).comp_mul_left' hc0
  have heq : (fun t:ℝ => (c^2 + t^2)⁻¹) = fun t => (c^2)⁻¹ * (1 + (c⁻¹ * t)^2)⁻¹ := by
    funext t; rw [← mul_inv]; congr 1; field_simp
  rw [heq]; exact h1.const_mul _

/-- The denominator `(c+it)(c+it+1)` never vanishes when `c > 0`: both factors have positive real
part. -/
private theorem kernel_den_ne {c : ℝ} (hc : 0 < c) (t : ℝ) :
    (↑c + ↑t*I) * (↑c + ↑t*I + 1) ≠ 0 := by
  refine mul_ne_zero ?_ ?_
  · intro h; have := congrArg Complex.re h; simp at this; linarith
  · intro h; have := congrArg Complex.re h; simp at this; linarith

/-- The Perron kernel `t ↦ 1/((c+it)(c+it+1))` is continuous on the line `Re s = c > 0`. -/
private theorem kernel_continuous {c : ℝ} (hc : 0 < c) :
    Continuous (fun t:ℝ => ((↑c + ↑t*I) * (↑c + ↑t*I + 1))⁻¹) :=
  Continuous.inv₀ (by fun_prop) (kernel_den_ne hc)

/-- The Perron kernel is dominated by the reciprocal quadratic: `‖1/((c+it)(c+it+1))‖ ≤ (c²+t²)⁻¹`,
because `‖c+it‖ = √(c²+t²)` and `‖c+it+1‖ ≥ ‖c+it‖` (larger real part). -/
private theorem kernel_norm_le {c : ℝ} (hc : 0 < c) (t : ℝ) :
    ‖((↑c + ↑t*I) * (↑c + ↑t*I + 1))⁻¹‖ ≤ (c^2 + t^2)⁻¹ := by
  set A : ℂ := (↑c + ↑t*I) with hA
  set B : ℂ := (↑c + ↑t*I + 1) with hB
  have hAnorm : ‖A‖ = Real.sqrt (c^2 + t^2) := by rw [hA, Complex.norm_add_mul_I]
  have hApos : 0 < ‖A‖ := by rw [hAnorm]; apply Real.sqrt_pos.mpr; positivity
  have hBge : ‖A‖ ≤ ‖B‖ := by
    have hBnorm : ‖B‖ = Real.sqrt ((c+1)^2 + t^2) := by
      rw [hB]
      have h : (↑c + ↑t*I + 1 : ℂ) = ↑(c+1) + ↑t*I := by push_cast; ring
      rw [h, Complex.norm_add_mul_I]
    rw [hAnorm, hBnorm]; apply Real.sqrt_le_sqrt; nlinarith
  have hBpos : 0 < ‖B‖ := lt_of_lt_of_le hApos hBge
  rw [norm_inv, norm_mul, inv_le_inv₀ (mul_pos hApos hBpos) (by positivity)]
  calc c^2 + t^2 = ‖A‖ * ‖A‖ := by rw [hAnorm, Real.mul_self_sqrt (by positivity)]
    _ ≤ ‖A‖ * ‖B‖ := mul_le_mul_of_nonneg_left hBge (le_of_lt hApos)

/-- **Absolute convergence of the inverse-Mellin vertical integral.**  On the line `Re s = c > 0`
the Perron kernel `t ↦ 1/((c+it)(c+it+1))` is integrable: its modulus is dominated by
`(c²+t²)⁻¹`, since `‖c+it‖ = √(c²+t²)` and `‖c+it+1‖ ≥ ‖c+it‖`. -/
theorem perronKernel_verticalIntegrable {c : ℝ} (hc : 0 < c) :
    VerticalIntegrable (mellin perronKernelG) c volume := by
  rw [VerticalIntegrable]
  -- On the vertical line the transform is the explicit kernel.
  have hval : (fun t : ℝ => mellin perronKernelG (↑c + ↑t * I))
      = fun t : ℝ => ((↑c + ↑t * I) * (↑c + ↑t * I + 1))⁻¹ := by
    funext t
    rw [perronKernel_mellin (by simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.I_re, Complex.ofReal_im, Complex.I_im]; simp; linarith), one_div]
  rw [hval]
  refine (inv_quad_integrable hc).mono' (kernel_continuous hc).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall (fun t => kernel_norm_le hc t)

/-- **The smoothed Perron formula (Mellin inversion of the kernel).**  For `c > 0` and `y > 0`,

    (1/2π) ∫_{t∈ℝ} y^{c+it} / ((c+it)(c+it+1)) dt = max(1 − 1/y, 0).

This is Mellin inversion applied to `perronKernelG` at the point `1/y`: the transform is the
kernel `1/(s(s+1))`, the vertical integral converges absolutely (`O(|t|^{-2})`), and the weight is
continuous, so the inverse Mellin integral reproduces `perronKernelG (1/y) = max(1 − 1/y, 0)`.
The base change `(1/y)^{-(c+it)} = y^{c+it}` (valid for `y > 0`) rewrites the inversion integral
into the stated form. -/
theorem perronKernel_inversion {c : ℝ} (hc : 0 < c) {y : ℝ} (hy : 0 < y) :
    (1 / (2 * Real.pi) : ℝ) •
        ∫ t : ℝ, (↑y : ℂ)^((c:ℂ) + ↑t * I) / (((c:ℂ) + ↑t * I) * ((c:ℂ) + ↑t * I + 1))
      = ((max (1 - 1/y) 0 : ℝ) : ℂ) := by
  -- Base change and kernel evaluation turn the integrand into the inversion integrand.
  have hintegrand : (fun t : ℝ => (↑y : ℂ)^((c:ℂ) + ↑t * I) / (((c:ℂ) + ↑t * I) * ((c:ℂ) + ↑t * I + 1)))
      = (fun t : ℝ => (↑(1/y) : ℂ)^(-((c:ℂ) + ↑t * I)) • mellin perronKernelG ((c:ℂ) + ↑t * I)) := by
    funext t
    have hre : 0 < ((c:ℂ) + ↑t * I).re := by
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re,
        Complex.ofReal_im, Complex.I_im]; simp; linarith
    have hbase : (↑(1/y) : ℂ)^(-((c:ℂ) + ↑t * I)) = (↑y : ℂ)^((c:ℂ) + ↑t * I) := by
      rw [one_div, Complex.ofReal_inv,
        Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg hy.le]; exact Real.pi_pos.ne'.symm),
        Complex.cpow_neg, inv_inv]
    rw [perronKernel_mellin hre, smul_eq_mul, hbase, one_div, div_eq_mul_inv]
  rw [hintegrand]
  -- The transformed left side is exactly `mellinInv c (mellin perronKernelG) (1/y)`.
  have key : mellinInv c (mellin perronKernelG) (1/y) = perronKernelG (1/y) :=
    mellinInv_mellin_eq c perronKernelG (by positivity)
      (perronKernel_mellinConvergent hc) (perronKernel_verticalIntegrable hc)
      (continuous_perronKernelG.continuousAt)
  rw [show (1 / (2 * Real.pi) : ℝ) •
        ∫ t : ℝ, (↑(1/y) : ℂ)^(-((c:ℂ) + ↑t * I)) • mellin perronKernelG ((c:ℂ) + ↑t * I)
      = mellinInv c (mellin perronKernelG) (1/y) from rfl, key]
  simp only [perronKernelG]

end RHTower
