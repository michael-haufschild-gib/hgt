import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# The removable singularity of the Barnes cone kernel at the origin

The Mellin representation of the Barnes double zeta,

```text
Γ(s) ζ₂(s, x) = ∫_0^∞ t^(s-1) e^(-x t) / ((1 - e^(-ω₁ t))(1 - e^(-ω₂ t))) dt,
```

converges only for `Re s > 2`, because the kernel has a pole of order two at `t = 0`.  Continuing
past `s = 2` means subtracting the singular part, and that requires knowing that

```text
t² · e^(-x t) / ((1 - e^(-ω₁ t))(1 - e^(-ω₂ t)))
```

extends across `t = 0`.  The whole point is one factor: `z / (1 - e^(-ω z))` has a removable
singularity at the origin with value `1/ω`, because the denominator vanishes to first order there.

`hasDerivAt_one_sub_exp_neg_mul` is that first-order vanishing, and
`tendsto_div_one_sub_exp_neg_mul` is the resulting limit, obtained by reading the reciprocal of the
difference quotient — the division-by-zero convention makes `(slope)⁻¹` equal `z / (1 - e^(-ω z))`
identically, so no case split on the denominator is needed.
-/

open Complex Filter Metric
open scoped Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The denominator of the cylinder kernel vanishes to first order at the origin. -/
theorem hasDerivAt_one_sub_exp_neg_mul (o : ℂ) :
    HasDerivAt (fun z : ℂ => 1 - Complex.exp (-(o * z))) o 0 := by
  have hlin : HasDerivAt (fun z : ℂ => -(o * z)) (-o) 0 := by
    have h0 : HasDerivAt (fun z : ℂ => (-o) * z) (-o) 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).const_mul (-o)
    refine h0.congr_of_eventuallyEq ?_
    filter_upwards with z
    ring
  have hexp := hlin.cexp
  have h := hexp.const_sub (1 : ℂ)
  simpa using h

@[simp] theorem one_sub_exp_neg_mul_zero (o : ℂ) :
    (fun z : ℂ => 1 - Complex.exp (-(o * z))) 0 = 0 := by
  simp

/-- **The kernel factor has a removable singularity at the origin.**  As `z → 0`,

```text
z / (1 - e^(-ω z)) → 1/ω,
```

which is why `t² F(t)` extends continuously across `t = 0` for the two-dimensional cone kernel. -/
theorem tendsto_div_one_sub_exp_neg_mul {o : ℂ} (ho : o ≠ 0) :
    Tendsto (fun z : ℂ => z / (1 - Complex.exp (-(o * z)))) (𝓝[≠] (0 : ℂ)) (𝓝 o⁻¹) := by
  have hslope : Tendsto (slope (fun z : ℂ => 1 - Complex.exp (-(o * z))) 0) (𝓝[≠] (0 : ℂ))
      (𝓝 o) := hasDerivAt_iff_tendsto_slope.mp (hasDerivAt_one_sub_exp_neg_mul o)
  have hinv := hslope.inv₀ ho
  refine hinv.congr fun z => ?_
  rw [slope_def_field]
  simp only [mul_zero, neg_zero, Complex.exp_zero, sub_self, sub_zero]
  rw [inv_div]

/-- Near the origin the kernel denominator vanishes only at the origin: its other zeros sit on the
lattice `2πi ℤ / ω`. -/
theorem one_sub_exp_neg_mul_ne_zero {o z : ℂ} (ho : o ≠ 0) (hz : z ≠ 0)
    (hsmall : ‖o * z‖ < 2 * Real.pi) : 1 - Complex.exp (-(o * z)) ≠ 0 := by
  intro h
  have h1 : Complex.exp (-(o * z)) = 1 := by linear_combination -h
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h1
  have hnorm : ‖o * z‖ = |(n : ℝ)| * (2 * Real.pi) := by
    have hneg : o * z = -((n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) := by
      linear_combination -hn
    rw [hneg, norm_neg, norm_mul]
    have h2 : ‖(2 : ℂ) * (Real.pi : ℂ) * Complex.I‖ = 2 * Real.pi := by
      rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos Real.pi_pos]
      simp
    rw [h2]
    simp
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hlt : |(n : ℝ)| * (2 * Real.pi) < 1 * (2 * Real.pi) := by
    rw [one_mul, ← hnorm]
    exact hsmall
  have hn1 : |(n : ℝ)| < 1 := lt_of_mul_lt_mul_right hlt hpi.le
  have hn0 : n = 0 := by
    by_contra hne
    have : (1 : ℝ) ≤ |(n : ℝ)| := by
      have : (1 : ℤ) ≤ |n| := Int.one_le_abs (by exact_mod_cast hne)
      calc (1 : ℝ) ≤ (|n| : ℤ) := by exact_mod_cast this
        _ = |(n : ℝ)| := by push_cast [Int.cast_abs]; rfl
    linarith
  rw [hn0] at hn
  simp only [Int.cast_zero, zero_mul] at hn
  have : o * z = 0 := by linear_combination -hn
  rcases mul_eq_zero.mp this with h' | h'
  · exact ho h'
  · exact hz h'

/-- The kernel factor `z / (1 - e^(-ω z))`, extended across the origin by its limit `1/ω`. -/
def cylKernelFactor (o : ℂ) (z : ℂ) : ℂ :=
  if z = 0 then o⁻¹ else z / (1 - Complex.exp (-(o * z)))

@[simp] theorem cylKernelFactor_zero (o : ℂ) : cylKernelFactor o 0 = o⁻¹ := by
  simp [cylKernelFactor]

theorem cylKernelFactor_of_ne {o z : ℂ} (hz : z ≠ 0) :
    cylKernelFactor o z = z / (1 - Complex.exp (-(o * z))) := by
  simp [cylKernelFactor, hz]

theorem cylKernelFactor_eventuallyEq (o : ℂ) :
    cylKernelFactor o =ᶠ[𝓝[≠] (0 : ℂ)] fun z => z / (1 - Complex.exp (-(o * z))) := by
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact cylKernelFactor_of_ne hz

/-- The extended kernel factor is continuous at the origin. -/
theorem continuousAt_cylKernelFactor {o : ℂ} (ho : o ≠ 0) :
    ContinuousAt (cylKernelFactor o) 0 := by
  have h1 : Tendsto (cylKernelFactor o) (𝓝[≠] (0 : ℂ)) (𝓝 (cylKernelFactor o 0)) := by
    rw [cylKernelFactor_zero]
    exact (tendsto_div_one_sub_exp_neg_mul ho).congr'
      (cylKernelFactor_eventuallyEq o).symm
  have h2 : Tendsto (cylKernelFactor o) (pure (0 : ℂ)) (𝓝 (cylKernelFactor o 0)) :=
    tendsto_pure_nhds _ _
  have h := h1.sup h2
  rw [nhdsNE_sup_pure] at h
  exact h

/-- Off the origin, and inside the disc of radius `2π/‖ω‖`, the extended kernel factor is
holomorphic. -/
theorem eventually_differentiableAt_cylKernelFactor {o : ℂ} (ho : o ≠ 0) :
    ∀ᶠ z in 𝓝[≠] (0 : ℂ), DifferentiableAt ℂ (cylKernelFactor o) z := by
  have hno : 0 < ‖o‖ := norm_pos_iff.mpr ho
  have hr : 0 < 2 * Real.pi / ‖o‖ := by positivity
  have hball : Metric.ball (0 : ℂ) (2 * Real.pi / ‖o‖) ∈ 𝓝 (0 : ℂ) := Metric.ball_mem_nhds _ hr
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hball] with z hz hzb
  have hz0 : z ≠ 0 := hz
  have hznorm : ‖z‖ < 2 * Real.pi / ‖o‖ := by
    simpa [Complex.dist_eq, sub_zero] using (Metric.mem_ball.mp hzb)
  have hsmall : ‖o * z‖ < 2 * Real.pi := by
    rw [norm_mul]
    calc ‖o‖ * ‖z‖ < ‖o‖ * (2 * Real.pi / ‖o‖) := by
          exact mul_lt_mul_of_pos_left hznorm hno
      _ = 2 * Real.pi := by field_simp
  have hne : 1 - Complex.exp (-(o * z)) ≠ 0 := one_sub_exp_neg_mul_ne_zero ho hz0 hsmall
  have hUopen : IsOpen (Metric.ball (0 : ℂ) (2 * Real.pi / ‖o‖) ∩ {(0 : ℂ)}ᶜ) :=
    Metric.isOpen_ball.inter isOpen_compl_singleton
  have hzU : z ∈ Metric.ball (0 : ℂ) (2 * Real.pi / ‖o‖) ∩ {(0 : ℂ)}ᶜ := ⟨hzb, hz⟩
  have heq : cylKernelFactor o =ᶠ[𝓝 z] fun w => w / (1 - Complex.exp (-(o * w))) := by
    filter_upwards [hUopen.mem_nhds hzU] with w hw
    exact cylKernelFactor_of_ne hw.2
  refine (Filter.EventuallyEq.differentiableAt_iff heq).mpr ?_
  have hnum : DifferentiableAt ℂ (fun w : ℂ => w) z := differentiableAt_id
  have hden : DifferentiableAt ℂ (fun w : ℂ => 1 - Complex.exp (-(o * w))) z := by
    fun_prop
  exact hnum.div hden hne

/-- **The cylinder kernel factor is analytic across the origin.**  The removable singularity of
`z ↦ z / (1 - e^(-ω z))` at `z = 0` is filled in by the value `1/ω`; the resulting function is
analytic there.  This is the fact that lets the two-dimensional Barnes cone kernel be written as
`t^(-2)` times a function analytic at the origin, which is what makes the singular part
subtractable and the Mellin integral continuable past `s = 2`. -/
theorem analyticAt_cylKernelFactor {o : ℂ} (ho : o ≠ 0) :
    AnalyticAt ℂ (cylKernelFactor o) 0 :=
  Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
    (eventually_differentiableAt_cylKernelFactor ho) (continuousAt_cylKernelFactor ho)


end

end GaloisForLFunctions.HTGeometry
