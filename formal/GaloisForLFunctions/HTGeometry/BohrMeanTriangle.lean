import GaloisForLFunctions.HTGeometry.BohrMultiFejerMean

/-!
# The triangle inequality for the mean, and the approximate-identity error term

The convergence step of the Bochner–Fejér argument rests on two elementary facts.

First, a kernel of mean one turns the convolution error into a mean of differences:
`M_u(f(u+t)K(u)) − f(t) = M_u((f(u+t) − f(t))·K(u))`, because `M_u(f(t)K(u)) = f(t)·M(K) = f(t)`.

Second, the mean obeys the triangle inequality: `‖M(g)‖ ≤ M(‖g‖)`, since each window average does.
Applied to a nonnegative kernel this bounds the error by `M_u(‖f(u+t) − f(t)‖·k(u))`, which is the
quantity the concentration of the kernel controls.
-/

open Filter Topology

namespace GaloisForLFunctions

noncomputable section

open scoped BigOperators

/-- The modulus of an almost-periodic function is almost periodic. -/
theorem isBohrAlmostPeriodic_norm {g : ℝ → ℂ} (hga : HTGeometry.IsBohrAlmostPeriodic g) :
    HTGeometry.IsBohrAlmostPeriodic fun u => ((‖g u‖ : ℝ) : ℂ) := by
  intro ε hε
  obtain ⟨L, hL, hdense⟩ := hga ε hε
  refine ⟨L, hL, fun a => ?_⟩
  obtain ⟨τ, hτmem, hτ⟩ := hdense a
  refine ⟨τ, hτmem, fun x => ?_⟩
  have h : ‖((‖g (x + τ)‖ : ℝ) : ℂ) - ((‖g x‖ : ℝ) : ℂ)‖ = |‖g (x + τ)‖ - ‖g x‖| := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [h]
  exact le_trans (abs_norm_sub_norm_le _ _) (hτ x)

/-- **Triangle inequality for the mean.** -/
theorem norm_bohrMean_le_re_bohrMean_norm {g : ℝ → ℂ} (hgc : Continuous g)
    (hga : HTGeometry.IsBohrAlmostPeriodic g) :
    ‖bohrMean g‖ ≤ (bohrMean fun u => ((‖g u‖ : ℝ) : ℂ)).re := by
  have hnc : Continuous fun u : ℝ => ((‖g u‖ : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp hgc.norm
  have hna : HTGeometry.IsBohrAlmostPeriodic fun u : ℝ => ((‖g u‖ : ℝ) : ℂ) :=
    isBohrAlmostPeriodic_norm hga
  have hlimL : Tendsto (fun T : ℝ => ‖windowAverage g T‖) atTop (nhds ‖bohrMean g‖) :=
    (continuous_norm.tendsto _).comp (tendsto_windowAverage_bohrMean hgc hga)
  have hlimR : Tendsto
      (fun T : ℝ => (windowAverage (fun u => ((‖g u‖ : ℝ) : ℂ)) T).re) atTop
      (nhds (bohrMean fun u => ((‖g u‖ : ℝ) : ℂ)).re) :=
    (Complex.continuous_re.tendsto _).comp (tendsto_windowAverage_bohrMean hnc hna)
  refine le_of_tendsto_of_tendsto hlimL hlimR ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  have hint : ‖∫ t in (0 : ℝ)..T, g t‖ ≤ ∫ t in (0 : ℝ)..T, ‖g t‖ :=
    intervalIntegral.norm_integral_le_integral_norm hT.le
  have hre : (windowAverage (fun u => ((‖g u‖ : ℝ) : ℂ)) T).re
      = T⁻¹ * ∫ t in (0 : ℝ)..T, ‖g t‖ := by
    simp only [windowAverage, intervalIntegral.integral_ofReal, Complex.real_smul]
    rw [← Complex.ofReal_mul, Complex.ofReal_re]
  rw [hre]
  simp only [windowAverage, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr hT.le)]
  exact mul_le_mul_of_nonneg_left hint (inv_nonneg.mpr hT.le)

/-- **A kernel of mean one turns the convolution error into a mean of differences.** -/
theorem bohrMean_translate_mul_kernel_sub {f K : ℝ → ℂ} (hfc : Continuous f)
    (hfa : HTGeometry.IsBohrAlmostPeriodic f) (hKc : Continuous K)
    (hKa : HTGeometry.IsBohrAlmostPeriodic K) (hK1 : bohrMean K = 1) (t : ℝ) :
    bohrMean (fun u => f (u + t) * K u) - f t
      = bohrMean fun u => (f (u + t) - f t) * K u := by
  have hfct : Continuous fun u : ℝ => f (u + t) := hfc.comp (continuous_id.add continuous_const)
  have hfat : HTGeometry.IsBohrAlmostPeriodic fun u : ℝ => f (u + t) :=
    isBohrAlmostPeriodic_comp_add_const hfa t
  have hconst : bohrMean (fun u => f t * K u) = f t := by
    rw [bohrMean_const_mul (f := K) (f t) hKc hKa, hK1, mul_one]
  have hsub : (fun u : ℝ => (f (u + t) - f t) * K u)
      = fun u : ℝ => f (u + t) * K u - f t * K u := funext fun u => by ring
  rw [hsub, bohrMean_sub (f := fun u : ℝ => f (u + t) * K u) (g := fun u : ℝ => f t * K u)
    (hfct.mul hKc) (isBohrAlmostPeriodic_mul hfct hfat hKc hKa)
    (continuous_const.mul hKc) (isBohrAlmostPeriodic_const_mul _ hKa), hconst]

/-- **The approximate-identity error estimate.**  For a nonnegative kernel of mean one the
convolution error is bounded by the mean of `‖f(u+t) − f(t)‖ · k(u)`. -/
theorem norm_bohrMean_translate_mul_kernel_sub_le {f : ℝ → ℂ} {k : ℝ → ℝ}
    (hfc : Continuous f) (hfa : HTGeometry.IsBohrAlmostPeriodic f)
    (hkc : Continuous fun u => ((k u : ℝ) : ℂ))
    (hka : HTGeometry.IsBohrAlmostPeriodic fun u => ((k u : ℝ) : ℂ))
    (hknn : ∀ u, 0 ≤ k u) (hk1 : bohrMean (fun u => ((k u : ℝ) : ℂ)) = 1) (t : ℝ) :
    ‖bohrMean (fun u => f (u + t) * ((k u : ℝ) : ℂ)) - f t‖
      ≤ (bohrMean fun u => (((‖f (u + t) - f t‖ * k u : ℝ)) : ℂ)).re := by
  have hfct : Continuous fun u : ℝ => f (u + t) := hfc.comp (continuous_id.add continuous_const)
  have hfat : HTGeometry.IsBohrAlmostPeriodic fun u : ℝ => f (u + t) :=
    isBohrAlmostPeriodic_comp_add_const hfa t
  have hdc : Continuous fun u : ℝ => (f (u + t) - f t) * ((k u : ℝ) : ℂ) :=
    (hfct.sub continuous_const).mul hkc
  have hda : HTGeometry.IsBohrAlmostPeriodic fun u : ℝ => (f (u + t) - f t) * ((k u : ℝ) : ℂ) :=
    isBohrAlmostPeriodic_mul (hfct.sub continuous_const)
      (isBohrAlmostPeriodic_sub hfct hfat continuous_const (isBohrAlmostPeriodic_const _))
      hkc hka
  rw [bohrMean_translate_mul_kernel_sub hfc hfa hkc hka hk1 t]
  have hnorm : (fun u : ℝ => ((‖(f (u + t) - f t) * ((k u : ℝ) : ℂ)‖ : ℝ) : ℂ))
      = fun u : ℝ => (((‖f (u + t) - f t‖ * k u : ℝ)) : ℂ) := by
    funext u
    congr 1
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hknn u)]
  have h := norm_bohrMean_le_re_bohrMean_norm hdc hda
  rwa [hnorm] at h

end

end GaloisForLFunctions
