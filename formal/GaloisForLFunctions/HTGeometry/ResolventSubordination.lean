import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import GaloisForLFunctions.HTGeometry.TwoSidedExponentialMoments

/-!
# Subordination of the logarithmic symbol to the resolvent family

The logarithmic symbol is an absolutely convergent superposition of resolvent symbols,

`log (1+z) = ∫₀^∞ [(1+λ)⁻¹ - (1+λ+z)⁻¹] dλ`,

and each resolvent symbol `(μ² + 4π²ξ²)⁻¹` is the Fourier transform of the two-sided exponential
kernel `e^{-μ|x|}/(2μ)`.  Superposing the kernels in the same parameter gives

`∫₀^∞ e^{-√(1+λ)·r} / (2√(1+λ)) dλ = e^{-r}/r`,

so the logarithmic symbol carries the off-diagonal kernel `e^{-r}/(2r)`: a Carleman singularity
times a bounded exponential factor.
-/

open Set MeasureTheory Filter Topology
open scoped FourierTransform

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## The two scalar superposition integrals -/

/-- The exponential ray integral in the subordination parameter. -/
theorem integral_Ioi_exp_neg_mul_right {r : ℝ} (hr : 0 < r) :
    (∫ μ in Ioi (1:ℝ), Real.exp (-(μ * r))) = Real.exp (-r) / r := by
  have hderiv : ∀ μ ∈ Ioi (1:ℝ),
      HasDerivAt (fun t : ℝ => -Real.exp (-(t * r)) / r) (Real.exp (-(μ * r))) μ := by
    intro μ _
    have hinner0 : HasDerivAt (fun t : ℝ => -(t * r)) (-(1 * r)) μ :=
      ((hasDerivAt_id' μ).mul_const r).neg
    rw [one_mul] at hinner0
    have hinner : HasDerivAt (fun t : ℝ => -(t * r)) (-r) μ := hinner0
    have hexp : HasDerivAt (fun t : ℝ => Real.exp (-(t * r))) (Real.exp (-(μ * r)) * -r) μ :=
      hinner.exp
    have hscaled := (hexp.neg).div_const r
    have hval : -(Real.exp (-(μ * r)) * -r) / r = Real.exp (-(μ * r)) := by
      field_simp
    rw [← hval]
    exact hscaled
  have hcont : ContinuousWithinAt (fun t : ℝ => -Real.exp (-(t * r)) / r) (Ici (1:ℝ)) 1 := by
    apply Continuous.continuousWithinAt
    fun_prop
  have hint : IntegrableOn (fun μ : ℝ => Real.exp (-(μ * r))) (Ioi (1:ℝ)) volume := by
    have h := exp_neg_integrableOn_Ioi (1:ℝ) hr
    refine h.congr_fun (fun x _ => ?_) measurableSet_Ioi
    show Real.exp (-r * x) = Real.exp (-(x * r))
    rw [show -r * x = -(x * r) by ring]
  have hlim : Tendsto (fun t : ℝ => -Real.exp (-(t * r)) / r) atTop (𝓝 0) := by
    have hexp : Tendsto (fun t : ℝ => Real.exp (-(t * r))) atTop (𝓝 0) := by
      have hlin : Tendsto (fun t : ℝ => -(t * r)) atTop atBot := by
        have : Tendsto (fun t : ℝ => t * r) atTop atTop :=
          Filter.Tendsto.atTop_mul_const hr tendsto_id
        exact tendsto_neg_atTop_atBot.comp this
      exact Real.tendsto_exp_atBot.comp hlin
    have := (hexp.neg).div_const r
    simpa using this
  have h := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint hlim
  rw [h, one_mul]
  ring

/-- **The logarithmic symbol as a resolvent superposition.** -/
theorem integral_Ioi_resolvent_diff {z : ℝ} (hz : 0 ≤ z) :
    (∫ l in Ioi (0:ℝ), ((1 + l)⁻¹ - (1 + l + z)⁻¹)) = Real.log (1 + z) := by
  have hpos : ∀ l ∈ Ioi (0:ℝ), (0:ℝ) < 1 + l := fun l hl => by
    have : (0:ℝ) < l := hl
    linarith
  have hposz : ∀ l ∈ Ioi (0:ℝ), (0:ℝ) < 1 + l + z := fun l hl => by
    have : (0:ℝ) < l := hl
    linarith
  have hderiv : ∀ l ∈ Ioi (0:ℝ),
      HasDerivAt (fun t : ℝ => Real.log (1 + t) - Real.log (1 + t + z))
        ((1 + l)⁻¹ - (1 + l + z)⁻¹) l := by
    intro l hl
    have h1 : HasDerivAt (fun t : ℝ => 1 + t) 1 l := by
      simpa using (hasDerivAt_id' l).const_add (1:ℝ)
    have h2 : HasDerivAt (fun t : ℝ => 1 + t + z) 1 l := by
      simpa using ((hasDerivAt_id' l).const_add (1:ℝ)).add_const z
    have hl1 := h1.log (ne_of_gt (hpos l hl))
    have hl2 := h2.log (ne_of_gt (hposz l hl))
    have hd : HasDerivAt (fun t : ℝ => Real.log (1 + t) - Real.log (1 + t + z))
        (1 / (1 + l) - 1 / (1 + l + z)) l := hl1.sub hl2
    simp only [one_div] at hd
    exact hd
  have hnn : ∀ l ∈ Ioi (0:ℝ), 0 ≤ (1 + l)⁻¹ - (1 + l + z)⁻¹ := by
    intro l hl
    have hl0 : (0:ℝ) < l := hl
    have h1 := hpos l hl
    have h2 := hposz l hl
    have hmono : (1 + l + z)⁻¹ ≤ (1 + l)⁻¹ := inv_anti₀ h1 (by linarith)
    linarith
  have hlim : Tendsto (fun t : ℝ => Real.log (1 + t) - Real.log (1 + t + z)) atTop (𝓝 0) := by
    have hcongr : ∀ᶠ t : ℝ in atTop,
        Real.log (1 + t) - Real.log (1 + t + z) = -Real.log ((1 + t + z) / (1 + t)) := by
      filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
      have h1 : (0:ℝ) < 1 + t := by linarith
      have h2 : (0:ℝ) < 1 + t + z := by linarith
      rw [Real.log_div (ne_of_gt h2) (ne_of_gt h1)]
      ring
    have hratio : Tendsto (fun t : ℝ => (1 + t + z) / (1 + t)) atTop (𝓝 1) := by
      have hexpand : ∀ᶠ t : ℝ in atTop, (1 + t + z) / (1 + t) = 1 + z / (1 + t) := by
        filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
        have h1 : (1:ℝ) + t ≠ 0 := by
          have : (0:ℝ) < 1 + t := by linarith
          exact ne_of_gt this
        field_simp
      have hz0 : Tendsto (fun t : ℝ => z / (1 + t)) atTop (𝓝 0) := by
        have hden : Tendsto (fun t : ℝ => 1 + t) atTop atTop :=
          tendsto_atTop_add_const_left _ 1 tendsto_id
        exact hden.const_div_atTop z
      have := (tendsto_const_nhds (x := (1:ℝ)) (f := atTop (α := ℝ))).add hz0
      rw [add_zero] at this
      exact this.congr' (hexpand.mono fun t ht => ht.symm)
    have hlog : Tendsto (fun t : ℝ => Real.log ((1 + t + z) / (1 + t))) atTop
        (𝓝 (Real.log 1)) := (Real.continuousAt_log (by norm_num)).tendsto.comp hratio
    rw [Real.log_one] at hlog
    have := hlog.neg
    rw [neg_zero] at this
    exact this.congr' (hcongr.mono fun t ht => ht.symm)
  have hcont0 : ContinuousAt (fun t : ℝ => Real.log (1 + t) - Real.log (1 + t + z)) 0 := by
    have hc1 : ContinuousAt (fun t : ℝ => Real.log (1 + t)) 0 := by
      refine ContinuousAt.log (by fun_prop) ?_
      norm_num
    have hc2 : ContinuousAt (fun t : ℝ => Real.log (1 + t + z)) 0 := by
      refine ContinuousAt.log (by fun_prop) ?_
      simp
      linarith
    exact hc1.sub hc2
  have h := integral_Ioi_of_hasDerivAt_of_nonneg hcont0.continuousWithinAt hderiv hnn hlim
  rw [h]
  simp

/-! ## The resolvent kernel and its Fourier transform -/

/-- The ray integral of a decaying complex exponential. -/
theorem integral_Ioi_cexp_neg {c : ℂ} (hc : 0 < c.re) :
    (∫ x in Ioi (0:ℝ), Complex.exp (-(c * x))) = 1 / c := by
  have hcne : c ≠ 0 := by
    intro h
    rw [h] at hc
    simp at hc
  have hderiv : ∀ x ∈ Ioi (0:ℝ),
      HasDerivAt (fun t : ℝ => -Complex.exp (-(c * t)) / c) (Complex.exp (-(c * x))) x := by
    intro x _
    have hinner0 : HasDerivAt (fun t : ℝ => -(c * (t:ℂ))) (-(c * 1)) x :=
      ((Complex.ofRealCLM.hasDerivAt (x := x)).const_mul c).neg
    rw [mul_one] at hinner0
    have hinner : HasDerivAt (fun t : ℝ => -(c * (t:ℂ))) (-c) x := hinner0
    have hexp : HasDerivAt (fun t : ℝ => Complex.exp (-(c * (t:ℂ))))
        (Complex.exp (-(c * x)) * -c) x := hinner.cexp
    have hscaled := (hexp.neg).div_const c
    have hval : -(Complex.exp (-(c * x)) * -c) / c = Complex.exp (-(c * x)) := by
      field_simp
    rw [← hval]
    exact hscaled
  have hnorm : ∀ x : ℝ, ‖Complex.exp (-(c * x))‖ = Real.exp (-(c.re * x)) := by
    intro x
    rw [Complex.norm_exp]
    congr 1
    simp [Complex.neg_re, Complex.mul_re]
  have hint : IntegrableOn (fun x : ℝ => Complex.exp (-(c * x))) (Ioi (0:ℝ)) volume := by
    refine Integrable.mono' (g := fun x : ℝ => Real.exp (-c.re * x))
      (exp_neg_integrableOn_Ioi 0 hc) ?_ ?_
    · apply Measurable.aestronglyMeasurable
      fun_prop
    · filter_upwards with x
      rw [hnorm x]
      apply le_of_eq
      congr 1
      ring
  have hlim : Tendsto (fun t : ℝ => -Complex.exp (-(c * t)) / c) atTop (𝓝 0) := by
    have hnormlim : Tendsto (fun t : ℝ => ‖-Complex.exp (-(c * (t:ℂ))) / c‖) atTop (𝓝 0) := by
      have hval : ∀ t : ℝ, ‖-Complex.exp (-(c * (t:ℂ))) / c‖
          = Real.exp (-(c.re * t)) / ‖c‖ := by
        intro t
        rw [norm_div, norm_neg, hnorm t]
      have hexp : Tendsto (fun t : ℝ => Real.exp (-(c.re * t))) atTop (𝓝 0) := by
        have hlin : Tendsto (fun t : ℝ => -(c.re * t)) atTop atBot := by
          have : Tendsto (fun t : ℝ => c.re * t) atTop atTop :=
            Filter.Tendsto.const_mul_atTop hc tendsto_id
          exact tendsto_neg_atTop_atBot.comp this
        exact Real.tendsto_exp_atBot.comp hlin
      have := hexp.div_const ‖c‖
      rw [zero_div] at this
      exact this.congr fun t => (hval t).symm
    exact tendsto_zero_iff_norm_tendsto_zero.mpr hnormlim
  have hcont : ContinuousWithinAt (fun t : ℝ => -Complex.exp (-(c * (t:ℂ))) / c) (Ici (0:ℝ)) 0 := by
    apply Continuous.continuousWithinAt
    fun_prop
  have h := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint hlim
  rw [h]
  simp [neg_div, one_div]

/-- **The resolvent symbol is the Fourier transform of the two-sided exponential kernel.** -/
theorem fourierIntegral_exp_neg_mul_abs {μ : ℝ} (hμ : 0 < μ) (ξ : ℝ) :
    𝓕 (fun x : ℝ => (Real.exp (-(μ * |x|)) : ℂ)) ξ
      = 2 * (μ:ℂ) / ((μ:ℂ) ^ (2 : ℕ) + 4 * (Real.pi : ℂ) ^ (2 : ℕ) * (ξ:ℂ) ^ (2 : ℕ)) := by
  set g : ℝ → ℂ := fun x => Complex.exp ((((-2 * Real.pi * x * ξ : ℝ)) : ℂ) * Complex.I)
      • (Real.exp (-(μ * |x|)) : ℂ) with hg
  have hnormg : ∀ x : ℝ, ‖g x‖ = Real.exp (-μ * |x|) := by
    intro x
    rw [hg]
    simp only [smul_eq_mul, norm_mul, Complex.norm_exp]
    have hre : ((((-2 * Real.pi * x * ξ : ℝ)) : ℂ) * Complex.I).re = 0 := by
      simp
    rw [hre, Real.exp_zero, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    congr 1
    ring
  have hmeas : AEStronglyMeasurable g volume := by
    apply Measurable.aestronglyMeasurable
    rw [hg]
    fun_prop
  have hintegrable : Integrable g volume := by
    have hbase : Integrable (fun x : ℝ => Real.exp (-μ * |x|)) volume := by
      have h := HTGeometry.integrable_abs_pow_mul_exp_neg_abs 0 hμ
      simpa using h
    exact Integrable.mono' hbase hmeas (Filter.Eventually.of_forall fun x => le_of_eq (hnormg x))
  have hsplit : (∫ x : ℝ, g x) = (∫ x in Iic (0:ℝ), g x) + ∫ x in Ioi (0:ℝ), g x := by
    rw [← MeasureTheory.setIntegral_univ, ← Iic_union_Ioi (a := (0:ℝ))]
    exact setIntegral_union (by simp [Set.disjoint_left]) measurableSet_Ioi
      hintegrable.integrableOn hintegrable.integrableOn
  have hne1 : (μ:ℂ) + 2 * (Real.pi : ℂ) * Complex.I * (ξ:ℂ) ≠ 0 := by
    intro h
    have hre : ((μ:ℂ) + 2 * (Real.pi : ℂ) * Complex.I * (ξ:ℂ)).re = μ := by simp
    rw [h] at hre
    simp at hre
    linarith
  have hne2 : (μ:ℂ) - 2 * (Real.pi : ℂ) * Complex.I * (ξ:ℂ) ≠ 0 := by
    intro h
    have hre : ((μ:ℂ) - 2 * (Real.pi : ℂ) * Complex.I * (ξ:ℂ)).re = μ := by simp
    rw [h] at hre
    simp at hre
    linarith
  have hright : (∫ x in Ioi (0:ℝ), g x)
      = 1 / ((μ:ℂ) + 2 * (Real.pi : ℂ) * Complex.I * (ξ:ℂ)) := by
    rw [← integral_Ioi_cexp_neg (c := (μ:ℂ) + 2 * (Real.pi : ℂ) * Complex.I * (ξ:ℂ)) (by simp [hμ])]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hx0 : (0:ℝ) < x := hx
    rw [hg]
    show Complex.exp ((((-2 * Real.pi * x * ξ : ℝ)) : ℂ) * Complex.I)
        • (Real.exp (-(μ * |x|)) : ℂ)
      = Complex.exp (-(((μ:ℂ) + 2 * (Real.pi : ℂ) * Complex.I * (ξ:ℂ)) * (x:ℂ)))
    rw [abs_of_pos hx0, smul_eq_mul, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hleft : (∫ x in Iic (0:ℝ), g x)
      = 1 / ((μ:ℂ) - 2 * (Real.pi : ℂ) * Complex.I * (ξ:ℂ)) := by
    have hrefl : (∫ x in Ioi (0:ℝ), g (-x)) = ∫ x in Iic (0:ℝ), g x := by
      have h := integral_comp_neg_Ioi (0:ℝ) g
      rwa [neg_zero] at h
    rw [← hrefl,
      ← integral_Ioi_cexp_neg (c := (μ:ℂ) - 2 * (Real.pi : ℂ) * Complex.I * (ξ:ℂ)) (by simp [hμ])]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hx0 : (0:ℝ) < x := hx
    rw [hg]
    show Complex.exp ((((-2 * Real.pi * (-x) * ξ : ℝ)) : ℂ) * Complex.I)
        • (Real.exp (-(μ * |(-x)|)) : ℂ)
      = Complex.exp (-(((μ:ℂ) - 2 * (Real.pi : ℂ) * Complex.I * (ξ:ℂ)) * (x:ℂ)))
    rw [abs_neg, abs_of_pos hx0, smul_eq_mul, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hprod : ((μ:ℂ) - 2 * (Real.pi : ℂ) * Complex.I * (ξ:ℂ))
      * ((μ:ℂ) + 2 * (Real.pi : ℂ) * Complex.I * (ξ:ℂ))
      = (μ:ℂ) ^ (2 : ℕ) + 4 * (Real.pi : ℂ) ^ (2 : ℕ) * (ξ:ℂ) ^ (2 : ℕ) := by
    linear_combination (-4 * (Real.pi : ℂ) ^ (2 : ℕ) * (ξ:ℂ) ^ (2 : ℕ)) * Complex.I_sq
  rw [Real.fourier_real_eq_integral_exp_smul]
  have hcongr : (∫ v : ℝ, Complex.exp ((((-2 * Real.pi * v * ξ : ℝ)) : ℂ) * Complex.I)
      • (Real.exp (-(μ * |v|)) : ℂ)) = ∫ x : ℝ, g x := rfl
  rw [hcongr, hsplit, hleft, hright, div_add_div _ _ hne2 hne1, hprod]
  congr 1
  ring

end

end GaloisForLFunctions.HTGeometry
