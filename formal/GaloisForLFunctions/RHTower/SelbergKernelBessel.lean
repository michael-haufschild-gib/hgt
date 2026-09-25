import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCauchyPowerFourierBessel
import GaloisForLFunctions.RHTower.SelbergEisensteinCuspExpansion

open Complex MeasureTheory Filter Topology
open scoped FourierTransform

/-!
# The Fourier transform of the Eisenstein kernel is a `K`-Bessel function

`ker₀(x) = (y/(x²+y²))^s = y^s (y²+x²)^{-s}` (`ker0_eq_cauchy`), so the Gamma–Bessel transform of the Cauchy power
gives, for `ξ ≠ 0`, `𝓕ker₀(ξ) = y^s · 2π^s/Γ(s) · (|ξ|/y)^{s-1/2} · K_{s-1/2}(2πy|ξ|)` for `Re s > 1`
(`fourier_ker0_eq_bessel_of_one_lt`). The right side (`kerBessel`) is entire in `s` (`1/Γ` is entire and
`K_ν(a)` is entire in the order, `differentiableAt_kerBessel`), and `𝓕ker₀` is holomorphic on `Re s > 1/2`, so the
identity holds on `Re s > 1/2` (`fourier_ker0_eq_bessel`). This is the analytic input for continuing the non-constant
Fourier terms of the `Γ(N)` Eisenstein series to the critical line.
-/

namespace GaloisForLFunctions.RHTower.SelbergKernelBessel
open GaloisForLFunctions.RHTower.SelbergPoincareKernel GaloisForLFunctions.RHTower.SelbergEisensteinCuspSlice
  GaloisForLFunctions.RHTower.SelbergPoincareContinuation GaloisForLFunctions.HTGeometry

theorem fourier_const_mul (f : ℝ → ℂ) (c : ℂ) (ξ : ℝ) : 𝓕 (fun x => c * f x) ξ = c * 𝓕 f ξ := by
  simp only [Real.fourier_eq, Circle.smul_def, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1; funext x; ring

/-- `(y/(x²+y²))^s = y^s (y²+x²)^{-s}`. -/
theorem ker0_eq_cauchy {y : ℝ} (hy : 0 < y) (s : ℂ) (x : ℝ) :
    ker 0 y s x = ((y : ℝ) : ℂ) ^ s * ((y ^ 2 + x ^ 2 : ℝ) : ℂ) ^ (-s) := by
  rw [ker0_eq y hy]
  have hq : 0 < y ^ 2 + x ^ 2 := by positivity
  have e : wt y x = y * (y ^ 2 + x ^ 2)⁻¹ := by unfold wt; field_simp; ring
  rw [e, ofReal_mul, mul_cpow_ofReal_nonneg hy.le (inv_pos.mpr hq).le, ofReal_inv, inv_cpow _ _
    (by rw [Complex.arg_ofReal_of_nonneg hq.le]; exact Real.pi_ne_zero.symm), cpow_neg]

/-- The Bessel form of `𝓕ker₀`: `y^s · 2π^s/Γ(s) · (|ξ|/y)^{s-1/2} · K_{s-1/2}(2πy|ξ|)`. -/
noncomputable def kerBessel (y : ℝ) (s : ℂ) (ξ : ℝ) : ℂ :=
  ((y : ℝ) : ℂ) ^ s * (2 * (Real.pi : ℂ) ^ s * (Complex.Gamma s)⁻¹) * (((|ξ| / y : ℝ)) : ℂ) ^ (s - 1 / 2) *
    modifiedBesselKOrder (2 * Real.pi * y * |ξ|) (s - 1 / 2)

theorem fourier_ker0_eq_bessel_of_one_lt {y : ℝ} (hy : 0 < y) {s : ℂ} (hs : 1 < s.re) {ξ : ℝ} (hξ : ξ ≠ 0) :
    𝓕 (ker 0 y s) ξ = kerBessel y s ξ := by
  have hk : ker 0 y s = fun x => ((y : ℝ) : ℂ) ^ s *
      RHTower.d4BMCauchyPowerKernel ⟨0, y, hy⟩ s x := by
    funext x; rw [ker0_eq_cauchy hy]; rfl
  rw [hk, fourier_const_mul]
  have h := RHTower.fourier_d4BMCauchyPowerKernel_ne_zero ⟨0, y, hy⟩ ⟨s, hs⟩ hξ
  simp only at h
  rw [h, kerBessel, div_eq_mul_inv]
  ring

theorem differentiableAt_kerBessel {y : ℝ} (hy : 0 < y) {ξ : ℝ} (hξ : ξ ≠ 0) (s : ℂ) :
    DifferentiableAt ℂ (fun s => kerBessel y s ξ) s := by
  unfold kerBessel
  have hy0 : ((y : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hq : (((|ξ| / y : ℝ)) : ℂ) ≠ 0 := by
    have : 0 < |ξ| / y := div_pos (abs_pos.mpr hξ) hy
    exact_mod_cast this.ne'
  have ha : 0 < 2 * Real.pi * y * |ξ| := by have := abs_pos.mpr hξ; positivity
  refine (((differentiableAt_id.const_cpow (Or.inl hy0)).mul
    (((differentiableAt_id.const_cpow (Or.inl hpi)).const_mul 2).mul
      (Complex.differentiable_one_div_Gamma s))).mul
    ((differentiableAt_id.sub_const _).const_cpow (Or.inl hq))).mul ?_
  exact ((differentiable_modifiedBesselKOrder ha) _).comp s (differentiableAt_id.sub_const _)

/-- **The Fourier transform of `ker₀` as a Bessel function** on `Re s > 1/2`, `ξ ≠ 0`. -/
theorem fourier_ker0_eq_bessel {y : ℝ} (hy : 0 < y) {s : ℂ} (hs : 1 / 2 < s.re) {ξ : ℝ} (hξ : ξ ≠ 0) :
    𝓕 (ker 0 y s) ξ = kerBessel y s ξ := by
  set U := {s : ℂ | 1 / 2 < s.re}
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hf : AnalyticOnNhd ℂ (fun s => 𝓕 (ker 0 y s) ξ) U :=
    DifferentiableOn.analyticOnNhd (fun s hs =>
      (differentiableAt_fourier_ker le_rfl hy hs ξ).differentiableWithinAt) hUo
  have hg : AnalyticOnNhd ℂ (fun s => kerBessel y s ξ) U :=
    DifferentiableOn.analyticOnNhd (fun s _ => (differentiableAt_kerBessel hy hξ s).differentiableWithinAt) hUo
  have h2 : (2 : ℂ) ∈ U := by show (1 : ℝ) / 2 < (2 : ℂ).re; norm_num
  have hev : (fun s => 𝓕 (ker 0 y s) ξ) =ᶠ[𝓝 2] (fun s => kerBessel y s ξ) := by
    have : {s : ℂ | 1 < s.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [this] with s hs'
    exact fourier_ker0_eq_bessel_of_one_lt hy hs' hξ
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg (convex_halfSpace_re_gt _).isPreconnected h2 hev hs

end GaloisForLFunctions.RHTower.SelbergKernelBessel
