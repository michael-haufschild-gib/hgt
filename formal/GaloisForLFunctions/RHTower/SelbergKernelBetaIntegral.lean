import GaloisForLFunctions.RHTower.SelbergKernelBessel

open Complex MeasureTheory Filter Topology
open scoped FourierTransform

/-!
# The zero Fourier mode of the Eisenstein kernel: a Beta integral

The Gamma–Bessel transform at frequency `0` gives `∫_ℝ (1+t²)^{-s} dt = √π Γ(s-1/2)/Γ(s)` for `Re s > 1`
(`integral_ker01_of_one_lt`); both sides are holomorphic on `Re s > 1/2` (`differentiableAt_cBeta`), so the identity
holds there (`integral_ker01`). The right side `C(s) = cBeta s` is meromorphic on `ℂ` with poles only at
`s = 1/2 - m`: it continues the archimedean factor of the scattering entries `φ_{∞,σ∞} = D_σ · C` past `Re s = 1/2`.
-/

namespace GaloisForLFunctions.RHTower.SelbergKernelBetaIntegral
open GaloisForLFunctions.RHTower.SelbergPoincareKernel GaloisForLFunctions.RHTower.SelbergEisensteinCuspSlice
  GaloisForLFunctions.RHTower.SelbergPoincareContinuation GaloisForLFunctions.RHTower.SelbergKernelBessel
  GaloisForLFunctions.RHTower.SelbergEisensteinScatteringEntry

/-- `C(s) = √π Γ(s - 1/2)/Γ(s)`. -/
noncomputable def cBeta (s : ℂ) : ℂ := (Real.sqrt Real.pi : ℂ) * Complex.Gamma (s - 1 / 2) * (Complex.Gamma s)⁻¹

theorem integral_ker01_of_one_lt {s : ℂ} (hs : 1 < s.re) : ∫ t, ker 0 1 s t = cBeta s := by
  have hk : ker 0 1 s = fun x => ((1 : ℝ) : ℂ) ^ s *
      RHTower.d4BMCauchyPowerKernel ⟨0, 1, one_pos⟩ s x := by
    funext x; rw [ker0_eq_cauchy one_pos]; rfl
  have h0 : ∫ t, ker 0 1 s t = 𝓕 (ker 0 1 s) 0 := by simp [Real.fourier_eq]
  rw [h0, hk, fourier_const_mul]
  have h := RHTower.fourier_d4BMCauchyPowerKernel_zero ⟨0, 1, one_pos⟩ ⟨s, hs⟩
  simp only at h
  rw [h, cBeta]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have e1 : (((Real.pi * 1 ^ 2 : ℝ)) : ℂ) ^ (-(s - 1 / 2)) = (Real.pi : ℂ) ^ (-(s - 1 / 2)) := by norm_num
  have e2 : (Real.sqrt Real.pi : ℂ) = (Real.pi : ℂ) ^ (1 / 2 : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow Real.pi_pos.le]; norm_num
  rw [e1, e2, ofReal_one, one_cpow, one_mul]
  have e3 : (Real.pi : ℂ) ^ s * (Real.pi : ℂ) ^ (-(s - 1 / 2)) = (Real.pi : ℂ) ^ (1 / 2 : ℂ) := by
    rw [← cpow_add _ _ hpi]; ring_nf
  calc (Real.pi : ℂ) ^ s / Complex.Gamma s * (Complex.Gamma (s - 1 / 2) * (Real.pi : ℂ) ^ (-(s - 1 / 2)))
      = ((Real.pi : ℂ) ^ s * (Real.pi : ℂ) ^ (-(s - 1 / 2))) * Complex.Gamma (s - 1 / 2) *
          (Complex.Gamma s)⁻¹ := by ring
    _ = _ := by rw [e3]

theorem differentiableAt_cBeta {s : ℂ} (hs : 1 / 2 < s.re) : DifferentiableAt ℂ cBeta s := by
  unfold cBeta
  refine ((differentiableAt_const _).mul ?_).mul (Complex.differentiable_one_div_Gamma s)
  refine (Complex.differentiableAt_Gamma _ (fun m hm => ?_)).comp s (differentiableAt_id.sub_const _)
  have := congrArg Complex.re hm
  simp at this
  have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  linarith

/-- **The Beta integral** `∫_ℝ (1+t²)^{-s} dt = √π Γ(s - 1/2)/Γ(s)` on `Re s > 1/2`. -/
theorem integral_ker01 {s : ℂ} (hs : 1 / 2 < s.re) : ∫ t, ker 0 1 s t = cBeta s := by
  set U := {s : ℂ | 1 / 2 < s.re}
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hf : AnalyticOnNhd ℂ (fun s => ∫ t, ker 0 1 s t) U :=
    DifferentiableOn.analyticOnNhd (fun s hs => (differentiableAt_integral_ker hs).differentiableWithinAt) hUo
  have hg : AnalyticOnNhd ℂ cBeta U :=
    DifferentiableOn.analyticOnNhd (fun s hs => (differentiableAt_cBeta hs).differentiableWithinAt) hUo
  have h2 : (2 : ℂ) ∈ U := by show (1 : ℝ) / 2 < (2 : ℂ).re; norm_num
  have hev : (fun s => ∫ t, ker 0 1 s t) =ᶠ[𝓝 2] cBeta := by
    have : {s : ℂ | 1 < s.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [this] with s hs'
    exact integral_ker01_of_one_lt hs'
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg (convex_halfSpace_re_gt _).isPreconnected h2 hev hs

end GaloisForLFunctions.RHTower.SelbergKernelBetaIntegral
