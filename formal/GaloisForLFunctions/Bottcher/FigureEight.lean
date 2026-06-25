/-
# Böttcher tower — the disconnected-basin figure-eight / component structure (L4)

The disconnected case turns on a fact that the connected case lacks: for `c ∉ M` the escaping critical
point `0` is a *critical point of the Green's function* `G_c`, sitting at a positive level `G_c(0) > 0`.
That critical point is the saddle whose level set `{G_c = G_c(0)}` is a figure-eight; below it the
sub-level basin splits into the two Cantor lobes that the dyadic monodromy winds around. This file builds
that structure from the harmonic `G_c` (`harmonicOnNhd_greenLimit_basin`) and the basin scaling law
`G_c(f_c z) = 2·G_c(z)`, upward toward the winding loop around a single component (the `2πi/2ⁿ` period
of `φ_{c₁}`) that, paired with `pathInt_dlog_lift_closed_eq_zero` (the loop fixes `φ_{c₂}`), assembles
the monodromy automorphism `σ_n` discharging `hDisc`.
-/
import GaloisForLFunctions.Bottcher.BasinBranching
import GaloisForLFunctions.Bottcher.Winding

open Complex

namespace Bottcher

/-- **[L4a — the branch point] The escaping critical point `0` is a critical point of `G_c`.**
For disconnected `c` (`0 ∉ K_c`), the Green's function has vanishing gradient at the critical point:
`fderiv ℝ (G_c) 0 = 0`. Reason: `G_c(z) = ½·G_c(f_c z)` near `0` (the basin scaling law), and
`f_c'(0) = 2·0 = 0`, so the chain rule kills the derivative — `fderiv G_c 0 = ½·(fderiv G_c c)∘(f_c'(0))
= 0`. This is the saddle of the harmonic `G_c`: the level set `{G_c = G_c(0)}` passes through `0` as a
figure-eight, and it is exactly *because* `0` escapes (`c ∉ M`) that this critical point sits at a
positive level `G_c(0) > 0`, splitting the sub-level basin into the two Cantor lobes the dyadic
monodromy winds around. The seed of the whole disconnected component structure. Axiom-clean. -/
theorem fderiv_greenLimit_critical {c : ℂ} (hc : Disconnected c) :
    fderiv ℝ (greenLimit c) 0 = 0 := by
  have h0 : (0 : ℂ) ∉ filledJulia c := (disconnected_iff_zero_not_mem c).mp hc
  have hc0 : quadratic c 0 ∉ filledJulia c := by
    simpa using not_mem_filledJulia_iterate h0 1
  have hdiffc : DifferentiableAt ℝ (greenLimit c) (quadratic c 0) :=
    (harmonicOnNhd_greenLimit_basin c (quadratic c 0) hc0).1.differentiableAt (by norm_num)
  have hfd : HasFDerivAt (quadratic c) (0 : ℂ →L[ℝ] ℂ) 0 := by
    have hd : HasDerivAt (quadratic c) 0 0 := by
      simpa using (hasStrictDerivAt_quadratic c 0).hasDerivAt
    have h2 := hd.hasFDerivAt.restrictScalars ℝ
    convert h2 using 1
    ext z; simp
  have hcomp : HasFDerivAt (greenLimit c ∘ quadratic c) (0 : ℂ →L[ℝ] ℝ) 0 := by
    have := hdiffc.hasFDerivAt.comp 0 hfd
    rwa [ContinuousLinearMap.comp_zero] at this
  have heq : greenLimit c =ᶠ[nhds (0:ℂ)] (fun z => (2:ℝ)⁻¹ * greenLimit c (quadratic c z)) := by
    filter_upwards [(isClosed_filledJulia c).isOpen_compl.mem_nhds h0] with w hw
    show greenLimit c w = (2:ℝ)⁻¹ * greenLimit c (quadratic c w)
    rw [greenLimit_quadratic_basin hw]; ring
  rw [heq.fderiv_eq]
  have hfinal : HasFDerivAt (fun z => (2:ℝ)⁻¹ * greenLimit c (quadratic c z))
      ((2:ℝ)⁻¹ • (0 : ℂ →L[ℝ] ℝ)) 0 := hcomp.const_mul (2:ℝ)⁻¹
  rw [hfinal.fderiv, smul_zero]

end Bottcher

namespace Bottcher
open Complex

/-- **[Winding value] A depth-`n` lifted loop carries the dyadic period `2πi/2ⁿ`.** If `γ` is a loop in
the escape set whose `n`-fold image `f_c^[n] ∘ γ` traces a contour of total `d log φ_c`-period `2πi`
(the base period, `circleIntegral_dlog_bottcher`), then `γ` itself has period `2πi/2ⁿ`. This is the
exact order-`2ⁿ` monodromy multiplier exponent: continuing `φ_{c₁}` around `γ` multiplies it by
`exp(2πi/2ⁿ) = ζ_{2ⁿ}`. Pure consequence of the `n`-fold period scaling `pathInt_iterate_comp`
(`∮_{f^[n]∘γ} = 2ⁿ ∮_γ`). Together with `pathInt_dlog_lift_closed_eq_zero` (the same loop fixes
`φ_{c₂}`), this is the full monodromy datum `σ_n F = ζF, σ_n G = G` — and the algebraic shadow of
"`φ_{c₁}∘f^[n]` is not a square in `meroField`", the Kummer-irreducibility input. Axiom-clean. -/
theorem winding_value_of_iterate_loop {c : ℂ} (n : ℕ) {γ γ' : ℝ → ℂ}
    (hmem : ∀ θ ∈ Set.uIcc (0:ℝ) (2 * Real.pi), γ θ ∈ escapeOpen c)
    (hbase : (∫ θ in (0:ℝ)..(2 * Real.pi),
        logDeriv (bottcherCoord c) ((quadratic c)^[n] (γ θ))
          * (2 ^ n * (∏ k ∈ Finset.range n, (quadratic c)^[k] (γ θ)) * γ' θ))
      = 2 * Real.pi * Complex.I) :
    (∫ θ in (0:ℝ)..(2 * Real.pi), logDeriv (bottcherCoord c) (γ θ) * γ' θ)
      = 2 * Real.pi * Complex.I / 2 ^ n := by
  have h := pathInt_iterate_comp (γ' := γ') n hmem
  rw [hbase] at h
  rw [eq_div_iff (show (2:ℂ) ^ n ≠ 0 from pow_ne_zero n two_ne_zero)]
  linear_combination -h

end Bottcher

namespace Bottcher
open Complex InnerProductSpace

/-- **[L4c — the holomorphic saddle model] Near the critical point `0`, `G_c` is the real part of a
holomorphic `F` with `F'(0) = 0`.** For disconnected `c`, `G_c` is harmonic on a ball about `0`
(`harmonicOnNhd_greenLimit_basin`), so it has a holomorphic completion `F` (`Re F = G_c`) on that ball
(Mathlib's harmonic-conjugate `exists_analyticOnNhd_ball_re_eq`). Since `0` is a critical point of `G_c`
(`fderiv_greenLimit_critical`), the Cauchy–Riemann derivative vanishes: `deriv F 0 = 0`. Thus `F(z) -
F(0) = ½F''(0)z² + O(z³)` — the standard non-degenerate saddle whose level set `{Re F = Re F(0)} =
{G_c = G_c(0)}` is the figure-eight, and below which the basin splits into the two Cantor lobes. This is
the local analytic model the disconnected component structure is read off from. Axiom-clean. -/
theorem exists_holomorphic_completion_critical {c : ℂ} (hc : Disconnected c) :
    ∃ (R : ℝ) (F : ℂ → ℂ), 0 < R ∧ AnalyticOnNhd ℂ F (Metric.ball 0 R) ∧
      Set.EqOn (fun z => (F z).re) (greenLimit c) (Metric.ball 0 R) ∧ deriv F 0 = 0 := by
  have h0 : (0 : ℂ) ∉ filledJulia c := (disconnected_iff_zero_not_mem c).mp hc
  obtain ⟨R, hRpos, hsub⟩ :=
    Metric.mem_nhds_iff.mp ((isClosed_filledJulia c).isOpen_compl.mem_nhds h0)
  have hharm : HarmonicOnNhd (greenLimit c) (Metric.ball 0 R) :=
    fun x hx => harmonicOnNhd_greenLimit_basin c x (hsub hx)
  obtain ⟨F, hFan, hFre⟩ := hharm.exists_analyticOnNhd_ball_re_eq
  refine ⟨R, F, hRpos, hFan, hFre, ?_⟩
  have hball0 : (0 : ℂ) ∈ Metric.ball 0 R := Metric.mem_ball_self hRpos
  have hFda : DifferentiableAt ℂ F 0 := (hFan 0 hball0).differentiableAt
  have hReF_eq : (fun z => (F z).re) =ᶠ[nhds (0:ℂ)] greenLimit c := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hball0] with w hw using hFre hw
  have hfd_eq : fderiv ℝ (fun z => (F z).re) 0 = 0 := by
    rw [hReF_eq.fderiv_eq]; exact fderiv_greenLimit_critical hc
  have hcomp : HasFDerivAt (fun z => (F z).re)
      (Complex.reCLM.comp ((fderiv ℂ F 0).restrictScalars ℝ)) 0 :=
    Complex.reCLM.hasFDerivAt.comp 0 (hFda.hasFDerivAt.restrictScalars ℝ)
  have hCLM : Complex.reCLM.comp ((fderiv ℂ F 0).restrictScalars ℝ) = 0 :=
    hcomp.fderiv.symm.trans hfd_eq
  have hd1 : (deriv F 0).re = 0 := by
    have h := congrArg (fun L => L (1:ℂ)) hCLM
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply,
      Complex.reCLM_apply] at h
    rw [← fderiv_apply_one_eq_deriv]
    exact h
  have hdI : (deriv F 0).im = 0 := by
    have h := congrArg (fun L => L Complex.I) hCLM
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply,
      Complex.reCLM_apply] at h
    have h1 : (fderiv ℂ F 0) Complex.I = Complex.I • (fderiv ℂ F 0) 1 := by
      rw [← ContinuousLinearMap.map_smul, smul_eq_mul, mul_one]
    have hI : (fderiv ℂ F 0) Complex.I = Complex.I * deriv F 0 := by
      rw [h1, fderiv_apply_one_eq_deriv, smul_eq_mul]
    rw [show (((fderiv ℂ F 0).restrictScalars ℝ) Complex.I) = (fderiv ℂ F 0) Complex.I from rfl,
      hI, Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub,
      neg_eq_zero] at h
    exact h
  exact Complex.ext hd1 hdI

end Bottcher
