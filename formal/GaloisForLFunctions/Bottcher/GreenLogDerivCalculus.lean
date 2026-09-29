/-
# Calculus of the logarithmic derivative `ω = φ_c'/φ_c = 2∂G_c`

For a real function `G` of a complex variable put `∇G := ∂ₓG − i∂ᵧG = 2∂G`; the global logarithmic
derivative of the Böttcher coordinate is `ω = ∇G_c` (`greenLogDeriv`).

* **Chain rule.**  For holomorphic `h`, `∇(G∘h) = (∇G ∘ h)·h'`.
* `∇(Re ∘ h) = h'` and `∇ log‖·‖ (v) = 1/v`.

Consequences for the Green function of `z² + c`:

* **self-similarity** `ω(f z)·f'(z) = 2ω(z)` on the basin, from `G_c ∘ f = 2G_c`;
* **level sections**: a holomorphic `Σ` with `G_c ∘ Σ = a·log‖·‖` satisfies `ω(Σ v)·Σ'(v) = a/v`;
* on the escape region `ω = φ_c'/φ_c`, since `G_c = log‖φ_c‖` there.
-/
import GaloisForLFunctions.Bottcher.GreenLogDeriv
import GaloisForLFunctions.Bottcher.GreenPullback
import GaloisForLFunctions.Bottcher.BasinColimit

open Complex Set Filter Topology

namespace Bottcher

noncomputable section

/-- The complex gradient `∂ₓG − i∂ᵧG = 2∂G` of a real function of a complex variable. -/
def realGrad (G : ℂ → ℝ) (z : ℂ) : ℂ :=
  (fderiv ℝ G z 1 : ℂ) - Complex.I * (fderiv ℝ G z Complex.I : ℂ)

theorem greenLogDeriv_eq_realGrad (c : ℂ) : greenLogDeriv c = realGrad (greenLimit c) := rfl

theorem realGrad_congr {G₁ G₂ : ℂ → ℝ} {z : ℂ} (h : G₁ =ᶠ[𝓝 z] G₂) :
    realGrad G₁ z = realGrad G₂ z := by
  simp only [realGrad, h.fderiv_eq]

/-- **Chain rule with a holomorphic inner function.** -/
theorem realGrad_comp {G : ℂ → ℝ} {h : ℂ → ℂ} {z : ℂ}
    (hG : DifferentiableAt ℝ G (h z)) (hh : DifferentiableAt ℂ h z) :
    realGrad (G ∘ h) z = realGrad G (h z) * deriv h z := by
  have hfd : HasFDerivAt h
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (deriv h z)).restrictScalars ℝ) z :=
    hh.hasDerivAt.hasFDerivAt.restrictScalars ℝ
  have hcomp := hG.hasFDerivAt.comp z hfd
  set A := fderiv ℝ G (h z) with hA
  set d := deriv h z with hd
  have hdecomp : ∀ u : ℂ, A u = u.re * A 1 + u.im * A Complex.I := by
    intro u
    have hu : u = (u.re : ℝ) • (1 : ℂ) + (u.im : ℝ) • Complex.I := by
      apply Complex.ext <;> simp
    conv_lhs => rw [hu]
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  rw [realGrad, hcomp.fderiv, realGrad, ← hA]
  have happ : ∀ u : ℂ, (A.comp ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) d).restrictScalars ℝ))
      u = A (u * d) := fun u => rfl
  rw [happ, happ, one_mul, hdecomp d, hdecomp (Complex.I * d)]
  have hre : (Complex.I * d).re = -d.im := by simp
  have him : (Complex.I * d).im = d.re := by simp
  rw [hre, him]
  conv_rhs => rw [← Complex.re_add_im d]
  push_cast
  linear_combination (↑(A Complex.I) * ↑d.im) * Complex.I_sq -
    (↑(A 1) * ↑d.im) * Complex.I_sq * 0

theorem realGrad_re : realGrad (fun w : ℂ => w.re) = fun _ => 1 := by
  funext z
  have h : fderiv ℝ (fun w : ℂ => w.re) z = Complex.reCLM := Complex.reCLM.fderiv
  simp [realGrad, h]

/-- The gradient of the real part of a holomorphic function is its derivative. -/
theorem realGrad_re_comp {h : ℂ → ℂ} {z : ℂ} (hh : DifferentiableAt ℂ h z) :
    realGrad (fun w => (h w).re) z = deriv h z := by
  have hre : DifferentiableAt ℝ (fun w : ℂ => w.re) (h z) :=
    Complex.reCLM.differentiableAt
  have := realGrad_comp hre hh
  rw [realGrad_re, one_mul] at this
  exact this

theorem differentiableAt_log_norm {v : ℂ} (hv : v ≠ 0) :
    DifferentiableAt ℝ (fun w : ℂ => Real.log ‖w‖) v :=
  (differentiableAt_id.norm ℝ hv).log (norm_pos_iff.mpr hv).ne'

/-- **`∇ log‖·‖ = 1/v`.** -/
theorem realGrad_log_norm {v : ℂ} (hv : v ≠ 0) :
    realGrad (fun w : ℂ => Real.log ‖w‖) v = v⁻¹ := by
  by_cases hs : v ∈ slitPlane
  · have heq : (fun w : ℂ => Real.log ‖w‖) = fun w => (Complex.log w).re := by
      funext w
      rw [Complex.log_re]
    rw [heq, realGrad_re_comp (Complex.differentiableAt_log hs), (Complex.hasDerivAt_log hs).deriv]
  · have hns : -v ∈ slitPlane := by
      rw [Complex.mem_slitPlane_iff] at hs ⊢
      push Not at hs
      have hre : v.re ≠ 0 := by
        intro h0
        exact hv (Complex.ext (by simpa using h0) (by simpa using hs.2))
      left
      simp only [Complex.neg_re]
      exact neg_pos.mpr (lt_of_le_of_ne hs.1 hre)
    have heq : (fun w : ℂ => Real.log ‖w‖) = fun w => (Complex.log (-w)).re := by
      funext w
      rw [Complex.log_re, norm_neg]
    have h : HasDerivAt (fun w : ℂ => Complex.log (-w)) ((-v)⁻¹ * -1) v :=
      (Complex.hasDerivAt_log hns).comp v (hasDerivAt_neg v)
    have hdiff : DifferentiableAt ℂ (fun w : ℂ => Complex.log (-w)) v := h.differentiableAt
    have hderiv : deriv (fun w : ℂ => Complex.log (-w)) v = v⁻¹ := by
      rw [h.deriv, inv_neg, neg_mul_neg, mul_one]
    rw [heq, realGrad_re_comp hdiff, hderiv]

theorem realGrad_const_mul {G : ℂ → ℝ} {z : ℂ} (a : ℝ) (hG : DifferentiableAt ℝ G z) :
    realGrad (fun w => a * G w) z = a * realGrad G z := by
  have h : fderiv ℝ (fun w => a * G w) z = a • fderiv ℝ G z := fderiv_const_mul hG a
  simp only [realGrad, h]
  simp
  ring

/-! ### The Green function -/

theorem greenFunctionDyn_eventuallyEq_greenLimit {c z : ℂ} (hz : z ∉ filledJulia c) :
    greenFunctionDyn c =ᶠ[𝓝 z] greenLimit c := by
  filter_upwards [(isClosed_filledJulia c).isOpen_compl.mem_nhds hz] with w hw
  unfold greenFunctionDyn
  rw [if_neg hw]

theorem differentiableAt_greenLimit_basin {c z : ℂ} (hz : z ∉ filledJulia c) :
    DifferentiableAt ℝ (greenLimit c) z :=
  (harmonicOnNhd_greenLimit_basin c z hz).1.differentiableAt (by norm_num)

theorem differentiableAt_greenFunctionDyn_basin {c z : ℂ} (hz : z ∉ filledJulia c) :
    DifferentiableAt ℝ (greenFunctionDyn c) z :=
  (differentiableAt_greenLimit_basin hz).congr_of_eventuallyEq
    (greenFunctionDyn_eventuallyEq_greenLimit hz)

theorem greenLogDeriv_eq_realGrad_greenFunctionDyn {c z : ℂ} (hz : z ∉ filledJulia c) :
    greenLogDeriv c z = realGrad (greenFunctionDyn c) z :=
  (realGrad_congr (greenFunctionDyn_eventuallyEq_greenLimit hz)).symm

theorem deriv_quadratic (c z : ℂ) : deriv (quadratic c) z = 2 * z := by
  have h : HasDerivAt (fun w : ℂ => w ^ (2 : ℕ) + c) (2 * z) z := by
    simpa using (hasDerivAt_pow 2 z).add_const c
  exact h.deriv

/-- **Self-similarity of `ω`.**  `ω(f_c z)·f_c'(z) = 2ω(z)` on the basin. -/
theorem greenLogDeriv_quadratic {c z : ℂ} (hz : z ∉ filledJulia c) :
    greenLogDeriv c (quadratic c z) * (2 * z) = 2 * greenLogDeriv c z := by
  have hfz : quadratic c z ∉ filledJulia c := fun h =>
    hz ((quadratic_mem_filledJulia_iff c z).mp h)
  have hdiff : DifferentiableAt ℂ (quadratic c) z := by
    unfold quadratic
    fun_prop
  have hchain := realGrad_comp (differentiableAt_greenFunctionDyn_basin hfz) hdiff
  have hfe : (greenFunctionDyn c ∘ quadratic c) = fun w => 2 * greenFunctionDyn c w := by
    funext w
    exact greenFunctionDyn_quadratic c w
  rw [hfe, realGrad_const_mul 2 (differentiableAt_greenFunctionDyn_basin hz),
    deriv_quadratic] at hchain
  rw [greenLogDeriv_eq_realGrad_greenFunctionDyn hz,
    greenLogDeriv_eq_realGrad_greenFunctionDyn hfz, ← hchain]
  push_cast
  ring

/-- **Level sections.**  A holomorphic map `Σ` with `G_c ∘ Σ = a·log‖·‖` on an open set satisfies
`ω(Σ v)·Σ'(v) = a/v` there. -/
theorem greenLogDeriv_mul_deriv_of_level {c : ℂ} {S : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    {a : ℝ} (hlev : ∀ v ∈ U, greenFunctionDyn c (S v) = a * Real.log ‖v‖)
    {v : ℂ} (hv : v ∈ U) (hv0 : v ≠ 0) (hS : DifferentiableAt ℂ S v)
    (hSv : S v ∉ filledJulia c) :
    greenLogDeriv c (S v) * deriv S v = a / v := by
  have hchain := realGrad_comp (differentiableAt_greenFunctionDyn_basin hSv) hS
  have hev : (greenFunctionDyn c ∘ S) =ᶠ[𝓝 v] fun w => a * Real.log ‖w‖ := by
    filter_upwards [hU.mem_nhds hv] with w hw
    exact hlev w hw
  rw [realGrad_congr hev, realGrad_const_mul a (differentiableAt_log_norm hv0),
    realGrad_log_norm hv0] at hchain
  rw [greenLogDeriv_eq_realGrad_greenFunctionDyn hSv, ← hchain, div_eq_mul_inv]

theorem differentiableAt_bottcherCoord_escape {c z : ℂ} (hz : z ∈ escapeOpen c) :
    DifferentiableAt ℂ (bottcherCoord c) z := by
  obtain ⟨_, hz2⟩ := mem_escapeOpen_regime hz
  have hz0 : z ≠ 0 := fun h => by rw [h, norm_zero] at hz2; linarith
  have hSdiff : DifferentiableAt ℂ (fun w => ∑' k, bottcherLogTerm c w k) z :=
    (differentiableOn_bottcherLogSum c).differentiableAt ((isOpen_escapeOpen c).mem_nhds hz)
  have hee : bottcherCoord c =ᶠ[𝓝 z]
      (fun w => w * Complex.exp (∑' k, bottcherLogTerm c w k)) := by
    filter_upwards [compl_singleton_mem_nhds hz0] with w hw
    exact bottcherCoord_eq_mul_exp (by simpa using hw)
  exact (differentiableAt_id.mul hSdiff.cexp).congr_of_eventuallyEq hee

/-- **On the escape region `ω = φ_c'/φ_c`.** -/
theorem greenLogDeriv_eq_logDeriv_bottcherCoord {c z : ℂ} (hz : z ∈ escapeOpen c) :
    greenLogDeriv c z = logDeriv (bottcherCoord c) z := by
  have hev : greenLimit c =ᶠ[𝓝 z] (fun w => Real.log ‖w‖) ∘ bottcherCoord c := by
    filter_upwards [(isOpen_escapeOpen c).mem_nhds hz] with w hw
    simp only [Function.comp_apply]
    rw [norm_bottcherCoord_eq_exp_green_escape hw, Real.log_exp]
  have hφ0 : bottcherCoord c z ≠ 0 := bottcherCoord_ne_zero c z
  have hchain := realGrad_comp (differentiableAt_log_norm hφ0)
    (differentiableAt_bottcherCoord_escape hz)
  rw [realGrad_log_norm hφ0] at hchain
  rw [greenLogDeriv_eq_realGrad, realGrad_congr hev, hchain, logDeriv_apply, div_eq_inv_mul]

end

end Bottcher
