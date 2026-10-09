import GaloisForLFunctions.RHTower.RiemannKernelComplexStrip
import GaloisForLFunctions.RHTower.StripHorizontalShift
import GaloisForLFunctions.RHTower.FourierPlancherelIntegral

/-!
# Plancherel for Riemann's kernel shifted into the strip

Let `0 ≤ c < π/4`.  Let `m` be holomorphic at every point of the closed strip `0 ≤ Im z ≤ c` and
bounded there, e.g. `m(z) = 1/((1 − iz/a₁)(1 − iz/a₂))` with real `a_j` whose poles `−ia_j` lie
outside the strip.  Put

  `ψ(x) = ∫ Φ(u) m(u) e^{ixu} du`,   `G(u) = Φ(u + ic) m(u + ic)`.

The integrand `Φ(z)m(z)e^{ixz}` is holomorphic on the strip and decays like `e^{−2|Re z|}` there
(`exists_norm_kernelC_le`).  Shifting the line of integration to `Im z = c` gives

* (a) `e^{cx}ψ(x) = ∫ G(u) e^{ixu} du = Ĝ(x)` (`exp_mul_kernelPsi_eq`);
* (b) `∫|e^{cx}ψ(x)|² dx = 2π ∫|G(u)|² du` (`integral_norm_sq_exp_mul_kernelPsi`);
* (c) `x ↦ e^{cx}ψ(x)` has derivative `(iuG)^(x)` (`hasDerivAt_exp_mul_kernelPsi`), and
  `∫|(e^{cx}ψ)′|² dx = 2π ∫ u²|G(u)|² du` (`integral_norm_sq_deriv_exp_mul_kernelPsi`).

Convention: `ĥ(x) = ∫ h(u) e^{ixu} du` (`Zeta23.paperFT`), for which Plancherel reads
`∫|ĥ|² = 2π∫|h|²` (`integral_norm_sq_paperFT_of_memLp`).
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real FourierTransform
open Zeta23

namespace RHTower.KernelStrip

noncomputable section

/-! ## Plancherel and differentiation for the paper transform -/

/-- **Plancherel** for integrable square-integrable `h`: `∫|ĥ(x)|² dx = 2π ∫|h|²`. -/
theorem integral_norm_sq_paperFT_of_memLp {h : ℝ → ℂ} (h1 : Integrable h) (h2 : MemLp h 2) :
    ∫ x : ℝ, ‖paperFT h x‖ ^ 2 = 2 * π * ∫ u : ℝ, ‖h u‖ ^ 2 := by
  have hP := GaloisForLFunctions.RHTower.integral_norm_sq_fourier_eq h1 h2
  have hdict : (fun x : ℝ => ‖paperFT h x‖ ^ 2) =
      fun x : ℝ => (fun ξ : ℝ => ‖𝓕 h ξ‖ ^ 2) (x / (-(2 * π))) := by
    funext x
    rw [paperFT_ofReal_eq_fourier, neg_div, ← div_neg]
  rw [hdict, Measure.integral_comp_div (fun ξ : ℝ => ‖𝓕 h ξ‖ ^ 2) (-(2 * π)), hP,
    abs_neg, abs_of_pos (by positivity), smul_eq_mul]

/-- **Differentiation** of the paper transform: `d/dx ĥ(x) = (iuh)^(x)`. -/
theorem hasDerivAt_paperFT {h : ℝ → ℂ} (h1 : Integrable h)
    (h2 : Integrable (fun u : ℝ => (u : ℂ) * h u)) (x : ℝ) :
    HasDerivAt (fun x : ℝ => paperFT h x) (paperFT (fun u => I * u * h u) x) x := by
  have h2' : Integrable (fun u : ℝ => u • h u) :=
    h2.congr (Eventually.of_forall fun u => by simp [Complex.real_smul])
  set w : ℝ → ℝ := fun x => -x / (2 * π) with hw
  have hd := Real.hasDerivAt_fourier h1 h2' (w x)
  have hwd : HasDerivAt w (-1 / (2 * π)) x := by
    have := (hasDerivAt_id x).neg.div_const (2 * π)
    simpa [hw, neg_div] using this
  have hc := hd.scomp x hwd
  have hfun : (fun x : ℝ => paperFT h x) = (𝓕 h) ∘ w := by
    funext x; simp only [Function.comp_apply, hw, paperFT_ofReal_eq_fourier]
  rw [hfun]
  refine hc.congr_deriv ?_
  rw [paperFT_ofReal_eq_fourier, Real.fourier_real_eq_integral_exp_smul,
    Real.fourier_real_eq_integral_exp_smul, ← integral_smul]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [hw, smul_eq_mul, Complex.real_smul]
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp

/-! ## The shifted profile -/

/-- `ψ(x) = ∫ Φ(u) m(u) e^{ixu} du`. -/
def kernelPsi (m : ℂ → ℂ) (x : ℝ) : ℂ :=
  ∫ u : ℝ, riemannPhiKernel u * m u * cexp (I * x * u)

/-- `G(u) = Φ(u + ic) m(u + ic)`. -/
def shiftedProfile (m : ℂ → ℂ) (c : ℝ) (u : ℝ) : ℂ :=
  kernelC ((u : ℂ) + (c : ℂ) * I) * m ((u : ℂ) + (c : ℂ) * I)

variable {m : ℂ → ℂ} {c M : ℝ}

theorem continuous_shiftedProfile (hc0 : 0 ≤ c) (hc : c < π / 4)
    (hm : ∀ z : ℂ, 0 ≤ z.im → z.im ≤ c → DifferentiableAt ℂ m z) :
    Continuous (shiftedProfile m c) := by
  refine continuous_iff_continuousAt.mpr fun u => ?_
  have hz : ((u : ℂ) + (c : ℂ) * I).im = c := by simp
  have hl : Continuous fun u : ℝ => (u : ℂ) + (c : ℂ) * I := by fun_prop
  have hk : ContinuousAt kernelC ((u : ℂ) + (c : ℂ) * I) :=
    (differentiableAt_kernelC (by rw [hz, abs_of_nonneg hc0]; exact hc)).continuousAt
  have hmc : ContinuousAt m ((u : ℂ) + (c : ℂ) * I) :=
    (hm _ (by rw [hz]; exact hc0) (by rw [hz])).continuousAt
  exact (hk.comp (f := fun u : ℝ => (u : ℂ) + (c : ℂ) * I) hl.continuousAt).mul
    (hmc.comp (f := fun u : ℝ => (u : ℂ) + (c : ℂ) * I) hl.continuousAt)

/-- `|G(u)| ≤ C e^{−2|u|}`. -/
theorem exists_norm_shiftedProfile_le (hc0 : 0 ≤ c) (hc : c < π / 4)
    (hmb : ∀ z : ℂ, 0 ≤ z.im → z.im ≤ c → ‖m z‖ ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, ‖shiftedProfile m c u‖ ≤ C * Real.exp (-(2 * |u|)) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_kernelC_le hc 2
  have hM : 0 ≤ M := (norm_nonneg _).trans (hmb 0 (by simp) (by simpa using hc0))
  refine ⟨C * M, mul_nonneg hC0 hM, fun u => ?_⟩
  have hz : ((u : ℂ) + (c : ℂ) * I).im = c := by simp
  have hre : ((u : ℂ) + (c : ℂ) * I).re = u := by simp
  have h1 := hC ((u : ℂ) + (c : ℂ) * I) (by rw [hz, abs_of_nonneg hc0])
  have h2 := hmb ((u : ℂ) + (c : ℂ) * I) (by rw [hz]; exact hc0) (by rw [hz])
  rw [hre] at h1
  rw [shiftedProfile, norm_mul]
  calc ‖kernelC ((u : ℂ) + (c : ℂ) * I)‖ * ‖m ((u : ℂ) + (c : ℂ) * I)‖
      ≤ C * Real.exp (-(2 * |u|)) * M := mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ = C * M * Real.exp (-(2 * |u|)) := by ring

theorem one_add_sq_le_exp_two_mul_abs (u : ℝ) : 1 + u ^ 2 ≤ Real.exp (2 * |u|) := by
  have h1 := Real.add_one_le_exp (2 * |u|)
  have h2 := Real.pow_div_factorial_le_exp (2 * |u|) (by positivity) 2
  norm_num at h2
  have hu := abs_nonneg u
  have hsq : u ^ 2 = |u| ^ 2 := (sq_abs u).symm
  rcases le_or_gt |u| 1 with h | h
  · nlinarith
  · nlinarith

theorem abs_le_exp_abs (u : ℝ) : |u| ≤ Real.exp |u| := by
  linarith [Real.add_one_le_exp |u|]

/-- Integrability package for `G`: `G`, `uG` are integrable and square integrable. -/
theorem shiftedProfile_integrability (hc0 : 0 ≤ c) (hc : c < π / 4)
    (hm : ∀ z : ℂ, 0 ≤ z.im → z.im ≤ c → DifferentiableAt ℂ m z)
    (hmb : ∀ z : ℂ, 0 ≤ z.im → z.im ≤ c → ‖m z‖ ≤ M) :
    Integrable (shiftedProfile m c) ∧ MemLp (shiftedProfile m c) 2 ∧
      Integrable (fun u : ℝ => I * u * shiftedProfile m c u) ∧
      MemLp (fun u : ℝ => I * u * shiftedProfile m c u) 2 := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_shiftedProfile_le hc0 hc hmb
  have hG := continuous_shiftedProfile hc0 hc hm
  have hH : Continuous fun u : ℝ => I * u * shiftedProfile m c u := by fun_prop
  have hb1 : ∀ u : ℝ, ‖I * u * shiftedProfile m c u‖ ≤ C * Real.exp (-(1 * |u|)) := by
    intro u
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    have h := hC u
    have he : |u| * Real.exp (-(2 * |u|)) ≤ Real.exp (-(1 * |u|)) := by
      have h1 := abs_le_exp_abs u
      calc |u| * Real.exp (-(2 * |u|)) ≤ Real.exp |u| * Real.exp (-(2 * |u|)) :=
            mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
        _ = Real.exp (-(1 * |u|)) := by rw [← Real.exp_add]; ring_nf
    calc |u| * ‖shiftedProfile m c u‖ ≤ |u| * (C * Real.exp (-(2 * |u|))) :=
          mul_le_mul_of_nonneg_left h (abs_nonneg _)
      _ = C * (|u| * Real.exp (-(2 * |u|))) := by ring
      _ ≤ C * Real.exp (-(1 * |u|)) := mul_le_mul_of_nonneg_left he hC0
  have hb0 : ∀ u : ℝ, ‖shiftedProfile m c u‖ ≤ C * Real.exp (-(1 * |u|)) := by
    intro u
    refine (hC u).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC0)
    nlinarith [abs_nonneg u]
  have hint1 := (RHTower.integrable_exp_neg_mul_abs' (c := 1) one_pos).const_mul C
  have hint2 := (RHTower.integrable_exp_neg_mul_abs' (c := 2) two_pos).const_mul (C ^ 2)
  have hsq : ∀ (F : ℝ → ℂ), (∀ u, ‖F u‖ ≤ C * Real.exp (-(1 * |u|))) → Continuous F →
      MemLp F 2 := by
    intro F hF hFc
    refine (memLp_two_iff_integrable_sq_norm hFc.aestronglyMeasurable).mpr ?_
    refine hint2.mono' (hFc.norm.pow 2).aestronglyMeasurable (Eventually.of_forall fun u => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h := pow_le_pow_left₀ (norm_nonneg _) (hF u) 2
    calc ‖F u‖ ^ 2 ≤ (C * Real.exp (-(1 * |u|))) ^ 2 := h
      _ = C ^ 2 * Real.exp (-(2 * |u|)) := by
        rw [mul_pow, ← Real.exp_nat_mul]; ring_nf
  refine ⟨hint1.mono' hG.aestronglyMeasurable (Eventually.of_forall hb0), hsq _ hb0 hG,
    hint1.mono' hH.aestronglyMeasurable (Eventually.of_forall hb1), hsq _ hb1 hH⟩

/-! ## (a) The contour shift -/

/-- **(a)** `e^{cx}ψ(x) = ∫ G(u)e^{ixu} du`. -/
theorem exp_mul_kernelPsi_eq (hc0 : 0 ≤ c) (hc : c < π / 4)
    (hm : ∀ z : ℂ, 0 ≤ z.im → z.im ≤ c → DifferentiableAt ℂ m z)
    (hmb : ∀ z : ℂ, 0 ≤ z.im → z.im ≤ c → ‖m z‖ ≤ M) (x : ℝ) :
    (Real.exp (c * x) : ℂ) * kernelPsi m x = paperFT (shiftedProfile m c) x := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_kernelC_le hc 2
  have hM : 0 ≤ M := (norm_nonneg _).trans (hmb 0 (by simp) (by simpa using hc0))
  set F : ℂ → ℂ := fun z => kernelC z * m z * cexp (I * x * z) with hF
  have hFd : ∀ z : ℂ, 0 ≤ z.im → z.im ≤ c → DifferentiableAt ℂ F z := by
    intro z h0 h1
    have hk := differentiableAt_kernelC (z := z) (by rw [abs_of_nonneg h0]; linarith)
    have hmz := hm z h0 h1
    simp only [hF]
    fun_prop
  have hFb : ∀ z : ℂ, 0 ≤ z.im → z.im ≤ c →
      ‖F z‖ ≤ C * M * Real.exp (|x| * c) * (1 + z.re ^ 2)⁻¹ := by
    intro z h0 h1
    have hk := hC z (by rw [abs_of_nonneg h0]; exact h1)
    have hmz := hmb z h0 h1
    have he : ‖cexp (I * x * z)‖ ≤ Real.exp (|x| * c) := by
      rw [Complex.norm_exp]
      apply Real.exp_le_exp.mpr
      have : (I * (x : ℂ) * z).re = -(x * z.im) := by simp [Complex.mul_re]
      rw [this]
      have ha := mul_nonneg (by linarith [neg_abs_le x] : (0 : ℝ) ≤ |x| + x) h0
      have hb := mul_le_mul_of_nonneg_left h1 (abs_nonneg x)
      nlinarith
    have hdecay : Real.exp (-(2 * |z.re|)) ≤ (1 + z.re ^ 2)⁻¹ := by
      rw [Real.exp_neg]
      exact inv_anti₀ (by positivity) (one_add_sq_le_exp_two_mul_abs z.re)
    simp only [hF]
    rw [norm_mul, norm_mul]
    calc ‖kernelC z‖ * ‖m z‖ * ‖cexp (I * x * z)‖
        ≤ (C * Real.exp (-(2 * |z.re|))) * M * Real.exp (|x| * c) := by gcongr
      _ ≤ (C * (1 + z.re ^ 2)⁻¹) * M * Real.exp (|x| * c) := by gcongr
      _ = C * M * Real.exp (|x| * c) * (1 + z.re ^ 2)⁻¹ := by ring
  have hshift := RHTower.integral_horizontal_shift_of_upper_inv_one_add_sq_decay hc0 hFd hFb
  have hL : ∫ t : ℝ, F ((t : ℂ) + (c : ℂ) * I) =
      cexp (-((c : ℂ) * x)) * paperFT (shiftedProfile m c) x := by
    unfold paperFT
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [hF, shiftedProfile]
    rw [show I * (x : ℂ) * ((t : ℂ) + (c : ℂ) * I) = I * x * t + (-((c : ℂ) * x)) by
      ring_nf; rw [Complex.I_sq]; ring, Complex.exp_add]
    ring
  have hR : ∫ t : ℝ, F (t : ℂ) = kernelPsi m x := by
    unfold kernelPsi
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [hF, kernelC_ofReal]
  rw [hL, hR] at hshift
  rw [← hshift, ← mul_assoc, Complex.ofReal_exp, ← Complex.exp_add]
  have h0 : ((c * x : ℝ) : ℂ) + -((c : ℂ) * x) = 0 := by push_cast; ring
  rw [h0, Complex.exp_zero, one_mul]

/-! ## (b) Plancherel -/

/-- **(b)** `∫|e^{cx}ψ(x)|² dx = 2π ∫|G(u)|² du`. -/
theorem integral_norm_sq_exp_mul_kernelPsi (hc0 : 0 ≤ c) (hc : c < π / 4)
    (hm : ∀ z : ℂ, 0 ≤ z.im → z.im ≤ c → DifferentiableAt ℂ m z)
    (hmb : ∀ z : ℂ, 0 ≤ z.im → z.im ≤ c → ‖m z‖ ≤ M) :
    ∫ x : ℝ, ‖(Real.exp (c * x) : ℂ) * kernelPsi m x‖ ^ 2 =
      2 * π * ∫ u : ℝ, ‖shiftedProfile m c u‖ ^ 2 := by
  obtain ⟨h1, h2, -, -⟩ := shiftedProfile_integrability hc0 hc hm hmb
  simp_rw [exp_mul_kernelPsi_eq hc0 hc hm hmb]
  exact integral_norm_sq_paperFT_of_memLp h1 h2

/-! ## (c) The derivative -/

/-- **(c)** `x ↦ e^{cx}ψ(x)` is differentiable with derivative `(iuG)^(x)`. -/
theorem hasDerivAt_exp_mul_kernelPsi (hc0 : 0 ≤ c) (hc : c < π / 4)
    (hm : ∀ z : ℂ, 0 ≤ z.im → z.im ≤ c → DifferentiableAt ℂ m z)
    (hmb : ∀ z : ℂ, 0 ≤ z.im → z.im ≤ c → ‖m z‖ ≤ M) (x : ℝ) :
    HasDerivAt (fun x : ℝ => (Real.exp (c * x) : ℂ) * kernelPsi m x)
      (paperFT (fun u : ℝ => I * u * shiftedProfile m c u) x) x := by
  obtain ⟨h1, -, h3, -⟩ := shiftedProfile_integrability hc0 hc hm hmb
  have h3' : Integrable (fun u : ℝ => (u : ℂ) * shiftedProfile m c u) := by
    have := h3.const_mul (-I)
    refine this.congr (Eventually.of_forall fun u => ?_)
    simp only
    ring_nf
    rw [Complex.I_sq]
    ring
  have hfun : (fun x : ℝ => (Real.exp (c * x) : ℂ) * kernelPsi m x) =
      fun x : ℝ => paperFT (shiftedProfile m c) x :=
    funext fun x => exp_mul_kernelPsi_eq hc0 hc hm hmb x
  rw [hfun]
  exact hasDerivAt_paperFT h1 h3' x

/-- **(c)** `∫|(e^{cx}ψ)′(x)|² dx = 2π ∫ u²|G(u)|² du`. -/
theorem integral_norm_sq_deriv_exp_mul_kernelPsi (hc0 : 0 ≤ c) (hc : c < π / 4)
    (hm : ∀ z : ℂ, 0 ≤ z.im → z.im ≤ c → DifferentiableAt ℂ m z)
    (hmb : ∀ z : ℂ, 0 ≤ z.im → z.im ≤ c → ‖m z‖ ≤ M) :
    ∫ x : ℝ, ‖deriv (fun x : ℝ => (Real.exp (c * x) : ℂ) * kernelPsi m x) x‖ ^ 2 =
      2 * π * ∫ u : ℝ, u ^ 2 * ‖shiftedProfile m c u‖ ^ 2 := by
  obtain ⟨-, -, h3, h4⟩ := shiftedProfile_integrability hc0 hc hm hmb
  simp_rw [fun x => (hasDerivAt_exp_mul_kernelPsi hc0 hc hm hmb x).deriv]
  rw [integral_norm_sq_paperFT_of_memLp h3 h4]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only
  rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow,
    sq_abs]

end

end RHTower.KernelStrip
