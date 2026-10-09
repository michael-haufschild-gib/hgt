import GaloisForLFunctions.RHTower.XiRealRootedPolynomialPreimage

/-!
# Polynomially damped Riemann kernels have transforms outside the Laguerre–Pólya class

For real `c_1, …, c_n` put `P(u) = ∏_j (1 − i c_j u)` and damp Riemann's kernel to `Φ(u)/P(u)`.
If some `c_j ≠ 0`, the entire function

  `Ξ_P(z) = ∫ Φ(u) P(u)^{−1} e^{izu} du`

is not Laguerre–Pólya (`not_laguerrePolya_dampedKernelTransform`).  In particular, for every real
`b ≠ 0` the transform of the Lorentzian damping `Φ(u)/(1 + b²u²)` is not Laguerre–Pólya
(`not_laguerrePolya_lorentzDampedKernelTransform`).  So no real-rootedness criterion for kernels
that is stable under such a damping can hold for `Φ`.

**Proof.**  `Φ` decays faster than every exponential (`exists_norm_riemannPhiKernel_le_exp`), so for
multipliers `h` of exponential growth `z ↦ ∫ Φh e^{izu}` is entire with derivative
`∫ iuΦh e^{izu}` (`hasDerivAt_paperFT_kernel`).  Hence `(1 − cD)` multiplies the multiplier by
`1 − icu` (`paperFT_kernel_sub_smul_deriv`), and `∏(1 − c_jD)Ξ_P = Ξ`
(`firstOrderChain_dampedKernelTransform`).  A Laguerre–Pólya `Ξ_P` would be a polynomial
Laguerre–Pólya preimage of `Ξ`, which does not exist
(`not_exists_laguerrePolya_firstOrderChain_preimage_XiC_of_exists_ne`).
-/

open Complex MeasureTheory Filter Topology Set Metric
open Zeta23

namespace RHTower.KernelStrip

noncomputable section

/-- `|Φ(u)| ≤ C e^{−r|u|}` for every `r`. -/
theorem exists_norm_riemannPhiKernel_le_exp (r : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, ‖riemannPhiKernel u‖ ≤ C * Real.exp (-(r * |u|)) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_kernelC_le (c := 0) (by positivity) r
  refine ⟨C, hC0, fun u => ?_⟩
  have h := hC (u : ℂ) (by simp)
  rwa [kernelC_ofReal, Complex.ofReal_re] at h

/-! ## Multipliers of exponential growth -/

/-- Continuous multipliers with `|h(u)| ≤ A e^{κ|u|}`. -/
def ExpGrowth (h : ℝ → ℂ) : Prop :=
  Continuous h ∧ ∃ A κ : ℝ, ∀ u, ‖h u‖ ≤ A * Real.exp (κ * |u|)

theorem ExpGrowth.mul {h g : ℝ → ℂ} (hh : ExpGrowth h) (hg : ExpGrowth g) :
    ExpGrowth fun u => h u * g u := by
  obtain ⟨hc, A, κ, hA⟩ := hh
  obtain ⟨gc, B, μ', hB⟩ := hg
  refine ⟨hc.mul gc, A * B, κ + μ', fun u => ?_⟩
  rw [norm_mul]
  have hA0 : 0 ≤ A * Real.exp (κ * |u|) := (norm_nonneg _).trans (hA u)
  calc ‖h u‖ * ‖g u‖ ≤ (A * Real.exp (κ * |u|)) * (B * Real.exp (μ' * |u|)) :=
        mul_le_mul (hA u) (hB u) (norm_nonneg _) hA0
    _ = A * B * Real.exp ((κ + μ') * |u|) := by
        rw [show (κ + μ') * |u| = κ * |u| + μ' * |u| by ring, Real.exp_add]; ring

theorem expGrowth_one_sub_I_mul (c : ℝ) : ExpGrowth fun u : ℝ => 1 - I * c * u := by
  refine ⟨by fun_prop, 1, |c|, fun u => ?_⟩
  have h1 : ‖(1 : ℂ) - I * c * u‖ ≤ 1 + |c| * |u| := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_one, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
  rw [one_mul]
  exact h1.trans (by linarith [Real.add_one_le_exp (|c| * |u|)])

theorem ExpGrowth.I_mul {h : ℝ → ℂ} (hh : ExpGrowth h) :
    ExpGrowth fun u : ℝ => I * u * h u := by
  have hu : ExpGrowth fun u : ℝ => I * (u : ℂ) := by
    refine ⟨by fun_prop, 1, 1, fun u => ?_⟩
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, one_mul, one_mul]
    linarith [Real.add_one_le_exp |u|]
  exact hu.mul hh

/-! ## The transform and its derivative -/

theorem integrable_kernel_mul_cexp {h : ℝ → ℂ} (hh : ExpGrowth h) (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, |z.im| ≤ R → ∀ u : ℝ,
      ‖riemannPhiKernel u * h u * cexp (I * z * u)‖ ≤ C * Real.exp (-(1 * |u|)) ∧
      ‖I * u * (riemannPhiKernel u * h u) * cexp (I * z * u)‖ ≤ C * Real.exp (-(1 * |u|)) := by
  obtain ⟨-, A, κ, hA⟩ := hh
  have hA0 : 0 ≤ A := by
    have := (norm_nonneg _).trans (hA 0)
    simpa using this
  obtain ⟨C, hC0, hC⟩ := exists_norm_riemannPhiKernel_le_exp (κ + |R| + 2)
  refine ⟨C * A, by positivity, fun z hz u => ?_⟩
  have hu := abs_nonneg u
  have hexp : ‖cexp (I * z * u)‖ ≤ Real.exp (|R| * |u|) := by
    rw [Complex.norm_exp]
    refine Real.exp_le_exp.mpr ?_
    have : (I * z * (u : ℂ)).re = -(z.im * u) := by simp
    rw [this]
    have h1 : -(z.im * u) ≤ |z.im| * |u| := by
      rw [← abs_mul]; exact neg_le_abs _
    have h2 : |z.im| * |u| ≤ |R| * |u| :=
      mul_le_mul_of_nonneg_right (hz.trans (le_abs_self R)) hu
    linarith
  have hΦ := hC u
  have hhu := hA u
  have hprod : ‖riemannPhiKernel u‖ * ‖h u‖ * ‖cexp (I * z * u)‖ ≤
      C * A * Real.exp (-(2 * |u|)) := by
    calc ‖riemannPhiKernel u‖ * ‖h u‖ * ‖cexp (I * z * u)‖
        ≤ (C * Real.exp (-((κ + |R| + 2) * |u|))) * (A * Real.exp (κ * |u|)) *
            Real.exp (|R| * |u|) :=
          mul_le_mul (mul_le_mul hΦ hhu (norm_nonneg _) (by positivity)) hexp (norm_nonneg _)
            (by positivity)
      _ = C * A * Real.exp (-(2 * |u|)) := by
          rw [mul_mul_mul_comm, mul_assoc, ← Real.exp_add, ← Real.exp_add]
          ring_nf
  have hle : Real.exp (-(2 * |u|)) ≤ Real.exp (-(1 * |u|)) :=
    Real.exp_le_exp.mpr (by linarith)
  have hule : |u| * Real.exp (-(2 * |u|)) ≤ Real.exp (-(1 * |u|)) := by
    have h1 : |u| ≤ Real.exp |u| := by linarith [Real.add_one_le_exp |u|]
    calc |u| * Real.exp (-(2 * |u|)) ≤ Real.exp |u| * Real.exp (-(2 * |u|)) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ = Real.exp (-(1 * |u|)) := by rw [← Real.exp_add]; ring_nf
  constructor
  · rw [norm_mul, norm_mul]
    calc _ ≤ C * A * Real.exp (-(2 * |u|)) := hprod
      _ ≤ C * A * Real.exp (-(1 * |u|)) := mul_le_mul_of_nonneg_left hle (by positivity)
  · rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs]
    calc |u| * (‖riemannPhiKernel u‖ * ‖h u‖) * ‖cexp (I * z * u)‖
        = |u| * (‖riemannPhiKernel u‖ * ‖h u‖ * ‖cexp (I * z * u)‖) := by ring
      _ ≤ |u| * (C * A * Real.exp (-(2 * |u|))) := mul_le_mul_of_nonneg_left hprod hu
      _ = C * A * (|u| * Real.exp (-(2 * |u|))) := by ring
      _ ≤ C * A * Real.exp (-(1 * |u|)) := mul_le_mul_of_nonneg_left hule (by positivity)

/-- **The damped transform is entire**, with derivative the transform of `iuΦh`. -/
theorem hasDerivAt_paperFT_kernel {h : ℝ → ℂ} (hh : ExpGrowth h) (z₀ : ℂ) :
    HasDerivAt (fun z => paperFT (fun u => riemannPhiKernel u * h u) z)
      (paperFT (fun u => I * u * (riemannPhiKernel u * h u)) z₀) z₀ := by
  obtain ⟨C, hC0, hC⟩ := integrable_kernel_mul_cexp hh (|z₀.im| + 1)
  have hcont := hh.1
  set F : ℂ → ℝ → ℂ := fun z u => riemannPhiKernel u * h u * cexp (I * z * u) with hF
  set F' : ℂ → ℝ → ℂ := fun z u => I * u * (riemannPhiKernel u * h u) * cexp (I * z * u)
    with hF'
  have hball : ∀ z ∈ ball z₀ 1, |z.im| ≤ |z₀.im| + 1 := by
    intro z hz
    rw [mem_ball, dist_eq_norm] at hz
    have : |z.im - z₀.im| ≤ ‖z - z₀‖ := by
      rw [← Complex.sub_im]; exact Complex.abs_im_le_norm _
    have h2 := abs_sub_abs_le_abs_sub z.im z₀.im
    linarith
  have hFc : ∀ z, Continuous (F z) := fun z => by
    simp only [hF]
    exact (continuous_riemannPhiKernel.mul hcont).mul (by fun_prop)
  have hF'c : ∀ z, Continuous (F' z) := fun z => by
    simp only [hF']
    exact ((by fun_prop : Continuous fun u : ℝ => I * (u : ℂ)).mul
      (continuous_riemannPhiKernel.mul hcont)).mul (by fun_prop)
  have hint : Integrable (F z₀) :=
    ((RHTower.integrable_exp_neg_mul_abs' (c := 1) one_pos).const_mul C).mono'
      (hFc z₀).aestronglyMeasurable (Eventually.of_forall fun u =>
        (hC z₀ (by linarith [abs_nonneg z₀.im]) u).1)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (F := F) (F' := F')
    (x₀ := z₀) (bound := fun u => C * Real.exp (-(1 * |u|))) (ball_mem_nhds z₀ one_pos)
    (Eventually.of_forall fun z => (hFc z).aestronglyMeasurable) hint
    (hF'c z₀).aestronglyMeasurable
    (Eventually.of_forall fun u z hz => (hC z (hball z hz) u).2)
    ((RHTower.integrable_exp_neg_mul_abs' (c := 1) one_pos).const_mul C)
    (Eventually.of_forall fun u z _ => by
      simp only [hF, hF']
      have h1 : HasDerivAt (fun w : ℂ => I * w * u) (I * u) z := by
        simpa using ((hasDerivAt_id z).const_mul I).mul_const (u : ℂ)
      have h2 := h1.cexp.const_mul (riemannPhiKernel u * h u)
      exact h2.congr_deriv (by ring))
  exact key.2

/-- **`(1 − cD)` multiplies the multiplier by `1 − icu`.** -/
theorem paperFT_kernel_sub_smul_deriv {h : ℝ → ℂ} (hh : ExpGrowth h) (c : ℝ) (z : ℂ) :
    paperFT (fun u => riemannPhiKernel u * h u) z -
        (c : ℂ) * deriv (fun z => paperFT (fun u => riemannPhiKernel u * h u) z) z =
      paperFT (fun u => riemannPhiKernel u * (h u * (1 - I * c * u))) z := by
  rw [(hasDerivAt_paperFT_kernel hh z).deriv]
  obtain ⟨C, hC0, hC⟩ := integrable_kernel_mul_cexp hh |z.im|
  have i1 : Integrable fun u : ℝ => riemannPhiKernel u * h u * cexp (I * z * u) :=
    ((RHTower.integrable_exp_neg_mul_abs' (c := 1) one_pos).const_mul C).mono'
      ((continuous_riemannPhiKernel.mul hh.1).mul (by fun_prop)).aestronglyMeasurable
      (Eventually.of_forall fun u => (hC z le_rfl u).1)
  have i2 : Integrable fun u : ℝ => I * u * (riemannPhiKernel u * h u) * cexp (I * z * u) :=
    ((RHTower.integrable_exp_neg_mul_abs' (c := 1) one_pos).const_mul C).mono'
      (((by fun_prop : Continuous fun u : ℝ => I * (u : ℂ)).mul
        (continuous_riemannPhiKernel.mul hh.1)).mul (by fun_prop)).aestronglyMeasurable
      (Eventually.of_forall fun u => (hC z le_rfl u).2)
  unfold paperFT
  rw [← integral_const_mul, ← integral_sub i1 (i2.const_mul _)]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only
  ring

/-! ## The chain symbol -/

/-- `P(u) = ∏_{c ∈ cs} (1 − icu)`. -/
def chainSymbol : List ℝ → ℝ → ℂ
  | [], _ => 1
  | c :: cs, u => (1 - I * c * u) * chainSymbol cs u

theorem expGrowth_chainSymbol (cs : List ℝ) : ExpGrowth (chainSymbol cs) := by
  induction cs with
  | nil => exact ⟨continuous_const, 1, 0, fun u => by simp [chainSymbol]⟩
  | cons c cs ih => exact (expGrowth_one_sub_I_mul c).mul ih

theorem one_le_norm_chainSymbol (cs : List ℝ) (u : ℝ) : 1 ≤ ‖chainSymbol cs u‖ := by
  induction cs with
  | nil => simp [chainSymbol]
  | cons c cs ih =>
    rw [chainSymbol, norm_mul]
    have h1 : 1 ≤ ‖(1 : ℂ) - I * c * u‖ := by
      have := one_le_norm_one_sub_I_mul_div (1 / c) u
      rcases eq_or_ne c 0 with rfl | hc
      · simp
      · convert this using 2
        push_cast
        field_simp
    nlinarith

theorem chainSymbol_ne_zero (cs : List ℝ) (u : ℝ) : chainSymbol cs u ≠ 0 :=
  norm_pos_iff.mp (lt_of_lt_of_le one_pos (one_le_norm_chainSymbol cs u))

theorem expGrowth_inv_chainSymbol (cs : List ℝ) : ExpGrowth fun u => (chainSymbol cs u)⁻¹ := by
  refine ⟨(expGrowth_chainSymbol cs).1.inv₀ (chainSymbol_ne_zero cs), 1, 0, fun u => ?_⟩
  rw [norm_inv, zero_mul, Real.exp_zero, mul_one]
  exact inv_le_one_of_one_le₀ (one_le_norm_chainSymbol cs u)

/-- **Transport along the chain.**  `∏_{c ∈ cs}(1 − cD)` maps `∫Φh e^{izu}` to
`∫ΦhP e^{izu}`. -/
theorem firstOrderChain_paperFT_kernel (cs : List ℝ) {h : ℝ → ℂ} (hh : ExpGrowth h) :
    firstOrderChain cs (fun z => paperFT (fun u => riemannPhiKernel u * h u) z) =
      fun z => paperFT (fun u => riemannPhiKernel u * (h u * chainSymbol cs u)) z := by
  induction cs with
  | nil => funext z; simp [firstOrderChain, chainSymbol]
  | cons c cs ih =>
    funext z
    simp only [firstOrderChain]
    rw [ih, paperFT_kernel_sub_smul_deriv (hh.mul (expGrowth_chainSymbol cs)) c z]
    congr 1
    funext u
    simp only [chainSymbol]
    ring

/-- The damped transform `Ξ_P(z) = ∫ Φ(u) P(u)^{−1} e^{izu} du`. -/
def dampedKernelTransform (cs : List ℝ) (z : ℂ) : ℂ :=
  paperFT (fun u => riemannPhiKernel u * (chainSymbol cs u)⁻¹) z

/-- `∏_{c ∈ cs}(1 − cD) Ξ_P = Ξ`. -/
theorem firstOrderChain_dampedKernelTransform (cs : List ℝ) :
    firstOrderChain cs (dampedKernelTransform cs) = XiC := by
  have h := firstOrderChain_paperFT_kernel cs (expGrowth_inv_chainSymbol cs)
  have e : dampedKernelTransform cs =
      fun z => paperFT (fun u => riemannPhiKernel u * (chainSymbol cs u)⁻¹) z := rfl
  rw [e, h]
  funext z
  rw [← Littlewood.paperFT_riemannPhiKernel_eq_XiC]
  congr 1
  funext u
  rw [inv_mul_cancel₀ (chainSymbol_ne_zero cs u), mul_one]

/-- **Damped kernels leave the Laguerre–Pólya class.**  If some `c ∈ cs` is nonzero, the
transform of `Φ(u)/∏_{c ∈ cs}(1 − icu)` is not Laguerre–Pólya. -/
theorem not_laguerrePolya_dampedKernelTransform {cs : List ℝ} (hcs : ∃ c ∈ cs, c ≠ 0) :
    ¬ GaloisForLFunctions.HTGeometry.LaguerrePolya (dampedKernelTransform cs) := fun hLP =>
  RHTower.not_exists_laguerrePolya_firstOrderChain_preimage_XiC_of_exists_ne hcs
    ⟨_, hLP, firstOrderChain_dampedKernelTransform cs⟩

/-- **Lorentzian damping.**  For every real `b ≠ 0`, `z ↦ ∫ Φ(u)/(1 + b²u²) e^{izu} du` is not
Laguerre–Pólya. -/
theorem not_laguerrePolya_lorentzDampedKernelTransform {b : ℝ} (hb : b ≠ 0) :
    ¬ GaloisForLFunctions.HTGeometry.LaguerrePolya
      (fun z => ∫ u : ℝ, riemannPhiKernel u / (1 + (b : ℂ) ^ 2 * (u : ℂ) ^ 2) *
        cexp (I * z * u)) := by
  have e : (fun z => ∫ u : ℝ, riemannPhiKernel u / (1 + (b : ℂ) ^ 2 * (u : ℂ) ^ 2) *
      cexp (I * z * u)) = dampedKernelTransform [b, -b] := by
    funext z
    unfold dampedKernelTransform paperFT
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    have hs : chainSymbol [b, -b] u = 1 + (b : ℂ) ^ 2 * (u : ℂ) ^ 2 := by
      simp only [chainSymbol]
      push_cast
      ring_nf
      rw [Complex.I_sq]
      ring
    simp only
    rw [hs, div_eq_mul_inv]
  rw [e]
  exact not_laguerrePolya_dampedKernelTransform ⟨b, by simp, hb⟩

end

end RHTower.KernelStrip
