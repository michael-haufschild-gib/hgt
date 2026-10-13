import GaloisForLFunctions.RHTower.ZetaWeightedPoisson

/-!
# The main term of the weighted kernel

For a window `φ` (continuous, supported in `[−A, A]`, `|φ̂(s)|(1 + s²)` bounded) Fourier inversion in the paper's
normalisation reads `∫ φ̂(r) e^{−iyr} dr = 2π φ(y)` (`integral_paperFT_mul_cexp_neg`).  Consequently

`∫ e^{iξs} φ̂(τ − s) φ̂(τ' − s) ds = 2π e^{iξτ'} ∫ φ(u) φ(ξ − u) e^{i(τ−τ')u} du`   (`integral_cexp_mul_phiHat_mul_phiHat`),

and for a weight `W = ψ^∨` the main term of the weighted Poisson identity is the continuous kernel

`∫ ψ(ξ) e^{iξτ'} G_ξ(0) dξ = (L/2π) ∫ W(s) φ̂(τ − s) φ̂(τ' − s) ds`   (`integral_psi_mul_Gaux2_zero_eq`).
-/

open Complex MeasureTheory Real Set Filter
open Zeta23
open scoped FourierTransform

noncomputable section

namespace RHTower

namespace TwistedPoisson

variable {φ : ℝ → ℝ} {A : ℝ}

theorem integrable_paperFT_of_decay
    (hdecay : ∃ C, ∀ s : ℝ, ‖paperFT (fun u => (φ u : ℂ)) s‖ * (1 + s ^ 2) ≤ C)
    (hc : Continuous fun s : ℝ => paperFT (fun u => (φ u : ℂ)) s) :
    Integrable fun s : ℝ => paperFT (fun u => (φ u : ℂ)) s := by
  obtain ⟨C, hC⟩ := hdecay
  refine Integrable.mono' ((integrable_inv_one_add_sq).const_mul C) hc.aestronglyMeasurable
    (Eventually.of_forall fun s => ?_)
  have hpos : 0 < 1 + s ^ 2 := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ hpos]
  exact hC s

/-- **Fourier inversion in the paper's normalisation:** `∫ φ̂(r) e^{−iyr} dr = 2π φ(y)`. -/
theorem integral_paperFT_mul_cexp_neg (hφc : Continuous φ) (hsupp : ∀ u, A ≤ |u| → φ u = 0)
    (hdecay : ∃ C, ∀ s : ℝ, ‖paperFT (fun u => (φ u : ℂ)) s‖ * (1 + s ^ 2) ≤ C)
    (hc : Continuous fun s : ℝ => paperFT (fun u => (φ u : ℂ)) s) (y : ℝ) :
    ∫ r : ℝ, paperFT (fun u => (φ u : ℂ)) (r : ℂ) * cexp (-(I * y * (r : ℂ))) = 2 * π * (φ y : ℂ) := by
  set f : ℝ → ℂ := fun u => (φ u : ℂ) with hf
  have hfc : Continuous f := by simp only [hf]; fun_prop
  have hfi : Integrable f := by
    refine hfc.integrable_of_hasCompactSupport ?_
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -A) (b := A)) ?_
    intro u hu
    rw [Function.mem_support] at hu
    by_contra h
    apply hu
    simp only [hf]
    rw [hsupp u]
    · simp
    rw [mem_Icc, not_and_or, not_le, not_le] at h
    rcases h with h | h
    · linarith [neg_abs_le u]
    · linarith [le_abs_self u]
  have hFi : Integrable (𝓕 f) := by
    have e : 𝓕 f = fun w => paperFT f (((-(2 * π) * w : ℝ)) : ℂ) := by
      funext w; rw [fourier_eq_paperFT]; push_cast; ring_nf
    rw [e]
    exact (integrable_paperFT_of_decay hdecay hc).comp_mul_left' (neg_ne_zero.mpr (by positivity))
  have hinv := congrFun (hfc.fourierInv_fourier_eq hfi hFi) y
  rw [Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq] at hinv
  set g : ℝ → ℂ := fun w => 𝓕 f w * cexp (((2 * π * (w * y)) : ℝ) * I) with hg
  have hinv' : ∫ w, g w = f y := by
    rw [← hinv]
    congr 1 with w
    simp only [hg, Circle.smul_def, Real.fourierChar_apply, smul_eq_mul]
    rw [mul_comm, show -(w * -y) = w * y by ring]
  have hcov := Measure.integral_comp_mul_left g (-(1 / (2 * π)))
  have hpt : ∀ r : ℝ, g (-(1 / (2 * π)) * r) = paperFT f r * cexp (-(I * y * r)) := by
    intro r
    simp only [hg]
    rw [fourier_eq_paperFT]
    congr 2
    · push_cast; field_simp
    · push_cast; field_simp
  simp_rw [hpt] at hcov
  rw [hcov, hinv', show |(-(1 / (2 * π)))⁻¹| = 2 * π by
    rw [inv_neg, abs_neg, one_div, inv_inv, abs_of_pos (by positivity)], Complex.real_smul]
  push_cast
  ring

/-- `∫ e^{iξs} φ̂(τ − s) φ̂(τ' − s) ds = 2π e^{iξτ'} ∫ φ(u) φ(ξ − u) e^{i(τ−τ')u} du`. -/
theorem integral_cexp_mul_phiHat_mul_phiHat (hφc : Continuous φ) (hsupp : ∀ u, A ≤ |u| → φ u = 0)
    (hdecay : ∃ C, ∀ s : ℝ, ‖paperFT (fun u => (φ u : ℂ)) s‖ * (1 + s ^ 2) ≤ C)
    (hc : Continuous fun s : ℝ => paperFT (fun u => (φ u : ℂ)) s) (ξ τ τ' : ℝ) :
    ∫ s : ℝ, cexp (I * ξ * s) * paperFT (fun u => (φ u : ℂ)) ((τ - s : ℝ) : ℂ)
        * paperFT (fun u => (φ u : ℂ)) ((τ' - s : ℝ) : ℂ)
      = 2 * π * cexp (I * ξ * τ')
        * ∫ u : ℝ, (φ u : ℂ) * (φ (ξ - u) : ℂ) * cexp (I * ((τ - τ' : ℝ) : ℂ) * u) := by
  set f : ℝ → ℂ := fun u => (φ u : ℂ) with hf
  have hfc : Continuous f := by simp only [hf]; fun_prop
  have hfi : Integrable f := by
    refine hfc.integrable_of_hasCompactSupport ?_
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -A) (b := A)) ?_
    intro u hu
    rw [Function.mem_support] at hu
    by_contra h
    apply hu
    simp only [hf]
    rw [hsupp u]
    · simp
    rw [mem_Icc, not_and_or, not_le, not_le] at h
    rcases h with h | h
    · linarith [neg_abs_le u]
    · linarith [le_abs_self u]
  have hPi := integrable_paperFT_of_decay hdecay hc
  set Fi : ℝ → ℝ → ℂ := fun s u => f u * cexp (I * τ * u)
      * (cexp (I * ((ξ - u : ℝ) : ℂ) * s) * paperFT f ((τ' - s : ℝ) : ℂ)) with hFi
  have hpt : ∀ s : ℝ, cexp (I * ξ * s) * paperFT f ((τ - s : ℝ) : ℂ) * paperFT f ((τ' - s : ℝ) : ℂ)
      = ∫ u, Fi s u := by
    intro s
    rw [paperFT_def]
    rw [show (cexp (I * ξ * s) * ∫ u : ℝ, f u * cexp (I * ((τ - s : ℝ) : ℂ) * u))
          * paperFT f ((τ' - s : ℝ) : ℂ)
        = (∫ u : ℝ, f u * cexp (I * ((τ - s : ℝ) : ℂ) * u))
          * (cexp (I * ξ * s) * paperFT f ((τ' - s : ℝ) : ℂ)) by ring, ← integral_mul_const]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [hFi]
    have e : cexp (I * ξ * s) * cexp (I * ((τ - s : ℝ) : ℂ) * u)
        = cexp (I * τ * u) * cexp (I * ((ξ - u : ℝ) : ℂ) * s) := by
      rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; push_cast; ring
    linear_combination (f u * paperFT f ((τ' - s : ℝ) : ℂ)) * e
  simp_rw [hpt]
  have hnorm : ∀ s u, ‖Fi s u‖ = ‖f u‖ * ‖paperFT f ((τ' - s : ℝ) : ℂ)‖ := by
    intro s u
    simp only [hFi]
    rw [norm_mul, norm_mul, norm_mul,
      show I * (τ : ℂ) * (u : ℂ) = ((τ * u : ℝ) : ℂ) * I by push_cast; ring,
      show I * ((ξ - u : ℝ) : ℂ) * (s : ℂ) = (((ξ - u) * s : ℝ) : ℂ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, Complex.norm_exp_ofReal_mul_I]
    ring
  have hint : Integrable (Function.uncurry Fi) (volume.prod volume) := by
    have hc2 : Continuous (Function.uncurry Fi) := by
      have hc' : Continuous fun q : ℝ × ℝ => paperFT f ((τ' - q.1 : ℝ) : ℂ) :=
        hc.comp ((continuous_const.sub continuous_fst))
      have hf2 : Continuous fun q : ℝ × ℝ => f q.2 := hfc.comp continuous_snd
      simp only [hFi]
      fun_prop
    have hmaj : Integrable (fun q : ℝ × ℝ => ‖paperFT f ((τ' - q.1 : ℝ) : ℂ)‖ * ‖f q.2‖)
        (volume.prod volume) :=
      ((hPi.comp_sub_left τ').norm).mul_prod hfi.norm
    refine hmaj.mono' hc2.aestronglyMeasurable (Eventually.of_forall fun q => ?_)
    show ‖Fi q.1 q.2‖ ≤ ‖paperFT f ((τ' - q.1 : ℝ) : ℂ)‖ * ‖f q.2‖
    rw [hnorm, mul_comm]
  rw [integral_integral_swap hint, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [hFi]
  rw [integral_const_mul]
  have hinner : ∫ s : ℝ, cexp (I * ((ξ - u : ℝ) : ℂ) * s) * paperFT f ((τ' - s : ℝ) : ℂ)
      = cexp (I * ((ξ - u : ℝ) : ℂ) * τ') * (2 * π * (φ (ξ - u) : ℂ)) := by
    rw [← integral_sub_left_eq_self (fun s : ℝ => cexp (I * ((ξ - u : ℝ) : ℂ) * s)
        * paperFT f ((τ' - s : ℝ) : ℂ)) volume τ',
      ← integral_paperFT_mul_cexp_neg hφc hsupp hdecay hc (ξ - u), ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun r => ?_)
    simp only [sub_sub_cancel]
    rw [show cexp (I * ((ξ - u : ℝ) : ℂ) * ((τ' - r : ℝ) : ℂ))
        = cexp (I * ((ξ - u : ℝ) : ℂ) * τ') * cexp (-(I * ((ξ - u : ℝ) : ℂ) * r)) by
      rw [← Complex.exp_add]; congr 1; push_cast; ring]
    ring
  rw [hinner]
  have e2 : cexp (I * τ * u) * cexp (I * ((ξ - u : ℝ) : ℂ) * τ')
      = cexp (I * ξ * τ') * cexp (I * ((τ - τ' : ℝ) : ℂ) * u) := by
    rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; push_cast; ring
  simp only [hf]
  linear_combination (2 * π * (φ u : ℂ) * (φ (ξ - u) : ℂ)) * e2

/-- **The main term of the weighted kernel is the continuous kernel:**
`∫ ψ(ξ) e^{iξτ'} G_ξ(0) dξ = (L/2π) ∫ W(s) φ̂(τ − s) φ̂(τ' − s) ds`, `W(s) = ∫ ψ(ξ) e^{iξs} dξ`. -/
theorem integral_psi_mul_Gaux2_zero_eq {L : ℝ} (hφc : Continuous φ)
    (hsupp : ∀ u, L / 2 ≤ |u| → φ u = 0)
    (hdecay : ∃ C, ∀ s : ℝ, ‖paperFT (fun u => (φ u : ℂ)) s‖ * (1 + s ^ 2) ≤ C)
    (hc : Continuous fun s : ℝ => paperFT (fun u => (φ u : ℂ)) s) {ψ : ℝ → ℂ} (hψ : Integrable ψ)
    (T τ τ' : ℝ) :
    ∫ ξ, ψ ξ * (cexp (I * ξ * τ') * Gaux2 φ (fun v => φ (v + ξ)) L T τ τ' 0)
      = ((L / (2 * π) : ℝ) : ℂ) * ∫ s : ℝ, (∫ ξ, ψ ξ * cexp (I * ξ * s))
          * paperFT (fun u => (φ u : ℂ)) ((τ - s : ℝ) : ℂ)
          * paperFT (fun u => (φ u : ℂ)) ((τ' - s : ℝ) : ℂ) := by
  set f : ℝ → ℂ := fun u => (φ u : ℂ) with hf
  have hPi := integrable_paperFT_of_decay hdecay hc
  obtain ⟨C, hC⟩ := hdecay
  have hC0 : 0 ≤ C := le_trans (by positivity) (hC 0)
  have hbdd : ∀ s : ℝ, ‖paperFT f s‖ ≤ C := by
    intro s
    have h2 : ‖paperFT f s‖ * 1 ≤ ‖paperFT f s‖ * (1 + s ^ 2) := by gcongr; nlinarith
    linarith [hC s]
  -- the key per-frequency identity
  have hkey : ∀ ξ : ℝ, cexp (I * ξ * τ') * Gaux2 φ (fun v => φ (v + ξ)) L T τ τ' 0
      = ((L / (2 * π) : ℝ) : ℂ) * ∫ s : ℝ, cexp (I * ξ * s) * paperFT f ((τ - s : ℝ) : ℂ)
          * paperFT f ((τ' - s : ℝ) : ℂ) := by
    intro ξ
    rw [Gaux2_zero_twist, integral_cexp_mul_phiHat_mul_phiHat hφc hsupp ⟨C, hC⟩ hc ξ τ τ']
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    push_cast
    field_simp
  simp_rw [hkey]
  -- Fubini
  set H : ℝ → ℝ → ℂ := fun ξ s => ψ ξ * (cexp (I * ξ * s) * paperFT f ((τ - s : ℝ) : ℂ)
      * paperFT f ((τ' - s : ℝ) : ℂ)) with hH
  have hnorm : ∀ ξ s, ‖H ξ s‖ = ‖ψ ξ‖ * (‖paperFT f ((τ - s : ℝ) : ℂ)‖ * ‖paperFT f ((τ' - s : ℝ) : ℂ)‖) := by
    intro ξ s
    simp only [hH]
    rw [norm_mul, norm_mul, norm_mul,
      show I * (ξ : ℂ) * (s : ℂ) = ((ξ * s : ℝ) : ℂ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I]
    ring
  have hprod : Integrable (fun s : ℝ => ‖paperFT f ((τ - s : ℝ) : ℂ)‖ * ‖paperFT f ((τ' - s : ℝ) : ℂ)‖) := by
    refine Integrable.mono' ((hPi.comp_sub_left τ).norm.mul_const C) ?_
      (Eventually.of_forall fun s => ?_)
    · exact ((hc.comp (continuous_const.sub continuous_id)).norm.mul
        (hc.comp (continuous_const.sub continuous_id)).norm).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left (hbdd _) (norm_nonneg _)
  have hint : Integrable (Function.uncurry H) (volume.prod volume) := by
    have hmaj : Integrable (fun q : ℝ × ℝ => ‖ψ q.1‖ * (‖paperFT f ((τ - q.2 : ℝ) : ℂ)‖
        * ‖paperFT f ((τ' - q.2 : ℝ) : ℂ)‖)) (volume.prod volume) := hψ.norm.mul_prod hprod
    have hmeas : AEStronglyMeasurable (Function.uncurry H) (volume.prod volume) := by
      have h1 : AEStronglyMeasurable (fun q : ℝ × ℝ => ψ q.1) (volume.prod volume) :=
        hψ.aestronglyMeasurable.comp_fst
      have h2 : Continuous fun q : ℝ × ℝ => cexp (I * q.1 * q.2) * paperFT f ((τ - q.2 : ℝ) : ℂ)
          * paperFT f ((τ' - q.2 : ℝ) : ℂ) := by
        have hc1 : Continuous fun q : ℝ × ℝ => paperFT f ((τ - q.2 : ℝ) : ℂ) :=
          hc.comp (continuous_const.sub continuous_snd)
        have hc2 : Continuous fun q : ℝ × ℝ => paperFT f ((τ' - q.2 : ℝ) : ℂ) :=
          hc.comp (continuous_const.sub continuous_snd)
        fun_prop
      exact h1.mul h2.aestronglyMeasurable
    refine hmaj.mono' hmeas (Eventually.of_forall fun q => le_of_eq ?_)
    exact hnorm q.1 q.2
  have e1 : ∫ ξ, ψ ξ * (((L / (2 * π) : ℝ) : ℂ) * ∫ s : ℝ, cexp (I * ξ * s)
        * paperFT f ((τ - s : ℝ) : ℂ) * paperFT f ((τ' - s : ℝ) : ℂ))
      = ((L / (2 * π) : ℝ) : ℂ) * ∫ ξ, ∫ s, H ξ s := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp only [hH]
    rw [← integral_const_mul, ← integral_const_mul, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    ring
  rw [e1, integral_integral_swap hint]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  simp only [hH]
  rw [← integral_mul_const, ← integral_mul_const]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  ring

/-- For an even window the transform is even: `φ̂(−z) = φ̂(z)`. -/
theorem paperFT_neg_of_even (heven : ∀ u, φ (-u) = φ u) (z : ℂ) :
    paperFT (fun u => (φ u : ℂ)) (-z) = paperFT (fun u => (φ u : ℂ)) z := by
  rw [paperFT_def, paperFT_def, ← integral_neg_eq_self]
  congr 1 with u
  rw [heven]
  congr 1
  push_cast
  ring_nf

/-- For an even real window the transform is real on the real line. -/
theorem paperFT_im_eq_zero_of_even (heven : ∀ u, φ (-u) = φ u) (r : ℝ) :
    (paperFT (fun u => (φ u : ℂ)) r).im = 0 := by
  have hconj : starRingEnd ℂ (paperFT (fun u => (φ u : ℂ)) r) = paperFT (fun u => (φ u : ℂ)) (-r) := by
    rw [paperFT_def, paperFT_def, ← integral_conj]
    congr 1 with u
    rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
    congr 2
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  rw [paperFT_neg_of_even heven] at hconj
  exact Complex.conj_eq_iff_im.mp hconj

/-- **The prime-frequency Gram entry in closed form.**  For an even window,
`∫ φ̂(τ − τ_a) φ̂(τ − τ_b) cos(yτ) dτ = Re[2π e^{iyτ_b} ∫ φ(u) φ(y − u) e^{i(τ_a − τ_b)u} du]`. -/
theorem integral_phiHat_mul_phiHat_mul_cos (hφc : Continuous φ) (hsupp : ∀ u, A ≤ |u| → φ u = 0)
    (heven : ∀ u, φ (-u) = φ u)
    (hdecay : ∃ C, ∀ s : ℝ, ‖paperFT (fun u => (φ u : ℂ)) s‖ * (1 + s ^ 2) ≤ C)
    (hc : Continuous fun s : ℝ => paperFT (fun u => (φ u : ℂ)) s) (y τa τb : ℝ) :
    ∫ τ : ℝ, (paperFT (fun u => (φ u : ℂ)) ((τ - τa : ℝ) : ℂ)).re
        * (paperFT (fun u => (φ u : ℂ)) ((τ - τb : ℝ) : ℂ)).re * Real.cos (τ * y)
      = (2 * π * cexp (I * y * τb)
          * ∫ u : ℝ, (φ u : ℂ) * (φ (y - u) : ℂ) * cexp (I * ((τa - τb : ℝ) : ℂ) * u)).re := by
  set f : ℝ → ℂ := fun u => (φ u : ℂ) with hf
  have hreal : ∀ r : ℝ, (paperFT f r : ℂ) = ((paperFT f r).re : ℂ) := fun r => by
    have h := paperFT_im_eq_zero_of_even (φ := φ) heven r
    rw [← hf] at h
    apply Complex.ext
    · simp
    · simp [h]
  have hPi := integrable_paperFT_of_decay hdecay hc
  obtain ⟨C, hC⟩ := hdecay
  have hC0 : 0 ≤ C := le_trans (by positivity) (hC 0)
  have hbdd : ∀ s : ℝ, ‖paperFT f s‖ ≤ C := by
    intro s
    have h2 : ‖paperFT f s‖ * 1 ≤ ‖paperFT f s‖ * (1 + s ^ 2) := by gcongr; nlinarith
    linarith [hC s]
  have hpt : ∀ τ : ℝ, (paperFT f ((τ - τa : ℝ) : ℂ)).re * (paperFT f ((τ - τb : ℝ) : ℂ)).re
        * Real.cos (τ * y)
      = (cexp (I * y * τ) * paperFT f ((τa - τ : ℝ) : ℂ) * paperFT f ((τb - τ : ℝ) : ℂ)).re := by
    intro τ
    have ea : paperFT f ((τa - τ : ℝ) : ℂ) = ((paperFT f ((τ - τa : ℝ) : ℂ)).re : ℂ) := by
      rw [show ((τa - τ : ℝ) : ℂ) = -((τ - τa : ℝ) : ℂ) by push_cast; ring,
        paperFT_neg_of_even heven]
      exact hreal _
    have eb : paperFT f ((τb - τ : ℝ) : ℂ) = ((paperFT f ((τ - τb : ℝ) : ℂ)).re : ℂ) := by
      rw [show ((τb - τ : ℝ) : ℂ) = -((τ - τb : ℝ) : ℂ) by push_cast; ring,
        paperFT_neg_of_even heven]
      exact hreal _
    rw [ea, eb, show cexp (I * (y : ℂ) * (τ : ℂ)) * ((paperFT f ((τ - τa : ℝ) : ℂ)).re : ℂ)
          * ((paperFT f ((τ - τb : ℝ) : ℂ)).re : ℂ)
        = (((paperFT f ((τ - τa : ℝ) : ℂ)).re * (paperFT f ((τ - τb : ℝ) : ℂ)).re : ℝ) : ℂ)
          * cexp (((y * τ : ℝ) : ℂ) * I) by push_cast; ring,
      Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re, mul_comm y τ]
  simp_rw [hpt]
  have hint : Integrable fun τ : ℝ => cexp (I * y * τ) * paperFT f ((τa - τ : ℝ) : ℂ)
      * paperFT f ((τb - τ : ℝ) : ℂ) := by
    refine Integrable.mono' ((hPi.comp_sub_left τa).norm.mul_const C) ?_
      (Eventually.of_forall fun τ => ?_)
    · have hc1 : Continuous fun τ : ℝ => paperFT f ((τa - τ : ℝ) : ℂ) :=
        hc.comp (continuous_const.sub continuous_id)
      have hc2 : Continuous fun τ : ℝ => paperFT f ((τb - τ : ℝ) : ℂ) :=
        hc.comp (continuous_const.sub continuous_id)
      exact (by fun_prop : Continuous fun τ : ℝ => cexp (I * y * τ) * paperFT f ((τa - τ : ℝ) : ℂ)
        * paperFT f ((τb - τ : ℝ) : ℂ)).aestronglyMeasurable
    · rw [norm_mul, norm_mul, show I * (y : ℂ) * (τ : ℂ) = ((y * τ : ℝ) : ℂ) * I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I, one_mul]
      exact mul_le_mul_of_nonneg_left (hbdd _) (norm_nonneg _)
  have hre := integral_re hint
  simp only [RCLike.re_to_complex] at hre
  rw [hre, integral_cexp_mul_phiHat_mul_phiHat hφc hsupp ⟨C, hC⟩ hc y τa τb]

end TwistedPoisson

end RHTower
