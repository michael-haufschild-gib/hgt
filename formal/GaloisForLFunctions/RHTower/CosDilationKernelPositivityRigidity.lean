import GaloisForLFunctions.RHTower.CosDilationKernelBlindnessLink
import GaloisForLFunctions.RHTower.CosDilationShortSupportRigidity

/-!
# Positivity, second-moment identity, and full-integer rigidity of the cosine–dilation kernel

Let `f : ℝ → ℝ` be smooth and supported in `[α, β]` (`0 < α ≤ β`) with `𝓜f(1) = ∫_0^∞ f = 0`, and
let `R_f = cosDilationCertMultiplier f` be the resolved certificate multiplier and
`Ψ_f = cosDilationKernel f = Cf ⋆ f` be the cosine–dilation kernel.

* **Kernel and Mellin injectivity** (`eq_zero_of_cosDilationKernel_pos_eq_zero`,
  `eq_zero_of_mellin_criticalLine_eq_zero`): if `Ψ_f` vanishes on `(0, ∞)` (for any continuous core
  `f`), or if `𝓜f` vanishes on the critical line `Re s = ½` (for any smooth core `f`), then `f = 0`.
* **Critical-strip and critical-line factorizations**
  (`norm_archXi_sq_mul_cosDilationCertMultiplier_criticalLine`,
  `xi_sq_mul_cosDilationCertMultiplier_strip`,
  `xi_sq_mul_cosDilationCertMultiplier_criticalLine`): on `0 < Re s < 1`, the functional equation
  `ξ(1−s) = ξ(s)` cancels the archimedean Gamma ratio algebraically to give
  `ξ(s)² R_f(s) = ζ(s) ζ(1−s) 𝓜f(s) 𝓜f(1−s)`. On `Re s = ½`, Schwarz reflection gives
  `ξ(½+it)² R_f(½+it) = ‖ζ(½+it) 𝓜f(½+it)‖²` and `‖archXi(½+it)² R_f(½+it)‖ = ‖𝓜f(½+it)‖²`.
* **Second-moment identity and central positivity**
  (`integral_norm_zeta_mul_mellin_sq_eq_cosDilationKernel_one`,
  `cosDilationKernel_one_nonneg_of_blind`): if `f` is blind at `n ≥ 2` (`Ψ_f(n) = 0` for all
  `n ≥ 2`), then
  `∫ ‖ζ(½+it) 𝓜f(½+it)‖² dt = 2π Ψ_f(1) ≥ 0`.
* **Full-integer blindness rigidity** (`eq_zero_of_cosDilationKernel_blind_of_one_nonpos`,
  `eq_zero_of_cosDilationKernel_nat_eq_zero`): if `f` is blind at `n ≥ 2` and `Ψ_f(1) ≤ 0`, then
  `f = 0` regardless of the support ratio `β/α`. In particular, no nonzero smooth core `f` with
  `𝓜f(1) = 0` can have `Ψ_f(n) = 0` for all `n ≥ 1`.
* **Critical log-room rigidity** (`eq_zero_of_cosDilationKernel_blind_of_mellin_logRoom`): if `f`
  is blind at `n ≥ 2` and `‖𝓜f(½+it)‖²` is integrable against `logRoomWeight (π / 2)`, then `f = 0`.
-/

open Complex MeasureTheory Set Real Filter Topology
open scoped FourierTransform ContDiff

namespace RHTower

open RHTower.ExactNullDivisorTransfer RHTower.PrimeBlindCarlson

noncomputable section

variable {f : ℝ → ℝ}

/-- If the cosine–dilation kernel `Ψ_f` vanishes on `(0, ∞)`, then `f = 0`. -/
theorem eq_zero_of_cosDilationKernel_pos_eq_zero (hf : Continuous f) {α β : ℝ}
    (hα : 0 < α) (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (hΨ : ∀ x : ℝ, 0 < x → cosDilationKernel f x = 0) (y : ℝ) : f y = 0 := by
  have hcontA : Continuous fun r => dilationAutocorr f |r| :=
    (continuous_dilationAutocorr hf hα hsupp).comp continuous_abs
  have hcsA := hasCompactSupport_dilationAutocorr_abs hα hαβ hsupp (f := f)
  have hcontΨ : Continuous (cosDilationKernel f) := by
    have e : cosDilationKernel f =
        fun x => ∫ r, dilationAutocorr f |r| * Real.cos (2 * π * (x * r)) := by
      funext x; exact cosDilationKernel_eq_integral_abs hf hα hαβ hsupp x
    rw [e]
    refine continuous_of_dominated (bound := fun r => abs (dilationAutocorr f |r|)) ?_ ?_ ?_ ?_
    · intro x; exact (hcontA.mul (by fun_prop)).aestronglyMeasurable
    · intro x; refine Eventually.of_forall fun r => ?_
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
    · exact hcontA.abs.integrable_of_hasCompactSupport hcsA.abs
    · exact Eventually.of_forall fun r => by fun_prop
  have hΨ0 : cosDilationKernel f 0 = 0 := by
    have hlim : Tendsto (cosDilationKernel f) (𝓝[>] 0) (𝓝 (cosDilationKernel f 0)) :=
      hcontΨ.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hzero : ∀ᶠ x in 𝓝[>] (0 : ℝ), cosDilationKernel f x = 0 := by
      filter_upwards [self_mem_nhdsWithin] with x hx using hΨ x hx
    exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (hzero.mono fun _ h => h.symm))
  set ρ : ℝ → ℂ := (evenDilationAutocorr hf hα hsupp : ℝ → ℂ)
  have hF0 : 𝓕 ρ = 0 := by
    funext w
    rw [Pi.zero_apply, fourier_evenDilationAutocorr hf hα hαβ hsupp w, Complex.ofReal_eq_zero]
    rcases lt_trichotomy 0 w with hw | rfl | hw
    · exact hΨ w hw
    · exact hΨ0
    · rw [← cosDilationKernel_neg hf hα hαβ hsupp]
      exact hΨ (-w) (neg_pos.mpr hw)
  have hρc : Continuous ρ := (evenDilationAutocorr hf hα hsupp).continuous
  have hρi : Integrable ρ :=
    hρc.integrable_of_hasCompactSupport
      (hcsA.comp_left (g := fun x : ℝ => (x : ℂ)) Complex.ofReal_zero)
  have hFi : Integrable (𝓕 ρ) := by rw [hF0]; exact integrable_zero _ _ _
  have hinv := Continuous.fourierInv_fourier_eq hρc hρi hFi
  rw [hF0] at hinv
  have hA1 : dilationAutocorr f 1 = 0 := by
    have h1 := (congrFun hinv 1).symm
    simpa [ρ, evenDilationAutocorr, Real.fourierInv_eq_fourier_neg,
      fourier_real_eq_integral_exp_smul] using h1
  have hfc : HasCompactSupport f := hasCompactSupport_of_support_Icc hsupp
  have hsq : Integrable fun z => f z * f z :=
    (hf.mul hf).integrable_of_hasCompactSupport hfc.mul_right
  have hEz : ∫ z, f z * f z = 0 := by
    rw [← hA1]
    unfold dilationAutocorr
    simp only [one_mul]
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => ?_).symm
    have : f z = 0 := by
      by_contra h
      exact hz (lt_of_lt_of_le hα (hsupp z h).1)
    simp [this]
  have hae : (fun z => f z * f z) =ᵐ[volume] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun z => mul_self_nonneg (f z)) hsq).mp hEz
  have heq := (Continuous.ae_eq_iff_eq volume (hf.mul hf) continuous_const).mp hae
  exact mul_self_eq_zero.mp (congrFun heq y)

/-- If the Mellin transform of a smooth compact core `f` vanishes on the critical line, `f = 0`. -/
theorem eq_zero_of_mellin_criticalLine_eq_zero (hf : ContDiff ℝ ∞ f) {α β : ℝ}
    (hα : 0 < α) (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (hm : ∀ t : ℝ, mellin (fun y : ℝ => (f y : ℂ)) (1 / 2 + t * I) = 0) (y : ℝ) : f y = 0 := by
  refine eq_zero_of_cosDilationKernel_pos_eq_zero hf.continuous hα hαβ hsupp (fun x hx => ?_) y
  rw [← Complex.ofReal_eq_zero, ← mellinInv_gammaRatio_mellin_eq_cosDilationKernel hf hα hαβ hsupp hx]
  unfold mellinInv
  have h0 : (∫ t : ℝ, (x : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)) •
      (Complex.Gammaℝ (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) /
        Complex.Gammaℝ (1 - (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)) *
        mellin (fun y : ℝ => (f y : ℂ)) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
        mellin (fun y : ℝ => (f y : ℂ)) (1 - (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)))) = 0 := by
    refine integral_eq_zero_of_ae (Eventually.of_forall fun t => ?_)
    show (x : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)) •
      (Complex.Gammaℝ (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) /
        Complex.Gammaℝ (1 - (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)) *
        mellin (fun y : ℝ => (f y : ℂ)) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
        mellin (fun y : ℝ => (f y : ℂ)) (1 - (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I))) = 0
    have ht := hm t
    push_cast at ht ⊢
    rw [ht, mul_zero, zero_mul, smul_zero]
  rw [h0, smul_zero]

/-- Schwarz reflection for the Mellin transform of a real-valued core. -/
theorem mellin_ofReal_conj (f : ℝ → ℝ) (s : ℂ) :
    mellin (fun y : ℝ => (f y : ℂ)) (starRingEnd ℂ s) =
      starRingEnd ℂ (mellin (fun y : ℝ => (f y : ℂ)) s) := by
  unfold mellin
  rw [← integral_conj]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : (0 : ℝ) < t := ht
  simp only [smul_eq_mul, map_mul, Complex.conj_ofReal]
  congr 1
  have harg : (t : ℂ).arg ≠ π := by
    rw [Complex.arg_ofReal_of_nonneg ht0.le]
    exact Real.pi_ne_zero.symm
  have hcp := Complex.cpow_conj (t : ℂ) (s - 1) harg
  simpa [Complex.conj_ofReal] using hcp

theorem one_sub_criticalLine_eq_conj (t : ℝ) :
    (1 : ℂ) - (1 / 2 + (t : ℂ) * I) = starRingEnd ℂ (1 / 2 + (t : ℂ) * I) := by
  apply Complex.ext
  · simp; norm_num
  · simp

/-- On the critical line, `‖archXi(½+it)² R_f(½+it)‖ = ‖𝓜f(½+it)‖²`. -/
theorem norm_archXi_sq_mul_cosDilationCertMultiplier_criticalLine
    (h0 : mellin (fun y : ℝ => (f y : ℂ)) 1 = 0) (t : ℝ) :
    ‖archXi (1 / 2 + t * I) ^ 2 * cosDilationCertMultiplier f (1 / 2 + t * I)‖ =
      ‖mellin (fun y : ℝ => (f y : ℂ)) (1 / 2 + t * I)‖ ^ 2 := by
  set s : ℂ := 1 / 2 + t * I with hs_def
  have hsre : 0 < s.re := by simp [s]
  have hs1 : s ≠ 1 := by intro h; have := congrArg Complex.re h; simp [s] at this
  have hG : Complex.Gamma ((1 - s) / 2) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by simp [s]; norm_num)
  rw [archXi_sq_mul_cosDilationCertMultiplier hsre hs1 hG h0, norm_mul, norm_mul, norm_div]
  have hconj : 1 - s = starRingEnd ℂ s := one_sub_criticalLine_eq_conj t
  have hGne : ‖Complex.Gammaℝ s‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (Complex.Gammaℝ_ne_zero_of_re_pos hsre)
  have hG1 : ‖Complex.Gammaℝ (1 - s)‖ = ‖Complex.Gammaℝ s‖ := by
    rw [hconj, Gammaℝ_conj, RCLike.norm_conj]
  have hm1 : ‖mellin (fun y : ℝ => (f y : ℂ)) (1 - s)‖ =
      ‖mellin (fun y : ℝ => (f y : ℂ)) s‖ := by
    rw [hconj, mellin_ofReal_conj, RCLike.norm_conj]
  rw [hG1, div_self hGne, one_mul, hm1, sq]

/-- On the open critical strip `0 < Re s < 1`,
`ξ(s)² R_f(s) = ζ(s) ζ(1−s) 𝓜f(s) 𝓜f(1−s)`. -/
theorem xi_sq_mul_cosDilationCertMultiplier_strip {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1)
    (h0 : mellin (fun y : ℝ => (f y : ℂ)) 1 = 0) :
    xi s ^ 2 * cosDilationCertMultiplier f s =
      riemannZeta s * riemannZeta (1 - s) *
        mellin (fun y : ℝ => (f y : ℂ)) s * mellin (fun y : ℝ => (f y : ℂ)) (1 - s) := by
  have hs_ne1 : s ≠ 1 := by intro h; rw [h] at hs1; simp at hs1
  have h1s_re : 0 < (1 - s).re := by simp; linarith
  have h1s_ne1 : 1 - s ≠ 1 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  have hG : Complex.Gamma ((1 - s) / 2) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hGR : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hs0
  have hGR1 : Complex.Gammaℝ (1 - s) ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos h1s_re
  have hxi_symm : xi s ^ 2 = xi s * xi (1 - s) := by rw [sq, xi_one_sub]
  have harch_div : archXi (1 - s) = archXi s * (Complex.Gammaℝ (1 - s) / Complex.Gammaℝ s) := by
    rw [mul_div_assoc', eq_div_iff hGR]
    unfold archXi; ring
  have harch_prod : archXi s * archXi (1 - s) * cosDilationCertMultiplier f s =
      mellin (fun y : ℝ => (f y : ℂ)) s * mellin (fun y : ℝ => (f y : ℂ)) (1 - s) := by
    have h := archXi_sq_mul_cosDilationCertMultiplier hs0 hs_ne1 hG h0
    calc archXi s * archXi (1 - s) * cosDilationCertMultiplier f s
        = (archXi s ^ 2 * cosDilationCertMultiplier f s) *
            (Complex.Gammaℝ (1 - s) / Complex.Gammaℝ s) := by
          rw [harch_div]; ring
      _ = mellin (fun y : ℝ => (f y : ℂ)) s * mellin (fun y : ℝ => (f y : ℂ)) (1 - s) := by
          rw [h]; field_simp
  rw [hxi_symm, xi_eq_archXi_mul_riemannZeta hs0 hs_ne1,
    xi_eq_archXi_mul_riemannZeta h1s_re h1s_ne1]
  calc archXi s * riemannZeta s * (archXi (1 - s) * riemannZeta (1 - s)) *
        cosDilationCertMultiplier f s
      = riemannZeta s * riemannZeta (1 - s) *
          (archXi s * archXi (1 - s) * cosDilationCertMultiplier f s) := by ring
    _ = riemannZeta s * riemannZeta (1 - s) *
          mellin (fun y : ℝ => (f y : ℂ)) s * mellin (fun y : ℝ => (f y : ℂ)) (1 - s) := by
        rw [harch_prod]; ring

/-- On the critical line `s = ½ + it`,
`ξ(½+it)² R_f(½+it) = ‖ζ(½+it) 𝓜f(½+it)‖²`. -/
theorem xi_sq_mul_cosDilationCertMultiplier_criticalLine
    (h0 : mellin (fun y : ℝ => (f y : ℂ)) 1 = 0) (t : ℝ) :
    xi (1 / 2 + t * I) ^ 2 * cosDilationCertMultiplier f (1 / 2 + t * I) =
      ((‖riemannZeta (1 / 2 + t * I) *
        mellin (fun y : ℝ => (f y : ℂ)) (1 / 2 + t * I)‖ ^ 2 : ℝ) : ℂ) := by
  set s : ℂ := 1 / 2 + t * I with hs_def
  rw [xi_sq_mul_cosDilationCertMultiplier_strip (by simp [s]) (by simp [s]; norm_num) h0]
  have hconj : 1 - s = starRingEnd ℂ s := one_sub_criticalLine_eq_conj t
  rw [hconj, riemannZeta_conj, mellin_ofReal_conj]
  set z : ℂ := riemannZeta s * mellin (fun y : ℝ => (f y : ℂ)) s
  have hz : riemannZeta s * (starRingEnd ℂ) (riemannZeta s) *
      mellin (fun y : ℝ => (f y : ℂ)) s * (starRingEnd ℂ) (mellin (fun y : ℝ => (f y : ℂ)) s) =
      z * starRingEnd ℂ z := by
    simp only [z, map_mul]; ring
  rw [hz, Complex.mul_conj']
  norm_cast

/-- **Exact second-moment identity for blind cosine–dilation cores.**
If `f` is smooth and supported in `[α, β]` (`0 < α ≤ β`) with `𝓜f(1) = 0`, and `Ψ_f(n) = 0` for
every integer `n ≥ 2`, then
`∫ ‖ζ(½+it) 𝓜f(½+it)‖² dt = 2π Ψ_f(1)`. -/
theorem integral_norm_zeta_mul_mellin_sq_eq_cosDilationKernel_one (hf : ContDiff ℝ ∞ f)
    {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (h0 : mellin (fun y : ℝ => (f y : ℂ)) 1 = 0)
    (hblind : ∀ n : ℕ, 2 ≤ n → cosDilationKernel f n = 0) :
    ∫ t : ℝ, ‖riemannZeta (1 / 2 + t * I) *
        mellin (fun y : ℝ => (f y : ℂ)) (1 / 2 + t * I)‖ ^ 2 =
      2 * π * cosDilationKernel f 1 := by
  have hR : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 3 → DifferentiableAt ℂ (cosDilationCertMultiplier f) s :=
    fun s h1 _ => differentiableAt_cosDilationCertMultiplier hf hα hαβ hsupp (by linarith)
  obtain ⟨C, hC⟩ := exists_bound_xi_sq_mul_cosDilationCertMultiplier hf hα hαβ hsupp h0
  obtain ⟨Ca, hCa⟩ := exists_bound_archXi_sq_mul_cosDilationCertMultiplier hf hα hαβ hsupp h0
  have hC' : ∀ t : ℝ, ‖archXi (3 + t * I) ^ 2 * cosDilationCertMultiplier f (3 + t * I)‖ ≤
      Ca / (1 + t ^ 2) := fun t => by
    have h := hCa (3 + t * I) (by simp; norm_num) (by simp)
    simpa using h
  have hvan : ∀ n : ℕ, 2 ≤ n → certKernel (cosDilationCertMultiplier f) n = 0 := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    rw [certKernel_cosDilationCertMultiplier hf hα hαβ hsupp h0 hn0, hblind n hn,
      Complex.ofReal_zero]
  have hint := integral_xi_sq_eq_certKernel_one (cosDilationCertMultiplier f) hR hC hC' hvan
  rw [certKernel_cosDilationCertMultiplier hf hα hαβ hsupp h0 one_pos] at hint
  simp_rw [xi_sq_mul_cosDilationCertMultiplier_criticalLine h0] at hint
  rw [integral_complex_ofReal] at hint
  exact Complex.ofReal_injective (by simpa using hint)

/-- For any blind smooth compact core `f` with `𝓜f(1) = 0`, the central kernel value `Ψ_f(1)` is
nonnegative. -/
theorem cosDilationKernel_one_nonneg_of_blind (hf : ContDiff ℝ ∞ f)
    {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (h0 : mellin (fun y : ℝ => (f y : ℂ)) 1 = 0)
    (hblind : ∀ n : ℕ, 2 ≤ n → cosDilationKernel f n = 0) :
    0 ≤ cosDilationKernel f 1 := by
  have h := integral_norm_zeta_mul_mellin_sq_eq_cosDilationKernel_one hf hα hαβ hsupp h0 hblind
  have hnn : 0 ≤ ∫ t : ℝ, ‖riemannZeta (1 / 2 + t * I) *
      mellin (fun y : ℝ => (f y : ℂ)) (1 / 2 + t * I)‖ ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  rw [h] at hnn
  exact nonneg_of_mul_nonneg_right hnn (by positivity)

/-- **Full-integer blindness rigidity.** If a smooth core `f` supported in `[α, β]` (`0 < α ≤ β`)
with `𝓜f(1) = 0` is blind at `n ≥ 2` and satisfies `Ψ_f(1) ≤ 0`, then `f = 0`. -/
theorem eq_zero_of_cosDilationKernel_blind_of_one_nonpos (hf : ContDiff ℝ ∞ f)
    {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (h0 : mellin (fun y : ℝ => (f y : ℂ)) 1 = 0)
    (hblind : ∀ n : ℕ, 2 ≤ n → cosDilationKernel f n = 0)
    (h1 : cosDilationKernel f 1 ≤ 0) (y : ℝ) : f y = 0 := by
  have hΨ1 : cosDilationKernel f 1 = 0 :=
    le_antisymm h1 (cosDilationKernel_one_nonneg_of_blind hf hα hαβ hsupp h0 hblind)
  have hint0 : ∫ t : ℝ, ‖riemannZeta (1 / 2 + t * I) *
      mellin (fun y : ℝ => (f y : ℂ)) (1 / 2 + t * I)‖ ^ 2 = 0 := by
    rw [integral_norm_zeta_mul_mellin_sq_eq_cosDilationKernel_one hf hα hαβ hsupp h0 hblind,
      hΨ1, mul_zero]
  set g : ℝ → ℝ := fun t => ‖riemannZeta (1 / 2 + t * I) *
    mellin (fun y : ℝ => (f y : ℂ)) (1 / 2 + t * I)‖ ^ 2 with hg_def
  have hgeq : ∀ t : ℝ, g t = ‖xi (1 / 2 + (t : ℂ) * I) ^ 2 *
      cosDilationCertMultiplier f (1 / 2 + (t : ℂ) * I)‖ := by
    intro t
    rw [xi_sq_mul_cosDilationCertMultiplier_criticalLine h0, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hgcont : Continuous g := by
    rw [show g = fun t : ℝ => ‖xi (1 / 2 + (t : ℂ) * I) ^ 2 *
      cosDilationCertMultiplier f (1 / 2 + (t : ℂ) * I)‖ from funext hgeq]
    refine Continuous.norm ?_
    rw [continuous_iff_continuousAt]
    intro t
    have hsre : 0 < ((1 / 2 : ℂ) + t * I).re := by simp
    have hd : DifferentiableAt ℂ (fun s => xi s ^ 2 * cosDilationCertMultiplier f s)
        (1 / 2 + t * I) :=
      ((xi_differentiable _).pow 2).mul
        (differentiableAt_cosDilationCertMultiplier hf hα hαβ hsupp hsre)
    exact ContinuousAt.comp (g := fun s => xi s ^ 2 * cosDilationCertMultiplier f s)
      hd.continuousAt (by fun_prop : ContinuousAt (fun t : ℝ => (1 / 2 : ℂ) + t * I) t)
  obtain ⟨C, hC⟩ := exists_bound_xi_sq_mul_cosDilationCertMultiplier hf hα hαβ hsupp h0
  have hgint : Integrable g := by
    refine (integrable_inv_one_add_sq.const_mul C).mono' hgcont.aestronglyMeasurable
      (Eventually.of_forall fun t => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), hgeq t]
    have h := hC (1 / 2 + t * I) (by simp) (by simp; norm_num)
    simpa [div_eq_mul_inv] using h
  have hgae : g =ᵐ[volume] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _) hgint).mp hint0
  have hg0 : ∀ t : ℝ, g t = 0 :=
    fun t => congrFun ((Continuous.ae_eq_iff_eq volume hgcont continuous_const).mp hgae) t
  -- Now `xi s * mellin f s` vanishes on `Re s = 1/2`, hence on all of `ℂ`.
  have htest := isTest_ofReal_of_support hf hα hαβ hsupp
  set G : ℂ → ℂ := fun s => xi s * mellin (fun y : ℝ => (f y : ℂ)) s with hG_def
  have hGd : Differentiable ℂ G := fun s =>
    (xi_differentiable s).mul (htest.differentiableAt_mellin s)
  have hGa : AnalyticOnNhd ℂ G univ :=
    hGd.differentiableOn.analyticOnNhd isOpen_univ
  have hGline : ∀ t : ℝ, G (1 / 2 + t * I) = 0 := by
    intro t
    have hgt := hg0 t
    simp only [hg_def, sq_eq_zero_iff, norm_eq_zero] at hgt
    have hsre : 0 < ((1 / 2 : ℂ) + t * I).re := by simp
    have hs1 : (1 / 2 : ℂ) + t * I ≠ 1 := by
      intro h; have := congrArg Complex.re h; simp at this
    simp only [hG_def, xi_eq_archXi_mul_riemannZeta hsre hs1, mul_assoc, hgt, mul_zero]
  have hGuniv : EqOn G 0 univ := by
    refine hGa.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ
      (mem_univ (1 / 2 : ℂ)) ?_
    have ht : Tendsto (fun k : ℕ => (1 / 2 : ℂ) + ((1 / ((k : ℝ) + 1) : ℝ) : ℂ) * I)
        atTop (𝓝[≠] (1 / 2 : ℂ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun k => ?_⟩
      · have h := (Complex.continuous_ofReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
        have h2 := (h.mul_const I).const_add (1 / 2 : ℂ)
        simpa using h2
      · simp only [mem_compl_iff, mem_singleton_iff]
        intro h
        have h0' : ((1 / ((k : ℝ) + 1) : ℝ) : ℂ) * I = 0 := by linear_combination h
        have hne : (1 / ((k : ℝ) + 1) : ℝ) ≠ 0 := by positivity
        exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hne) I_ne_zero h0'
    exact ht.frequently (Frequently.of_forall fun k => hGline _)
  -- Hence `mellin f` vanishes on `(1, ∞)`, so everywhere on `ℂ`.
  set M : ℂ → ℂ := mellin (fun y : ℝ => (f y : ℂ)) with hM_def
  have hMd : Differentiable ℂ M := fun s => htest.differentiableAt_mellin s
  have hMa : AnalyticOnNhd ℂ M univ :=
    hMd.differentiableOn.analyticOnNhd isOpen_univ
  have hMray : ∀ x : ℝ, 1 < x → M x = 0 := by
    intro x hx
    have hGx : G x = 0 := hGuniv (mem_univ (x : ℂ))
    have hxre : 1 < (x : ℂ).re := by simpa using hx
    have hx0 : 0 < (x : ℂ).re := by linarith
    have hx1 : (x : ℂ) ≠ 1 := by intro h; have := congrArg Complex.re h; simp at this; linarith
    have hzeta : riemannZeta (x : ℂ) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hxre
    have harch : archXi (x : ℂ) ≠ 0 := by
      unfold archXi
      refine mul_ne_zero (div_ne_zero (mul_ne_zero ?_ (sub_ne_zero.mpr hx1)) two_ne_zero)
        (Complex.Gammaℝ_ne_zero_of_re_pos hx0)
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have hxi : xi (x : ℂ) ≠ 0 := by
      rw [xi_eq_archXi_mul_riemannZeta hx0 hx1]
      exact mul_ne_zero harch hzeta
    exact (mul_eq_zero.mp hGx).resolve_left hxi
  have hMuniv : EqOn M 0 univ := by
    refine hMa.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ
      (mem_univ (2 : ℂ)) ?_
    have ht : Tendsto (fun k : ℕ => ((2 + 1 / ((k : ℝ) + 1) : ℝ) : ℂ))
        atTop (𝓝[≠] (2 : ℂ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun k => ?_⟩
      · have h := tendsto_one_div_add_atTop_nhds_zero_nat.const_add (2 : ℝ)
        rw [add_zero] at h
        exact (Complex.continuous_ofReal.tendsto 2).comp h
      · simp only [mem_compl_iff, mem_singleton_iff]
        intro h
        have h' := Complex.ofReal_injective h
        have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
        linarith
    exact ht.frequently (Frequently.of_forall fun k => hMray _ (by
      have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      linarith))
  exact eq_zero_of_mellin_criticalLine_eq_zero hf hα hαβ hsupp
    (fun t => hMuniv (mem_univ _)) y

/-- No nonzero smooth core `f` supported in `[α, β]` (`0 < α ≤ β`) with `𝓜f(1) = 0` can have
`Ψ_f(n) = 0` for all positive integers `n ≥ 1`. -/
theorem eq_zero_of_cosDilationKernel_nat_eq_zero (hf : ContDiff ℝ ∞ f)
    {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (h0 : mellin (fun y : ℝ => (f y : ℂ)) 1 = 0)
    (hblind : ∀ n : ℕ, 1 ≤ n → cosDilationKernel f n = 0) (y : ℝ) : f y = 0 :=
  eq_zero_of_cosDilationKernel_blind_of_one_nonpos hf hα hαβ hsupp h0
    (fun n hn => hblind n (by omega)) (by simpa using (hblind 1 le_rfl).le) y

/-- **Critical log-room rigidity for smooth cosine–dilation cores.**
If `f` is smooth and supported in `[α, β]` (`0 < α ≤ β`) with `𝓜f(1) = 0`, `Ψ_f(n) = 0` for all
`n ≥ 2`, and `‖𝓜f(½+it)‖²` is integrable against `logRoomWeight (π / 2)`, then `f = 0`. -/
theorem eq_zero_of_cosDilationKernel_blind_of_mellin_logRoom (hf : ContDiff ℝ ∞ f)
    {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (h0 : mellin (fun y : ℝ => (f y : ℂ)) 1 = 0)
    (hroom : Integrable fun t : ℝ =>
      ‖mellin (fun y : ℝ => (f y : ℂ)) (1 / 2 + t * I)‖ ^ 2 * logRoomWeight (π / 2) t)
    (hblind : ∀ n : ℕ, 2 ≤ n → cosDilationKernel f n = 0) (y : ℝ) : f y = 0 := by
  have hR : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 3 → DifferentiableAt ℂ (cosDilationCertMultiplier f) s :=
    fun s h1 _ => differentiableAt_cosDilationCertMultiplier hf hα hαβ hsupp (by linarith)
  obtain ⟨C, hC⟩ := exists_bound_xi_sq_mul_cosDilationCertMultiplier hf hα hαβ hsupp h0
  obtain ⟨Ca, hCa⟩ := exists_bound_archXi_sq_mul_cosDilationCertMultiplier hf hα hαβ hsupp h0
  have hroom' : Integrable fun t : ℝ =>
      ‖archXi (1 / 2 + t * I) ^ 2 * cosDilationCertMultiplier f (1 / 2 + t * I)‖ *
        logRoomWeight (π / 2) t := by
    refine hroom.congr (Eventually.of_forall fun t => ?_)
    dsimp only
    rw [norm_archXi_sq_mul_cosDilationCertMultiplier_criticalLine h0 t]
  have hblind' := (logNode_blind_iff_cosDilationKernel_vanishes hf hα hαβ hsupp h0).mpr hblind
  have hint0 := integral_xi_sq_eq_zero_of_logNode_blind_of_logRoom
    (cosDilationCertMultiplier f) hR hC hCa hroom' hblind'
  simp_rw [xi_sq_mul_cosDilationCertMultiplier_criticalLine h0] at hint0
  rw [integral_complex_ofReal] at hint0
  have hint_real : ∫ t : ℝ, ‖riemannZeta (1 / 2 + t * I) *
      mellin (fun y : ℝ => (f y : ℂ)) (1 / 2 + t * I)‖ ^ 2 = 0 :=
    Complex.ofReal_injective (by simpa using hint0)
  rw [integral_norm_zeta_mul_mellin_sq_eq_cosDilationKernel_one hf hα hαβ hsupp h0 hblind]
    at hint_real
  have hΨ1 : cosDilationKernel f 1 ≤ 0 := by
    have : cosDilationKernel f 1 = 0 :=
      (mul_eq_zero.mp hint_real).resolve_left (by positivity)
    linarith
  exact eq_zero_of_cosDilationKernel_blind_of_one_nonpos hf hα hαβ hsupp h0 hblind hΨ1 y

end

end RHTower
