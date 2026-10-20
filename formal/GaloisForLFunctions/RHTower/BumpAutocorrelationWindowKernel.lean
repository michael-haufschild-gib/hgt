import GaloisForLFunctions.RHTower.ImaginaryShiftQuadraticFourierDefect
import GaloisForLFunctions.RHTower.LittlewoodShortWindowZeroCount
import GaloisForLFunctions.RHTower.RiemannKernelStripPlancherel

/-!
# The bump window kernel and its transform

Let `Φ_ℓ(u) = Φ(u/ℓ)` be the scaled smooth bump (`cb ℓ 0`, supported in `[−ℓ, ℓ]`, `ℓ > 0`) and
`K_ℓ = Φ_ℓ ⋆ Φ̃_ℓ` its autocorrelation (`bumpAutocorrelation`), `K_ℓ(x) = ∫ Φ_ℓ(t) Φ_ℓ(t − x) dt`.

* `K_ℓ` is smooth, real, even and supported in `[−2ℓ, 2ℓ]`; it is nonnegative and at least
  `ℓ c₀/2` on `[−ℓ/2, ℓ/2]`, with `c₀ = ϑ(7/16)²` (`bumpAutocorrelation_re_ge`).
* On the real line `K̂_ℓ(y) = |Φ̂_ℓ(y)|² = ψ_ℓ(y)` (`psi ℓ 0`), with derivative
  `ψ_ℓ' = Re (iuK_ℓ)^` (`hasDerivAt_psi_zero`); both decay like `(1 + |y|)⁻⁴`.
* **Scaling.** `Φ̂_ℓ(y) = ℓ Φ̂_1(ℓy)`, hence `ψ_ℓ(y) = ℓ² ψ_1(ℓy)`, `ψ_ℓ'(y) = ℓ³ ψ_1'(ℓy)` and
  `∫ |ψ_ℓ'| = ℓ² ∫ |ψ_1'|` (`integral_abs_psiDeriv_eq`).
-/

open Complex MeasureTheory Real Set Filter Topology

noncomputable section

namespace RHTower.Littlewood

open Zeta23

/-! ### The kernel -/

/-- The autocorrelation `K_ℓ = Φ_ℓ ⋆ Φ̃_ℓ` of the scaled bump. -/
def bumpAutocorrelation (ℓ : ℝ) : ℝ → ℂ := EF.weilTest (cb ℓ 0) (cb ℓ 0)

/-- The real autocorrelation `∫ Φ_ℓ(t) Φ_ℓ(t − x) dt`. -/
def bumpAutocorrelationReal (ℓ x : ℝ) : ℝ := ∫ t : ℝ, sc ℓ 0 t * sc ℓ 0 (t - x)

theorem bumpAutocorrelation_eq (ℓ x : ℝ) : bumpAutocorrelation ℓ x = (bumpAutocorrelationReal ℓ x : ℂ) := by
  rw [bumpAutocorrelation, EF.weilTest, MeasureTheory.convolution_def, bumpAutocorrelationReal, ← integral_complex_ofReal]
  congr 1 with t
  simp only [ContinuousLinearMap.mul_apply', EF.tilde, cb, Complex.conj_ofReal, neg_sub,
    Complex.ofReal_mul]

theorem bumpAutocorrelation_re (ℓ x : ℝ) : (bumpAutocorrelation ℓ x).re = bumpAutocorrelationReal ℓ x := by
  rw [bumpAutocorrelation_eq, Complex.ofReal_re]

theorem bumpAutocorrelation_im (ℓ x : ℝ) : (bumpAutocorrelation ℓ x).im = 0 := by
  rw [bumpAutocorrelation_eq, Complex.ofReal_im]

theorem bumpAutocorrelationReal_neg (ℓ x : ℝ) : bumpAutocorrelationReal ℓ (-x) = bumpAutocorrelationReal ℓ x := by
  unfold bumpAutocorrelationReal
  calc ∫ t : ℝ, sc ℓ 0 t * sc ℓ 0 (t - -x)
      = ∫ t : ℝ, (fun s => sc ℓ 0 (s - x) * sc ℓ 0 s) (t + x) := by
        congr 1 with t; simp only [sub_neg_eq_add, add_sub_cancel_right]
    _ = ∫ t : ℝ, sc ℓ 0 (t - x) * sc ℓ 0 t :=
        integral_add_right_eq_self (μ := volume) (fun s => sc ℓ 0 (s - x) * sc ℓ 0 s) x
    _ = ∫ t : ℝ, sc ℓ 0 t * sc ℓ 0 (t - x) := by congr 1 with t; ring

theorem bumpAutocorrelation_neg (ℓ x : ℝ) : bumpAutocorrelation ℓ (-x) = bumpAutocorrelation ℓ x := by
  rw [bumpAutocorrelation_eq, bumpAutocorrelation_eq, bumpAutocorrelationReal_neg]

section Pos

variable {ℓ : ℝ} (hℓ : 0 < ℓ)
include hℓ

theorem tsupport_cb_subset : tsupport (cb ℓ 0) ⊆ Icc (-(2 * ℓ / 2)) (2 * ℓ / 2) := by
  rw [show 2 * ℓ / 2 = ℓ by ring]
  refine closure_minimal (fun u hu => ?_) isClosed_Icc
  exact abs_le.mp (cb_support hℓ 0 u hu)

theorem bumpAutocorrelation_support (u : ℝ) (hu : bumpAutocorrelation ℓ u ≠ 0) : |u| ≤ 2 * ℓ := by
  have h := EF.tsupport_weilTest_subset (tsupport_cb_subset hℓ) (tsupport_cb_subset hℓ)
  exact abs_le.mpr (h (subset_tsupport _ hu))

theorem hasCompactSupport_bumpKernel : HasCompactSupport (bumpAutocorrelation ℓ) :=
  hasCompactSupport_of_support_subset_abs (bumpAutocorrelation_support hℓ)

theorem bumpAutocorrelation_contDiff {n : ℕ∞} : ContDiff ℝ n (bumpAutocorrelation ℓ) := by
  have h := (hasCompactSupport_cb hℓ 0).contDiff_convolution_left (n := n)
    (L := ContinuousLinearMap.mul ℝ ℂ) (μ := volume) (contDiff_cb ℓ 0)
    (EF.continuous_tilde (contDiff_cb ℓ 0 (n := 0)).continuous).locallyIntegrable
  simpa [bumpAutocorrelation, EF.weilTest] using h

theorem bumpAutocorrelation_continuous : Continuous (bumpAutocorrelation ℓ) :=
  (bumpAutocorrelation_contDiff hℓ (n := 0)).continuous

/-- On the real line the transform of `K_ℓ` is `ψ_ℓ = |Φ̂_ℓ|²`. -/
theorem paperFT_bumpKernel_ofReal (y : ℝ) :
    paperFT (bumpAutocorrelation ℓ) y = (psi ℓ 0 y : ℂ) := by
  have hc := (contDiff_cb ℓ 0 (n := 0)).continuous
  rw [bumpAutocorrelation, EF.paperFT_weilTest hc hc (hasCompactSupport_cb hℓ 0) (hasCompactSupport_cb hℓ 0),
    Complex.conj_ofReal, Complex.mul_conj, psi, Complex.normSq_eq_norm_sq]

theorem psi_eq_re_paperFT (y : ℝ) : psi ℓ 0 y = (paperFT (bumpAutocorrelation ℓ) y).re := by
  rw [paperFT_bumpKernel_ofReal hℓ, Complex.ofReal_re]

/-- The first moment kernel `u ↦ iuK_ℓ(u)`. -/
def bumpMomentKernel (ℓ : ℝ) (u : ℝ) : ℂ := I * u * bumpAutocorrelation ℓ u

omit hℓ in
theorem bumpMomentKernel_contDiff' (hℓ : 0 < ℓ) {n : ℕ∞} : ContDiff ℝ n (bumpMomentKernel ℓ) := by
  unfold bumpMomentKernel
  exact (contDiff_const.mul Complex.ofRealCLM.contDiff).mul (bumpAutocorrelation_contDiff hℓ)

theorem bumpMomentKernel_support (u : ℝ) (hu : bumpMomentKernel ℓ u ≠ 0) : |u| ≤ 2 * ℓ :=
  bumpAutocorrelation_support hℓ u (fun h => hu (by simp [bumpMomentKernel, h]))

/-- The derivative `ψ_ℓ' = Re (iuK_ℓ)^`. -/
def psiDeriv (ℓ y : ℝ) : ℝ := (paperFT (bumpMomentKernel ℓ) y).re

theorem hasDerivAt_psi_zero (y : ℝ) : HasDerivAt (psi ℓ 0) (psiDeriv ℓ y) y := by
  have hKc := hasCompactSupport_bumpKernel hℓ
  have hK := bumpAutocorrelation_continuous hℓ
  have h1 : Integrable (bumpAutocorrelation ℓ) := hK.integrable_of_hasCompactSupport hKc
  have h2 : Integrable fun u : ℝ => (u : ℂ) * bumpAutocorrelation ℓ u :=
    (by fun_prop : Continuous fun u : ℝ => (u : ℂ) * bumpAutocorrelation ℓ u).integrable_of_hasCompactSupport
      hKc.mul_left
  have hd := RHTower.KernelStrip.hasDerivAt_paperFT h1 h2 y
  have hre := (Complex.reCLM.hasFDerivAt (x := paperFT (bumpAutocorrelation ℓ) y)).comp_hasDerivAt y hd
  have hfun : psi ℓ 0 = (Complex.reCLM ∘ fun x : ℝ => paperFT (bumpAutocorrelation ℓ) x) := by
    funext x; simp [psi_eq_re_paperFT hℓ]
  rw [hfun]
  exact hre

/-- **Decay.** `|ψ_ℓ(y)| (1 + |y|)⁴` and `|ψ_ℓ'(y)| (1 + |y|)⁴` are bounded. -/
theorem exists_abs_psi_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ,
    |psi ℓ 0 y| * (1 + |y|) ^ 4 ≤ C ∧ |psiDeriv ℓ y| * (1 + |y|) ^ 4 ≤ C := by
  set C₁ := 2 ^ 4 * Real.exp (|(0 : ℝ)| * (2 * ℓ)) * ((∫ u, ‖bumpAutocorrelation ℓ u‖) +
    ∫ u, ‖iteratedDeriv 4 (bumpAutocorrelation ℓ) u‖) with hC₁
  set C₂ := 2 ^ 4 * Real.exp (|(0 : ℝ)| * (2 * ℓ)) * ((∫ u, ‖bumpMomentKernel ℓ u‖) +
    ∫ u, ‖iteratedDeriv 4 (bumpMomentKernel ℓ) u‖) with hC₂
  refine ⟨max C₁ C₂, ?_, fun y => ⟨?_, ?_⟩⟩
  · exact le_max_of_le_left (by rw [hC₁]; positivity)
  · have h := norm_paperFT_mul_one_add_pow_le (bumpAutocorrelation_contDiff hℓ (n := 4))
      (bumpAutocorrelation_support hℓ) (y : ℂ)
    simp only [Complex.ofReal_re, Complex.ofReal_im] at h
    rw [psi_eq_re_paperFT hℓ]
    exact (mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm _) (by positivity)).trans
      (h.trans (le_max_left _ _))
  · have h := norm_paperFT_mul_one_add_pow_le (bumpMomentKernel_contDiff' hℓ (n := 4))
      (bumpMomentKernel_support hℓ) (y : ℂ)
    simp only [Complex.ofReal_re, Complex.ofReal_im] at h
    exact (mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm _) (by positivity)).trans
      (h.trans (le_max_right _ _))

end Pos

/-! ### Scaling -/

theorem paperFT_cb_scale {ℓ : ℝ} (hℓ : 0 < ℓ) (y : ℝ) :
    paperFT (cb ℓ 0) y = ℓ * paperFT (cb 1 0) (ℓ * y) := by
  rw [paperFT_def, paperFT_def]
  have h := Measure.integral_comp_mul_left
    (fun u : ℝ => cb ℓ 0 u * cexp (I * (y : ℂ) * u)) ℓ
  rw [abs_inv, abs_of_pos hℓ, Complex.real_smul] at h
  have hg : ∀ x : ℝ, cb ℓ 0 (ℓ * x) * cexp (I * (y : ℂ) * ↑(ℓ * x)) =
      cb 1 0 x * cexp (I * ((ℓ : ℂ) * y) * x) := by
    intro x
    simp only [cb, sc_zero, mul_div_cancel_left₀ x hℓ.ne', div_one, Complex.ofReal_mul]
    ring_nf
  simp only [hg] at h
  rw [h, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hℓ.ne', Complex.ofReal_one, one_mul]

theorem psi_scale {ℓ : ℝ} (hℓ : 0 < ℓ) (y : ℝ) : psi ℓ 0 y = ℓ ^ 2 * psi 1 0 (ℓ * y) := by
  simp only [psi]
  rw [paperFT_cb_scale hℓ, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hℓ]
  push_cast
  ring

theorem psiDeriv_scale {ℓ : ℝ} (hℓ : 0 < ℓ) (y : ℝ) :
    psiDeriv ℓ y = ℓ ^ 3 * psiDeriv 1 (ℓ * y) := by
  have h1 := hasDerivAt_psi_zero hℓ y
  have h2 : HasDerivAt (fun y => ℓ ^ 2 * psi 1 0 (ℓ * y)) (ℓ ^ 2 * (psiDeriv 1 (ℓ * y) * ℓ)) y :=
    ((hasDerivAt_psi_zero one_pos (ℓ * y)).comp y
      ((hasDerivAt_id y).const_mul ℓ |>.congr_deriv (by ring))).const_mul (ℓ ^ 2)
  have hfun : psi ℓ 0 = fun y => ℓ ^ 2 * psi 1 0 (ℓ * y) := funext (psi_scale hℓ)
  rw [hfun] at h1
  rw [h1.unique h2]
  ring

/-- `∫ |ψ_ℓ'| = ℓ² ∫ |ψ_1'|`. -/
theorem integral_abs_psiDeriv_eq {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ∫ y, |psiDeriv ℓ y| = ℓ ^ 2 * ∫ y, |psiDeriv 1 y| := by
  simp_rw [psiDeriv_scale hℓ, abs_mul, abs_of_pos (pow_pos hℓ 3)]
  rw [integral_const_mul, Measure.integral_comp_mul_left (fun y => |psiDeriv 1 y|) ℓ,
    abs_inv, abs_of_pos hℓ, smul_eq_mul]
  field_simp

/-! ### Positivity of the kernel -/

theorem sc_zero_nonneg (ℓ u : ℝ) : 0 ≤ sc ℓ 0 u := by
  rw [sc_zero]; exact bump_nonneg _

theorem bumpAutocorrelationReal_nonneg (ℓ x : ℝ) : 0 ≤ bumpAutocorrelationReal ℓ x :=
  integral_nonneg fun t => mul_nonneg (sc_zero_nonneg ℓ t) (sc_zero_nonneg ℓ _)

theorem bump_ge_of_abs_le {v : ℝ} (hv : |v| ≤ 3 / 4) :
    Real.smoothTransition (7 / 16) ≤ bump v := by
  rw [bump]
  apply Real.smoothTransition.monotone
  have : v ^ 2 ≤ (3 / 4) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg v) hv 2
  linarith

/-- **Lower bound.** `K_ℓ(x) ≥ (ℓ/2) ϑ(7/16)²` for `|x| ≤ ℓ/2`. -/
theorem bumpAutocorrelationReal_ge {ℓ : ℝ} (hℓ : 0 < ℓ) {x : ℝ} (hx : |x| ≤ ℓ / 2) :
    ℓ / 2 * Real.smoothTransition (7 / 16) ^ 2 ≤ bumpAutocorrelationReal ℓ x := by
  set c := Real.smoothTransition (7 / 16) with hc
  have hc0 : 0 ≤ c := Real.smoothTransition.nonneg _
  have hb : Continuous bump := (contDiff_bump (n := 0)).continuous
  have hcont : Continuous fun t : ℝ => sc ℓ 0 t * sc ℓ 0 (t - x) := by
    simp only [sc_zero]; fun_prop
  have hint : Integrable fun t : ℝ => sc ℓ 0 t * sc ℓ 0 (t - x) := by
    refine hcont.integrable_of_hasCompactSupport (HasCompactSupport.mul_right ?_)
    refine hasCompactSupport_of_support_subset_abs (Λ := ℓ) fun u hu => cb_support hℓ 0 u ?_
    simpa [cb] using hu
  have hset : ∫ t in Icc (-(ℓ / 4)) (ℓ / 4), c * c ≤
      ∫ t in Icc (-(ℓ / 4)) (ℓ / 4), sc ℓ 0 t * sc ℓ 0 (t - x) := by
    refine setIntegral_mono_on continuous_const.integrableOn_Icc hint.integrableOn
      measurableSet_Icc fun t ht => ?_
    have ht' : |t| ≤ ℓ / 4 := abs_le.mpr ht
    have h1 : c ≤ sc ℓ 0 t := by
      rw [sc_zero]; apply bump_ge_of_abs_le
      rw [abs_div, abs_of_pos hℓ, div_le_iff₀ hℓ]; linarith
    have h2 : c ≤ sc ℓ 0 (t - x) := by
      rw [sc_zero]; apply bump_ge_of_abs_le
      rw [abs_div, abs_of_pos hℓ, div_le_iff₀ hℓ]
      linarith [abs_sub t x]
    exact mul_le_mul h1 h2 hc0 (sc_zero_nonneg ℓ t)
  have hle : ∫ t in Icc (-(ℓ / 4)) (ℓ / 4), sc ℓ 0 t * sc ℓ 0 (t - x) ≤ bumpAutocorrelationReal ℓ x :=
    setIntegral_le_integral hint (Eventually.of_forall fun t =>
      mul_nonneg (sc_zero_nonneg ℓ t) (sc_zero_nonneg ℓ _))
  rw [setIntegral_const, Measure.real, Real.volume_Icc, smul_eq_mul] at hset
  rw [ENNReal.toReal_ofReal (by linarith)] at hset
  nlinarith

end RHTower.Littlewood
