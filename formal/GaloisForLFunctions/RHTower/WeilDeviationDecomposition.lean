import GaloisForLFunctions.RHTower.WeilDeviationFejerTest
import GaloisForLFunctions.RHTower.XiRealDivisorSampling

/-!
# Decomposition tools for the excess rigidity argument

- **Finite zero windows** (`finite_riemannXi_zeros`). `Ξ` has finitely many real zeros in every
  window.
- **Division by `Ξ²`** (`contDiff_div_riemannXi_sq`). A smooth, compactly supported `R` that vanishes
  near every zero of `Ξ` is `Ξ² g` for a smooth, compactly supported `g`.
- **Splitting the pairing** into the excess part, which is bounded by `‖e‖₁` times a sup norm, and
  the deficit part.
- **The tail** (`tendsto_deviationPairing_tail`). If `𝓕Φ` is compactly supported, the pairing with
  `𝓕(Φ(1 − χ(·/Γ)))` tends to `0` as `Γ → ∞`. The tail tends to `0` pointwise, by dominated
  convergence on the frequency side. It is dominated uniformly by `C/(1 + u²)`, since
  `𝓕(Φχ(·/Γ))(u) = ∫ 𝓕Φ(u − y/Γ) 𝓕χ(y) dy` and `𝓕χ` decays like `(1 + y²)^{−2}`.
-/

open Complex MeasureTheory Filter Topology Set FourierTransform
open scoped Real ComplexConjugate ContDiff Convolution

namespace RHTower.WeilExcess

noncomputable section

/-! ## Finite zero windows -/

theorem finite_riemannXi_zeros (R : ℝ) :
    {ξ : ℝ | |ξ| ≤ R ∧ riemannXi ξ = 0}.Finite := by
  have h := locallyFiniteSamples_xiRealDivisor (2 * π * R)
  refine (h.image fun t => t / (2 * π)).subset ?_
  rintro ξ ⟨hξR, hξ0⟩
  refine ⟨2 * π * ξ, ⟨?_, ?_⟩, by field_simp⟩
  · show XiC ((2 * π * ξ : ℝ) : ℂ) = 0
    rw [← riemannXi_eq_zero_iff]; exact hξ0
  · rw [mem_Icc]
    have hπ := Real.pi_pos
    have := abs_le.mp hξR
    constructor <;> nlinarith

/-! ## Division by `Ξ²` -/

/-- The quotient `R/Ξ²`, extended by `0` at the zeros of `Ξ`. -/
def divRiemannXiSq (R : ℝ → ℂ) (ξ : ℝ) : ℂ := R ξ / riemannXi ξ ^ 2

theorem riemannXi_sq_mul_divRiemannXiSq {R : ℝ → ℂ}
    (hR : ∀ ξ, riemannXi ξ = 0 → R ξ = 0) (ξ : ℝ) :
    riemannXi ξ ^ 2 * divRiemannXiSq R ξ = R ξ := by
  unfold divRiemannXiSq
  by_cases h : riemannXi ξ = 0
  · rw [h, hR ξ h]; simp
  · field_simp

theorem contDiff_divRiemannXiSq {R : ℝ → ℂ} (hRs : ContDiff ℝ ∞ R)
    (hR : ∀ ξ, riemannXi ξ = 0 → R =ᶠ[𝓝 ξ] 0) : ContDiff ℝ ∞ (divRiemannXiSq R) := by
  rw [contDiff_iff_contDiffAt]
  intro ξ
  by_cases h : riemannXi ξ = 0
  · have hev : divRiemannXiSq R =ᶠ[𝓝 ξ] fun _ => (0 : ℂ) := by
      filter_upwards [hR ξ h] with x hx
      simp [divRiemannXiSq, hx]
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · have h1 : ContDiffAt ℝ ∞ (fun x => (riemannXi x ^ 2)⁻¹) ξ :=
      ((contDiff_riemannXi.pow 2).contDiffAt).inv (pow_ne_zero 2 h)
    have h2 := hRs.contDiffAt.mul h1
    refine h2.congr_of_eventuallyEq (Eventually.of_forall fun x => ?_)
    simp [divRiemannXiSq, div_eq_mul_inv]

theorem hasCompactSupport_divRiemannXiSq {R : ℝ → ℂ} (hRc : HasCompactSupport R) :
    HasCompactSupport (divRiemannXiSq R) := by
  refine hRc.mono' fun ξ hξ => subset_tsupport _ ?_
  rw [Function.mem_support] at hξ ⊢
  intro h0; apply hξ; simp [divRiemannXiSq, h0]

/-! ## Splitting the pairing -/

theorem summable_excess_pairing {lam : ℕ → ℝ} (hexc : Summable (deviationExcess lam))
    {φ : ℝ → ℂ} {B : ℝ} (hφ : ∀ u, ‖φ u‖ ≤ B) :
    Summable (fun n : ℕ => (deviationExcess lam n : ℂ) * (φ (Real.log n) + φ (-Real.log n))) ∧
      ‖weightPairing (deviationExcess lam) φ‖ ≤ 2 * B * ∑' n, deviationExcess lam n := by
  have hb : ∀ n : ℕ, ‖(deviationExcess lam n : ℂ) * (φ (Real.log n) + φ (-Real.log n))‖ ≤
      deviationExcess lam n * (2 * B) := by
    intro n
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (deviationExcess_nonneg lam n)]
    have h1 := hφ (Real.log n)
    have h2 := hφ (-Real.log n)
    have h3 : ‖φ (Real.log n) + φ (-Real.log n)‖ ≤ 2 * B :=
      (norm_add_le _ _).trans (by linarith)
    exact mul_le_mul_of_nonneg_left h3 (deviationExcess_nonneg lam n)
  have hs := Summable.of_norm_bounded (hexc.mul_right (2 * B)) hb
  refine ⟨hs, ?_⟩
  unfold weightPairing
  calc _ ≤ ∑' n, deviationExcess lam n * (2 * B) := tsum_of_norm_bounded
        (hexc.mul_right (2 * B)).hasSum hb
    _ = 2 * B * ∑' n, deviationExcess lam n := by rw [tsum_mul_right]; ring

theorem deviationPairing_eq_sub {lam : ℕ → ℝ} {φ : ℝ → ℂ}
    (he : Summable (fun n : ℕ => (deviationExcess lam n : ℂ) * (φ (Real.log n) + φ (-Real.log n))))
    (hv : Summable (fun n : ℕ => (deviationDeficit lam n : ℂ) * (φ (Real.log n) + φ (-Real.log n)))) :
    deviationPairing lam φ = weightPairing (deviationExcess lam) φ -
      weightPairing (deviationDeficit lam) φ := by
  unfold deviationPairing weightPairing
  rw [← Summable.tsum_sub he hv]
  refine tsum_congr fun n => ?_
  rw [weilDeviation_eq_sub]; push_cast; ring

/-! ## The tail -/

/-- The complex cutoff `χ`, equal to `1` on `[−1, 1]` and supported in `[−2, 2]`. -/
def cutoffC (x : ℝ) : ℂ := ((excessFlatBump x : ℝ) : ℂ)

theorem contDiff_cutoffC : ContDiff ℝ ∞ cutoffC := ofRealCLM.contDiff.comp excessFlatBump.contDiff

theorem hasCompactSupport_cutoffC : HasCompactSupport cutoffC :=
  excessFlatBump.hasCompactSupport.comp_left Complex.ofReal_zero

theorem integrable_cutoffC : Integrable cutoffC :=
  contDiff_cutoffC.continuous.integrable_of_hasCompactSupport hasCompactSupport_cutoffC

theorem norm_cutoffC_le (x : ℝ) : ‖cutoffC x‖ ≤ 1 := by
  rw [cutoffC, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg excessFlatBump.nonneg]
  exact excessFlatBump.le_one

theorem cutoffC_zero : cutoffC 0 = 1 := by
  rw [cutoffC, excessFlatBump_eq_one (by simp)]; simp

theorem norm_one_sub_cutoffC_le (x : ℝ) : ‖1 - cutoffC x‖ ≤ 1 := by
  rw [cutoffC, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by linarith [excessFlatBump.le_one (x := x)])]
  linarith [excessFlatBump.nonneg (x := x)]

/-- A decay bound `(1 + y²)² ‖𝓕χ(y)‖ ≤ C` for the cutoff. -/
theorem exists_fourier_cutoffC_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y, ‖𝓕 cutoffC y‖ ≤ C / (1 + y ^ 2) ^ 2 := by
  obtain ⟨C₀, hC₀, h₀⟩ := GaloisForLFunctions.HTGeometry.exists_pow_mul_norm_fourierIntegral_le
    hasCompactSupport_cutoffC contDiff_cutoffC 0
  obtain ⟨C₄, hC₄, h₄⟩ := GaloisForLFunctions.HTGeometry.exists_pow_mul_norm_fourierIntegral_le
    hasCompactSupport_cutoffC contDiff_cutoffC 4
  refine ⟨2 * (C₀ + C₄), by positivity, fun y => ?_⟩
  rw [le_div_iff₀ (by positivity)]
  have a := h₀ y
  have b := h₄ y
  rw [pow_zero, one_mul] at a
  have hy4 : |y| ^ 4 = (y ^ 2) ^ 2 := by rw [← sq_abs y]; ring
  rw [hy4] at b
  have hN := norm_nonneg (𝓕 cutoffC y)
  have hsq : (1 + y ^ 2) ^ 2 ≤ 2 * (1 + (y ^ 2) ^ 2) := by nlinarith [sq_nonneg (y ^ 2 - 1)]
  calc ‖𝓕 cutoffC y‖ * (1 + y ^ 2) ^ 2 ≤ ‖𝓕 cutoffC y‖ * (2 * (1 + (y ^ 2) ^ 2)) :=
        mul_le_mul_of_nonneg_left hsq hN
    _ = 2 * (‖𝓕 cutoffC y‖ + (y ^ 2) ^ 2 * ‖𝓕 cutoffC y‖) := by ring
    _ ≤ 2 * (C₀ + C₄) := by linarith

theorem integrable_fourier_cutoffC : Integrable (𝓕 cutoffC) :=
  integrable_fourier_smooth contDiff_cutoffC hasCompactSupport_cutoffC

/-- The integral of `𝓕χ` is `χ(0) = 1`. -/
theorem integral_fourier_cutoffC : ∫ y, 𝓕 cutoffC y = 1 := by
  have h := eq_integral_fourier contDiff_cutoffC.continuous integrable_cutoffC
    integrable_fourier_cutoffC 0
  rw [cutoffC_zero] at h
  rw [h]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp

/-- The convolution form of a cut-off transform: `𝓕(Φ χ(·/Γ))(u) = ∫ 𝓕Φ(u − y/Γ) 𝓕χ(y) dy`. -/
theorem fourier_mul_cutoff_eq {Φ : ℝ → ℂ} (hΦc : Continuous Φ) (hΦi : Integrable Φ)
    (hFΦ : Integrable (𝓕 Φ)) {Γ : ℝ} (hΓ : 0 < Γ) (u : ℝ) :
    𝓕 (fun ξ => Φ ξ * packet cutoffC 0 Γ ξ) u = ∫ y, 𝓕 Φ (u - y / Γ) * 𝓕 cutoffC y := by
  rw [fourier_mul_eq_integral hΦc hΦi hFΦ (integrable_packet integrable_cutoffC 0 hΓ)]
  have h1 : (∫ s, 𝓕 Φ s * 𝓕 (packet cutoffC 0 Γ) (u - s)) =
      ∫ x, 𝓕 Φ (u - x) * ((Γ : ℂ) * 𝓕 cutoffC (Γ * x)) := by
    rw [← integral_sub_left_eq_self (μ := volume)
      (fun s => 𝓕 Φ s * 𝓕 (packet cutoffC 0 Γ) (u - s)) u]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [sub_sub_cancel, fourier_packet cutoffC 0 hΓ]
    simp
  rw [h1]
  have h2 := Measure.integral_comp_mul_left
    (fun y => 𝓕 Φ (u - y / Γ) * 𝓕 cutoffC y) Γ
  simp only [mul_div_cancel_left₀ _ hΓ.ne'] at h2
  rw [abs_inv, abs_of_pos hΓ, Complex.real_smul] at h2
  have h3 : (∫ x, 𝓕 Φ (u - x) * ((Γ : ℂ) * 𝓕 cutoffC (Γ * x))) =
      (Γ : ℂ) * ∫ x, 𝓕 Φ (u - x) * 𝓕 cutoffC (Γ * x) := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun x => by ring)
  rw [h3, h2, ← mul_assoc]
  push_cast
  rw [mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hΓ.ne'), one_mul]

/-- The tail transform `𝓕(Φ(1 − χ(·/Γ)))`. -/
def tailTransform (Φ : ℝ → ℂ) (Γ u : ℝ) : ℂ :=
  𝓕 (fun ξ => Φ ξ * (1 - packet cutoffC 0 Γ ξ)) u

theorem integrable_exp_mul {f : ℝ → ℂ} (hf : Integrable f) (u : ℝ) :
    Integrable fun ξ => Complex.exp (-(2 * π * ξ * u : ℝ) * I) * f ξ :=
  hf.bdd_mul (c := 1) (Continuous.aestronglyMeasurable (by fun_prop))
    (Eventually.of_forall fun ξ => by
      rw [← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I])

theorem fourier_sub_eq {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (u : ℝ) :
    𝓕 (fun ξ => f ξ - g ξ) u = 𝓕 f u - 𝓕 g u := by
  rw [fourier_eq_integral, fourier_eq_integral, fourier_eq_integral,
    ← integral_sub (integrable_exp_mul hf u) (integrable_exp_mul hg u)]
  exact integral_congr_ae (Eventually.of_forall fun ξ => by ring)

theorem integrable_mul_cutoff {Φ : ℝ → ℂ} (hΦc : Continuous Φ) (hΦi : Integrable Φ) (Γ : ℝ) :
    Integrable fun ξ => Φ ξ * packet cutoffC 0 Γ ξ :=
  hΦi.mul_bdd (c := 1) (contDiff_cutoffC.continuous.comp (by fun_prop)).aestronglyMeasurable
    (Eventually.of_forall fun ξ => norm_cutoffC_le _)

theorem tailTransform_eq {Φ : ℝ → ℂ} (hΦc : Continuous Φ) (hΦi : Integrable Φ)
    (hFΦ : Integrable (𝓕 Φ)) {Γ : ℝ} (hΓ : 0 < Γ) (u : ℝ) :
    tailTransform Φ Γ u = ∫ y, (𝓕 Φ u - 𝓕 Φ (u - y / Γ)) * 𝓕 cutoffC y := by
  have hsplit : (fun ξ => Φ ξ * (1 - packet cutoffC 0 Γ ξ)) =
      fun ξ => Φ ξ - Φ ξ * packet cutoffC 0 Γ ξ := funext fun ξ => by ring
  rw [tailTransform, hsplit, fourier_sub_eq hΦi (integrable_mul_cutoff hΦc hΦi Γ),
    fourier_mul_cutoff_eq hΦc hΦi hFΦ hΓ]
  have hb : ∀ v, ‖𝓕 Φ v‖ ≤ ∫ ξ, ‖Φ ξ‖ := norm_fourier_le_integral_norm Φ
  have hi2 : Integrable fun y => 𝓕 Φ (u - y / Γ) * 𝓕 cutoffC y :=
    integrable_fourier_cutoffC.bdd_mul (c := ∫ ξ, ‖Φ ξ‖)
      (((continuous_fourier_integrable hΦi).comp (by fun_prop))).aestronglyMeasurable
      (Eventually.of_forall fun y => hb _)
  have e : (fun y => (𝓕 Φ u - 𝓕 Φ (u - y / Γ)) * 𝓕 cutoffC y) =
      fun y => 𝓕 Φ u * 𝓕 cutoffC y - 𝓕 Φ (u - y / Γ) * 𝓕 cutoffC y :=
    funext fun y => by ring
  rw [e, integral_sub (integrable_fourier_cutoffC.const_mul _) hi2, integral_const_mul,
    integral_fourier_cutoffC, mul_one]

theorem cauchyProfile_one_zero (u : ℝ) : cauchyProfile 1 0 u = 1 / (1 + u ^ 2) := by
  simp [cauchyProfile]

theorem cauchyProfile_le_self {η : ℝ} (hη : 0 < η) (s u : ℝ) : cauchyProfile η s u ≤ η := by
  simp only [cauchyProfile]
  rw [div_le_iff₀ (by positivity)]; nlinarith [sq_nonneg (η * (u - s))]

/-- **Uniform domination of the tail.** -/
theorem exists_norm_tailTransform_le {Φ : ℝ → ℂ} (hΦc : Continuous Φ) (hΦi : Integrable Φ)
    (hFΦ : Integrable (𝓕 Φ)) {b : ℝ} (hb : 0 ≤ b) (hsupp : ∀ u, b < |u| → 𝓕 Φ u = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Γ : ℝ, 1 ≤ Γ → ∀ u, ‖tailTransform Φ Γ u‖ ≤ C * cauchyProfile 1 0 u := by
  set M := ∫ ξ, ‖Φ ξ‖ with hM
  have hM0 : 0 ≤ M := integral_nonneg fun _ => norm_nonneg _
  have hb' : ∀ v, ‖𝓕 Φ v‖ ≤ M := norm_fourier_le_integral_norm Φ
  obtain ⟨Cχ, hCχ0, hCχ⟩ := exists_fourier_cutoffC_le
  set Lχ := ∫ y, ‖𝓕 cutoffC y‖ with hLχ
  have hLχ0 : 0 ≤ Lχ := integral_nonneg fun _ => norm_nonneg _
  set B₁ := b + 1 with hB₁
  refine ⟨2 * M * Lχ * (1 + B₁ ^ 2) + M * Cχ * π * B₁ ^ 2, by positivity, fun Γ hΓ u => ?_⟩
  have hΓ0 : 0 < Γ := by linarith
  rw [tailTransform_eq hΦc hΦi hFΦ hΓ0, cauchyProfile_one_zero]
  have hint1 : Integrable fun y => ‖(𝓕 Φ u - 𝓕 Φ (u - y / Γ)) * 𝓕 cutoffC y‖ := by
    refine (integrable_fourier_cutoffC.norm.const_mul (2 * M)).mono'
      ((((continuous_const.sub ((continuous_fourier_integrable hΦi).comp (by fun_prop))).mul
        (continuous_fourier_integrable integrable_cutoffC)).norm).aestronglyMeasurable)
      (Eventually.of_forall fun y => ?_)
    rw [norm_norm, norm_mul]
    have := norm_sub_le (𝓕 Φ u) (𝓕 Φ (u - y / Γ))
    exact mul_le_mul_of_nonneg_right (by linarith [hb' u, hb' (u - y / Γ)]) (norm_nonneg _)
  refine (norm_integral_le_integral_norm _).trans ?_
  rcases le_or_gt |u| B₁ with hu | hu
  · -- bounded region
    have hle : ∫ y, ‖(𝓕 Φ u - 𝓕 Φ (u - y / Γ)) * 𝓕 cutoffC y‖ ≤ 2 * M * Lχ := by
      rw [hLχ, ← integral_const_mul]
      refine integral_mono hint1 (integrable_fourier_cutoffC.norm.const_mul _) fun y => ?_
      rw [norm_mul]
      have := norm_sub_le (𝓕 Φ u) (𝓕 Φ (u - y / Γ))
      exact mul_le_mul_of_nonneg_right (by linarith [hb' u, hb' (u - y / Γ)]) (norm_nonneg _)
    have hu2 : 1 + u ^ 2 ≤ 1 + B₁ ^ 2 := by
      have := sq_abs u; nlinarith [abs_nonneg u]
    calc _ ≤ 2 * M * Lχ := hle
      _ ≤ 2 * M * Lχ * (1 + B₁ ^ 2) * (1 / (1 + u ^ 2)) := by
          rw [mul_one_div, le_div_iff₀ (by positivity)]
          exact mul_le_mul_of_nonneg_left hu2 (by positivity)
      _ ≤ _ := by
          have : 0 ≤ M * Cχ * π * B₁ ^ 2 * (1 / (1 + u ^ 2)) := by positivity
          nlinarith
  · -- far region
    have hbu : b < |u| := by linarith
    have hzero : 𝓕 Φ u = 0 := hsupp u hbu
    set d := |u| - b with hd
    have hd0 : 1 < d := by linarith
    have hpt : ∀ y, ‖(𝓕 Φ u - 𝓕 Φ (u - y / Γ)) * 𝓕 cutoffC y‖ ≤
        M * Cχ / (1 + d ^ 2) * (1 + y ^ 2)⁻¹ := by
      intro y
      rw [hzero, zero_sub, norm_mul, norm_neg]
      by_cases hy : b < |u - y / Γ|
      · rw [hsupp _ hy, norm_zero, zero_mul]; positivity
      · push Not at hy
        have hyd : d ≤ |y| := by
          have h1 : |u| - |y / Γ| ≤ |u - y / Γ| := abs_sub_abs_le_abs_sub u (y / Γ)
          have h2 : |y / Γ| ≤ |y| := by
            rw [abs_div, abs_of_pos hΓ0]; exact div_le_self (abs_nonneg y) hΓ
          linarith
        have hy2 : d ^ 2 ≤ y ^ 2 := by
          rw [← sq_abs y]; exact pow_le_pow_left₀ (by linarith) hyd 2
        have hχ := hCχ y
        have hden : (1 + d ^ 2) * (1 + y ^ 2) ≤ (1 + y ^ 2) ^ 2 := by nlinarith [sq_nonneg y]
        have hχ' : ‖𝓕 cutoffC y‖ ≤ Cχ / ((1 + d ^ 2) * (1 + y ^ 2)) :=
          hχ.trans (div_le_div_of_nonneg_left hCχ0 (by positivity) hden)
        calc ‖𝓕 Φ (u - y / Γ)‖ * ‖𝓕 cutoffC y‖ ≤ M * (Cχ / ((1 + d ^ 2) * (1 + y ^ 2))) :=
              mul_le_mul (hb' _) hχ' (norm_nonneg _) hM0
          _ = M * Cχ / (1 + d ^ 2) * (1 + y ^ 2)⁻¹ := by field_simp
    have hle : ∫ y, ‖(𝓕 Φ u - 𝓕 Φ (u - y / Γ)) * 𝓕 cutoffC y‖ ≤ M * Cχ / (1 + d ^ 2) * π := by
      rw [← integral_univ_inv_one_add_sq, ← integral_const_mul]
      exact integral_mono hint1 (integrable_inv_one_add_sq.const_mul _) hpt
    have hdu : (1 + u ^ 2) ≤ B₁ ^ 2 * (1 + d ^ 2) := by
      have hB : 1 ≤ B₁ := by linarith
      have h1 : |u| ≤ B₁ * d := by
        rw [hd]; nlinarith [abs_nonneg u]
      have h2 : u ^ 2 ≤ B₁ ^ 2 * d ^ 2 := by
        rw [← sq_abs u]; nlinarith [abs_nonneg u]
      nlinarith [sq_nonneg B₁]
    calc _ ≤ M * Cχ / (1 + d ^ 2) * π := hle
      _ ≤ M * Cχ * π * B₁ ^ 2 * (1 / (1 + u ^ 2)) := by
          rw [mul_one_div, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
          have h0 : 0 ≤ M * Cχ * π := by positivity
          nlinarith [mul_le_mul_of_nonneg_left hdu h0]
      _ ≤ _ := by
          have : 0 ≤ 2 * M * Lχ * (1 + B₁ ^ 2) * (1 / (1 + u ^ 2)) := by positivity
          nlinarith

/-- **The tail tends to zero pointwise.** -/
theorem tendsto_tailTransform {Φ : ℝ → ℂ} (hΦi : Integrable Φ) (u : ℝ) :
    Tendsto (fun Γ => tailTransform Φ Γ u) atTop (𝓝 0) := by
  have h0 : (0 : ℂ) = ∫ ξ, Complex.exp (-(2 * π * ξ * u : ℝ) * I) * (Φ ξ * (1 - 1)) := by simp
  simp only [tailTransform, fourier_eq_integral]
  rw [h0]
  refine tendsto_integral_filter_of_dominated_convergence (fun ξ => ‖Φ ξ‖) ?_ ?_ hΦi.norm ?_
  · exact Eventually.of_forall fun Γ => (integrable_exp_mul
      (hΦi.mul_bdd (c := 1) ((continuous_const.sub (contDiff_cutoffC.continuous.comp
        (by fun_prop))).aestronglyMeasurable)
        (Eventually.of_forall fun ξ => norm_one_sub_cutoffC_le _)) u).aestronglyMeasurable
  · refine Eventually.of_forall fun Γ => Eventually.of_forall fun ξ => ?_
    rw [norm_mul, ← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I, one_mul, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_one_sub_cutoffC_le _)
  · refine Eventually.of_forall fun ξ => ?_
    have hc : Tendsto (fun Γ : ℝ => (ξ - 0) / Γ) atTop (𝓝 0) := by
      simpa using tendsto_const_nhds.div_atTop tendsto_id
    have h1 : Tendsto (fun Γ : ℝ => cutoffC ((ξ - 0) / Γ)) atTop (𝓝 (cutoffC 0)) :=
      (contDiff_cutoffC.continuous.tendsto 0).comp hc
    rw [cutoffC_zero] at h1
    exact ((tendsto_const_nhds.sub h1).const_mul (Φ ξ)).const_mul _

/-- **The tail pairing tends to zero.** -/
theorem tendsto_deviationPairing_tail {lam : ℕ → ℝ} (hexc : Summable (deviationExcess lam))
    {D : ℝ} (hD : CauchyBounded (deviationDeficit lam) D) {Φ : ℝ → ℂ} (hΦc : Continuous Φ)
    (hΦi : Integrable Φ) (hFΦ : Integrable (𝓕 Φ)) {b : ℝ} (hb : 0 ≤ b)
    (hsupp : ∀ u, b < |u| → 𝓕 Φ u = 0) :
    Tendsto (fun Γ => deviationPairing lam (tailTransform Φ Γ)) atTop (𝓝 0) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_tailTransform_le hΦc hΦi hFΦ hb hsupp
  obtain ⟨hvs, -⟩ := hD 1 one_pos le_rfl 0
  have ha : ∀ n, |weilDeviation lam n| ≤ deviationExcess lam n + deviationDeficit lam n := by
    intro n
    rw [weilDeviation_eq_sub]
    refine (abs_sub _ _).trans (le_of_eq ?_)
    rw [abs_of_nonneg (deviationExcess_nonneg lam n), abs_of_nonneg (deviationDeficit_nonneg lam n)]
  have h0 : (0 : ℂ) = ∑' n : ℕ, (0 : ℂ) := by simp
  unfold deviationPairing
  rw [h0]
  refine tendsto_tsum_of_dominated_convergence
    (bound := fun n : ℕ => C * (2 * deviationExcess lam n) + C * (deviationDeficit lam n *
      (cauchyProfile 1 0 (Real.log n) + cauchyProfile 1 0 (-Real.log n))))
    ((hexc.mul_left 2 |>.mul_left C).add (hvs.mul_left C)) (fun n => ?_) ?_
  · have h1 := (tendsto_tailTransform hΦi (Real.log n)).add (tendsto_tailTransform hΦi (-Real.log n))
    rw [add_zero] at h1
    simpa using h1.const_mul (weilDeviation lam n : ℂ)
  · filter_upwards [eventually_ge_atTop 1] with Γ hΓ
    intro n
    have h1 := hC Γ hΓ (Real.log n)
    have h2 := hC Γ hΓ (-Real.log n)
    have hc1 := cauchyProfile_le_self one_pos 0 (Real.log n)
    have hc2 := cauchyProfile_le_self one_pos 0 (-Real.log n)
    have hp1 := cauchyProfile_nonneg zero_le_one 0 (Real.log n)
    have hp2 := cauchyProfile_nonneg zero_le_one 0 (-Real.log n)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hsum : ‖tailTransform Φ Γ (Real.log n) + tailTransform Φ Γ (-Real.log n)‖ ≤
        C * (cauchyProfile 1 0 (Real.log n) + cauchyProfile 1 0 (-Real.log n)) :=
      (norm_add_le _ _).trans (by linarith)
    have he := deviationExcess_nonneg lam n
    have hv := deviationDeficit_nonneg lam n
    calc |weilDeviation lam n| *
          ‖tailTransform Φ Γ (Real.log n) + tailTransform Φ Γ (-Real.log n)‖
        ≤ (deviationExcess lam n + deviationDeficit lam n) *
          (C * (cauchyProfile 1 0 (Real.log n) + cauchyProfile 1 0 (-Real.log n))) :=
          mul_le_mul (ha n) hsum (norm_nonneg _) (by positivity)
      _ ≤ _ := by
          have hcs : cauchyProfile 1 0 (Real.log n) + cauchyProfile 1 0 (-Real.log n) ≤ 2 := by
            linarith
          have hk : deviationExcess lam n * (C * (cauchyProfile 1 0 (Real.log n) +
              cauchyProfile 1 0 (-Real.log n))) ≤ deviationExcess lam n * (C * 2) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcs hC0) he
          linarith

end

end RHTower.WeilExcess
