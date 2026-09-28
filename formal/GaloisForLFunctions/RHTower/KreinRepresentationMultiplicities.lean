import GaloisForLFunctions.RHTower.XiOnLineZeroLocalBounds

/-!
# The resolvent test at an on-line zero

A positive measure `ν` *represents* the level-`L` Hodge form of `ζ` if
`∫ |f̂|² dν = |W(f,f)|` for every Hodge-class test at level `L` (`RepresentsHodgeForm`); every
positive Krein completion does, and under RH so does the zero-counting measure.

This module provides the ingredients of the mass law at an on-line zero `ρ₀ = 1/2 + iγ₀`:

* `measure_le_of_representation`, `norm_W_le_of_representation`: the two measure inequalities
  (an upper mass bound from a lower bound of `|f̂|` on a ball; a lower bound of `|W(f,f)|` from a
  pointwise domination off the ball).
* `norm_W_resolventTest_sub_le`: for `f = (D_{γ₀}^{m₀} Φ_θ)_{≤U} ⋆ κ₂`, the Weil form is
  `m₀ |f̂(γ₀)|²` up to the squared tail.
* `norm_paperFT_resolventTest_le`: off the ball `|τ - γ₀| ≥ r`, the test is dominated by
  `r^{-m₀}` times the tilted radical test plus a tail times the plain bump.
* `norm_paperFT_resolventTest_sub_le`: on the ball, the test is constant up to the variation of
  `D_{γ₀}^{m₀} Φ̂_θ` and the Lipschitz constant of the bump transform.
-/

open Complex MeasureTheory Filter Topology Set Metric
open scoped Real ENNReal
open Bottcher Zeta23

namespace RHTower

noncomputable section

/-- A Hodge-class test at level `L`: `C²`, supported in `[-L, L]`, `f̂(±i/2) = 0`. -/
def IsHodgeTest (L : ℝ) (f : ℝ → ℂ) : Prop :=
  ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-L) L ∧ paperFT f (I / 2) = 0 ∧ paperFT f (-(I / 2)) = 0

/-- `ν` represents the level-`L` Hodge form: `∫ |f̂|² dν = |W(f,f)|` on the Hodge class. -/
def RepresentsHodgeForm (L : ℝ) (ν : Measure ℝ) : Prop :=
  ∀ f : ℝ → ℂ, IsHodgeTest L f →
    ∫⁻ τ, ENNReal.ofReal (‖paperFT f τ‖ ^ 2) ∂ν = ENNReal.ofReal ‖zetaZeroConfig.W f f‖

theorem IsHodgeTest.superExpDecay {L : ℝ} {f : ℝ → ℂ} (hf : IsHodgeTest L f) :
    SuperExpDecay f := by
  have hcs : HasCompactSupport f := isCompact_Icc.of_isClosed_subset (isClosed_tsupport f) hf.2.1
  refine ⟨hf.1.continuous, fun c => ?_⟩
  exact (hf.1.continuous.norm.mul (by fun_prop)).integrable_of_hasCompactSupport hcs.norm.mul_right

theorem measurable_ofReal_norm_paperFT_sq {L : ℝ} {f : ℝ → ℂ} (hf : IsHodgeTest L f) :
    Measurable (fun τ : ℝ => ENNReal.ofReal (‖paperFT f (τ : ℂ)‖ ^ 2)) := by
  have hc : Continuous (fun τ : ℝ => paperFT f (τ : ℂ)) :=
    hf.superExpDecay.continuous_paperFT.comp Complex.continuous_ofReal
  exact ENNReal.measurable_ofReal.comp ((hc.norm.pow 2).measurable)

/-! ## The two measure-theoretic inequalities -/

/-- **Upper mass bound.**  If `|f̂| ≥ ℓ > 0` on `B`, then `ν(B) ≤ |W(f,f)|/ℓ²`. -/
theorem measure_le_of_representation {L : ℝ} {ν : Measure ℝ} (hν : RepresentsHodgeForm L ν)
    {f : ℝ → ℂ} (hf : IsHodgeTest L f) {B : Set ℝ} (hB : MeasurableSet B) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hlow : ∀ τ ∈ B, ℓ ≤ ‖paperFT f (τ : ℂ)‖) :
    ν B ≤ ENNReal.ofReal (‖zetaZeroConfig.W f f‖ / ℓ ^ 2) := by
  have hind : ∫⁻ τ, B.indicator (fun _ => ENNReal.ofReal (ℓ ^ 2)) τ ∂ν ≤
      ∫⁻ τ, ENNReal.ofReal (‖paperFT f (τ : ℂ)‖ ^ 2) ∂ν := by
    refine lintegral_mono fun τ => ?_
    by_cases hτ : τ ∈ B
    · rw [indicator_of_mem hτ]
      exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hℓ.le (hlow τ hτ) 2)
    · rw [indicator_of_notMem hτ]; exact bot_le
  rw [lintegral_indicator_const hB, hν f hf] at hind
  have hℓ2 : 0 < ℓ ^ 2 := by positivity
  rw [ENNReal.ofReal_div_of_pos hℓ2]
  rw [ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.mpr hℓ2).ne')
    (Or.inl ENNReal.ofReal_ne_top)]
  rw [mul_comm]; exact hind

/-- **Lower mass bound.**  If `|f̂| ≤ X` on `B` and `|f̂| ≤ a|ĝ| + b|k̂|` off `B`, then
`|W(f,f)| ≤ ν(B) X² + 2a²|W(g,g)| + 2b²|W(k,k)|`. -/
theorem norm_W_le_of_representation {L : ℝ} {ν : Measure ℝ} (hν : RepresentsHodgeForm L ν)
    {f g k : ℝ → ℂ} (hf : IsHodgeTest L f) (hg : IsHodgeTest L g) (hk : IsHodgeTest L k)
    {B : Set ℝ} (hB : MeasurableSet B) (hBfin : ν B ≠ ⊤) {X a b : ℝ}
    (hin : ∀ τ ∈ B, ‖paperFT f (τ : ℂ)‖ ≤ X)
    (hout : ∀ τ ∉ B, ‖paperFT f (τ : ℂ)‖ ≤ a * ‖paperFT g (τ : ℂ)‖ + b * ‖paperFT k (τ : ℂ)‖) :
    ‖zetaZeroConfig.W f f‖ ≤ (ν B).toReal * X ^ 2 + 2 * a ^ 2 * ‖zetaZeroConfig.W g g‖ +
      2 * b ^ 2 * ‖zetaZeroConfig.W k k‖ := by
  have hX0 : ∀ τ ∈ B, 0 ≤ X := fun τ hτ => (norm_nonneg _).trans (hin τ hτ)
  set G := fun τ : ℝ => ENNReal.ofReal (‖paperFT g (τ : ℂ)‖ ^ 2)
  set K := fun τ : ℝ => ENNReal.ofReal (‖paperFT k (τ : ℂ)‖ ^ 2)
  have hpt : ∀ τ : ℝ, ENNReal.ofReal (‖paperFT f (τ : ℂ)‖ ^ 2) ≤
      B.indicator (fun _ => ENNReal.ofReal (X ^ 2)) τ +
        (ENNReal.ofReal (2 * a ^ 2) * G τ + ENNReal.ofReal (2 * b ^ 2) * K τ) := by
    intro τ
    by_cases hτ : τ ∈ B
    · rw [indicator_of_mem hτ]
      refine le_trans (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (hin τ hτ) 2))
        le_self_add
    · rw [indicator_of_notMem hτ, zero_add]
      have h1 := hout τ hτ
      have h2 : ‖paperFT f (τ : ℂ)‖ ^ 2 ≤
          2 * a ^ 2 * ‖paperFT g (τ : ℂ)‖ ^ 2 + 2 * b ^ 2 * ‖paperFT k (τ : ℂ)‖ ^ 2 := by
        have := pow_le_pow_left₀ (norm_nonneg _) h1 2
        nlinarith [sq_nonneg (a * ‖paperFT g (τ : ℂ)‖ - b * ‖paperFT k (τ : ℂ)‖)]
      refine (ENNReal.ofReal_le_ofReal h2).trans (le_of_eq ?_)
      rw [ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_mul (p := 2 * a ^ 2) (by positivity),
        ENNReal.ofReal_mul (p := 2 * b ^ 2) (by positivity)]
  have hGm : Measurable G := measurable_ofReal_norm_paperFT_sq hg
  have hKm : Measurable K := measurable_ofReal_norm_paperFT_sq hk
  have hint := lintegral_mono (μ := ν) hpt
  rw [hν f hf, lintegral_add_left (measurable_const.indicator hB),
    lintegral_indicator_const hB, lintegral_add_left (hGm.const_mul _),
    lintegral_const_mul _ hGm, lintegral_const_mul _ hKm, hν g hg, hν k hk] at hint
  set P : ℝ≥0∞ := ENNReal.ofReal (X ^ 2) * ν B with hP
  set Q : ℝ≥0∞ := ENNReal.ofReal (2 * a ^ 2) * ENNReal.ofReal ‖zetaZeroConfig.W g g‖ with hQ
  set R : ℝ≥0∞ := ENNReal.ofReal (2 * b ^ 2) * ENNReal.ofReal ‖zetaZeroConfig.W k k‖ with hR
  have hPf : P ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hBfin
  have hQf : Q ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hRf : R ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hQR : Q + R ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨hQf, hRf⟩
  have hfin : P + (Q + R) ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨hPf, hQR⟩
  have hreal := (ENNReal.ofReal_le_iff_le_toReal hfin).mp hint
  have hPr : P.toReal = X ^ 2 * (ν B).toReal := by
    rw [hP, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  have hQr : Q.toReal = 2 * a ^ 2 * ‖zetaZeroConfig.W g g‖ := by
    rw [hQ, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
      ENNReal.toReal_ofReal (norm_nonneg _)]
  have hRr : R.toReal = 2 * b ^ 2 * ‖zetaZeroConfig.W k k‖ := by
    rw [hR, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
      ENNReal.toReal_ofReal (norm_nonneg _)]
  rw [ENNReal.toReal_add hPf hQR, ENNReal.toReal_add hQf hRf, hPr, hQr, hRr] at hreal
  linarith

/-! ## The resolvent test off the ball -/

/-- **Pointwise domination off the ball.**  With `(z - γ₀)^m F̂ = Φ̂_θ`, for real `τ` with
`|τ - γ₀| ≥ r`:
`|f̂(τ)| ≤ r^{-m} |ĝ(τ)| + (r^{-m} ε_Φ + ε_F) |κ̂₂(τ)|`, where `f = F_{≤U} ⋆ κ₂`,
`g = Φ_{θ,≤U} ⋆ κ₂` and `ε` are the weighted tails. -/
theorem norm_paperFT_resolventTest_le {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : 2 * θ < π / 2) {γ₀ : ℝ}
    {m : ℕ} {F : ℝ → ℂ} (hF : SuperExpDecay F)
    (hprod : ∀ z : ℂ, (z - (γ₀ : ℂ)) ^ m * paperFT F z = paperFT (tiltedPhi θ) z)
    {U w : ℝ} (hw : 0 < w) {r : ℝ} (hr0 : 0 < r) {τ : ℝ} (hτ : r ≤ |τ - γ₀|) :
    ‖paperFT (bumpedTest (cutoffCore U F) w γ₀) (τ : ℂ)‖ ≤
      (r ^ m)⁻¹ * ‖paperFT (bumpedTest (cutoffCore U (tiltedPhi θ)) w γ₀) (τ : ℂ)‖ +
      ((r ^ m)⁻¹ * expTail (tiltedPhi θ) (1 / 2) U + expTail F (1 / 2) U) *
        ‖paperFT (scaledBumpPolarFree w γ₀) (τ : ℂ)‖ := by
  have hdecay := superExpDecay_tiltedRiemannKernel hθ0 hθ
  have hz : |((τ : ℂ)).im| ≤ 1 / 2 := by simp
  rw [paperFT_bumpedTest (integrable_cutoffCore hF.1) (fun u hu => cutoffCore_eq_zero hu) hw,
    paperFT_bumpedTest (integrable_cutoffCore hdecay.1) (fun u hu => cutoffCore_eq_zero hu) hw,
    paperFT_cutoffCore_eq hF, paperFT_cutoffCore_eq hdecay]
  set κ := paperFT (scaledBumpPolarFree w γ₀) (τ : ℂ)
  set TF := paperFT (cutoffTail U F) (τ : ℂ)
  set TΦ := paperFT (cutoffTail U (tiltedPhi θ)) (τ : ℂ)
  have hTF : ‖TF‖ ≤ expTail F (1 / 2) U := norm_paperFT_cutoffTail_le hF hz
  have hTΦ : ‖TΦ‖ ≤ expTail (tiltedPhi θ) (1 / 2) U := norm_paperFT_cutoffTail_le hdecay hz
  set D : ℂ := (τ : ℂ) - (γ₀ : ℂ) with hD
  have hDn : ‖D‖ = |τ - γ₀| := by
    rw [hD, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have hD0 : D ≠ 0 := by
    intro h; rw [h, norm_zero] at hDn; linarith [abs_nonneg (τ - γ₀)]
  have hDm : D ^ m ≠ 0 := pow_ne_zero _ hD0
  have hFτ : paperFT F (τ : ℂ) = paperFT (tiltedPhi θ) (τ : ℂ) / D ^ m := by
    rw [eq_div_iff hDm, mul_comm]; exact hprod τ
  have hrm : r ^ m ≤ ‖D ^ m‖ := by
    rw [norm_pow, hDn]; exact pow_le_pow_left₀ hr0.le hτ m
  have hrm0 : 0 < r ^ m := pow_pos hr0 m
  have hinv : ‖D ^ m‖⁻¹ ≤ (r ^ m)⁻¹ := inv_anti₀ hrm0 hrm
  have hkey : (paperFT F (τ : ℂ) - TF) * κ =
      (paperFT (tiltedPhi θ) (τ : ℂ) - TΦ) * κ / D ^ m + (TΦ / D ^ m - TF) * κ := by
    rw [hFτ]; field_simp; ring
  rw [hkey]
  calc ‖(paperFT (tiltedPhi θ) (τ : ℂ) - TΦ) * κ / D ^ m + (TΦ / D ^ m - TF) * κ‖
      ≤ ‖(paperFT (tiltedPhi θ) (τ : ℂ) - TΦ) * κ‖ * ‖D ^ m‖⁻¹ +
          (‖TΦ‖ * ‖D ^ m‖⁻¹ + ‖TF‖) * ‖κ‖ := by
        refine (norm_add_le _ _).trans (add_le_add (le_of_eq ?_) ?_)
        · rw [norm_div, div_eq_mul_inv]
        · rw [norm_mul]
          refine mul_le_mul_of_nonneg_right ((norm_sub_le _ _).trans (le_of_eq ?_)) (norm_nonneg _)
          rw [norm_div, div_eq_mul_inv]
    _ ≤ ‖(paperFT (tiltedPhi θ) (τ : ℂ) - TΦ) * κ‖ * (r ^ m)⁻¹ +
          (expTail (tiltedPhi θ) (1 / 2) U * (r ^ m)⁻¹ + expTail F (1 / 2) U) * ‖κ‖ :=
        add_le_add (mul_le_mul_of_nonneg_left hinv (norm_nonneg _))
          (mul_le_mul_of_nonneg_right (add_le_add (mul_le_mul hTΦ hinv
            (inv_nonneg.mpr (norm_nonneg _)) (expTail_nonneg _ _ _)) hTF) (norm_nonneg _))
    _ = _ := by ring

/-! ## Lipschitz bounds for the bump transform -/

theorem norm_scaledBump_le {w u : ℝ} : ‖scaledBump w u‖ ≤ 1 := by
  unfold scaledBump weilBumpC
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg weilBump.nonneg]
  exact weilBump.le_one

theorem norm_paperFT_scaledBump_real_sub_le {w : ℝ} (hw : 0 < w) (s s' : ℝ) :
    ‖paperFT (scaledBump w) (s : ℂ) - paperFT (scaledBump w) (s' : ℂ)‖ ≤ 2 * w ^ 2 * |s - s'| := by
  have hcs : HasCompactSupport (scaledBump w) :=
    hasCompactSupport_of_support_subset_abs (Λ := w) fun u hu => by
      by_contra h; push Not at h; exact hu (scaledBump_eq_zero hw h.le)
  have hi : ∀ t : ℝ, Integrable (fun u : ℝ => scaledBump w u * cexp (I * (t : ℂ) * u)) := fun t =>
    ((contDiff_scaledBump w).continuous.mul (by fun_prop)).integrable_of_hasCompactSupport
      hcs.mul_right
  unfold paperFT
  rw [← integral_sub (hi s) (hi s')]
  have hmaj : Integrable ((Icc (-w) w).indicator (fun _ : ℝ => w * |s - s'|)) :=
    (continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc
  refine (norm_integral_le_integral_norm _).trans ?_
  refine (integral_mono_of_nonneg (Eventually.of_forall fun u => norm_nonneg _) hmaj
    (Eventually.of_forall fun u => ?_)).trans (le_of_eq ?_)
  · simp only [indicator]
    split_ifs with h
    · rw [← mul_sub, norm_mul]
      have h1 : ‖scaledBump w u‖ ≤ 1 := norm_scaledBump_le
      have h2 : ‖cexp (I * (s : ℂ) * u) - cexp (I * (s' : ℂ) * u)‖ ≤ |s - s'| * w := by
        have e : cexp (I * (s : ℂ) * u) - cexp (I * (s' : ℂ) * u) =
            cexp (I * (s' : ℂ) * u) * (cexp (I * (((s - s') * u : ℝ) : ℂ)) - 1) := by
          rw [mul_sub, ← Complex.exp_add, mul_one]; congr 2; push_cast; ring
        rw [e, norm_mul]
        have h3 : ‖cexp (I * (s' : ℂ) * u)‖ = 1 := by
          rw [show I * (s' : ℂ) * u = ((s' * u : ℝ) : ℂ) * I by push_cast; ring,
            Complex.norm_exp_ofReal_mul_I]
        rw [h3, one_mul]
        refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans ?_
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_left (abs_le.mpr ⟨h.1, h.2⟩) (abs_nonneg _)
      calc ‖scaledBump w u‖ * ‖cexp (I * (s : ℂ) * u) - cexp (I * (s' : ℂ) * u)‖
          ≤ 1 * (|s - s'| * w) := mul_le_mul h1 h2 (norm_nonneg _) (by norm_num)
        _ = w * |s - s'| := by ring
    · have hu : w ≤ |u| := by
        by_contra hc; push Not at hc; exact h ⟨by linarith [(abs_lt.mp hc).1],
          by linarith [(abs_lt.mp hc).2]⟩
      rw [scaledBump_eq_zero hw hu, zero_mul, zero_mul, sub_zero, norm_zero]
  · rw [integral_indicator_const _ measurableSet_Icc, smul_eq_mul,
      Real.volume_real_Icc_of_le (by linarith)]
    ring

theorem norm_paperFT_scaledBump_real_le {w : ℝ} (hw : 0 < w) (s : ℝ) :
    ‖paperFT (scaledBump w) (s : ℂ)‖ ≤ 2 * w := by
  have hcs : HasCompactSupport (scaledBump w) :=
    hasCompactSupport_of_support_subset_abs (Λ := w) fun u hu => by
      by_contra h; push Not at h; exact hu (scaledBump_eq_zero hw h.le)
  unfold paperFT
  have hmaj : Integrable ((Icc (-w) w).indicator (fun _ : ℝ => (1 : ℝ))) :=
    (continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc
  refine (norm_integral_le_integral_norm _).trans ?_
  refine (integral_mono_of_nonneg (Eventually.of_forall fun u => norm_nonneg _) hmaj
    (Eventually.of_forall fun u => ?_)).trans (le_of_eq ?_)
  · simp only [indicator]
    split_ifs with h
    · rw [norm_mul]
      have h3 : ‖cexp (I * (s : ℂ) * u)‖ = 1 := by
        rw [show I * (s : ℂ) * u = ((s * u : ℝ) : ℂ) * I by push_cast; ring,
          Complex.norm_exp_ofReal_mul_I]
      rw [h3, mul_one]; exact norm_scaledBump_le
    · have hu : w ≤ |u| := by
        by_contra hc; push Not at hc; exact h ⟨by linarith [(abs_lt.mp hc).1],
          by linarith [(abs_lt.mp hc).2]⟩
      rw [scaledBump_eq_zero hw hu, zero_mul, norm_zero]
  · rw [integral_indicator_const _ measurableSet_Icc, smul_eq_mul,
      Real.volume_real_Icc_of_le (by linarith)]
    ring

/-- `L_κ = 2w² (|γ₀|+2)² + 2w (2|γ₀|+1)`. -/
def bumpLipConst (w γ₀ : ℝ) : ℝ := 2 * w ^ 2 * (|γ₀| + 2) ^ 2 + 2 * w * (2 * |γ₀| + 1)

/-- For real `|τ - γ₀| ≤ 1`: `|κ̂₂(τ) - κ̂₂(γ₀)| ≤ L_κ |τ - γ₀|`. -/
theorem norm_paperFT_scaledBumpPolarFree_real_sub_le {w : ℝ} (hw : 0 < w) (γ₀ : ℝ) {τ : ℝ}
    (hτ : |τ - γ₀| ≤ 1) :
    ‖paperFT (scaledBumpPolarFree w γ₀) (τ : ℂ) - paperFT (scaledBumpPolarFree w γ₀) (γ₀ : ℂ)‖ ≤
      bumpLipConst w γ₀ * |τ - γ₀| := by
  rw [paperFT_scaledBumpPolarFree hw, paperFT_scaledBumpPolarFree hw, sub_self,
    show ((τ : ℂ) - (γ₀ : ℂ)) = ((τ - γ₀ : ℝ) : ℂ) by push_cast; ring]
  have h1 := norm_paperFT_scaledBump_real_sub_le hw (τ - γ₀) 0
  have h2 := norm_paperFT_scaledBump_real_le hw 0
  push_cast at h1 h2
  set A := paperFT (scaledBump w) ((τ - γ₀ : ℝ) : ℂ)
  set A0 := paperFT (scaledBump w) 0
  have e : -((τ : ℂ) ^ 2 + 1 / 4) * A - -((γ₀ : ℂ) ^ 2 + 1 / 4) * A0 =
      -((τ : ℂ) ^ 2 + 1 / 4) * (A - A0) - (((τ - γ₀) * (τ + γ₀) : ℝ) : ℂ) * A0 := by
    push_cast; ring
  rw [e]
  have hτa : |τ| ≤ |γ₀| + 1 := by
    have := abs_sub_abs_le_abs_sub τ γ₀; linarith
  have hq : ‖-((τ : ℂ) ^ 2 + 1 / 4)‖ ≤ (|γ₀| + 2) ^ 2 := by
    rw [norm_neg, show (τ : ℂ) ^ 2 + 1 / 4 = ((τ ^ 2 + 1 / 4 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have : τ ^ 2 ≤ (|γ₀| + 1) ^ 2 := by
      rw [← sq_abs τ]; exact pow_le_pow_left₀ (abs_nonneg _) hτa 2
    nlinarith [abs_nonneg γ₀]
  have hAd : ‖A - A0‖ ≤ 2 * w ^ 2 * |τ - γ₀| := by
    have := h1; simpa [A, A0] using this
  have hA0 : ‖A0‖ ≤ 2 * w := by simpa [A0] using h2
  have hlin : ‖(((τ - γ₀) * (τ + γ₀) : ℝ) : ℂ)‖ ≤ |τ - γ₀| * (2 * |γ₀| + 1) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    calc |τ + γ₀| ≤ |τ| + |γ₀| := abs_add_le _ _
      _ ≤ 2 * |γ₀| + 1 := by linarith
  calc ‖-((τ : ℂ) ^ 2 + 1 / 4) * (A - A0) - (((τ - γ₀) * (τ + γ₀) : ℝ) : ℂ) * A0‖
      ≤ ‖-((τ : ℂ) ^ 2 + 1 / 4)‖ * ‖A - A0‖ + ‖(((τ - γ₀) * (τ + γ₀) : ℝ) : ℂ)‖ * ‖A0‖ := by
        refine (norm_sub_le _ _).trans ?_
        rw [norm_mul, norm_mul]
    _ ≤ (|γ₀| + 2) ^ 2 * (2 * w ^ 2 * |τ - γ₀|) + (|τ - γ₀| * (2 * |γ₀| + 1)) * (2 * w) := by
        gcongr
    _ = bumpLipConst w γ₀ * |τ - γ₀| := by unfold bumpLipConst; ring

/-! ## The resolvent test on the ball -/

/-- **Variation on the ball.**  If `|F̂(τ) - F̂(γ₀)| ≤ β |F̂(γ₀)|` for `|τ - γ₀| ≤ r ≤ 1`, then
`|f̂(τ) - f̂(γ₀)| ≤ (β|F̂(γ₀)| + 2ε_F)(|κ̂₂(γ₀)| + L_κ r) + (|F̂(γ₀)| + ε_F) L_κ r`. -/
theorem norm_paperFT_resolventTest_sub_le {γ₀ : ℝ} {F : ℝ → ℂ} (hF : SuperExpDecay F) {U w : ℝ}
    (hw : 0 < w) {β r : ℝ}
    (hvar : ∀ τ : ℝ, |τ - γ₀| ≤ r →
      ‖paperFT F (τ : ℂ) - paperFT F (γ₀ : ℂ)‖ ≤ β * ‖paperFT F (γ₀ : ℂ)‖)
    {τ : ℝ} (hτ : |τ - γ₀| ≤ r) (hr1 : r ≤ 1) :
    ‖paperFT (bumpedTest (cutoffCore U F) w γ₀) (τ : ℂ) -
        paperFT (bumpedTest (cutoffCore U F) w γ₀) (γ₀ : ℂ)‖ ≤
      (β * ‖paperFT F (γ₀ : ℂ)‖ + 2 * expTail F (1 / 2) U) *
          (‖paperFT (scaledBumpPolarFree w γ₀) (γ₀ : ℂ)‖ + bumpLipConst w γ₀ * r) +
        (‖paperFT F (γ₀ : ℂ)‖ + expTail F (1 / 2) U) * (bumpLipConst w γ₀ * r) := by
  have hsupp : ∀ u, U < |u| → cutoffCore U F u = 0 := fun u hu => cutoffCore_eq_zero hu
  have hint := integrable_cutoffCore (U := U) hF.1
  rw [paperFT_bumpedTest hint hsupp hw, paperFT_bumpedTest hint hsupp hw,
    paperFT_cutoffCore_eq hF, paperFT_cutoffCore_eq hF]
  have hz1 : |((τ : ℂ)).im| ≤ 1 / 2 := by simp
  have hz0 : |((γ₀ : ℂ)).im| ≤ 1 / 2 := by simp
  set εF := expTail F (1 / 2) U
  have hT1 := norm_paperFT_cutoffTail_le (U := U) hF hz1
  have hT0 := norm_paperFT_cutoffTail_le (U := U) hF hz0
  set κτ := paperFT (scaledBumpPolarFree w γ₀) (τ : ℂ)
  set κ0 := paperFT (scaledBumpPolarFree w γ₀) (γ₀ : ℂ)
  set Aτ := paperFT F (τ : ℂ) - paperFT (cutoffTail U F) (τ : ℂ)
  set A0 := paperFT F (γ₀ : ℂ) - paperFT (cutoffTail U F) (γ₀ : ℂ)
  have hL := norm_paperFT_scaledBumpPolarFree_real_sub_le hw γ₀ (τ := τ) (by linarith)
  have hLr : ‖κτ - κ0‖ ≤ bumpLipConst w γ₀ * r := by
    refine hL.trans (mul_le_mul_of_nonneg_left hτ ?_)
    unfold bumpLipConst; positivity
  have hκτ : ‖κτ‖ ≤ ‖κ0‖ + bumpLipConst w γ₀ * r := by
    have := norm_le_insert' κτ κ0
    linarith [norm_sub_rev κτ κ0]
  have hAd : ‖Aτ - A0‖ ≤ β * ‖paperFT F (γ₀ : ℂ)‖ + 2 * εF := by
    have e : Aτ - A0 = (paperFT F (τ : ℂ) - paperFT F (γ₀ : ℂ)) -
        (paperFT (cutoffTail U F) (τ : ℂ) - paperFT (cutoffTail U F) (γ₀ : ℂ)) := by ring
    rw [e]
    refine (norm_sub_le _ _).trans ?_
    have := norm_sub_le (paperFT (cutoffTail U F) (τ : ℂ)) (paperFT (cutoffTail U F) (γ₀ : ℂ))
    linarith [hvar τ hτ]
  have hA0 : ‖A0‖ ≤ ‖paperFT F (γ₀ : ℂ)‖ + εF := by
    refine (norm_sub_le _ _).trans ?_; linarith
  have e : Aτ * κτ - A0 * κ0 = (Aτ - A0) * κτ + A0 * (κτ - κ0) := by ring
  rw [e]
  calc ‖(Aτ - A0) * κτ + A0 * (κτ - κ0)‖ ≤ ‖Aτ - A0‖ * ‖κτ‖ + ‖A0‖ * ‖κτ - κ0‖ := by
        refine (norm_add_le _ _).trans ?_; rw [norm_mul, norm_mul]
    _ ≤ (β * ‖paperFT F (γ₀ : ℂ)‖ + 2 * εF) * (‖κ0‖ + bumpLipConst w γ₀ * r) +
          (‖paperFT F (γ₀ : ℂ)‖ + εF) * (bumpLipConst w γ₀ * r) := by
        have h1 : 0 ≤ β * ‖paperFT F (γ₀ : ℂ)‖ + 2 * εF := le_trans (norm_nonneg _) hAd
        exact add_le_add (mul_le_mul hAd hκτ (norm_nonneg _) h1)
          (mul_le_mul hA0 hLr (norm_nonneg _) (le_trans (norm_nonneg _) hA0))

/-! ## The Weil form of the resolvent test -/

theorem one_half_add_I_mul_im_of_line {ρ₀ : ℂ} (hline : ρ₀.re = 1 / 2) :
    1 / 2 + I * ((ρ₀.im : ℝ) : ℂ) = ρ₀ := by
  apply Complex.ext <;> simp [hline]

theorem gammaOf_of_line {ρ₀ : ℂ} (hline : ρ₀.re = 1 / 2) : gammaOf ρ₀ = ((ρ₀.im : ℝ) : ℂ) := by
  have h1 := one_half_add_I_mul_gammaOf ρ₀
  have h2 := one_half_add_I_mul_im_of_line hline
  have : I * gammaOf ρ₀ = I * ((ρ₀.im : ℝ) : ℂ) := by linear_combination h1 - h2
  exact mul_left_cancel₀ Complex.I_ne_zero this

theorem reflect_of_line {ρ₀ : ℂ} (hline : ρ₀.re = 1 / 2) : Zeta23.reflect ρ₀ = ρ₀ := by
  unfold Zeta23.reflect
  apply Complex.ext
  · simp [hline]; norm_num
  · simp

/-- **The Weil form of the resolvent test.**  At every zero other than `ρ₀` both evaluation points
see only the tail of `F`, so
`| |W(f,f)| - m₀ |f̂(γ₀)|² | ≤ ε_F² B_w² (1+|γ₀|)⁴ · 24 A₀ log(|γ₀|+3)`. -/
theorem norm_W_resolventTest_sub_le {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (zetaZeroConfig.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3))
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : 2 * θ < π / 2) {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ zetaZeroConfig.carrier)
    (hline : ρ₀.re = 1 / 2) {m : ℕ} {F : ℝ → ℂ} (hF : SuperExpDecay F)
    (hprod : ∀ z : ℂ, (z - (ρ₀.im : ℂ)) ^ m * paperFT F z = paperFT (tiltedPhi θ) z)
    {U w : ℝ} (hw : 0 < w) (hw4 : 4 * w ≤ 1) :
    |‖zetaZeroConfig.W (bumpedTest (cutoffCore U F) w ρ₀.im)
        (bumpedTest (cutoffCore U F) w ρ₀.im)‖ -
      (zetaZeroConfig.mult ρ₀ : ℝ) *
        ‖paperFT (bumpedTest (cutoffCore U F) w ρ₀.im) ((ρ₀.im : ℝ) : ℂ)‖ ^ 2| ≤
      expTail F (1 / 2) U ^ 2 * scaledBumpConst w ^ 2 * (1 + |ρ₀.im|) ^ 4 *
        (24 * A₀ * Real.log (|ρ₀.im| + 3)) := by
  set γ₀ := ρ₀.im with hγ₀
  set f := bumpedTest (cutoffCore U F) w γ₀ with hf
  set εF := expTail F (1 / 2) U with hεF
  have hεF0 : 0 ≤ εF := expTail_nonneg _ _ _
  have hC := scaledBumpConst_nonneg hw
  have hsupp : ∀ u, U < |u| → cutoffCore U F u = 0 := fun u hu => cutoffCore_eq_zero hu
  have hint := integrable_cutoffCore (U := U) hF.1
  obtain ⟨hsumm, hsumle⟩ := window_tsum_le zetaZeroConfig hA₀ hloc γ₀
  set K := εF ^ 2 * scaledBumpConst w ^ 2 * (1 + |γ₀|) ^ 4 with hK
  have hK0 : 0 ≤ K := by positivity
  have hsγ := one_half_add_I_mul_im_of_line hline
  rw [← hγ₀] at hsγ
  -- vanishing of `F̂` at every other zero
  have hvan : ∀ x : ℂ, |x.im| ≤ 1 / 2 → x ≠ (γ₀ : ℂ) → riemannPhiTransform (1 / 2 + I * x) = 0 →
      paperFT F x = 0 := by
    intro x hx hne hzero
    have h := hprod x
    rw [paperFT_tiltedPhi hθ0 hθ hx, hzero, mul_zero] at h
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ (sub_ne_zero.mpr hne))
  have hRT : ∀ σ ∈ zetaZeroConfig.carrier, riemannPhiTransform σ = 0 := by
    intro σ hσ
    rw [zetaZeroConfig_carrier] at hσ
    exact riemannPhiTransform_eq_zero_of_nontrivial hσ.1 hσ.2.1 hσ.2.2
  have hval : ∀ x : ℂ, |x.im| ≤ 1 / 2 → paperFT F x = 0 →
      ‖paperFT f x‖ ≤ εF * (scaledBumpConst w * (1 + |γ₀|) ^ 2 / (1 + |x.re - γ₀|) ^ 2) := by
    intro x hx h0
    rw [hf, paperFT_bumpedTest hint hsupp hw, paperFT_cutoffCore_eq hF, h0, zero_sub, norm_mul,
      norm_neg]
    exact mul_le_mul (norm_paperFT_cutoffTail_le hF hx)
      (norm_paperFT_scaledBumpPolarFree_le hw hw4 γ₀ hx) (norm_nonneg _) hεF0
  set S : zetaZeroConfig.carrier → ℂ := fun ρ => zetaZeroConfig.Wsummand f f ρ with hS
  set T : zetaZeroConfig.carrier → ℂ := fun ρ => if ρ = ⟨ρ₀, hρ₀⟩ then 0 else S ρ with hT
  have hTpt : ∀ ρ : zetaZeroConfig.carrier,
      ‖T ρ‖ ≤ K * ((zetaZeroConfig.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - γ₀|) ^ 3) := by
    intro ρ
    by_cases hρρ : ρ = ⟨ρ₀, hρ₀⟩
    · simp only [hT, if_pos hρρ, norm_zero]; positivity
    · simp only [hT, if_neg hρρ, hS]
      have hne : (ρ : ℂ) ≠ ρ₀ := fun h => hρρ (Subtype.ext h)
      have hmem := ρ.2
      have hstrip' : 0 < (ρ : ℂ).re ∧ (ρ : ℂ).re < 1 := by
        have h : IsNontrivialZero (ρ : ℂ) := hmem
        exact ⟨h.2.1, h.2.2⟩
      have hIm : |(gammaOf (ρ : ℂ)).im| ≤ 1 / 2 := (WeilEF.abs_gammaOf_im_lt hstrip').le
      have hIm' : |((starRingEnd ℂ) (gammaOf (ρ : ℂ))).im| ≤ 1 / 2 := by
        rw [Complex.conj_im, abs_neg]; exact hIm
      have hre1 : (gammaOf (ρ : ℂ)).re = (ρ : ℂ).im := WeilEF.gammaOf_re _
      have hre2 : ((starRingEnd ℂ) (gammaOf (ρ : ℂ))).re = (ρ : ℂ).im := by
        rw [Complex.conj_re, WeilEF.gammaOf_re]
      have h1 : 1 / 2 + I * gammaOf (ρ : ℂ) = (ρ : ℂ) := one_half_add_I_mul_gammaOf _
      have h2 : 1 / 2 + I * (starRingEnd ℂ) (gammaOf (ρ : ℂ)) = Zeta23.reflect (ρ : ℂ) := by
        unfold gammaOf Zeta23.reflect
        apply Complex.ext
        · simp; ring
        · simp
      have hx1 : gammaOf (ρ : ℂ) ≠ (γ₀ : ℂ) := by
        intro h; apply hne; rw [← h1, h, hsγ]
      have hx2 : (starRingEnd ℂ) (gammaOf (ρ : ℂ)) ≠ (γ₀ : ℂ) := by
        intro h
        apply hne
        have h3 : Zeta23.reflect (ρ : ℂ) = ρ₀ := by rw [← h2, h, hsγ]
        rw [← reflect_reflect (ρ : ℂ), h3, reflect_of_line hline]
      have hF1 := hvan _ hIm hx1 (by rw [h1]; exact hRT _ hmem)
      have hF2 := hvan _ hIm' hx2 (by rw [h2]; exact hRT _ (zetaZeroConfig.reflect_mem _ hmem))
      have hv1 := hval _ hIm hF1
      have hv2 := hval _ hIm' hF2
      rw [hre1] at hv1; rw [hre2] at hv2
      unfold ZeroConfig.Wsummand
      rw [norm_mul, norm_mul, Complex.norm_natCast, RCLike.norm_conj]
      have hm : (0 : ℝ) ≤ zetaZeroConfig.mult ρ := Nat.cast_nonneg _
      set D := 1 + |(ρ : ℂ).im - γ₀| with hD
      have hD1 : 1 ≤ D := by rw [hD]; linarith [abs_nonneg ((ρ : ℂ).im - γ₀)]
      have hq : εF * (scaledBumpConst w * (1 + |γ₀|) ^ 2 / D ^ 2) *
          (εF * (scaledBumpConst w * (1 + |γ₀|) ^ 2 / D ^ 2)) ≤ K * (1 / D ^ 3) := by
        rw [hK]
        have hD4 : D ^ 3 ≤ D ^ 4 := pow_le_pow_right₀ hD1 (by norm_num)
        have e : εF * (scaledBumpConst w * (1 + |γ₀|) ^ 2 / D ^ 2) *
            (εF * (scaledBumpConst w * (1 + |γ₀|) ^ 2 / D ^ 2)) =
            εF ^ 2 * scaledBumpConst w ^ 2 * (1 + |γ₀|) ^ 4 * (1 / D ^ 4) := by
          field_simp
        rw [e]
        apply mul_le_mul_of_nonneg_left _ hK0
        exact one_div_le_one_div_of_le (by positivity) hD4
      calc (zetaZeroConfig.mult ρ : ℝ) * ‖paperFT f (gammaOf ρ)‖ *
            ‖paperFT f ((starRingEnd ℂ) (gammaOf ρ))‖
          ≤ (zetaZeroConfig.mult ρ : ℝ) * (εF * (scaledBumpConst w * (1 + |γ₀|) ^ 2 / D ^ 2)) *
              (εF * (scaledBumpConst w * (1 + |γ₀|) ^ 2 / D ^ 2)) := by gcongr
        _ = (zetaZeroConfig.mult ρ : ℝ) * (εF * (scaledBumpConst w * (1 + |γ₀|) ^ 2 / D ^ 2) *
              (εF * (scaledBumpConst w * (1 + |γ₀|) ^ 2 / D ^ 2))) := by ring
        _ ≤ (zetaZeroConfig.mult ρ : ℝ) * (K * (1 / D ^ 3)) := mul_le_mul_of_nonneg_left hq hm
        _ = K * ((zetaZeroConfig.mult ρ : ℝ) / D ^ 3) := by ring
  have hTsum : Summable (fun ρ => ‖T ρ‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hTpt (hsumm.mul_left _)
  have hTs : Summable T := hTsum.of_norm
  have hSs : Summable S := by
    have hsingle : Summable (fun ρ : zetaZeroConfig.carrier =>
        if ρ = ⟨ρ₀, hρ₀⟩ then S ⟨ρ₀, hρ₀⟩ else 0) :=
      summable_of_ne_finset_zero (s := {⟨ρ₀, hρ₀⟩}) fun ρ hρ => by
        rw [Finset.mem_singleton] at hρ; rw [if_neg hρ]
    refine (hTs.add hsingle).congr fun ρ => ?_
    simp only [hT]
    split_ifs with h
    · rw [h]; ring
    · ring
  have hsplit := hSs.tsum_eq_add_tsum_ite ⟨ρ₀, hρ₀⟩
  have hW : zetaZeroConfig.W f f = S ⟨ρ₀, hρ₀⟩ + ∑' ρ, T ρ := by
    unfold ZeroConfig.W; exact hsplit
  have hS0 : S ⟨ρ₀, hρ₀⟩ = ((zetaZeroConfig.mult ρ₀ : ℝ) * ‖paperFT f (γ₀ : ℂ)‖ ^ 2 : ℝ) := by
    simp only [hS]
    unfold ZeroConfig.Wsummand
    rw [gammaOf_of_line hline, ← hγ₀, Complex.conj_ofReal, mul_assoc, Complex.mul_conj,
      Complex.normSq_eq_norm_sq]
    push_cast; ring
  have hTle : ‖∑' ρ, T ρ‖ ≤ K * (24 * A₀ * Real.log (|γ₀| + 3)) := by
    refine (norm_tsum_le_tsum_norm hTsum).trans ?_
    refine (Summable.tsum_le_tsum hTpt hTsum (hsumm.mul_left _)).trans ?_
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left hsumle hK0
  rw [hW, hS0]
  have hmain : ‖(((zetaZeroConfig.mult ρ₀ : ℝ) * ‖paperFT f (γ₀ : ℂ)‖ ^ 2 : ℝ) : ℂ)‖ =
      (zetaZeroConfig.mult ρ₀ : ℝ) * ‖paperFT f (γ₀ : ℂ)‖ ^ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have := abs_norm_sub_norm_le ((((zetaZeroConfig.mult ρ₀ : ℝ) * ‖paperFT f (γ₀ : ℂ)‖ ^ 2 : ℝ) :
    ℂ) + ∑' ρ, T ρ) (((zetaZeroConfig.mult ρ₀ : ℝ) * ‖paperFT f (γ₀ : ℂ)‖ ^ 2 : ℝ) : ℂ)
  rw [hmain, add_sub_cancel_left] at this
  calc _ ≤ ‖∑' ρ, T ρ‖ := this
    _ ≤ K * (24 * A₀ * Real.log (|γ₀| + 3)) := hTle
    _ = _ := by rw [hK]

end

end RHTower
