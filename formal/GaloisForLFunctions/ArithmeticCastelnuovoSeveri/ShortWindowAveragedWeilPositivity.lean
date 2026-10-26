import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.ZeroDensityFilteredWeilPositivityAndCoercivity
import GaloisForLFunctions.RHTower.SelbergShortWindowNearLineDensity
import GaloisForLFunctions.RHTower.LorentzianZeroMass
import GaloisForLFunctions.RHTower.ZetaLocalWindowTail
import GaloisForLFunctions.RHTower.XiZeroCountLocalCeiling
import GaloisForLFunctions.RHTower.XiCensusVonMangoldtBridge

/-!
# Averaged Weil positivity on windows of length `Γ^{99/100}`

`exists_logarithmic_aperture_frequencyAverage_quadrature_pos` proves positivity of the complete
Weil form at logarithmic aperture after averaging the carrier frequency over `[Γ, 2Γ]`. This module
shortens the window to `[Γ, Γ + H]` for every `Γ^{99/100} ≤ H ≤ Γ/8`
(`exists_shortWindow_frequencyAverage_quadrature_pos`):

`(1/H) ∫_Γ^{Γ+H} [Q(F₀ cos γ·) + Q(F₀ sin γ·)] dγ ≥ (1/16) log Γ ‖F₀‖² − C₀ Γ^{−1/2} N(F₀)²`

for `0 ≤ A ≤ κ₀ log Γ` and real `F₀ ∈ C²_c([−A, A])`, `N` the envelope norm.

The dyadic window entered the dyadic proof in four places, and each has a short-window form.

* **Remote zeros** (`integral_window_tsum_depthDiff_le`). A zero at distance `≥ H` from the window
  contributes at most `e^A N² H^{−2}` times its Lorentzian mass term, and the Lorentzian mass of all
  zeros at height `t` is `O(log t)` (`lorentzMass_le_log`).
* **The core** (`integral_window_norm_paperFT_depthSum_sq_ge`, `exists_window_core_count`). A zero
  with ordinate in `[Γ + H/4, Γ + 3H/4]` contributes at least `2π‖F₀‖² − O(e^A N² H^{−2})`, and by
  Riemann–von Mangoldt on short windows there are `≥ H log Γ/(16π)` of them.
* **Near-line zeros** (`exists_window_shell_le`). On `[Γ − H, Γ + 2H]` the zeros within
  `C₂/log Γ` of the line cost `O(κ₀²)` each and number `O(H log Γ)`; the deeper ones are paid by
  Selberg's near-line density on windows of length `U^{99/100}`
  (`RHTower.exists_shortWindowZeros_weighted_le`).

So the positivity theorem needs zero density only on windows of length `Γ^{99/100}`: the averaged
positivity of the complete Weil form selects every window of that length.
-/

open Complex MeasureTheory Real Set Filter Topology Finset
open scoped BigOperators Real ComplexConjugate
open Zeta23 RHTower GaloisForLFunctions.ArithmeticCriticalityTheory
  GaloisForLFunctions.ArithmeticPositivityTheory
  GaloisForLFunctions.BiScaleUncertainty

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-! ### 1. Lorentzian bounds for one zero -/

private theorem gammaOf_sub_real' (ρ : ℂ) (ω : ℝ) :
    gammaOf ρ - (ω : ℂ) = ((ρ.im - ω : ℝ) : ℂ) - ((ρ.re - 1 / 2 : ℝ) : ℂ) * Complex.I := by
  rw [gammaOf, Complex.div_I]
  apply Complex.ext <;> simp

private theorem conj_gammaOf_sub_real' (ρ : ℂ) (ω : ℝ) :
    conj (gammaOf ρ) - (ω : ℂ) = ((ρ.im - ω : ℝ) : ℂ) + ((ρ.re - 1 / 2 : ℝ) : ℂ) * Complex.I := by
  rw [gammaOf, Complex.div_I]
  apply Complex.ext <;> simp

/-- Both reflected transforms of a strip zero obey the Lorentzian bound
`e^{A/2} N / (1 + (Im ρ − ω)²)`. -/
private theorem norm_paperFT_gammaOf_le {F₀ : ℝ → ℝ} (hF₀ : ContDiff ℝ 2 F₀)
    (hF₀c : HasCompactSupport F₀) {A : ℝ} (hA : 0 ≤ A) (hsupp : ∀ u : ℝ, A < |u| → F₀ u = 0)
    {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) (ω : ℝ) :
    ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf ρ - (ω : ℂ))‖ ≤
        Real.exp (A / 2) * envelopeWindowNorm F₀ / (1 + (ρ.im - ω) ^ 2) ∧
      ‖paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf ρ) - (ω : ℂ))‖ ≤
        Real.exp (A / 2) * envelopeWindowNorm F₀ / (1 + (ρ.im - ω) ^ 2) := by
  have him1 : |(gammaOf ρ - (ω : ℂ)).im| ≤ 1 / 2 := by
    rw [gammaOf_sub_real']; simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_sub, abs_neg]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have him2 : |(conj (gammaOf ρ) - (ω : ℂ)).im| ≤ 1 / 2 := by
    rw [conj_gammaOf_sub_real']; simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hre1 : (gammaOf ρ - (ω : ℂ)).re = ρ.im - ω := by rw [gammaOf_sub_real']; simp
  have hre2 : (conj (gammaOf ρ) - (ω : ℂ)).re = ρ.im - ω := by rw [conj_gammaOf_sub_real']; simp
  have hb1 := norm_paperFT_symm_le hF₀ hF₀c hA hsupp (gammaOf ρ - (ω : ℂ))
  have hb2 := norm_paperFT_symm_le hF₀ hF₀c hA hsupp (conj (gammaOf ρ) - (ω : ℂ))
  rw [hre1] at hb1; rw [hre2] at hb2
  have hexp1 : Real.exp (A * |(gammaOf ρ - (ω : ℂ)).im|) ≤ Real.exp (A / 2) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hexp2 : Real.exp (A * |(conj (gammaOf ρ) - (ω : ℂ)).im|) ≤ Real.exp (A / 2) :=
    Real.exp_le_exp.mpr (by nlinarith)
  exact ⟨hb1.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hexp1 (envelopeWindowNorm_nonneg F₀)) (by positivity)),
    hb2.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hexp2 (envelopeWindowNorm_nonneg F₀)) (by positivity))⟩

/-- **Lorentzian bound for the depth difference.** For a strip zero `ρ`,
`‖F̂(γ_ρ − ω) − F̂(γ̄_ρ − ω)‖²/4 ≤ e^A N² (1 + (Im ρ − ω)²)^{−2}`. -/
theorem norm_sq_depthDiff_div_four_le_lorentz {F₀ : ℝ → ℝ} (hF₀ : ContDiff ℝ 2 F₀)
    (hF₀c : HasCompactSupport F₀) {A : ℝ} (hA : 0 ≤ A) (hsupp : ∀ u : ℝ, A < |u| → F₀ u = 0)
    {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) (ω : ℝ) :
    ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf ρ - (ω : ℂ)) -
        paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf ρ) - (ω : ℂ))‖ ^ 2 / 4 ≤
      Real.exp A * envelopeWindowNorm F₀ ^ 2 * (1 / (1 + (ρ.im - ω) ^ 2) ^ 2) := by
  obtain ⟨h1, h2⟩ := norm_paperFT_gammaOf_le hF₀ hF₀c hA hsupp hρ0 hρ1 ω
  have htri := (norm_sub_le _ _).trans (add_le_add h1 h2)
  have hsq := pow_le_pow_left₀ (norm_nonneg _) htri 2
  have hexpA : Real.exp (A / 2) ^ 2 = Real.exp A := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  have hd : 0 < 1 + (ρ.im - ω) ^ 2 := by positivity
  calc _ ≤ (Real.exp (A / 2) * envelopeWindowNorm F₀ / (1 + (ρ.im - ω) ^ 2) +
          Real.exp (A / 2) * envelopeWindowNorm F₀ / (1 + (ρ.im - ω) ^ 2)) ^ 2 / 4 :=
        div_le_div_of_nonneg_right hsq (by norm_num)
    _ = Real.exp (A / 2) ^ 2 * envelopeWindowNorm F₀ ^ 2 * (1 / (1 + (ρ.im - ω) ^ 2) ^ 2) := by
        have hdne : 1 + (ρ.im - ω) ^ 2 ≠ 0 := hd.ne'
        field_simp <;> ring
    _ = _ := by rw [hexpA]

/-- Lorentzian bound for the depth sum `paperFT (depthSumProfile F₀ ρ) (−ω)`. -/
private theorem norm_sq_depthSum_le_lorentz {F₀ : ℝ → ℝ} (hF₀ : ContDiff ℝ 2 F₀)
    (hF₀c : HasCompactSupport F₀) {A : ℝ} (hA : 0 ≤ A) (hsupp : ∀ u : ℝ, A < |u| → F₀ u = 0)
    {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) (ω : ℝ) :
    ‖paperFT (depthSumProfile F₀ ρ) (-(ω : ℂ))‖ ^ 2 ≤
      Real.exp A * envelopeWindowNorm F₀ ^ 2 * (1 / (1 + (ρ.im - ω) ^ 2) ^ 2) := by
  rw [paperFT_depthSumProfile_eq hF₀.continuous hF₀c ρ ω]
  obtain ⟨h1, h2⟩ := norm_paperFT_gammaOf_le hF₀ hF₀c hA hsupp hρ0 hρ1 ω
  have htri : ‖(paperFT (fun u => (F₀ u : ℂ)) (gammaOf ρ - (ω : ℂ)) +
        paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf ρ) - (ω : ℂ))) / 2‖ ≤
      Real.exp (A / 2) * envelopeWindowNorm F₀ / (1 + (ρ.im - ω) ^ 2) := by
    rw [norm_div, Complex.norm_ofNat]
    linarith [norm_add_le (paperFT (fun u => (F₀ u : ℂ)) (gammaOf ρ - (ω : ℂ)))
      (paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf ρ) - (ω : ℂ)))]
  have hsq := pow_le_pow_left₀ (norm_nonneg _) htri 2
  have hexpA : Real.exp (A / 2) ^ 2 = Real.exp A := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  calc _ ≤ (Real.exp (A / 2) * envelopeWindowNorm F₀ / (1 + (ρ.im - ω) ^ 2)) ^ 2 := hsq
    _ = Real.exp (A / 2) ^ 2 * envelopeWindowNorm F₀ ^ 2 * (1 / (1 + (ρ.im - ω) ^ 2) ^ 2) := by
        rw [div_pow, mul_pow, mul_one_div]
    _ = _ := by rw [hexpA]

/-! ### 2. Remote zeros -/

/-- `1/(1 + x²)² ≤ (1/H²) · 1/(1 + x²)` once `|x| ≥ H > 0`. -/
private theorem lorentz_sq_le_of_far {x H : ℝ} (hH : 0 < H) (hx : H ≤ |x|) :
    1 / (1 + x ^ 2) ^ 2 ≤ (1 / H ^ 2) * (1 / (1 + x ^ 2)) := by
  have hx2 : H ^ 2 ≤ x ^ 2 := by
    rw [← sq_abs x]; exact pow_le_pow_left₀ hH.le hx 2
  have hd : 0 < 1 + x ^ 2 := by positivity
  rw [show (1 : ℝ) / (1 + x ^ 2) ^ 2 = (1 / (1 + x ^ 2)) * (1 / (1 + x ^ 2)) by ring]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  rw [div_le_div_iff₀ hd (by positivity)]
  linarith

/-- The depth-difference term of one zero at frequency `γ`. -/
private def ddt (F₀ : ℝ → ℝ) (z : ℂ) (γ : ℝ) : ℝ :=
  ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf z - (γ : ℂ)) -
    paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf z) - (γ : ℂ))‖ ^ 2 / 4

/-- **Window master bound.** On `[Γ, Γ + H]`, the depth-difference series is at most the sum over
the zeros with ordinate in `[Γ − H, Γ + 2H]` plus a remote tail `8 (C + log(2Γ + 4)) e^A N²/H`. -/
theorem integral_window_tsum_depthDiff_le {F₀ : ℝ → ℝ} (hF₀ : ContDiff ℝ 2 F₀)
    (hF₀c : HasCompactSupport F₀) {Γ H A : ℝ} (hΓ : 1 ≤ Γ) (hH : 0 < H) (hHΓ : H ≤ Γ / 2)
    (hA : 0 ≤ A) (hsupp : ∀ u : ℝ, A < |u| → F₀ u = 0) :
    ∃ G_loc : Finset XiZeroCopy,
      (∀ q ∈ G_loc, Γ - H ≤ (q.1 : ℂ).im ∧ (q.1 : ℂ).im ≤ Γ + 2 * H) ∧
      IntegrableOn (fun γ : ℝ => ∑' ρ : zetaZeroConfig.carrier,
        (zetaZeroConfig.mult ρ : ℝ) *
          ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (ρ : ℂ) - (γ : ℂ)) -
            paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (ρ : ℂ)) - (γ : ℂ))‖ ^ 2 / 4)
        (Icc Γ (Γ + H)) ∧
      (∫ γ in Icc Γ (Γ + H), ∑' ρ : zetaZeroConfig.carrier,
        (zetaZeroConfig.mult ρ : ℝ) *
          ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (ρ : ℂ) - (γ : ℂ)) -
            paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (ρ : ℂ)) - (γ : ℂ))‖ ^ 2 / 4) ≤
        (∑ q ∈ G_loc,
          (∫ γ in Icc Γ (Γ + H),
            ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (q.1 : ℂ) - (γ : ℂ)) -
              paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (q.1 : ℂ)) - (γ : ℂ))‖ ^ 2) / 4) +
          (8 * (xiLineTwoLogDerivConstant + Real.log (2 * Γ + 4)) / H) *
            Real.exp A * envelopeWindowNorm F₀ ^ 2 := by
  classical
  obtain ⟨-, -, hc_sub, -, -⟩ := integral_Icc_tsum_depthDiff_div_four_le hF₀ hF₀c hΓ hA hsupp
  have hd_cont : ∀ z : ℂ, Continuous (ddt F₀ z) := fun z => by unfold ddt; fun_prop
  have hd_nn : ∀ z γ, 0 ≤ ddt F₀ z γ := fun _ _ => by unfold ddt; positivity
  have hS_fin : ({q : XiZeroCopy | Γ - H ≤ (q.1 : ℂ).im ∧ (q.1 : ℂ).im ≤ Γ + 2 * H}).Finite :=
    (finite_xiOrdinateWindow (Γ + 2 * H) 0).subset fun q hq => by
      rw [mem_xiOrdinateWindow_iff, sub_zero, abs_le]
      exact ⟨by linarith [hq.1], hq.2⟩
  obtain ⟨G_loc, hmem_Gloc⟩ : ∃ G_loc : Finset XiZeroCopy,
      ∀ q : XiZeroCopy, q ∈ G_loc ↔ Γ - H ≤ (q.1 : ℂ).im ∧ (q.1 : ℂ).im ≤ Γ + 2 * H :=
    ⟨hS_fin.toFinset, fun _ => hS_fin.mem_toFinset⟩
  have hwin_sub : Icc Γ (Γ + H) ⊆ Icc Γ (2 * Γ) := Icc_subset_Icc le_rfl (by linarith)
  have hint_tsum := (hc_sub.mono hwin_sub).integrableOn_Icc
  set B : ℝ := Real.exp A * envelopeWindowNorm F₀ ^ 2 *
    (8 * (xiLineTwoLogDerivConstant + Real.log (2 * Γ + 4))) / H ^ 2 with hB
  have hstrip : ∀ q : XiZeroCopy, 0 < (q.1 : ℂ).re ∧ (q.1 : ℂ).re < 1 :=
    fun q => xi_divisor_support_re_mem_open_unit q.1
  -- Pointwise split into local zeros and a Lorentzian tail.
  have hpt : ∀ γ ∈ Icc Γ (Γ + H),
      (∑' ρ : zetaZeroConfig.carrier, (zetaZeroConfig.mult ρ : ℝ) *
          ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (ρ : ℂ) - (γ : ℂ)) -
            paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (ρ : ℂ)) - (γ : ℂ))‖ ^ 2 / 4) ≤
        (∑ q ∈ G_loc, ddt F₀ (q.1 : ℂ) γ) + B := by
    intro γ hγ
    have hdom : ∀ q : XiZeroCopy, ddt F₀ (q.1 : ℂ) γ ≤
        Real.exp A * envelopeWindowNorm F₀ ^ 2 * lorentzMassTerm γ q := fun q => by
      have h := norm_sq_depthDiff_div_four_le_lorentz hF₀ hF₀c hA hsupp (hstrip q).1 (hstrip q).2 γ
      refine h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
      unfold lorentzMassTerm
      rw [show (γ - (q.1 : ℂ).im) ^ 2 = ((q.1 : ℂ).im - γ) ^ 2 by ring]
      have hpos : 0 < 1 + ((q.1 : ℂ).im - γ) ^ 2 := by positivity
      rw [div_le_div_iff₀ (by positivity) hpos]
      nlinarith [sq_nonneg ((q.1 : ℂ).im - γ)]
    have hsum_q : Summable fun q : XiZeroCopy => ddt F₀ (q.1 : ℂ) γ :=
      ((summable_lorentzMassTerm γ).mul_left
        (Real.exp A * envelopeWindowNorm F₀ ^ 2)).of_nonneg_of_le (fun q => hd_nn _ _) hdom
    have hbridge : (∑' q : XiZeroCopy, ddt F₀ (q.1 : ℂ) γ) =
        ∑' ρ : zetaZeroConfig.carrier, (zetaZeroConfig.mult ρ : ℝ) * ddt F₀ (ρ : ℂ) γ :=
      tsum_xiZeroCopy_eq_zetaCarrier (g := fun z => ddt F₀ z γ) hsum_q
    have hform : (∑' ρ : zetaZeroConfig.carrier, (zetaZeroConfig.mult ρ : ℝ) *
          ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (ρ : ℂ) - (γ : ℂ)) -
            paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (ρ : ℂ)) - (γ : ℂ))‖ ^ 2 / 4) =
        ∑' ρ : zetaZeroConfig.carrier, (zetaZeroConfig.mult ρ : ℝ) * ddt F₀ (ρ : ℂ) γ :=
      tsum_congr fun ρ => by unfold ddt; ring
    rw [hform, ← hbridge, ← hsum_q.sum_add_tsum_subtype_compl G_loc]
    refine add_le_add le_rfl ?_
    have hfar : ∀ q : {q : XiZeroCopy // q ∉ G_loc}, ddt F₀ ((q : XiZeroCopy).1 : ℂ) γ ≤
        (Real.exp A * envelopeWindowNorm F₀ ^ 2 / H ^ 2) * lorentzMassTerm γ q := fun q => by
      have hq := q.2
      rw [hmem_Gloc, not_and_or] at hq
      have hfarx : H ≤ |((q : XiZeroCopy).1 : ℂ).im - γ| := by
        rcases hq with h | h
        · rw [abs_sub_comm, abs_of_nonneg (by linarith [hγ.1, not_le.mp h])]
          linarith [hγ.1, not_le.mp h]
        · rw [abs_of_nonneg (by linarith [hγ.2, not_le.mp h])]
          linarith [hγ.2, not_le.mp h]
      have h := norm_sq_depthDiff_div_four_le_lorentz hF₀ hF₀c hA hsupp
        (hstrip q).1 (hstrip q).2 γ
      have hl := lorentz_sq_le_of_far hH hfarx
      have hterm : lorentzMassTerm γ q = 1 / (1 + (((q : XiZeroCopy).1 : ℂ).im - γ) ^ 2) := by
        unfold lorentzMassTerm
        rw [show (γ - ((q : XiZeroCopy).1 : ℂ).im) ^ 2 =
          (((q : XiZeroCopy).1 : ℂ).im - γ) ^ 2 by ring]
      rw [hterm]
      calc ddt F₀ ((q : XiZeroCopy).1 : ℂ) γ
          ≤ Real.exp A * envelopeWindowNorm F₀ ^ 2 *
            (1 / (1 + (((q : XiZeroCopy).1 : ℂ).im - γ) ^ 2) ^ 2) := h
        _ ≤ Real.exp A * envelopeWindowNorm F₀ ^ 2 *
            ((1 / H ^ 2) * (1 / (1 + (((q : XiZeroCopy).1 : ℂ).im - γ) ^ 2))) :=
            mul_le_mul_of_nonneg_left hl (by positivity)
        _ = _ := by ring
    have hsum_far : Summable fun q : {q : XiZeroCopy // q ∉ G_loc} =>
        (Real.exp A * envelopeWindowNorm F₀ ^ 2 / H ^ 2) * lorentzMassTerm γ q :=
      ((summable_lorentzMassTerm γ).subtype {q | q ∉ G_loc}).mul_left _
    have hmass_sub : (∑' q : {q : XiZeroCopy // q ∉ G_loc}, lorentzMassTerm γ q) ≤
        lorentzMass γ :=
      Summable.tsum_subtype_le (lorentzMassTerm γ) {q | q ∉ G_loc}
        (fun q => lorentzMassTerm_nonneg γ q) (summable_lorentzMassTerm γ)
    have hlog : lorentzMass γ ≤ 8 * (xiLineTwoLogDerivConstant + Real.log (2 * Γ + 4)) := by
      refine (lorentzMass_le_log γ).trans ?_
      have hγpos : 0 ≤ γ := by linarith [hγ.1]
      have hle : |γ| + 4 ≤ 2 * Γ + 4 := by rw [abs_of_nonneg hγpos]; linarith [hγ.2]
      have := Real.log_le_log (by positivity) hle
      linarith
    calc (∑' q : {q : XiZeroCopy // q ∉ G_loc}, ddt F₀ ((q : XiZeroCopy).1 : ℂ) γ)
        ≤ ∑' q : {q : XiZeroCopy // q ∉ G_loc},
            (Real.exp A * envelopeWindowNorm F₀ ^ 2 / H ^ 2) * lorentzMassTerm γ q :=
          Summable.tsum_le_tsum hfar (hsum_q.subtype {q | q ∉ G_loc}) hsum_far
      _ = (Real.exp A * envelopeWindowNorm F₀ ^ 2 / H ^ 2) *
            ∑' q : {q : XiZeroCopy // q ∉ G_loc}, lorentzMassTerm γ q := tsum_mul_left
      _ ≤ (Real.exp A * envelopeWindowNorm F₀ ^ 2 / H ^ 2) *
            (8 * (xiLineTwoLogDerivConstant + Real.log (2 * Γ + 4))) :=
          mul_le_mul_of_nonneg_left (hmass_sub.trans hlog) (by positivity)
      _ = B := by rw [hB]; ring
  have hfin_int : IntegrableOn (fun γ : ℝ => ∑ q ∈ G_loc, ddt F₀ (q.1 : ℂ) γ) (Icc Γ (Γ + H)) :=
    (continuous_finsetSum G_loc fun q _ => hd_cont (q.1 : ℂ)).integrableOn_Icc
  have hrhs_int : IntegrableOn (fun γ : ℝ => (∑ q ∈ G_loc, ddt F₀ (q.1 : ℂ) γ) + B)
      (Icc Γ (Γ + H)) := hfin_int.add continuous_const.integrableOn_Icc
  refine ⟨G_loc, fun q hq => (hmem_Gloc q).mp hq, hint_tsum, ?_⟩
  have hmono := setIntegral_mono_on hint_tsum hrhs_int measurableSet_Icc hpt
  refine hmono.trans (le_of_eq ?_)
  rw [integral_add hfin_int continuous_const.integrableOn_Icc,
    integral_finsetSum G_loc fun q _ => (hd_cont (q.1 : ℂ)).integrableOn_Icc, setIntegral_const,
    Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith),
    show Γ + H - Γ = H by ring, smul_eq_mul]
  congr 1
  · refine Finset.sum_congr rfl fun q _ => ?_
    unfold ddt
    rw [integral_div]
  · rw [hB]
    field_simp <;> ring

/-! ### 3. The core -/

private theorem depthSumProfile_plancherel' {F₀ : ℝ → ℝ}
    (hF₀ : Continuous F₀) (hF₀c : HasCompactSupport F₀) (ρ : ℂ) :
    Continuous (fun γ : ℝ => ‖paperFT (depthSumProfile F₀ ρ) (-(γ : ℂ))‖ ^ 2) ∧
    Integrable (fun γ : ℝ => ‖paperFT (depthSumProfile F₀ ρ) (-(γ : ℂ))‖ ^ 2) ∧
    2 * Real.pi * (∫ u, F₀ u ^ 2) ≤
      ∫ γ : ℝ, ‖paperFT (depthSumProfile F₀ ρ) (-(γ : ℂ))‖ ^ 2 := by
  let h := depthSumProfile F₀ ρ
  have hh_cont : Continuous h := by unfold h depthSumProfile; fun_prop
  have hh_comp : HasCompactSupport h := by
    unfold h depthSumProfile
    exact ((hF₀c.mul_right).comp_left Complex.ofReal_zero).mul_right
  have hh1 : Integrable h := hh_cont.integrable_of_hasCompactSupport hh_comp
  have hint_h2 : Integrable fun u : ℝ => ‖h u‖ ^ 2 :=
    (hh_cont.norm.pow 2).integrable_of_hasCompactSupport
      ((hh_comp.norm).comp_left (zero_pow two_ne_zero))
  have hh2 : MemLp h 2 :=
    (memLp_two_iff_integrable_sq_norm hh_cont.aestronglyMeasurable).mpr hint_h2
  have hft_cont : Continuous fun x : ℝ => paperFT h (x : ℂ) := by
    have hint_h : Integrable fun u : ℝ => ‖h u‖ := hh1.norm
    rw [continuous_iff_continuousAt]
    intro x₀
    refine continuousAt_of_dominated (bound := fun u : ℝ => ‖h u‖)
      (Eventually.of_forall fun x => (hh_cont.mul (by fun_prop)).aestronglyMeasurable)
      (Eventually.of_forall fun x => Eventually.of_forall fun u => ?_)
      hint_h (Eventually.of_forall fun u => by fun_prop)
    have hexp1 : ‖Complex.exp (Complex.I * (x : ℂ) * (u : ℂ))‖ = 1 := by
      have : Complex.I * (x : ℂ) * (u : ℂ) = ((x * u : ℝ) : ℂ) * Complex.I := by push_cast; ring
      rw [this, Complex.norm_exp_ofReal_mul_I]
    rw [norm_mul, hexp1, mul_one]
  have heq_m : (fun γ : ℝ => ‖paperFT h (-(γ : ℂ))‖ ^ 2) =
      fun γ : ℝ => ‖paperFT h ((-γ : ℝ) : ℂ)‖ ^ 2 := by funext γ; simp
  have hc_minus : Continuous fun γ : ℝ => ‖paperFT h (-(γ : ℂ))‖ ^ 2 := by
    rw [heq_m]; exact ((hft_cont.comp continuous_neg).norm).pow 2
  have hint_pos : Integrable fun x : ℝ => ‖paperFT h (x : ℂ)‖ ^ 2 := by
    have hfun : (fun x : ℝ => ‖paperFT h (x : ℂ)‖ ^ 2) =
        fun x => (fun ξ : ℝ => ‖FourierTransform.fourier h ξ‖ ^ 2) (x / (-(2 * Real.pi))) := by
      funext x; rw [paperFT_ofReal_eq_fourier, neg_div, ← div_neg]
    rw [hfun]
    exact (GaloisForLFunctions.RHTower.integrable_norm_sq_fourier hh1 hh2).comp_div
      (by linarith [Real.pi_pos])
  have hint_minus : Integrable fun γ : ℝ => ‖paperFT h (-(γ : ℂ))‖ ^ 2 := by
    rw [heq_m]; exact hint_pos.comp_neg
  have hwhole : (∫ γ : ℝ, ‖paperFT h (-(γ : ℂ))‖ ^ 2) = 2 * Real.pi * ∫ u : ℝ, ‖h u‖ ^ 2 := by
    rw [heq_m, integral_neg_eq_self (fun x : ℝ => ‖paperFT h (x : ℂ)‖ ^ 2)]
    exact RHTower.KernelStrip.integral_norm_sq_paperFT_of_memLp hh1 hh2
  have hint_F₀2 : Integrable fun u : ℝ => F₀ u ^ 2 :=
    (hF₀.pow 2).integrable_of_hasCompactSupport (hF₀c.comp_left (zero_pow two_ne_zero))
  have hL2_ge : (∫ u : ℝ, F₀ u ^ 2) ≤ ∫ u : ℝ, ‖h u‖ ^ 2 := by
    refine integral_mono hint_F₀2 hint_h2 fun u => ?_
    dsimp [h, depthSumProfile]
    have hexp_norm : ‖Complex.exp (Complex.I * (ρ.im : ℂ) * (u : ℂ))‖ = 1 := by
      have : Complex.I * (ρ.im : ℂ) * (u : ℂ) = ((ρ.im * u : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      rw [this, Complex.norm_exp_ofReal_mul_I]
    rw [norm_mul, hexp_norm, mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow]
    exact le_mul_of_one_le_right (sq_nonneg _) (one_le_cosh_sq ((ρ.re - 1 / 2) * u))
  refine ⟨hc_minus, hint_minus, ?_⟩
  rw [hwhole]
  exact mul_le_mul_of_nonneg_left hL2_ge (by positivity)

/-- **Per-zero core bound.** A strip zero with ordinate in `[Γ + H/4, Γ + 3H/4]` contributes at
least `2π‖F₀‖² − (16π/H²) e^A N²` to the depth-sum integral over `[Γ, Γ + H]`. -/
theorem integral_window_norm_paperFT_depthSum_sq_ge {F₀ : ℝ → ℝ}
    (hF₀ : ContDiff ℝ 2 F₀) (hF₀c : HasCompactSupport F₀)
    {Γ H A : ℝ} (hH : 0 < H) (hA : 0 ≤ A) (hsupp : ∀ u : ℝ, A < |u| → F₀ u = 0)
    {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1)
    (hρ_im1 : Γ + H / 4 ≤ ρ.im) (hρ_im2 : ρ.im ≤ Γ + 3 * H / 4) :
    Continuous (fun γ : ℝ => ‖paperFT (depthSumProfile F₀ ρ) (-(γ : ℂ))‖ ^ 2) ∧
    2 * Real.pi * (∫ u, F₀ u ^ 2) -
        (16 * Real.pi / H ^ 2) * Real.exp A * envelopeWindowNorm F₀ ^ 2 ≤
      (∫ γ in Icc Γ (Γ + H), ‖paperFT (depthSumProfile F₀ ρ) (-(γ : ℂ))‖ ^ 2) := by
  obtain ⟨hc_minus, hint_minus, hpl_ge⟩ := depthSumProfile_plancherel' hF₀.continuous hF₀c ρ
  have hint_lor : Integrable fun γ : ℝ => 1 / (1 + (ρ.im - γ) ^ 2) := by
    have heq : (fun γ : ℝ => 1 / (1 + (ρ.im - γ) ^ 2)) = fun γ : ℝ => (1 + (γ - ρ.im) ^ 2)⁻¹ := by
      funext γ; simp only [one_div]; congr 2; ring
    rw [heq]
    exact integrable_inv_one_add_sq.comp_sub_right ρ.im
  have hint_lor_val : (∫ γ : ℝ, 1 / (1 + (ρ.im - γ) ^ 2)) = Real.pi := by
    have heq : (fun γ : ℝ => 1 / (1 + (ρ.im - γ) ^ 2)) = fun γ : ℝ => (1 + (γ - ρ.im) ^ 2)⁻¹ := by
      funext γ; simp only [one_div]; congr 2; ring
    rw [heq, integral_sub_right_eq_self (fun u : ℝ => (1 + u ^ 2)⁻¹) ρ.im]
    exact integral_univ_inv_one_add_sq
  have hext_le : (∫ γ in (Icc Γ (Γ + H))ᶜ, ‖paperFT (depthSumProfile F₀ ρ) (-(γ : ℂ))‖ ^ 2) ≤
      (16 * Real.pi / H ^ 2) * Real.exp A * envelopeWindowNorm F₀ ^ 2 := by
    have hpt_ext : ∀ γ ∈ (Icc Γ (Γ + H))ᶜ,
        ‖paperFT (depthSumProfile F₀ ρ) (-(γ : ℂ))‖ ^ 2 ≤
          Real.exp A * envelopeWindowNorm F₀ ^ 2 * (16 / H ^ 2) *
            (1 / (1 + (ρ.im - γ) ^ 2)) := fun γ hγ => by
      have hgap : H / 4 ≤ |ρ.im - γ| := by
        rw [Set.mem_compl_iff, Set.mem_Icc, not_and_or] at hγ
        rcases hγ with h1 | h2
        · rw [abs_of_nonneg (by linarith [not_le.mp h1])]; linarith [not_le.mp h1]
        · rw [abs_sub_comm, abs_of_nonneg (by linarith [not_le.mp h2])]; linarith [not_le.mp h2]
      have hl := lorentz_sq_le_of_far (by positivity : (0 : ℝ) < H / 4) hgap
      refine (norm_sq_depthSum_le_lorentz hF₀ hF₀c hA hsupp hρ0 hρ1 γ).trans ?_
      calc Real.exp A * envelopeWindowNorm F₀ ^ 2 * (1 / (1 + (ρ.im - γ) ^ 2) ^ 2)
          ≤ Real.exp A * envelopeWindowNorm F₀ ^ 2 *
              ((1 / (H / 4) ^ 2) * (1 / (1 + (ρ.im - γ) ^ 2))) :=
            mul_le_mul_of_nonneg_left hl (by positivity)
        _ = _ := by
            have hHne : H ≠ 0 := hH.ne'
            field_simp <;> ring
    have hint_maj := hint_lor.const_mul (Real.exp A * envelopeWindowNorm F₀ ^ 2 * (16 / H ^ 2))
    calc (∫ γ in (Icc Γ (Γ + H))ᶜ, ‖paperFT (depthSumProfile F₀ ρ) (-(γ : ℂ))‖ ^ 2)
        ≤ ∫ γ in (Icc Γ (Γ + H))ᶜ,
            Real.exp A * envelopeWindowNorm F₀ ^ 2 * (16 / H ^ 2) *
              (1 / (1 + (ρ.im - γ) ^ 2)) :=
          setIntegral_mono_on hint_minus.integrableOn hint_maj.integrableOn
            measurableSet_Icc.compl hpt_ext
      _ ≤ ∫ γ : ℝ, Real.exp A * envelopeWindowNorm F₀ ^ 2 * (16 / H ^ 2) *
            (1 / (1 + (ρ.im - γ) ^ 2)) :=
          setIntegral_le_integral hint_maj (Eventually.of_forall fun _ => by positivity)
      _ = Real.exp A * envelopeWindowNorm F₀ ^ 2 * (16 / H ^ 2) * Real.pi := by
          rw [integral_const_mul, hint_lor_val]
      _ = (16 * Real.pi / H ^ 2) * Real.exp A * envelopeWindowNorm F₀ ^ 2 := by ring
  have hsplit := integral_add_compl (s := Icc Γ (Γ + H)) measurableSet_Icc hint_minus
  exact ⟨hc_minus, by linarith [hsplit, hext_le, hpl_ge]⟩

/-- **Riemann–von Mangoldt on the core.** For `Γ` large and `Γ^{99/100} ≤ H ≤ Γ/8`, the zeros with
ordinate in `(Γ + H/4, Γ + 3H/4]` have total multiplicity between `H log Γ/(16π)` and `H log Γ`. -/
theorem exists_window_core_count :
    ∃ Γ_c : ℝ, 16 ≤ Γ_c ∧ ∀ Γ : ℝ, Γ_c ≤ Γ → ∀ H : ℝ, Γ ^ (99 / 100 : ℝ) ≤ H → H ≤ Γ / 8 →
      (1 / (16 * Real.pi)) * H * Real.log Γ ≤
          (∑ ρ ∈ xiSupportsWindow (Γ + H / 4) (Γ + 3 * H / 4), (xiSupportMultiplicity ρ : ℝ)) ∧
        (∑ ρ ∈ xiSupportsWindow (Γ + H / 4) (Γ + 3 * H / 4), (xiSupportMultiplicity ρ : ℝ)) ≤
          H * Real.log Γ := by
  obtain ⟨C, hC, T₀, hT₀, hwin⟩ := exists_xiPosZeroCount_window_bounds
  set Γ_c : ℝ := max 16 (max T₀ (max (routeKRVMBase ^ 2 * Real.exp 4)
    ((64 * Real.pi * C + 1) ^ (2 : ℕ))))
  refine ⟨Γ_c, le_max_left _ _, fun Γ hΓ H hH1 hH2 => ?_⟩
  have hΓ16 : 16 ≤ Γ := (le_max_left _ _).trans hΓ
  have hΓT : T₀ ≤ Γ := ((le_max_left _ _).trans (le_max_right _ _)).trans hΓ
  have hΓbase : routeKRVMBase ^ 2 * Real.exp 4 ≤ Γ :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hΓ
  have hΓK : (64 * Real.pi * C + 1) ^ (2 : ℕ) ≤ Γ :=
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hΓ
  have hΓ0 : 0 < Γ := by linarith
  have hlogΓ : 0 < Real.log Γ := Real.log_pos (by linarith)
  have hH0 : 0 < H := lt_of_lt_of_le (Real.rpow_pos_of_pos hΓ0 _) hH1
  have hbase := routeKRVMBase_pos
  set T₁ := Γ + H / 4 with hT₁def
  set T₂ := Γ + 3 * H / 4 with hT₂def
  have hT₁ : T₀ ≤ T₁ := by linarith
  have hT12 : T₁ ≤ T₂ := by linarith
  obtain ⟨hlow, hupp⟩ := hwin T₁ T₂ hT₁ hT12
  have hwinsum := sum_mult_xiSupportsWindow (by linarith : (0 : ℝ) ≤ T₁) hT12
  have hpos₁ := xiPosZeroCount_eq_xiZeroCount (by linarith : (0 : ℝ) ≤ T₁)
  have hpos₂ := xiPosZeroCount_eq_xiZeroCount (by linarith : (0 : ℝ) ≤ T₂)
  have hcast : (xiPosZeroCount T₂ : ℝ) - xiPosZeroCount T₁ =
      (xiZeroCount T₂ : ℝ) - (xiZeroCount T₁ : ℝ) := by
    have h1 : ((xiPosZeroCount T₁ : ℤ) : ℝ) = (xiZeroCount T₁ : ℝ) := by exact_mod_cast hpos₁
    have h2 : ((xiPosZeroCount T₂ : ℤ) : ℝ) = (xiZeroCount T₂ : ℝ) := by exact_mod_cast hpos₂
    push_cast at h1 h2
    rw [h1, h2]
  rw [hwinsum, ← hcast]
  -- `log Γ ≤ 2 log(T₁/base)` and `log(T₂/base) ≤ log Γ` up to the constant.
  have hlogT₁ : Real.log Γ / 2 ≤ Real.log (T₁ / routeKRVMBase) := by
    have h1 : Real.log Γ / 2 ≤ Real.log Γ - Real.log routeKRVMBase := by
      have hb2 : Real.log (routeKRVMBase ^ 2) ≤ Real.log Γ :=
        Real.log_le_log (pow_pos hbase 2) (le_trans (le_mul_of_one_le_right (by positivity)
          (Real.one_le_exp (by norm_num))) hΓbase)
      rw [Real.log_pow] at hb2
      push_cast at hb2
      linarith
    have h2 : Real.log Γ - Real.log routeKRVMBase ≤ Real.log (T₁ / routeKRVMBase) := by
      rw [Real.log_div (by linarith : (0 : ℝ) < T₁).ne' hbase.ne']
      linarith [Real.log_le_log hΓ0 (by linarith : Γ ≤ T₁)]
    linarith
  have hlogT₂ : Real.log (T₂ / routeKRVMBase) + 1 ≤ 2 * Real.log Γ := by
    have hlb : 1 ≤ Real.log routeKRVMBase := by
      have he : Real.exp 1 ≤ routeKRVMBase := by
        unfold routeKRVMBase
        nlinarith [Real.pi_gt_three, Real.exp_pos 1]
      have := Real.log_le_log (Real.exp_pos 1) he
      rwa [Real.log_exp] at this
    have hT₂le : T₂ ≤ Γ ^ 2 := by nlinarith
    have h2 : Real.log T₂ ≤ 2 * Real.log Γ := by
      have := Real.log_le_log (by linarith) hT₂le
      rw [Real.log_pow] at this; push_cast at this; linarith
    rw [Real.log_div (by linarith : (0 : ℝ) < T₂).ne' hbase.ne']
    linarith
  have hlogsum : Real.log T₁ + Real.log T₂ ≤ 4 * Real.log Γ := by
    have h1 : Real.log T₁ ≤ Real.log (Γ ^ 2) := Real.log_le_log (by linarith) (by nlinarith)
    have h2 : Real.log T₂ ≤ Real.log (Γ ^ 2) := Real.log_le_log (by linarith) (by nlinarith)
    rw [Real.log_pow] at h1 h2
    push_cast at h1 h2
    linarith
  have hHbig : 64 * Real.pi * C ≤ H := by
    have hsq : 64 * Real.pi * C + 1 ≤ Γ ^ (1 / 2 : ℝ) := by
      have := Real.rpow_le_rpow (by positivity) hΓK (by norm_num : (0 : ℝ) ≤ 1 / 2)
      rwa [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), show ((2 : ℕ) : ℝ) * (1 / 2) = 1
        by norm_num, Real.rpow_one] at this
    have hrp : Γ ^ (1 / 2 : ℝ) ≤ Γ ^ (99 / 100 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    linarith
  constructor
  · have hmain : (T₂ - T₁) * (Real.log (T₁ / routeKRVMBase) + 1) / (2 * Real.pi) ≥
        (H / 2) * (Real.log Γ / 2) / (2 * Real.pi) := by
      have hT : T₂ - T₁ = H / 2 := by rw [hT₁def, hT₂def]; ring
      rw [hT]
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have herr : C * (Real.log T₁ + Real.log T₂) ≤ C * (4 * Real.log Γ) :=
      mul_le_mul_of_nonneg_left hlogsum hC.le
    have hfin : (1 / (16 * Real.pi)) * H * Real.log Γ ≤
        (H / 2) * (Real.log Γ / 2) / (2 * Real.pi) - C * (4 * Real.log Γ) := by
      have e : (H / 2) * (Real.log Γ / 2) / (2 * Real.pi) = (1 / (8 * Real.pi)) * H * Real.log Γ := by
        ring
      rw [e]
      have hCl : C * (4 * Real.log Γ) ≤ (1 / (16 * Real.pi)) * H * Real.log Γ := by
        have : C * 4 ≤ (1 / (16 * Real.pi)) * H := by
          rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
          nlinarith [Real.pi_pos]
        nlinarith
      have : (1 / (8 * Real.pi)) * H * Real.log Γ =
          2 * ((1 / (16 * Real.pi)) * H * Real.log Γ) := by ring
      linarith
    linarith
  · have hmain : (T₂ - T₁) * (Real.log (T₂ / routeKRVMBase) + 1) / (2 * Real.pi) ≤
        (H / 2) * (2 * Real.log Γ) / (2 * Real.pi) := by
      have hT : T₂ - T₁ = H / 2 := by rw [hT₁def, hT₂def]; ring
      rw [hT]
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hlogT₂ (by positivity)
    have herr : C * (Real.log T₁ + Real.log T₂) ≤ C * (4 * Real.log Γ) :=
      mul_le_mul_of_nonneg_left hlogsum hC.le
    have hfin : (H / 2) * (2 * Real.log Γ) / (2 * Real.pi) + C * (4 * Real.log Γ) ≤
        H * Real.log Γ := by
      have e : (H / 2) * (2 * Real.log Γ) / (2 * Real.pi) = (1 / (2 * Real.pi)) * H * Real.log Γ := by
        ring
      rw [e]
      have hπ : (1 / (2 * Real.pi)) ≤ 1 / 6 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith [Real.pi_gt_three]
      have hCl : C * 4 ≤ H / 2 := by nlinarith [Real.pi_gt_three]
      have hHl : 0 ≤ H * Real.log Γ := by positivity
      have h1 := mul_le_mul_of_nonneg_right hπ hHl
      have h2 := mul_le_mul_of_nonneg_right hCl hlogΓ.le
      nlinarith
    linarith

/-! ### 4. Near-line zeros on `[Γ − H, Γ + 2H]` -/

/-- The copies with ordinate in `(a, b]` number `N(b) − N(a)`. -/
private theorem card_le_xiZeroCount_sub {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (G : Finset XiZeroCopy) (hG : ∀ q ∈ G, a < (q.1 : ℂ).im ∧ (q.1 : ℂ).im ≤ b) :
    (G.card : ℝ) ≤ (xiZeroCount b : ℝ) - (xiZeroCount a : ℝ) := by
  classical
  have hsub : G ⊆ xiCopiesOf (xiSupportsWindow a b) := fun q hq => by
    unfold xiCopiesOf
    rw [Finset.mem_sigma]
    exact ⟨(mem_xiSupportsWindow ha).mpr (hG q hq), Finset.mem_univ _⟩
  have hcard := Finset.card_le_card hsub
  have hcopies : ((xiCopiesOf (xiSupportsWindow a b)).card : ℝ) =
      ∑ ρ ∈ xiSupportsWindow a b, (xiSupportMultiplicity ρ : ℝ) := by
    unfold xiCopiesOf
    rw [Finset.card_sigma]
    push_cast
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [Finset.card_univ, Fintype.card_fin]
    rfl
  rw [← sum_mult_xiSupportsWindow ha hab, ← hcopies]
  exact_mod_cast hcard

/-- **Shell absorption on short windows.** For every `ε > 0` there are `κ₀ > 0` and `Γ₁` such that
for `Γ ≥ Γ₁`, `Γ^{99/100} ≤ H ≤ Γ/8`, `0 ≤ A ≤ κ₀ log Γ` and every finite set `G` of zero copies
with ordinates in `[Γ − H, Γ + 2H]`, `(1/H) Σ_{q∈G} w_A(q) ≤ ε log Γ`. -/
theorem exists_window_shell_le {ε : ℝ} (hε : 0 < ε) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ κ₀ ≤ 1 / 38400 ∧ ∃ Γ₁ : ℝ, 64 ≤ Γ₁ ∧
      ∀ Γ : ℝ, Γ₁ ≤ Γ → ∀ H : ℝ, Γ ^ (99 / 100 : ℝ) ≤ H → H ≤ Γ / 8 →
      ∀ A : ℝ, 0 ≤ A → A ≤ κ₀ * Real.log Γ →
        ∀ G : Finset XiZeroCopy,
          (∀ q ∈ G, Γ - H ≤ (q.1 : ℂ).im ∧ (q.1 : ℂ).im ≤ Γ + 2 * H) →
          (1 / H) * (∑ q ∈ G, localZeroWeight A q) ≤ ε * Real.log Γ := by
  obtain ⟨A_sel, K_sel, hA_sel, hK_sel, hev_sel⟩ := RHTower.exists_shortWindowZeros_weighted_le
  obtain ⟨U_sel, hU_sel⟩ := Filter.eventually_atTop.mp hev_sel
  obtain ⟨Cw, hCw, T₀w, hT₀w, hwinle⟩ := exists_xiZeroCount_window_le
  obtain ⟨K₃, hK₃1, hK₃⟩ := exists_one_add_log_pow_le_rpow 3 (by norm_num : (0 : ℝ) < 1 / 4)
  set C₂ : ℝ := max 4800 (64 * A_sel / ε)
  have hC₂_4800 : 4800 ≤ C₂ := le_max_left _ _
  have hC₂_pos : 0 < C₂ := by linarith
  have hC₂_sel : 64 * A_sel / ε ≤ C₂ := le_max_right _ _
  clear_value C₂
  set κ₀ : ℝ := min (1 / 38400) (min (1 / (2 * C₂)) (Real.sqrt (ε / (36 * Real.pi * C₂ ^ 2))))
  have hκ₀_pos : 0 < κ₀ :=
    lt_min (by norm_num) (lt_min (by positivity) (Real.sqrt_pos.mpr (by positivity)))
  have hκ₀_1 : κ₀ ≤ 1 / 38400 := min_le_left _ _
  have hκ₀_2 : κ₀ ≤ 1 / (2 * C₂) := (min_le_right _ _).trans (min_le_left _ _)
  have hκ₀_sq : κ₀ ^ 2 ≤ ε / (36 * Real.pi * C₂ ^ 2) := by
    have hle : κ₀ ≤ Real.sqrt (ε / (36 * Real.pi * C₂ ^ 2)) :=
      (min_le_right _ _).trans (min_le_right _ _)
    exact (pow_le_pow_left₀ hκ₀_pos.le hle 2).trans_eq (Real.sq_sqrt (by positivity))
  clear_value κ₀
  set M : ℝ := 256 * (K_sel + 1) * K₃ / (C₂ * ε) with hM_def
  have hM_pos : 0 < M := by positivity
  clear_value M
  set Γ₁ : ℝ := max 64 (max U_sel (max (Real.exp (4 * C₂)) (max (M ^ (5 : ℕ))
    (max (2 * T₀w + 2) ((8 * Cw + 8) ^ (2 : ℕ))))))
  have hΓ₁_64 : 64 ≤ Γ₁ := le_max_left _ _
  refine ⟨κ₀, hκ₀_pos, hκ₀_1, Γ₁, hΓ₁_64, fun Γ hΓ H hH1 hH2 A hA0 hA G hG => ?_⟩
  classical
  have hΓ64 : 64 ≤ Γ := hΓ₁_64.trans hΓ
  have hΓUsel : U_sel ≤ Γ := ((le_max_left _ _).trans (le_max_right _ _)).trans hΓ
  have hΓexp : Real.exp (4 * C₂) ≤ Γ :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hΓ
  have hΓM : M ^ (5 : ℕ) ≤ Γ := ((le_max_left _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _)))).trans hΓ
  have hΓT : 2 * T₀w + 2 ≤ Γ := ((le_max_left _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))).trans hΓ
  have hΓC : (8 * Cw + 8) ^ (2 : ℕ) ≤ Γ := ((le_max_right _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))).trans hΓ
  have hΓ0 : 0 < Γ := by linarith
  have hΓ1 : 1 ≤ Γ := by linarith
  have hlogΓ_ge : 4 * C₂ ≤ Real.log Γ := by
    have := Real.log_le_log (Real.exp_pos _) hΓexp; rwa [Real.log_exp] at this
  have hlogΓ_pos : 0 < Real.log Γ := by linarith
  have hlogΓ_ge1 : 1 ≤ Real.log Γ := by linarith
  have hH0 : 0 < H := lt_of_lt_of_le (Real.rpow_pos_of_pos hΓ0 _) hH1
  have hsqrtH : Γ ^ (1 / 2 : ℝ) ≤ H :=
    (Real.rpow_le_rpow_of_exponent_le hΓ1 (by norm_num)).trans hH1
  have hHC : 8 * Cw + 8 ≤ H := by
    refine le_trans ?_ hsqrtH
    have := Real.rpow_le_rpow (by positivity) hΓC (by norm_num : (0 : ℝ) ≤ 1 / 2)
    rwa [← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
      show ((2 : ℕ) : ℝ) * (1 / 2) = 1 by norm_num, Real.rpow_one] at this
  set v₀ : ℝ := C₂ / Real.log Γ with hv₀_def
  have hv₀_pos : 0 < v₀ := div_pos hC₂_pos hlogΓ_pos
  have hv₀_le_quarter : v₀ ≤ 1 / 4 := by
    rw [hv₀_def, div_le_div_iff₀ hlogΓ_pos (by norm_num)]; linarith
  clear_value v₀
  let G_sh := G.filter (fun q => foldedRe q ≤ 1 / 2 + v₀)
  let G_dp := G.filter (fun q => 1 / 2 + v₀ < foldedRe q)
  have hsplit_G : ∑ q ∈ G, localZeroWeight A q =
      (∑ q ∈ G_sh, localZeroWeight A q) + ∑ q ∈ G_dp, localZeroWeight A q := by
    dsimp [G_sh, G_dp]
    rw [← Finset.sum_filter_add_sum_filter_not G (fun q => foldedRe q ≤ 1 / 2 + v₀)]
    congr 2; ext q; simp [not_le]
  -- Shallow zeros: each costs `O(κ₀²)` and there are `≤ 3H log Γ` of them.
  have hcardG : (G.card : ℝ) ≤ 3 * H * Real.log Γ := by
    have ha0 : (0 : ℝ) ≤ Γ - H - 1 := by linarith
    have hc := card_le_xiZeroCount_sub ha0 (by linarith) G fun q hq =>
      ⟨by linarith [(hG q hq).1], (hG q hq).2⟩
    have hw := hwinle (Γ - H - 1) (by linarith) (3 * H + 1) (by linarith)
    rw [show Γ - H - 1 + (3 * H + 1) = Γ + 2 * H by ring] at hw
    have hlog2 : Real.log (Γ + 2 * H) ≤ 2 * Real.log Γ := by
      have : Real.log (Γ + 2 * H) ≤ Real.log (Γ ^ 2) := Real.log_le_log (by linarith) (by nlinarith)
      rw [Real.log_pow] at this; push_cast at this; linarith
    have hlogpos : 0 ≤ Real.log (Γ + 2 * H) := Real.log_nonneg (by linarith)
    calc (G.card : ℝ) ≤ (3 * H + 1) / (2 * Real.pi) * Real.log (Γ + 2 * H) +
          2 * Cw * Real.log (Γ + 2 * H) := hc.trans hw
      _ ≤ (3 * H + 1) / (2 * Real.pi) * (2 * Real.log Γ) + 2 * Cw * (2 * Real.log Γ) := by gcongr
      _ ≤ 3 * H * Real.log Γ := by
          have hπ : (3 * H + 1) / (2 * Real.pi) ≤ (3 * H + 1) / 6 :=
            div_le_div_of_nonneg_left (by positivity) (by norm_num) (by nlinarith [Real.pi_gt_three])
          have h1 : (3 * H + 1) / (2 * Real.pi) * (2 * Real.log Γ) ≤
              (3 * H + 1) / 6 * (2 * Real.log Γ) :=
            mul_le_mul_of_nonneg_right hπ (by positivity)
          have h2 : (3 * H + 1) / 6 * (2 * Real.log Γ) + 2 * Cw * (2 * Real.log Γ) =
              (H + 1 / 3 + 4 * Cw) * Real.log Γ := by ring
          have h3 : (H + 1 / 3 + 4 * Cw) * Real.log Γ ≤ (3 * H) * Real.log Γ :=
            mul_le_mul_of_nonneg_right (by linarith) hlogΓ_pos.le
          linarith
  have hsh_pt : ∀ q ∈ G_sh, localZeroWeight A q ≤ 6 * Real.pi * C₂ ^ 2 * κ₀ ^ 2 := fun q hq => by
    have hq_le : foldedRe q - 1 / 2 ≤ v₀ := by linarith [(Finset.mem_filter.mp hq).2]
    have hq_nn : 0 ≤ foldedRe q - 1 / 2 := sub_nonneg.mpr (half_le_foldedRe q)
    have hprod_le : A * (foldedRe q - 1 / 2) ≤ κ₀ * C₂ := by
      calc A * (foldedRe q - 1 / 2) ≤ (κ₀ * Real.log Γ) * v₀ :=
            mul_le_mul hA hq_le hq_nn (by positivity)
        _ = κ₀ * C₂ := by rw [hv₀_def]; field_simp [hlogΓ_pos.ne']
    have hκC₂_le : κ₀ * C₂ ≤ 1 / 2 := by
      have hm := mul_le_mul_of_nonneg_right hκ₀_2 hC₂_pos.le
      have heq : 1 / (2 * C₂) * C₂ = 1 / 2 := by field_simp [hC₂_pos.ne']
      linarith
    have hexp_le3 : Real.exp (2 * A * (foldedRe q - 1 / 2)) ≤ 3 := by
      have h1 : Real.exp (2 * A * (foldedRe q - 1 / 2)) ≤ Real.exp 1 :=
        Real.exp_le_exp.mpr (by linarith)
      exact h1.trans (Real.exp_one_lt_d9.le.trans (by norm_num))
    have hsq_le : A ^ 2 * (foldedRe q - 1 / 2) ^ 2 ≤ C₂ ^ 2 * κ₀ ^ 2 := by
      calc A ^ 2 * (foldedRe q - 1 / 2) ^ 2 = (A * (foldedRe q - 1 / 2)) ^ 2 := by ring
        _ ≤ (κ₀ * C₂) ^ 2 := pow_le_pow_left₀ (mul_nonneg hA0 hq_nn) hprod_le 2
        _ = C₂ ^ 2 * κ₀ ^ 2 := by ring
    unfold localZeroWeight
    refine (min_le_right _ _).trans ?_
    calc 2 * Real.pi * A ^ 2 * (foldedRe q - 1 / 2) ^ 2 * Real.exp (2 * A * (foldedRe q - 1 / 2))
        = 2 * Real.pi * (A ^ 2 * (foldedRe q - 1 / 2) ^ 2) *
            Real.exp (2 * A * (foldedRe q - 1 / 2)) := by ring
      _ ≤ 2 * Real.pi * (C₂ ^ 2 * κ₀ ^ 2) * 3 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hsq_le (by positivity))
            hexp_le3 (Real.exp_pos _).le (by positivity)
      _ = 6 * Real.pi * C₂ ^ 2 * κ₀ ^ 2 := by ring
  have hsh_tot : (1 / H) * (∑ q ∈ G_sh, localZeroWeight A q) ≤ (ε / 2) * Real.log Γ := by
    have hcard_sh : (G_sh.card : ℝ) ≤ 3 * H * Real.log Γ :=
      le_trans (by exact_mod_cast Finset.card_filter_le G _) hcardG
    have hs1 : (∑ q ∈ G_sh, localZeroWeight A q) ≤
        (G_sh.card : ℝ) * (6 * Real.pi * C₂ ^ 2 * κ₀ ^ 2) := by
      refine (Finset.sum_le_sum hsh_pt).trans_eq ?_
      rw [Finset.sum_const, nsmul_eq_mul]
    calc (1 / H) * (∑ q ∈ G_sh, localZeroWeight A q)
        ≤ (1 / H) * ((3 * H * Real.log Γ) * (6 * Real.pi * C₂ ^ 2 * κ₀ ^ 2)) :=
          mul_le_mul_of_nonneg_left
            (hs1.trans (mul_le_mul_of_nonneg_right hcard_sh (by positivity))) (by positivity)
      _ = 18 * Real.pi * C₂ ^ 2 * κ₀ ^ 2 * Real.log Γ := by field_simp [hH0.ne']; ring
      _ ≤ 18 * Real.pi * C₂ ^ 2 * (ε / (36 * Real.pi * C₂ ^ 2)) * Real.log Γ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hκ₀_sq (by positivity))
            hlogΓ_pos.le
      _ = (ε / 2) * Real.log Γ := by field_simp [Real.pi_ne_zero, hC₂_pos.ne']; ring
  -- Deep zeros: one short Selberg window `[Γ − H − 2, Γ + 2H + 2]` at `U = 3Γ`.
  set U : ℝ := 3 * Γ with hU
  have hUsel : U_sel ≤ U := by rw [hU]; linarith
  have hlogU_ge : Real.log Γ ≤ Real.log U := Real.log_le_log hΓ0 (by rw [hU]; linarith)
  have hlogU_le : Real.log U ≤ 2 * Real.log Γ := by
    have : Real.log U ≤ Real.log (Γ ^ 2) := Real.log_le_log (by positivity) (by rw [hU]; nlinarith)
    rw [Real.log_pow] at this; push_cast at this; linarith
  have hlogU_pos : 0 < Real.log U := lt_of_lt_of_le hlogΓ_pos hlogU_ge
  have hW99 : Real.exp (99 / 100 * Real.log U) + 2 ≤ 3 * H + 4 := by
    have hU99 : Real.exp (99 / 100 * Real.log U) = U ^ (99 / 100 : ℝ) := by
      rw [Real.rpow_def_of_pos (by positivity), mul_comm]
    rw [hU99, hU, Real.mul_rpow (by norm_num) hΓ0.le]
    have h3 : (3 : ℝ) ^ (99 / 100 : ℝ) ≤ 3 := by
      calc (3 : ℝ) ^ (99 / 100 : ℝ) ≤ (3 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 3 := Real.rpow_one 3
    nlinarith [Real.rpow_pos_of_pos hΓ0 (99 / 100 : ℝ)]
  obtain ⟨T₁, hT₁, T₂, hT₂, hsel⟩ := hU_sel U hUsel (Γ - H - 2) (3 * H + 4)
    (by rw [hU]; linarith) (by rw [hU]; linarith) hW99
  have hT₁pos : 0 < T₁ := by linarith [hT₁.1]
  have hT12 : T₁ ≤ T₂ := by linarith [hT₁.2, hT₂.1]
  have hv₀_low : 2 / Real.log U ≤ v₀ := by
    rw [hv₀_def]
    exact (div_le_div_of_nonneg_left (by norm_num) hlogΓ_pos hlogU_ge).trans
      (div_le_div_of_nonneg_right (by linarith) hlogΓ_pos.le)
  have hexp_le_lam : ∀ q : XiZeroCopy, Real.exp (2 * A * (foldedRe q - 1 / 2)) ≤
      Real.exp ((1 / 19200) * (foldedRe q - 1 / 2) * Real.log U) := fun q => by
    apply Real.exp_le_exp.mpr
    have h2A : 2 * A ≤ (1 / 19200) * Real.log U := by
      calc 2 * A ≤ 2 * (κ₀ * Real.log Γ) := by linarith
        _ ≤ 2 * ((1 / 38400) * Real.log Γ) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hκ₀_1 hlogΓ_pos.le) (by norm_num)
        _ = (1 / 19200) * Real.log Γ := by ring
        _ ≤ (1 / 19200) * Real.log U := mul_le_mul_of_nonneg_left hlogU_ge (by norm_num)
    have hnn : 0 ≤ foldedRe q - 1 / 2 := sub_nonneg.mpr (half_le_foldedRe q)
    exact (mul_le_mul_of_nonneg_right h2A hnn).trans_eq (by ring)
  have hG_dp : ∀ q ∈ G_dp, 1 / 2 + v₀ < foldedRe q ∧ T₁ ≤ |(q.1 : ℂ).im| ∧ |(q.1 : ℂ).im| ≤ T₂ :=
    fun q hq => by
      have hq1 := Finset.mem_filter.mp hq
      have hqG := hG q hq1.1
      have hpos : 0 < (q.1 : ℂ).im := by linarith [hqG.1]
      rw [abs_of_pos hpos]
      exact ⟨hq1.2, by linarith [hT₁.2, hqG.1], by linarith [hT₂.1, hqG.2]⟩
  have h4fold := sum_foldedRe_le_four_mul_windowZeros
    (g := fun y => Real.exp ((1 / 19200) * (y - 1 / 2) * Real.log U))
    (fun _ => (Real.exp_pos _).le) hT₁pos hT12 hv₀_pos G_dp hG_dp
  have hselU := hsel (1 / 19200) v₀ (by norm_num) (by norm_num) hv₀_low hv₀_le_quarter
  have hvL_ge : 4800 ≤ v₀ * Real.log U := by
    have h1 : C₂ ≤ v₀ * Real.log U := by
      rw [hv₀_def]
      calc C₂ = C₂ / Real.log Γ * Real.log Γ := by field_simp [hlogΓ_pos.ne']
        _ ≤ C₂ / Real.log Γ * Real.log U := mul_le_mul_of_nonneg_left hlogU_ge (by positivity)
    linarith
  have hlen : T₂ - T₁ ≤ 4 * H := by linarith [hT₁.1, hT₂.2]
  have hterm1 : (T₂ - T₁) * A_sel / (Real.pi * v₀) * (1 + 4800 / (v₀ * Real.log U)) *
        Real.exp (-(v₀ * Real.log U / 4800)) ≤ (8 * A_sel / (Real.pi * C₂)) * H * Real.log Γ := by
    have hf1 : 1 + 4800 / (v₀ * Real.log U) ≤ 2 := by
      have : 4800 / (v₀ * Real.log U) ≤ 1 := div_le_one_of_le₀ hvL_ge (by positivity)
      linarith
    have hf2 : Real.exp (-(v₀ * Real.log U / 4800)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hprod : (1 + 4800 / (v₀ * Real.log U)) * Real.exp (-(v₀ * Real.log U / 4800)) ≤ 2 :=
      (mul_le_mul hf1 hf2 (Real.exp_pos _).le (by norm_num)).trans_eq (by ring)
    have hmain : (T₂ - T₁) * A_sel / (Real.pi * v₀) ≤ (4 * A_sel / (Real.pi * C₂)) * H * Real.log Γ := by
      calc (T₂ - T₁) * A_sel / (Real.pi * v₀) ≤ (4 * H) * A_sel / (Real.pi * v₀) :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hlen hA_sel.le) (by positivity)
        _ = (4 * A_sel / (Real.pi * C₂)) * H * Real.log Γ := by
            rw [hv₀_def]; field_simp [Real.pi_ne_zero, hC₂_pos.ne', hlogΓ_pos.ne']; ring
    calc (T₂ - T₁) * A_sel / (Real.pi * v₀) * (1 + 4800 / (v₀ * Real.log U)) *
          Real.exp (-(v₀ * Real.log U / 4800))
        = ((T₂ - T₁) * A_sel / (Real.pi * v₀)) *
            ((1 + 4800 / (v₀ * Real.log U)) * Real.exp (-(v₀ * Real.log U / 4800))) := by ring
      _ ≤ ((4 * A_sel / (Real.pi * C₂)) * H * Real.log Γ) * 2 :=
          mul_le_mul hmain hprod (by positivity) (by positivity)
      _ = (8 * A_sel / (Real.pi * C₂)) * H * Real.log Γ := by ring
  have hterm2 : Real.log U * (K_sel * Real.log U / (Real.pi * v₀) *
        Real.exp ((1 / 19200) * Real.log U)) ≤
      (4 * (K_sel + 1) * K₃ / (Real.pi * C₂)) * Γ ^ (3 / 4 : ℝ) := by
    have hexpU : Real.exp ((1 / 19200) * Real.log U) ≤ Γ ^ (1 / 2 : ℝ) := by
      have hle : (1 / 19200) * Real.log U ≤ (1 / 2) * Real.log Γ := by linarith
      calc Real.exp ((1 / 19200) * Real.log U) ≤ Real.exp ((1 / 2) * Real.log Γ) :=
            Real.exp_le_exp.mpr hle
        _ = Γ ^ (1 / 2 : ℝ) := by rw [Real.rpow_def_of_pos hΓ0, mul_comm]
    have hlog3 : Real.log Γ ^ 3 ≤ K₃ * Γ ^ (1 / 4 : ℝ) :=
      (pow_le_pow_left₀ hlogΓ_pos.le (by linarith) 3).trans (hK₃ Γ hΓ1)
    have hK_le : K_sel ≤ K_sel + 1 := by linarith
    calc Real.log U * (K_sel * Real.log U / (Real.pi * v₀) * Real.exp ((1 / 19200) * Real.log U))
        ≤ (2 * Real.log Γ) * ((K_sel + 1) * (2 * Real.log Γ) / (Real.pi * v₀) *
            Γ ^ (1 / 2 : ℝ)) := by
          refine mul_le_mul hlogU_le ?_ (by positivity) (by positivity)
          refine mul_le_mul ?_ hexpU (Real.exp_pos _).le (by positivity)
          exact div_le_div_of_nonneg_right
            (mul_le_mul hK_le hlogU_le hlogU_pos.le (by positivity)) (by positivity)
      _ = (4 * (K_sel + 1) / (Real.pi * C₂)) * Real.log Γ ^ 3 * Γ ^ (1 / 2 : ℝ) := by
          rw [hv₀_def, show Real.pi * (C₂ / Real.log Γ) = (Real.pi * C₂) / Real.log Γ by ring,
            div_div_eq_mul_div]
          ring
      _ ≤ (4 * (K_sel + 1) / (Real.pi * C₂)) * (K₃ * Γ ^ (1 / 4 : ℝ)) * Γ ^ (1 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog3 (by positivity))
            (Real.rpow_nonneg hΓ0.le _)
      _ = (4 * (K_sel + 1) * K₃ / (Real.pi * C₂)) * (Γ ^ (1 / 4 : ℝ) * Γ ^ (1 / 2 : ℝ)) := by ring
      _ = (4 * (K_sel + 1) * K₃ / (Real.pi * C₂)) * Γ ^ (3 / 4 : ℝ) := by
          rw [← Real.rpow_add hΓ0]; norm_num
  have hdp_pt : ∀ q ∈ G_dp, localZeroWeight A q ≤
      (Real.pi / 2) * Real.exp ((1 / 19200) * (foldedRe q - 1 / 2) * Real.log U) := fun q _ => by
    unfold localZeroWeight
    exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_left (hexp_le_lam q) (by positivity))
  have hdp_sum : (∑ q ∈ G_dp, localZeroWeight A q) ≤
      2 * Real.pi * ((8 * A_sel / (Real.pi * C₂)) * H * Real.log Γ +
        (4 * (K_sel + 1) * K₃ / (Real.pi * C₂)) * Γ ^ (3 / 4 : ℝ)) := by
    refine (Finset.sum_le_sum hdp_pt).trans ?_
    rw [← Finset.mul_sum]
    have h4 := h4fold.trans (mul_le_mul_of_nonneg_left hselU (by norm_num))
    have h5 : (∑ q ∈ G_dp, Real.exp ((1 / 19200) * (foldedRe q - 1 / 2) * Real.log U)) ≤
        4 * ((8 * A_sel / (Real.pi * C₂)) * H * Real.log Γ +
          (4 * (K_sel + 1) * K₃ / (Real.pi * C₂)) * Γ ^ (3 / 4 : ℝ)) :=
      h4.trans (by linarith [hterm1, hterm2])
    calc (Real.pi / 2) * (∑ q ∈ G_dp, Real.exp ((1 / 19200) * (foldedRe q - 1 / 2) * Real.log U))
        ≤ (Real.pi / 2) * (4 * ((8 * A_sel / (Real.pi * C₂)) * H * Real.log Γ +
          (4 * (K_sel + 1) * K₃ / (Real.pi * C₂)) * Γ ^ (3 / 4 : ℝ))) :=
          mul_le_mul_of_nonneg_left h5 (by positivity)
      _ = _ := by ring
  have hdp_tot : (1 / H) * (∑ q ∈ G_dp, localZeroWeight A q) ≤ (ε / 2) * Real.log Γ := by
    have hfirst : (1 / H) * (2 * Real.pi * ((8 * A_sel / (Real.pi * C₂)) * H * Real.log Γ)) ≤
        (ε / 4) * Real.log Γ := by
      have e : (1 / H) * (2 * Real.pi * ((8 * A_sel / (Real.pi * C₂)) * H * Real.log Γ)) =
          (16 * A_sel / C₂) * Real.log Γ := by
        field_simp [hH0.ne', Real.pi_ne_zero, hC₂_pos.ne']
        ring
      rw [e]
      apply mul_le_mul_of_nonneg_right _ hlogΓ_pos.le
      rw [div_le_iff₀ hC₂_pos]
      have hmul : 64 * A_sel ≤ C₂ * ε := (div_le_iff₀ hε).mp hC₂_sel
      nlinarith
    have hsecond : (1 / H) * (2 * Real.pi * ((4 * (K_sel + 1) * K₃ / (Real.pi * C₂)) *
        Γ ^ (3 / 4 : ℝ))) ≤ (ε / 4) * Real.log Γ := by
      have hH' : Γ ^ (99 / 100 : ℝ) ≤ H := hH1
      have hfrac : (1 / H) * Γ ^ (3 / 4 : ℝ) ≤ Γ ^ (-(6 / 25 : ℝ)) := by
        rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hH0]
        calc Γ ^ (3 / 4 : ℝ) = Γ ^ (-(6 / 25 : ℝ)) * Γ ^ (99 / 100 : ℝ) := by
              rw [← Real.rpow_add hΓ0]; norm_num
          _ ≤ Γ ^ (-(6 / 25 : ℝ)) * H :=
              mul_le_mul_of_nonneg_left hH' (Real.rpow_nonneg hΓ0.le _)
      have hMle : M ≤ Γ ^ (6 / 25 : ℝ) := by
        have h1 : M ≤ Γ ^ (1 / 5 : ℝ) := by
          calc M = (M ^ (5 : ℕ)) ^ (1 / 5 : ℝ) := by
                rw [← Real.rpow_natCast M 5, ← Real.rpow_mul hM_pos.le]; norm_num
            _ ≤ Γ ^ (1 / 5 : ℝ) := Real.rpow_le_rpow (by positivity) hΓM (by norm_num)
        exact h1.trans (Real.rpow_le_rpow_of_exponent_le hΓ1 (by norm_num))
      have hinv : Γ ^ (-(6 / 25 : ℝ)) ≤ 1 / M := by
        rw [Real.rpow_neg hΓ0.le, ← one_div]
        exact one_div_le_one_div_of_le hM_pos hMle
      have e : (1 / H) * (2 * Real.pi * ((4 * (K_sel + 1) * K₃ / (Real.pi * C₂)) *
          Γ ^ (3 / 4 : ℝ))) = (8 * (K_sel + 1) * K₃ / C₂) * ((1 / H) * Γ ^ (3 / 4 : ℝ)) := by
        field_simp [hH0.ne', Real.pi_ne_zero, hC₂_pos.ne']
        ring
      rw [e]
      calc (8 * (K_sel + 1) * K₃ / C₂) * ((1 / H) * Γ ^ (3 / 4 : ℝ))
          ≤ (8 * (K_sel + 1) * K₃ / C₂) * (1 / M) :=
            mul_le_mul_of_nonneg_left (hfrac.trans hinv) (by positivity)
        _ = ε / 32 := by
            rw [hM_def]
            have hK1 : K_sel + 1 ≠ 0 := by linarith
            have hK3 : K₃ ≠ 0 := by linarith
            field_simp [hC₂_pos.ne', hε.ne']
            ring
        _ ≤ (ε / 4) * Real.log Γ := by nlinarith [mul_le_mul_of_nonneg_left hlogΓ_ge1 hε.le]
    have hsplit2 : (1 / H) * (∑ q ∈ G_dp, localZeroWeight A q) ≤
        (1 / H) * (2 * Real.pi * ((8 * A_sel / (Real.pi * C₂)) * H * Real.log Γ)) +
          (1 / H) * (2 * Real.pi * ((4 * (K_sel + 1) * K₃ / (Real.pi * C₂)) *
            Γ ^ (3 / 4 : ℝ))) := by
      rw [← mul_add, ← mul_add]
      exact mul_le_mul_of_nonneg_left hdp_sum (by positivity)
    linarith
  rw [hsplit_G, mul_add]
  linarith [hsh_tot, hdp_tot]

/-! ### 5. Averaged positivity on short windows -/

/-- **Averaged Weil positivity on windows of length `Γ^{99/100}`.** There are `κ₀ > 0`, `C₀ ≥ 0`
and `Γ₀` such that for all `Γ ≥ Γ₀`, `Γ^{99/100} ≤ H ≤ Γ/8`, `0 ≤ A ≤ κ₀ log Γ` and real
`F₀ ∈ C²_c([−A, A])`,
`(1/H) ∫_Γ^{Γ+H} [Q(F₀ cos γ·) + Q(F₀ sin γ·)] dγ ≥ (1/16) log Γ ‖F₀‖² − C₀ Γ^{−1/2} N(F₀)²`. -/
theorem exists_shortWindow_frequencyAverage_quadrature_pos :
    ∃ κ₀ C₀ : ℝ, 0 < κ₀ ∧ 0 ≤ C₀ ∧ ∃ Γ₀ : ℝ, 64 ≤ Γ₀ ∧
      ∀ Γ : ℝ, Γ₀ ≤ Γ → ∀ H : ℝ, Γ ^ (99 / 100 : ℝ) ≤ H → H ≤ Γ / 8 →
      ∀ A : ℝ, 0 ≤ A → A ≤ κ₀ * Real.log Γ →
        ∀ F₀ : ℝ → ℝ, ContDiff ℝ 2 F₀ → HasCompactSupport F₀ →
          (∀ u : ℝ, A < |u| → F₀ u = 0) →
          (1 / 16) * Real.log Γ * (∫ u, F₀ u ^ 2) -
              C₀ * Γ ^ (-(1 / 2 : ℝ)) * envelopeWindowNorm F₀ ^ 2 ≤
            (1 / H) * ∫ γ in Icc Γ (Γ + H),
              (fullZeroForm (cosineSource F₀ γ) + fullZeroForm (sineSource F₀ γ)) := by
  obtain ⟨Γ_c, hΓ_c, hcore⟩ := exists_window_core_count
  obtain ⟨κ₀, hκ₀, hκ₀1, Γ₁, hΓ₁, hshell⟩ := exists_window_shell_le (ε := 1 / 16) (by norm_num)
  obtain ⟨K₁, hK₁1, hK₁⟩ := exists_one_add_log_pow_le_rpow 1 (by norm_num : (0 : ℝ) < 1 / 6)
  set Cx : ℝ := 8 * (|xiLineTwoLogDerivConstant| + 3 * K₁) with hCx_def
  set C₀ : ℝ := 16 * Real.pi * K₁ + Cx with hC₀_def
  have hCx : 0 ≤ Cx := by positivity
  refine ⟨κ₀, C₀, hκ₀, by positivity, max Γ₁ Γ_c, hΓ₁.trans (le_max_left _ _),
    fun Γ hΓ H hH1 hH2 A hA0 hA F₀ hF₀ hF₀c hsupp => ?_⟩
  classical
  have hΓ64 : 64 ≤ Γ := (hΓ₁.trans (le_max_left _ _)).trans hΓ
  have hΓ1 : 1 ≤ Γ := by linarith
  have hΓ0 : 0 < Γ := by linarith
  have hlogΓ_nn : 0 ≤ Real.log Γ := Real.log_nonneg hΓ1
  have hH0 : 0 < H := lt_of_lt_of_le (Real.rpow_pos_of_pos hΓ0 _) hH1
  have hA_half : A ≤ (1 / 2) * Real.log Γ := by
    have : κ₀ * Real.log Γ ≤ (1 / 2) * Real.log Γ :=
      mul_le_mul_of_nonneg_right (hκ₀1.trans (by norm_num)) hlogΓ_nn
    linarith
  have hexpA_half : Real.exp A ≤ Γ ^ (1 / 2 : ℝ) := by
    calc Real.exp A ≤ Real.exp ((1 / 2) * Real.log Γ) := Real.exp_le_exp.mpr hA_half
      _ = Γ ^ (1 / 2 : ℝ) := by rw [Real.rpow_def_of_pos hΓ0, mul_comm]
  have hlog1 : Real.log Γ ≤ K₁ * Γ ^ (1 / 6 : ℝ) := by
    have h1 : Real.log Γ ≤ (1 + Real.log Γ) ^ 1 := by rw [pow_one]; linarith
    exact h1.trans (hK₁ Γ hΓ1)
  -- `e^A log Γ / H² ≤ K₁ Γ^{−1/2}` and the same with the Lorentzian constant.
  have hinvH2 : 1 / H ^ 2 ≤ Γ ^ (-(198 / 100 : ℝ)) := by
    have hH2 : Γ ^ (198 / 100 : ℝ) ≤ H ^ 2 := by
      have := pow_le_pow_left₀ (Real.rpow_nonneg hΓ0.le _) hH1 2
      rwa [← Real.rpow_natCast, ← Real.rpow_mul hΓ0.le, show (99 / 100 : ℝ) * ((2 : ℕ) : ℝ) =
        198 / 100 by norm_num] at this
    rw [Real.rpow_neg hΓ0.le, ← one_div]
    exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos hΓ0 _) hH2
  have hkey : Γ ^ (1 / 2 : ℝ) * Γ ^ (1 / 6 : ℝ) * Γ ^ (-(198 / 100 : ℝ)) ≤ Γ ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_add hΓ0, ← Real.rpow_add hΓ0]
    exact Real.rpow_le_rpow_of_exponent_le hΓ1 (by norm_num)
  have herr_gen : ∀ c : ℝ, 0 ≤ c → c * Real.log Γ ≤ c * (K₁ * Γ ^ (1 / 6 : ℝ)) :=
    fun c hc => mul_le_mul_of_nonneg_left hlog1 hc
  -- The master bound on the window and the core.
  obtain ⟨G_loc, hG_loc, hint_tsum, hsub_win⟩ :=
    integral_window_tsum_depthDiff_le hF₀ hF₀c hΓ1 hH0 (by linarith) hA0 hsupp
  obtain ⟨hd_sub_sum, -, -, -, -⟩ := integral_Icc_tsum_depthDiff_div_four_le hF₀ hF₀c hΓ1 hA0 hsupp
  let W_core : Finset XiDivisorSupport := xiSupportsWindow (Γ + H / 4) (Γ + 3 * H / 4)
  let C_core : Finset zetaZeroConfig.carrier := W_core.map xiDivisorZetaCarrierEquiv.toEmbedding
  have hmem_core : ∀ ρ ∈ C_core, 0 < (ρ : ℂ).re ∧ (ρ : ℂ).re < 1 ∧
      Γ + H / 4 ≤ (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ Γ + 3 * H / 4 := by
    intro ρ hρ
    rcases Finset.mem_map.mp hρ with ⟨ξ₀, hξ₀, rfl⟩
    have hwin := (mem_xiSupportsWindow (by positivity : 0 ≤ Γ + H / 4)).mp hξ₀
    have hstrip := (xiDivisorZetaCarrierEquiv ξ₀).2
    exact ⟨hstrip.2.1, hstrip.2.2, hwin.1.le, hwin.2⟩
  let coreQ : zetaZeroConfig.carrier → ℝ → ℝ := fun ρ γ =>
    (zetaZeroConfig.mult ρ : ℝ) * ‖paperFT (depthSumProfile F₀ (ρ : ℂ)) (-(γ : ℂ))‖ ^ 2
  have hcore_cont : ∀ ρ ∈ C_core, Continuous (coreQ ρ) := fun ρ hρ => by
    obtain ⟨hr0, hr1, hi1, hi2⟩ := hmem_core ρ hρ
    exact continuous_const.mul
      (integral_window_norm_paperFT_depthSum_sq_ge hF₀ hF₀c hH0 hA0 hsupp hr0 hr1 hi1 hi2).1
  have hquad_cont : Continuous fun γ : ℝ =>
      fullZeroForm (cosineSource F₀ γ) + fullZeroForm (sineSource F₀ γ) := by
    have heq : (fun γ : ℝ => fullZeroForm (cosineSource F₀ γ) + fullZeroForm (sineSource F₀ γ)) =
        fun γ : ℝ =>
          (zetaZeroConfig.W (complexModulatedSource F₀ γ) (complexModulatedSource F₀ γ)).re :=
      funext (fullZeroForm_cosine_add_sine_eq_zeta_W_re hF₀ hF₀c)
    rw [heq]
    exact (continuous_zeta_W_re_modulated hF₀ hF₀c).1
  have hcore_sum_int : IntegrableOn (fun γ : ℝ => ∑ ρ ∈ C_core, coreQ ρ γ) (Icc Γ (Γ + H)) :=
    (continuous_finsetSum C_core hcore_cont).integrableOn_Icc
  have hlhs_int : IntegrableOn
      (fun γ : ℝ => (∑ ρ ∈ C_core, coreQ ρ γ) -
        ∑' ρ : zetaZeroConfig.carrier,
          (zetaZeroConfig.mult ρ : ℝ) *
            ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (ρ : ℂ) - (γ : ℂ)) -
              paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (ρ : ℂ)) - (γ : ℂ))‖ ^ 2 / 4)
      (Icc Γ (Γ + H)) :=
    hcore_sum_int.sub hint_tsum
  have hint_ge := setIntegral_mono_on hlhs_int hquad_cont.integrableOn_Icc measurableSet_Icc
    fun γ _ => by
      rw [fullZeroForm_cosine_add_sine_eq_zeta_W_re hF₀ hF₀c γ]
      exact re_zeta_W_complexModulatedSource_ge_finset hF₀ hF₀c γ C_core (hd_sub_sum γ)
  rw [integral_sub hcore_sum_int hint_tsum,
    integral_finsetSum C_core (fun ρ hρ => (hcore_cont ρ hρ).integrableOn_Icc)] at hint_ge
  have hcore_each : ∀ ρ ∈ C_core,
      (zetaZeroConfig.mult ρ : ℝ) *
          (2 * Real.pi * (∫ u, F₀ u ^ 2) -
            (16 * Real.pi / H ^ 2) * Real.exp A * envelopeWindowNorm F₀ ^ 2) ≤
        ∫ γ in Icc Γ (Γ + H), coreQ ρ γ := fun ρ hρ => by
    obtain ⟨hr0, hr1, hi1, hi2⟩ := hmem_core ρ hρ
    have hb := (integral_window_norm_paperFT_depthSum_sq_ge hF₀ hF₀c hH0 hA0 hsupp hr0 hr1
      hi1 hi2).2
    dsimp [coreQ]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _)
  have hmult_sum_eq : (∑ ρ ∈ C_core, (zetaZeroConfig.mult ρ : ℝ)) =
      ∑ ξ₀ ∈ W_core, (xiSupportMultiplicity ξ₀ : ℝ) := by
    dsimp [C_core]; rw [Finset.sum_map]
    refine Finset.sum_congr rfl fun ξ₀ _ => ?_
    exact_mod_cast (xiDivisorZetaCarrierEquiv_multiplicity ξ₀).symm
  obtain ⟨hrvm_low, hrvm_high⟩ := hcore Γ ((le_max_right _ _).trans hΓ) H hH1 hH2
  have hmass_nn : 0 ≤ ∫ u, F₀ u ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hcore_sum_ge : (1 / 8) * H * Real.log Γ * (∫ u, F₀ u ^ 2) -
        (16 * Real.pi * Real.log Γ / H) * Real.exp A * envelopeWindowNorm F₀ ^ 2 ≤
      ∑ ρ ∈ C_core, ∫ γ in Icc Γ (Γ + H), coreQ ρ γ := by
    have hs := Finset.sum_le_sum hcore_each
    rw [← Finset.sum_mul, hmult_sum_eq] at hs
    have hp1 : (1 / 8) * H * Real.log Γ * (∫ u, F₀ u ^ 2) ≤
        (∑ ξ₀ ∈ W_core, (xiSupportMultiplicity ξ₀ : ℝ)) * (2 * Real.pi * (∫ u, F₀ u ^ 2)) := by
      calc (1 / 8) * H * Real.log Γ * (∫ u, F₀ u ^ 2)
          = ((1 / (16 * Real.pi)) * H * Real.log Γ) * (2 * Real.pi * (∫ u, F₀ u ^ 2)) := by
            field_simp [Real.pi_ne_zero]; ring
        _ ≤ (∑ ξ₀ ∈ W_core, (xiSupportMultiplicity ξ₀ : ℝ)) *
              (2 * Real.pi * (∫ u, F₀ u ^ 2)) :=
            mul_le_mul_of_nonneg_right hrvm_low (by positivity)
    have hp2 : (∑ ξ₀ ∈ W_core, (xiSupportMultiplicity ξ₀ : ℝ)) *
          ((16 * Real.pi / H ^ 2) * Real.exp A * envelopeWindowNorm F₀ ^ 2) ≤
        (16 * Real.pi * Real.log Γ / H) * Real.exp A * envelopeWindowNorm F₀ ^ 2 := by
      calc (∑ ξ₀ ∈ W_core, (xiSupportMultiplicity ξ₀ : ℝ)) *
            ((16 * Real.pi / H ^ 2) * Real.exp A * envelopeWindowNorm F₀ ^ 2)
          ≤ (H * Real.log Γ) * ((16 * Real.pi / H ^ 2) * Real.exp A * envelopeWindowNorm F₀ ^ 2) :=
            mul_le_mul_of_nonneg_right hrvm_high (by positivity)
        _ = (16 * Real.pi * Real.log Γ / H) * Real.exp A * envelopeWindowNorm F₀ ^ 2 := by
            field_simp [hH0.ne']
            ring
    linarith
  have hGloc_sub : (∑ q ∈ G_loc,
      (∫ γ in Icc Γ (Γ + H),
        ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (q.1 : ℂ) - (γ : ℂ)) -
          paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (q.1 : ℂ)) - (γ : ℂ))‖ ^ 2) / 4) ≤
      (∑ q ∈ G_loc, localZeroWeight A q) * ∫ u, F₀ u ^ 2 := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun q _ => ?_
    obtain ⟨_, hb1, hb2⟩ := integral_norm_paperFT_depthDiff_sq_le hF₀.continuous hF₀c hA0 hsupp
      (q.1 : ℂ) Γ (Γ + H)
    have hsq_abs : ((q.1 : ℂ).re - 1 / 2) ^ 2 = (foldedRe q - 1 / 2) ^ 2 := by
      rw [foldedRe_sub_half_eq_abs, sq_abs]
    rw [← foldedRe_sub_half_eq_abs q] at hb1 hb2
    rw [hsq_abs] at hb2
    unfold localZeroWeight
    rcases min_cases
      ((Real.pi / 2) * Real.exp (2 * A * (foldedRe q - 1 / 2)))
      (2 * Real.pi * A ^ 2 * (foldedRe q - 1 / 2) ^ 2 * Real.exp (2 * A * (foldedRe q - 1 / 2)))
      with ⟨heq, _⟩ | ⟨heq, _⟩ <;> (rw [heq]; linarith)
  have hsel_bound := hshell Γ ((le_max_left _ _).trans hΓ) H hH1 hH2 A hA0 hA G_loc hG_loc
  -- Error terms.
  have herr_core : (1 / H) * ((16 * Real.pi * Real.log Γ / H) * Real.exp A *
      envelopeWindowNorm F₀ ^ 2) ≤ 16 * Real.pi * K₁ * Γ ^ (-(1 / 2 : ℝ)) *
        envelopeWindowNorm F₀ ^ 2 := by
    have e : (1 / H) * ((16 * Real.pi * Real.log Γ / H) * Real.exp A * envelopeWindowNorm F₀ ^ 2) =
        16 * Real.pi * (Real.exp A * Real.log Γ * (1 / H ^ 2)) * envelopeWindowNorm F₀ ^ 2 := by
      field_simp [hH0.ne']
      ring
    rw [e]
    have hb : Real.exp A * Real.log Γ * (1 / H ^ 2) ≤ K₁ * Γ ^ (-(1 / 2 : ℝ)) := by
      calc Real.exp A * Real.log Γ * (1 / H ^ 2)
          ≤ Γ ^ (1 / 2 : ℝ) * (K₁ * Γ ^ (1 / 6 : ℝ)) * Γ ^ (-(198 / 100 : ℝ)) :=
            mul_le_mul (mul_le_mul hexpA_half hlog1 hlogΓ_nn (Real.rpow_nonneg hΓ0.le _))
              hinvH2 (by positivity) (by positivity)
        _ = K₁ * (Γ ^ (1 / 2 : ℝ) * Γ ^ (1 / 6 : ℝ) * Γ ^ (-(198 / 100 : ℝ))) := by ring
        _ ≤ K₁ * Γ ^ (-(1 / 2 : ℝ)) := mul_le_mul_of_nonneg_left hkey (by linarith)
    have := mul_le_mul_of_nonneg_left hb (by positivity : (0 : ℝ) ≤ 16 * Real.pi)
    nlinarith [sq_nonneg (envelopeWindowNorm F₀)]
  have herr_tail : (1 / H) * ((8 * (xiLineTwoLogDerivConstant + Real.log (2 * Γ + 4)) / H) *
      Real.exp A * envelopeWindowNorm F₀ ^ 2) ≤ Cx * Γ ^ (-(1 / 2 : ℝ)) * envelopeWindowNorm F₀ ^ 2 := by
    have hlog24 : Real.log (2 * Γ + 4) ≤ 3 * Real.log Γ := by
      have : Real.log (2 * Γ + 4) ≤ Real.log (Γ ^ 3) := Real.log_le_log (by positivity) (by nlinarith)
      rw [Real.log_pow] at this; push_cast at this; linarith
    have hconst : xiLineTwoLogDerivConstant + Real.log (2 * Γ + 4) ≤
        (|xiLineTwoLogDerivConstant| + 3 * K₁) * Γ ^ (1 / 6 : ℝ) := by
      have h1 : xiLineTwoLogDerivConstant ≤ |xiLineTwoLogDerivConstant| * Γ ^ (1 / 6 : ℝ) := by
        have : (1 : ℝ) ≤ Γ ^ (1 / 6 : ℝ) := Real.one_le_rpow hΓ1 (by norm_num)
        nlinarith [le_abs_self xiLineTwoLogDerivConstant, abs_nonneg xiLineTwoLogDerivConstant]
      nlinarith
    have hpos : 0 ≤ (|xiLineTwoLogDerivConstant| + 3 * K₁) * Γ ^ (1 / 6 : ℝ) := by positivity
    have e : (1 / H) * ((8 * (xiLineTwoLogDerivConstant + Real.log (2 * Γ + 4)) / H) *
        Real.exp A * envelopeWindowNorm F₀ ^ 2) =
        8 * (xiLineTwoLogDerivConstant + Real.log (2 * Γ + 4)) * Real.exp A * (1 / H ^ 2) *
          envelopeWindowNorm F₀ ^ 2 := by
      field_simp [hH0.ne']
      ring
    rw [e]
    have hb : 8 * (xiLineTwoLogDerivConstant + Real.log (2 * Γ + 4)) * Real.exp A * (1 / H ^ 2) ≤
        Cx * Γ ^ (-(1 / 2 : ℝ)) := by
      have hEH : Real.exp A * (1 / H ^ 2) ≤ Γ ^ (1 / 2 : ℝ) * Γ ^ (-(198 / 100 : ℝ)) :=
        mul_le_mul hexpA_half hinvH2 (by positivity) (Real.rpow_nonneg hΓ0.le _)
      calc 8 * (xiLineTwoLogDerivConstant + Real.log (2 * Γ + 4)) * Real.exp A * (1 / H ^ 2)
          = 8 * (xiLineTwoLogDerivConstant + Real.log (2 * Γ + 4)) *
              (Real.exp A * (1 / H ^ 2)) := by ring
        _ ≤ 8 * ((|xiLineTwoLogDerivConstant| + 3 * K₁) * Γ ^ (1 / 6 : ℝ)) *
              (Real.exp A * (1 / H ^ 2)) :=
            mul_le_mul_of_nonneg_right (by linarith [hconst]) (by positivity)
        _ ≤ 8 * ((|xiLineTwoLogDerivConstant| + 3 * K₁) * Γ ^ (1 / 6 : ℝ)) *
              (Γ ^ (1 / 2 : ℝ) * Γ ^ (-(198 / 100 : ℝ))) :=
            mul_le_mul_of_nonneg_left hEH (by positivity)
        _ = Cx * (Γ ^ (1 / 2 : ℝ) * Γ ^ (1 / 6 : ℝ) * Γ ^ (-(198 / 100 : ℝ))) := by
            rw [hCx_def]; ring
        _ ≤ Cx * Γ ^ (-(1 / 2 : ℝ)) := mul_le_mul_of_nonneg_left hkey hCx
    nlinarith [sq_nonneg (envelopeWindowNorm F₀)]
  have hmain_pos : (1 / H) * ((1 / 8) * H * Real.log Γ * (∫ u, F₀ u ^ 2)) =
      (1 / 8) * Real.log Γ * (∫ u, F₀ u ^ 2) := by field_simp [hH0.ne']
  have hsel_mass : (1 / H) * ((∑ q ∈ G_loc, localZeroWeight A q) * (∫ u, F₀ u ^ 2)) ≤
      (1 / 16) * Real.log Γ * (∫ u, F₀ u ^ 2) := by
    calc (1 / H) * ((∑ q ∈ G_loc, localZeroWeight A q) * (∫ u, F₀ u ^ 2))
        = ((1 / H) * ∑ q ∈ G_loc, localZeroWeight A q) * (∫ u, F₀ u ^ 2) := by ring
      _ ≤ ((1 / 16) * Real.log Γ) * (∫ u, F₀ u ^ 2) :=
          mul_le_mul_of_nonneg_right hsel_bound hmass_nn
      _ = (1 / 16) * Real.log Γ * (∫ u, F₀ u ^ 2) := by ring
  have h1 := mul_le_mul_of_nonneg_left hint_ge (by positivity : 0 ≤ 1 / H)
  have h2 := mul_le_mul_of_nonneg_left hcore_sum_ge (by positivity : 0 ≤ 1 / H)
  have h3 := mul_le_mul_of_nonneg_left (hsub_win.trans (add_le_add hGloc_sub le_rfl))
    (by positivity : 0 ≤ 1 / H)
  have hC₀ : C₀ * Γ ^ (-(1 / 2 : ℝ)) * envelopeWindowNorm F₀ ^ 2 =
      16 * Real.pi * K₁ * Γ ^ (-(1 / 2 : ℝ)) * envelopeWindowNorm F₀ ^ 2 +
        Cx * Γ ^ (-(1 / 2 : ℝ)) * envelopeWindowNorm F₀ ^ 2 := by rw [hC₀_def]; ring
  rw [mul_sub] at h1
  rw [mul_sub] at h2
  rw [mul_add] at h3
  linarith [h1, h2, h3, hmain_pos, hsel_mass, herr_core, herr_tail, hC₀]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
