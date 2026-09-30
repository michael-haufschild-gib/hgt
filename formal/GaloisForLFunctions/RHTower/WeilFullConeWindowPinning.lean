import GaloisForLFunctions.RHTower.WeilFullConeOneSidedCriterion
import GaloisForLFunctions.RHTower.SelbergSymbolCriticalStrip

/-!
# Window pinning of the Weil cone

Fix a real `C²` bump `g` supported in `[−¼, ¼]`, with autocorrelation `ρ(x) = ∫ g(t) g(t − x) dt`.
For weights `lam`, the smoothed log-window at `L` is
`S_L(lam) = Σ_{n≥2} lam(n) (ρ(log n − L) + ρ(log n + L)) / √n`.

**Theorem** (`exists_abs_windowSum_sub_le`). There is a constant `C`, depending only on `g`, such
that every full-cone Weil-positive `lam` satisfies
`|S_L(lam) − 2 P₊ P₋ cosh(L/2)| ≤ C` for every `L ∈ ℝ`, where `P_± = ∫ g(u) e^{∓u/2} du`.

In prime-number-theorem normalization, put `w(u) = e^{−u/2}ρ(u)`. Then every member of the Weil
cone obeys `Σ_n lam(n) w(log n − L) = e^{L} ∫ w(u) e^{u} du + O_g(e^{L/2})` as `L → ∞`, since
`∫ w(u)e^{u} du = P₊P₋`. This is a smoothed prime number theorem with square-root error, uniform
over the whole cone.

**Proof.** Apply Weil positivity to the shift pairs `f_± = g ± g(· − L)`. Their autocorrelation
is `2ρ ± (ρ(· + L) + ρ(· − L))`, and it vanishes at `±log n` except through the shifted copies.
- The pole term is `2P₊P₋(2 ± 2cosh(L/2))`.
- The archimedean term is bounded by `4∫|ĝ|²|μ|`, uniformly in `L`.
- The prime term is `±2 S_L(lam)`.

The two signs give the two-sided bound.
-/

open Complex MeasureTheory Filter Topology Set Finsupp
open scoped Real ComplexConjugate ContDiff
open Zeta23

namespace RHTower.WeilOneSided

noncomputable section

variable {g : ℝ → ℝ}

/-! ## The real autocorrelation -/

/-- The autocorrelation `ρ(x) = ∫ g(t) g(t − x) dt`. -/
def autoCorr (g : ℝ → ℝ) (x : ℝ) : ℝ := ∫ t, g t * g (t - x)

/-- The complex lift of `g`. -/
def liftC (g : ℝ → ℝ) (u : ℝ) : ℂ := (g u : ℂ)

theorem weilTest_liftC (g : ℝ → ℝ) (x : ℝ) :
    EF.weilTest (liftC g) (liftC g) x = (autoCorr g x : ℂ) := by
  rw [weilTest_apply, autoCorr, ← integral_complex_ofReal]
  congr 1; funext t
  simp only [liftC, Complex.conj_ofReal]
  push_cast; ring

theorem autoCorr_neg (g : ℝ → ℝ) (x : ℝ) : autoCorr g (-x) = autoCorr g x := by
  unfold autoCorr
  rw [← integral_sub_right_eq_self (μ := volume) (fun t => g t * g (t - -x)) x]
  congr 1; funext t
  simp only [sub_neg_eq_add, sub_add_cancel]
  ring

theorem autoCorr_eq_zero (hsupp : ∀ u, 1 / 4 < |u| → g u = 0) {x : ℝ} (hx : 1 / 2 < |x|) :
    autoCorr g x = 0 := by
  unfold autoCorr
  have h0 : (fun t => g t * g (t - x)) = fun _ => 0 := by
    funext t
    rcases le_or_gt |t| (1 / 4) with ht | ht
    · have : 1 / 4 < |t - x| := by
        have := abs_sub_abs_le_abs_sub x t
        rw [abs_sub_comm] at this; linarith
      simp [hsupp _ this]
    · simp [hsupp t ht]
  rw [h0, integral_zero]

/-! ## Shift pairs -/

/-- The shift pair `g + σ g(· − L)`. -/
def shiftPair (g : ℝ → ℝ) (σ L : ℝ) (u : ℝ) : ℂ := liftC g u + (σ : ℂ) * liftC g (u - L)

theorem shiftPair_eq_sum (g : ℝ → ℝ) (σ L : ℝ) :
    shiftPair g σ L = fun u => ∑ m ∈ Finset.range 2,
      (if m = 0 then (1 : ℂ) else (σ : ℂ)) * liftC g (u - if m = 0 then 0 else L) := by
  funext u
  simp [shiftPair, Finset.sum_range_succ]

theorem contDiff_liftC (hg : ContDiff ℝ 2 g) : ContDiff ℝ 2 (liftC g) :=
  ofRealCLM.contDiff.comp hg

theorem hasCompactSupport_liftC (hgc : HasCompactSupport g) : HasCompactSupport (liftC g) :=
  hgc.comp_left Complex.ofReal_zero

theorem contDiff_shiftPair (hg : ContDiff ℝ 2 g) (σ L : ℝ) : ContDiff ℝ 2 (shiftPair g σ L) :=
  (contDiff_liftC hg).add (contDiff_const.mul ((contDiff_liftC hg).comp
    (contDiff_id.sub contDiff_const)))

theorem hasCompactSupport_shiftPair (hgc : HasCompactSupport g) (σ L : ℝ) :
    HasCompactSupport (shiftPair g σ L) :=
  (hasCompactSupport_liftC hgc).add
    ((hasCompactSupport_liftC hgc).comp_homeomorph (Homeomorph.subRight L)).mul_left

/-- The autocorrelation of a shift pair. -/
theorem weilTest_shiftPair (hg : Continuous g) (hgc : HasCompactSupport g) (σ L y : ℝ) :
    EF.weilTest (shiftPair g σ L) (shiftPair g σ L) y =
      ((1 + σ ^ 2) * autoCorr g y + σ * (autoCorr g (y + L) + autoCorr g (y - L)) : ℝ) := by
  rw [shiftPair_eq_sum, weilTest_sum_translates
    (show Continuous (liftC g) from Complex.continuous_ofReal.comp hg) (hasCompactSupport_liftC hgc)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, if_true, one_ne_zero,
    if_false, Complex.conj_ofReal, map_one, mul_one, one_mul, sub_zero, add_zero,
    weilTest_liftC]
  rw [show y - L + L = y by ring]
  push_cast
  ring

/-! ## The `ℓ`-vector of a shift pair -/

/-- The window value `(ρ(log n − L) + ρ(log n + L))/√n`. -/
def windowValue (g : ℝ → ℝ) (L : ℝ) (n : ℕ) : ℝ :=
  (autoCorr g (Real.log n - L) + autoCorr g (Real.log n + L)) / Real.sqrt n

theorem logValue_shiftPair (hg : Continuous g) (hgc : HasCompactSupport g)
    (hsupp : ∀ u, 1 / 4 < |u| → g u = 0) (σ L : ℝ) {n : ℕ} (hn : 2 ≤ n) :
    logValue (shiftPair g σ L) n = 2 * σ * windowValue g L n := by
  have hlog : 1 / 2 < Real.log n := by
    have := Real.log_le_log two_pos (by exact_mod_cast hn : (2 : ℝ) ≤ n)
    linarith [WeilExcess.seventeen_div_twentyfive_lt_log_two]
  have h1 := autoCorr_eq_zero hsupp (x := Real.log n) (by rw [abs_of_pos (by linarith)]; exact hlog)
  have h2 := autoCorr_eq_zero hsupp (x := -Real.log n)
    (by rw [abs_neg, abs_of_pos (by linarith)]; exact hlog)
  rw [logValue, weilTest_shiftPair hg hgc, weilTest_shiftPair hg hgc, h1, h2, windowValue,
    show -Real.log n + L = -(Real.log n - L) by ring,
    show -Real.log n - L = -(Real.log n + L) by ring, autoCorr_neg, autoCorr_neg]
  rw [← Complex.ofReal_add, Complex.ofReal_re]
  ring

/-- The shift pair as a Weil test. -/
def shiftPairFn (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (σ L : ℝ) : WeilTestFn :=
  ⟨shiftPair g σ L, contDiff_shiftPair hg σ L, hasCompactSupport_shiftPair hgc σ L⟩

theorem finite_support_windowValue (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hsupp : ∀ u, 1 / 4 < |u| → g u = 0) (L : ℝ) :
    (Function.support fun j : LogIndex => windowValue g L j).Finite := by
  refine (finite_support_logValue (shiftPairFn hg hgc 1 L)).subset fun j hj => ?_
  simp only [Function.mem_support] at hj ⊢
  change logValue (shiftPair g 1 L) j ≠ 0
  rw [logValue_shiftPair hg.continuous hgc hsupp 1 L j.2]
  simpa using hj

/-- The window vector, finitely supported on `n ≥ 2`. -/
def windowVector (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hsupp : ∀ u, 1 / 4 < |u| → g u = 0) (L : ℝ) : LogIndex →₀ ℝ :=
  Finsupp.ofSupportFinite (fun j => windowValue g L j) (finite_support_windowValue hg hgc hsupp L)

/-- The smoothed log-window `S_L(lam) = Σ_{n≥2} lam(n)(ρ(log n − L) + ρ(log n + L))/√n`. -/
def windowSum (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hsupp : ∀ u, 1 / 4 < |u| → g u = 0) (lam : ℕ → ℝ) (L : ℝ) : ℝ :=
  linearCombination ℝ (fun j : LogIndex => lam j) (windowVector hg hgc hsupp L)

theorem logVector_shiftPairFn (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hsupp : ∀ u, 1 / 4 < |u| → g u = 0) (σ L : ℝ) :
    logVector (shiftPairFn hg hgc σ L) = (2 * σ) • windowVector hg hgc hsupp L := by
  ext j
  rw [logVector_apply, Finsupp.smul_apply, smul_eq_mul]
  change logValue (shiftPair g σ L) j = _
  rw [logValue_shiftPair hg.continuous hgc hsupp σ L j.2]
  simp [windowVector, Finsupp.ofSupportFinite_coe]

/-! ## The pole term -/

theorem integrable_liftC_mul_exp (hg : Continuous g) (hgc : HasCompactSupport g) (z : ℂ) :
    Integrable fun u : ℝ => liftC g u * Complex.exp (I * z * u) :=
  ((Complex.continuous_ofReal.comp hg).mul (by fun_prop)).integrable_of_hasCompactSupport
    (hasCompactSupport_liftC hgc).mul_right

theorem paperFT_shiftPair (hg : Continuous g) (hgc : HasCompactSupport g) (σ L : ℝ) (z : ℂ) :
    paperFT (shiftPair g σ L) z = paperFT (liftC g) z * (1 + σ * Complex.exp (I * z * L)) := by
  have htr := paperFT_translate' (liftC g) L z
  have hi1 := integrable_liftC_mul_exp hg hgc z
  have hi2 : Integrable fun u : ℝ => liftC g (u - L) * Complex.exp (I * z * u) :=
    ((show Continuous fun u : ℝ => liftC g (u - L) by unfold liftC; fun_prop).mul
      (by fun_prop)).integrable_of_hasCompactSupport
      ((hasCompactSupport_liftC hgc).comp_homeomorph (Homeomorph.subRight L)).mul_right
  have hsplit : paperFT (shiftPair g σ L) z =
      paperFT (liftC g) z + σ * paperFT (fun u => liftC g (u - L)) z := by
    unfold paperFT
    rw [← integral_const_mul, ← integral_add hi1 (hi2.const_mul _)]
    congr 1; funext u; simp only [shiftPair]; ring
  rw [hsplit, htr]; ring

theorem paperFT_liftC_half_I (g : ℝ → ℝ) :
    paperFT (liftC g) (I / 2) = ((∫ u, g u * Real.exp (-u / 2) : ℝ) : ℂ) := by
  rw [paperFT, ← integral_complex_ofReal]
  congr 1; funext u
  rw [liftC, Complex.ofReal_mul, Complex.ofReal_exp]
  congr 2
  push_cast
  rw [show I * (I / 2) * (u : ℂ) = (I * I) * u / 2 by ring, Complex.I_mul_I]
  ring

theorem paperFT_liftC_neg_half_I (g : ℝ → ℝ) :
    paperFT (liftC g) (-I / 2) = ((∫ u, g u * Real.exp (u / 2) : ℝ) : ℂ) := by
  rw [paperFT, ← integral_complex_ofReal]
  congr 1; funext u
  rw [liftC, Complex.ofReal_mul, Complex.ofReal_exp]
  congr 2
  push_cast
  rw [show I * (-I / 2) * (u : ℂ) = -(I * I) * u / 2 by ring, Complex.I_mul_I]
  ring

/-- The pole term of a shift pair. -/
theorem pole_shiftPair (hg : Continuous g) (hgc : HasCompactSupport g) (σ L : ℝ) :
    paperFT (EF.weilTest (shiftPair g σ L) (shiftPair g σ L)) (I / 2) +
        paperFT (EF.weilTest (shiftPair g σ L) (shiftPair g σ L)) (-I / 2) =
      ((2 * (∫ u, g u * Real.exp (-u / 2)) * (∫ u, g u * Real.exp (u / 2)) *
        ((1 + σ * Real.exp (-L / 2)) * (1 + σ * Real.exp (L / 2))) : ℝ) : ℂ) := by
  have hc : Continuous (shiftPair g σ L) := by unfold shiftPair liftC; fun_prop
  have hcs := hasCompactSupport_shiftPair hgc σ L
  have hconj1 : (starRingEnd ℂ) (I / 2) = -I / 2 := by
    rw [map_div₀, Complex.conj_I, map_ofNat]
  have hconj2 : (starRingEnd ℂ) (-I / 2) = I / 2 := by
    rw [map_div₀, map_neg, Complex.conj_I, neg_neg, map_ofNat]
  have e1 : Complex.exp (I * (I / 2) * (L : ℂ)) = (Real.exp (-L / 2) : ℂ) := by
    rw [Complex.ofReal_exp]; congr 1
    rw [show I * (I / 2) * (L : ℂ) = (I * I) * L / 2 by ring, Complex.I_mul_I]; push_cast; ring
  have e2 : Complex.exp (I * (-I / 2) * (L : ℂ)) = (Real.exp (L / 2) : ℂ) := by
    rw [Complex.ofReal_exp]; congr 1
    rw [show I * (-I / 2) * (L : ℂ) = -(I * I) * L / 2 by ring, Complex.I_mul_I]; push_cast; ring
  rw [EF.paperFT_weilTest hc hc hcs hcs, EF.paperFT_weilTest hc hc hcs hcs, hconj1, hconj2,
    paperFT_shiftPair hg hgc, paperFT_shiftPair hg hgc, e1, e2, paperFT_liftC_half_I,
    paperFT_liftC_neg_half_I]
  simp only [map_mul, map_add, map_one, Complex.conj_ofReal]
  push_cast; ring

/-! ## The archimedean term -/

theorem norm_paperFT_shiftPair_le (hg : Continuous g) (hgc : HasCompactSupport g) {σ : ℝ}
    (hσ : |σ| ≤ 1) (L τ : ℝ) :
    ‖paperFT (shiftPair g σ L) τ‖ ≤ 2 * ‖paperFT (liftC g) τ‖ := by
  rw [paperFT_shiftPair hg hgc, norm_mul, mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  refine (norm_add_le _ _).trans ?_
  rw [norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    show I * (τ : ℂ) * (L : ℂ) = ((τ * L : ℝ) : ℂ) * I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I]
  linarith

/-- The archimedean term of a shift pair is bounded uniformly in the shift. -/
theorem abs_arch_shiftPair_le (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) {σ : ℝ}
    (hσ : |σ| ≤ 1) (L : ℝ) :
    |((1 / (2 * π) : ℂ) * ∫ r : ℝ, paperFT (EF.weilTest (shiftPair g σ L) (shiftPair g σ L)) r *
        (EF.gammaBracket r : ℂ)).re| ≤
      4 * ∫ τ : ℝ, ‖paperFT (EF.weilTest (liftC g) (liftC g)) τ * (mu τ : ℂ)‖ := by
  have hgC := contDiff_liftC hg
  have hgCc := hasCompactSupport_liftC hgc
  have hρd := EF.weilTest_contDiff hgC hgC.continuous hgCc
  have hρc := EF.weilTest_hasCompactSupport hgCc hgCc
  have hB := (EF.integrable_paperFT_mul_mu hρd hρc gammaFacts).norm
  have hc : Continuous (shiftPair g σ L) := (contDiff_shiftPair hg σ L).continuous
  have hcs := hasCompactSupport_shiftPair hgc σ L
  rw [EF.gamma_term, ← integral_const_mul]
  refine (Complex.abs_re_le_norm _).trans (norm_integral_le_of_norm_le (hB.const_mul 4)
    (Eventually.of_forall fun τ => ?_))
  rw [paperFT_weilTest_self_ofReal hc hcs, paperFT_weilTest_self_ofReal hgC.continuous hgCc]
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_pow, abs_norm]
  have h1 := norm_paperFT_shiftPair_le hg.continuous hgc hσ L τ
  have h2 := norm_nonneg (paperFT (shiftPair g σ L) τ)
  have h3 : ‖paperFT (shiftPair g σ L) τ‖ ^ 2 ≤ 4 * ‖paperFT (liftC g) τ‖ ^ 2 := by nlinarith
  have h4 := mul_le_mul_of_nonneg_right h3 (abs_nonneg (mu τ))
  linarith

/-! ## Window pinning -/

/-- **Window pinning of the Weil cone.** Every full-cone Weil-positive `lam` has smoothed
log-windows within a constant (depending only on `g`) of `2P₊P₋ cosh(L/2)`. -/
theorem exists_abs_windowSum_sub_le (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hsupp : ∀ u, 1 / 4 < |u| → g u = 0) :
    ∃ C : ℝ, ∀ lam : ℕ → ℝ, WeilPositiveFull lam → ∀ L : ℝ,
      |windowSum hg hgc hsupp lam L - 2 * (∫ u, g u * Real.exp (-u / 2)) *
        (∫ u, g u * Real.exp (u / 2)) * Real.cosh (L / 2)| ≤ C := by
  set Pp := ∫ u, g u * Real.exp (-u / 2) with hPp
  set Pm := ∫ u, g u * Real.exp (u / 2) with hPm
  set B := ∫ τ : ℝ, ‖paperFT (EF.weilTest (liftC g) (liftC g)) τ * (mu τ : ℂ)‖ with hB
  refine ⟨2 * |Pp * Pm| + 2 * B, fun lam hW L => ?_⟩
  have key : ∀ σ : ℝ, |σ| ≤ 1 →
      2 * σ * windowSum hg hgc hsupp lam L ≤
        2 * Pp * Pm * ((1 + σ * Real.exp (-L / 2)) * (1 + σ * Real.exp (L / 2))) + 4 * B := by
    intro σ hσ
    have h0 := hW (shiftPair g σ L) (contDiff_shiftPair hg σ L) (hasCompactSupport_shiftPair hgc σ L)
    have e := re_weilFullFunctional_eq lam (shiftPairFn hg hgc σ L)
    change (weilFullFunctional lam (EF.weilTest (shiftPair g σ L) (shiftPair g σ L))).re =
      weilArchRe (EF.weilTest (shiftPair g σ L) (shiftPair g σ L)) -
        linearCombination ℝ (fun j : LogIndex => lam j) (logVector (shiftPairFn hg hgc σ L)) at e
    rw [e, logVector_shiftPairFn hg hgc hsupp, map_smul, smul_eq_mul, weilArchRe,
      Complex.add_re, pole_shiftPair hg.continuous hgc, Complex.ofReal_re] at h0
    have ha := abs_arch_shiftPair_le hg hgc hσ L
    have ha' := (abs_le.mp ha).2
    unfold windowSum
    linarith
  have hab : Real.exp (-L / 2) * Real.exp (L / 2) = 1 := by
    rw [← Real.exp_add, show -L / 2 + L / 2 = 0 by ring, Real.exp_zero]
  have hcosh : 2 * Real.cosh (L / 2) = Real.exp (L / 2) + Real.exp (-L / 2) := by
    rw [Real.cosh_eq, neg_div]; ring
  have k1 := key 1 (by norm_num)
  have k2 := key (-1) (by norm_num)
  have hPP := le_abs_self (Pp * Pm)
  have hPP' := neg_abs_le (Pp * Pm)
  rw [abs_le]
  constructor
  · have : 2 * Pp * Pm * ((1 + -1 * Real.exp (-L / 2)) * (1 + -1 * Real.exp (L / 2))) =
        2 * (Pp * Pm) * 2 - 2 * (Pp * Pm) * (2 * Real.cosh (L / 2)) := by
      rw [hcosh]; linear_combination (2 * (Pp * Pm)) * hab
    nlinarith
  · have : 2 * Pp * Pm * ((1 + 1 * Real.exp (-L / 2)) * (1 + 1 * Real.exp (L / 2))) =
        2 * (Pp * Pm) * 2 + 2 * (Pp * Pm) * (2 * Real.cosh (L / 2)) := by
      rw [hcosh]; linear_combination (2 * (Pp * Pm)) * hab
    nlinarith

end

end RHTower.WeilOneSided
