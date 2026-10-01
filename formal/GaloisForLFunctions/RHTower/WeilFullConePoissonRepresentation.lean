import GaloisForLFunctions.RHTower.WeilFullConeBoundaryMeasure

/-!
# The Poisson representation of the Weil function

Let `lam` be full-cone Weil-positive, with boundary measure `μ_lam` (`boundaryMeasure`).  For
`Re s > 1`, with `w = s − ½`,

`Re Φ_lam(s) = Re w · ∫ |w − ir|⁻² dμ_lam(r)`  (`re_weilFunction_eq_lintegral`),

i.e. `Re Φ_lam` is the Poisson integral of `μ_lam` (since `Re(1/(w − ir)) = Re w/|w − ir|²`).  In
particular `∫ dμ_lam/(1 + r²) < ∞` (`lintegral_inv_one_add_sq_lt_top`, the case `s = 3/2`).

**Proof.**  On the tests `h_j` of `WeilFullConeHerglotzRightHalfPlane`, the Weil functional is
`∫ |ĥ_j|² dμ_lam` (`weilFullFunctional_weilTest_eq_lintegral`) and tends to `Re Φ_lam(s)/Re w`
(`tendsto_re_autoCorr`).  Pointwise `ĥ_j(r) → 1/(w − ir)` with `|ĥ_j| ≤ 2|w − ir|⁻¹`.  Fatou bounds
`∫ |w − ir|⁻² dμ_lam` by the limit, and then dominated convergence identifies it.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate NNReal ENNReal
open Zeta23

noncomputable section

namespace RHTower.WeilSpectral

open WeilHerglotz

/-- **The limit of the test functionals.**  For `Re s > 1` and `w = s − ½`,
`Re W_lam(h_j ⋆ h̃_j) → Re Φ_lam(s) / Re w`. -/
theorem tendsto_re_autoCorr {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {s : ℂ} (hs : 1 < s.re) :
    Tendsto (fun j : ℕ => (weilFullFunctional lam (autoCorr (s - 1 / 2) j)).re) atTop
      (𝓝 ((weilFunction lam s).re / (s - 1 / 2).re)) := by
  set w : ℂ := s - 1 / 2 with hwdef
  have hw : 1 / 2 < w.re := by rw [hwdef]; norm_num; linarith
  have hw0 : 0 < w.re := by linarith
  have hsw : s = w + 1 / 2 := by rw [hwdef]; ring
  have hfun : ∀ j : ℕ, weilFullFunctional lam (autoCorr w j) =
      (paperFT (autoCorr w j) (I / 2) + paperFT (autoCorr w j) (-I / 2))
        - (∑' n : ℕ, primeCoeff lam n * (autoCorr w j (Real.log n) + autoCorr w j (-Real.log n)))
        + (1 / (2 * π) : ℂ) * ∫ r : ℝ, paperFT (autoCorr w j) r * (EF.gammaBracket r : ℂ) := by
    intro j
    rfl
  have hlim := ((tendsto_pole hw).sub (tendsto_prime hW hw)).add
    ((tendsto_arch hw0).const_mul (1 / (2 * π) : ℂ))
  simp_rw [← hfun] at hlim
  have hre := (Complex.continuous_re.tendsto _).comp hlim
  have hL : (1 / (w + 1 / 2) * conj (1 / (w - 1 / 2)) + 1 / (w - 1 / 2) * conj (1 / (w + 1 / 2)) -
      ∑' n : ℕ, primeCoeff lam n * (oneSidedCorr w (Real.log n) + oneSidedCorr w (-Real.log n)) +
      (1 / (2 * π) : ℂ) * ∫ r : ℝ, 1 / (w - I * r) * conj (1 / (w - I * r)) *
        (EF.gammaBracket r : ℂ)).re = (weilFunction lam s).re / w.re := by
    rw [prime_limit_eq hW hw, arch_limit_eq hw0, Complex.add_re, Complex.sub_re, pole_limit_re hw,
      Complex.ofReal_re, Complex.ofReal_re]
    have hdig : (Complex.digamma (((1 / 4 + w.re / 2 : ℝ) : ℂ) + ((w.im / 2 : ℝ) : ℂ) * I)) =
        Complex.digamma (s / 2) := by
      congr 1
      rw [hsw]
      apply Complex.ext <;> simp; ring
    rw [hdig]
    have h1 : w + 1 / 2 = s := hsw.symm
    have h2 : w - 1 / 2 = s - 1 := by rw [hsw]; ring
    rw [h1, h2, weilFunction]
    simp only [Complex.sub_re, Complex.add_re, Complex.div_ofNat_re, Complex.ofReal_re]
    field_simp
    ring
  rw [← hL]
  exact hre

/-- The Poisson density `|w − ir|⁻²` as an `ℝ≥0∞`-valued function. -/
def poissonDensity (w : ℂ) (r : ℝ) : ℝ≥0∞ := ((‖1 / (w - I * (r : ℂ))‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞)

theorem measurable_poissonDensity (w : ℂ) : Measurable (poissonDensity w) := by
  unfold poissonDensity
  refine (Measurable.pow_const ?_ 2).coe_nnreal_ennreal
  exact (by fun_prop : Measurable fun r : ℝ => 1 / (w - I * (r : ℂ))).nnnorm

theorem specDensity_testFn_le {w : ℂ} (hw : 0 < w.re) (j : ℕ) (r : ℝ) :
    (specDensity (testFn w j) r : ℝ≥0∞) ≤ 4 * poissonDensity w r := by
  have h := norm_paperFT_testFn_le hw j r
  have hne : ‖w - I * (r : ℂ)‖ ≠ 0 := by
    rw [norm_ne_zero_iff]
    intro h0
    have := congrArg Complex.re h0
    rw [re_sub_I_mul_ofReal] at this
    simp at this
    linarith
  unfold specDensity poissonDensity
  rw [show (4 : ℝ≥0∞) = ((4 : ℝ≥0) : ℝ≥0∞) by norm_num, ← ENNReal.coe_mul, ENNReal.coe_le_coe,
    ← NNReal.coe_le_coe]
  push_cast
  rw [norm_div, norm_one]
  have hpos : 0 < ‖w - I * (r : ℂ)‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
  calc ‖paperFT (testFn w j) r‖ ^ 2 ≤ (2 / ‖w - I * (r : ℂ)‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = 4 * (1 / ‖w - I * (r : ℂ)‖) ^ 2 := by ring

theorem tendsto_specDensity_testFn {w : ℂ} (hw : 0 < w.re) (r : ℝ) :
    Tendsto (fun j : ℕ => (specDensity (testFn w j) r : ℝ≥0∞)) atTop (𝓝 (poissonDensity w r)) := by
  have hre : 0 < (w - I * (r : ℂ)).re := by rw [re_sub_I_mul_ofReal]; exact hw
  have h := tendsto_paperFT_testFn hre
  unfold specDensity poissonDensity
  exact ENNReal.tendsto_coe.mpr ((continuous_nnnorm.tendsto _).comp h |>.pow 2)

/-- **The Poisson representation.**  For `Re s > 1` and `w = s − ½`,
`∫ |w − ir|⁻² dμ_lam = Re Φ_lam(s) / Re w`, and the integral is finite. -/
theorem lintegral_poissonDensity_eq {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {s : ℂ}
    (hs : 1 < s.re) :
    (∫⁻ r, poissonDensity (s - 1 / 2) r ∂boundaryMeasure hW) =
      ENNReal.ofReal ((weilFunction lam s).re / (s - 1 / 2).re) := by
  set w : ℂ := s - 1 / 2 with hwdef
  have hw0 : 0 < w.re := by rw [hwdef]; norm_num; linarith
  set μ := boundaryMeasure hW with hμ
  set F : ℕ → ℝ → ℝ≥0∞ := fun j r => (specDensity (testFn w j) r : ℝ≥0∞) with hF
  have hFmeas : ∀ j, Measurable (F j) := fun j =>
    (measurable_specDensity ((continuous_testFn w j).integrable_of_hasCompactSupport
      (hasCompactSupport_testFn w j))).coe_nnreal_ennreal
  -- the integrals of `F j` are the test functionals
  have hrep : ∀ j, (∫⁻ r, F j r ∂μ) < ⊤ ∧
      weilFullFunctional lam (autoCorr w j) = (((∫⁻ r, F j r ∂μ).toReal : ℝ) : ℂ) := fun j =>
    weilFullFunctional_weilTest_eq_lintegral hW (contDiff_testFn w j) (hasCompactSupport_testFn w j)
  have hlimR := tendsto_re_autoCorr hW hs
  rw [← hwdef] at hlimR
  have hlimE : Tendsto (fun j => ∫⁻ r, F j r ∂μ) atTop
      (𝓝 (ENNReal.ofReal ((weilFunction lam s).re / w.re))) := by
    have := ENNReal.tendsto_ofReal hlimR
    refine this.congr fun j => ?_
    rw [(hrep j).2, Complex.ofReal_re, ENNReal.ofReal_toReal (hrep j).1.ne]
  -- Fatou
  have hfatou : (∫⁻ r, poissonDensity w r ∂μ) ≤ ENNReal.ofReal ((weilFunction lam s).re / w.re) := by
    have hl := lintegral_liminf_le (μ := μ) (u := atTop) hFmeas
    have hpt : ∀ r, liminf (fun j => F j r) atTop = poissonDensity w r := fun r =>
      (tendsto_specDensity_testFn hw0 r).liminf_eq
    simp_rw [hpt] at hl
    rwa [hlimE.liminf_eq] at hl
  have hfin : (∫⁻ r, 4 * poissonDensity w r ∂μ) ≠ ⊤ := by
    rw [lintegral_const_mul _ (measurable_poissonDensity w)]
    exact ENNReal.mul_ne_top (by norm_num) (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hfatou)
  -- dominated convergence
  have hdom := tendsto_lintegral_of_dominated_convergence (μ := μ) (F := F)
    (fun r => 4 * poissonDensity w r) hFmeas
    (fun j => Eventually.of_forall fun r => specDensity_testFn_le hw0 j r) hfin
    (Eventually.of_forall fun r => tendsto_specDensity_testFn hw0 r)
  exact tendsto_nhds_unique hdom hlimE

/-- **Growth of the boundary measure.** `∫ dμ_lam/(1 + r²) < ∞`. -/
theorem lintegral_poissonDensity_three_halves_lt_top {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    (∫⁻ r, poissonDensity 1 r ∂boundaryMeasure hW) < ⊤ := by
  have h := lintegral_poissonDensity_eq hW (s := 3 / 2) (by norm_num)
  rw [show (3 / 2 : ℂ) - 1 / 2 = 1 by norm_num] at h
  rw [h]
  exact ENNReal.ofReal_lt_top

end RHTower.WeilSpectral

end
