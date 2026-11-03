import GaloisForLFunctions.ConjugateDiagonalGeometry.WindowPortFlux.CauchyCapCancellationAndPolynomialStage
import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.NearLineDensityBesselCertificateAndSeparation

/-!
# Intrinsic Control of the Right Half-Port via Shifted and Critical-Line Flux Identities

Intrinsic bounds and rigidity equivalences for the right half-window port
`rightHalfPort y₁ y₂ N t = rightEdgeFlux y₁ y₂ N t + horizCapFlux (1/2) (3/2) y₁ y₂ N t`
from `[1/2, 3/2] × [y₁, y₂]` alone:

1. **Oscillatory integration by parts and shifted-abscissa right-port control**
   (`exists_vertFlux_inv_decay`, `exists_shortCap_inv_decay`,
   `rightHalfPort_eq_vertFlux_add_shortCap`, `exists_rightHalfPort_shifted_inv_decay`,
   `exists_criticalLineFlux_inv_decay_of_rightHalfZeroFree`):
   One integration by parts along `{σ} × [y₁, y₂]` upgrades `exists_norm_vertFlux_le_exp` to
   `‖vertFlux σ y₁ y₂ N t‖ ≤ C_V * exp((σ - 1/2) t) / (|t| + 1)` for all `t : ℝ`, and one
   integration by parts along `[1/2, σ₁] × {y₁, y₂}` bounds `horizCapFlux (1/2) σ₁` by
   `C_H * exp((σ₁ - 1/2) t) / (t + 1)` for `t ≥ 0`. Combining these with Cauchy cap cancellation
   yields `‖rightHalfPort(t)‖ ≤ C * exp((σ₁ - 1/2) t) / (t + 1)` and exact boundary Laplace
   integrability `exp(-2(σ₁ - 1/2) t) ‖rightHalfPort(t)‖² ∈ L¹(0, ∞)` whenever `A_N ≠ 0` on
   `[σ₁, 3/2] × [y₁, y₂]`, upgrading `rightHalfPort_eq_criticalLineFlux_of_rightHalfZeroFree` at
   `σ₁ = 1/2` to `O(1 / (|t| + 1))` and `L²(0, ∞)`.

2. **6-way zero-free window rigidity and 5-way uniform-boundedness equivalences**
   (`rightHalfPort_criticalLineFlux_zeroFree_tfae`, `rightHalfPort_uniformBounded_tfae`):
   On any boundary-regular centered window, the hypothesis `∀ z ∈ [1/2, 3/2] × [y₁, y₂], A_N z ≠ 0`
   of `rightHalfPort_eq_criticalLineFlux_of_rightHalfZeroFree` and unweighted `L²(0, ∞)` decay of
   `rightHalfPort` are both equivalent to total absence of window zeros (`𝒵_N ≡ 0`), whereas
   uniform boundedness `‖rightHalfPort(t)‖ ≤ M` (`t ≥ 0`) is equivalent to local critical-line
   purity (`Re z = 1/2`) and an `O(1 / (t + 1))`-accurate critical-line mode decomposition.

3. **Unconditional right-half-port control laws for `ζ`**
   (`exists_burnol_rightHalfPort_subHalfExp_inv_decay`,
   `almostAll_unitWindow_rightHalfPort_doubleLog_decay`,
   `microPlanckWindow_criticalLineFlux_volume_le`):
   Unconditionally for `ζ`'s integer-theta prefixes `A_N`, `rightHalfPort` satisfies:
   - `O(exp((burnolCapAbscissa m - 1/2) t) / (t + 1))` and boundary Laplace integrability on every
     Burnol unit window (`N ≥ capCancelSqrtPrefix m`);
   - `O(exp((3 log(log V) / log V) t) / (t + 1))` on all except `O(V / log(log V))` Burnol unit
     windows (`N ≥ doorSqrtPrefix m`);
   - exact critical-line flux identity `rightHalfPort = vertFlux (1/2)` and `O(1 / (|t| + 1))`
     decay on `(1 - O(B)) V` of micro-Planck windows `[t₀, t₀ + B / log V]` (`N = doorSqrtPrefix ⌊t₀⌋₊`).
-/

set_option autoImplicit false

open Complex MeasureTheory Set Filter intervalIntegral
open scoped BigOperators Topology Classical

noncomputable section

namespace GaloisForLFunctions.ConjugateDiagonalGeometry.WindowPortFlux

open GaloisForLFunctions.ConjugateDiagonalGeometry.SzegoCollision
open GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect
open GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean

/-! ## §1. Oscillatory integration by parts and shifted-abscissa right-port control -/

/-- **Oscillatory vertical-flux `O(e^{(σ - 1/2) t} / (|t| + 1))` decay.**
Whenever `finiteThetaAmplitude N` is nonvanishing along `{σ} × [y₁, y₂]` (`y₁ ≤ y₂`), one
integration by parts against `e^{i t y}` bounds `vertFlux σ y₁ y₂ N t` by
`C_V * exp((σ - 1/2) * t) / (|t| + 1)` for all `t : ℝ`. -/
theorem exists_vertFlux_inv_decay {σ y₁ y₂ : ℝ} (hy : y₁ ≤ y₂) (N : ℕ)
    (hnz : ∀ y ∈ Icc y₁ y₂, _root_.RHTower.finiteThetaAmplitude N ((σ : ℂ) + (y : ℂ) * I) ≠ 0) :
    ∃ C_V : ℝ, 0 < C_V ∧ ∀ t : ℝ,
      ‖vertFlux σ y₁ y₂ N t‖ ≤ C_V * Real.exp ((σ - 1 / 2) * t) / (|t| + 1) := by
  set g : ℝ → ℂ := fun y => thetaLogDeriv N ((σ : ℂ) + (y : ℂ) * I)
  set g' : ℝ → ℂ := fun y => I * deriv (thetaLogDeriv N) ((σ : ℂ) + (y : ℂ) * I)
  have hlin_cont : Continuous (fun u : ℝ => (σ : ℂ) + (u : ℂ) * I) := by fun_prop
  have hg_cont : ContinuousOn g (Icc y₁ y₂) := fun y hy_m =>
    (ContinuousAt.comp (g := thetaLogDeriv N) (f := fun u : ℝ => (σ : ℂ) + (u : ℂ) * I)
      (analyticAt_thetaLogDeriv (hnz y hy_m)).continuousAt hlin_cont.continuousAt).continuousWithinAt
  have hg'_cont : ContinuousOn g' (Icc y₁ y₂) := fun y hy_m =>
    ContinuousWithinAt.const_smul
      ((ContinuousAt.comp (g := deriv (thetaLogDeriv N)) (f := fun u : ℝ => (σ : ℂ) + (u : ℂ) * I)
        (analyticAt_thetaLogDeriv (hnz y hy_m)).deriv.continuousAt
        hlin_cont.continuousAt).continuousWithinAt) I
  obtain ⟨M₀, hM₀_bd⟩ := isCompact_Icc.exists_bound_of_continuousOn hg_cont
  obtain ⟨M₁, hM₁_bd⟩ := isCompact_Icc.exists_bound_of_continuousOn hg'_cont
  have hM₀_nn : 0 ≤ M₀ := (norm_nonneg (g y₁)).trans (hM₀_bd y₁ ⟨le_rfl, hy⟩)
  have hM₁_nn : 0 ≤ M₁ := (norm_nonneg (g' y₁)).trans (hM₁_bd y₁ ⟨le_rfl, hy⟩)
  have hdy : 0 ≤ y₂ - y₁ := sub_nonneg.mpr hy
  set K : ℝ := 2 * (2 * M₀ + (M₀ + M₁) * (y₂ - y₁) + 1)
  have hK_pos : 0 < K := by dsimp only [K]; positivity
  refine ⟨(2 * Real.pi)⁻¹ * K, by positivity, fun t => ?_⟩
  -- Factor `exp((σ - 1/2) t)` outside the `y`-integral.
  have hfactor : vertFlux σ y₁ y₂ N t =
      (2 * Real.pi : ℂ)⁻¹ * ((Real.exp ((σ - 1 / 2) * t) : ℂ) *
        ∫ y in y₁..y₂, cexp ((t : ℂ) * (y : ℂ) * I) * g y) := by
    unfold vertFlux
    congr 1
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun y _ => ?_
    dsimp only [g]
    rw [← mul_assoc, Complex.ofReal_exp, ← Complex.exp_add]
    congr 2
    push_cast; ring
  have hexp_unit : ∀ y : ℝ, ‖cexp ((t : ℂ) * (y : ℂ) * I)‖ = 1 := fun y => by
    have hre : ((t : ℂ) * (y : ℂ) * I).re = 0 := by simp
    rw [Complex.norm_exp, hre, Real.exp_zero]
  have hosc_le : ‖∫ y in y₁..y₂, cexp ((t : ℂ) * (y : ℂ) * I) * g y‖ ≤ K / (|t| + 1) := by
    by_cases ht1 : |t| ≤ 1
    · have hb : ∀ y ∈ Icc y₁ y₂, ‖cexp ((t : ℂ) * (y : ℂ) * I) * g y‖ ≤ M₀ := fun y hy_cc => by
        rw [norm_mul, hexp_unit y, one_mul]; exact hM₀_bd y hy_cc
      have hint := intervalIntegral.norm_integral_le_of_norm_le_const' hy hb
      rw [abs_of_nonneg hdy] at hint
      refine hint.trans ?_
      rw [le_div_iff₀ (by positivity : 0 < |t| + 1)]
      have h1 : M₀ * (y₂ - y₁) * (|t| + 1) ≤ M₀ * (y₂ - y₁) * 2 :=
        mul_le_mul_of_nonneg_left (by linarith only [ht1]) (mul_nonneg hM₀_nn hdy)
      have h2 : 0 ≤ M₁ * (y₂ - y₁) := mul_nonneg hM₁_nn hdy
      dsimp only [K]
      linarith only [h1, h2, hM₀_nn]
    · replace ht1 : 1 < |t| := not_le.mp ht1
      have ht_ne : t ≠ 0 := fun h0 => by simp [h0] at ht1; linarith
      have htI_ne : (t : ℂ) * I ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr ht_ne) I_ne_zero
      set E : ℝ → ℂ := fun y => cexp ((t : ℂ) * (y : ℂ) * I)
      set H : ℝ → ℂ := fun y => (((t : ℂ) * I)⁻¹ * E y) * g y
      have hderiv_H : ∀ y ∈ uIcc y₁ y₂,
          HasDerivAt H (E y * g y + ((t : ℂ) * I)⁻¹ * (E y * g' y)) y := by
        rw [uIcc_of_le hy]
        intro y hy_cc
        have hE_d : HasDerivAt E (((t : ℂ) * I) * E y) y := by
          have hlin : HasDerivAt (fun w : ℂ => (t : ℂ) * w * I) ((t : ℂ) * I) (y : ℂ) :=
            (((hasDerivAt_id (y : ℂ)).const_mul (t : ℂ)).mul_const I).congr_deriv (by ring)
          exact (hlin.cexp.comp_ofReal).congr_deriv (by dsimp only [E]; ring)
        have hg_d : HasDerivAt g (g' y) y := by
          have hw := (analyticAt_thetaLogDeriv (hnz y hy_cc)).differentiableAt.hasDerivAt.comp (y : ℂ)
            (((hasDerivAt_id (y : ℂ)).mul_const I).const_add (σ : ℂ))
          exact (hw.comp_ofReal).congr_deriv (by dsimp only [g']; ring)
        have hprod : HasDerivAt H
            ((((t : ℂ) * I)⁻¹ * (((t : ℂ) * I) * E y)) * g y + (((t : ℂ) * I)⁻¹ * E y) * g' y) y :=
          HasDerivAt.mul (hE_d.const_mul ((t : ℂ) * I)⁻¹) hg_d
        exact hprod.congr_deriv (by rw [inv_mul_cancel_left₀ htI_ne]; ring)
      have hi_eg : IntervalIntegrable (fun y => E y * g y) volume y₁ y₂ :=
        (ContinuousOn.mul (by fun_prop) hg_cont).intervalIntegrable_of_Icc hy
      have hi_eg' : IntervalIntegrable (fun y => ((t : ℂ) * I)⁻¹ * (E y * g' y)) volume y₁ y₂ :=
        (ContinuousOn.const_smul (ContinuousOn.mul (by fun_prop) hg'_cont)
          ((t : ℂ) * I)⁻¹).intervalIntegrable_of_Icc hy
      have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv_H (hi_eg.add hi_eg')
      rw [intervalIntegral.integral_add hi_eg hi_eg'] at hftc
      have hibp : (∫ y in y₁..y₂, E y * g y) =
          H y₂ - H y₁ - ((t : ℂ) * I)⁻¹ * ∫ y in y₁..y₂, E y * g' y := by
        rw [← intervalIntegral.integral_const_mul]
        linear_combination hftc
      have hnorm_inv : ‖((t : ℂ) * I)⁻¹‖ = |t|⁻¹ := by
        rw [norm_inv, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_I, mul_one]
      have hH_bd : ∀ y ∈ Icc y₁ y₂, ‖H y‖ ≤ M₀ / |t| := fun y hy_cc => by
        dsimp only [H]
        rw [norm_mul, norm_mul, hnorm_inv, hexp_unit y, mul_one, inv_mul_eq_div]
        exact div_le_div_of_nonneg_right (hM₀_bd y hy_cc) (by positivity)
      have hint_g' : ‖∫ y in y₁..y₂, E y * g' y‖ ≤ M₁ * (y₂ - y₁) := by
        have hb : ∀ y ∈ Icc y₁ y₂, ‖E y * g' y‖ ≤ M₁ := fun y hy_cc => by
          rw [norm_mul, hexp_unit y, one_mul]; exact hM₁_bd y hy_cc
        have hi := intervalIntegral.norm_integral_le_of_norm_le_const' hy hb
        rwa [abs_of_nonneg hdy] at hi
      have hrem : ‖((t : ℂ) * I)⁻¹ * ∫ y in y₁..y₂, E y * g' y‖ ≤ M₁ * (y₂ - y₁) / |t| := by
        rw [norm_mul, hnorm_inv, inv_mul_eq_div]
        exact div_le_div_of_nonneg_right hint_g' (by positivity)
      rw [show (fun y : ℝ => cexp ((t : ℂ) * (y : ℂ) * I) * g y) = fun y : ℝ => E y * g y from rfl,
        hibp]
      calc ‖H y₂ - H y₁ - ((t : ℂ) * I)⁻¹ * ∫ y in y₁..y₂, E y * g' y‖
          ≤ (‖H y₂‖ + ‖H y₁‖) + ‖((t : ℂ) * I)⁻¹ * ∫ y in y₁..y₂, E y * g' y‖ :=
            (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
        _ ≤ (M₀ / |t| + M₀ / |t|) + M₁ * (y₂ - y₁) / |t| :=
            add_le_add (add_le_add (hH_bd y₂ ⟨hy, le_rfl⟩) (hH_bd y₁ ⟨le_rfl, hy⟩)) hrem
        _ = (2 * M₀ + M₁ * (y₂ - y₁)) / |t| := by ring
        _ ≤ K / (|t| + 1) := by
            rw [div_le_div_iff₀ (by linarith only [ht1]) (by positivity)]
            have hA : 2 * M₀ + M₁ * (y₂ - y₁) ≤ 2 * M₀ + (M₀ + M₁) * (y₂ - y₁) + 1 := by
              have h0 : 0 ≤ M₀ * (y₂ - y₁) := mul_nonneg hM₀_nn hdy
              linarith only [h0]
            have hB : |t| + 1 ≤ 2 * |t| := by linarith only [ht1]
            exact (mul_le_mul hA hB (by positivity)
              (by positivity : 0 ≤ 2 * M₀ + (M₀ + M₁) * (y₂ - y₁) + 1)).trans_eq
              (by dsimp only [K]; ring)
  rw [hfactor, norm_mul, norm_mul, norm_inv, norm_mul, Complex.norm_ofNat, Complex.norm_real,
    Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le,
    Real.norm_of_nonneg (Real.exp_pos _).le]
  calc (2 * Real.pi)⁻¹ * (Real.exp ((σ - 1 / 2) * t) *
          ‖∫ y in y₁..y₂, cexp ((t : ℂ) * (y : ℂ) * I) * g y‖)
      ≤ (2 * Real.pi)⁻¹ * (Real.exp ((σ - 1 / 2) * t) * (K / (|t| + 1))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hosc_le (Real.exp_pos _).le) (by positivity)
    _ = (2 * Real.pi)⁻¹ * K * Real.exp ((σ - 1 / 2) * t) / (|t| + 1) := by ring

/-- Helper: integration by parts along a single right horizontal segment `[1/2, σ₁] × {y}`. -/
private lemma exists_norm_right_horiz_integral_le {σ₁ y : ℝ} (hσ : 1 / 2 ≤ σ₁) (N : ℕ)
    (hnz : ∀ x ∈ Icc (1 / 2) σ₁,
      _root_.RHTower.finiteThetaAmplitude N ((x : ℂ) + (y : ℂ) * I) ≠ 0) :
    ∃ C_seg : ℝ, 0 < C_seg ∧ ∀ t : ℝ, 0 ≤ t →
      ‖∫ x in (1 / 2 : ℝ)..σ₁,
          cexp ((t : ℂ) * (((x : ℂ) + (y : ℂ) * I) - 1 / 2)) *
            thetaLogDeriv N ((x : ℂ) + (y : ℂ) * I)‖ ≤
        C_seg * Real.exp ((σ₁ - 1 / 2) * t) / (t + 1) := by
  set g : ℝ → ℂ := fun x => thetaLogDeriv N ((x : ℂ) + (y : ℂ) * I)
  set g' : ℝ → ℂ := fun x => deriv (thetaLogDeriv N) ((x : ℂ) + (y : ℂ) * I)
  have hlin_cont : Continuous (fun u : ℝ => (u : ℂ) + (y : ℂ) * I) := by fun_prop
  have hg_cont : ContinuousOn g (Icc (1 / 2) σ₁) := fun x hx =>
    (ContinuousAt.comp (g := thetaLogDeriv N) (f := fun u : ℝ => (u : ℂ) + (y : ℂ) * I)
      (analyticAt_thetaLogDeriv (hnz x hx)).continuousAt hlin_cont.continuousAt).continuousWithinAt
  have hg'_cont : ContinuousOn g' (Icc (1 / 2) σ₁) := fun x hx =>
    (ContinuousAt.comp (g := deriv (thetaLogDeriv N)) (f := fun u : ℝ => (u : ℂ) + (y : ℂ) * I)
      (analyticAt_thetaLogDeriv (hnz x hx)).deriv.continuousAt
      hlin_cont.continuousAt).continuousWithinAt
  obtain ⟨M₀, hM₀_bd⟩ := isCompact_Icc.exists_bound_of_continuousOn hg_cont
  obtain ⟨M₁, hM₁_bd⟩ := isCompact_Icc.exists_bound_of_continuousOn hg'_cont
  have hM₀_nn : 0 ≤ M₀ := (norm_nonneg (g (1 / 2))).trans (hM₀_bd (1 / 2) ⟨le_rfl, hσ⟩)
  have hM₁_nn : 0 ≤ M₁ := (norm_nonneg (g' (1 / 2))).trans (hM₁_bd (1 / 2) ⟨le_rfl, hσ⟩)
  have hdσ : 0 ≤ σ₁ - 1 / 2 := sub_nonneg.mpr hσ
  set C_seg : ℝ := 2 * (2 * M₀ + (M₀ + M₁) * (σ₁ - 1 / 2) + 1)
  refine ⟨C_seg, by dsimp only [C_seg]; positivity, fun t ht => ?_⟩
  have hexp_le : ∀ x ∈ Icc (1 / 2) σ₁,
      ‖cexp ((t : ℂ) * (((x : ℂ) + (y : ℂ) * I) - 1 / 2))‖ ≤ Real.exp ((σ₁ - 1 / 2) * t) := by
    intro x hx
    rw [Complex.norm_exp]
    have hre : ((t : ℂ) * (((x : ℂ) + (y : ℂ) * I) - 1 / 2)).re = (x - 1 / 2) * t := by
      simp; ring
    rw [hre]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith [hx.2]) ht)
  by_cases ht1 : t ≤ 1
  · have hb : ∀ x ∈ Icc (1 / 2) σ₁,
        ‖cexp ((t : ℂ) * (((x : ℂ) + (y : ℂ) * I) - 1 / 2)) * g x‖ ≤
          Real.exp ((σ₁ - 1 / 2) * t) * M₀ := fun x hx => by
      rw [norm_mul]
      exact mul_le_mul (hexp_le x hx) (hM₀_bd x hx) (norm_nonneg _) (Real.exp_pos _).le
    have hint := intervalIntegral.norm_integral_le_of_norm_le_const' hσ hb
    rw [abs_of_nonneg hdσ] at hint
    refine hint.trans ?_
    rw [le_div_iff₀ (by linarith)]
    have hexp_pos : 0 < Real.exp ((σ₁ - 1 / 2) * t) := Real.exp_pos _
    have hcoef : M₀ * (σ₁ - 1 / 2) * (t + 1) ≤ C_seg := by
      have h1 : M₀ * (σ₁ - 1 / 2) * (t + 1) ≤ M₀ * (σ₁ - 1 / 2) * 2 :=
        mul_le_mul_of_nonneg_left (by linarith only [ht1]) (mul_nonneg hM₀_nn hdσ)
      have h2 : 0 ≤ M₁ * (σ₁ - 1 / 2) := mul_nonneg hM₁_nn hdσ
      dsimp only [C_seg]; linarith only [h1, h2, hM₀_nn]
    calc Real.exp ((σ₁ - 1 / 2) * t) * M₀ * (σ₁ - 1 / 2) * (t + 1)
        = (M₀ * (σ₁ - 1 / 2) * (t + 1)) * Real.exp ((σ₁ - 1 / 2) * t) := by ring
      _ ≤ C_seg * Real.exp ((σ₁ - 1 / 2) * t) := mul_le_mul_of_nonneg_right hcoef hexp_pos.le
  · replace ht1 : 1 < t := not_le.mp ht1
    have ht_pos : 0 < t := by linarith
    have htC_ne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht_pos.ne'
    set E : ℝ → ℂ := fun x => cexp ((t : ℂ) * (((x : ℂ) + (y : ℂ) * I) - 1 / 2))
    set H : ℝ → ℂ := fun x => ((t : ℂ)⁻¹ * E x) * g x
    have hderiv_H : ∀ x ∈ uIcc (1 / 2 : ℝ) σ₁,
        HasDerivAt H (E x * g x + (t : ℂ)⁻¹ * (E x * g' x)) x := by
      rw [uIcc_of_le hσ]
      intro x hx
      have hE_d : HasDerivAt E ((t : ℂ) * E x) x := by
        have hlin : HasDerivAt (fun w : ℂ => (t : ℂ) * ((w + (y : ℂ) * I) - 1 / 2))
            (t : ℂ) (x : ℂ) := by
          simpa using (((hasDerivAt_id (x : ℂ)).add_const ((y : ℂ) * I)).sub_const
            (1 / 2 : ℂ)).const_mul (t : ℂ)
        exact (hlin.cexp.comp_ofReal).congr_deriv (by dsimp only [E]; ring)
      have hg_d : HasDerivAt g (g' x) x := by
        have hw := (analyticAt_thetaLogDeriv (hnz x hx)).differentiableAt.hasDerivAt.comp (x : ℂ)
          ((hasDerivAt_id (x : ℂ)).add_const ((y : ℂ) * I))
        exact (hw.comp_ofReal).congr_deriv (by dsimp only [g']; ring)
      have hprod : HasDerivAt H
          (((t : ℂ)⁻¹ * ((t : ℂ) * E x)) * g x + ((t : ℂ)⁻¹ * E x) * g' x) x :=
        HasDerivAt.mul (hE_d.const_mul (t : ℂ)⁻¹) hg_d
      exact hprod.congr_deriv (by rw [inv_mul_cancel_left₀ htC_ne]; ring)
    have hi_eg : IntervalIntegrable (fun x => E x * g x) volume (1 / 2) σ₁ :=
      (ContinuousOn.mul (by fun_prop) hg_cont).intervalIntegrable_of_Icc hσ
    have hi_eg' : IntervalIntegrable (fun x => (t : ℂ)⁻¹ * (E x * g' x)) volume (1 / 2) σ₁ :=
      (ContinuousOn.const_smul (ContinuousOn.mul (by fun_prop) hg'_cont)
        (t : ℂ)⁻¹).intervalIntegrable_of_Icc hσ
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv_H (hi_eg.add hi_eg')
    rw [intervalIntegral.integral_add hi_eg hi_eg'] at hftc
    have hibp : (∫ x in (1 / 2 : ℝ)..σ₁, E x * g x) =
        H σ₁ - H (1 / 2) - (t : ℂ)⁻¹ * ∫ x in (1 / 2 : ℝ)..σ₁, E x * g' x := by
      rw [← intervalIntegral.integral_const_mul]
      linear_combination hftc
    have hH_bd : ∀ x ∈ Icc (1 / 2) σ₁,
        ‖H x‖ ≤ M₀ * Real.exp ((σ₁ - 1 / 2) * t) / t := fun x hx => by
      dsimp only [H]
      rw [norm_mul, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg ht_pos.le]
      have h12 : ‖E x‖ * ‖g x‖ ≤ Real.exp ((σ₁ - 1 / 2) * t) * M₀ :=
        mul_le_mul (hexp_le x hx) (hM₀_bd x hx) (norm_nonneg _) (Real.exp_pos _).le
      calc t⁻¹ * ‖E x‖ * ‖g x‖ = (‖E x‖ * ‖g x‖) / t := by ring
        _ ≤ (Real.exp ((σ₁ - 1 / 2) * t) * M₀) / t := div_le_div_of_nonneg_right h12 ht_pos.le
        _ = M₀ * Real.exp ((σ₁ - 1 / 2) * t) / t := by ring
    have hint_g' : ‖∫ x in (1 / 2 : ℝ)..σ₁, E x * g' x‖ ≤
        M₁ * (σ₁ - 1 / 2) * Real.exp ((σ₁ - 1 / 2) * t) := by
      have hb : ∀ x ∈ Icc (1 / 2) σ₁, ‖E x * g' x‖ ≤ Real.exp ((σ₁ - 1 / 2) * t) * M₁ :=
        fun x hx => by
          rw [norm_mul]
          exact mul_le_mul (hexp_le x hx) (hM₁_bd x hx) (norm_nonneg _) (Real.exp_pos _).le
      have hi := intervalIntegral.norm_integral_le_of_norm_le_const' hσ hb
      rw [abs_of_nonneg hdσ] at hi
      exact hi.trans_eq (by ring)
    have hrem : ‖(t : ℂ)⁻¹ * ∫ x in (1 / 2 : ℝ)..σ₁, E x * g' x‖ ≤
        M₁ * (σ₁ - 1 / 2) * Real.exp ((σ₁ - 1 / 2) * t) / t := by
      rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg ht_pos.le, inv_mul_eq_div]
      exact div_le_div_of_nonneg_right hint_g' ht_pos.le
    rw [show (fun x : ℝ => cexp ((t : ℂ) * (((x : ℂ) + (y : ℂ) * I) - 1 / 2)) * g x) =
      fun x : ℝ => E x * g x from rfl, hibp]
    calc ‖H σ₁ - H (1 / 2) - (t : ℂ)⁻¹ * ∫ x in (1 / 2 : ℝ)..σ₁, E x * g' x‖
        ≤ (‖H σ₁‖ + ‖H (1 / 2)‖) + ‖(t : ℂ)⁻¹ * ∫ x in (1 / 2 : ℝ)..σ₁, E x * g' x‖ :=
          (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      _ ≤ (M₀ * Real.exp ((σ₁ - 1 / 2) * t) / t + M₀ * Real.exp ((σ₁ - 1 / 2) * t) / t) +
            M₁ * (σ₁ - 1 / 2) * Real.exp ((σ₁ - 1 / 2) * t) / t :=
          add_le_add (add_le_add (hH_bd σ₁ ⟨hσ, le_rfl⟩) (hH_bd (1 / 2) ⟨le_rfl, hσ⟩)) hrem
      _ = ((2 * M₀ + M₁ * (σ₁ - 1 / 2)) / t) * Real.exp ((σ₁ - 1 / 2) * t) := by ring
      _ ≤ (C_seg / (t + 1)) * Real.exp ((σ₁ - 1 / 2) * t) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
          rw [div_le_div_iff₀ ht_pos (by linarith only [ht1])]
          have hA : 2 * M₀ + M₁ * (σ₁ - 1 / 2) ≤ 2 * M₀ + (M₀ + M₁) * (σ₁ - 1 / 2) + 1 := by
            have h0 : 0 ≤ M₀ * (σ₁ - 1 / 2) := mul_nonneg hM₀_nn hdσ
            linarith only [h0]
          have hB : t + 1 ≤ 2 * t := by linarith only [ht1]
          exact (mul_le_mul hA hB (by positivity)
            (by positivity : 0 ≤ 2 * M₀ + (M₀ + M₁) * (σ₁ - 1 / 2) + 1)).trans_eq
            (by dsimp only [C_seg]; ring)
      _ = C_seg * Real.exp ((σ₁ - 1 / 2) * t) / (t + 1) := by ring

/-- **Short horizontal-cap `O(e^{(σ₁ - 1/2) t} / (t + 1))` decay.**
Whenever `finiteThetaAmplitude N` is nonvanishing on `[1/2, σ₁] × {y₁, y₂}` (`1/2 ≤ σ₁`), one
integration by parts bounds `horizCapFlux (1/2) σ₁ y₁ y₂ N t` by
`C_H * exp((σ₁ - 1/2) * t) / (t + 1)` for all `t ≥ 0`. -/
theorem exists_shortCap_inv_decay {σ₁ y₁ y₂ : ℝ} (hσ : 1 / 2 ≤ σ₁) (N : ℕ)
    (hnz₁ : ∀ x ∈ Icc (1 / 2) σ₁,
      _root_.RHTower.finiteThetaAmplitude N ((x : ℂ) + (y₁ : ℂ) * I) ≠ 0)
    (hnz₂ : ∀ x ∈ Icc (1 / 2) σ₁,
      _root_.RHTower.finiteThetaAmplitude N ((x : ℂ) + (y₂ : ℂ) * I) ≠ 0) :
    ∃ C_H : ℝ, 0 < C_H ∧ ∀ t : ℝ, 0 ≤ t →
      ‖horizCapFlux (1 / 2) σ₁ y₁ y₂ N t‖ ≤ C_H * Real.exp ((σ₁ - 1 / 2) * t) / (t + 1) := by
  obtain ⟨C₁, hC₁_pos, hC₁_bd⟩ := exists_norm_right_horiz_integral_le hσ N hnz₁
  obtain ⟨C₂, hC₂_pos, hC₂_bd⟩ := exists_norm_right_horiz_integral_le hσ N hnz₂
  refine ⟨(2 * Real.pi)⁻¹ * (C₁ + C₂), by positivity, fun t ht => ?_⟩
  unfold horizCapFlux
  have hpre : ‖(2 * Real.pi * I)⁻¹‖ = (2 * Real.pi)⁻¹ := by
    rw [norm_inv, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le, norm_I, mul_one]
  rw [norm_mul, hpre]
  have hsub := (norm_sub_le _ _).trans (add_le_add (hC₁_bd t ht) (hC₂_bd t ht))
  exact (mul_le_mul_of_nonneg_left hsub (by positivity)).trans_eq (by ring)

/-- **Shifted-abscissa decomposition of `rightHalfPort` alone.**
If `A_N` has no zeros on `[σ₁, 3/2] × [y₁, y₂]` (`1/2 ≤ σ₁ ≤ 3/2`, `y₁ ≤ y₂`) and no zeros on
`[1/2, 3/2] × {y₁, y₂}`, then `rightHalfPort` reduces identically to
`vertFlux σ₁ + horizCapFlux (1/2) σ₁`, cancelling the `e^t` right-edge flux internally inside the
right half-window. -/
theorem rightHalfPort_eq_vertFlux_add_shortCap {σ₁ y₁ y₂ : ℝ}
    (hσ_lo : 1 / 2 ≤ σ₁) (hσ_hi : σ₁ ≤ 3 / 2) (hy : y₁ ≤ y₂) (N : ℕ)
    (hnz_rect : ∀ z ∈ Icc σ₁ (3 / 2) ×ℂ Icc y₁ y₂, _root_.RHTower.finiteThetaAmplitude N z ≠ 0)
    (hnz₁ : ∀ x ∈ Icc (1 / 2 : ℝ) (3 / 2 : ℝ),
      _root_.RHTower.finiteThetaAmplitude N ((x : ℂ) + (y₁ : ℂ) * I) ≠ 0)
    (hnz₂ : ∀ x ∈ Icc (1 / 2 : ℝ) (3 / 2 : ℝ),
      _root_.RHTower.finiteThetaAmplitude N ((x : ℂ) + (y₂ : ℂ) * I) ≠ 0)
    (t : ℝ) :
    rightHalfPort y₁ y₂ N t = vertFlux σ₁ y₁ y₂ N t + horizCapFlux (1 / 2) σ₁ y₁ y₂ N t := by
  unfold rightHalfPort
  rw [horizCapFlux_add_adjacent hσ_lo hσ_hi N hnz₁ hnz₂ t]
  have hcauchy := rightEdgeFlux_add_horizCapFlux_eq_vertFlux hσ_hi hy N hnz_rect t
  linear_combination hcauchy

/-- **Intrinsic shifted-abscissa `O(e^{(σ₁ - 1/2) t} / (t + 1))` decay and boundary Laplace
integrability of `rightHalfPort`.**
Whenever `A_N` is zero-free on `[σ₁, 3/2] × [y₁, y₂]` and `[1/2, 3/2] × {y₁, y₂}`, `rightHalfPort`
satisfies `‖rightHalfPort(t)‖ ≤ C * exp((σ₁ - 1/2) * t) / (t + 1)` for all `t ≥ 0`, so
`exp(-2 * (σ₁ - 1/2) * t) * ‖rightHalfPort(t)‖²` is integrable right at the critical boundary
exponent `x = 2 * (σ₁ - 1/2)`. -/
theorem exists_rightHalfPort_shifted_inv_decay {σ₁ y₁ y₂ : ℝ}
    (hσ_lo : 1 / 2 ≤ σ₁) (hσ_hi : σ₁ ≤ 3 / 2) (hy : y₁ ≤ y₂) (N : ℕ)
    (hnz_rect : ∀ z ∈ Icc σ₁ (3 / 2) ×ℂ Icc y₁ y₂, _root_.RHTower.finiteThetaAmplitude N z ≠ 0)
    (hnz₁ : ∀ x ∈ Icc (1 / 2 : ℝ) (3 / 2 : ℝ),
      _root_.RHTower.finiteThetaAmplitude N ((x : ℂ) + (y₁ : ℂ) * I) ≠ 0)
    (hnz₂ : ∀ x ∈ Icc (1 / 2 : ℝ) (3 / 2 : ℝ),
      _root_.RHTower.finiteThetaAmplitude N ((x : ℂ) + (y₂ : ℂ) * I) ≠ 0) :
    (∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t →
      ‖rightHalfPort y₁ y₂ N t‖ ≤ C * Real.exp ((σ₁ - 1 / 2) * t) / (t + 1)) ∧
    IntegrableOn
      (fun t : ℝ => Real.exp (-(2 * (σ₁ - 1 / 2) * t)) * ‖rightHalfPort y₁ y₂ N t‖ ^ 2)
      (Ioi (0 : ℝ)) := by
  have hnz_v : ∀ y ∈ Icc y₁ y₂,
      _root_.RHTower.finiteThetaAmplitude N ((σ₁ : ℂ) + (y : ℂ) * I) ≠ 0 := fun y hy_m =>
    hnz_rect ((σ₁ : ℂ) + (y : ℂ) * I)
      ⟨⟨by simp, by simpa using hσ_hi⟩, ⟨by simpa using hy_m.1, by simpa using hy_m.2⟩⟩
  have hnz_s₁ : ∀ x ∈ Icc (1 / 2) σ₁,
      _root_.RHTower.finiteThetaAmplitude N ((x : ℂ) + (y₁ : ℂ) * I) ≠ 0 :=
    fun x hx => hnz₁ x ⟨hx.1, hx.2.trans hσ_hi⟩
  have hnz_s₂ : ∀ x ∈ Icc (1 / 2) σ₁,
      _root_.RHTower.finiteThetaAmplitude N ((x : ℂ) + (y₂ : ℂ) * I) ≠ 0 :=
    fun x hx => hnz₂ x ⟨hx.1, hx.2.trans hσ_hi⟩
  obtain ⟨C_V, hCV_pos, hCV_bd⟩ := exists_vertFlux_inv_decay hy N hnz_v
  obtain ⟨C_H, hCH_pos, hCH_bd⟩ := exists_shortCap_inv_decay hσ_lo N hnz_s₁ hnz_s₂
  set C : ℝ := C_V + C_H
  have hC_pos : 0 < C := by dsimp only [C]; positivity
  have hpt : ∀ t : ℝ, 0 ≤ t →
      ‖rightHalfPort y₁ y₂ N t‖ ≤ C * Real.exp ((σ₁ - 1 / 2) * t) / (t + 1) := by
    intro t ht
    rw [rightHalfPort_eq_vertFlux_add_shortCap hσ_lo hσ_hi hy N hnz_rect hnz₁ hnz₂ t]
    have hv := hCV_bd t
    rw [abs_of_nonneg ht] at hv
    exact ((norm_add_le _ _).trans (add_le_add hv (hCH_bd t ht))).trans_eq (by dsimp only [C]; ring)
  refine ⟨⟨C, hC_pos, hpt⟩, ?_⟩
  have hcont_port : Continuous (rightHalfPort y₁ y₂ N) := by
    have heq : rightHalfPort y₁ y₂ N =
        fun t => vertFlux σ₁ y₁ y₂ N t + horizCapFlux (1 / 2) σ₁ y₁ y₂ N t :=
      funext (rightHalfPort_eq_vertFlux_add_shortCap hσ_lo hσ_hi hy N hnz_rect hnz₁ hnz₂)
    rw [heq]
    exact (continuous_vertFlux_of_ne_zero hy hnz_v).add
      (continuous_horizCapFlux_of_ne_zero hσ_lo hnz_s₁ hnz_s₂)
  have hdom : IntegrableOn (fun t : ℝ => C ^ 2 * (t + 1) ^ (-2 : ℝ)) (Ioi (0 : ℝ)) :=
    (integrableOn_add_rpow_Ioi_of_lt (a := -2) (c := 0) (m := 1) (by norm_num)
      (by norm_num)).const_mul _
  refine hdom.mono'
    (((Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).mul
      (hcont_port.norm.pow 2)).aestronglyMeasurable) ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
  have ht0 : 0 ≤ t := (mem_Ioi.mp ht).le
  have ht1 : 0 < t + 1 := by linarith
  have hsq : ‖rightHalfPort y₁ y₂ N t‖ ^ 2 ≤
      C ^ 2 * Real.exp (2 * (σ₁ - 1 / 2) * t) / (t + 1) ^ 2 := by
    have h1 := pow_le_pow_left₀ (norm_nonneg _) (hpt t ht0) 2
    refine h1.trans_eq ?_
    rw [div_pow, mul_pow, sq (Real.exp _), ← Real.exp_add,
      show (σ₁ - 1 / 2) * t + (σ₁ - 1 / 2) * t = 2 * (σ₁ - 1 / 2) * t by ring]
  have hrpow : C ^ 2 / (t + 1) ^ 2 = C ^ 2 * (t + 1) ^ (-2 : ℝ) := by
    rw [div_eq_mul_inv, show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num,
      Real.rpow_neg ht1.le, Real.rpow_natCast]
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (sq_nonneg _)), ← hrpow]
  calc Real.exp (-(2 * (σ₁ - 1 / 2) * t)) * ‖rightHalfPort y₁ y₂ N t‖ ^ 2
      ≤ Real.exp (-(2 * (σ₁ - 1 / 2) * t)) *
          (C ^ 2 * Real.exp (2 * (σ₁ - 1 / 2) * t) / (t + 1) ^ 2) :=
        mul_le_mul_of_nonneg_left hsq (Real.exp_pos _).le
    _ = C ^ 2 * (Real.exp (-(2 * (σ₁ - 1 / 2) * t)) * Real.exp (2 * (σ₁ - 1 / 2) * t)) /
          (t + 1) ^ 2 := by ring
    _ = C ^ 2 / (t + 1) ^ 2 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]

/-- **Critical-line `O(1 / (|t| + 1))` and `L²(0, ∞)` upgrade of
`rightHalfPort_eq_criticalLineFlux_of_rightHalfZeroFree`.**
If `A_N` has no zeros on `[1/2, 3/2] × [y₁, y₂]` (`y₁ ≤ y₂`), then `rightHalfPort = vertFlux (1/2)`
decays as `C / (|t| + 1)` across all `t : ℝ` and is square-integrable on `(0, ∞)`. -/
theorem exists_criticalLineFlux_inv_decay_of_rightHalfZeroFree {y₁ y₂ : ℝ} (hy : y₁ ≤ y₂) (N : ℕ)
    (hnz : ∀ z ∈ Icc (1 / 2) (3 / 2) ×ℂ Icc y₁ y₂, _root_.RHTower.finiteThetaAmplitude N z ≠ 0) :
    (∀ t : ℝ, rightHalfPort y₁ y₂ N t = vertFlux (1 / 2) y₁ y₂ N t) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, ‖rightHalfPort y₁ y₂ N t‖ ≤ C / (|t| + 1)) ∧
    IntegrableOn (fun t : ℝ => ‖rightHalfPort y₁ y₂ N t‖ ^ 2) (Ioi (0 : ℝ)) := by
  have heq := (rightHalfPort_eq_criticalLineFlux_of_rightHalfZeroFree hy N hnz).1
  obtain ⟨C_V, hCV_pos, hCV_bd⟩ := exists_vertFlux_inv_decay (σ := 1 / 2) hy N fun y hy_m =>
    hnz (((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)
      ⟨⟨by simp, by simp; norm_num⟩, ⟨by simpa using hy_m.1, by simpa using hy_m.2⟩⟩
  have hsh := (exists_rightHalfPort_shifted_inv_decay (σ₁ := 1 / 2) le_rfl (by norm_num) hy N hnz
    (fun x hx => hnz ((x : ℂ) + (y₁ : ℂ) * I) ⟨⟨by simpa using hx.1, by simpa using hx.2⟩, ⟨by simp, by simpa using hy⟩⟩)
    (fun x hx => hnz ((x : ℂ) + (y₂ : ℂ) * I) ⟨⟨by simpa using hx.1, by simpa using hx.2⟩, ⟨by simpa using hy, by simp⟩⟩)).2
  refine ⟨heq, ⟨C_V, hCV_pos, fun t => ?_⟩, ?_⟩
  · rw [heq t]
    simpa only [sub_self, zero_mul, Real.exp_zero, mul_one] using hCV_bd t
  · simpa only [sub_self, mul_zero, zero_mul, neg_zero, Real.exp_zero, one_mul] using hsh


/-! ## §2. 6-way zero-free window rigidity and 5-way uniform-boundedness equivalences -/

/-- **6-way zero-free window rigidity (`rightHalfPort_criticalLineFlux_zeroFree_tfae`).**
On any boundary-regular centered window `[-1/2, 3/2] × [y₁, y₂]` (`y₁ ≤ y₂`), right-half
zero-freeness `∀ z ∈ [1/2, 3/2] × [y₁, y₂], A_N z ≠ 0`, `O(1 / (|t| + 1))` critical-line flux
control, unweighted `L²(0, ∞)` integrability of `rightHalfPort`, full open-window zero-freeness,
identical vanishing of `centeredThetaExpSum`, and skew-conjugation symmetry of `rightHalfPort`
are unconditionally equivalent. -/
theorem rightHalfPort_criticalLineFlux_zeroFree_tfae {y₁ y₂ : ℝ} (hy : y₁ ≤ y₂) (N : ℕ)
    (hbdry : ∀ τ : ℝ, _root_.RHTower.finiteThetaAmplitude N
      (_root_.RHTower.rectangleBoundaryPath
        (centeredWindowLowerLeft y₁) (centeredWindowUpperRight y₂) τ) ≠ 0) :
    [ -- 1. Exact hypothesis of `rightHalfPort_eq_criticalLineFlux_of_rightHalfZeroFree`:
      ∀ z ∈ Icc (1 / 2) (3 / 2) ×ℂ Icc y₁ y₂, _root_.RHTower.finiteThetaAmplitude N z ≠ 0,
      -- 2. Critical-line flux identity with `O(1 / (|t| + 1))` decay:
      (∀ t : ℝ, rightHalfPort y₁ y₂ N t = vertFlux (1 / 2) y₁ y₂ N t) ∧
        (∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, ‖rightHalfPort y₁ y₂ N t‖ ≤ C / (|t| + 1)),
      -- 3. Unweighted `L²(0, ∞)` integrability of `rightHalfPort`:
      IntegrableOn (fun t : ℝ => ‖rightHalfPort y₁ y₂ N t‖ ^ 2) (Ioi (0 : ℝ)),
      -- 4. Full open-window zero-freeness of `A_N` on `(-1/2, 3/2) × (y₁, y₂)`:
      ∀ z : ℂ, -1 / 2 < z.re → z.re < 3 / 2 → y₁ < z.im → z.im < y₂ →
        _root_.RHTower.finiteThetaAmplitude N z ≠ 0,
      -- 5. Identical vanishing of the window exponential sum `𝒵_N`:
      ∀ t : ℝ, centeredThetaExpSum y₁ y₂ N t = 0,
      -- 6. Skew-conjugation symmetry `𝒫_+(t) = -conj(𝒫_+(-t))`:
      ∀ t : ℝ, rightHalfPort y₁ y₂ N t = -star (rightHalfPort y₁ y₂ N (-t))
    ].TFAE := by
  set W := centeredThetaWindow hy N hbdry
  have hcont_right : Continuous (rightHalfPort y₁ y₂ N) := by
    unfold rightHalfPort rightEdgeFlux
    refine (continuous_vertFlux_of_ne_zero hy ?_).add
      (continuous_horizCapFlux_of_ne_zero (by norm_num) ?_ ?_)
    · intro y hy_m
      exact edge_ne_zero_of_bdry_regular hy hbdry ⟨by simp; norm_num, by simp⟩
        ⟨by simpa using hy_m.1, by simpa using hy_m.2⟩ (Or.inr (Or.inl (by simp)))
    · intro x hx
      exact edge_ne_zero_of_bdry_regular hy hbdry ⟨by simp; linarith [hx.1], by simpa using hx.2⟩
        ⟨by simp, by simpa using hy⟩ (Or.inr (Or.inr (Or.inl (by simp))))
    · intro x hx
      exact edge_ne_zero_of_bdry_regular hy hbdry ⟨by simp; linarith [hx.1], by simpa using hx.2⟩
        ⟨by simpa using hy, by simp⟩ (Or.inr (Or.inr (Or.inr (by simp))))
  tfae_have 1 → 2 := by
    intro hnz
    have h := exists_criticalLineFlux_inv_decay_of_rightHalfZeroFree hy N hnz
    exact ⟨h.1, h.2.1⟩
  tfae_have 2 → 3 := by
    rintro ⟨_, C, hC, hbd⟩
    have hdom : IntegrableOn (fun t : ℝ => C ^ 2 * (t + 1) ^ (-2 : ℝ)) (Ioi (0 : ℝ)) :=
      (integrableOn_add_rpow_Ioi_of_lt (a := -2) (c := 0) (m := 1) (by norm_num)
        (by norm_num)).const_mul _
    refine hdom.mono' (hcont_right.norm.pow 2).aestronglyMeasurable ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
    have ht0 : 0 ≤ t := (mem_Ioi.mp ht).le
    have ht1 : 0 < t + 1 := by linarith
    have habs : ‖rightHalfPort y₁ y₂ N t‖ ≤ C / (t + 1) := by
      simpa only [abs_of_nonneg ht0] using hbd t
    have hsq := pow_le_pow_left₀ (norm_nonneg _) habs 2
    have hrpow : (C / (t + 1)) ^ 2 = C ^ 2 * (t + 1) ^ (-2 : ℝ) := by
      rw [div_pow, div_eq_mul_inv,
        show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg ht1.le, Real.rpow_natCast]
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← hrpow]
    exact hsq
  tfae_have 3 → 4 := by
    intro hint_R z hx1 hx2 hy1 hy2 hz0
    have hint_R0 : IntegrableOn
        (fun t : ℝ => Real.exp (-(0 * t)) * ‖rightHalfPort y₁ y₂ N t‖ ^ 2) (Ioi (0 : ℝ)) := by
      simpa only [zero_mul, neg_zero, Real.exp_zero, one_mul] using hint_R
    have hint_Z0 := (integrableOn_windowEnergy_iff_rightHalfPort hy N hbdry le_rfl).mpr hint_R0
    have hint_W : IntegrableOn
        (fun t : ℝ => Real.exp (-(0 * t)) * ‖W.expSum t‖ ^ 2) (Ioi (0 : ℝ)) := by
      have heq : (fun t : ℝ => Real.exp (-(0 * t)) * ‖W.expSum t‖ ^ 2) =
          fun t => Real.exp (-(0 * t)) * ‖centeredThetaExpSum y₁ y₂ N t‖ ^ 2 :=
        funext fun t => by rw [centeredThetaWindow_expSum]
      rwa [heq]
    have hzW : z ∈ W.Z := (mem_centeredThetaWindow_iff hy N hbdry z).mpr ⟨⟨hx1, hx2, hy1, hy2⟩, hz0⟩
    set z₁ : ℂ := if 1 / 2 ≤ z.re then z else 1 - star z
    have hz₁_W : z₁ ∈ W.Z := by
      dsimp only [z₁]; split_ifs
      · exact hzW
      · exact W.refl_mem z hzW
    have hz₁_nn : 0 ≤ z₁.re - 1 / 2 := by
      dsimp only [z₁]; split_ifs with hge
      · linarith
      · simp; linarith
    obtain ⟨z₀, hz₀_W, hmax⟩ := Finset.exists_max_image W.Z (fun w => w.re - 1 / 2) ⟨z₁, hz₁_W⟩
    set δ : ℝ := z₀.re - 1 / 2
    have hδ_nn : 0 ≤ δ := hz₁_nn.trans (hmax z₁ hz₁_W)
    have h2δ := W.lt_of_integrableOn_energy hmax hz₀_W rfl hint_W
    linarith
  tfae_have 4 → 1 := by
    intro hopen z ⟨⟨hzx1, hzx2⟩, ⟨hzy1, hzy2⟩⟩ hz0
    by_cases hedge : z.re = 3 / 2 ∨ z.im = y₁ ∨ z.im = y₂
    · exact edge_ne_zero_of_bdry_regular hy hbdry ⟨by linarith, hzx2⟩ ⟨hzy1, hzy2⟩
        (Or.inr hedge) hz0
    · push Not at hedge
      exact hopen z (by linarith) (lt_of_le_of_ne hzx2 hedge.1)
        (lt_of_le_of_ne hzy1 hedge.2.1.symm) (lt_of_le_of_ne hzy2 hedge.2.2) hz0
  tfae_have 4 → 5 := by
    intro hopen t
    have hempty : (centeredThetaWindow hy N hbdry).Z = ∅ := by
      ext z; simp only [Finset.notMem_empty, iff_false]
      intro hz
      obtain ⟨⟨hx1, hx2, hy1, hy2⟩, hz0⟩ := (mem_centeredThetaWindow_iff hy N hbdry z).mp hz
      exact hopen z hx1 hx2 hy1 hy2 hz0
    rw [← centeredThetaWindow_expSum hy N hbdry t]
    unfold ReflectedWindow.expSum
    rw [hempty, Finset.sum_empty]
  tfae_have 5 → 6 := by
    intro hzero t
    have hsum := centeredThetaExpSum_eq_rightHalfPort_add_conj_neg hy N hbdry t
    rw [hzero t] at hsum
    linear_combination -hsum
  tfae_have 6 → 3 := by
    intro hskew
    have hleft := integrableOn_leftHalfPort_sq hy N hbdry
    have heq : (fun t : ℝ => ‖rightHalfPort y₁ y₂ N t‖ ^ 2) =
        fun t => ‖leftHalfPort y₁ y₂ N t‖ ^ 2 := by
      funext t
      rw [hskew t, ← leftHalfPort_eq_conj_rightHalfPort_neg y₁ y₂ N t, norm_neg]
    rwa [heq]
  tfae_finish

/-- **5-way critical-line uniform boundedness and mode-decomposition equivalence
(`rightHalfPort_uniformBounded_tfae`).**
On any boundary-regular centered window `[-1/2, 3/2] × [y₁, y₂]` (`y₁ ≤ y₂`), uniform boundedness
of `rightHalfPort` on `[0, ∞)`, uniform boundedness of `centeredThetaExpSum` on `[0, ∞)`,
subexponential growth of `‖rightHalfPort‖²`, local critical-line purity (`Re z = 1/2`), and an
explicit `O(1 / (t + 1))`-accurate critical-line oscillatory mode decomposition of `rightHalfPort`
are unconditionally equivalent. -/
theorem rightHalfPort_uniformBounded_tfae {y₁ y₂ : ℝ} (hy : y₁ ≤ y₂) (N : ℕ)
    (hbdry : ∀ τ : ℝ, _root_.RHTower.finiteThetaAmplitude N
      (_root_.RHTower.rectangleBoundaryPath
        (centeredWindowLowerLeft y₁) (centeredWindowUpperRight y₂) τ) ≠ 0) :
    [ -- 1. Uniform boundedness of `rightHalfPort` on `[0, ∞)`:
      ∃ M : ℝ, 0 < M ∧ ∀ t : ℝ, 0 ≤ t → ‖rightHalfPort y₁ y₂ N t‖ ≤ M,
      -- 2. Uniform boundedness of `centeredThetaExpSum` on `[0, ∞)`:
      ∃ M : ℝ, 0 < M ∧ ∀ t : ℝ, 0 ≤ t → ‖centeredThetaExpSum y₁ y₂ N t‖ ≤ M,
      -- 3. Subexponential growth of `‖rightHalfPort‖²` on `[0, ∞)`:
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t →
        ‖rightHalfPort y₁ y₂ N t‖ ^ 2 ≤ C * Real.exp (ε * t),
      -- 4. Local critical-line purity of `A_N` inside `(-1/2, 3/2) × (y₁, y₂)`:
      ∀ z : ℂ, -1 / 2 < z.re → z.re < 3 / 2 → y₁ < z.im → z.im < y₂ →
        _root_.RHTower.finiteThetaAmplitude N z = 0 → z.re = 1 / 2,
      -- 5. Critical-line mode decomposition of `rightHalfPort` up to `O(1 / (t + 1))`:
      (∀ z ∈ (centeredThetaWindow hy N hbdry).Z, z.re = 1 / 2) ∧
        ∃ C_L : ℝ, 0 < C_L ∧ ∀ t : ℝ, 0 ≤ t →
          ‖rightHalfPort y₁ y₂ N t -
              ∑ z ∈ (centeredThetaWindow hy N hbdry).Z,
                ((centeredThetaWindow hy N hbdry).mult z : ℂ) * cexp ((t : ℂ) * (z.im : ℂ) * I)‖ ≤
            C_L / (t + 1)
    ].TFAE := by
  set W := centeredThetaWindow hy N hbdry
  tfae_have 1 → 3 := by
    rintro ⟨M, hM, hbd⟩ ε hε
    refine ⟨M ^ 2, by positivity, fun t ht => ?_⟩
    have hsq : ‖rightHalfPort y₁ y₂ N t‖ ^ 2 ≤ M ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hbd t ht) 2
    have hexp1 : 1 ≤ Real.exp (ε * t) := Real.one_le_exp (mul_nonneg hε.le ht)
    exact hsq.trans ((mul_one (M ^ 2)).symm.trans_le
      (mul_le_mul_of_nonneg_left hexp1 (sq_nonneg M)))
  tfae_have 2 → 3 := by
    rintro ⟨M, hM, hbd⟩ ε hε
    obtain ⟨C_L, hC_L, hleft⟩ := exists_leftEdge_and_leftHalfPort_decay hy N hbdry
    refine ⟨(M + C_L) ^ 2, by positivity, fun t ht => ?_⟩
    have hport_eq : rightHalfPort y₁ y₂ N t =
        centeredThetaExpSum y₁ y₂ N t - leftHalfPort y₁ y₂ N t := by
      have h := centeredThetaExpSum_eq_rightHalfPort_add_leftHalfPort hy N hbdry t
      linear_combination -h
    have hleft_le : ‖leftHalfPort y₁ y₂ N t‖ ≤ C_L :=
      (hleft t ht).2.trans (div_le_self hC_L.le (by linarith))
    have hnorm_le : ‖rightHalfPort y₁ y₂ N t‖ ≤ M + C_L := by
      rw [hport_eq]
      exact (norm_sub_le _ _).trans (add_le_add (hbd t ht) hleft_le)
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hnorm_le 2
    have hexp1 : 1 ≤ Real.exp (ε * t) := Real.one_le_exp (mul_nonneg hε.le ht)
    exact hsq.trans ((mul_one ((M + C_L) ^ 2)).symm.trans_le
      (mul_le_mul_of_nonneg_left hexp1 (sq_nonneg _)))
  tfae_have 3 → 4 := by
    exact ((subexp_windowEnergy_tfae hy N hbdry).out 2 3).mp
  tfae_have 4 → 2 := by
    intro hpure
    refine ⟨(W.degree : ℝ) + 1, by positivity, fun t ht => ?_⟩
    have hδ0 : ∀ z ∈ W.Z, z.re - 1 / 2 ≤ 0 := fun z hz => by
      obtain ⟨⟨hx1, hx2, hy1, hy2⟩, hz0⟩ := (mem_centeredThetaWindow_iff hy N hbdry z).mp hz
      linarith [hpure z hx1 hx2 hy1 hy2 hz0]
    rw [← centeredThetaWindow_expSum hy N hbdry t]
    have hbd := W.norm_expSum_le hδ0 ht
    rw [zero_mul, Real.exp_zero, mul_one] at hbd
    linarith
  tfae_have 4 → 5 := by
    intro hpure
    have hW_re : ∀ z ∈ W.Z, z.re = 1 / 2 := fun z hz => by
      obtain ⟨⟨hx1, hx2, hy1, hy2⟩, hz0⟩ := (mem_centeredThetaWindow_iff hy N hbdry z).mp hz
      exact hpure z hx1 hx2 hy1 hy2 hz0
    obtain ⟨C_L, hC_L, hleft⟩ := exists_leftEdge_and_leftHalfPort_decay hy N hbdry
    refine ⟨hW_re, C_L, hC_L, fun t ht => ?_⟩
    have hexp_modes : centeredThetaExpSum y₁ y₂ N t =
        ∑ z ∈ W.Z, (W.mult z : ℂ) * cexp ((t : ℂ) * (z.im : ℂ) * I) := by
      rw [← centeredThetaWindow_expSum hy N hbdry t]
      unfold ReflectedWindow.expSum
      refine Finset.sum_congr rfl fun z hz => ?_
      have hre := hW_re z hz
      have hsub : z - 1 / 2 = (z.im : ℂ) * I := by
        apply Complex.ext <;> simp [hre]
      rw [hsub, ← mul_assoc]
    have hdiff : rightHalfPort y₁ y₂ N t -
        ∑ z ∈ W.Z, (W.mult z : ℂ) * cexp ((t : ℂ) * (z.im : ℂ) * I) =
        -leftHalfPort y₁ y₂ N t := by
      rw [← hexp_modes, centeredThetaExpSum_eq_rightHalfPort_add_leftHalfPort hy N hbdry t]
      ring
    rw [hdiff, norm_neg]
    exact (hleft t ht).2
  tfae_have 5 → 1 := by
    rintro ⟨_, C_L, hC_L, happrox⟩
    refine ⟨(W.degree : ℝ) + C_L + 1, by positivity, fun t ht => ?_⟩
    set S_osc : ℂ := ∑ z ∈ W.Z, (W.mult z : ℂ) * cexp ((t : ℂ) * (z.im : ℂ) * I)
    have hS_norm : ‖S_osc‖ ≤ (W.degree : ℝ) := by
      dsimp only [S_osc]
      unfold ReflectedWindow.degree
      rw [Nat.cast_sum]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun z _ => ?_)
      have hexp1 : ‖cexp ((t : ℂ) * (z.im : ℂ) * I)‖ = 1 := by
        have hre : ((t : ℂ) * (z.im : ℂ) * I).re = 0 := by simp
        rw [Complex.norm_exp, hre, Real.exp_zero]
      rw [norm_mul, Complex.norm_natCast, hexp1, mul_one]
    have hrem_le : ‖rightHalfPort y₁ y₂ N t - S_osc‖ ≤ C_L :=
      (happrox t ht).trans (div_le_self hC_L.le (by linarith))
    have htri : ‖rightHalfPort y₁ y₂ N t‖ ≤ ‖rightHalfPort y₁ y₂ N t - S_osc‖ + ‖S_osc‖ := by
      simpa only [sub_add_cancel] using norm_add_le (rightHalfPort y₁ y₂ N t - S_osc) S_osc
    linarith [htri, hrem_le, hS_norm]
  tfae_finish


/-! ## §3. Unconditional right-half-port control laws for `ζ` -/

/-- **Unconditional sub-`e^{t/2} / (t + 1)` decay and boundary Laplace integrability of
`rightHalfPort` alone on every Burnol unit window.**
For every `m : ℕ` and every `N ≥ capCancelSqrtPrefix m`, `rightHalfPort` alone on the `m`-th Burnol
unit window satisfies `‖rightHalfPort(t)‖ ≤ C * exp((burnolCapAbscissa m - 1/2) * t) / (t + 1)`
(`burnolCapAbscissa m - 1/2 < 1/2`) and is Laplace square-integrable right at the boundary exponent
`2 * (burnolCapAbscissa m - 1/2)`. -/
theorem exists_burnol_rightHalfPort_subHalfExp_inv_decay (m : ℕ) {N : ℕ}
    (hN : capCancelSqrtPrefix m ≤ N) :
    3 / 4 < burnolCapAbscissa m ∧ burnolCapAbscissa m < 1 ∧
    burnolCapAbscissa m - 1 / 2 < 1 / 2 ∧
    (∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t →
      ‖rightHalfPort (burnolUnitLower m) (burnolUnitUpper m) N t‖ ≤
        C * Real.exp ((burnolCapAbscissa m - 1 / 2) * t) / (t + 1)) ∧
    IntegrableOn
      (fun t : ℝ => Real.exp (-(2 * (burnolCapAbscissa m - 1 / 2) * t)) *
        ‖rightHalfPort (burnolUnitLower m) (burnolUnitUpper m) N t‖ ^ 2)
      (Ioi (0 : ℝ)) := by
  obtain ⟨hσ_lo, hσ_hi, hσ_sub, hrect_nz, _⟩ := exists_burnol_subHalfExp_cap_cancellation m hN
  have hy_le := burnolUnitLower_le_upper m
  have hbdry := burnolUnit_bdry_regular m ((burnolPrefix_le_capCancelSqrtPrefix m).trans hN)
  have hnz₁ : ∀ x ∈ Icc (1 / 2 : ℝ) (3 / 2 : ℝ),
      _root_.RHTower.finiteThetaAmplitude N
        ((x : ℂ) + (burnolUnitLower m : ℂ) * I) ≠ 0 := fun x hx =>
    edge_ne_zero_of_bdry_regular hy_le hbdry ⟨by simp; linarith [hx.1], by simpa using hx.2⟩
      ⟨by simp, by simpa using hy_le⟩ (Or.inr (Or.inr (Or.inl (by simp))))
  have hnz₂ : ∀ x ∈ Icc (1 / 2 : ℝ) (3 / 2 : ℝ),
      _root_.RHTower.finiteThetaAmplitude N
        ((x : ℂ) + (burnolUnitUpper m : ℂ) * I) ≠ 0 := fun x hx =>
    edge_ne_zero_of_bdry_regular hy_le hbdry ⟨by simp; linarith [hx.1], by simpa using hx.2⟩
      ⟨by simpa using hy_le, by simp⟩ (Or.inr (Or.inr (Or.inr (by simp))))
  obtain ⟨hpt, hint⟩ := exists_rightHalfPort_shifted_inv_decay
    (by linarith : 1 / 2 ≤ burnolCapAbscissa m) (by linarith : burnolCapAbscissa m ≤ 3 / 2)
    hy_le N hrect_nz hnz₁ hnz₂
  exact ⟨hσ_lo, hσ_hi, hσ_sub, hpt, hint⟩

/-- Elementary bound `log x ≤ 2 √x` for `x > 0`. -/
private lemma log_le_two_sqrt_local {x : ℝ} (hx : 0 < x) : Real.log x ≤ 2 * Real.sqrt x := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have h := Real.log_le_sub_one_of_pos hs
  have hlog : Real.log x = 2 * Real.log (Real.sqrt x) := by
    conv_lhs => rw [← Real.mul_self_sqrt hx.le]
    rw [Real.log_mul hs.ne' hs.ne']; ring
  linarith

/-- **Unconditional double-logarithmic right-port decay on `1 - O(1 / log(log V))` Burnol unit windows.**
There exists `C₀ > 0` such that eventually in `V`, for all except at most `C₀ * V / log(log V)`
Burnol unit windows `m ∈ [⌈V⌉, ⌊2V⌋]`, for every `N ≥ doorSqrtPrefix m`, `rightHalfPort` alone
satisfies `‖rightHalfPort(t)‖ ≤ C_{m,N} * exp((3 * log(log V) / log V) * t) / (t + 1)` across all
`t ≥ 0`. -/
theorem almostAll_unitWindow_rightHalfPort_doubleLog_decay :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ᶠ V : ℝ in atTop,
      (((Finset.Icc (Nat.ceil V) (Nat.floor (2 * V))).filter (fun m =>
        ¬ ∀ N ≥ doorSqrtPrefix m, ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t →
          ‖rightHalfPort (burnolUnitLower m) (burnolUnitUpper m) N t‖ ≤
            C * Real.exp ((3 * Real.log (Real.log V) / Real.log V) * t) / (t + 1))).card : ℝ) ≤
        C₀ * V / Real.log (Real.log V) := by
  obtain ⟨C_d, κ_r, hCd_pos, hκ_pos, hd_ev⟩ :=
    deepExtendedShell_orderSum_le (r := 3 / 4) (by norm_num) (by norm_num)
  obtain ⟨m₁, htail⟩ := exists_logStage_tail_lt 1 zero_lt_one
  refine ⟨3 * C_d, by positivity, ?_⟩
  have ht_ll : Tendsto (fun V : ℝ => Real.log (Real.log V)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  filter_upwards [hd_ev,
    eventually_ge_atTop (max 32 ((m₁ : ℝ) + 1)),
    ht_ll.eventually_ge_atTop 2,
    Real.tendsto_log_atTop.eventually_ge_atTop (max 64 ((16 / κ_r) ^ 2 + 1))]
    with V hV_d hV_ge hll2 hlog_ge
  have hV32 : 32 ≤ V := (le_max_left _ _).trans hV_ge
  have hVm₁ : (m₁ : ℝ) + 1 ≤ V := (le_max_right _ _).trans hV_ge
  have hV_pos : 0 < V := by linarith only [hV32]
  have hlog64 : 64 ≤ Real.log V := (le_max_left _ _).trans hlog_ge
  have hlog_κ : (16 / κ_r) ^ 2 + 1 ≤ Real.log V := (le_max_right _ _).trans hlog_ge
  have hlogV_pos : 0 < Real.log V := by linarith only [hlog64]
  have hll_pos : 0 < Real.log (Real.log V) := by linarith only [hll2]
  have hll_rt : Real.log (Real.log V) ≤ 2 * Real.sqrt (Real.log V) := log_le_two_sqrt_local hlogV_pos
  have hrt_pos : 0 < Real.sqrt (Real.log V) := Real.sqrt_pos.mpr hlogV_pos
  set A_V : ℝ := 2 * Real.log (Real.log V)
  have hAV_2 : 2 ≤ A_V := by dsimp only [A_V]; linarith only [hll2]
  have hAV_hi : A_V ≤ κ_r * Real.log V := by
    have hrt_gt : 16 / κ_r < Real.sqrt (Real.log V) := by
      rw [← Real.sqrt_sq (by positivity : 0 ≤ 16 / κ_r)]
      exact Real.sqrt_lt_sqrt (by positivity) (lt_of_lt_of_le (lt_add_one _) hlog_κ)
    have hmul : (16 / κ_r) * Real.sqrt (Real.log V) < Real.log V := by
      have h1 := mul_lt_mul_of_pos_right hrt_gt hrt_pos
      rwa [Real.mul_self_sqrt hlogV_pos.le] at h1
    have hmul_κ : 16 * Real.sqrt (Real.log V) < κ_r * Real.log V := by
      have h1 := mul_lt_mul_of_pos_left hmul hκ_pos
      rwa [← mul_assoc, mul_div_cancel₀ 16 hκ_pos.ne'] at h1
    dsimp only [A_V]; linarith only [hll_rt, hmul_κ, hrt_pos]
  -- Check `3 * log(log V) / log V ≤ 1` so `σ_V = 1/2 + 3 * log(log V) / log V ∈ (1/2, 3/2]`.
  set σ_V : ℝ := 1 / 2 + 3 * Real.log (Real.log V) / Real.log V
  have hσV_lo : 1 / 2 ≤ σ_V := le_add_of_nonneg_right (by positivity)
  have hσV_hi : σ_V ≤ 3 / 2 := by
    dsimp only [σ_V]
    have hrt8 : 8 ≤ Real.sqrt (Real.log V) := by
      rw [show (8 : ℝ) = Real.sqrt 64 by norm_num]; exact Real.sqrt_le_sqrt hlog64
    have hmul8 : 8 * Real.sqrt (Real.log V) ≤ Real.log V := by
      calc 8 * Real.sqrt (Real.log V) ≤ Real.sqrt (Real.log V) * Real.sqrt (Real.log V) :=
            mul_le_mul_of_nonneg_right hrt8 hrt_pos.le
        _ = Real.log V := Real.mul_self_sqrt hlogV_pos.le
    have hdiv1 : 3 * Real.log (Real.log V) / Real.log V ≤ 1 := by
      rw [div_le_one hlogV_pos]; linarith only [hll_rt, hmul8, hrt_pos]
    exact (add_le_add_right hdiv1 (1 / 2)).trans (by norm_num : (1 / 2 : ℝ) + 1 ≤ 3 / 2)
  -- Bound deep extended shell at `A_V = 2 * log(log V)`.
  set B_ext := (shellZeros (V - 4) (2 * V + 4)).filter (fun z => A_V / Real.log V ≤ |z.re - 1 / 2|)
  have hB_card : (B_ext.card : ℝ) ≤ (C_d / 2) * V / Real.log (Real.log V) := by
    have h1 : (B_ext.card : ℝ) ≤ ∑ z ∈ B_ext, ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) := by
      rw [Finset.card_eq_sum_ones, Nat.cast_sum]
      refine Finset.sum_le_sum fun z hz => ?_
      have hxi : _root_.RHTower.xi z = 0 :=
        (_root_.RHTower.mem_stripFinsetPos.mp
          (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).1).2.2.2.2
      exact_mod_cast Nat.pos_of_ne_zero (_root_.RHTower.xi_order_toNat_ne_zero hxi)
    have h2 := h1.trans (hV_d A_V hAV_2 hAV_hi)
    have hexp_le : Real.exp (-(3 / 4 * A_V)) ≤ (Real.log V)⁻¹ := by
      calc Real.exp (-(3 / 4 * A_V))
          ≤ Real.exp (-Real.log (Real.log V)) := Real.exp_le_exp.mpr (by dsimp only [A_V]; linarith only [hll_pos])
        _ = (Real.log V)⁻¹ := by rw [Real.exp_neg, Real.exp_log hlogV_pos]
    calc (B_ext.card : ℝ)
        ≤ C_d * (Real.exp (-(3 / 4 * A_V)) / A_V) * V * Real.log V := h2
      _ ≤ C_d * ((Real.log V)⁻¹ / A_V) * V * Real.log V :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left
                (div_le_div_of_nonneg_right hexp_le (by linarith only [hAV_2])) hCd_pos.le)
              hV_pos.le) hlogV_pos.le
      _ = (C_d / 2) * V / Real.log (Real.log V) := by
          dsimp only [A_V]; field_simp [hlogV_pos.ne', hll_pos.ne']
  set I_V := Finset.Icc (Nat.ceil V) (Nat.floor (2 * V))
  set Bad_port := I_V.filter (fun m =>
    ¬ ∀ N ≥ doorSqrtPrefix m, ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t →
      ‖rightHalfPort (burnolUnitLower m) (burnolUnitUpper m) N t‖ ≤
        C * Real.exp ((3 * Real.log (Real.log V) / Real.log V) * t) / (t + 1))
  -- Every window `m ∈ I_V` without deep `ξ`-zeros satisfies the double-log right-port bound.
  have hgood_of_free : ∀ m ∈ I_V,
      (¬ ∃ ρ ∈ burnolUnitXiZeros m, A_V / Real.log V ≤ |ρ.re - 1 / 2|) →
      m ∉ Bad_port := by
    intro m hm_I hfree hm_bad
    apply (Finset.mem_filter.mp hm_bad).2
    intro N hN
    obtain ⟨hm_lo, hm_hi⟩ := Finset.mem_Icc.mp hm_I
    have hm_ge_V : V ≤ (m : ℝ) := (Nat.le_ceil V).trans (by exact_mod_cast hm_lo)
    have hm_m₁ : m₁ ≤ m := (Nat.cast_lt.mp (by linarith only [hVm₁, hm_ge_V] : (m₁ : ℝ) < (m : ℝ))).le
    have hy_le := burnolUnitLower_le_upper m
    have hbdry := burnolUnit_bdry_regular m ((burnolPrefix_le_doorSqrtPrefix m).trans hN)
    set n_m : ℕ := logDoorStage 1 m
    have hn_pos : (0 : ℝ) < (n_m : ℝ) := by linarith only [six_le_logDoorStage_real 1 m]
    have hn_ge_logV : Real.log V ≤ (n_m : ℝ) := by
      have hX : V < ((m + 5 : ℕ) : ℝ) := by push_cast; linarith only [hm_ge_V]
      calc Real.log V ≤ 1 * Real.log ((m + 5 : ℕ) : ℝ) := by
            rw [one_mul]; exact Real.log_le_log hV_pos hX.le
        _ ≤ (Nat.ceil (1 * Real.log ((m + 5 : ℕ) : ℝ)) : ℝ) := Nat.le_ceil _
        _ ≤ (n_m : ℝ) := by exact_mod_cast (le_max_right 6 _)
    have hrad_le : 1 / (16 * (n_m : ℝ)) ≤ Real.log (Real.log V) / (2 * Real.log V) := by
      have h1 : 1 / (16 * (n_m : ℝ)) ≤ 1 / (16 * Real.log V) :=
        one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left hn_ge_logV (by norm_num))
      have h2 : 1 / (16 * Real.log V) ≤ Real.log (Real.log V) / (2 * Real.log V) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith only [hll2, hlogV_pos]
      exact h1.trans h2
    have hrect_nz : ∀ z ∈ Icc σ_V (3 / 2) ×ℂ Icc (burnolUnitLower m) (burnolUnitUpper m),
        _root_.RHTower.finiteThetaAmplitude N z ≠ 0 := by
      intro z ⟨⟨hzx1, hzx2⟩, ⟨hzy1, hzy2⟩⟩ hz0
      by_cases hedge : z.re = 3 / 2 ∨ z.im = burnolUnitLower m ∨ z.im = burnolUnitUpper m
      · exact edge_ne_zero_of_bdry_regular hy_le hbdry ⟨by linarith only [hzx1, hσV_lo], hzx2⟩ ⟨hzy1, hzy2⟩
          (Or.inr hedge) hz0
      · push Not at hedge
        obtain ⟨w, hw_unit, hzw_dist⟩ := exists_xiZero_near_thetaZero m N
          (r := 1 / (16 * (n_m : ℝ))) (by positivity) (htail m hm_m₁ N hN)
          ⟨by linarith only [hzx1, hσV_lo], lt_of_le_of_ne hzx2 hedge.1,
            lt_of_le_of_ne hzy1 hedge.2.1.symm, lt_of_le_of_ne hzy2 hedge.2.2⟩ hz0
        have hw_lt : |w.re - 1 / 2| < A_V / Real.log V := by
          by_contra hge; exact hfree ⟨w, hw_unit, not_lt.mp hge⟩
        have hre_diff : z.re - w.re ≤ 1 / (16 * (n_m : ℝ)) :=
          (le_abs_self _).trans ((Complex.abs_re_le_norm (z - w)).trans
            (by simpa only [Complex.sub_re] using hzw_dist))
        have hw_re_lt : w.re < 1 / 2 + A_V / Real.log V :=
          sub_lt_iff_lt_add'.mp ((le_abs_self (w.re - 1 / 2)).trans_lt hw_lt)
        have hz_lt_σ : z.re < σ_V := by
          have hzw_le : z.re ≤ w.re + 1 / (16 * (n_m : ℝ)) := sub_le_iff_le_add'.mp hre_diff
          calc z.re ≤ w.re + 1 / (16 * (n_m : ℝ)) := hzw_le
            _ < (1 / 2 + A_V / Real.log V) + Real.log (Real.log V) / (2 * Real.log V) :=
                add_lt_add_of_lt_of_le hw_re_lt hrad_le
            _ = 1 / 2 + (5 / 2) * Real.log (Real.log V) / Real.log V := by
                dsimp only [A_V]; field_simp [hlogV_pos.ne']; ring
            _ < σ_V := by
                dsimp only [σ_V]
                exact add_lt_add_right
                  (div_lt_div_of_pos_right (by linarith only [hll_pos]) hlogV_pos) (1 / 2)
        exact absurd hz_lt_σ (not_lt.mpr hzx1)
    have hnz₁ : ∀ x ∈ Icc (1 / 2 : ℝ) (3 / 2 : ℝ),
        _root_.RHTower.finiteThetaAmplitude N
          ((x : ℂ) + (burnolUnitLower m : ℂ) * I) ≠ 0 := fun x hx =>
      edge_ne_zero_of_bdry_regular hy_le hbdry ⟨by simp; linarith only [hx.1], by simpa using hx.2⟩
        ⟨by simp, by simpa using hy_le⟩ (Or.inr (Or.inr (Or.inl (by simp))))
    have hnz₂ : ∀ x ∈ Icc (1 / 2 : ℝ) (3 / 2 : ℝ),
        _root_.RHTower.finiteThetaAmplitude N
          ((x : ℂ) + (burnolUnitUpper m : ℂ) * I) ≠ 0 := fun x hx =>
      edge_ne_zero_of_bdry_regular hy_le hbdry ⟨by simp; linarith only [hx.1], by simpa using hx.2⟩
        ⟨by simpa using hy_le, by simp⟩ (Or.inr (Or.inr (Or.inr (by simp))))
    obtain ⟨⟨C, hC_pos, hpt⟩, _⟩ := exists_rightHalfPort_shifted_inv_decay
      hσV_lo hσV_hi hy_le N hrect_nz hnz₁ hnz₂
    refine ⟨C, hC_pos, fun t ht => ?_⟩
    have hsub_eq : σ_V - 1 / 2 = 3 * Real.log (Real.log V) / Real.log V := by
      dsimp only [σ_V]; ring
    simpa only [hsub_eq] using hpt t ht
  -- Cover `Bad_port` by `B_ext.biUnion (fun z => Finset.Icc (⌊z.im⌋₊ - 2) (⌊z.im⌋₊ + 3))`.
  have hsub_bad : Bad_port ⊆
      B_ext.biUnion (fun z => Finset.Icc (Nat.floor z.im - 2) (Nat.floor z.im + 3)) := by
    intro m hm
    have hm_I := (Finset.mem_filter.mp hm).1
    obtain ⟨hm_lo, hm_hi⟩ := Finset.mem_Icc.mp hm_I
    have hex : ∃ ρ ∈ burnolUnitXiZeros m, A_V / Real.log V ≤ |ρ.re - 1 / 2| := by
      by_contra hfree; exact hgood_of_free m hm_I hfree hm
    obtain ⟨ρ, hρ_Z, hρ_deep⟩ := hex
    obtain ⟨⟨hr0, hr1, hy1, hy2⟩, hxi⟩ := (mem_burnolUnitXiZeros_iff m ρ).mp hρ_Z
    have hy1_lo := sub_three_le_burnolUnitLower m
    have hy2_hi := (burnolUnit_coords m).2.2.2.1
    have hm_ge_V : V ≤ (m : ℝ) := (Nat.le_ceil V).trans (by exact_mod_cast hm_lo)
    have hm_le_2V : (m : ℝ) ≤ 2 * V :=
      ((Nat.cast_le (α := ℝ)).mpr hm_hi).trans (Nat.floor_le (by positivity))
    have him_pos : 0 < ρ.im := by linarith only [hV32, hm_ge_V, hy1_lo, hy1]
    have hρ_B : ρ ∈ B_ext := Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr
        ⟨_root_.RHTower.mem_stripFinsetPos.mpr
          ⟨hr0, hr1, him_pos, by linarith only [hm_le_2V, hy2_hi, hy2], hxi⟩,
          by linarith only [hm_ge_V, hy1_lo, hy1, hm_le_2V, hy2_hi, hy2]⟩,
        hρ_deep⟩
    refine Finset.mem_biUnion.mpr ⟨ρ, hρ_B, ?_⟩
    have hfl_le : (Nat.floor ρ.im : ℝ) ≤ ρ.im := Nat.floor_le him_pos.le
    have hlt_fl1 : ρ.im < (Nat.floor ρ.im : ℝ) + 1 := Nat.lt_floor_add_one ρ.im
    have hc1 : Nat.floor ρ.im ≤ m + 2 := by
      by_contra hlt
      have hcast : (m : ℝ) + 3 ≤ (Nat.floor ρ.im : ℝ) := by
        exact_mod_cast (show m + 3 ≤ Nat.floor ρ.im by omega)
      linarith only [hy2, hy2_hi, hfl_le, hcast]
    have hc2 : m ≤ Nat.floor ρ.im + 3 := by
      by_contra hlt
      have hcast : (Nat.floor ρ.im : ℝ) + 4 ≤ (m : ℝ) := by
        exact_mod_cast (show Nat.floor ρ.im + 4 ≤ m by omega)
      linarith only [hy1, hy1_lo, hlt_fl1, hcast]
    rw [Finset.mem_Icc]; omega
  have hcard_nat : Bad_port.card ≤ 6 * B_ext.card := by
    calc Bad_port.card
        ≤ (B_ext.biUnion (fun z => Finset.Icc (Nat.floor z.im - 2) (Nat.floor z.im + 3))).card :=
          Finset.card_le_card hsub_bad
      _ ≤ ∑ z ∈ B_ext, (Finset.Icc (Nat.floor z.im - 2) (Nat.floor z.im + 3)).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _z ∈ B_ext, 6 := Finset.sum_le_sum fun z _ => by rw [Nat.card_Icc]; omega
      _ = 6 * B_ext.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hcard_R : (Bad_port.card : ℝ) ≤ 6 * (B_ext.card : ℝ) := by exact_mod_cast hcard_nat
  calc (Bad_port.card : ℝ) ≤ 6 * ((C_d / 2) * V / Real.log (Real.log V)) :=
        hcard_R.trans (mul_le_mul_of_nonneg_left hB_card (by norm_num))
    _ = 3 * C_d * V / Real.log (Real.log V) := by ring

/-- Helper: vertical-edge points of a sub-rectangle inside a Burnol unit window inherit boundary
nonvanishing. -/
private lemma subrect_vertical_edge_ne_zero {y₁ y_u : ℝ} (N : ℕ)
    (houter : ∀ s : ℝ, _root_.RHTower.finiteThetaAmplitude N
      (_root_.RHTower.rectangleBoundaryPath
        (centeredWindowLowerLeft y₁) (centeredWindowUpperRight y_u) s) ≠ 0)
    {z : ℂ} (hre : z.re = -1 / 2 ∨ z.re = 3 / 2)
    (him_lo : y₁ ≤ z.im) (him_hi : z.im ≤ y_u) :
    _root_.RHTower.finiteThetaAmplitude N z ≠ 0 := by
  have hy_le : y₁ ≤ y_u := him_lo.trans him_hi
  refine edge_ne_zero_of_bdry_regular hy_le houter ?_ ⟨him_lo, him_hi⟩ ?_
  · rcases hre with h | h <;> (rw [h]; constructor <;> norm_num)
  · rcases hre with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

/-- **Unconditional direct critical-line flux control on `(1 - O(B)) V` micro-Planck windows.**
There exists `C₀ > 0` such that for every `B > 0`, eventually in `V`, outside a set of heights
`t₀ ∈ [V, 2V]` of Lebesgue measure at most `C₀ * B * V`, the micro-Planck window
`[1/2, 3/2] × [t₀, t₀ + B / log V]` at `N = doorSqrtPrefix ⌊t₀⌋₊` is completely zero-free for
`finiteThetaAmplitude N`, so `rightHalfPort_eq_criticalLineFlux_of_rightHalfZeroFree` applies
verbatim and gives `O(1 / (|t| + 1))` decay and `L²(0, ∞)` integrability. -/
theorem microPlanckWindow_criticalLineFlux_volume_le :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ B : ℝ, 0 < B → ∀ᶠ V : ℝ in atTop,
      volume {t₀ ∈ Icc V (2 * V) |
        ¬ let N := doorSqrtPrefix (Nat.floor t₀)
          let y₂ := t₀ + B / Real.log V
          (∀ z ∈ Icc (1 / 2) (3 / 2) ×ℂ Icc t₀ y₂, _root_.RHTower.finiteThetaAmplitude N z ≠ 0) ∧
          (∀ t : ℝ, rightHalfPort t₀ y₂ N t = vertFlux (1 / 2) t₀ y₂ N t) ∧
          (∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, ‖rightHalfPort t₀ y₂ N t‖ ≤ C / (|t| + 1)) ∧
          IntegrableOn (fun t : ℝ => ‖rightHalfPort t₀ y₂ N t‖ ^ 2) (Ioi (0 : ℝ))} ≤
        ENNReal.ofReal (C₀ * B * V) := by
  obtain ⟨C_tot, hC_tot, htot⟩ := stripFinsetPos_orderSum_le_mul_log
  refine ⟨8 * C_tot, by positivity, fun B hB => ?_⟩
  by_cases hB_large : 1 ≤ 8 * C_tot * B
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with V hV0
    calc volume {t₀ ∈ Icc V (2 * V) | _}
        ≤ volume (Icc V (2 * V)) := measure_mono fun _ ht => ht.1
      _ = ENNReal.ofReal V := by rw [Real.volume_Icc, show 2 * V - V = V by ring]
      _ ≤ ENNReal.ofReal (8 * C_tot * B * V) :=
          ENNReal.ofReal_le_ofReal ((one_mul V).symm.trans_le
            (mul_le_mul_of_nonneg_right hB_large hV0))
  · push Not at hB_large
    set c : ℝ := 1 / B
    have hc_pos : 0 < c := by dsimp only [c]; positivity
    obtain ⟨m₁, htail⟩ := exists_logStage_tail_lt c hc_pos
    filter_upwards [eventually_ge_atTop (max 32 ((m₁ + 2 : ℕ) : ℝ)),
      Real.tendsto_log_atTop.eventually_ge_atTop (max 16 B)] with V hV_lo hlog_lo
    have hV32 : 32 ≤ V := (le_max_left _ _).trans hV_lo
    have hVm₁ : ((m₁ + 2 : ℕ) : ℝ) ≤ V := (le_max_right _ _).trans hV_lo
    have hV_pos : 0 < V := by linarith only [hV32]
    have hlog16 : 16 ≤ Real.log V := (le_max_left _ _).trans hlog_lo
    have hlogB : B ≤ Real.log V := (le_max_right _ _).trans hlog_lo
    have hlogV_pos : 0 < Real.log V := by linarith only [hlog16]
    have hB_div_pos : 0 < B / Real.log V := div_pos hB hlogV_pos
    have hB_div_le1 : B / Real.log V ≤ 1 := (div_le_one hlogV_pos).mpr hlogB
    set S_V := _root_.RHTower.stripFinsetPos (2 * V + 4)
    set δ_B : ℝ := B / (16 * Real.log V)
    have hδB_le : δ_B ≤ 1 / 16 := by
      dsimp only [δ_B]
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith only [hlogB]
    -- Every height `t₀ ∈ [V, 2V]` failing zero-freeness on `[1/2, 3/2] × [t₀, t₀ + B/log V]` lies in `[w.im - 17 B / (16 log V), w.im + B / (16 log V)]` for some `w ∈ S_V`.
    have hcov : {t₀ ∈ Icc V (2 * V) |
        ¬ let N := doorSqrtPrefix (Nat.floor t₀)
          let y₂ := t₀ + B / Real.log V
          (∀ z ∈ Icc (1 / 2) (3 / 2) ×ℂ Icc t₀ y₂, _root_.RHTower.finiteThetaAmplitude N z ≠ 0) ∧
          (∀ t : ℝ, rightHalfPort t₀ y₂ N t = vertFlux (1 / 2) t₀ y₂ N t) ∧
          (∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, ‖rightHalfPort t₀ y₂ N t‖ ≤ C / (|t| + 1)) ∧
          IntegrableOn (fun t : ℝ => ‖rightHalfPort t₀ y₂ N t‖ ^ 2) (Ioi (0 : ℝ))} ⊆
        ⋃ w ∈ S_V, Icc (w.im - B / Real.log V - δ_B) (w.im + δ_B) := by
      intro t₀ ⟨ht₀_I, hfail⟩
      set m : ℕ := Nat.floor t₀
      set N : ℕ := doorSqrtPrefix m
      set y₂ : ℝ := t₀ + B / Real.log V
      have hy_le : t₀ ≤ y₂ := le_add_of_nonneg_right hB_div_pos.le
      -- If `A_N ≠ 0` on `[1/2, 3/2] × [t₀, y₂]`, `exists_criticalLineFlux_inv_decay_of_rightHalfZeroFree` discharges all 4 conjuncts.
      have hex_zero : ∃ z ∈ Icc (1 / 2) (3 / 2) ×ℂ Icc t₀ y₂,
          _root_.RHTower.finiteThetaAmplitude N z = 0 := by
        by_contra hnz_all
        push Not at hnz_all
        obtain ⟨h1, h2, h3⟩ := exists_criticalLineFlux_inv_decay_of_rightHalfZeroFree hy_le N hnz_all
        exact hfail ⟨hnz_all, h1, h2, h3⟩
      obtain ⟨z, ⟨⟨hzx1, hzx2⟩, ⟨hzy1, hzy2⟩⟩, hz0⟩ := hex_zero
      have hm_le_t₀ : (m : ℝ) ≤ t₀ := Nat.floor_le (by linarith only [hV32, ht₀_I.1])
      have ht₀_lt_m1 : t₀ < (m : ℝ) + 1 := Nat.lt_floor_add_one t₀
      have hm₁_le : m₁ ≤ m := by
        by_contra hlt; push Not at hlt
        have h1 : (m : ℝ) + 1 ≤ (m₁ : ℝ) := by exact_mod_cast hlt
        have h2 : (m₁ : ℝ) + 2 ≤ V := by push_cast at hVm₁; exact hVm₁
        linarith only [h1, h2, hm_le_t₀, ht₀_lt_m1, ht₀_I.1]
      have hcoords := burnolUnit_coords m
      have hy₁_lt : burnolUnitLower m < t₀ := by linarith only [hm_le_t₀, hcoords.2.1]
      have hy₂_lt : y₂ < burnolUnitUpper m := by
        calc y₂ = t₀ + B / Real.log V := rfl
          _ < ((m : ℝ) + 1) + 1 := add_lt_add_of_lt_of_le ht₀_lt_m1 hB_div_le1
          _ ≤ burnolUnitUpper m := by linarith only [hcoords.2.2.1]
      have hzx2_lt : z.re < 3 / 2 := by
        refine lt_of_le_of_ne hzx2 fun hre32 => ?_
        exact subrect_vertical_edge_ne_zero N
          (burnolUnit_bdry_regular m (burnolPrefix_le_doorSqrtPrefix m))
          (Or.inr hre32) (by linarith only [hy₁_lt, hzy1]) (by linarith only [hy₂_lt, hzy2]) hz0
      set n_m : ℕ := logDoorStage c m
      have hn_pos : (0 : ℝ) < (n_m : ℝ) := by linarith only [six_le_logDoorStage_real c m]
      obtain ⟨w, hw_unit, hzw_dist⟩ := exists_xiZero_near_thetaZero m N
        (r := 1 / (16 * (n_m : ℝ))) (by positivity) (htail m hm₁_le N le_rfl)
        ⟨by linarith only [hzx1], hzx2_lt,
          by linarith only [hy₁_lt, hzy1], by linarith only [hy₂_lt, hzy2]⟩ hz0
      have hn_lo : c * Real.log V ≤ (n_m : ℝ) := by
        have hX : V < ((m + 5 : ℕ) : ℝ) := by push_cast; linarith only [ht₀_I.1, ht₀_lt_m1]
        calc c * Real.log V ≤ c * Real.log ((m + 5 : ℕ) : ℝ) :=
              mul_le_mul_of_nonneg_left (Real.log_le_log hV_pos hX.le) hc_pos.le
          _ ≤ (Nat.ceil (c * Real.log ((m + 5 : ℕ) : ℝ)) : ℝ) := Nat.le_ceil _
          _ ≤ (n_m : ℝ) := by exact_mod_cast (le_max_right 6 _)
      have hrad_le_δ : 1 / (16 * (n_m : ℝ)) ≤ δ_B := by
        dsimp only [δ_B, c] at hn_lo ⊢
        have hrhs : B / (16 * Real.log V) = 1 / (16 * ((1 / B) * Real.log V)) := by
          field_simp [hB.ne', hlogV_pos.ne']
        rw [hrhs]
        exact one_div_le_one_div_of_le (by positivity)
          (mul_le_mul_of_nonneg_left hn_lo (by norm_num))
      have him_diff : |z.im - w.im| ≤ 1 / (16 * (n_m : ℝ)) :=
        (Complex.abs_im_le_norm (z - w)).trans (by simpa only [Complex.sub_im] using hzw_dist)
      have him_16 : |z.im - w.im| ≤ 1 / 16 := him_diff.trans (hrad_le_δ.trans hδB_le)
      have hy₂_le_2V1 : y₂ ≤ 2 * V + 1 := add_le_add ht₀_I.2 hB_div_le1
      obtain ⟨⟨hw0, hw1, _, _⟩, hw_xi⟩ := (mem_burnolUnitXiZeros_iff m w).mp hw_unit
      have hw_im_pos : 0 < w.im := by
        have h2 := (abs_le.mp him_16).2
        linarith only [hV32, ht₀_I.1, hzy1, h2]
      have hw_im_hi : w.im ≤ 2 * V + 4 := by
        have h1 := (abs_le.mp him_16).1
        linarith only [hy₂_le_2V1, hzy2, h1]
      have hw_S : w ∈ S_V := _root_.RHTower.mem_stripFinsetPos.mpr
        ⟨hw0, hw1, hw_im_pos, hw_im_hi, hw_xi⟩
      refine Set.mem_biUnion hw_S ⟨?_, ?_⟩
      · have hwz : w.im - z.im ≤ δ_B :=
          (le_abs_self _).trans ((abs_sub_comm _ _).trans_le (him_diff.trans hrad_le_δ))
        have hzy2' : z.im - B / Real.log V ≤ t₀ := sub_le_iff_le_add.mpr hzy2
        calc w.im - B / Real.log V - δ_B
            = (w.im - z.im - δ_B) + (z.im - B / Real.log V) := by ring
          _ ≤ 0 + t₀ := add_le_add (sub_nonpos.mpr hwz) hzy2'
          _ = t₀ := zero_add t₀
      · have hzw : z.im - w.im ≤ δ_B := (le_abs_self _).trans (him_diff.trans hrad_le_δ)
        calc t₀ ≤ z.im := hzy1
          _ = w.im + (z.im - w.im) := by ring
          _ ≤ w.im + δ_B := add_le_add_right hzw w.im
    -- Bound `#S_V ≤ 6 * C_tot * V * log V` and sum interval lengths `(9 / 8) * B / log V`.
    have hcard_S : (S_V.card : ℝ) ≤ 6 * C_tot * V * Real.log V := by
      have h1 : (S_V.card : ℝ) ≤ ∑ w ∈ S_V, ((analyticOrderAt _root_.RHTower.xi w).toNat : ℝ) := by
        rw [Finset.card_eq_sum_ones, Nat.cast_sum]
        refine Finset.sum_le_sum fun w hw => ?_
        have hxi := (_root_.RHTower.mem_stripFinsetPos.mp hw).2.2.2.2
        exact_mod_cast Nat.pos_of_ne_zero (_root_.RHTower.xi_order_toNat_ne_zero hxi)
      have h2 := h1.trans (htot (V := 2 * V + 4) (by linarith only [hV32]))
      have h2V4_le : 2 * V + 4 ≤ 3 * V := by linarith only [hV32]
      have hlog_le : Real.log (2 * V + 4) ≤ 2 * Real.log V := by
        have hsq : 2 * V + 4 ≤ V ^ 2 := by nlinarith only [hV32]
        calc Real.log (2 * V + 4) ≤ Real.log (V ^ 2) := Real.log_le_log (by linarith only [hV32]) hsq
          _ = 2 * Real.log V := by rw [Real.log_pow]; push_cast; rfl
      calc (S_V.card : ℝ)
          ≤ C_tot * (2 * V + 4) * Real.log (2 * V + 4) := h2
        _ ≤ C_tot * (3 * V) * (2 * Real.log V) :=
            mul_le_mul (mul_le_mul_of_nonneg_left h2V4_le hC_tot.le) hlog_le
              (Real.log_nonneg (by linarith only [hV32])) (by positivity)
        _ = 6 * C_tot * V * Real.log V := by ring
    calc volume {t₀ ∈ Icc V (2 * V) | _}
        ≤ volume (⋃ w ∈ S_V, Icc (w.im - B / Real.log V - δ_B) (w.im + δ_B)) := measure_mono hcov
      _ ≤ ∑ w ∈ S_V, volume (Icc (w.im - B / Real.log V - δ_B) (w.im + δ_B)) :=
          measure_biUnion_finset_le S_V _
      _ = ∑ _w ∈ S_V, ENNReal.ofReal ((9 / 8) * B / Real.log V) := by
          refine Finset.sum_congr rfl fun w _ => ?_
          rw [Real.volume_Icc]
          congr 1
          dsimp only [δ_B]; field_simp [hlogV_pos.ne']; ring
      _ = ENNReal.ofReal ((S_V.card : ℝ) * ((9 / 8) * B / Real.log V)) := by
          rw [Finset.sum_const, nsmul_eq_mul,
            ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal (8 * C_tot * B * V) := by
          refine ENNReal.ofReal_le_ofReal ?_
          calc (S_V.card : ℝ) * ((9 / 8) * B / Real.log V)
              ≤ (6 * C_tot * V * Real.log V) * ((9 / 8) * B / Real.log V) :=
                mul_le_mul_of_nonneg_right hcard_S (by positivity)
            _ = (27 / 4) * (C_tot * B * V) := by field_simp [hlogV_pos.ne']; ring
            _ ≤ 8 * C_tot * B * V := by
                have hpos_cbv : 0 ≤ C_tot * B * V := by positivity
                linarith only [hpos_cbv]

end GaloisForLFunctions.ConjugateDiagonalGeometry.WindowPortFlux

end

section AxiomAudit
open GaloisForLFunctions.ConjugateDiagonalGeometry.WindowPortFlux
#print axioms exists_vertFlux_inv_decay
#print axioms exists_shortCap_inv_decay
#print axioms rightHalfPort_eq_vertFlux_add_shortCap
#print axioms exists_rightHalfPort_shifted_inv_decay
#print axioms exists_criticalLineFlux_inv_decay_of_rightHalfZeroFree
#print axioms rightHalfPort_criticalLineFlux_zeroFree_tfae
#print axioms rightHalfPort_uniformBounded_tfae
#print axioms exists_burnol_rightHalfPort_subHalfExp_inv_decay
#print axioms almostAll_unitWindow_rightHalfPort_doubleLog_decay
#print axioms microPlanckWindow_criticalLineFlux_volume_le
end AxiomAudit
