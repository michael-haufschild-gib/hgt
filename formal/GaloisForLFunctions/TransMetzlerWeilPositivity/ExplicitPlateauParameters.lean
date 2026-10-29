import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.SmoothPlateausRecoverTheCompletedRobinMargin
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheCompleteWeilTrialEnergiesAreSimpleAndProper
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.ThePoleMomentsHaveQuadraticDilationError
import GaloisForLFunctions.ArithmeticLorentzianGeometry.TheMetzlerThresholdOfTheOverlapRatioIsOne

/-!
# Explicit plateau parameters for crossing the Metzler overlap threshold

This module fixes the smooth compactly supported profile `transMetzlerProfile = plateau (1/1000)`
and establishes the quantitative shape, Lipschitz, variance-reserve, and Robin-margin bounds
governing its complete Weil matrix near and strictly above the touching overlap ratio `c = 1`:

* explicit derivative bound `0 ≤ σ'(x) ≤ 4` for `Real.smoothTransition`, yielding the Lipschitz
  constant `8000` on `transMetzlerProfile`;
* strict positivity on `(0, 1)`, certifying via `metzlerThreshold_overlapRatio` that for every
  `ρ > 1` no unimodular gauge makes the atomic Markov Gram matrix Metzler;
* explicit charge deficit `1 / 128000 ≤ 1 - completeWeilPoleShift transMetzlerProfile 1`, ensuring
  uniform prime-defect coercivity slightly past `c = 1`;
* completed Robin margin `1 / 20 < completeWeilAdjunctionEnergy transMetzlerProfile c m` for every
  `c ∈ (0, 1 + 1/1000]` and every positive conductor `m`;
* Robin--Euler ratio `exp(β(φ₀)/‖φ₀‖²) / (2π) < 1/2`, locating the Liouville twin breakdown well
  inside the strictly separated regime.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped Real ComplexOrder

namespace GaloisForLFunctions.TransMetzlerWeilPositivity

open SpacingScaleHarmonicAnalysis CriticalArithmeticCorrelationTheory
  RenormalizedArithmeticPotentialTheory ArithmeticLorentzianGeometry
  ArithmeticElectrostatics

/-! ### Explicit smooth-transition derivative and Lipschitz constant -/

private theorem expNegInvGlue_eq_of_pos {x : ℝ} (hx : 0 < x) :
    expNegInvGlue x = Real.exp (-x⁻¹) := by
  unfold expNegInvGlue
  exact if_neg (not_le.mpr hx)

private theorem hasDerivAt_expNegInvGlue_of_pos {x : ℝ} (hx : 0 < x) :
    HasDerivAt expNegInvGlue (x⁻¹ ^ 2 * expNegInvGlue x) x := by
  have h1 : HasDerivAt (fun y : ℝ => Real.exp (-y⁻¹))
      (Real.exp (-x⁻¹) * - -(x ^ 2)⁻¹) x :=
    ((hasDerivAt_inv hx.ne').neg).exp
  have h2 : expNegInvGlue =ᶠ[𝓝 x] fun y : ℝ => Real.exp (-y⁻¹) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact expNegInvGlue_eq_of_pos hy
  refine (h1.congr_of_eventuallyEq h2).congr_deriv ?_
  rw [expNegInvGlue_eq_of_pos hx, inv_pow]
  ring

private theorem deriv_expNegInvGlue_of_pos {x : ℝ} (hx : 0 < x) :
    deriv expNegInvGlue x = x⁻¹ ^ 2 * expNegInvGlue x :=
  (hasDerivAt_expNegInvGlue_of_pos hx).deriv

private theorem deriv_expNegInvGlue_of_nonpos {x : ℝ} (hx : x ≤ 0) :
    deriv expNegInvGlue x = 0 := by
  have hcont : Continuous (deriv expNegInvGlue) :=
    (contDiff_infty_iff_deriv.mp expNegInvGlue.contDiff).2.continuous
  have hclosed : IsClosed {y : ℝ | deriv expNegInvGlue y = 0} :=
    isClosed_eq hcont continuous_const
  have hsub : Iio (0 : ℝ) ⊆ {y : ℝ | deriv expNegInvGlue y = 0} := fun y hy => by
    have heq : expNegInvGlue =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds hy] with z hz
      exact expNegInvGlue.zero_of_nonpos (le_of_lt hz)
    simp only [mem_setOf_eq, heq.deriv_eq, deriv_const]
  have hcl := hclosed.closure_subset_iff.mpr hsub
  rw [closure_Iio' nonempty_Iio] at hcl
  exact hcl hx

private theorem sq_mul_exp_neg_le {u : ℝ} (hu : 0 ≤ u) :
    u ^ 2 * Real.exp (-u) ≤ 4 * Real.exp (-2) := by
  have h1 : u / 2 ≤ Real.exp (u / 2 - 1) := by
    have := Real.add_one_le_exp (u / 2 - 1)
    linarith only [this]
  have h2 : (u / 2) ^ 2 ≤ Real.exp (u / 2 - 1) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h1 2
  rw [div_pow, ← Real.exp_nat_mul] at h2
  have h3 : ((2 : ℕ) : ℝ) * (u / 2 - 1) = u - 2 := by norm_num; ring
  rw [h3, show (2 : ℝ) ^ 2 = 4 by norm_num, div_le_iff₀ (by norm_num)] at h2
  have h4 := mul_le_mul_of_nonneg_right h2 (Real.exp_pos (-u)).le
  rwa [mul_comm (Real.exp (u - 2)), mul_assoc, ← Real.exp_add,
    show u - 2 + -u = (-2 : ℝ) by ring] at h4

private theorem deriv_expNegInvGlue_bounds (x : ℝ) :
    0 ≤ deriv expNegInvGlue x ∧ deriv expNegInvGlue x ≤ 4 * Real.exp (-2) := by
  rcases le_or_gt x 0 with hx | hx
  · rw [deriv_expNegInvGlue_of_nonpos hx]
    exact ⟨le_rfl, by positivity⟩
  · rw [deriv_expNegInvGlue_of_pos hx, expNegInvGlue_eq_of_pos hx]
    exact ⟨by positivity, sq_mul_exp_neg_le (inv_nonneg.mpr hx.le)⟩

private def smoothTransitionDenom (x : ℝ) : ℝ :=
  expNegInvGlue x + expNegInvGlue (1 - x)

private theorem smoothTransitionDenom_ge (x : ℝ) :
    Real.exp (-2) ≤ smoothTransitionDenom x := by
  unfold smoothTransitionDenom
  have hhalf : expNegInvGlue (1 / 2) = Real.exp (-2) := by
    rw [expNegInvGlue_eq_of_pos (by norm_num)]
    norm_num
  rcases le_total x (1 / 2) with hx | hx
  · have h1 : expNegInvGlue (1 / 2) ≤ expNegInvGlue (1 - x) :=
      expNegInvGlue.monotone (by linarith only [hx])
    have h0 : 0 ≤ expNegInvGlue x := expNegInvGlue.nonneg x
    linarith only [hhalf, h1, h0]
  · have h1 : expNegInvGlue (1 / 2) ≤ expNegInvGlue x :=
      expNegInvGlue.monotone hx
    have h0 : 0 ≤ expNegInvGlue (1 - x) := expNegInvGlue.nonneg (1 - x)
    linarith only [hhalf, h1, h0]

private theorem smoothTransitionDenom_pos (x : ℝ) :
    0 < smoothTransitionDenom x :=
  (Real.exp_pos (-2)).trans_le (smoothTransitionDenom_ge x)

private theorem smoothTransition_mul_denom (x : ℝ) :
    Real.smoothTransition x * smoothTransitionDenom x = expNegInvGlue x := by
  change (expNegInvGlue x / smoothTransitionDenom x) * smoothTransitionDenom x = expNegInvGlue x
  exact div_mul_cancel₀ _ (smoothTransitionDenom_pos x).ne'

private theorem hasDerivAt_expNegInvGlue (x : ℝ) :
    HasDerivAt expNegInvGlue (deriv expNegInvGlue x) x :=
  ((expNegInvGlue.contDiff (n := (⊤ : ℕ∞))).differentiable (by simp) x).hasDerivAt

private theorem hasDerivAt_smoothTransition (x : ℝ) :
    HasDerivAt Real.smoothTransition (deriv Real.smoothTransition x) x :=
  ((Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))).differentiable (by simp) x).hasDerivAt

private theorem hasDerivAt_smoothTransitionDenom (x : ℝ) :
    HasDerivAt smoothTransitionDenom
      (deriv expNegInvGlue x - deriv expNegInvGlue (1 - x)) x := by
  unfold smoothTransitionDenom
  have h1 := hasDerivAt_expNegInvGlue x
  have h2 := (hasDerivAt_expNegInvGlue (1 - x)).comp x ((hasDerivAt_id x).const_sub 1)
  exact (h1.add h2).congr_deriv (by ring)

private theorem deriv_smoothTransition_mul_denom (x : ℝ) :
    deriv Real.smoothTransition x * smoothTransitionDenom x =
      (1 - Real.smoothTransition x) * deriv expNegInvGlue x +
        Real.smoothTransition x * deriv expNegInvGlue (1 - x) := by
  have hlhs := (hasDerivAt_smoothTransition x).mul (hasDerivAt_smoothTransitionDenom x)
  have hrhs : HasDerivAt (Real.smoothTransition * smoothTransitionDenom)
      (deriv expNegInvGlue x) x :=
    (hasDerivAt_expNegInvGlue x).congr_of_eventuallyEq
      (Eventually.of_forall fun y => smoothTransition_mul_denom y)
  have heq := hlhs.unique hrhs
  linarith only [heq]

/-- The first derivative of `Real.smoothTransition` lies in `[0, 4]` everywhere. -/
theorem deriv_smoothTransition_bounds (x : ℝ) :
    0 ≤ deriv Real.smoothTransition x ∧ deriv Real.smoothTransition x ≤ 4 := by
  have hD := smoothTransitionDenom_ge x
  have hD0 := smoothTransitionDenom_pos x
  have hσ0 := Real.smoothTransition.nonneg x
  have hσ1 : 0 ≤ 1 - Real.smoothTransition x := sub_nonneg.mpr (Real.smoothTransition.le_one x)
  have hf1 := deriv_expNegInvGlue_bounds x
  have hf2 := deriv_expNegInvGlue_bounds (1 - x)
  have hid := deriv_smoothTransition_mul_denom x
  constructor
  · have hprod : 0 ≤ deriv Real.smoothTransition x * smoothTransitionDenom x := by
      rw [hid]
      exact add_nonneg (mul_nonneg hσ1 hf1.1) (mul_nonneg hσ0 hf2.1)
    exact nonneg_of_mul_nonneg_left hprod hD0
  · have hprod : deriv Real.smoothTransition x * smoothTransitionDenom x ≤
        4 * smoothTransitionDenom x := by
      calc deriv Real.smoothTransition x * smoothTransitionDenom x
          = (1 - Real.smoothTransition x) * deriv expNegInvGlue x +
              Real.smoothTransition x * deriv expNegInvGlue (1 - x) := hid
        _ ≤ (1 - Real.smoothTransition x) * (4 * Real.exp (-2)) +
              Real.smoothTransition x * (4 * Real.exp (-2)) :=
            add_le_add (mul_le_mul_of_nonneg_left hf1.2 hσ1)
              (mul_le_mul_of_nonneg_left hf2.2 hσ0)
        _ = 4 * Real.exp (-2) := by ring
        _ ≤ 4 * smoothTransitionDenom x := by linarith only [hD]
    exact le_of_mul_le_mul_right hprod hD0

/-- `Real.smoothTransition` is globally `4`-Lipschitz. -/
theorem abs_smoothTransition_sub_le (a b : ℝ) :
    |Real.smoothTransition a - Real.smoothTransition b| ≤ 4 * |a - b| := by
  have hdiff : Differentiable ℝ Real.smoothTransition :=
    (Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))).differentiable (by simp)
  have hbound : ∀ x ∈ (Set.univ : Set ℝ), ‖deriv Real.smoothTransition x‖ ≤ 4 := by
    intro x _
    rw [Real.norm_eq_abs, abs_of_nonneg (deriv_smoothTransition_bounds x).1]
    exact (deriv_smoothTransition_bounds x).2
  have h := convex_univ.norm_image_sub_le_of_norm_deriv_le (fun x _ => hdiff x) hbound
    (mem_univ b) (mem_univ a)
  simpa only [Real.norm_eq_abs] using h

/-! ### Explicit trans-Metzler profile and overlap parameters -/

/-- Transition width of the explicit trans-Metzler plateau profile. -/
def etaZero : ℝ := 1 / 1000

/-- The explicit smooth plateau profile supported in `[0, 1]` and strictly positive on `(0, 1)`. -/
def transMetzlerProfile : ℝ → ℝ := plateau etaZero

/-- Overlap excess parameter `10⁻¹⁸` past the touching ratio `1`. -/
def deltaZero : ℝ := (10 : ℝ)⁻¹ ^ 18

/-- Explicit rational overlap ratio `1 + 10⁻¹⁸ > 1` at width `c / N`. -/
def cZero : ℝ := 1 + deltaZero

/-- Explicit rational overlap ratio `1 + (1/2) * 10⁻¹⁸ > 1` in units of `atomSpacing N`. -/
def rhoZero : ℝ := 1 + (1 / 2) * deltaZero

theorem etaZero_pos : 0 < etaZero := by norm_num [etaZero]

theorem deltaZero_pos : 0 < deltaZero := by
  unfold deltaZero
  positivity

theorem one_lt_cZero : 1 < cZero := by
  unfold cZero
  linarith only [deltaZero_pos]

theorem cZero_pos : 0 < cZero := zero_lt_one.trans one_lt_cZero

theorem one_lt_rhoZero : 1 < rhoZero := by
  unfold rhoZero
  linarith only [deltaZero_pos]

theorem rhoZero_pos : 0 < rhoZero := zero_lt_one.trans one_lt_rhoZero

theorem contDiff_transMetzlerProfile : ContDiff ℝ 2 transMetzlerProfile :=
  contDiff_plateau etaZero

theorem contDiff_top_transMetzlerProfile : ContDiff ℝ (⊤ : ℕ∞) transMetzlerProfile :=
  (Real.smoothTransition.contDiff.comp (contDiff_id.div_const etaZero)).mul
    (Real.smoothTransition.contDiff.comp ((contDiff_const.sub contDiff_id).div_const etaZero))

theorem hasCompactSupport_transMetzlerProfile : HasCompactSupport transMetzlerProfile :=
  hasCompactSupport_plateau etaZero_pos

theorem transMetzlerProfile_nonneg (u : ℝ) : 0 ≤ transMetzlerProfile u :=
  plateau_nonneg u

theorem transMetzlerProfile_le_one (u : ℝ) : transMetzlerProfile u ≤ 1 :=
  plateau_le_one u

theorem transMetzlerProfile_eq_zero {u : ℝ} (hu : u ∉ Icc 0 1) : transMetzlerProfile u = 0 :=
  plateau_eq_zero etaZero_pos hu

theorem transMetzlerProfile_zero : transMetzlerProfile 0 = 0 := by
  unfold transMetzlerProfile plateau
  rw [zero_div, Real.smoothTransition.zero_of_nonpos le_rfl, zero_mul]

/-- `transMetzlerProfile` is strictly positive on the entire open support `(0, 1)`. -/
theorem transMetzlerProfile_pos {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    0 < transMetzlerProfile u := by
  unfold transMetzlerProfile plateau
  have h1 : 0 < u / etaZero := div_pos hu.1 etaZero_pos
  have h2 : 0 < (1 - u) / etaZero := div_pos (sub_pos.mpr hu.2) etaZero_pos
  exact mul_pos (Real.smoothTransition.pos_of_pos h1) (Real.smoothTransition.pos_of_pos h2)

/-- `transMetzlerProfile` is globally `8000`-Lipschitz. -/
theorem abs_transMetzlerProfile_sub_le (u v : ℝ) :
    |transMetzlerProfile u - transMetzlerProfile v| ≤ 8000 * |u - v| := by
  have h := abs_plateau_sub_le abs_smoothTransition_sub_le etaZero_pos u v
  have hc : 2 * (4 : ℝ) / etaZero = 8000 := by norm_num [etaZero]
  simpa only [transMetzlerProfile, hc] using h

/-- For every overlap multiple `ρ > 1`, `transMetzlerProfile` eventually frustrates the atomic
Markov Gram matrix in every unimodular gauge. -/
theorem transMetzlerProfile_frustrated_of_one_lt {ρ : ℝ} (hρ : 1 < ρ) :
    ∀ᶠ N : ℕ in atTop, ¬ ∃ γ : Fin N → ℂ, (∀ i, ‖γ i‖ = 1) ∧
      ∀ i j, i ≠ j → 0 ≤ starRingEnd ℂ (γ i) * γ j *
        ((-atomicMarkovGram (ArithmeticLorentzianGeometry.dilate transMetzlerProfile
          (ρ * atomSpacing N)) N i j : ℝ) : ℂ) := by
  have hm := (metzlerThreshold_overlapRatio contDiff_transMetzlerProfile
    hasCompactSupport_transMetzlerProfile transMetzlerProfile_nonneg
    (fun u hu => transMetzlerProfile_eq_zero hu)
    (fun u hu => transMetzlerProfile_pos hu)
    (by norm_num : (0 : ℝ) ≤ 8000) abs_transMetzlerProfile_sub_le).2 ρ hρ
  obtain ⟨N₀, hN₀⟩ := hm
  filter_upwards [eventually_ge_atTop N₀] with N hN
  exact hN₀ N hN

/-! ### Mass bounds, variance charge reserve, and pole-moment constant -/

theorem integral_transMetzlerProfile_ge :
    (499 : ℝ) / 500 ≤ ∫ u, transMetzlerProfile u := by
  have h := integral_plateau_ge etaZero_pos (by norm_num [etaZero])
  have hc : 1 - 2 * etaZero = (499 : ℝ) / 500 := by norm_num [etaZero]
  simpa only [transMetzlerProfile, hc] using h

theorem integral_transMetzlerProfile_le_one :
    (∫ u, transMetzlerProfile u) ≤ 1 := by
  have h1 : |∫ u, transMetzlerProfile u| ≤ ∫ u, |transMetzlerProfile u| :=
    abs_integral_le_integral_abs
  have h2 : (∫ u, |transMetzlerProfile u|) ≤ 1 := integral_abs_plateau_le etaZero_pos
  exact (le_abs_self _).trans (h1.trans h2)

theorem integral_transMetzlerProfile_sq_ge :
    (499 : ℝ) / 500 ≤ ∫ u, transMetzlerProfile u ^ 2 := by
  have h := integral_plateau_sq_ge etaZero_pos (by norm_num [etaZero])
  have hc : 1 - 2 * etaZero = (499 : ℝ) / 500 := by norm_num [etaZero]
  simpa only [transMetzlerProfile, hc] using h

theorem integral_transMetzlerProfile_sq_pos :
    0 < ∫ u, transMetzlerProfile u ^ 2 :=
  lt_of_lt_of_le (by norm_num) integral_transMetzlerProfile_sq_ge

theorem integral_transMetzlerProfile_sq_le_one :
    (∫ u, transMetzlerProfile u ^ 2) ≤ 1 :=
  integral_plateau_sq_le etaZero_pos

private theorem variance_integral_transMetzlerProfile_eq (c : ℝ) :
    ∫ u in Icc (0 : ℝ) 1, (transMetzlerProfile u - c) ^ 2 =
      (∫ u, transMetzlerProfile u ^ 2) - 2 * c * (∫ u, transMetzlerProfile u) + c ^ 2 := by
  have hcont : Continuous transMetzlerProfile := contDiff_transMetzlerProfile.continuous
  have hiφ : IntegrableOn transMetzlerProfile (Icc 0 1) := hcont.integrableOn_Icc
  have hiφ2 : IntegrableOn (fun u => transMetzlerProfile u ^ 2) (Icc 0 1) :=
    (hcont.pow 2).integrableOn_Icc
  have hIeq : ∫ u in Icc (0 : ℝ) 1, transMetzlerProfile u = ∫ u, transMetzlerProfile u :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun u hu => transMetzlerProfile_eq_zero hu
  have hMeq : ∫ u in Icc (0 : ℝ) 1, transMetzlerProfile u ^ 2 = ∫ u, transMetzlerProfile u ^ 2 :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun u hu => by
      rw [transMetzlerProfile_eq_zero hu]; norm_num
  have hexp : (fun u => (transMetzlerProfile u - c) ^ 2) =
      fun u => (transMetzlerProfile u ^ 2 - 2 * c * transMetzlerProfile u) + c ^ 2 := by
    funext u; ring
  have hi_sub : IntegrableOn (fun u => transMetzlerProfile u ^ 2 - 2 * c * transMetzlerProfile u)
      (Icc 0 1) := hiφ2.sub (hiφ.const_mul (2 * c))
  rw [hexp, integral_add hi_sub (continuous_const.integrableOn_Icc),
    integral_sub hiφ2 (hiφ.const_mul (2 * c)), integral_const_mul, hMeq, hIeq,
    setIntegral_const, smul_eq_mul, Real.volume_real_Icc_of_le zero_le_one]
  ring

/-- Explicit variance lower bound `∫ φ₀² - (∫ φ₀)² ≥ 1 / 128000` from the left transition layer. -/
theorem transMetzlerProfile_variance_ge :
    (1 : ℝ) / 128000 ≤ (∫ u, transMetzlerProfile u ^ 2) - (∫ u, transMetzlerProfile u) ^ 2 := by
  have hcont : Continuous transMetzlerProfile := contDiff_transMetzlerProfile.continuous
  have hivar (c : ℝ) : IntegrableOn (fun u => (transMetzlerProfile u - c) ^ 2) (Icc 0 1) :=
    ((hcont.sub continuous_const).pow 2).integrableOn_Icc
  have hvareq : ∫ u in Icc (0 : ℝ) 1,
      (transMetzlerProfile u - ∫ v, transMetzlerProfile v) ^ 2 =
      (∫ u, transMetzlerProfile u ^ 2) - (∫ u, transMetzlerProfile u) ^ 2 := by
    rw [variance_integral_transMetzlerProfile_eq]
    ring
  have hsub : Icc (0 : ℝ) (1 / 32000) ⊆ Icc 0 1 :=
    Icc_subset_Icc_right (by norm_num)
  have hmono : ∫ u in Icc (0 : ℝ) (1 / 32000),
      (transMetzlerProfile u - ∫ v, transMetzlerProfile v) ^ 2 ≤
      ∫ u in Icc (0 : ℝ) 1, (transMetzlerProfile u - ∫ v, transMetzlerProfile v) ^ 2 :=
    setIntegral_mono_set (hivar _) (Eventually.of_forall fun _ => sq_nonneg _) hsub.eventuallyLE
  have hpt : ∀ u ∈ Icc (0 : ℝ) (1 / 32000),
      (1 : ℝ) / 4 ≤ (transMetzlerProfile u - ∫ v, transMetzlerProfile v) ^ 2 := by
    intro u hu
    have hlip := abs_transMetzlerProfile_sub_le u 0
    rw [transMetzlerProfile_zero, sub_zero, sub_zero,
      abs_of_nonneg (transMetzlerProfile_nonneg u), abs_of_nonneg hu.1] at hlip
    have hu4 : transMetzlerProfile u ≤ 1 / 4 := by linarith only [hlip, hu.2]
    have hI34 : (3 : ℝ) / 4 ≤ ∫ v, transMetzlerProfile v := by
      linarith only [integral_transMetzlerProfile_ge]
    have hdiff : (1 : ℝ) / 2 ≤ (∫ v, transMetzlerProfile v) - transMetzlerProfile u := by
      linarith only [hu4, hI34]
    nlinarith only [hdiff]
  have hlow : (1 : ℝ) / 128000 ≤
      ∫ u in Icc (0 : ℝ) (1 / 32000),
        (transMetzlerProfile u - ∫ v, transMetzlerProfile v) ^ 2 := by
    have h := setIntegral_mono_on (continuous_const.integrableOn_Icc)
      ((hivar _).mono_set hsub) measurableSet_Icc hpt
    rw [setIntegral_const, smul_eq_mul, Real.volume_real_Icc_of_le (by norm_num)] at h
    have hvol : ((1 / 32000 : ℝ) - 0) * (1 / 4) = 1 / 128000 := by norm_num
    rwa [hvol] at h
  linarith only [hlow, hmono, hvareq]

/-- Explicit charge deficit `1 / 128000 ≤ 1 - completeWeilPoleShift transMetzlerProfile 1`. -/
theorem transMetzlerProfile_charge_deficit_ge :
    (1 : ℝ) / 128000 ≤ 1 - completeWeilPoleShift transMetzlerProfile 1 := by
  have hMpos := integral_transMetzlerProfile_sq_pos
  have hM1 := integral_transMetzlerProfile_sq_le_one
  have hvar := transMetzlerProfile_variance_ge
  rw [completeWeilPoleShift, one_mul, one_sub_div hMpos.ne']
  rw [le_div_iff₀ hMpos]
  nlinarith only [hM1, hvar]

/-- Explicit upper bound on `atomPoleMomentErrorConstant transMetzlerProfile`. -/
theorem atomPoleMomentErrorConstant_transMetzlerProfile_le :
    atomPoleMomentErrorConstant transMetzlerProfile ≤ 6 := by
  unfold atomPoleMomentErrorConstant
  have he : Real.exp (1 / 2) < 2 := by
    have he1 := Real.exp_one_lt_d9
    have hsq : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    nlinarith only [he1, hsq, Real.exp_pos (1 / 2)]
  have hI0 : 0 ≤ ∫ u, |transMetzlerProfile u| := integral_nonneg fun _ => abs_nonneg _
  have hI1 : (∫ u, |transMetzlerProfile u|) ≤ 1 := integral_abs_plateau_le etaZero_pos
  have hIsq : (∫ u, |transMetzlerProfile u|) ^ 2 ≤ 1 := by nlinarith only [hI0, hI1]
  have hM := integral_transMetzlerProfile_sq_ge
  have hMpos := integral_transMetzlerProfile_sq_pos
  rw [div_le_iff₀ hMpos]
  have hexp : Real.exp (1 / 2) * (Real.exp (1 / 2) + 1) / 2 ≤ 3 := by
    nlinarith only [he, Real.exp_pos (1 / 2)]
  nlinarith only [hexp, hIsq, hM, Real.exp_pos (1 / 2)]

/-! ### Completed Robin margin and Robin--Euler twin threshold -/

/-- Rational upper bound `log (2π) < 1839 / 1000`. -/
theorem log_two_pi_lt : Real.log (2 * Real.pi) < (1839 : ℝ) / 1000 := by
  have hlog2 : Real.log 2 < (347 : ℝ) / 500 := by
    linarith only [Real.log_two_lt_d9]
  have hlogpi : Real.log Real.pi < (229 : ℝ) / 200 := by
    rw [Real.log_lt_iff_lt_exp Real.pi_pos]
    refine Real.pi_lt_d4.trans_le ?_
    refine le_trans ?_ (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 229 / 200) 7)
    norm_num [Finset.sum_range_succ]
  rw [Real.log_mul two_ne_zero Real.pi_pos.ne']
  linarith only [hlog2, hlogpi]

/-- Every positive conductor has completed adjunction energy strictly above `1 / 20` on
`transMetzlerProfile` throughout `c ∈ (0, 1 + 1/1000]`. -/
theorem completeWeilAdjunctionEnergy_transMetzlerProfile_gt_one_twentieth
    {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1 + 1 / 1000) {m : ℕ} (hm : 0 < m) :
    (1 : ℝ) / 20 < completeWeilAdjunctionEnergy transMetzlerProfile c m := by
  have hshape := plateau_completed_shape_ge (η := etaZero) (δ := 1 / 20)
    etaZero_pos (by norm_num [etaZero]) (by norm_num) (by norm_num)
  have hnum : (1908 : ℝ) / 1000 <
      (1 - (1 / 20 : ℝ)) * (1 - 2 * etaZero / (1 / 20)) + (1 - 2 * etaZero) ^ 2 := by
    norm_num [etaZero]
  have hshape' : (1908 : ℝ) / 1000 <
      bumpRobin transMetzlerProfile 1 / (∫ u, transMetzlerProfile u ^ 2) +
        completeWeilPoleShift transMetzlerProfile 1 := by
    rw [completeWeilPoleShift, one_mul]
    exact hnum.trans_le hshape
  have h2pi := log_two_pi_lt
  have hq0_le : completeWeilPoleShift transMetzlerProfile 1 ≤ 1 := by
    simpa only [one_mul] using completeWeilPoleShift_le contDiff_transMetzlerProfile.continuous
      (fun u hu => transMetzlerProfile_eq_zero hu) integral_transMetzlerProfile_sq_pos zero_le_one
  have hq0_nonneg : 0 ≤ completeWeilPoleShift transMetzlerProfile 1 :=
    completeWeilPoleShift_nonneg transMetzlerProfile zero_le_one
  have hself : completeWeilSelfFinitePart transMetzlerProfile c =
      -Real.log (2 * Real.pi) - Real.log c +
        bumpRobin transMetzlerProfile 1 / (∫ u, transMetzlerProfile u ^ 2) := by
    rw [completeWeilSelfFinitePart, one_div, Real.log_inv,
      Real.log_mul (by positivity : (2 * Real.pi : ℝ) ≠ 0) hc0.ne']
    ring
  have hshift_eq : completeWeilPoleShift transMetzlerProfile c =
      c * completeWeilPoleShift transMetzlerProfile 1 := by
    unfold completeWeilPoleShift; ring
  have hlogc : Real.log c ≤ c - 1 := Real.log_le_sub_one_of_pos hc0
  have hm1_energy : (1 : ℝ) / 20 < completeWeilAdjunctionEnergy transMetzlerProfile c 1 := by
    have hram1 := log_le_ramanujanAdjunctionEnergy_sub 1
    simp only [Nat.cast_one, Real.log_one] at hram1
    rw [completeWeilAdjunctionEnergy, if_pos rfl, hself, hshift_eq]
    have hc_shift : completeWeilPoleShift transMetzlerProfile 1 - 1 / 1000 ≤
        -Real.log c + c * completeWeilPoleShift transMetzlerProfile 1 := by
      have h1mc : 0 ≤ (1 - c) * (1 - completeWeilPoleShift transMetzlerProfile 1) ∨
          c > 1 := by
        rcases le_or_gt c 1 with hle | hgt
        · exact Or.inl (mul_nonneg (sub_nonneg.mpr hle) (sub_nonneg.mpr hq0_le))
        · exact Or.inr hgt
      rcases h1mc with hnonneg | hgt
      · nlinarith only [hlogc, hnonneg]
      · nlinarith only [hlogc, hgt, hc1, hq0_le, hq0_nonneg]
    linarith only [hshape', h2pi, hc_shift, hram1]
  rcases eq_or_lt_of_le (Nat.succ_le_of_lt hm) with rfl | hm2
  · exact hm1_energy
  · refine hm1_energy.trans ?_
    have hlog2 : (693 : ℝ) / 1000 < Real.log 2 := by
      linarith only [Real.log_two_gt_d9]
    have hgap := (SelectiveMultiscaleArithmeticPositivity.ramanujanAdjunctionEnergy_sub_one_ge hm2).1
    have hshift_le : completeWeilPoleShift transMetzlerProfile c ≤ c :=
      completeWeilPoleShift_le contDiff_transMetzlerProfile.continuous
        (fun u hu => transMetzlerProfile_eq_zero hu) integral_transMetzlerProfile_sq_pos hc0.le
    rw [completeWeilAdjunctionEnergy, completeWeilAdjunctionEnergy, if_pos rfl,
      if_neg (by omega), add_zero]
    linarith only [hlog2, hgap, hshift_le, hc1]

/-- The Robin--Euler threshold `exp(β(φ₀)/‖φ₀‖²) / (2π)` of `transMetzlerProfile` is strictly
less than `1 / 2`. -/
theorem transMetzlerProfile_robinEuler_lt_half :
    Real.exp (bumpRobin transMetzlerProfile 1 / ∫ u, transMetzlerProfile u ^ 2) /
      (2 * Real.pi) < 1 / 2 := by
  have hb := bumpRobin_plateau_le (C := 4) (by norm_num) abs_smoothTransition_sub_le
    etaZero_pos (by norm_num [etaZero])
  have hlog10 : Real.log 10 < (14 : ℝ) / 5 := by
    have h10 : Real.log 10 < Real.log 16 := Real.log_lt_log (by norm_num) (by norm_num)
    have h16 : Real.log (16 : ℝ) = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow]; norm_num
    have h2 : Real.log 2 < (7 : ℝ) / 10 := by linarith only [Real.log_two_lt_d9]
    linarith only [h10, h16, h2]
  have hlog_eta : Real.log etaZero = -3 * Real.log 10 := by
    rw [etaZero, one_div, Real.log_inv, show (1000 : ℝ) = 10 ^ (3 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have hb_num : bumpRobin transMetzlerProfile 1 ≤ (1045 : ℝ) / 1000 := by
    unfold transMetzlerProfile
    rw [hlog_eta] at hb
    rw [etaZero] at hb ⊢
    norm_num at hb
    linarith only [hb, hlog10]
  have hM := integral_transMetzlerProfile_sq_ge
  have hMpos := integral_transMetzlerProfile_sq_pos
  have hquot : bumpRobin transMetzlerProfile 1 / (∫ u, transMetzlerProfile u ^ 2) ≤ 21 / 20 := by
    rw [div_le_iff₀ hMpos]
    linarith only [hb_num, hM]
  have hexp_le : Real.exp (21 / 20 : ℝ) < Real.pi := by
    have he1 : Real.exp 1 < (272 : ℝ) / 100 := by linarith only [Real.exp_one_lt_d9]
    have hm19 : (19 : ℝ) / 20 ≤ Real.exp (-(1 / 20 : ℝ)) := by
      have h := Real.add_one_le_exp (-(1 / 20 : ℝ))
      linarith only [h]
    have he20 : Real.exp (1 / 20 : ℝ) ≤ 20 / 19 := by
      have hprod : Real.exp (1 / 20 : ℝ) * Real.exp (-(1 / 20 : ℝ)) = 1 := by
        rw [← Real.exp_add]; norm_num
      have hmul := mul_le_mul_of_nonneg_left hm19 (Real.exp_pos (1 / 20 : ℝ)).le
      linarith only [hprod, hmul]
    have hsplit : Real.exp (21 / 20 : ℝ) = Real.exp 1 * Real.exp (1 / 20 : ℝ) := by
      rw [← Real.exp_add]; norm_num
    have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
    rw [hsplit]
    nlinarith only [he1, he20, hpi, Real.exp_pos (1 / 20 : ℝ)]
  rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)]
  have hexp_mono := Real.exp_le_exp.mpr hquot
  linarith only [hexp_mono, hexp_le]

end GaloisForLFunctions.TransMetzlerWeilPositivity

#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.deriv_smoothTransition_bounds
#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.transMetzlerProfile_frustrated_of_one_lt
#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.transMetzlerProfile_charge_deficit_ge
#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.completeWeilAdjunctionEnergy_transMetzlerProfile_gt_one_twentieth
#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.transMetzlerProfile_robinEuler_lt_half
