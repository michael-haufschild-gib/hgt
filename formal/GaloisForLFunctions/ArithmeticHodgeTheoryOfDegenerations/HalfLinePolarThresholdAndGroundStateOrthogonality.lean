import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.PolarPaymentExcludesChargedLimitProfiles
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.PolarPaymentThresholdHierarchy

/-!
# Half-line polar threshold identity and critical ground-state orthogonality

Window-level polar payment across all compact terminal windows `[-A, 0]` (`A ≥ 0`) is equivalent
to strict positivity of the Gamma-truncated charged critical form on measurable half-line profiles
`F ∈ L¹(ℝ) ∩ L²(ℝ)` vanishing on `[0, ∞)` with finite eighth exponential mass. Consequently,
`polarPaymentCriticalThreshold`, `criticalPositivityThreshold`, and `halfLinePolarThreshold`
coincide identically.

At the global continuum window threshold `W = ⨅ A ≥ 0, windowThreshold A`, either
`RiemannHypothesis` holds (`W = ⊤`), or `W = (W₀ : EReal)` (`0 < W₀`) and strong compactness of
the high-conductor collar bridge produces a unit-norm half-line ground state `F_*` at `W₀`. Every
such ground state imposes an explicit reciprocal shift bound on `polarPaymentCriticalThreshold` in
terms of its polar pairing `∫ F · polarSourceProfile`, forcing exact pole orthogonality whenever
`polarPaymentCriticalThreshold = W < ⊤`.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set RHTower
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open CriticalArithmeticCorrelationTheory CompletedArithmeticForms RenormalizedArithmeticPotentialTheory
  SpacingScaleHarmonicAnalysis ArithmeticCastelnuovoSeveri WindowTowerOfSpecZ
  CohomologyOfWindowsOfSpecZ WindowVisibilityLaw ArithmeticPositivityTheory
  ArithmeticDegenerationTheory

/-- Strict positivity of the Gamma-truncated charged critical form at ratio `R` across all
jointly nontrivial measurable half-line profiles `F ∈ L¹(ℝ) ∩ L²(ℝ)` with `∫ F² ≤ 1` and finite
eighth exponential mass. -/
def HalfLinePolarPositive (R : ℝ) : Prop :=
  ∀ (F : ℝ → ℝ) (β : ℝ), Measurable F → Integrable F → Integrable (fun u => F u ^ 2) →
    (∫ u, F u ^ 2) ≤ 1 → Integrable (fun u => F u ^ 2 * Real.exp (-(8 * u))) →
    (∀ u, 0 ≤ u → F u = 0) → 0 < (∫ u, F u ^ 2) + β ^ 2 →
    ∃ T : ℝ, Real.exp factorialSpanGammaOffset ≤ T ∧
      0 < truncatedWeilForm F T +
        criticalAliasCoefficient R * (∫ u in Iio 0, F u ^ 2 * Real.exp (-(8 * u))) +
        (∫ u, tiltedUnitSpline u ^ 2) * criticalPoleWindowCost R * β ^ 2 +
        2 * (∫ u, tiltedUnitSpline u) * β * (∫ u, F u * polarSourceProfile u)

/-- Supremum in `EReal` of positive ratios at which `HalfLinePolarPositive` holds. -/
def halfLinePolarThreshold : EReal :=
  sSup ((fun R : ℝ => (R : EReal)) '' {R : ℝ | 0 < R ∧ HalfLinePolarPositive R})

/-- Polar payment on all compact windows at ratio `S` forces `HalfLinePolarPositive R` at every
strictly smaller positive ratio `R < S`. -/
theorem halfLinePolarPositive_of_lt_polarPayment {R S : ℝ} (hR : 0 < R) (hRS : R < S)
    (hpay : ∀ A : ℝ, 0 ≤ A → PolarPaymentAt S A) :
    HalfLinePolarPositive R := by
  intro F β hFm hFi hF2 hFmass hF8 hFzero hnonzero
  by_contra hnot
  push Not at hnot
  exact no_charged_limit_profile_below_polarPayment hR hRS hpay hFm hFi hF2 hFmass hF8 hFzero
    hnonzero hnot

/-- Above `e^{G₀}` the Gamma weight is nonnegative, so the truncated Weil form bounds `weilQuad`
from below on smooth compactly supported profiles. -/
theorem truncatedWeilForm_le_weilQuad {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {T : ℝ} (hT : Real.exp factorialSpanGammaOffset ≤ T) :
    truncatedWeilForm f T ≤ weilQuad f := by
  have hlow := lowGammaForm_add_high_le_archForm hf hfc hT le_rfl
  have hlog : 0 ≤ Real.log T - factorialSpanGammaOffset := by
    have h := Real.log_le_log (Real.exp_pos _) hT
    rw [Real.log_exp] at h
    linarith only [h]
  have hhigh : 0 ≤ (Real.log T - factorialSpanGammaOffset) * highFourierMass f T :=
    mul_nonneg hlog (highFourierMass_nonneg f T)
  rw [weilQuad_eq_arch_sub_prime_add_pole hf hfc, truncatedWeilForm]
  linarith only [hlow, hhigh]

/-- Half-line continuum polar positivity at `R > 0` implies `PolarPaymentAt R A` on every compact
terminal window `[-A, 0]` (`A ≥ 0`). -/
theorem polarPaymentAt_of_halfLinePolarPositive {R A : ℝ} (hR : 0 < R)
    (hpos : HalfLinePolarPositive R) (hA : 0 ≤ A) :
    PolarPaymentAt R A := by
  intro h hh hsupp
  let F₀ : ℝ → ℝ := halfWeight h
  have hF₀d : ContDiff ℝ 2 F₀ := contDiff_halfWeight hh
  have hF₀c : HasCompactSupport F₀ := hasCompactSupport_halfWeight (hasCompactSupport_of_window hsupp)
  have hF₀_zero : ∀ u, 0 ≤ u → F₀ u = 0 := by
    intro u hu
    rcases lt_or_eq_of_le hu with hgt | rfl
    · have hz : h u = 0 := hsupp u fun hm => by linarith only [hm.2, hgt]
      simp only [F₀, halfWeight, hz, mul_zero]
    · have hx_zero : ∀ k : ℕ, h (1 / ((k : ℝ) + 1)) = 0 := fun k => by
        have hk : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
        exact hsupp _ fun hm => by linarith only [hm.2, hk]
      have hlim := hh.continuous.continuousAt.tendsto.comp tendsto_one_div_add_atTop_nhds_zero_nat
      have h0 : h 0 = 0 :=
        tendsto_nhds_unique hlim (by simpa only [Function.comp_def, hx_zero] using tendsto_const_nhds)
      simp only [F₀, halfWeight, h0, mul_zero]
  let S₀ : ℝ := generalTerminalPolarSource A h
  let D : ℝ := criticalPoleWindowCost R
  have hD : 0 < D := criticalPoleWindowCost_pos hR
  let I₁ : ℝ := ∫ u, tiltedUnitSpline u
  let I₂ : ℝ := ∫ u, tiltedUnitSpline u ^ 2
  have hI₁ : I₁ ≠ 0 := integral_tiltedUnitSpline_ne_zero
  have hI₂ : 0 < I₂ := integral_tiltedUnitSpline_sq_pos
  let β₀ : ℝ := -S₀ / (I₁ * D)
  have hF₀2_int : Integrable fun u => F₀ u ^ 2 := by
    have hi : Integrable fun u => F₀ u * F₀ u :=
      (hF₀d.continuous.mul hF₀d.continuous).integrable_of_hasCompactSupport hF₀c.mul_left
    simpa only [sq] using hi
  have hsum_nn : 0 ≤ (∫ u, F₀ u ^ 2) + β₀ ^ 2 :=
    add_nonneg (integral_nonneg fun _ => sq_nonneg _) (sq_nonneg _)
  rcases eq_or_lt_of_le hsum_nn with hzero_sum | hpos_sum
  · have hF₀_int_zero : (∫ u, F₀ u ^ 2) = 0 := by
      have h1 : 0 ≤ ∫ u, F₀ u ^ 2 := integral_nonneg fun _ => sq_nonneg _
      have h2 : 0 ≤ β₀ ^ 2 := sq_nonneg _
      linarith only [hzero_sum, h1, h2]
    have hβ₀_sq : β₀ ^ 2 = 0 := by linarith only [hzero_sum, hF₀_int_zero]
    have hβ₀ : β₀ = 0 := sq_eq_zero_iff.mp hβ₀_sq
    have hS₀ : S₀ = 0 := by
      have hne : I₁ * D ≠ 0 := mul_ne_zero hI₁ hD.ne'
      have hd : -S₀ = 0 := (div_eq_zero_iff.mp hβ₀).resolve_right hne
      linarith only [hd]
    have hF₀_eq_zero : F₀ = 0 := by
      funext u₀
      by_contra hne
      let ε : ℝ := F₀ u₀ ^ 2 / 2
      have hε : 0 < ε := half_pos (sq_pos_of_ne_zero hne)
      obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.mp (hF₀d.continuous.pow 2).continuousAt ε hε
      have hsub : ∀ u ∈ Icc (u₀ - δ / 2) (u₀ + δ / 2), ε ≤ F₀ u ^ 2 := by
        intro u hu
        have hd : dist u u₀ < δ := by
          rw [Real.dist_eq, abs_lt]
          constructor <;> linarith only [hu.1, hu.2, hδ]
        have hb := hball hd
        rw [Real.dist_eq, abs_lt] at hb
        simp only [Pi.pow_apply] at hb
        dsimp only [ε] at hb ⊢
        linarith only [hb.1]
      have hle1 : (∫ _ in Icc (u₀ - δ / 2) (u₀ + δ / 2), ε) ≤
          ∫ u in Icc (u₀ - δ / 2) (u₀ + δ / 2), F₀ u ^ 2 :=
        setIntegral_mono_on (integrableOn_const isCompact_Icc.measure_lt_top.ne)
          hF₀2_int.integrableOn measurableSet_Icc hsub
      have hle2 : (∫ u in Icc (u₀ - δ / 2) (u₀ + δ / 2), F₀ u ^ 2) ≤ ∫ u, F₀ u ^ 2 :=
        setIntegral_le_integral hF₀2_int (Eventually.of_forall fun _ => sq_nonneg _)
      rw [setIntegral_const, Measure.real, Real.volume_Icc,
        ENNReal.toReal_ofReal (by linarith only [hδ] : 0 ≤ (u₀ + δ / 2) - (u₀ - δ / 2)),
        smul_eq_mul] at hle1
      have hpos_i : 0 < ((u₀ + δ / 2) - (u₀ - δ / 2)) * ε :=
        mul_pos (by linarith only [hδ]) hε
      rw [hF₀_int_zero] at hle2
      linarith only [hle1, hle2, hpos_i]
    have hwq0 : weilQuad F₀ = 0 := by
      have hm := weilQuad_const_mul hF₀d hF₀c 0
      have h0eq : (fun x => (0 : ℝ) * F₀ x) = F₀ := by
        funext x; simp [hF₀_eq_zero]
      rw [h0eq, zero_pow two_ne_zero, zero_mul] at hm
      exact hm
    have hexp0 : exponentialMass 8 F₀ = 0 := by
      simp [exponentialMass, hF₀_eq_zero]
    change S₀ ^ 2 / D ≤ windowPencil R F₀
    rw [hS₀, windowPencil, hwq0, hexp0]
    norm_num
  · let σ : ℝ := Real.sqrt ((∫ u, F₀ u ^ 2) + β₀ ^ 2)
    have hσ : 0 < σ := Real.sqrt_pos.mpr hpos_sum
    have hσ_sq : σ ^ 2 = (∫ u, F₀ u ^ 2) + β₀ ^ 2 := Real.sq_sqrt hpos_sum.le
    let F₁ : ℝ → ℝ := fun u => σ⁻¹ * F₀ u
    let β₁ : ℝ := σ⁻¹ * β₀
    have hF₁d : ContDiff ℝ 2 F₁ := contDiff_const.mul hF₀d
    have hF₁c : HasCompactSupport F₁ := hF₀c.mul_left
    have hF₁m : Measurable F₁ := hF₁d.continuous.measurable
    have hF₁i : Integrable F₁ := hF₁d.continuous.integrable_of_hasCompactSupport hF₁c
    have hF₁2 : Integrable fun u => F₁ u ^ 2 := by
      have hi : Integrable fun u => F₁ u * F₁ u :=
        (hF₁d.continuous.mul hF₁d.continuous).integrable_of_hasCompactSupport hF₁c.mul_left
      simpa only [sq] using hi
    have hF₁8 : Integrable fun u => F₁ u ^ 2 * Real.exp (-(8 * u)) := by
      have hi : Integrable fun u => (F₁ u * F₁ u) * Real.exp (-(8 * u)) :=
        ((hF₁d.continuous.mul hF₁d.continuous).mul
          (Real.continuous_exp.comp
            (continuous_const.mul continuous_id).neg)).integrable_of_hasCompactSupport
          (hF₁c.mul_left.mul_right)
      simpa only [sq] using hi
    have hF₁_norm : (∫ u, F₁ u ^ 2) + β₁ ^ 2 = 1 := by
      have hint : (∫ u, F₁ u ^ 2) = σ⁻¹ ^ 2 * ∫ u, F₀ u ^ 2 := by
        dsimp only [F₁]
        simp_rw [mul_pow]
        exact integral_const_mul _ _
      rw [hint]
      dsimp only [β₁]
      rw [mul_pow, ← mul_add, ← hσ_sq, inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 hσ.ne')]
    have hF₁_mass : (∫ u, F₁ u ^ 2) ≤ 1 := by linarith only [hF₁_norm, sq_nonneg β₁]
    have hF₁_zero : ∀ u, 0 ≤ u → F₁ u = 0 := fun u hu => by
      simp only [F₁, hF₀_zero u hu, mul_zero]
    have hF₁_pos : 0 < (∫ u, F₁ u ^ 2) + β₁ ^ 2 := by rw [hF₁_norm]; exact one_pos
    obtain ⟨T, hT, hposT⟩ := hpos F₁ β₁ hF₁m hF₁i hF₁2 hF₁_mass hF₁8 hF₁_zero hF₁_pos
    have hwq_le : truncatedWeilForm F₁ T ≤ weilQuad F₁ := truncatedWeilForm_le_weilQuad hF₁d hF₁c hT
    have hI₈_le : (∫ u in Iio 0, F₁ u ^ 2 * Real.exp (-(8 * u))) ≤ exponentialMass 8 F₁ := by
      have hle := setIntegral_le_integral (s := Iio (0 : ℝ)) hF₁8
        (Eventually.of_forall fun _ => by positivity)
      simpa only [exponentialMass, mul_comm] using hle
    have hAlias_nn : 0 ≤ criticalAliasCoefficient R := by
      unfold criticalAliasCoefficient
      have := tiltedJordanOne_pos
      positivity
    have hphys₁ : 0 < weilQuad F₁ + criticalAliasCoefficient R * exponentialMass 8 F₁ +
        I₂ * D * β₁ ^ 2 + 2 * I₁ * β₁ * (∫ u, F₁ u * polarSourceProfile u) := by
      have hm := mul_le_mul_of_nonneg_left hI₈_le hAlias_nn
      dsimp only [I₁, I₂, D] at hposT ⊢
      linarith only [hposT, hwq_le, hm]
    have hwq_scale : weilQuad F₁ = σ⁻¹ ^ 2 * weilQuad F₀ :=
      weilQuad_const_mul hF₀d hF₀c σ⁻¹
    have hexp_scale : exponentialMass 8 F₁ = σ⁻¹ ^ 2 * exponentialMass 8 F₀ := by
      unfold exponentialMass
      dsimp only [F₁]
      rw [← integral_const_mul]
      exact integral_congr_ae (Eventually.of_forall fun u => by ring)
    have hsrc_scale : (∫ u, F₁ u * polarSourceProfile u) =
        σ⁻¹ * ∫ u, F₀ u * polarSourceProfile u := by
      dsimp only [F₁]
      simp_rw [mul_assoc]
      exact integral_const_mul _ _
    rw [hwq_scale, hexp_scale, hsrc_scale] at hphys₁
    have hphys₀ : 0 < weilQuad F₀ + criticalAliasCoefficient R * exponentialMass 8 F₀ +
        I₂ * D * β₀ ^ 2 + 2 * I₁ * β₀ * (∫ u, F₀ u * polarSourceProfile u) := by
      have hmul := mul_pos (pow_pos hσ 2) hphys₁
      have hinv : σ ^ 2 * σ⁻¹ ^ 2 = 1 := by
        rw [inv_pow, mul_inv_cancel₀ (pow_ne_zero 2 hσ.ne')]
      have hid : σ ^ 2 * (σ⁻¹ ^ 2 * weilQuad F₀ +
          criticalAliasCoefficient R * (σ⁻¹ ^ 2 * exponentialMass 8 F₀) +
          I₂ * D * β₁ ^ 2 + 2 * I₁ * β₁ * (σ⁻¹ * ∫ u, F₀ u * polarSourceProfile u)) =
          (σ ^ 2 * σ⁻¹ ^ 2) * (weilQuad F₀ + criticalAliasCoefficient R * exponentialMass 8 F₀ +
            I₂ * D * β₀ ^ 2 + 2 * I₁ * β₀ * (∫ u, F₀ u * polarSourceProfile u)) := by
        dsimp only [β₁]; ring
      rw [hid, hinv, one_mul] at hmul
      exact hmul
    have hsrc_eq : S₀ = splineAtom * ∫ u, F₀ u * polarSourceProfile u :=
      generalTerminalPolarSource_eq_integral_polarSourceProfile hh hA hsupp
    have hκ : 0 < splineAtom := splineAtom_pos
    have hscaled := mul_pos hκ hphys₀
    have heq : splineAtom * (weilQuad F₀ + criticalAliasCoefficient R * exponentialMass 8 F₀ +
        I₂ * D * β₀ ^ 2 + 2 * I₁ * β₀ * (∫ u, F₀ u * polarSourceProfile u)) =
        windowPencil R F₀ - S₀ ^ 2 / D := by
      rw [hsrc_eq]
      dsimp only [β₀]
      rw [hsrc_eq]
      unfold windowPencil splineAtom criticalAliasCoefficient
      dsimp only [I₁, I₂] at hI₁ hI₂ ⊢
      field_simp [hI₁, hI₂.ne', hR.ne', hD.ne']
      ring
    rw [heq] at hscaled
    exact (sub_pos.mp hscaled).le

/-- **Half-line continuum polar threshold identity**: the window-level polar-payment threshold
equals the continuum half-line charged Gamma threshold. -/
theorem polarPaymentCriticalThreshold_eq_halfLinePolarThreshold :
    polarPaymentCriticalThreshold = halfLinePolarThreshold := by
  apply le_antisymm
  · refine sSup_le ?_
    rintro _ ⟨S, ⟨hS, hpay⟩, rfl⟩
    refine le_of_forall_lt fun c hc => ?_
    rcases le_or_gt c 0 with hc0 | hc0
    · obtain ⟨R₀, hR₀, hpay₀⟩ := exists_polarPaymentAt_on_every_window
      have hpos₀ : HalfLinePolarPositive (R₀ / 2) :=
        halfLinePolarPositive_of_lt_polarPayment (half_pos hR₀) (half_lt_self hR₀)
          (hpay₀ R₀ hR₀ le_rfl)
      exact hc0.trans_lt ((EReal.coe_pos.mpr (half_pos hR₀)).trans_le
        (le_sSup ⟨R₀ / 2, ⟨half_pos hR₀, hpos₀⟩, rfl⟩))
    · lift c to ℝ using ⟨(hc.trans (EReal.coe_lt_top S)).ne, (lt_trans EReal.bot_lt_zero hc0).ne'⟩
      have hc_pos : 0 < c := EReal.coe_pos.mp hc0
      have hcS : c < S := EReal.coe_lt_coe_iff.mp hc
      let R : ℝ := (c + S) / 2
      have hR : 0 < R := by dsimp only [R]; linarith only [hc_pos, hS]
      have hRS : R < S := by dsimp only [R]; linarith only [hcS]
      have hcR : (c : EReal) < (R : EReal) := EReal.coe_lt_coe_iff.mpr (by
        dsimp only [R]; linarith only [hcS])
      exact hcR.trans_le (le_sSup ⟨R, ⟨hR, halfLinePolarPositive_of_lt_polarPayment hR hRS hpay⟩, rfl⟩)
  · refine sSup_le ?_
    rintro _ ⟨R, ⟨hR, hpos⟩, rfl⟩
    exact le_sSup ⟨R, ⟨hR, fun A hA => polarPaymentAt_of_halfLinePolarPositive hR hpos hA⟩, rfl⟩

/-- Whole-space critical positivity sits below `halfLinePolarThreshold`. -/
theorem criticalPositivityThreshold_le_halfLinePolarThreshold :
    criticalPositivityThreshold ≤ halfLinePolarThreshold :=
  criticalPositivityThreshold_le_polarPaymentCriticalThreshold.trans
    polarPaymentCriticalThreshold_eq_halfLinePolarThreshold.le

/-- Equality `polarPaymentCriticalThreshold = ⨅ A ≥ 0, windowThreshold A` holds if and only if
`HalfLinePolarPositive R` holds at every positive ratio strictly below the global window threshold. -/
theorem polarPaymentCriticalThreshold_eq_iInf_windowThreshold_iff_halfLinePolarPositive :
    polarPaymentCriticalThreshold = (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) ↔
      ∀ R : ℝ, 0 < R → (R : EReal) < (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) →
        HalfLinePolarPositive R := by
  constructor
  · intro heq R hR hlt
    rw [← heq] at hlt
    obtain ⟨_, ⟨S, ⟨hS, hpay⟩, rfl⟩, hRS⟩ := lt_sSup_iff.mp hlt
    exact halfLinePolarPositive_of_lt_polarPayment hR (EReal.coe_lt_coe_iff.mp hRS) hpay
  · intro hall
    apply le_antisymm polarPaymentCriticalThreshold_le_iInf_windowThreshold
    rw [polarPaymentCriticalThreshold_eq_halfLinePolarThreshold]
    refine le_of_forall_lt fun c hc => ?_
    rcases le_or_gt c 0 with hc0 | hc0
    · have hpos := polarPaymentCriticalThreshold_pos
      rw [polarPaymentCriticalThreshold_eq_halfLinePolarThreshold] at hpos
      exact hc0.trans_lt hpos
    · lift c to ℝ using ⟨(hc.trans_le le_top).ne, (lt_trans EReal.bot_lt_zero hc0).ne'⟩
      have hc_pos : 0 < c := EReal.coe_pos.mp hc0
      cases hW : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) with
      | bot => rw [hW] at hc; exact absurd hc not_lt_bot
      | top =>
        have hlt1 : (c : EReal) < ((c + 1 : ℝ) : EReal) := EReal.coe_lt_coe_iff.mpr (by linarith)
        have htop : ((c + 1 : ℝ) : EReal) < ⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A := by
          rw [hW]; exact EReal.coe_lt_top _
        exact hlt1.trans_le
          (le_sSup ⟨c + 1, ⟨by positivity, hall (c + 1) (by positivity) htop⟩, rfl⟩)
      | coe M =>
        rw [hW, EReal.coe_lt_coe_iff] at hc
        let d : ℝ := (c + M) / 2
        have hd_pos : 0 < d := by dsimp only [d]; linarith
        have hcd : (c : EReal) < (d : EReal) :=
          EReal.coe_lt_coe_iff.mpr (by dsimp only [d]; linarith)
        have hdW : (d : EReal) < ⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A := by
          rw [hW, EReal.coe_lt_coe_iff]; dsimp only [d]; linarith
        exact hcd.trans_le (le_sSup ⟨d, ⟨hd_pos, hall d hd_pos hdW⟩, rfl⟩)

/-- A unit-norm measurable half-line profile supported on `(-∞, 0)` with finite eighth exponential
mass whose critical Gamma-truncated energy at ratio `W₀` is nonpositive at every cutoff `T ≥ e^{G₀}`. -/
def IsCriticalHalfLineGroundState (W₀ : ℝ) (F : ℝ → ℝ) : Prop :=
  Measurable F ∧ Integrable F ∧ Integrable (fun u => F u ^ 2) ∧
    (∫ u, F u ^ 2) = 1 ∧ Integrable (fun u => F u ^ 2 * Real.exp (-(8 * u))) ∧
    (∀ u, 0 ≤ u → F u = 0) ∧
    ∀ T : ℝ, Real.exp factorialSpanGammaOffset ≤ T →
      truncatedWeilForm F T +
        criticalAliasCoefficient W₀ * (∫ u in Iio 0, F u ^ 2 * Real.exp (-(8 * u))) ≤ 0

/-- **Unconditional critical half-line ground-state dichotomy.** Either `RiemannHypothesis` holds,
or `⨅ A ≥ 0, windowThreshold A = (W₀ : EReal)` for a finite `W₀ > 0` admitting a unit-norm critical
half-line ground state. -/
theorem riemannHypothesis_or_exists_criticalHalfLineGroundState :
    RiemannHypothesis ∨
      ∃ (W₀ : ℝ) (F : ℝ → ℝ), 0 < W₀ ∧
        (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal) ∧
        IsCriticalHalfLineGroundState W₀ F := by
  rcases Classical.em RiemannHypothesis with hRH | hnotRH
  · exact Or.inl hRH
  · right
    have hpos_thr : (0 : EReal) < highConductorCriticalThreshold :=
      criticalPositivityThreshold_pos.trans_le criticalPositivityThreshold_le_highConductorCriticalThreshold
    have hne_top : highConductorCriticalThreshold ≠ ⊤ :=
      mt highConductorCriticalThreshold_eq_top_iff_riemannHypothesis.mp hnotRH
    have hne_bot : highConductorCriticalThreshold ≠ ⊥ := (lt_trans EReal.bot_lt_zero hpos_thr).ne'
    lift highConductorCriticalThreshold to ℝ using ⟨hne_top, hne_bot⟩ with W₀ hW₀_eq
    have hW₀_pos : 0 < W₀ := EReal.coe_pos.mp hpos_thr
    have hW_inf : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal) := by
      rw [← highConductorCriticalThreshold_eq_iInf_windowThreshold, ← hW₀_eq]
    obtain ⟨R₀, hR₀, hpos_R₀⟩ := exists_pos_eventuallyCriticalPosDef
    obtain ⟨c_W, hc_W, hbridge_gen⟩ := eventually_complement_collar_weilQuad_bridge
    let Rmax : ℝ := W₀ + 1
    have hRmax_pos : 0 < Rmax := by dsimp only [Rmax]; positivity
    obtain ⟨B_far, hB_far, hbridge_ev⟩ := hbridge_gen hRmax_pos
    let R_k : ℕ → ℝ := fun k => W₀ + 1 / ((k : ℝ) + 1)
    have hnot_pos : ∀ k : ℕ, ¬ EventuallyHighConductorPosDef (R_k k) := by
      intro k hpos_k
      have hle : ((R_k k : ℝ) : EReal) ≤ highConductorCriticalThreshold :=
        le_sSup ⟨R_k k, ⟨by dsimp only [R_k]; positivity, hpos_k⟩, rfl⟩
      rw [← hW₀_eq, EReal.coe_le_coe_iff] at hle
      have hk : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      dsimp only [R_k] at hle
      linarith only [hle, hk]
    let BadAt (k N : ℕ) : Prop :=
      ∃ (c : ℝ) (z : EuclideanSpace ℝ (PrimeHorizonIndex N)),
        1 ≤ c ∧ c ^ 8 ≤ R_k k * Real.log (N : ℝ) ∧
          z ∈ (conductorSubspace ⌊Real.log (N : ℝ) ^ (13 / 32 : ℝ)⌋₊ N)ᗮ ∧
          z ≠ 0 ∧ completeWeilEnergy tiltedUnitSpline c N z ≤ 0
    have hfreq_bad : ∀ k : ℕ, ∃ᶠ N : ℕ in atTop, BadAt k N := by
      intro k
      have hn := hnot_pos k
      rw [EventuallyHighConductorPosDef, Filter.not_eventually] at hn
      refine hn.mono fun N hN => ?_
      push Not at hN
      obtain ⟨c, hc1, hc8, z, hz, hzne, hle⟩ := hN
      exact ⟨c, z, hc1, hc8, hz, hzne, hle⟩
    let GoodAt (k N : ℕ) : Prop :=
      3 ≤ N ∧ ((k : ℝ) + 1) ≤ (N : ℝ) ∧
        ((k : ℝ) + 1) * (Rmax + 1) * Real.log (N : ℝ) ≤ (N : ℝ) ∧
        (∀ {c : ℝ}, 1 ≤ c → c ^ 8 ≤ R₀ * Real.log (N : ℝ) →
          ∀ {z : EuclideanSpace ℝ (PrimeHorizonIndex N)}, z ≠ 0 →
            0 < completeWeilEnergy tiltedUnitSpline c N z) ∧
        (∀ {c : ℝ}, 1 ≤ c → c ^ 8 ≤ Rmax * Real.log (N : ℝ) →
          ∀ {z : EuclideanSpace ℝ (PrimeHorizonIndex N)},
            z ∈ (conductorSubspace ⌊Real.log (N : ℝ) ^ (13 / 32 : ℝ)⌋₊ N)ᗮ →
            completeWeilEnergy tiltedUnitSpline c N z ≤ 0 →
            ∃ w : EuclideanSpace ℝ (PrimeHorizonIndex N),
              w ∈ (conductorSubspace (subexpCutoff N) N)ᗮ ∧
              let U_w := normalizedCentredAtomicTest tiltedUnitSpline
                (atomicTailCoefficients (N / linearDefectCutoff c) (primeHorizonExtension w)) c N
              (tiltedSplineSpectralFloorConstant + 2) * ‖z‖ ^ 2 ≤
                  (c * B_far) * (∫ u, U_w u ^ 2) ∧
                (∫ u, U_w u ^ 2 * Real.exp (-(8 * u))) ≤
                  (Rmax * B_far / c_W) * (∫ u, U_w u ^ 2) ∧
                levyEnergy U_w ≤
                  (4 * (∫ u, tiltedUnitSpline u ^ 2) * B_far) * (∫ u, U_w u ^ 2) ∧
                weilQuad U_w ≤ (1 / ((k : ℝ) + 1)) * ∫ u, U_w u ^ 2)
    have hLN_zero : Tendsto (fun t : ℝ => Real.log t / t) atTop (𝓝 0) := by
      simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    have hgood_ev : ∀ k : ℕ, ∀ᶠ N : ℕ in atTop, GoodAt k N := by
      intro k
      have hK_pos : 0 < ((k : ℝ) + 1) * (Rmax + 1) := by dsimp only [Rmax]; positivity
      have hev_log := (hLN_zero.comp tendsto_natCast_atTop_atTop).eventually
        (gt_mem_nhds (inv_pos.mpr hK_pos))
      filter_upwards [eventually_ge_atTop (max 3 (k + 1)), hev_log, hpos_R₀,
        hbridge_ev (by positivity : (0 : ℝ) < 1 / ((k : ℝ) + 1))] with N hN_ge hlt_log hR₀N hbrN
      have hN3 : 3 ≤ N := (le_max_left _ _).trans hN_ge
      have hkN : (k : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast (le_max_right 3 (k + 1)).trans hN_ge
      have hN0 : (0 : ℝ) < N := by positivity
      dsimp only [Function.comp_def] at hlt_log
      have hlog_le : ((k : ℝ) + 1) * (Rmax + 1) * Real.log (N : ℝ) ≤ (N : ℝ) := by
        have hm := (div_lt_iff₀ hN0).mp hlt_log
        have hm2 := mul_lt_mul_of_pos_left hm hK_pos
        have hid : ((k : ℝ) + 1) * (Rmax + 1) * ((((k : ℝ) + 1) * (Rmax + 1))⁻¹ * (N : ℝ)) =
            (N : ℝ) := by field_simp [hK_pos.ne']
        linarith only [hm2, hid]
      exact ⟨hN3, hkN, hlog_le, hR₀N, hbrN⟩
    have hex_step : ∀ k M : ℕ, ∃ N : ℕ, M ≤ N ∧ GoodAt k N ∧ BadAt k N := fun k M => by
      obtain ⟨N, hbad, hMN, hgk⟩ :=
        ((hfreq_bad k).and_eventually ((eventually_ge_atTop M).and (hgood_ev k))).exists
      exact ⟨N, hMN, hgk, hbad⟩
    let N_seq : ℕ → ℕ := fun k =>
      Nat.recOn k (Classical.choose (hex_step 0 3))
        (fun k' prev => Classical.choose (hex_step (k' + 1) (prev + 1)))
    have hN_step : ∀ k : ℕ, GoodAt k (N_seq k) ∧ BadAt k (N_seq k) := by
      intro k
      cases k with
      | zero =>
        have hs := Classical.choose_spec (hex_step 0 3)
        exact ⟨hs.2.1, hs.2.2⟩
      | succ k' =>
        have hs := Classical.choose_spec (hex_step (k' + 1) (N_seq k' + 1))
        exact ⟨hs.2.1, hs.2.2⟩
    have hN_strict : StrictMono N_seq :=
      strictMono_nat_of_lt_succ fun k =>
        Nat.lt_of_succ_le (Classical.choose_spec (hex_step (k + 1) (N_seq k + 1))).1
    choose c_seq z_seq hz_spec using fun k => (hN_step k).2
    have hN3_seq : ∀ k, 3 ≤ N_seq k := fun k => (hN_step k).1.1
    have hL_pos : ∀ k, 0 < Real.log (Nat.cast (N_seq k)) := fun k =>
      Real.log_pos (Nat.one_lt_cast.mpr (by have := hN3_seq k; omega))
    have hRk_le_Rmax : ∀ k : ℕ, R_k k ≤ Rmax := fun k => by
      have h1 : (1 : ℝ) / ((k : ℝ) + 1) ≤ 1 :=
        div_le_one_of_le₀ (by linarith only [Nat.cast_nonneg (α := ℝ) k]) (by positivity)
      dsimp only [R_k, Rmax]
      linarith only [h1]
    have hc8_Rmax : ∀ k, c_seq k ^ 8 ≤ Rmax * Real.log (Nat.cast (N_seq k)) := fun k =>
      (hz_spec k).2.1.trans (mul_le_mul_of_nonneg_right (hRk_le_Rmax k) (hL_pos k).le)
    have hratio_Rk : ∀ k, c_seq k ^ 8 / Real.log (Nat.cast (N_seq k)) ≤ R_k k := fun k =>
      (div_le_iff₀ (hL_pos k)).mpr (hz_spec k).2.1
    have hratio_mem : ∀ k, c_seq k ^ 8 / Real.log (Nat.cast (N_seq k)) ∈ Set.Icc R₀ Rmax := by
      intro k
      refine ⟨?_, (hratio_Rk k).trans (hRk_le_Rmax k)⟩
      by_contra hlt_R₀
      push Not at hlt_R₀
      have hc8_R₀ : c_seq k ^ 8 ≤ R₀ * Real.log (Nat.cast (N_seq k)) :=
        ((div_lt_iff₀ (hL_pos k)).mp hlt_R₀).le
      have hpos := (hN_step k).1.2.2.2.1 (hz_spec k).1 hc8_R₀ (hz_spec k).2.2.2.1
      linarith only [hpos, (hz_spec k).2.2.2.2]
    have hc_width : ∀ k, c_seq k / Nat.cast (N_seq k) ≤ 1 / ((k : ℝ) + 1) := by
      intro k
      obtain ⟨hN3, _, hlog_le, _, _⟩ := (hN_step k).1
      have hN0 : (0 : ℝ) < Nat.cast (N_seq k) := Nat.cast_pos.mpr (by omega)
      have hc_le : ((k : ℝ) + 1) * c_seq k ≤ Nat.cast (N_seq k) := by
        by_cases hcL : c_seq k ≤ (Rmax + 1) * Real.log (Nat.cast (N_seq k))
        · calc ((k : ℝ) + 1) * c_seq k
              ≤ ((k : ℝ) + 1) * ((Rmax + 1) * Real.log (Nat.cast (N_seq k))) :=
                mul_le_mul_of_nonneg_left hcL (by positivity)
            _ = ((k : ℝ) + 1) * (Rmax + 1) * Real.log (Nat.cast (N_seq k)) := (mul_assoc _ _ _).symm
            _ ≤ Nat.cast (N_seq k) := hlog_le
        · push Not at hcL
          have hc8_gt : (Rmax + 1) * Real.log (Nat.cast (N_seq k)) < c_seq k ^ 8 :=
            hcL.trans_le (le_self_pow₀ (hz_spec k).1 (by norm_num))
          linarith only [hc8_gt, hc8_Rmax k, hL_pos k]
      rw [div_le_div_iff₀ hN0 (by positivity)]
      linarith only [hc_le]
    have hbr_k : ∀ k : ℕ, ∃ w : EuclideanSpace ℝ (PrimeHorizonIndex (N_seq k)),
        let U_w := normalizedCentredAtomicTest tiltedUnitSpline
          (atomicTailCoefficients (N_seq k / linearDefectCutoff (c_seq k)) (primeHorizonExtension w))
          (c_seq k) (N_seq k)
        (tiltedSplineSpectralFloorConstant + 2) * ‖z_seq k‖ ^ 2 ≤
            (c_seq k * B_far) * (∫ u, U_w u ^ 2) ∧
          (∫ u, U_w u ^ 2 * Real.exp (-(8 * u))) ≤
            (Rmax * B_far / c_W) * (∫ u, U_w u ^ 2) ∧
          weilQuad U_w ≤ (1 / ((k : ℝ) + 1)) * ∫ u, U_w u ^ 2 := by
      intro k
      obtain ⟨hc1, _, hz_orth, _, hle0⟩ := hz_spec k
      obtain ⟨w, _, hb1, hb2, _, hb4⟩ := (hN_step k).1.2.2.2.2 hc1 (hc8_Rmax k) hz_orth hle0
      exact ⟨w, hb1, hb2, hb4⟩
    let w_seq : ∀ k : ℕ, EuclideanSpace ℝ (PrimeHorizonIndex (N_seq k)) :=
      fun k => Classical.choose (hbr_k k)
    let y_raw : ℕ → ℕ → ℝ := fun k =>
      atomicTailCoefficients (N_seq k / linearDefectCutoff (c_seq k))
        (primeHorizonExtension (w_seq k))
    let U_raw : ℕ → ℝ → ℝ := fun k =>
      normalizedCentredAtomicTest tiltedUnitSpline (y_raw k) (c_seq k) (N_seq k)
    have hU_raw_pos : ∀ k, 0 < ∫ u, U_raw k u ^ 2 := by
      intro k
      obtain ⟨hb1, _, _⟩ := Classical.choose_spec (hbr_k k)
      obtain ⟨hc1, _, _, hzne, _⟩ := hz_spec k
      have hzl : 0 < (tiltedSplineSpectralFloorConstant + 2) * ‖z_seq k‖ ^ 2 :=
        mul_pos (by have := tiltedSplineSpectralFloorConstant_pos; positivity)
          (sq_pos_of_pos (norm_pos_iff.mpr hzne))
      have hcf : 0 < c_seq k * B_far := mul_pos (zero_lt_one.trans_le hc1) hB_far
      by_contra hle
      push Not at hle
      have hle' : (c_seq k * B_far) * (∫ u, U_raw k u ^ 2) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hcf.le hle
      linarith only [hzl, hb1, hle']
    let ν : ℕ → ℝ := fun k => Real.sqrt (∫ u, U_raw k u ^ 2)
    have hν_pos : ∀ k, 0 < ν k := fun k => Real.sqrt_pos.mpr (hU_raw_pos k)
    have hν_sq : ∀ k, ν k ^ 2 = ∫ u, U_raw k u ^ 2 := fun k => Real.sq_sqrt (hU_raw_pos k).le
    let y_norm : ℕ → ℕ → ℝ := fun k n => (ν k)⁻¹ * y_raw k n
    let V : ℕ → ℝ → ℝ := fun k =>
      normalizedCentredAtomicTest tiltedUnitSpline (y_norm k) (c_seq k) (N_seq k)
    have hV_eq : ∀ k, V k = fun u => (ν k)⁻¹ * U_raw k u := fun k =>
      normalizedCentredAtomicTest_const_mul (ν k)⁻¹ (y_raw k) (c_seq k) (N_seq k)
    have hUd : ∀ k, ContDiff ℝ 2 (U_raw k) := fun k =>
      contDiff_const.mul (contDiff_centredAtomicTest contDiff_tiltedUnitSpline _ _ _)
    have hUc : ∀ k, HasCompactSupport (U_raw k) := fun k =>
      (hasCompactSupport_centredAtomicTest tiltedUnitSpline_eq_zero (y_raw k)
        (zero_lt_one.trans_le (hz_spec k).1) (by have := hN3_seq k; omega)).mul_left
    have hV_norm : ∀ k, (∫ u, V k u ^ 2) = 1 := by
      intro k
      rw [hV_eq k]
      simp_rw [mul_pow]
      rw [integral_const_mul, inv_pow, ← hν_sq k, inv_mul_cancel₀ (pow_ne_zero 2 (hν_pos k).ne')]
    set M₈ : ℝ := Rmax * B_far / c_W
    have hM₈_pos : 0 < M₈ := by dsimp only [M₈, Rmax]; positivity
    have hV_M₈ : ∀ k, (∫ u, V k u ^ 2 * Real.exp (-(8 * u))) ≤ M₈ := by
      intro k
      obtain ⟨_, hb2, _⟩ := Classical.choose_spec (hbr_k k)
      have heq : (∫ u, V k u ^ 2 * Real.exp (-(8 * u))) =
          (ν k)⁻¹ ^ 2 * ∫ u, U_raw k u ^ 2 * Real.exp (-(8 * u)) := by
        rw [hV_eq k, ← integral_const_mul]
        exact integral_congr_ae (Eventually.of_forall fun u => by dsimp only; ring)
      rw [heq]
      have hm := mul_le_mul_of_nonneg_left hb2 (sq_nonneg (ν k)⁻¹)
      have hid : (ν k)⁻¹ ^ 2 * (M₈ * ∫ u, U_raw k u ^ 2) = M₈ := by
        have hne : (∫ u, U_raw k u ^ 2) ≠ 0 := (hU_raw_pos k).ne'
        rw [inv_pow, hν_sq k, mul_comm M₈, inv_mul_cancel_left₀ hne]
      linarith only [hm, hid]
    have hV_wq : ∀ k : ℕ, weilQuad (V k) ≤ 1 / ((k : ℝ) + 1) := by
      intro k
      obtain ⟨_, _, hb3⟩ := Classical.choose_spec (hbr_k k)
      rw [hV_eq k, weilQuad_const_mul (hUd k) (hUc k) (ν k)⁻¹]
      have hm := mul_le_mul_of_nonneg_left hb3 (sq_nonneg (ν k)⁻¹)
      have hid : (ν k)⁻¹ ^ 2 * ((1 / ((k : ℝ) + 1)) * ∫ u, U_raw k u ^ 2) =
          1 / ((k : ℝ) + 1) := by
        have hne : (∫ u, U_raw k u ^ 2) ≠ 0 := (hU_raw_pos k).ne'
        rw [inv_pow, hν_sq k, mul_comm (1 / ((k : ℝ) + 1)), inv_mul_cancel_left₀ hne]
      linarith only [hm, hid]
    obtain ⟨R_lim, hR_lim_mem, φ₁, hφ₁_mono, hφ₁_lim⟩ :=
      isCompact_Icc.isSeqCompact hratio_mem
    have hR_lim_pos : 0 < R_lim := hR₀.trans_le hR_lim_mem.1
    have hR_lim_le : R_lim ≤ W₀ := by
      have hRk_lim : Tendsto (fun j : ℕ => R_k (φ₁ j)) atTop (𝓝 W₀) := by
        have hz := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hφ₁_mono.tendsto_atTop
        simpa only [R_k, Function.comp_def, add_zero] using (tendsto_const_nhds (x := W₀)).add hz
      exact le_of_tendsto_of_tendsto hφ₁_lim hRk_lim
        (Eventually.of_forall fun j => hratio_Rk (φ₁ j))
    have hindex : ∀ j : ℕ, j ≤ φ₁ j := hφ₁_mono.id_le
    have hinv : ∀ j : ℕ, (1 : ℝ) / ((φ₁ j : ℝ) + 1) ≤ 1 / ((j : ℝ) + 1) := fun j =>
      div_le_div_of_nonneg_left zero_le_one (by positivity)
        (by exact_mod_cast Nat.add_le_add_right (hindex j) 1)
    let V₁ : ℕ → ℝ → ℝ := fun j => V (φ₁ j)
    have hV₁d : ∀ j, ContDiff ℝ 2 (V₁ j) := fun j =>
      contDiff_const.mul (contDiff_centredAtomicTest contDiff_tiltedUnitSpline _ _ _)
    have hV₁c : ∀ j, HasCompactSupport (V₁ j) := fun j =>
      (hasCompactSupport_centredAtomicTest tiltedUnitSpline_eq_zero (y_norm (φ₁ j))
        (zero_lt_one.trans_le (hz_spec (φ₁ j)).1)
        (by have := hN3_seq (φ₁ j); omega)).mul_left
    have hV₁_supp : ∀ (j : ℕ) (u : ℝ), 1 / ((j : ℝ) + 1) < u → V₁ j u = 0 := by
      intro j u hu
      have hc0 : 0 < c_seq (φ₁ j) := zero_lt_one.trans_le (hz_spec (φ₁ j)).1
      have hN1 : 1 ≤ N_seq (φ₁ j) := by have := hN3_seq (φ₁ j); omega
      have hN0 : (0 : ℝ) < Nat.cast (N_seq (φ₁ j)) :=
        (Nat.cast_pos (α := ℝ)).mpr (Nat.lt_of_lt_of_le Nat.zero_lt_one hN1)
      have hw : 0 < c_seq (φ₁ j) / Nat.cast (N_seq (φ₁ j)) := div_pos hc0 hN0
      have hsupp_atom := tiltedUnitSpline_atom_support hw
      have hu' : c_seq (φ₁ j) / Nat.cast (N_seq (φ₁ j)) < u :=
        ((hc_width (φ₁ j)).trans (hinv j)).trans_lt hu
      simp only [V₁, V, normalizedCentredAtomicTest, centredAtomicTest,
        ArithmeticElectrostatics.atomicTest]
      rw [mul_eq_zero]
      right
      refine Finset.sum_eq_zero fun n hn => ?_
      obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hn
      have hn0 : (0 : ℝ) < Nat.cast n :=
        (Nat.cast_pos (α := ℝ)).mpr (Nat.lt_of_lt_of_le Nat.zero_lt_one hn1)
      have hlog : Real.log (Nat.cast n) ≤ Real.log (Nat.cast (N_seq (φ₁ j))) :=
        Real.log_le_log hn0 (Nat.cast_le.mpr hnN)
      rw [hsupp_atom _ fun hmem => by linarith only [hmem.2, hu', hlog], mul_zero]
    have hV₁_wq1 : ∀ j, weilQuad (V₁ j) ≤ 1 := fun j =>
      (hV_wq (φ₁ j)).trans ((hinv j).trans
        (div_le_one_of_le₀ (by linarith only [Nat.cast_nonneg (α := ℝ) j]) (by positivity)))
    obtain ⟨F, s, hs_mono, hFm, hFi, hF2, _, hF8, _, hFzero, _, hL1, hmass_lim⟩ :=
      exists_strong_negative_limit_of_bounded_weilQuad hV₁d hV₁c
        (fun j => (hV_norm (φ₁ j)).le) hM₈_pos.le (fun j => hV_M₈ (φ₁ j)) hV₁_supp hV₁_wq1
    have hF_norm1 : (∫ u, F u ^ 2) = 1 :=
      tendsto_nhds_unique hmass_lim
        (by simpa only [V₁, hV_norm] using (tendsto_const_nhds (x := (1 : ℝ))))
    have hgamma_W₀ : ∀ T : ℝ, Real.exp factorialSpanGammaOffset ≤ T →
        truncatedWeilForm F T +
          criticalAliasCoefficient W₀ * (∫ u in Iio 0, F u ^ 2 * Real.exp (-(8 * u))) ≤ 0 := by
      intro T hT
      have hgamma_Rlim : truncatedWeilForm F T +
          criticalAliasCoefficient R_lim * (∫ u in Iio 0, F u ^ 2 * Real.exp (-(8 * u))) ≤ 0 := by
        by_contra hpos_sum
        push Not at hpos_sum
        let b : ℝ := (truncatedWeilForm F T +
          criticalAliasCoefficient R_lim * (∫ u in Iio 0, F u ^ 2 * Real.exp (-(8 * u)))) / 2
        have hb_pos : 0 < b := half_pos hpos_sum
        have hb_lt : b < truncatedWeilForm F T +
            criticalAliasCoefficient R_lim * (∫ u in Iio 0, F u ^ 2 * Real.exp (-(8 * u))) :=
          half_lt_self hpos_sum
        have hev := eventually_lt_weilQuad_of_subsequence_L1_limit
          ((hN_strict.comp hφ₁_mono).comp hs_mono)
          (fun j => (hz_spec (φ₁ (s j))).1) hR_lim_pos
          (hφ₁_lim.comp hs_mono.tendsto_atTop)
          (fun j => y_norm (φ₁ (s j)))
          (fun j => (hV_norm (φ₁ (s j))).le) hM₈_pos.le
          (fun j => hV_M₈ (φ₁ (s j))) hFi hL1 hT hb_lt
        have heps : Tendsto (fun j : ℕ => 1 / ((φ₁ (s j) : ℝ) + 1)) atTop (𝓝 0) :=
          tendsto_one_div_add_atTop_nhds_zero_nat.comp (hφ₁_mono.comp hs_mono).tendsto_atTop
        obtain ⟨j, hj_gt, hj_lt⟩ := (hev.and (heps.eventually (gt_mem_nhds hb_pos))).exists
        have hwq_j := hV_wq (φ₁ (s j))
        change b < weilQuad (V (φ₁ (s j))) at hj_gt
        linarith only [hj_gt, hj_lt, hwq_j]
      have halias_le : criticalAliasCoefficient W₀ ≤ criticalAliasCoefficient R_lim := by
        unfold criticalAliasCoefficient
        have hnum : 0 ≤ 7 * (∫ u, tiltedUnitSpline u ^ 2) * tiltedJordanOne := by
          have := tiltedJordanOne_pos
          positivity
        have hI₁sq : 0 < (∫ u, tiltedUnitSpline u) ^ 2 :=
          sq_pos_of_ne_zero integral_tiltedUnitSpline_ne_zero
        exact div_le_div_of_nonneg_left hnum (mul_pos hI₁sq hR_lim_pos)
          (mul_le_mul_of_nonneg_left hR_lim_le hI₁sq.le)
      have hI₈_nn : 0 ≤ ∫ u in Iio 0, F u ^ 2 * Real.exp (-(8 * u)) :=
        setIntegral_nonneg measurableSet_Iio fun _ _ => by positivity
      have hm := mul_le_mul_of_nonneg_right halias_le hI₈_nn
      linarith only [hgamma_Rlim, hm]
    exact ⟨W₀, F, hW₀_pos, hW_inf, hFm, hFi, hF2, hF_norm1, hF8, hFzero, hgamma_W₀⟩

/-- **Quantitative reciprocal shift bound on `polarPaymentCriticalThreshold` from any critical
half-line ground state.** For any `W₀ > 0` and any critical half-line ground state `F` at `W₀`,
putting `S := splineAtom * ∫ F · polarSourceProfile`, `D₀ := criticalPoleWindowCost W₀`, and
`I₈ := ∫_{u<0} F(u)² e^{-8u}`, the polar-payment threshold satisfies
`polarPaymentCriticalThreshold ≤ (1 / W₀ + D₀ S² / (7 J(1) D₀² I₈ + J_bulk(1) S²))⁻¹`. -/
theorem polarPaymentCriticalThreshold_le_of_criticalHalfLineGroundState
    {W₀ : ℝ} (hW₀ : 0 < W₀) {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    let S := splineAtom * ∫ u, F u * polarSourceProfile u
    let D₀ := criticalPoleWindowCost W₀
    let I₈ := ∫ u in Iio 0, F u ^ 2 * Real.exp (-(8 * u))
    polarPaymentCriticalThreshold ≤
      (((1 / W₀ + D₀ * S ^ 2 /
        (7 * tiltedJordanOne * D₀ ^ 2 * I₈ + jordanCoefficient 1 * S ^ 2))⁻¹ : ℝ) : EReal) := by
  rcases hF with ⟨hFm, hFi, hF2, hFnorm, hF8, hFzero, hgamma⟩
  intro S D₀ I₈
  have hD₀ : 0 < D₀ := criticalPoleWindowCost_pos hW₀
  have hI₁ : (∫ u, tiltedUnitSpline u) ≠ 0 := integral_tiltedUnitSpline_ne_zero
  have hI₂ : 0 < ∫ u, tiltedUnitSpline u ^ 2 := integral_tiltedUnitSpline_sq_pos
  have hJ₁ : 0 < tiltedJordanOne := tiltedJordanOne_pos
  have hJb : 0 < jordanCoefficient 1 := jordanCoefficient_pos (by norm_num : (0 : ℕ) < 1)
  have hI₈_ge_one : 1 ≤ I₈ := by
    have heq : (∫ u, F u ^ 2) = ∫ u in Iio 0, F u ^ 2 := by
      rw [← integral_indicator measurableSet_Iio]
      apply integral_congr_ae (Eventually.of_forall fun u => ?_)
      by_cases hu : u < 0
      · rw [Set.indicator_of_mem (show u ∈ Iio (0 : ℝ) from hu)]
      · rw [Set.indicator_of_notMem (show u ∉ Iio (0 : ℝ) from hu)]
        simp only [hFzero u (not_lt.mp hu), zero_pow two_ne_zero]
    rw [← hFnorm, heq]
    exact setIntegral_mono_on hF2.integrableOn hF8.integrableOn measurableSet_Iio fun u hu =>
      le_mul_of_one_le_right (sq_nonneg _)
        (Real.one_le_exp (by have hu0 : u < 0 := hu; linarith only [hu0]))
  have hI₈_pos : 0 < I₈ := zero_lt_one.trans_le hI₈_ge_one
  have hden_pos : 0 < 7 * tiltedJordanOne * D₀ ^ 2 * I₈ + jordanCoefficient 1 * S ^ 2 :=
    add_pos_of_pos_of_nonneg (by positivity) (by positivity)
  let shift : ℝ := D₀ * S ^ 2 /
    (7 * tiltedJordanOne * D₀ ^ 2 * I₈ + jordanCoefficient 1 * S ^ 2)
  have hshift_nn : 0 ≤ shift := div_nonneg (by positivity) hden_pos.le
  let μ : ℝ := 1 / W₀ + shift
  have hμ_pos : 0 < μ := add_pos_of_pos_of_nonneg (one_div_pos.mpr hW₀) hshift_nn
  let Rb : ℝ := μ⁻¹
  have hRb_pos : 0 < Rb := inv_pos.mpr hμ_pos
  let P : ℝ := ∫ u, F u * polarSourceProfile u
  let I₁ : ℝ := ∫ u, tiltedUnitSpline u
  let I₂ : ℝ := ∫ u, tiltedUnitSpline u ^ 2
  let β : ℝ := -(I₁ * P) / (I₂ * D₀)
  have hcharged_Rb : ∀ T : ℝ, Real.exp factorialSpanGammaOffset ≤ T →
      truncatedWeilForm F T + criticalAliasCoefficient Rb * I₈ +
        I₂ * criticalPoleWindowCost Rb * β ^ 2 + 2 * I₁ * β * P ≤ 0 := by
    intro T hT
    have hg := hgamma T hT
    have hcost_diff := criticalPoleWindowCost_sub_eq hRb_pos.ne' hW₀.ne'
    have hRb_inv : 1 / Rb - 1 / W₀ = shift := by
      dsimp only [Rb, μ]
      rw [one_div, inv_inv]
      ring
    have halias_diff : (criticalAliasCoefficient Rb - criticalAliasCoefficient W₀) * I₈ =
        (7 * I₂ * tiltedJordanOne / I₁ ^ 2) * I₈ * shift := by
      unfold criticalAliasCoefficient
      dsimp only [I₁, I₂] at hI₁ ⊢
      have h1 : 7 * I₂ * tiltedJordanOne / (I₁ ^ 2 * Rb) -
          7 * I₂ * tiltedJordanOne / (I₁ ^ 2 * W₀) =
          (7 * I₂ * tiltedJordanOne / I₁ ^ 2) * (1 / Rb - 1 / W₀) := by
        field_simp [hI₁, hRb_pos.ne', hW₀.ne']
      rw [h1, hRb_inv]
      ring
    have hcost_eq : criticalPoleWindowCost Rb = D₀ + jordanCoefficient 1 * shift := by
      dsimp only [D₀]
      rw [hRb_inv] at hcost_diff
      linarith only [hcost_diff]
    have hS_def : S = (I₁ ^ 2 / I₂) * P := by
      dsimp only [S, P, I₁, I₂]
      rfl
    have hcancel : (7 * I₂ * tiltedJordanOne / I₁ ^ 2) * I₈ * shift +
        I₂ * (D₀ + jordanCoefficient 1 * shift) * β ^ 2 + 2 * I₁ * β * P = 0 := by
      dsimp only [shift, β]
      rw [hS_def]
      have hden_scaled : 0 < 7 * tiltedJordanOne * D₀ ^ 2 * I₈ +
          jordanCoefficient 1 * ((I₁ ^ 2 / I₂) * P) ^ 2 := by
        simpa only [← hS_def] using hden_pos
      field_simp [hI₁, hI₂.ne', hD₀.ne', hden_scaled.ne']
      ring
    have hsplit : truncatedWeilForm F T + criticalAliasCoefficient Rb * I₈ +
        I₂ * criticalPoleWindowCost Rb * β ^ 2 + 2 * I₁ * β * P =
        (truncatedWeilForm F T + criticalAliasCoefficient W₀ * I₈) +
        ((criticalAliasCoefficient Rb - criticalAliasCoefficient W₀) * I₈ +
          I₂ * criticalPoleWindowCost Rb * β ^ 2 + 2 * I₁ * β * P) := by ring
    rw [hsplit, halias_diff, hcost_eq, hcancel, add_zero]
    exact hg
  refine sSup_le ?_
  rintro _ ⟨S_pay, ⟨hSpay, hpay⟩, rfl⟩
  refine EReal.coe_le_coe_iff.mpr ?_
  by_contra hgt
  push Not at hgt
  exact no_charged_limit_profile_below_polarPayment hRb_pos hgt hpay hFm hFi hF2 hFnorm.le
    hF8 hFzero (by rw [hFnorm]; positivity) hcharged_Rb

/-- Any critical half-line ground state at `W₀ > 0` with nonzero polar pairing forces the strict
separation `polarPaymentCriticalThreshold < W₀`. -/
theorem polarPaymentCriticalThreshold_lt_of_charged_criticalHalfLineGroundState
    {W₀ : ℝ} (hW₀ : 0 < W₀) {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F)
    (hP : (∫ u, F u * polarSourceProfile u) ≠ 0) :
    polarPaymentCriticalThreshold < (W₀ : EReal) := by
  have hle := polarPaymentCriticalThreshold_le_of_criticalHalfLineGroundState hW₀ hF
  dsimp only at hle
  let S : ℝ := splineAtom * ∫ u, F u * polarSourceProfile u
  let D₀ : ℝ := criticalPoleWindowCost W₀
  let I₈ : ℝ := ∫ u in Iio 0, F u ^ 2 * Real.exp (-(8 * u))
  have hS_ne : S ≠ 0 := mul_ne_zero splineAtom_pos.ne' hP
  have hS_sq : 0 < S ^ 2 := sq_pos_of_ne_zero hS_ne
  have hD₀ : 0 < D₀ := criticalPoleWindowCost_pos hW₀
  have hI₈_nn : 0 ≤ I₈ := setIntegral_nonneg measurableSet_Iio fun _ _ => by positivity
  have hJb : 0 < jordanCoefficient 1 := jordanCoefficient_pos (by norm_num : (0 : ℕ) < 1)
  have hJ₁ : 0 < tiltedJordanOne := tiltedJordanOne_pos
  have hden_pos : 0 < 7 * tiltedJordanOne * D₀ ^ 2 * I₈ + jordanCoefficient 1 * S ^ 2 :=
    add_pos_of_nonneg_of_pos (by positivity) (mul_pos hJb hS_sq)
  have hshift_pos : 0 < D₀ * S ^ 2 /
      (7 * tiltedJordanOne * D₀ ^ 2 * I₈ + jordanCoefficient 1 * S ^ 2) :=
    div_pos (mul_pos hD₀ hS_sq) hden_pos
  have hinv_lt : (1 / W₀ + D₀ * S ^ 2 /
      (7 * tiltedJordanOne * D₀ ^ 2 * I₈ + jordanCoefficient 1 * S ^ 2))⁻¹ < W₀ := by
    have h1 : 0 < 1 / W₀ := one_div_pos.mpr hW₀
    have hlt : (1 / W₀ + D₀ * S ^ 2 /
        (7 * tiltedJordanOne * D₀ ^ 2 * I₈ + jordanCoefficient 1 * S ^ 2))⁻¹ < (1 / W₀)⁻¹ :=
      (inv_lt_inv₀ (by linarith only [h1, hshift_pos]) h1).mpr (by linarith only [hshift_pos])
    rw [one_div, inv_inv] at hlt
    simpa only [one_div] using hlt
  exact hle.trans_lt (EReal.coe_lt_coe_iff.mpr hinv_lt)

/-- **Unconditional three-way classification of `polarPaymentCriticalThreshold` against
`W = ⨅ A ≥ 0, windowThreshold A`.** Either:
1. `RiemannHypothesis` holds (`polarPaymentCriticalThreshold = W = ⊤`), or
2. `¬ RiemannHypothesis` and `polarPaymentCriticalThreshold < W`, or
3. `¬ RiemannHypothesis`, `polarPaymentCriticalThreshold = W = (W₀ : EReal)` (`0 < W₀`), a
   critical half-line ground state at `W₀` exists, and every critical half-line ground state `F`
   at `W₀` is strictly orthogonal to `polarSourceProfile` (`∫ F · polarSourceProfile = 0`). -/
theorem polarPaymentCriticalThreshold_windowThreshold_classification :
    let W := ⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A
    (RiemannHypothesis ∧ polarPaymentCriticalThreshold = ⊤ ∧ W = ⊤) ∨
      (¬ RiemannHypothesis ∧ polarPaymentCriticalThreshold < W) ∨
      (¬ RiemannHypothesis ∧ ∃ W₀ : ℝ, 0 < W₀ ∧ polarPaymentCriticalThreshold = (W₀ : EReal) ∧
        W = (W₀ : EReal) ∧ (∃ F : ℝ → ℝ, IsCriticalHalfLineGroundState W₀ F) ∧
        ∀ F : ℝ → ℝ, IsCriticalHalfLineGroundState W₀ F →
          (∫ u, F u * polarSourceProfile u) = 0) := by
  intro W
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with hRH | ⟨W₀, F₀, hW₀, hW, hF₀⟩
  · refine Or.inl ⟨hRH, polarPaymentCriticalThreshold_eq_top_iff_riemannHypothesis.mpr hRH, ?_⟩
    dsimp only [W]
    rw [← highConductorCriticalThreshold_eq_iInf_windowThreshold]
    exact highConductorCriticalThreshold_eq_top_iff_riemannHypothesis.mpr hRH
  · have hnotRH : ¬ RiemannHypothesis := by
      intro hRH
      have htop : W = ⊤ := by
        dsimp only [W]
        rw [← highConductorCriticalThreshold_eq_iInf_windowThreshold]
        exact highConductorCriticalThreshold_eq_top_iff_riemannHypothesis.mpr hRH
      dsimp only [W] at htop
      rw [hW] at htop
      exact EReal.coe_ne_top W₀ htop
    have hle : polarPaymentCriticalThreshold ≤ W := polarPaymentCriticalThreshold_le_iInf_windowThreshold
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact Or.inr (Or.inl ⟨hnotRH, hlt⟩)
    · refine Or.inr (Or.inr ⟨hnotRH, W₀, hW₀, heq.trans hW, hW, ⟨F₀, hF₀⟩, ?_⟩)
      intro F hF
      by_contra hP
      have hlt := polarPaymentCriticalThreshold_lt_of_charged_criticalHalfLineGroundState hW₀ hF hP
      rw [heq] at hlt
      dsimp only [W] at hlt
      rw [hW] at hlt
      exact lt_irrefl _ hlt

#print axioms polarPaymentCriticalThreshold_eq_halfLinePolarThreshold
#print axioms criticalPositivityThreshold_le_halfLinePolarThreshold
#print axioms polarPaymentCriticalThreshold_eq_iInf_windowThreshold_iff_halfLinePolarPositive
#print axioms riemannHypothesis_or_exists_criticalHalfLineGroundState
#print axioms polarPaymentCriticalThreshold_le_of_criticalHalfLineGroundState
#print axioms polarPaymentCriticalThreshold_lt_of_charged_criticalHalfLineGroundState
#print axioms polarPaymentCriticalThreshold_windowThreshold_classification

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
