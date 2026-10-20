import GaloisForLFunctions.SquareRootThreshold.OneParameterLagFamilyMeasuresTheAbscissa
import GaloisForLFunctions.SquareRootThreshold.LagFamilyMeetsTheCrystalAtTheThreshold
import GaloisForLFunctions.ArithmeticCriticalityTheory.ExplicitSmallApertureCCMGroundEnergyFloor
import GaloisForLFunctions.ArithmeticCriticalityTheory.WindowGaugeLogarithmicGroundEnergyFloor
import GaloisForLFunctions.ArithmeticCriticalityTheory.RestrictedWeilGroundEnergyCriticalAtInfinity
import GaloisForLFunctions.RHTower.ZerosApproachLineAttainment
import GaloisForLFunctions.RHTower.CCMZetaWeilSmoothIdentity

/-!
# Ground-Energy Abscissa Law and Geometric Lag-Grid Attainment Bridge

This module connects the restricted Weil ground energy `ccmRestrictedWeilGroundEnergy A` (`μ(A)`)
of `ArithmeticCriticalityTheory`, the one-parameter difference two-bump dyadic prime window family
`P_{w,v}` of `SquareRootThreshold`, and the high-height attainment hierarchy (`ZerosApproachLine`,
`EventualHadamardPositivity`, `AttainedTop`) of `RHTower`:

1. **Closed-aperture Rayleigh–Prime-Window Bridge** (`ccmRestrictedWeilGroundEnergy_mul_integral_norm_sq_le_re_W`,
   `two_mul_ccmRestrictedWeilGroundEnergy_le_re_lagPrimeWindowRHS`):
   Using Suzuki right-aperture continuity (`tendsto_ccmRestrictedWeilGroundEnergy_suzukiRightAperture`),
   every smooth test `g` supported in the closed interval `[-A, A]` satisfies
   `μ(A) ∫ ‖g‖² ≤ Re W_ζ(g, g)`. Evaluating on the centered difference two-bump test
   `f_{w,v}(t) = κ_w(t + v/2) - κ_w(t - v/2)` at the exact aperture `A = v/2 + w` gives, for
   disjoint bumps `2w < v` with `2w < log 2`,
   `2 (∫ ‖κ_w‖²) μ(v/2 + w) ≤ Re W_ζ(f_{w,v}, f_{w,v}) = Re P_{w,v}`.
   This transfers the explicit small-aperture Markov floor `μ(A) ≥ 1/30` (`A ≤ 21/200`) and the
   logarithmic window-gauge floor `μ(A) ≥ windowFloor(R)` (`2R < log 2`) directly to the dyadic
   prime window functional `P_{w,v}` (`one_fifteenth_mul_le_re_lagPrimeWindowRHS_of_le`,
   `two_mul_windowFloor_le_re_lagPrimeWindowRHS_of_lt`).

2. **Unconditional Sharp `2σ`-Abscissa Law for `μ(A)`**
   (`re_le_of_ccmRestrictedWeilGroundEnergy_ge_neg_exp`,
   `abs_re_sub_half_le_of_ccmRestrictedWeilGroundEnergy_ge_neg_exp`,
   `abs_im_xiSpectralPoint_le_of_ccmRestrictedWeilGroundEnergy_ge_neg_exp`):
   Because `f_{w,v}` is centered with support radius `v/2 + w` and constant `L²` norm `2 ∫ ‖κ_w‖² > 0`
   for `v > 2w`, a ground-energy lower bound `μ(A) ≥ -C e^{2σA}` (`A ≥ A₀`, `σ ≥ 0`) yields
   `Re W_ζ(f_{w,v}, f_{w,v}) ≥ -C' e^{σv}` for all large `v`, which via
   `re_le_iff_lag_twoBump_ge_neg_exp` **unconditionally** forces `|Re ρ - 1/2| ≤ σ` for every
   nontrivial zero `ρ` of `ζ`—requiring neither `ZerosApproachLine` nor `AttainedTopExcess` and
   eliminating the factor-of-2 exponent loss of uncentered test sequences.

3. **Geometric Lag-Grid Abscissa Law and `ZerosApproachLine` Split**
   (`exists_re_gt_of_grid_lag_ge_neg_exp`, `re_le_iff_topAttained_above_and_grid_lag_ge_neg_exp`,
   `zeta_re_le_iff_grid_primeWindow_ge_neg_exp_of_zerosApproachLine`,
   `riemannHypothesis_iff_zerosApproachLine_and_grid_primeWindow_nonneg`,
   `riemannHypothesis_iff_zerosApproachLine_and_grid_ccmRestrictedWeilGroundEnergy_bddBelow`):
   Generalizing `exists_re_gt_of_grid_lag_ge` to exponential grid lower bounds `-C e^{σ k ℓ}`,
   any zero above `1/2 + σ` is strictly exceeded in real part by another zero whenever
   `Re P_{w, kℓ} ≥ -C e^{σ k ℓ}` along a single non-resonant geometric grid `X_k = e^{kℓ}`.
   Paired with `ZerosApproachLine` (or `EventualHadamardPositivity`), this characterizes every
   quasi-RH half-plane `Re ρ ≤ 1/2 + σ`—and at `σ = 0`, `RiemannHypothesis` itself—by a single
   geometric progression of dyadic prime windows or a single arithmetic progression of apertures
   `A_k = kℓ/2 + w` of `μ(A)`.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate
open Zeta23 _root_.RHTower
open GaloisForLFunctions.ArithmeticCriticalityTheory

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

/-! ### Generic widths, non-resonant steps, and zero-carrier bridges -/

/-- Every nonempty open interval of reals contains a point outside any given countable set. -/
theorem exists_mem_Ioo_notMem_of_countable {a b : ℝ} (hab : a < b) {E : Set ℝ}
    (hE : E.Countable) : ∃ x ∈ Ioo a b, x ∉ E := by
  by_contra h
  push Not at h
  have h0 : volume (Ioo a b) = 0 := measure_mono_null h (hE.measure_zero volume)
  rw [Real.volume_Ioo] at h0
  have : b - a ≤ 0 := ENNReal.ofReal_eq_zero.mp h0
  linarith

/-- Every zero configuration admits a width `w ∈ (0, ½ log 2)` whose bump transform vanishes at no
off-line zero ordinate `γ_ρ`. -/
theorem exists_good_width (Z : ZeroConfig) :
    ∃ w : ℝ, 0 < w ∧ 2 * w < Real.log 2 ∧
      ∀ ρ ∈ Z.carrier, ρ.re ≠ 1 / 2 → paperFT (scaledBump w) (gammaOf ρ) ≠ 0 := by
  obtain ⟨w, ⟨hw0, hw2⟩, hwE⟩ := exists_mem_Ioo_notMem_of_countable
    (half_pos (Real.log_pos one_lt_two)) (countable_bad_widths Z)
  exact ⟨w, hw0, by linarith, fun ρ hρ hre h0 => hwE ⟨hw0, ρ, hρ, hre, h0⟩⟩

/-- Every zero configuration admits a non-resonant grid step `ℓ > 0`. -/
theorem exists_nonresonant_step (Z : ZeroConfig) :
    ∃ ℓ : ℝ, 0 < ℓ ∧ ℓ ∉ resonantSteps Z := by
  obtain ⟨ℓ, ⟨hℓ0, _⟩, hℓE⟩ := exists_mem_Ioo_notMem_of_countable zero_lt_one
    (countable_resonantSteps Z)
  exact ⟨ℓ, hℓ0, hℓE⟩

/-- Every nontrivial zero of `ζ` in the critical strip lifts to a copy in `XiZeroCopy`. -/
theorem exists_xiZeroCopy_of_mem_zetaZeroConfig {ρ : ℂ} (hρ : ρ ∈ zetaZeroConfig.carrier) :
    ∃ q : XiZeroCopy, (q.1 : ℂ) = ρ := by
  let d : XiDivisorSupport := xiDivisorZetaCarrierEquiv.symm ⟨ρ, hρ⟩
  refine ⟨⟨d, ⟨0, by have h := xi_divisor_pos_on_support d; omega⟩⟩, rfl⟩

/-- `RiemannHypothesis` is equivalent to all zeros in `zetaZeroConfig.carrier` lying on `Re s = 1/2`. -/
theorem riemannHypothesis_iff_zetaZeroConfig_onLine :
    RiemannHypothesis ↔ ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re = 1 / 2 := by
  constructor
  · intro hRH ρ ⟨hz, hre0, hre1⟩
    refine hRH ρ hz ?_ ?_
    · rintro ⟨n, hn⟩
      have := congrArg Complex.re hn
      simp at this
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    · intro h; rw [h] at hre1; simp at hre1
  · intro hon
    by_contra hnot
    obtain ⟨q, hq⟩ := exists_xiZeroCopy_re_gt_half_of_not_riemannHypothesis hnot
    have := hon (q.1 : ℂ) (xiZeroCopy_mem_carrier q)
    linarith

/-- `AttainedTop β₀` is equivalent to `β₀` being the attained maximum of `Re ρ` on
`zetaZeroConfig.carrier`. -/
theorem attainedTop_iff_zetaZeroConfig {β₀ : ℝ} :
    AttainedTop β₀ ↔
      (∃ ρ ∈ zetaZeroConfig.carrier, ρ.re = β₀) ∧
        ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ β₀ := by
  constructor
  · rintro ⟨⟨q₀, hq₀⟩, hmax⟩
    refine ⟨⟨q₀.1, xiZeroCopy_mem_carrier q₀, hq₀⟩, fun ρ hρ => ?_⟩
    obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_mem_zetaZeroConfig hρ
    rw [← hq]
    exact hmax q
  · rintro ⟨⟨ρ₀, hρ₀, hre₀⟩, hmax⟩
    obtain ⟨q₀, hq₀⟩ := exists_xiZeroCopy_of_mem_zetaZeroConfig hρ₀
    exact ⟨⟨q₀, by rw [hq₀, hre₀]⟩, fun q => hmax (q.1 : ℂ) (xiZeroCopy_mem_carrier q)⟩

/-- Under `ZerosApproachLine`, if any zero in `zetaZeroConfig.carrier` satisfies `Re ρ > 1/2 + σ`
(`σ ≥ 0`), then `zetaZeroConfig.carrier` attains a maximum real part `β₀ > 1/2 + σ`. -/
theorem exists_attainedTop_of_zerosApproachLine_of_re_gt
    (hZ : BacklundConverse.ZerosApproachLine) {σ : ℝ} (hσ : 0 ≤ σ) {ρ₁ : ℂ}
    (hρ₁ : ρ₁ ∈ zetaZeroConfig.carrier) (hre₁ : 1 / 2 + σ < ρ₁.re) :
    ∃ β₀ : ℝ, 1 / 2 + σ < β₀ ∧ AttainedTop β₀ := by
  obtain ⟨q₁, hq₁⟩ := exists_xiZeroCopy_of_mem_zetaZeroConfig hρ₁
  have hq₁re : 1 / 2 + σ < (q₁.1 : ℂ).re := by rwa [hq₁]
  set h : ℝ := ((q₁.1 : ℂ).re - 1 / 2) / 2 with hh
  have hh0 : 0 < h := by rw [hh]; linarith
  set F : Set XiZeroCopy := {q | 1 / 2 + h < (q.1 : ℂ).re} with hF
  have hFfin : F.Finite := by
    refine (BacklundConverse.finite_abs_im_gt_of_zerosApproachLine hZ hh0).subset fun q hq => ?_
    simp only [hF, mem_setOf_eq] at hq ⊢
    have him : (xiSpectralPoint q).im = 1 / 2 - (q.1 : ℂ).re := by simp [xiSpectralPoint]
    rw [him, abs_sub_comm, abs_of_pos (by linarith)]
    linarith
  have hq₁F : q₁ ∈ F := by simp only [hF, mem_setOf_eq]; rw [hh]; linarith
  obtain ⟨q₀, hq₀F, hmax⟩ := hFfin.exists_maximalFor (fun q => (q.1 : ℂ).re) F ⟨q₁, hq₁F⟩
  have hq₀ : (q₁.1 : ℂ).re ≤ (q₀.1 : ℂ).re := by
    by_contra hlt
    push Not at hlt
    exact absurd (hmax hq₁F hlt.le) (not_le.mpr hlt)
  refine ⟨(q₀.1 : ℂ).re, by linarith, ⟨q₀, rfl⟩, fun q => ?_⟩
  by_cases hq : q ∈ F
  · by_contra hlt
    push Not at hlt
    exact absurd (hmax hq hlt.le) (not_le.mpr hlt)
  · simp only [hF, mem_setOf_eq, not_lt] at hq
    have : 1 / 2 + h < (q₀.1 : ℂ).re := hq₀F
    linarith

/-! ### Closed-aperture Rayleigh bridge from `ccmRestrictedWeilGroundEnergy` to dyadic prime windows -/

theorem contDiff_top_weilBumpC : ContDiff ℝ (⊤ : ℕ∞) weilBumpC :=
  Complex.ofRealCLM.contDiff.comp weilBump.contDiff

theorem contDiff_top_scaledBump (w : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (scaledBump w) :=
  contDiff_top_weilBumpC.comp (contDiff_id.div_const _)

theorem contDiff_top_modScaledBump (w ω : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (modScaledBump w ω) := by
  unfold modScaledBump
  refine ContDiff.mul ?_ (contDiff_top_scaledBump w)
  have : ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => -(I * (ω : ℂ) * (u : ℂ))) :=
    (contDiff_const.mul Complex.ofRealCLM.contDiff).neg
  exact Complex.contDiff_exp.comp this

theorem contDiff_top_bumpTest {β : ℝ → ℂ} (hβ : ContDiff ℝ (⊤ : ℕ∞) β) (ℓ : ℝ) {n : ℕ}
    (c : Fin n → ℂ) : ContDiff ℝ (⊤ : ℕ∞) (bumpTest β ℓ c) := by
  unfold bumpTest
  exact ContDiff.sum fun i _ => contDiff_const.mul (hβ.comp (contDiff_id.sub contDiff_const))

/-- **Closed-aperture Rayleigh inequality.** For every `A : SuzukiPositiveAperture` and every smooth
test `g` supported in `[-A, A]`, `μ(A) ∫ ‖g‖² ≤ Re W_ζ(g, g)`. -/
theorem ccmRestrictedWeilGroundEnergy_mul_integral_norm_sq_le_re_W
    {A : SuzukiPositiveAperture} {g : ℝ → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgs : tsupport g ⊆ Icc (-A.1) A.1) :
    ccmRestrictedWeilGroundEnergy A * ∫ x, ‖g x‖ ^ 2 ≤ (zetaZeroConfig.W g g).re := by
  have hgc : HasCompactSupport g := hasCompactSupport_of_tsupport_subset_Icc hgs
  have hseq : ∀ n : ℕ,
      ccmRestrictedWeilGroundEnergy (suzukiRightAperture A n) * ∫ x, ‖g x‖ ^ 2 ≤
        (zetaZeroConfig.W g g).re := by
    intro n
    have hgt := suzukiRightAperture_gt A n
    have hsub : tsupport g ⊆ Ioo (-(suzukiRightAperture A n).1) (suzukiRightAperture A n).1 :=
      hgs.trans fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
    let u : CCMComplexSmoothInteriorSource (suzukiRightAperture A n) := ⟨g, hg, hgc, hsub⟩
    have h := ccmRestrictedWeilGroundEnergy_mul_formNorm_sq_le_source
      (suzukiRightAperture A n) u.toCCMFormVector
    rwa [norm_sq_ccmArchimedeanFormToAperture_toCCMFormVector,
      ccmRestrictedWeilSource_complexSmooth_eq_zetaWeil] at h
  exact le_of_tendsto
    ((tendsto_ccmRestrictedWeilGroundEnergy_suzukiRightAperture A).mul_const _)
    (Eventually.of_forall hseq)

/-- For disjoint bumps (`2w < v`), the `L²` mass of the difference two-bump test is `2 ∫ ‖κ_w‖²`. -/
theorem integral_norm_sq_twoBump_modScaledBump_eq {w v : ℝ} (hw : 0 < w) (hv : 2 * w < v) :
    (∫ t, ‖twoBump (modScaledBump w 0) v (-1) t‖ ^ 2) =
      2 * ∫ t, ‖modScaledBump w 0 t‖ ^ 2 := by
  have hbs := modScaledBump_support hw 0
  have hb : Continuous (modScaledBump w 0) := (contDiff_modScaledBump_two w 0).continuous
  have hbc : HasCompactSupport (modScaledBump w 0) := hasCompactSupport_of_support_subset_abs hbs
  have hv0 : 0 < v := by linarith
  have h := weilTest_twoBump_neg_one hb hbc v 0
  rw [weilTest_self_zero, weilTest_self_zero, zero_add, zero_sub,
    weilTest_self_eq_zero_of_lt hbs (by rw [abs_of_pos hv0]; exact hv),
    weilTest_self_eq_zero_of_lt hbs (by rw [abs_neg, abs_of_pos hv0]; exact hv),
    sub_zero, sub_zero] at h
  exact_mod_cast h

/-- Exact Rayleigh lower bound on the difference two-bump Weil form at aperture `v / 2 + w`. -/
theorem ccmRestrictedWeilGroundEnergy_mul_le_re_W_twoBump {w v : ℝ} (hw : 0 < w) (hv : 0 ≤ v) :
    ccmRestrictedWeilGroundEnergy ⟨v / 2 + w, by positivity⟩ *
        ∫ t, ‖twoBump (modScaledBump w 0) v (-1) t‖ ^ 2 ≤
      (zetaZeroConfig.W (twoBump (modScaledBump w 0) v (-1))
        (twoBump (modScaledBump w 0) v (-1))).re :=
  ccmRestrictedWeilGroundEnergy_mul_integral_norm_sq_le_re_W
    (contDiff_top_bumpTest (contDiff_top_modScaledBump w 0) v ![1, -1])
    (tsupport_twoBump_modScaledBump_subset hw hv)

/-- For disjoint bumps (`2w < v`), the two-bump Weil form is bounded below by
`2 ‖κ_w‖₂² μ(v/2 + w)`. -/
theorem two_mul_ccmRestrictedWeilGroundEnergy_le_re_W_twoBump {w v : ℝ} (hw : 0 < w)
    (hv : 2 * w < v) :
    2 * (∫ t, ‖modScaledBump w 0 t‖ ^ 2) *
        ccmRestrictedWeilGroundEnergy ⟨v / 2 + w, by linarith⟩ ≤
      (zetaZeroConfig.W (twoBump (modScaledBump w 0) v (-1))
        (twoBump (modScaledBump w 0) v (-1))).re := by
  have h := ccmRestrictedWeilGroundEnergy_mul_le_re_W_twoBump hw (by linarith : 0 ≤ v)
  rw [integral_norm_sq_twoBump_modScaledBump_eq hw hv] at h
  linarith

/-- **Rayleigh–Prime-Window Bridge.** For `0 < w`, `2w < log 2`, and `2w < v`, the dyadic prime
window functional `Re P_{w,v}` is bounded below by `2 ‖κ_w‖₂² μ(v/2 + w)`. -/
theorem two_mul_ccmRestrictedWeilGroundEnergy_le_re_lagPrimeWindowRHS {w v : ℝ} (hw : 0 < w)
    (hw2 : 2 * w < Real.log 2) (hv : 2 * w < v) :
    2 * (∫ t, ‖modScaledBump w 0 t‖ ^ 2) *
        ccmRestrictedWeilGroundEnergy ⟨v / 2 + w, by linarith⟩ ≤
      (lagPrimeWindowRHS v w (EF.weilTest (twoBump (modScaledBump w 0) v (-1))
        (twoBump (modScaledBump w 0) v (-1)))).re := by
  have hv0 : 0 ≤ v := by linarith
  have h := two_mul_ccmRestrictedWeilGroundEnergy_le_re_W_twoBump hw hv
  rwa [zeta_W_eq_literatureRHS (f := twoBump (modScaledBump w 0) v (-1))
    (contDiff_bumpTest (contDiff_modScaledBump_two w 0) v ![1, -1])
    (hasCompactSupport_twoBump (hasCompactSupport_of_support_subset_abs
      (modScaledBump_support hw 0)) v (-1)),
    literatureRHS_twoBump_eq_lagPrimeWindowRHS (modScaledBump_support hw 0) hw2 hv0] at h

/-- **Small-aperture Markov floor on dyadic prime windows.** For `0 < w`, `2w < v`, and
`v / 2 + w ≤ 21 / 200`, the prime window functional satisfies `Re P_{w,v} ≥ (1/15) ∫ ‖κ_w‖²`. -/
theorem one_fifteenth_mul_le_re_lagPrimeWindowRHS_of_le {w v : ℝ} (hw : 0 < w) (hv : 2 * w < v)
    (hvw : v / 2 + w ≤ 21 / 200) :
    1 / 15 * ∫ t, ‖modScaledBump w 0 t‖ ^ 2 ≤
      (lagPrimeWindowRHS v w (EF.weilTest (twoBump (modScaledBump w 0) v (-1))
        (twoBump (modScaledBump w 0) v (-1)))).re := by
  have hw2 : 2 * w < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hray := two_mul_ccmRestrictedWeilGroundEnergy_le_re_lagPrimeWindowRHS hw hw2 hv
  have hfloor := one_thirtieth_le_ccmRestrictedWeilGroundEnergy (A := ⟨v / 2 + w, by linarith⟩) hvw
  have hB0 : 0 ≤ ∫ t, ‖modScaledBump w 0 t‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  nlinarith

/-- **Logarithmic window-gauge floor on dyadic prime windows.** For `0 < w`, `2w < v`,
`v / 2 + w < R`, and `2R < log 2`, `Re P_{w,v} ≥ 2 windowFloor(R) ∫ ‖κ_w‖²`. -/
theorem two_mul_windowFloor_le_re_lagPrimeWindowRHS_of_lt {w v R : ℝ} (hw : 0 < w)
    (hv : 2 * w < v) (hR : v / 2 + w < R) (hR2 : 2 * R < Real.log 2) :
    2 * windowFloor R * ∫ t, ‖modScaledBump w 0 t‖ ^ 2 ≤
      (lagPrimeWindowRHS v w (EF.weilTest (twoBump (modScaledBump w 0) v (-1))
        (twoBump (modScaledBump w 0) v (-1)))).re := by
  have hw2 : 2 * w < Real.log 2 := by linarith
  have hray := two_mul_ccmRestrictedWeilGroundEnergy_le_re_lagPrimeWindowRHS hw hw2 hv
  have hfloor := windowFloor_le_ccmRestrictedWeilGroundEnergy
    (A := ⟨v / 2 + w, by linarith⟩) hR hR2
  have hB0 : 0 ≤ ∫ t, ‖modScaledBump w 0 t‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  nlinarith

/-! ### Unconditional sharp `2σ`-abscissa law for `ccmRestrictedWeilGroundEnergy` -/

/-- **Unconditional sharp `2σ`-abscissa theorem for the restricted Weil ground energy `μ(A)`.**
If `μ(A) ≥ -C e^{2σA}` for all `A ≥ A₀` (`σ ≥ 0`), then every nontrivial zero of `ζ` in the
critical strip satisfies `Re ρ ≤ 1/2 + σ` (without any `ZerosApproachLine` or `AttainedTop`
hypothesis). -/
theorem re_le_of_ccmRestrictedWeilGroundEnergy_ge_neg_exp {σ C A₀ : ℝ} (hσ : 0 ≤ σ)
    (hμ : ∀ A : SuzukiPositiveAperture, A₀ ≤ A.1 →
      -(C * Real.exp (2 * σ * A.1)) ≤ ccmRestrictedWeilGroundEnergy A) :
    ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ 1 / 2 + σ := by
  obtain ⟨w, hw0, _, hgood⟩ := exists_good_width zetaZeroConfig
  have hlt : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re < 1 := fun ρ hρ => hρ.2.2
  rw [re_le_iff_lag_twoBump_ge_neg_exp _ temperedConfig_zetaZeroConfig hlt hw0 hgood hσ]
  set B := ∫ t, ‖modScaledBump w 0 t‖ ^ 2 with hB
  have hB0 : 0 ≤ B := integral_nonneg fun _ => sq_nonneg _
  refine ⟨2 * B * max C 0 * Real.exp (2 * σ * w), max (2 * w + 1) (2 * (A₀ - w)), fun v hv => ?_⟩
  have hv2w : 2 * w < v := by linarith [le_max_left (2 * w + 1) (2 * (A₀ - w))]
  have hvA₀ : A₀ ≤ v / 2 + w := by linarith [le_max_right (2 * w + 1) (2 * (A₀ - w))]
  have hray := two_mul_ccmRestrictedWeilGroundEnergy_le_re_W_twoBump hw0 hv2w
  have hfloor := hμ ⟨v / 2 + w, by linarith⟩ hvA₀
  have hC : C ≤ max C 0 := le_max_left _ _
  have hexp : Real.exp (2 * σ * (v / 2 + w)) = Real.exp (2 * σ * w) * Real.exp (σ * v) := by
    rw [← Real.exp_add]; congr 1; ring
  have h1 : -(2 * B * max C 0 * Real.exp (2 * σ * w) * Real.exp (σ * v)) ≤
      2 * B * ccmRestrictedWeilGroundEnergy ⟨v / 2 + w, by linarith⟩ := by
    calc -(2 * B * max C 0 * Real.exp (2 * σ * w) * Real.exp (σ * v))
        = 2 * B * (-(max C 0 * Real.exp (2 * σ * (v / 2 + w)))) := by rw [hexp]; ring
      _ ≤ 2 * B * (-(C * Real.exp (2 * σ * (v / 2 + w)))) := by
          refine mul_le_mul_of_nonneg_left (neg_le_neg ?_) (by linarith)
          exact mul_le_mul_of_nonneg_right hC (Real.exp_pos _).le
      _ ≤ 2 * B * ccmRestrictedWeilGroundEnergy ⟨v / 2 + w, by linarith⟩ :=
          mul_le_mul_of_nonneg_left hfloor (by linarith)
  linarith

/-- Symmetric strip bound `|Re ρ - 1/2| ≤ σ` from `μ(A) ≥ -C e^{2σA}`. -/
theorem abs_re_sub_half_le_of_ccmRestrictedWeilGroundEnergy_ge_neg_exp {σ C A₀ : ℝ} (hσ : 0 ≤ σ)
    (hμ : ∀ A : SuzukiPositiveAperture, A₀ ≤ A.1 →
      -(C * Real.exp (2 * σ * A.1)) ≤ ccmRestrictedWeilGroundEnergy A)
    {ρ : ℂ} (hρ : ρ ∈ zetaZeroConfig.carrier) :
    |ρ.re - 1 / 2| ≤ σ := by
  have h1 := re_le_of_ccmRestrictedWeilGroundEnergy_ge_neg_exp hσ hμ ρ hρ
  have h2 := re_le_of_ccmRestrictedWeilGroundEnergy_ge_neg_exp hσ hμ (Zeta23.reflect ρ)
    (zetaZeroConfig.reflect_mem ρ hρ)
  have hrefl : (Zeta23.reflect ρ).re = 1 - ρ.re := by simp [Zeta23.reflect]
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

/-- Unconditional sharp `2σ` bound on `|(xiSpectralPoint q).im|` from `μ(A) ≥ -C e^{2σA}`. -/
theorem abs_im_xiSpectralPoint_le_of_ccmRestrictedWeilGroundEnergy_ge_neg_exp {σ C A₀ : ℝ}
    (hσ : 0 ≤ σ)
    (hμ : ∀ A : SuzukiPositiveAperture, A₀ ≤ A.1 →
      -(C * Real.exp (2 * σ * A.1)) ≤ ccmRestrictedWeilGroundEnergy A)
    (q : XiZeroCopy) :
    |(xiSpectralPoint q).im| ≤ σ := by
  have h := abs_re_sub_half_le_of_ccmRestrictedWeilGroundEnergy_ge_neg_exp hσ hμ
    (xiZeroCopy_mem_carrier q)
  have him : (xiSpectralPoint q).im = 1 / 2 - (q.1 : ℂ).re := by
    simp [xiSpectralPoint]
  rw [him, ← abs_neg, show -(1 / 2 - (q.1 : ℂ).re) = (q.1 : ℂ).re - 1 / 2 by ring]
  exact h

/-- Contrapositive: any zero `ρ ∈ zetaZeroConfig.carrier` with `Re ρ > 1/2 + σ` (`σ ≥ 0`) forces
`μ(A) < -C e^{2σA}` at arbitrarily large apertures `A ≥ A₀`. -/
theorem exists_ccmRestrictedWeilGroundEnergy_lt_neg_exp_of_re_gt {σ : ℝ} (hσ : 0 ≤ σ)
    {ρ : ℂ} (hρ : ρ ∈ zetaZeroConfig.carrier) (hre : 1 / 2 + σ < ρ.re) (C A₀ : ℝ) :
    ∃ A : SuzukiPositiveAperture, A₀ ≤ A.1 ∧
      ccmRestrictedWeilGroundEnergy A < -(C * Real.exp (2 * σ * A.1)) := by
  by_contra hno
  push Not at hno
  have := re_le_of_ccmRestrictedWeilGroundEnergy_ge_neg_exp hσ hno ρ hρ
  linarith

/-! ### Geometric lag grids measure the abscissa up to chains and resolve `ZerosApproachLine` -/

/-- **Geometric lag grids see attained tops above `1/2 + σ`.** If `Re W ≥ -C e^{σ k ℓ}` along the
grid `v_k = kℓ` for a good width `w > 0` and non-resonant step `ℓ > 0`, then every zero
`ρ₀ ∈ Z.carrier` with `Re ρ₀ > 1/2 + σ` is strictly exceeded in real part by another zero. -/
theorem exists_re_gt_of_grid_lag_ge_neg_exp (Z : ZeroConfig) (hZ : TemperedConfig Z)
    {w : ℝ} (hw : 0 < w)
    (hgood : ∀ ρ ∈ Z.carrier, ρ.re ≠ 1 / 2 → paperFT (scaledBump w) (gammaOf ρ) ≠ 0) {ℓ : ℝ}
    (hℓ : 0 < ℓ) (hres : ℓ ∉ resonantSteps Z) {σ C : ℝ} (hσ : 0 ≤ σ) {N : ℕ}
    (hm : ∀ k : ℕ, N ≤ k → -(C * Real.exp (σ * (k * ℓ))) ≤
      (Z.W (twoBump (modScaledBump w 0) (k * ℓ) (-1))
        (twoBump (modScaledBump w 0) (k * ℓ) (-1))).re)
    {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ Z.carrier) (hre₀ : 1 / 2 + σ < ρ₀.re) :
    ∃ ρ ∈ Z.carrier, ρ₀.re < ρ.re := by
  classical
  by_contra hno
  push Not at hno
  set b := modScaledBump w 0 with hbdef
  have hb : ContDiff ℝ 2 b := contDiff_modScaledBump_two w 0
  have hbs := modScaledBump_support hw 0
  set D := ρ₀.re - 1 / 2 with hD
  have hDσ : 0 < D - σ := by rw [hD]; linarith
  have hD0 : 0 < D := by linarith
  set ι : Set ℂ := {z | evenCoeff Z b z ≠ 0} with hι
  haveI : Countable ι := (countable_evenCoeff_support Z b).to_subtype
  have hDs : Summable fun z : ℂ => ‖evenCoeff Z b z‖ := by
    have h0 := (two_re_lagStructure_eq Z hZ hb hbs 0).1.norm
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one] at h0
    exact h0
  have hreD : ∀ z : ι, (z : ℂ).re ≤ D := fun z => by
    rcases mem_of_evenCoeff_ne_zero z.2 with h | h
    · have := hno _ h; simp at this; linarith
    · have := hno _ h; simp at this; linarith
  set W : ι → ℂ := fun z => cexp (((z : ℂ) - D) * ℓ) with hWdef
  have hWre : ∀ z : ι, ‖W z‖ = Real.exp (((z : ℂ).re - D) * ℓ) := fun z => by
    rw [hWdef, Complex.norm_exp]; simp
  have hWn : ∀ z : ι, ‖W z‖ ≤ 1 := fun z => by
    rw [hWre, Real.exp_le_one_iff]
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith [hreD z]) hℓ.le
  have hgrid : ∀ k : ℕ, ∑' z : ι, evenCoeff Z b z * W z ^ k =
      ((Real.exp (-D * (k * ℓ)) * (2 * (lagStructure Z b (k * ℓ)).re) : ℝ) : ℂ) := fun k => by
    have hsub :
        Function.support (fun z : ℂ => evenCoeff Z b z * cexp (z * ((k * ℓ : ℝ) : ℂ))) ⊆ ι :=
      fun z hz h0 => hz (show evenCoeff Z b z * cexp (z * ((k * ℓ : ℝ) : ℂ)) = 0 by
        rw [h0, zero_mul])
    rw [Complex.ofReal_mul, (two_re_lagStructure_eq Z hZ hb hbs (k * ℓ)).2,
      ← tsum_subtype_eq_of_support_subset hsub, ← tsum_mul_left]
    refine tsum_congr fun z => ?_
    have e : W z ^ k = cexp (((-D * (k * ℓ) : ℝ) : ℂ)) * cexp ((z : ℂ) * ((k * ℓ : ℝ) : ℂ)) := by
      rw [hWdef, ← Complex.exp_nat_mul, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [e, Complex.ofReal_exp]
    ring
  have hreal : ∀ k : ℕ, (∑' z : ι, evenCoeff Z b z * W z ^ k).im = 0 := fun k => by
    rw [hgrid, Complex.ofReal_im]
  have hlim : ∀ ε > 0, ∀ᶠ k : ℕ in atTop, (∑' z : ι, evenCoeff Z b z * W z ^ k).re ≤ ε := by
    intro ε hε
    set A := max (2 * (lagStructure Z b 0).re) 0 + max C 0 with hA
    have hexp : Tendsto (fun k : ℕ => Real.exp (-(D - σ) * (k * ℓ)) * A) atTop (𝓝 0) := by
      have h1 : Tendsto (fun k : ℕ => -(D - σ) * (k * ℓ)) atTop atBot := by
        have : Tendsto (fun k : ℕ => (D - σ) * ℓ * (k : ℝ)) atTop atTop :=
          tendsto_natCast_atTop_atTop.const_mul_atTop (mul_pos hDσ hℓ)
        refine (tendsto_neg_atTop_atBot.comp this).congr fun k => ?_
        simp only [Function.comp]
        ring
      simpa using (Real.tendsto_exp_atBot.comp h1).mul_const A
    filter_upwards [eventually_ge_atTop N, (tendsto_order.1 hexp).2 ε hε] with k hk hk'
    rw [hgrid, Complex.ofReal_re]
    have h := hm k hk
    rw [re_W_lag_eq Z hZ hb hbs] at h
    have hv0 : 0 ≤ (k : ℝ) * ℓ := mul_nonneg k.cast_nonneg hℓ.le
    have h1 : 1 ≤ Real.exp (σ * (k * ℓ)) := Real.one_le_exp (mul_nonneg hσ hv0)
    have hS0 : 2 * (lagStructure Z b 0).re ≤
        max (2 * (lagStructure Z b 0).re) 0 * Real.exp (σ * (k * ℓ)) := by
      nlinarith [le_max_left (2 * (lagStructure Z b 0).re) 0,
        le_max_right (2 * (lagStructure Z b 0).re) 0]
    have hCe : C * Real.exp (σ * (k * ℓ)) ≤ max C 0 * Real.exp (σ * (k * ℓ)) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
    have h2 : 2 * (lagStructure Z b (k * ℓ)).re ≤ A * Real.exp (σ * (k * ℓ)) := by
      rw [hA, add_mul]; linarith
    have h3 : Real.exp (-D * (k * ℓ)) * (2 * (lagStructure Z b (k * ℓ)).re) ≤
        Real.exp (-(D - σ) * (k * ℓ)) * A := by
      calc Real.exp (-D * (k * ℓ)) * (2 * (lagStructure Z b (k * ℓ)).re)
          ≤ Real.exp (-D * (k * ℓ)) * (A * Real.exp (σ * (k * ℓ))) :=
            mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
        _ = (Real.exp (-D * (k * ℓ)) * Real.exp (σ * (k * ℓ))) * A := by ring
        _ = Real.exp (-(D - σ) * (k * ℓ)) * A := by
            rw [← Real.exp_add]; congr 2; ring
    exact h3.trans hk'.le
  set z₀ : ℂ := ρ₀ - 1 / 2 with hz₀def
  have hz₀ : evenCoeff Z b z₀ ≠ 0 :=
    evenCoeff_modScaledBump_zero_sub_half_ne_zero Z hw hρ₀ (hgood ρ₀ hρ₀ (by linarith))
  have hz₀re : z₀.re = D := by rw [hz₀def, hD]; simp
  have hWz₀ : ‖W ⟨z₀, hz₀⟩‖ = 1 := by
    rw [hWre]; simp only [hz₀re, sub_self, zero_mul, Real.exp_zero]
  have hsumι : Summable fun z : ι => ‖evenCoeff Z b z‖ := hDs.subtype ι
  have key := norm_tsum_ite_le_of_limsup_nonpos hsumι hWn hreal hlim hWz₀
  have hL : (∑' z : ι, if W z = W ⟨z₀, hz₀⟩ then evenCoeff Z b z else 0) =
      evenCoeff Z b z₀ := by
    rw [tsum_eq_single ⟨z₀, hz₀⟩ fun z hz => if_neg fun h => hz (Subtype.ext
      (eq_of_cexp_eq_of_not_resonant hℓ hres (im_mem_zeroHeights_of_evenCoeff_ne_zero z.2)
        (im_mem_zeroHeights_of_evenCoeff_ne_zero hz₀) h)), if_pos rfl]
  have hR : 0 ≤ (∑' z : ι, if W z = 1 then evenCoeff Z b z else 0).re := by
    rw [Complex.re_tsum (f := fun z : ι => if W z = 1 then evenCoeff Z b z else 0)
      (Summable.of_norm_bounded hsumι fun z => by split_ifs <;> simp)]
    refine tsum_nonneg fun z => ?_
    split_ifs with h
    · have h0 : (z : ℂ) = (D : ℂ) := eq_of_cexp_eq_of_not_resonant hℓ hres
        (im_mem_zeroHeights_of_evenCoeff_ne_zero z.2) (by simp [zeroHeights])
        (h.trans (by simp))
      have him : (z : ℂ).im = 0 := by rw [h0, Complex.ofReal_im]
      have hmem : (1 / 2 + (z : ℂ)) ∈ Z.carrier :=
        (mem_of_evenCoeff_ne_zero z.2).elim id fun h' => by
          rwa [show conj (z : ℂ) = z from Complex.ext (by simp) (by simp [him])] at h'
      exact (re_evenCoeff_modScaledBump_zero_pos Z hw hmem him).le
    · simp
  rw [hL] at key
  have := norm_pos_iff.mpr hz₀
  linarith

/-- **Geometric lag grids measure the abscissa up to chains.** For a tempered configuration `Z`,
a good width `w > 0`, a non-resonant step `ℓ > 0`, and `σ ≥ 0`: all zeros satisfy
`Re ρ ≤ 1/2 + σ` iff any zero above `1/2 + σ` implies an attained maximum of `Re ρ` on `Z.carrier`
and `Re W ≥ -C e^{σ k ℓ}` along `v_k = kℓ` (`k ≥ N`). -/
theorem re_le_iff_topAttained_above_and_grid_lag_ge_neg_exp (Z : ZeroConfig)
    (hZ : TemperedConfig Z) {w : ℝ} (hw : 0 < w)
    (hgood : ∀ ρ ∈ Z.carrier, ρ.re ≠ 1 / 2 → paperFT (scaledBump w) (gammaOf ρ) ≠ 0) {ℓ : ℝ}
    (hℓ : 0 < ℓ) (hres : ℓ ∉ resonantSteps Z) {σ : ℝ} (hσ : 0 ≤ σ) (N : ℕ) :
    (∀ ρ ∈ Z.carrier, ρ.re ≤ 1 / 2 + σ) ↔
      ((∃ ρ ∈ Z.carrier, 1 / 2 + σ < ρ.re) →
          ∃ ρ₀ ∈ Z.carrier, ∀ ρ ∈ Z.carrier, ρ.re ≤ ρ₀.re) ∧
        ∃ C : ℝ, ∀ k : ℕ, N ≤ k → -(C * Real.exp (σ * (k * ℓ))) ≤
          (Z.W (twoBump (modScaledBump w 0) (k * ℓ) (-1))
            (twoBump (modScaledBump w 0) (k * ℓ) (-1))).re := by
  set b := modScaledBump w 0 with hbdef
  have hb : ContDiff ℝ 2 b := contDiff_modScaledBump_two w 0
  have hbs := modScaledBump_support hw 0
  constructor
  · intro hle
    refine ⟨fun ⟨ρ, hρ, hgt⟩ => absurd (hle ρ hρ) (not_le.mpr hgt), ?_⟩
    set A := 2 * (lagStructure Z b 0).re with hA
    set M := ∑' z : ℂ, ‖evenCoeff Z b z‖ with hM
    refine ⟨|A| + M, fun k _ => ?_⟩
    have hv : (0 : ℝ) ≤ k * ℓ := mul_nonneg k.cast_nonneg hℓ.le
    have h := two_re_lagStructure_le_mul_exp Z hZ hb hbs (τ := σ) (fun z hz => by
      rcases mem_of_evenCoeff_ne_zero hz with h | h
      · have := hle _ h; simp at this; linarith
      · have := hle _ h; simp at this; linarith) hv
    have he1 : 1 ≤ Real.exp (σ * (k * ℓ)) := Real.one_le_exp (mul_nonneg hσ hv)
    have h1 : |A| ≤ |A| * Real.exp (σ * (k * ℓ)) := le_mul_of_one_le_right (abs_nonneg _) he1
    rw [re_W_lag_eq Z hZ hb hbs, add_mul]
    linarith [neg_abs_le A]
  · rintro ⟨htop, C, hm⟩ ρ hρ
    by_contra hgt
    push Not at hgt
    obtain ⟨ρ₀, hρ₀, hmax⟩ := htop ⟨ρ, hρ, hgt⟩
    obtain ⟨ρ', hρ', hgt'⟩ := exists_re_gt_of_grid_lag_ge_neg_exp Z hZ hw hgood hℓ hres hσ hm hρ₀
      (lt_of_lt_of_le hgt (hmax ρ hρ))
    exact absurd (hmax ρ' hρ') (not_le.mpr hgt')

/-- **Single-grid exclusion of `AttainedTop` above `1/2 + σ`.** If `Re P_{w, kℓ} ≥ -C e^{σ k ℓ}`
(`k ≥ N`) along a single non-resonant geometric progression of dyadic prime windows `X_k = e^{kℓ}`,
then `¬ AttainedTop β₀` for every `β₀ > 1/2 + σ`. -/
theorem not_attainedTop_of_grid_primeWindow_ge_neg_exp {w ℓ σ C : ℝ} (hw : 0 < w)
    (hw2 : 2 * w < Real.log 2)
    (hgood : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≠ 1 / 2 → paperFT (scaledBump w) (gammaOf ρ) ≠ 0)
    (hℓ : 0 < ℓ) (hres : ℓ ∉ resonantSteps zetaZeroConfig) (hσ : 0 ≤ σ) {N : ℕ}
    (hm : ∀ k : ℕ, N ≤ k → -(C * Real.exp (σ * (k * ℓ))) ≤
      (lagPrimeWindowRHS (k * ℓ) w (EF.weilTest (twoBump (modScaledBump w 0) (k * ℓ) (-1))
        (twoBump (modScaledBump w 0) (k * ℓ) (-1)))).re)
    {β₀ : ℝ} (hβ₀ : 1 / 2 + σ < β₀) :
    ¬ AttainedTop β₀ := by
  intro hatt
  obtain ⟨⟨ρ₀, hρ₀, hre₀⟩, hmax⟩ := attainedTop_iff_zetaZeroConfig.mp hatt
  have hmW : ∀ k : ℕ, N ≤ k → -(C * Real.exp (σ * (k * ℓ))) ≤
      (zetaZeroConfig.W (twoBump (modScaledBump w 0) (k * ℓ) (-1))
        (twoBump (modScaledBump w 0) (k * ℓ) (-1))).re := fun k hk => by
    have hv : (0 : ℝ) ≤ k * ℓ := mul_nonneg k.cast_nonneg hℓ.le
    rw [zeta_W_eq_literatureRHS (f := twoBump (modScaledBump w 0) (k * ℓ) (-1))
      (contDiff_bumpTest (contDiff_modScaledBump_two w 0) (k * ℓ) ![1, -1])
      (hasCompactSupport_twoBump (hasCompactSupport_of_support_subset_abs
        (modScaledBump_support hw 0)) (k * ℓ) (-1)),
      literatureRHS_twoBump_eq_lagPrimeWindowRHS (modScaledBump_support hw 0) hw2 hv]
    exact hm k hk
  obtain ⟨ρ', hρ', hgt⟩ := exists_re_gt_of_grid_lag_ge_neg_exp zetaZeroConfig
    temperedConfig_zetaZeroConfig hw hgood hℓ hres hσ hmW hρ₀ (by linarith)
  have := hmax ρ' hρ'
  linarith

/-- **Single-grid quasi-RH equivalence under `ZerosApproachLine`.** Under `ZerosApproachLine`, for
all but countably many widths `w ∈ (0, ½ log 2)` and steps `ℓ > 0` and every `σ ≥ 0` and `N : ℕ`,
every nontrivial zero of `ζ` has `Re ρ ≤ 1/2 + σ` iff `Re P_{w, kℓ} ≥ -C e^{σ k ℓ}` along the
single geometric progression `X_k = e^{kℓ}` (`k ≥ N`). -/
theorem zeta_re_le_iff_grid_primeWindow_ge_neg_exp_of_zerosApproachLine
    (hZAL : BacklundConverse.ZerosApproachLine) :
    ∃ E : Set ℝ, E.Countable ∧ ∃ E' : Set ℝ, E'.Countable ∧ ∀ w : ℝ, 0 < w →
      2 * w < Real.log 2 → w ∉ E → ∀ ℓ : ℝ, 0 < ℓ → ℓ ∉ E' → ∀ σ : ℝ, 0 ≤ σ → ∀ N : ℕ,
        ((∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ 1 / 2 + σ) ↔
          ∃ C : ℝ, ∀ k : ℕ, N ≤ k → -(C * Real.exp (σ * (k * ℓ))) ≤
            (lagPrimeWindowRHS (k * ℓ) w (EF.weilTest (twoBump (modScaledBump w 0) (k * ℓ) (-1))
              (twoBump (modScaledBump w 0) (k * ℓ) (-1)))).re) := by
  refine ⟨_, countable_bad_widths zetaZeroConfig, _, countable_resonantSteps zetaZeroConfig,
    fun w hw hw2 hwE ℓ hℓ hres σ hσ N => ?_⟩
  have hgood : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≠ 1 / 2 →
      paperFT (scaledBump w) (gammaOf ρ) ≠ 0 := fun ρ hρ hre h0 => hwE ⟨hw, ρ, hρ, hre, h0⟩
  have heq : ∀ k : ℕ, (zetaZeroConfig.W (twoBump (modScaledBump w 0) (k * ℓ) (-1))
      (twoBump (modScaledBump w 0) (k * ℓ) (-1))).re =
      (lagPrimeWindowRHS (k * ℓ) w (EF.weilTest (twoBump (modScaledBump w 0) (k * ℓ) (-1))
        (twoBump (modScaledBump w 0) (k * ℓ) (-1)))).re := fun k => by
    have hv : (0 : ℝ) ≤ k * ℓ := mul_nonneg k.cast_nonneg hℓ.le
    rw [zeta_W_eq_literatureRHS (f := twoBump (modScaledBump w 0) (k * ℓ) (-1))
      (contDiff_bumpTest (contDiff_modScaledBump_two w 0) (k * ℓ) ![1, -1])
      (hasCompactSupport_twoBump (hasCompactSupport_of_support_subset_abs
        (modScaledBump_support hw 0)) (k * ℓ) (-1)),
      literatureRHS_twoBump_eq_lagPrimeWindowRHS (modScaledBump_support hw 0) hw2 hv]
  rw [re_le_iff_topAttained_above_and_grid_lag_ge_neg_exp _ temperedConfig_zetaZeroConfig hw
    hgood hℓ hres hσ N]
  have htop : (∃ ρ ∈ zetaZeroConfig.carrier, 1 / 2 + σ < ρ.re) →
      ∃ ρ₀ ∈ zetaZeroConfig.carrier, ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ ρ₀.re := by
    rintro ⟨ρ₁, hρ₁, hre₁⟩
    obtain ⟨β₀, -, hatt⟩ := exists_attainedTop_of_zerosApproachLine_of_re_gt hZAL hσ hρ₁ hre₁
    obtain ⟨⟨ρ₀, hρ₀, hre₀⟩, hmax⟩ := attainedTop_iff_zetaZeroConfig.mp hatt
    exact ⟨ρ₀, hρ₀, fun ρ hρ => by rw [hre₀]; exact hmax ρ hρ⟩
  simp_rw [heq]
  exact ⟨fun h => h.2, fun h => ⟨htop, h⟩⟩

/-- **Exact `RiemannHypothesis` split on a single geometric progression of dyadic prime windows.**
For all but countably many widths `w ∈ (0, ½ log 2)` and steps `ℓ > 0` and every `N : ℕ`,
`RiemannHypothesis` holds iff `ZerosApproachLine` holds and `Re P_{w, kℓ} ≥ 0` (or `≥ -C`) on the
single geometric grid `X_k = e^{kℓ}` (`k ≥ N`). -/
theorem riemannHypothesis_iff_zerosApproachLine_and_grid_primeWindow_nonneg :
    ∃ E : Set ℝ, E.Countable ∧ ∃ E' : Set ℝ, E'.Countable ∧ ∀ w : ℝ, 0 < w →
      2 * w < Real.log 2 → w ∉ E → ∀ ℓ : ℝ, 0 < ℓ → ℓ ∉ E' → ∀ N : ℕ,
        (RiemannHypothesis ↔
          BacklundConverse.ZerosApproachLine ∧
            ∀ k : ℕ, N ≤ k → 0 ≤ (lagPrimeWindowRHS (k * ℓ) w
              (EF.weilTest (twoBump (modScaledBump w 0) (k * ℓ) (-1))
                (twoBump (modScaledBump w 0) (k * ℓ) (-1)))).re) ∧
        (RiemannHypothesis ↔
          BacklundConverse.ZerosApproachLine ∧
            ∃ C : ℝ, ∀ k : ℕ, N ≤ k → -C ≤ (lagPrimeWindowRHS (k * ℓ) w
              (EF.weilTest (twoBump (modScaledBump w 0) (k * ℓ) (-1))
                (twoBump (modScaledBump w 0) (k * ℓ) (-1)))).re) := by
  refine ⟨_, countable_bad_widths zetaZeroConfig, _, countable_resonantSteps zetaZeroConfig,
    fun w hw hw2 hwE ℓ hℓ hres N => ?_⟩
  have hgood : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≠ 1 / 2 →
      paperFT (scaledBump w) (gammaOf ρ) ≠ 0 := fun ρ hρ hre h0 => hwE ⟨hw, ρ, hρ, hre, h0⟩
  have heq : ∀ k : ℕ, (zetaZeroConfig.W (twoBump (modScaledBump w 0) (k * ℓ) (-1))
      (twoBump (modScaledBump w 0) (k * ℓ) (-1))).re =
      (lagPrimeWindowRHS (k * ℓ) w (EF.weilTest (twoBump (modScaledBump w 0) (k * ℓ) (-1))
        (twoBump (modScaledBump w 0) (k * ℓ) (-1)))).re := fun k => by
    have hv : (0 : ℝ) ≤ k * ℓ := mul_nonneg k.cast_nonneg hℓ.le
    rw [zeta_W_eq_literatureRHS (f := twoBump (modScaledBump w 0) (k * ℓ) (-1))
      (contDiff_bumpTest (contDiff_modScaledBump_two w 0) (k * ℓ) ![1, -1])
      (hasCompactSupport_twoBump (hasCompactSupport_of_support_subset_abs
        (modScaledBump_support hw 0)) (k * ℓ) (-1)),
      literatureRHS_twoBump_eq_lagPrimeWindowRHS (modScaledBump_support hw 0) hw2 hv]
  constructor
  · constructor
    · intro hRH
      refine ⟨zerosApproachLine_of_riemannHypothesis hRH, fun k _ => ?_⟩
      rw [← heq k]
      exact weil_nonneg_of_onLine _ (riemannHypothesis_iff_zetaZeroConfig_onLine.mp hRH) _
    · rintro ⟨hZAL, hm⟩
      by_contra hRH
      obtain ⟨β₀, hβ₀, hatt⟩ := exists_attainedTop_of_zerosApproachLine hZAL hRH
      refine not_attainedTop_of_grid_primeWindow_ge_neg_exp hw hw2 hgood hℓ hres le_rfl (C := 0)
        (N := N) (fun k hk => ?_) (by linarith) hatt
      simpa using hm k hk
  · constructor
    · intro hRH
      refine ⟨zerosApproachLine_of_riemannHypothesis hRH, 0, fun k _ => ?_⟩
      rw [neg_zero, ← heq k]
      exact weil_nonneg_of_onLine _ (riemannHypothesis_iff_zetaZeroConfig_onLine.mp hRH) _
    · rintro ⟨hZAL, C, hm⟩
      by_contra hRH
      obtain ⟨β₀, hβ₀, hatt⟩ := exists_attainedTop_of_zerosApproachLine hZAL hRH
      refine not_attainedTop_of_grid_primeWindow_ge_neg_exp hw hw2 hgood hℓ hres le_rfl (C := C)
        (N := N) (fun k hk => ?_) (by linarith) hatt
      simpa using hm k hk

/-- **Single arithmetic progression of restricted Weil ground energies `μ(kℓ/2 + w)` decides RH
under `ZerosApproachLine`.** For every non-resonant step `ℓ > 0` and good width `w > 0`,
`RiemannHypothesis` holds iff `ZerosApproachLine` holds and `μ(kℓ/2 + w)` is bounded below along
`k ≥ N`. -/
theorem riemannHypothesis_iff_zerosApproachLine_and_grid_ccmRestrictedWeilGroundEnergy_bddBelow
    {w ℓ : ℝ} (hw : 0 < w)
    (hgood : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≠ 1 / 2 → paperFT (scaledBump w) (gammaOf ρ) ≠ 0)
    (hℓ : 0 < ℓ) (hres : ℓ ∉ resonantSteps zetaZeroConfig) (N : ℕ) :
    RiemannHypothesis ↔
      BacklundConverse.ZerosApproachLine ∧
        ∃ C : ℝ, ∀ k : ℕ, N ≤ k →
          -C ≤ ccmRestrictedWeilGroundEnergy
            ⟨k * ℓ / 2 + w, by have : (0 : ℝ) ≤ k * ℓ := mul_nonneg k.cast_nonneg hℓ.le; positivity⟩ := by
  constructor
  · intro hRH
    refine ⟨zerosApproachLine_of_riemannHypothesis hRH, 0, fun k _ => ?_⟩
    rw [neg_zero]
    exact ccmRestrictedWeilGroundEnergy_nonneg_of_riemannHypothesis' hRH _
  · rintro ⟨hZAL, C, hm⟩
    by_contra hRH
    obtain ⟨β₀, hβ₀, hatt⟩ := exists_attainedTop_of_zerosApproachLine hZAL hRH
    obtain ⟨⟨ρ₀, hρ₀, hre₀⟩, hmax⟩ := attainedTop_iff_zetaZeroConfig.mp hatt
    obtain ⟨K, hK⟩ := exists_nat_gt (2 * w / ℓ)
    have hKℓ : 2 * w < K * ℓ := by rwa [div_lt_iff₀ hℓ] at hK
    set B := ∫ t, ‖modScaledBump w 0 t‖ ^ 2 with hB
    have hB0 : 0 ≤ B := integral_nonneg fun _ => sq_nonneg _
    have hmW : ∀ k : ℕ, max N K ≤ k → -(2 * B * max C 0 * Real.exp (0 * (k * ℓ))) ≤
        (zetaZeroConfig.W (twoBump (modScaledBump w 0) (k * ℓ) (-1))
          (twoBump (modScaledBump w 0) (k * ℓ) (-1))).re := fun k hk => by
      have hkN : N ≤ k := le_trans (le_max_left _ _) hk
      have hkK : K ≤ k := le_trans (le_max_right _ _) hk
      have h2w : 2 * w < k * ℓ := lt_of_lt_of_le hKℓ
        (mul_le_mul_of_nonneg_right (by exact_mod_cast hkK) hℓ.le)
      have hray := two_mul_ccmRestrictedWeilGroundEnergy_le_re_W_twoBump hw h2w
      have hfloor := hm k hkN
      have hC : C ≤ max C 0 := le_max_left _ _
      simp only [zero_mul, Real.exp_zero, mul_one]
      nlinarith
    obtain ⟨ρ', hρ', hgt⟩ := exists_re_gt_of_grid_lag_ge_neg_exp zetaZeroConfig
      temperedConfig_zetaZeroConfig hw hgood hℓ hres le_rfl hmW hρ₀ (by linarith)
    have := hmax ρ' hρ'
    linarith

end GaloisForLFunctions.SquareRootThreshold

end
