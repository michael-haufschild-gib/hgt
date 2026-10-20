import GaloisForLFunctions.SquareRootThreshold.LagFamilyMeetsTheCrystalAtTheThreshold
import GaloisForLFunctions.ArithmeticCriticalityTheory.WindowGaugeLogarithmicGroundEnergyFloor
import GaloisForLFunctions.RHTower.ZerosApproachLineAttainment

/-!
# Polar Ground-Energy Bridge, Closed-Aperture Mean-Zero Variation, and the One-Parameter Pole-Free Lag Abscissa Law

This module connects three theorem spines across `RHTower`, `ArithmeticCriticalityTheory`, and
`SquareRootThreshold`:

1. **Closed-Aperture Polar-Constrained Rayleigh Bridge and Closed-Support Mean-Zero Variation**
   (`ccmRestrictedWeilPolarGroundEnergy_mul_integral_norm_sq_le_re_W`,
   `polarGroundEnergy_mul_le_fullZeroForm_Icc`,
   `reflectedDifferenceEnergy_add_le_poleFree_of_meanZero_Icc`,
   `reflectedDifferenceEnergy_add_le_poleFree_of_support_le_halfLogTwo`,
   `reflectedDifferenceEnergy_add_le_poleFree_of_support_le_primeTwo`):
   For any smooth interior source `u`, the two CCM polar inner products
   `⟪ccmPolarApertureVector A (±1/2), u⟫` equal the Fourier transforms `paperFT u (∓I/2)`. Using
   Suzuki polar right-continuity (`tendsto_ccmRestrictedWeilPolarGroundEnergy_suzukiRightAperture`),
   every smooth test `g` supported in the closed interval `[-A, A]` with `paperFT g (±I/2) = 0`
   satisfies `μ₀(A) ∫ ‖g‖² ≤ Re W_ζ(g, g)`. On the `μ_a`-mean-zero sector of
   `ArithmeticCriticalityTheory`, this removes the open-interval margin loss of
   `MeanZeroProfileVariationInequalityPastPrimeTwo`, extending the `1/10`-margin variation
   inequality from `[-1/3, 1/3]` to the full closed prime-free threshold
   `[-½ log 2, ½ log 2]` and the `1/20`-margin inequality from `[-7/20, 7/20]` to the full closed
   prime-2 aperture `[-½(log 2 + 1/50), ½(log 2 + 1/50)]`.

2. **Rayleigh Bridge to Pole-Free Two-Bump Tests and Dyadic Prime Windows Past the Prime `2`**
   (`two_mul_ccmRestrictedWeilPolarGroundEnergy_le_re_W_polarFree_twoBump`,
   `two_mul_ccmRestrictedWeilPolarGroundEnergy_le_arch_sub_primeWindow_polarFree`,
   `one_fifth_mul_le_arch_sub_primeWindow_polarFree_of_le_halfLogTwo`,
   `one_tenth_mul_le_arch_sub_primeWindow_polarFree_of_le_primeTwo`):
   Evaluating the closed-aperture polar Rayleigh bound on the centered polar-free difference test
   `f^{(2)}_{w,ω,v}(t) = κ_{2,w,ω}(t + v/2) - κ_{2,w,ω}(t - v/2)` at aperture `A = v/2 + w` gives,
   for disjoint bumps `2w < v`,
   `2 (∫ ‖κ_{2,w,ω}‖²) μ₀(v/2 + w) ≤ Re W_ζ(f^{(2)}_{w,ω,v}, f^{(2)}_{w,ω,v})`.
   Combining with `μ₀(A) ≥ 1/10` (`A ≤ ½ log 2`) and `μ₀(A) ≥ 1/20` (`A ≤ ½(log 2 + 1/50)`) gives
   height-uniform positivity of the pole-free dyadic prime window functional all the way through
   `v + 2w ≤ log 2 + 1/50`, where the prime `2` actively enters the window.

3. **One-Parameter Pole-Free Lag Abscissa Law and Unconditional Sharp `2σ`-Abscissa Law for `μ₀(A)`**
   (`re_le_iff_polarFree_lag_twoBump_ge_neg_exp`,
   `zeta_re_le_iff_polarFree_lag_primeWindow_ge_neg_exp`,
   `re_le_of_ccmRestrictedWeilPolarGroundEnergy_ge_neg_exp`,
   `abs_im_xiSpectralPoint_le_of_ccmRestrictedWeilPolarGroundEnergy_ge_neg_exp`,
   `riemannHypothesis_iff_zerosApproachLine_and_grid_polarFree_primeWindow_le_arch`,
   `riemannHypothesis_iff_zerosApproachLine_and_grid_ccmRestrictedWeilPolarGroundEnergy_bddBelow`):
   Because `evenCoeff Z (scaledBumpPolarFree w 0) z = (1/4 - z²)² evenCoeff Z (modScaledBump w 0) z`
   and `(1/4 - z²)² > 0` on real strip zeros `z ∈ (-1/2, 1/2)`, the unmodulated (`γ = 0`, `τ = -1`)
   one-parameter pole-free difference family `κ_{2,w}(t + v/2) - κ_{2,w}(t - v/2)` measures every
   quasi-RH abscissa `1/2 + σ` (`σ ≥ 0`) without any height or phase parameter, and sees every
   attained top along a single non-resonant geometric grid `v_k = kℓ`. Pairing with the polar
   Rayleigh bridge proves **unconditionally** that `μ₀(A) ≥ -C e^{2σA}` (`A ≥ A₀`) forces
   `|Re ρ - 1/2| ≤ σ` for all nontrivial zeros of `ζ`, sharpening the exponent of
   `CCMRestrictedWeilPolarBombieriYoshidaQuantitative` by the exact factor of `2`.

4. **Global Arithmetic Window Floor for All Apertures `A > 0` and All Lags `v > 2w`**
   (`profilePrimeSum_le_two_mul_aperturePrimeSum`,
   `aperturePrimeSum_le_four_mul_mul_exp`,
   `neg_poleFreeWeilOperator_ge_polarWindowFloor`,
   `polarWindowFloor_le_ccmRestrictedWeilPolarGroundEnergy`,
   `explicit_global_le_ccmRestrictedWeilPolarGroundEnergy`,
   `reflectedDifferenceEnergy_add_polarWindowFloor_le_poleFree_of_meanZero_Icc`,
   `two_mul_polarWindowFloor_le_arch_sub_primeWindow_polarFree`):
   Removes the `2R < log 2` restriction of `WindowGaugeLogarithmicGroundEnergyFloor` and the `4R³`
   odd-pole penalty on the pole-vanishing sector: at any aperture `R > 0`, the prime shift sum
   `profilePrimeSum M x` on `(-R, R)` truncates to `n ≤ ⌊e^{2R}⌋` and is bounded by
   `2 Σ_{n ≤ ⌊e^{2R}⌋} Λ(n) n^{-1/2} ≤ 8 R e^R`. Consequently, for **every** aperture `A > 0` and
   **every** lag `v > 2w`, the pole-vanishing ground energy `μ₀(A)`, the `μ_a`-mean-zero variation
   inequality, and the pole-free dyadic prime window functional obey explicit global arithmetic
   lower bounds governed by `polarWindowFloor(A) ≥ -log(2A) - (3/2)A - (γ + log π) - 8 A e^A`.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate InnerProduct
open Zeta23 _root_.RHTower _root_.RHTower.CHMDPolar
open GaloisForLFunctions.ArithmeticCriticalityTheory

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

/-! ### Smoothness and generic parameter helpers -/

private theorem exists_mem_Ioo_notMem_of_countable' {a b : ℝ} (hab : a < b) {E : Set ℝ}
    (hE : E.Countable) : ∃ x ∈ Ioo a b, x ∉ E := by
  by_contra h
  push Not at h
  have h0 : volume (Ioo a b) = 0 := measure_mono_null h (hE.measure_zero volume)
  rw [Real.volume_Ioo] at h0
  have : b - a ≤ 0 := ENNReal.ofReal_eq_zero.mp h0
  linarith

private theorem exists_good_width' (Z : ZeroConfig) :
    ∃ w : ℝ, 0 < w ∧ 2 * w < Real.log 2 ∧
      ∀ ρ ∈ Z.carrier, ρ.re ≠ 1 / 2 → paperFT (scaledBump w) (gammaOf ρ) ≠ 0 := by
  obtain ⟨w, ⟨hw0, hw2⟩, hwE⟩ := exists_mem_Ioo_notMem_of_countable'
    (half_pos (Real.log_pos one_lt_two)) (countable_bad_widths Z)
  exact ⟨w, hw0, by linarith, fun ρ hρ hre h0 => hwE ⟨hw0, ρ, hρ, hre, h0⟩⟩

private theorem contDiff_top_weilBumpC' : ContDiff ℝ (⊤ : ℕ∞) weilBumpC :=
  Complex.ofRealCLM.contDiff.comp weilBump.contDiff

private theorem contDiff_top_scaledBump' (w : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (scaledBump w) :=
  contDiff_top_weilBumpC'.comp (contDiff_id.div_const _)

private theorem contDiff_top_modScaledBump' (w ω : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (modScaledBump w ω) := by
  unfold modScaledBump
  refine ContDiff.mul ?_ (contDiff_top_scaledBump' w)
  have : ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => -(I * (ω : ℂ) * (u : ℂ))) :=
    (contDiff_const.mul Complex.ofRealCLM.contDiff).neg
  exact Complex.contDiff_exp.comp this

/-- The modulated polar-free bump `κ_{2,w,ω} = κ_{w,ω}'' - κ_{w,ω}/4` is `C^∞`. -/
theorem contDiff_top_scaledBumpPolarFree (w ω : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (scaledBumpPolarFree w ω) := by
  unfold scaledBumpPolarFree
  exact (contDiff_top_modScaledBump' w ω).deriv'.deriv'.sub
    ((contDiff_top_modScaledBump' w ω).div_const 4)

private theorem contDiff_top_bumpTest' {β : ℝ → ℂ} (hβ : ContDiff ℝ (⊤ : ℕ∞) β) (ℓ : ℝ) {n : ℕ}
    (c : Fin n → ℂ) : ContDiff ℝ (⊤ : ℕ∞) (bumpTest β ℓ c) := by
  unfold bumpTest
  exact ContDiff.sum fun i _ => contDiff_const.mul (hβ.comp (contDiff_id.sub contDiff_const))

/-! ### Closed-aperture polar-constrained Rayleigh bridge and closed-support mean-zero variation -/

/-- The `+1/2` polar Riesz inner product of a smooth interior source is `paperFT u (-I/2)`. -/
theorem inner_ccmPolarApertureVector_half_eq_paperFT_neg_half_I {A : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource A) :
    inner ℂ (ccmPolarApertureVector A (1 / 2))
        (ccmArchimedeanFormToAperture A u.toCCMFormVector) =
      paperFT u (-(I / 2)) := by
  rw [inner_ccmPolarApertureVector_ccmComplexSmoothFormVector]
  unfold paperFT
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  have hexp : cexp (I * -(I / 2) * (x : ℂ)) = (Real.exp (1 / 2 * x) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    calc I * -(I / 2) * (x : ℂ) = -(I ^ 2) / 2 * (x : ℂ) := by ring
      _ = ((1 / 2 * x : ℝ) : ℂ) := by rw [Complex.I_sq]; push_cast; ring
  dsimp only
  rw [hexp, mul_comm]

/-- The `-1/2` polar Riesz inner product of a smooth interior source is `paperFT u (I/2)`. -/
theorem inner_ccmPolarApertureVector_neg_half_eq_paperFT_half_I {A : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource A) :
    inner ℂ (ccmPolarApertureVector A (-1 / 2))
        (ccmArchimedeanFormToAperture A u.toCCMFormVector) =
      paperFT u (I / 2) := by
  rw [inner_ccmPolarApertureVector_ccmComplexSmoothFormVector]
  unfold paperFT
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  have hexp : cexp (I * (I / 2) * (x : ℂ)) = (Real.exp (-1 / 2 * x) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    calc I * (I / 2) * (x : ℂ) = I ^ 2 / 2 * (x : ℂ) := by ring
      _ = ((-1 / 2 * x : ℝ) : ℂ) := by rw [Complex.I_sq]; push_cast; ring
  dsimp only
  rw [hexp, mul_comm]

/-- A smooth interior source whose Fourier transform vanishes at `±I/2` is polar-constrained. -/
theorem isPolarConstrained_of_paperFT_half_I_eq_zero {A : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource A) (hp : paperFT u (I / 2) = 0)
    (hn : paperFT u (-(I / 2)) = 0) :
    IsPolarConstrained A u.toCCMFormVector := by
  refine ⟨?_, ?_⟩
  · rw [inner_ccmPolarApertureVector_half_eq_paperFT_neg_half_I, hn]
  · rw [inner_ccmPolarApertureVector_neg_half_eq_paperFT_half_I, hp]

/-- **Closed-aperture polar-constrained Rayleigh inequality.** For every aperture `A` and every
smooth test `g` supported in `[-A, A]` with `paperFT g (±I/2) = 0`,
`μ₀(A) ∫ ‖g‖² ≤ Re W_ζ(g, g)`. -/
theorem ccmRestrictedWeilPolarGroundEnergy_mul_integral_norm_sq_le_re_W
    {A : SuzukiPositiveAperture} {g : ℝ → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgs : tsupport g ⊆ Icc (-A.1) A.1) (hp : paperFT g (I / 2) = 0)
    (hn : paperFT g (-(I / 2)) = 0) :
    ccmRestrictedWeilPolarGroundEnergy A * ∫ x, ‖g x‖ ^ 2 ≤ (zetaZeroConfig.W g g).re := by
  have hgc : HasCompactSupport g := hasCompactSupport_of_tsupport_subset_Icc hgs
  have hseq : ∀ n : ℕ,
      ccmRestrictedWeilPolarGroundEnergy (suzukiRightAperture A n) * ∫ x, ‖g x‖ ^ 2 ≤
        (zetaZeroConfig.W g g).re := by
    intro n
    have hgt := suzukiRightAperture_gt A n
    have hsub : tsupport g ⊆ Ioo (-(suzukiRightAperture A n).1) (suzukiRightAperture A n).1 :=
      hgs.trans fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
    let u : CCMComplexSmoothInteriorSource (suzukiRightAperture A n) := ⟨g, hg, hgc, hsub⟩
    have hpol : IsPolarConstrained (suzukiRightAperture A n) u.toCCMFormVector :=
      isPolarConstrained_of_paperFT_half_I_eq_zero u hp hn
    have h := ccmRestrictedWeilPolarGroundEnergy_mul_le (suzukiRightAperture A n)
      u.toCCMFormVector hpol
    rwa [norm_sq_ccmArchimedeanFormToAperture_toCCMFormVector,
      ccmRestrictedWeilSource_complexSmooth_eq_zetaWeil] at h
  exact le_of_tendsto
    ((tendsto_ccmRestrictedWeilPolarGroundEnergy_suzukiRightAperture A).mul_const _)
    (Eventually.of_forall hseq)

/-- **Closed-aperture pole-vanishing floor for `fullZeroForm`.** For every real smooth `F` supported
in the closed interval `[-A, A]` with `evenPoleMoment F = 0` and `oddPoleMoment F = 0`,
`μ₀(A) ∫ F² ≤ fullZeroForm F`. -/
theorem polarGroundEnergy_mul_le_fullZeroForm_Icc (A : SuzukiPositiveAperture) {F : ℝ → ℝ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hFs : tsupport F ⊆ Icc (-A.1) A.1)
    (hC : evenPoleMoment F = 0) (hS : oddPoleMoment F = 0) :
    ccmRestrictedWeilPolarGroundEnergy A * ∫ x, F x ^ 2 ≤ fullZeroForm F := by
  have hFc : HasCompactSupport F := IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport F) hFs
  have hseq : ∀ n : ℕ,
      ccmRestrictedWeilPolarGroundEnergy (suzukiRightAperture A n) * ∫ x, F x ^ 2 ≤
        fullZeroForm F := by
    intro n
    have hgt := suzukiRightAperture_gt A n
    have hsub : tsupport F ⊆ Ioo (-(suzukiRightAperture A n).1) (suzukiRightAperture A n).1 :=
      hFs.trans fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
    exact polarGroundEnergy_mul_le_fullZeroForm (suzukiRightAperture A n) hF hFc hsub hC hS
  exact le_of_tendsto
    ((tendsto_ccmRestrictedWeilPolarGroundEnergy_suzukiRightAperture A).mul_const _)
    (Eventually.of_forall hseq)

/-- **Closed-aperture mean-zero variation inequality.** For every shift `a > 0` and every smooth
even `μ_a`-mean-zero profile `u` supported in the closed interval `[-A, A]`,
`D_a(u) + μ₀(A) ∫ (m_a u)² ≤ 2 S_a(u) + V_a(u)`. -/
theorem reflectedDifferenceEnergy_add_le_poleFree_of_meanZero_Icc {a : ℝ} {u : ℝ → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (heven : ∀ x, u (-x) = u x) (hmean : profileMoment a u = 0)
    (ha : 0 < a) (A : SuzukiPositiveAperture) (hsupp : tsupport u ⊆ Icc (-A.1) A.1) :
    reflectedDifferenceEnergy (shiftedGroundState a) u +
        ccmRestrictedWeilPolarGroundEnergy A *
          ∫ x, phiDoobTest (fun y => shiftedGroundState a y * u y) x ^ 2 ≤
      2 * sameSideEnergy (shiftedGroundState a) u + profileVariance a u := by
  have huc : HasCompactSupport u := IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport u) hsupp
  have hseq : ∀ n : ℕ,
      reflectedDifferenceEnergy (shiftedGroundState a) u +
          ccmRestrictedWeilPolarGroundEnergy (suzukiRightAperture A n) *
            ∫ x, phiDoobTest (fun y => shiftedGroundState a y * u y) x ^ 2 ≤
        2 * sameSideEnergy (shiftedGroundState a) u + profileVariance a u := by
    intro n
    have hgt := suzukiRightAperture_gt A n
    have hsub : tsupport u ⊆ Ioo (-(suzukiRightAperture A n).1) (suzukiRightAperture A n).1 :=
      hsupp.trans fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
    exact reflectedDifferenceEnergy_add_le_poleFree_of_meanZero hu huc heven hmean ha
      (suzukiRightAperture A n) hsub
  exact le_of_tendsto
    (tendsto_const_nhds.add
      ((tendsto_ccmRestrictedWeilPolarGroundEnergy_suzukiRightAperture A).mul_const _))
    (Eventually.of_forall hseq)

/-- **Exact closed prime-free threshold `[−½ log 2, ½ log 2]` for mean-zero profiles.** Every
smooth even `μ_a`-mean-zero profile supported in `[−½ log 2, ½ log 2]` satisfies the variation
inequality with margin `1/10`, extending `reflectedDifferenceEnergy_add_le_poleFree_of_support_le_third`
from `1/3` to the full prime-free threshold `½ log 2`. -/
theorem reflectedDifferenceEnergy_add_le_poleFree_of_support_le_halfLogTwo {a : ℝ} {u : ℝ → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (heven : ∀ x, u (-x) = u x) (hmean : profileMoment a u = 0)
    (ha : 0 < a) (hsupp : tsupport u ⊆ Icc (-(Real.log 2 / 2)) (Real.log 2 / 2)) :
    reflectedDifferenceEnergy (shiftedGroundState a) u +
        1 / 10 * ∫ x, phiDoobTest (fun y => shiftedGroundState a y * u y) x ^ 2 ≤
      2 * sameSideEnergy (shiftedGroundState a) u + profileVariance a u := by
  have h := reflectedDifferenceEnergy_add_le_poleFree_of_meanZero_Icc hu heven hmean ha
    halfLogTwoAperture hsupp
  have hI : 0 ≤ ∫ x, phiDoobTest (fun y => shiftedGroundState a y * u y) x ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  nlinarith [one_tenth_le_ccmRestrictedWeilPolarGroundEnergy_halfLogTwo]

/-- **Full closed prime-2 aperture `[−½(log 2 + 1/50), ½(log 2 + 1/50)]` for mean-zero profiles.**
Every smooth even `μ_a`-mean-zero profile supported in `[−½(log 2 + 1/50), ½(log 2 + 1/50)]`
satisfies the variation inequality with margin `1/20`, extending
`reflectedDifferenceEnergy_add_le_poleFree_of_support_le_seven_twentieths` from `7/20 = 0.35` to the
full certified aperture `(log 2 + 1/50)/2 > 0.3565`. -/
theorem reflectedDifferenceEnergy_add_le_poleFree_of_support_le_primeTwo {a : ℝ} {u : ℝ → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (heven : ∀ x, u (-x) = u x) (hmean : profileMoment a u = 0)
    (ha : 0 < a)
    (hsupp : tsupport u ⊆ Icc (-((Real.log 2 + 1 / 50) / 2)) ((Real.log 2 + 1 / 50) / 2)) :
    reflectedDifferenceEnergy (shiftedGroundState a) u +
        1 / 20 * ∫ x, phiDoobTest (fun y => shiftedGroundState a y * u y) x ^ 2 ≤
      2 * sameSideEnergy (shiftedGroundState a) u + profileVariance a u := by
  have h := reflectedDifferenceEnergy_add_le_poleFree_of_meanZero_Icc hu heven hmean ha
    primeTwoAperture hsupp
  have hI : 0 ≤ ∫ x, phiDoobTest (fun y => shiftedGroundState a y * u y) x ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  nlinarith [one_twentieth_le_ccmRestrictedWeilPolarGroundEnergy_primeTwo]

/-! ### Polar Rayleigh bridge to pole-free two-bump tests and dyadic prime windows past the prime 2 -/

/-- Support of the polar-free two-bump test `κ_{2,w,ω}(t + v/2) + τ κ_{2,w,ω}(t − v/2)` lies in
`[−(v/2 + w), v/2 + w]`. -/
theorem tsupport_twoBump_scaledBumpPolarFree_subset {w : ℝ} (hw : 0 < w) (ω : ℝ) {v : ℝ}
    (hv : 0 ≤ v) (τ : ℂ) :
    tsupport (twoBump (scaledBumpPolarFree w ω) v τ) ⊆ Icc (-(v / 2 + w)) (v / 2 + w) :=
  tsupport_bumpTest_subset (scaledBumpPolarFree_support hw ω) hv
    (a := v / 2 + w) (n := 2) (by push_cast; linarith) ![1, τ]

/-- For disjoint bumps (`2w < v`), the `L²` mass of the polar-free difference two-bump test is
`2 ∫ ‖κ_{2,w,ω}‖²`. -/
theorem integral_norm_sq_twoBump_scaledBumpPolarFree_eq {w v : ℝ} (hw : 0 < w) (ω : ℝ)
    (hv : 2 * w < v) :
    (∫ t, ‖twoBump (scaledBumpPolarFree w ω) v (-1) t‖ ^ 2) =
      2 * ∫ t, ‖scaledBumpPolarFree w ω t‖ ^ 2 := by
  have hbs := scaledBumpPolarFree_support hw ω
  have hb : Continuous (scaledBumpPolarFree w ω) := (contDiff_scaledBumpPolarFree w ω).continuous
  have hbc : HasCompactSupport (scaledBumpPolarFree w ω) :=
    hasCompactSupport_of_support_subset_abs hbs
  have hv0 : 0 < v := by linarith
  have h := weilTest_twoBump_neg_one hb hbc v 0
  rw [weilTest_self_zero, weilTest_self_zero, zero_add, zero_sub,
    weilTest_self_eq_zero_of_lt hbs (by rw [abs_of_pos hv0]; exact hv),
    weilTest_self_eq_zero_of_lt hbs (by rw [abs_neg, abs_of_pos hv0]; exact hv),
    sub_zero, sub_zero] at h
  exact_mod_cast h

/-- Exact polar Rayleigh lower bound on the polar-free two-bump test at aperture `v / 2 + w`. -/
theorem ccmRestrictedWeilPolarGroundEnergy_mul_le_re_W_polarFree_twoBump {w v : ℝ} (hw : 0 < w)
    (ω : ℝ) (hv : 0 ≤ v) (τ : ℂ) :
    ccmRestrictedWeilPolarGroundEnergy ⟨v / 2 + w, by positivity⟩ *
        ∫ t, ‖twoBump (scaledBumpPolarFree w ω) v τ t‖ ^ 2 ≤
      (zetaZeroConfig.W (twoBump (scaledBumpPolarFree w ω) v τ)
        (twoBump (scaledBumpPolarFree w ω) v τ)).re := by
  obtain ⟨hp, hn⟩ := paperFT_scaledBumpPolarFree_half hw ω
  have hb : Continuous (scaledBumpPolarFree w ω) := (contDiff_scaledBumpPolarFree w ω).continuous
  have hbc : HasCompactSupport (scaledBumpPolarFree w ω) :=
    hasCompactSupport_of_support_subset_abs (scaledBumpPolarFree_support hw ω)
  exact ccmRestrictedWeilPolarGroundEnergy_mul_integral_norm_sq_le_re_W
    (contDiff_top_bumpTest' (contDiff_top_scaledBumpPolarFree w ω) v ![1, τ])
    (tsupport_twoBump_scaledBumpPolarFree_subset hw ω hv τ)
    (paperFT_twoBump_eq_zero hb hbc v τ hp)
    (paperFT_twoBump_eq_zero hb hbc v τ hn)

/-- For disjoint bumps (`2w < v`), the polar-free difference two-bump Weil form is bounded below by
`2 ‖κ_{2,w,ω}‖₂² μ₀(v/2 + w)`. -/
theorem two_mul_ccmRestrictedWeilPolarGroundEnergy_le_re_W_polarFree_twoBump {w v : ℝ}
    (hw : 0 < w) (ω : ℝ) (hv : 2 * w < v) :
    2 * (∫ t, ‖scaledBumpPolarFree w ω t‖ ^ 2) *
        ccmRestrictedWeilPolarGroundEnergy ⟨v / 2 + w, by linarith⟩ ≤
      (zetaZeroConfig.W (twoBump (scaledBumpPolarFree w ω) v (-1))
        (twoBump (scaledBumpPolarFree w ω) v (-1))).re := by
  have h := ccmRestrictedWeilPolarGroundEnergy_mul_le_re_W_polarFree_twoBump hw ω
    (by linarith : 0 ≤ v) (-1)
  rw [integral_norm_sq_twoBump_scaledBumpPolarFree_eq hw ω hv] at h
  linarith

/-- On any polar-free two-bump test (`2w < log 2`, `v ≥ 0`), `Re W_ζ` equals the archimedean term
minus the dyadic prime window sum of `polarFreeKernel w ω v τ` (with zero pole terms). -/
theorem zeta_re_W_polarFree_twoBump_eq_arch_sub_primeWindow {w : ℝ} (hw : 0 < w)
    (hw2 : 2 * w < Real.log 2) (ω : ℝ) {v : ℝ} (hv : 0 ≤ v) (τ : ℂ) :
    (zetaZeroConfig.W (twoBump (scaledBumpPolarFree w ω) v τ)
      (twoBump (scaledBumpPolarFree w ω) v τ)).re =
      ((1 / (2 * π) : ℂ) * ∫ r : ℝ, paperFT (polarFreeKernel w ω v τ) r *
        (EF.gammaBracket r : ℂ)).re -
      (∑ n ∈ lagPrimeWindow v w, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
        (polarFreeKernel w ω v τ (Real.log n) + polarFreeKernel w ω v τ (-Real.log n))).re := by
  have hc := (contDiff_scaledBumpPolarFree w ω).continuous
  have hbc := hasCompactSupport_of_support_subset_abs (scaledBumpPolarFree_support hw ω)
  have hfc := hasCompactSupport_twoBump hbc v τ
  have hfcont : Continuous (twoBump (scaledBumpPolarFree w ω) v τ) :=
    (contDiff_bumpTest (contDiff_scaledBumpPolarFree w ω) v ![1, τ]).continuous
  obtain ⟨hp, hn⟩ := paperFT_scaledBumpPolarFree_half hw ω
  have hpole : ∀ z : ℂ, paperFT (twoBump (scaledBumpPolarFree w ω) v τ) z = 0 →
      paperFT (polarFreeKernel w ω v τ) z = 0 := fun z hz => by
    rw [polarFreeKernel, EF.paperFT_weilTest hfcont hfcont hfc hfc, hz, zero_mul]
  rw [zeta_W_eq_literatureRHS (f := twoBump (scaledBumpPolarFree w ω) v τ)
    (contDiff_bumpTest (contDiff_scaledBumpPolarFree w ω) v ![1, τ]) hfc,
    literatureRHS_twoBump_eq_lagPrimeWindowRHS (scaledBumpPolarFree_support hw ω) hw2 hv,
    lagPrimeWindowRHS, ← polarFreeKernel,
    hpole _ (paperFT_twoBump_eq_zero hc hbc v τ hp),
    hpole _ (by rw [neg_div]; exact paperFT_twoBump_eq_zero hc hbc v τ hn)]
  simp only [add_zero, zero_sub, Complex.add_re, Complex.neg_re]
  ring

/-- **Polar Rayleigh–Prime-Window Bridge.** For `0 < w`, `2w < log 2`, and `2w < v`, the
archimedean-minus-prime window functional of `polarFreeKernel w ω v (-1)` is bounded below by
`2 ‖κ_{2,w,ω}‖₂² μ₀(v/2 + w)`. -/
theorem two_mul_ccmRestrictedWeilPolarGroundEnergy_le_arch_sub_primeWindow_polarFree {w v : ℝ}
    (hw : 0 < w) (hw2 : 2 * w < Real.log 2) (ω : ℝ) (hv : 2 * w < v) :
    2 * (∫ t, ‖scaledBumpPolarFree w ω t‖ ^ 2) *
        ccmRestrictedWeilPolarGroundEnergy ⟨v / 2 + w, by linarith⟩ ≤
      ((1 / (2 * π) : ℂ) * ∫ r : ℝ, paperFT (polarFreeKernel w ω v (-1)) r *
        (EF.gammaBracket r : ℂ)).re -
      (∑ n ∈ lagPrimeWindow v w, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
        (polarFreeKernel w ω v (-1) (Real.log n) +
          polarFreeKernel w ω v (-1) (-Real.log n))).re := by
  have h := two_mul_ccmRestrictedWeilPolarGroundEnergy_le_re_W_polarFree_twoBump hw ω hv
  rwa [zeta_re_W_polarFree_twoBump_eq_arch_sub_primeWindow hw hw2 ω (by linarith) (-1)] at h

/-- **Prime-free aperture floor (`v / 2 + w ≤ ½ log 2`) on pole-free dyadic windows.** -/
theorem one_fifth_mul_le_arch_sub_primeWindow_polarFree_of_le_halfLogTwo {w v : ℝ} (hw : 0 < w)
    (ω : ℝ) (hv : 2 * w < v) (hvw : v / 2 + w ≤ Real.log 2 / 2) :
    1 / 5 * ∫ t, ‖scaledBumpPolarFree w ω t‖ ^ 2 ≤
      ((1 / (2 * π) : ℂ) * ∫ r : ℝ, paperFT (polarFreeKernel w ω v (-1)) r *
        (EF.gammaBracket r : ℂ)).re -
      (∑ n ∈ lagPrimeWindow v w, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
        (polarFreeKernel w ω v (-1) (Real.log n) +
          polarFreeKernel w ω v (-1) (-Real.log n))).re := by
  have hw2 : 2 * w < Real.log 2 := by linarith
  have hray := two_mul_ccmRestrictedWeilPolarGroundEnergy_le_arch_sub_primeWindow_polarFree
    hw hw2 ω hv
  have hfloor : (1 / 10 : ℝ) ≤ ccmRestrictedWeilPolarGroundEnergy ⟨v / 2 + w, by linarith⟩ :=
    one_tenth_le_ccmRestrictedWeilPolarGroundEnergy_halfLogTwo.trans
      (ccmRestrictedWeilPolarGroundEnergy_antitone hvw)
  have hB0 : 0 ≤ ∫ t, ‖scaledBumpPolarFree w ω t‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  nlinarith

/-- **Height-uniform positivity of pole-free dyadic prime windows past the entry of the prime `2`
(`v / 2 + w ≤ ½(log 2 + 1/50)`).** For `0 < w`, `2w < log 2`, `2w < v`, and
`v / 2 + w ≤ (log 2 + 1/50) / 2`, the archimedean term exceeds the dyadic prime window sum of
`polarFreeKernel w ω v (-1)` by at least `(1/10) ∫ ‖κ_{2,w,ω}‖²`, uniformly over all heights `ω`. -/
theorem one_tenth_mul_le_arch_sub_primeWindow_polarFree_of_le_primeTwo {w v : ℝ} (hw : 0 < w)
    (hw2 : 2 * w < Real.log 2) (ω : ℝ) (hv : 2 * w < v)
    (hvw : v / 2 + w ≤ (Real.log 2 + 1 / 50) / 2) :
    1 / 10 * ∫ t, ‖scaledBumpPolarFree w ω t‖ ^ 2 ≤
      ((1 / (2 * π) : ℂ) * ∫ r : ℝ, paperFT (polarFreeKernel w ω v (-1)) r *
        (EF.gammaBracket r : ℂ)).re -
      (∑ n ∈ lagPrimeWindow v w, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
        (polarFreeKernel w ω v (-1) (Real.log n) +
          polarFreeKernel w ω v (-1) (-Real.log n))).re := by
  have hray := two_mul_ccmRestrictedWeilPolarGroundEnergy_le_arch_sub_primeWindow_polarFree
    hw hw2 ω hv
  have hfloor := one_twentieth_le_ccmRestrictedWeilPolarGroundEnergy_of_le_primeTwo
    ⟨v / 2 + w, by linarith⟩ hvw
  have hB0 : 0 ≤ ∫ t, ‖scaledBumpPolarFree w ω t‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  nlinarith

/-! ### The one-parameter pole-free lag family (`γ = 0`, `τ = -1`) measures the abscissa -/

/-- For a real exponent `z` (`z.im = 0`) in the open strip `(-1/2, 1/2)`, `(1/4 - z²)²` is a
strictly positive real number `(1/4 - z.re²)² > 0`. -/
theorem one_fourth_sub_sq_eq_of_im_eq_zero {z : ℂ} (him : z.im = 0) :
    (1 / 4 - z ^ 2) ^ 2 = (((1 / 4 - z.re ^ 2) ^ 2 : ℝ) : ℂ) := by
  have hz : z = (z.re : ℂ) := Complex.ext rfl (by simp [him])
  conv_lhs => rw [hz]
  push_cast
  ring

/-- For a real exponent `z` (`z.im = 0`) of a zero `1/2 + z ∈ Z.carrier` in the open critical strip
`0 < Re ρ < 1`, the merged coefficient of `scaledBumpPolarFree w 0` has strictly positive real
part. -/
theorem re_evenCoeff_scaledBumpPolarFree_zero_pos (Z : ZeroConfig)
    (hlt : ∀ ρ ∈ Z.carrier, ρ.re < 1) {w : ℝ} (hw : 0 < w) {z : ℂ}
    (hz : (1 / 2 + z) ∈ Z.carrier) (hz0 : -1 / 2 < z.re) (him : z.im = 0) :
    0 < (evenCoeff Z (scaledBumpPolarFree w 0) z).re := by
  have h2 : (1 / 2 + z).re < 1 := hlt _ hz
  simp only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re] at h2
  have hsq : z.re ^ 2 < 1 / 4 := by nlinarith
  have hpos : 0 < (1 / 4 - z.re ^ 2) ^ 2 := sq_pos_of_pos (by linarith)
  rw [evenCoeff_scaledBumpPolarFree Z hw 0 z, one_fourth_sub_sq_eq_of_im_eq_zero him,
    Complex.re_ofReal_mul]
  exact mul_pos hpos (re_evenCoeff_modScaledBump_zero_pos Z hw hz him)

/-- Every zero `ρ ∈ Z.carrier` in the open strip `0 < Re ρ < 1` with `paperFT (scaledBump w) (gammaOf ρ) ≠ 0`
has a nonzero merged coefficient for the unmodulated polar-free bump `scaledBumpPolarFree w 0`. -/
theorem evenCoeff_scaledBumpPolarFree_zero_sub_half_ne_zero (Z : ZeroConfig)
    (hlt : ∀ ρ ∈ Z.carrier, ρ.re < 1) {w : ℝ} (hw : 0 < w) {ρ : ℂ} (hρ : ρ ∈ Z.carrier)
    (hre0 : 0 < ρ.re) (hg : paperFT (scaledBump w) (gammaOf ρ) ≠ 0) :
    evenCoeff Z (scaledBumpPolarFree w 0) (ρ - 1 / 2) ≠ 0 := by
  rw [evenCoeff_scaledBumpPolarFree Z hw 0 (ρ - 1 / 2)]
  refine mul_ne_zero (pow_ne_zero 2 ?_)
    (evenCoeff_modScaledBump_zero_sub_half_ne_zero Z hw hρ hg)
  intro h0
  have hfac : ρ * (1 - ρ) = 0 := by linear_combination h0
  have hre1 : ρ.re < 1 := hlt ρ hρ
  rcases mul_eq_zero.mp hfac with rfl | h1
  · simp at hre0
  · have : ρ = 1 := by linear_combination -h1
    subst this
    simp at hre1

/-- **No exponent beyond the rate for the one-parameter pole-free lag family.** If `Z` is tempered
with zeros in `0 < Re ρ < 1` and `Re W ≥ -C e^{σv}` on the unmodulated polar-free difference tests
`κ_{2,w}(t + v/2) - κ_{2,w}(t - v/2)` for all `v ≥ V` (`σ ≥ 0`), then `evenCoeff Z κ_{2,w} z = 0`
whenever `Re z > σ`. -/
theorem evenCoeff_eq_zero_of_polarFree_lag_ge_neg_exp (Z : ZeroConfig) (hZ : TemperedConfig Z)
    (hlt : ∀ ρ ∈ Z.carrier, ρ.re < 1) {w : ℝ} (hw : 0 < w) {σ C V : ℝ} (hσ : 0 ≤ σ)
    (hm : ∀ v : ℝ, V ≤ v → -(C * Real.exp (σ * v)) ≤
      (Z.W (twoBump (scaledBumpPolarFree w 0) v (-1))
        (twoBump (scaledBumpPolarFree w 0) v (-1))).re)
    {z : ℂ} (hz : σ < z.re) : evenCoeff Z (scaledBumpPolarFree w 0) z = 0 := by
  classical
  set b := scaledBumpPolarFree w 0 with hbdef
  have hb : ContDiff ℝ 2 b := contDiff_scaledBumpPolarFree w 0
  have hbs := scaledBumpPolarFree_support hw 0
  obtain ⟨M, hM0, hMb⟩ := exists_two_re_lagStructure_le_exp Z hZ hb hbs hσ hm
  have hhalf : ∀ x : ℂ, evenCoeff Z b x ≠ 0 → x.re < 1 / 2 := fun x hx => by
    rcases mem_of_evenCoeff_ne_zero hx with h | h
    · have := hlt _ h; simp at this; linarith
    · have := hlt _ h; simp at this; linarith
  by_contra hne
  have hσh : σ < 1 / 2 := hz.trans (hhalf z hne)
  set R := (finite_evenCoeff_line Z b 0).toFinset.filter fun x => σ < x.re with hR
  have hmemR : ∀ x : ℂ, evenCoeff Z b x ≠ 0 → x.im = 0 → σ < x.re → x ∈ R := fun x hx him hre =>
    Finset.mem_filter.mpr ⟨(Set.Finite.mem_toFinset _).mpr ⟨hx, him⟩, hre⟩
  by_cases hRne : R.Nonempty
  · obtain ⟨x₀, hx₀R, hmax⟩ := R.exists_max_image Complex.re hRne
    obtain ⟨hx₀L, hx₀σ⟩ := Finset.mem_filter.mp hx₀R
    obtain ⟨hx₀, hx₀im⟩ := (Set.Finite.mem_toFinset _).mp hx₀L
    have habove : ∀ y : ℂ, x₀.re < y.re → evenCoeff Z b y = 0 := fun y hy =>
      evenCoeff_eq_zero_of_two_re_lagStructure_le_exp Z hZ hb hbs (hσ.trans hx₀σ.le)
        (hhalf x₀ hx₀) (fun x hx him => by
          by_contra h
          push Not at h
          exact absurd (hmax x (hmemR x hx him (hx₀σ.trans h))) (not_le.mpr h))
        (fun u hu => (hMb u hu).trans (mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hx₀σ.le hu)) hM0)) hy
    set ι : Set ℂ := {z | evenCoeff Z b z ≠ 0} with hι
    haveI : Countable ι := (countable_evenCoeff_support Z b).to_subtype
    have hD0 : Summable fun z : ℂ => ‖evenCoeff Z b z‖ := by
      have h0 := (two_re_lagStructure_eq Z hZ hb hbs 0).1.norm
      simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one] at h0
      exact h0
    have hle : ∀ t : ι, ((t : ℂ) - σ).re ≤ x₀.re - σ := fun t => by
      by_contra h
      have : x₀.re < (t : ℂ).re := by simp at h; linarith
      exact t.2 (habove _ this)
    have hrep : ∀ v : ℝ, 0 ≤ v →
        (∑' t : ι, evenCoeff Z b t * cexp (((t : ℂ) - σ) * v)).re ≤ M := fun v hv => by
      have hsub : Function.support (fun z : ℂ => evenCoeff Z b z * cexp (z * v)) ⊆ ι :=
        fun z hz h0 => hz (show evenCoeff Z b z * cexp (z * v) = 0 by rw [h0, zero_mul])
      have e1 : ∑' t : ι, evenCoeff Z b t * cexp (((t : ℂ) - σ) * v) =
          ((Real.exp (-σ * v) * (2 * (lagStructure Z b v).re) : ℝ) : ℂ) := by
        rw [Complex.ofReal_mul, (two_re_lagStructure_eq Z hZ hb hbs v).2,
          ← tsum_subtype_eq_of_support_subset hsub, ← tsum_mul_left]
        refine tsum_congr fun t => ?_
        rw [Complex.ofReal_exp, mul_left_comm, ← Complex.exp_add]
        congr 2
        push_cast
        ring
      rw [e1, Complex.ofReal_re]
      calc Real.exp (-σ * v) * (2 * (lagStructure Z b v).re)
          ≤ Real.exp (-σ * v) * (M * Real.exp (σ * v)) :=
            mul_le_mul_of_nonneg_left (hMb v hv) (Real.exp_pos _).le
        _ = M := by
            rw [mul_left_comm, ← Real.exp_add, show -σ * v + σ * v = 0 by ring, Real.exp_zero,
              mul_one]
    have hpos := re_evenCoeff_scaledBumpPolarFree_zero_pos Z hlt hw
      ((mem_of_evenCoeff_ne_zero hx₀).elim id fun h => by
        rwa [show conj x₀ = x₀ from Complex.ext (by simp) (by simp [hx₀im])] at h)
      (by linarith) hx₀im
    have hnonpos := re_le_zero_of_re_tsum_exp_le (ι := ι) (lam := fun t => (t : ℂ) - σ)
      (q := fun t => evenCoeff Z b t) (hD0.subtype ι) (σ := x₀.re - σ) (by linarith) hle
      ⟨x₀, hx₀⟩ (Complex.ext (by simp) (by simp [hx₀im]))
      (fun t ht => Subtype.ext (sub_left_injective ht)) hrep
    exact absurd hnonpos (not_le.mpr hpos)
  · exact hne (evenCoeff_eq_zero_of_two_re_lagStructure_le_exp Z hZ hb hbs hσ hσh
      (fun x hx him => by
        by_contra h
        push Not at h
        exact hRne ⟨x, hmemR x hx him h⟩) hMb hz)

/-- **The one-parameter pole-free lag family measures the abscissa.** For any tempered configuration
`Z` with `Re ρ < 1`, any good width `w > 0`, and any `σ ≥ 0`, every zero satisfies
`Re ρ ≤ 1/2 + σ` iff `Re W ≥ -C e^{σv}` on the unmodulated polar-free difference tests
`κ_{2,w}(t + v/2) - κ_{2,w}(t - v/2)` for all large `v`. -/
theorem re_le_iff_polarFree_lag_twoBump_ge_neg_exp (Z : ZeroConfig) (hZ : TemperedConfig Z)
    (hlt : ∀ ρ ∈ Z.carrier, ρ.re < 1) {w : ℝ} (hw : 0 < w)
    (hgood : ∀ ρ ∈ Z.carrier, ρ.re ≠ 1 / 2 → paperFT (scaledBump w) (gammaOf ρ) ≠ 0) {σ : ℝ}
    (hσ : 0 ≤ σ) :
    (∀ ρ ∈ Z.carrier, ρ.re ≤ 1 / 2 + σ) ↔ ∃ C V : ℝ, ∀ v : ℝ, V ≤ v → -(C * Real.exp (σ * v)) ≤
      (Z.W (twoBump (scaledBumpPolarFree w 0) v (-1))
        (twoBump (scaledBumpPolarFree w 0) v (-1))).re := by
  set b := scaledBumpPolarFree w 0 with hbdef
  have hb : ContDiff ℝ 2 b := contDiff_scaledBumpPolarFree w 0
  have hbs := scaledBumpPolarFree_support hw 0
  constructor
  · intro hre
    set A := 2 * (lagStructure Z b 0).re with hA
    set N := ∑' z : ℂ, ‖evenCoeff Z b z‖ with hN
    refine ⟨|A| + N, 0, fun v hv => ?_⟩
    have h := two_re_lagStructure_le_mul_exp Z hZ hb hbs (τ := σ) (fun z hz => by
      rcases mem_of_evenCoeff_ne_zero hz with h | h
      · have := hre _ h; simp at this; linarith
      · have := hre _ h; simp at this; linarith) hv
    have he1 : 1 ≤ Real.exp (σ * v) := Real.one_le_exp (mul_nonneg hσ hv)
    have h1 : |A| ≤ |A| * Real.exp (σ * v) := le_mul_of_one_le_right (abs_nonneg _) he1
    rw [re_W_lag_eq Z hZ hb hbs, add_mul]
    linarith [neg_abs_le A]
  · rintro ⟨C, V, hm⟩ ρ hρ
    by_contra hre
    push Not at hre
    exact evenCoeff_scaledBumpPolarFree_zero_sub_half_ne_zero Z hlt hw hρ (by linarith)
      (hgood ρ hρ (by linarith))
      (evenCoeff_eq_zero_of_polarFree_lag_ge_neg_exp Z hZ hlt hw hσ hm (by simp; linarith))

/-- **One-parameter pole-free dyadic prime window abscissa law for `ζ`.** For all but countably many
widths `w ∈ (0, ½ log 2)` and every `σ ≥ 0`, every nontrivial zero of `ζ` has `Re ρ ≤ 1/2 + σ` iff
for all large lags `v ≥ V`, the archimedean term minus the dyadic prime window sum of
`polarFreeKernel w 0 v (-1)` (with no height or phase parameter and no pole term) is `≥ -C e^{σv}`. -/
theorem zeta_re_le_iff_polarFree_lag_primeWindow_ge_neg_exp :
    ∃ E : Set ℝ, E.Countable ∧ ∀ w : ℝ, 0 < w → 2 * w < Real.log 2 → w ∉ E → ∀ σ : ℝ, 0 ≤ σ →
      ((∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ 1 / 2 + σ) ↔ ∃ C V : ℝ, 0 ≤ V ∧ ∀ v : ℝ, V ≤ v →
        -(C * Real.exp (σ * v)) ≤
          ((1 / (2 * π) : ℂ) * ∫ r : ℝ, paperFT (polarFreeKernel w 0 v (-1)) r *
            (EF.gammaBracket r : ℂ)).re -
          (∑ n ∈ lagPrimeWindow v w, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
            (polarFreeKernel w 0 v (-1) (Real.log n) +
              polarFreeKernel w 0 v (-1) (-Real.log n))).re) := by
  refine ⟨_, countable_bad_widths zetaZeroConfig, fun w hw hw2 hwE σ hσ => ?_⟩
  have hgood : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≠ 1 / 2 →
      paperFT (scaledBump w) (gammaOf ρ) ≠ 0 := fun ρ hρ hre h0 => hwE ⟨hw, ρ, hρ, hre, h0⟩
  have hlt : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re < 1 := fun ρ hρ => hρ.2.2
  rw [re_le_iff_polarFree_lag_twoBump_ge_neg_exp _ temperedConfig_zetaZeroConfig hlt hw hgood hσ]
  constructor
  · rintro ⟨C, V, h⟩
    exact ⟨C, max V 0, le_max_right _ _, fun v hv => by
      rw [← zeta_re_W_polarFree_twoBump_eq_arch_sub_primeWindow hw hw2 0
        ((le_max_right _ _).trans hv) (-1)]
      exact h v ((le_max_left _ _).trans hv)⟩
  · rintro ⟨C, V, hV, h⟩
    exact ⟨C, V, fun v hv => by
      rw [zeta_re_W_polarFree_twoBump_eq_arch_sub_primeWindow hw hw2 0 (hV.trans hv) (-1)]
      exact h v hv⟩

/-! ### Unconditional sharp `2σ`-abscissa law for `ccmRestrictedWeilPolarGroundEnergy` (`μ₀(A)`) -/

/-- **Unconditional sharp `2σ`-abscissa theorem for the pole-vanishing ground energy `μ₀(A)`.**
If `μ₀(A) ≥ -C e^{2σA}` for all `A ≥ A₀` (`σ ≥ 0`), then every nontrivial zero of `ζ` in the
critical strip satisfies `Re ρ ≤ 1/2 + σ`—sharpening the exponent of
`CCMRestrictedWeilPolarBombieriYoshidaQuantitative` by a factor of `2` and requiring the bound only
at large apertures `A ≥ A₀`. -/
theorem re_le_of_ccmRestrictedWeilPolarGroundEnergy_ge_neg_exp {σ C A₀ : ℝ} (hσ : 0 ≤ σ)
    (hμ₀ : ∀ A : SuzukiPositiveAperture, A₀ ≤ A.1 →
      -(C * Real.exp (2 * σ * A.1)) ≤ ccmRestrictedWeilPolarGroundEnergy A) :
    ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ 1 / 2 + σ := by
  obtain ⟨w, hw0, _, hgood⟩ := exists_good_width' zetaZeroConfig
  have hlt : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re < 1 := fun ρ hρ => hρ.2.2
  rw [re_le_iff_polarFree_lag_twoBump_ge_neg_exp _ temperedConfig_zetaZeroConfig hlt hw0 hgood hσ]
  set B := ∫ t, ‖scaledBumpPolarFree w 0 t‖ ^ 2 with hB
  have hB0 : 0 ≤ B := integral_nonneg fun _ => sq_nonneg _
  refine ⟨2 * B * max C 0 * Real.exp (2 * σ * w), max (2 * w + 1) (2 * (A₀ - w)), fun v hv => ?_⟩
  have hv2w : 2 * w < v := by linarith [le_max_left (2 * w + 1) (2 * (A₀ - w))]
  have hvA₀ : A₀ ≤ v / 2 + w := by linarith [le_max_right (2 * w + 1) (2 * (A₀ - w))]
  have hray := two_mul_ccmRestrictedWeilPolarGroundEnergy_le_re_W_polarFree_twoBump hw0 0 hv2w
  have hfloor := hμ₀ ⟨v / 2 + w, by linarith⟩ hvA₀
  have hC : C ≤ max C 0 := le_max_left _ _
  have hexp : Real.exp (2 * σ * (v / 2 + w)) = Real.exp (2 * σ * w) * Real.exp (σ * v) := by
    rw [← Real.exp_add]; congr 1; ring
  have h1 : -(2 * B * max C 0 * Real.exp (2 * σ * w) * Real.exp (σ * v)) ≤
      2 * B * ccmRestrictedWeilPolarGroundEnergy ⟨v / 2 + w, by linarith⟩ := by
    calc -(2 * B * max C 0 * Real.exp (2 * σ * w) * Real.exp (σ * v))
        = 2 * B * (-(max C 0 * Real.exp (2 * σ * (v / 2 + w)))) := by rw [hexp]; ring
      _ ≤ 2 * B * (-(C * Real.exp (2 * σ * (v / 2 + w)))) := by
          refine mul_le_mul_of_nonneg_left (neg_le_neg ?_) (by linarith)
          exact mul_le_mul_of_nonneg_right hC (Real.exp_pos _).le
      _ ≤ 2 * B * ccmRestrictedWeilPolarGroundEnergy ⟨v / 2 + w, by linarith⟩ :=
          mul_le_mul_of_nonneg_left hfloor (by linarith)
  linarith

/-- Symmetric strip bound `|Re ρ - 1/2| ≤ σ` from `μ₀(A) ≥ -C e^{2σA}` (`A ≥ A₀`). -/
theorem abs_re_sub_half_le_of_ccmRestrictedWeilPolarGroundEnergy_ge_neg_exp {σ C A₀ : ℝ}
    (hσ : 0 ≤ σ)
    (hμ₀ : ∀ A : SuzukiPositiveAperture, A₀ ≤ A.1 →
      -(C * Real.exp (2 * σ * A.1)) ≤ ccmRestrictedWeilPolarGroundEnergy A)
    {ρ : ℂ} (hρ : ρ ∈ zetaZeroConfig.carrier) :
    |ρ.re - 1 / 2| ≤ σ := by
  have h1 := re_le_of_ccmRestrictedWeilPolarGroundEnergy_ge_neg_exp hσ hμ₀ ρ hρ
  have h2 := re_le_of_ccmRestrictedWeilPolarGroundEnergy_ge_neg_exp hσ hμ₀ (Zeta23.reflect ρ)
    (zetaZeroConfig.reflect_mem ρ hρ)
  have hrefl : (Zeta23.reflect ρ).re = 1 - ρ.re := by simp [Zeta23.reflect]
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

/-- Unconditional sharp `2σ` bound on `|(xiSpectralPoint q).im|` from `μ₀(A) ≥ -C e^{2σA}`. -/
theorem abs_im_xiSpectralPoint_le_of_ccmRestrictedWeilPolarGroundEnergy_ge_neg_exp {σ C A₀ : ℝ}
    (hσ : 0 ≤ σ)
    (hμ₀ : ∀ A : SuzukiPositiveAperture, A₀ ≤ A.1 →
      -(C * Real.exp (2 * σ * A.1)) ≤ ccmRestrictedWeilPolarGroundEnergy A)
    (q : XiZeroCopy) :
    |(xiSpectralPoint q).im| ≤ σ := by
  have h := abs_re_sub_half_le_of_ccmRestrictedWeilPolarGroundEnergy_ge_neg_exp hσ hμ₀
    (xiZeroCopy_mem_carrier q)
  have him : (xiSpectralPoint q).im = 1 / 2 - (q.1 : ℂ).re := by simp [xiSpectralPoint]
  rw [him, ← abs_neg, show -(1 / 2 - (q.1 : ℂ).re) = (q.1 : ℂ).re - 1 / 2 by ring]
  exact h

/-- Contrapositive: any zero `ρ ∈ zetaZeroConfig.carrier` with `Re ρ > 1/2 + σ` (`σ ≥ 0`) forces
the pole-vanishing ground energy `μ₀(A) < -C e^{2σA}` at arbitrarily large apertures `A ≥ A₀`. -/
theorem exists_ccmRestrictedWeilPolarGroundEnergy_lt_neg_exp_of_re_gt {σ : ℝ} (hσ : 0 ≤ σ)
    {ρ : ℂ} (hρ : ρ ∈ zetaZeroConfig.carrier) (hre : 1 / 2 + σ < ρ.re) (C A₀ : ℝ) :
    ∃ A : SuzukiPositiveAperture, A₀ ≤ A.1 ∧
      ccmRestrictedWeilPolarGroundEnergy A < -(C * Real.exp (2 * σ * A.1)) := by
  by_contra hno
  push Not at hno
  have := re_le_of_ccmRestrictedWeilPolarGroundEnergy_ge_neg_exp hσ hno ρ hρ
  linarith

/-! ### Pole-free geometric lag grids and `ZerosApproachLine` splits -/

private theorem exists_xiZeroCopy_of_mem_zetaZeroConfig' {ρ : ℂ} (hρ : ρ ∈ zetaZeroConfig.carrier) :
    ∃ q : XiZeroCopy, (q.1 : ℂ) = ρ := by
  let d : XiDivisorSupport := xiDivisorZetaCarrierEquiv.symm ⟨ρ, hρ⟩
  refine ⟨⟨d, ⟨0, by have h := xi_divisor_pos_on_support d; omega⟩⟩, rfl⟩

private theorem riemannHypothesis_iff_zetaZeroConfig_onLine' :
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

private theorem attainedTop_iff_zetaZeroConfig' {β₀ : ℝ} :
    AttainedTop β₀ ↔
      (∃ ρ ∈ zetaZeroConfig.carrier, ρ.re = β₀) ∧
        ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ β₀ := by
  constructor
  · rintro ⟨⟨q₀, hq₀⟩, hmax⟩
    refine ⟨⟨q₀.1, xiZeroCopy_mem_carrier q₀, hq₀⟩, fun ρ hρ => ?_⟩
    obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_mem_zetaZeroConfig' hρ
    rw [← hq]
    exact hmax q
  · rintro ⟨⟨ρ₀, hρ₀, hre₀⟩, hmax⟩
    obtain ⟨q₀, hq₀⟩ := exists_xiZeroCopy_of_mem_zetaZeroConfig' hρ₀
    exact ⟨⟨q₀, by rw [hq₀, hre₀]⟩, fun q => hmax (q.1 : ℂ) (xiZeroCopy_mem_carrier q)⟩

/-- **Pole-free geometric lag grids see attained tops above `1/2 + σ`.** If `Re W ≥ -C e^{σ k ℓ}`
along the grid `v_k = kℓ` for the unmodulated polar-free difference tests
`κ_{2,w}(t + kℓ/2) - κ_{2,w}(t - kℓ/2)`, then every zero `ρ₀ ∈ Z.carrier` with
`1/2 + σ < Re ρ₀ < 1` is strictly exceeded in real part by another zero. -/
theorem exists_re_gt_of_grid_polarFree_lag_ge_neg_exp (Z : ZeroConfig) (hZ : TemperedConfig Z)
    (hlt : ∀ ρ ∈ Z.carrier, ρ.re < 1) {w : ℝ} (hw : 0 < w)
    (hgood : ∀ ρ ∈ Z.carrier, ρ.re ≠ 1 / 2 → paperFT (scaledBump w) (gammaOf ρ) ≠ 0) {ℓ : ℝ}
    (hℓ : 0 < ℓ) (hres : ℓ ∉ resonantSteps Z) {σ C : ℝ} (hσ : 0 ≤ σ) {N : ℕ}
    (hm : ∀ k : ℕ, N ≤ k → -(C * Real.exp (σ * (k * ℓ))) ≤
      (Z.W (twoBump (scaledBumpPolarFree w 0) (k * ℓ) (-1))
        (twoBump (scaledBumpPolarFree w 0) (k * ℓ) (-1))).re)
    {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ Z.carrier) (hre₀ : 1 / 2 + σ < ρ₀.re) :
    ∃ ρ ∈ Z.carrier, ρ₀.re < ρ.re := by
  classical
  by_contra hno
  push Not at hno
  set b := scaledBumpPolarFree w 0 with hbdef
  have hb : ContDiff ℝ 2 b := contDiff_scaledBumpPolarFree w 0
  have hbs := scaledBumpPolarFree_support hw 0
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
    evenCoeff_scaledBumpPolarFree_zero_sub_half_ne_zero Z hlt hw hρ₀ (by linarith)
      (hgood ρ₀ hρ₀ (by linarith))
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
      have hzre : -1 / 2 < (z : ℂ).re := by rw [h0, Complex.ofReal_re]; linarith
      have hmem : (1 / 2 + (z : ℂ)) ∈ Z.carrier :=
        (mem_of_evenCoeff_ne_zero z.2).elim id fun h' => by
          rwa [show conj (z : ℂ) = z from Complex.ext (by simp) (by simp [him])] at h'
      exact (re_evenCoeff_scaledBumpPolarFree_zero_pos Z hlt hw hmem hzre him).le
    · simp
  rw [hL] at key
  have := norm_pos_iff.mpr hz₀
  linarith

/-- Single-grid exclusion of `AttainedTop β₀` (`β₀ > 1/2 + σ`) by the one-parameter pole-free
dyadic prime window family along `v_k = kℓ`. -/
theorem not_attainedTop_of_grid_polarFree_primeWindow_ge_neg_exp {w ℓ σ C : ℝ} (hw : 0 < w)
    (hw2 : 2 * w < Real.log 2)
    (hgood : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≠ 1 / 2 → paperFT (scaledBump w) (gammaOf ρ) ≠ 0)
    (hℓ : 0 < ℓ) (hres : ℓ ∉ resonantSteps zetaZeroConfig) (hσ : 0 ≤ σ) {N : ℕ}
    (hm : ∀ k : ℕ, N ≤ k → -(C * Real.exp (σ * (k * ℓ))) ≤
      ((1 / (2 * π) : ℂ) * ∫ r : ℝ, paperFT (polarFreeKernel w 0 (k * ℓ) (-1)) r *
        (EF.gammaBracket r : ℂ)).re -
      (∑ n ∈ lagPrimeWindow (k * ℓ) w, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
        (polarFreeKernel w 0 (k * ℓ) (-1) (Real.log n) +
          polarFreeKernel w 0 (k * ℓ) (-1) (-Real.log n))).re)
    {β₀ : ℝ} (hβ₀ : 1 / 2 + σ < β₀) :
    ¬ AttainedTop β₀ := by
  intro hatt
  obtain ⟨⟨ρ₀, hρ₀, hre₀⟩, hmax⟩ := attainedTop_iff_zetaZeroConfig'.mp hatt
  have hlt : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re < 1 := fun ρ hρ => hρ.2.2
  have hmW : ∀ k : ℕ, N ≤ k → -(C * Real.exp (σ * (k * ℓ))) ≤
      (zetaZeroConfig.W (twoBump (scaledBumpPolarFree w 0) (k * ℓ) (-1))
        (twoBump (scaledBumpPolarFree w 0) (k * ℓ) (-1))).re := fun k hk => by
    rw [zeta_re_W_polarFree_twoBump_eq_arch_sub_primeWindow hw hw2 0
      (mul_nonneg k.cast_nonneg hℓ.le) (-1)]
    exact hm k hk
  obtain ⟨ρ', hρ', hgt⟩ := exists_re_gt_of_grid_polarFree_lag_ge_neg_exp zetaZeroConfig
    temperedConfig_zetaZeroConfig hlt hw hgood hℓ hres hσ hmW hρ₀ (by linarith)
  have := hmax ρ' hρ'
  linarith

/-- **Exact `RiemannHypothesis` split on a single geometric progression of pole-free dyadic prime
windows (one parameter, zero pole terms).** For all but countably many widths `w ∈ (0, ½ log 2)`
and steps `ℓ > 0` and every `N : ℕ`, `RiemannHypothesis` holds iff `ZerosApproachLine` holds and
the archimedean term dominates the dyadic prime window sum of `polarFreeKernel w 0 (k * ℓ) (-1)`
for all `k ≥ N`. -/
theorem riemannHypothesis_iff_zerosApproachLine_and_grid_polarFree_primeWindow_le_arch :
    ∃ E : Set ℝ, E.Countable ∧ ∃ E' : Set ℝ, E'.Countable ∧ ∀ w : ℝ, 0 < w →
      2 * w < Real.log 2 → w ∉ E → ∀ ℓ : ℝ, 0 < ℓ → ℓ ∉ E' → ∀ N : ℕ,
        RiemannHypothesis ↔
          BacklundConverse.ZerosApproachLine ∧
            ∀ k : ℕ, N ≤ k →
              (∑ n ∈ lagPrimeWindow (k * ℓ) w,
                ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
                  (polarFreeKernel w 0 (k * ℓ) (-1) (Real.log n) +
                    polarFreeKernel w 0 (k * ℓ) (-1) (-Real.log n))).re ≤
              ((1 / (2 * π) : ℂ) * ∫ r : ℝ, paperFT (polarFreeKernel w 0 (k * ℓ) (-1)) r *
                (EF.gammaBracket r : ℂ)).re := by
  refine ⟨_, countable_bad_widths zetaZeroConfig, _, countable_resonantSteps zetaZeroConfig,
    fun w hw hw2 hwE ℓ hℓ hres N => ?_⟩
  have hgood : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≠ 1 / 2 →
      paperFT (scaledBump w) (gammaOf ρ) ≠ 0 := fun ρ hρ hre h0 => hwE ⟨hw, ρ, hρ, hre, h0⟩
  constructor
  · intro hRH
    refine ⟨zerosApproachLine_of_riemannHypothesis hRH, fun k _ => ?_⟩
    have hnonneg : 0 ≤ (zetaZeroConfig.W (twoBump (scaledBumpPolarFree w 0) (k * ℓ) (-1))
        (twoBump (scaledBumpPolarFree w 0) (k * ℓ) (-1))).re :=
      weil_nonneg_of_onLine _ (riemannHypothesis_iff_zetaZeroConfig_onLine'.mp hRH) _
    rw [zeta_re_W_polarFree_twoBump_eq_arch_sub_primeWindow hw hw2 0
      (mul_nonneg k.cast_nonneg hℓ.le) (-1)] at hnonneg
    linarith
  · rintro ⟨hZAL, hm⟩
    by_contra hRH
    obtain ⟨β₀, hβ₀, hatt⟩ := exists_attainedTop_of_zerosApproachLine hZAL hRH
    refine not_attainedTop_of_grid_polarFree_primeWindow_ge_neg_exp hw hw2 hgood hℓ hres le_rfl
      (C := 0) (N := N) (fun k hk => ?_) (by linarith) hatt
    have := hm k hk
    simp only [zero_mul, neg_zero]
    linarith

/-- Under `RiemannHypothesis`, the pole-vanishing ground energy `μ₀(A)` is nonnegative at every
aperture. -/
theorem ccmRestrictedWeilPolarGroundEnergy_nonneg_of_riemannHypothesis
    (hRH : RiemannHypothesis) (A : SuzukiPositiveAperture) :
    0 ≤ ccmRestrictedWeilPolarGroundEnergy A :=
  (ccmRestrictedWeilGroundEnergy_nonneg_of_riemannHypothesis' hRH A).trans
    (ccmRestrictedWeilGroundEnergy_le_polar A)

/-- **Single arithmetic progression of pole-vanishing ground energies `μ₀(kℓ/2 + w)` decides RH
under `ZerosApproachLine`.** For every good width `w > 0`, non-resonant step `ℓ > 0`, and `N : ℕ`,
`RiemannHypothesis` holds iff `ZerosApproachLine` holds and `μ₀(kℓ/2 + w)` is bounded below along
`k ≥ N`. -/
theorem riemannHypothesis_iff_zerosApproachLine_and_grid_ccmRestrictedWeilPolarGroundEnergy_bddBelow
    {w ℓ : ℝ} (hw : 0 < w)
    (hgood : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≠ 1 / 2 → paperFT (scaledBump w) (gammaOf ρ) ≠ 0)
    (hℓ : 0 < ℓ) (hres : ℓ ∉ resonantSteps zetaZeroConfig) (N : ℕ) :
    RiemannHypothesis ↔
      BacklundConverse.ZerosApproachLine ∧
        ∃ C : ℝ, ∀ k : ℕ, N ≤ k →
          -C ≤ ccmRestrictedWeilPolarGroundEnergy
            ⟨k * ℓ / 2 + w, by have : (0 : ℝ) ≤ k * ℓ := mul_nonneg k.cast_nonneg hℓ.le; positivity⟩ := by
  constructor
  · intro hRH
    refine ⟨zerosApproachLine_of_riemannHypothesis hRH, 0, fun k _ => ?_⟩
    rw [neg_zero]
    exact ccmRestrictedWeilPolarGroundEnergy_nonneg_of_riemannHypothesis hRH _
  · rintro ⟨hZAL, C, hm⟩
    by_contra hRH
    obtain ⟨β₀, hβ₀, hatt⟩ := exists_attainedTop_of_zerosApproachLine hZAL hRH
    obtain ⟨⟨ρ₀, hρ₀, hre₀⟩, hmax⟩ := attainedTop_iff_zetaZeroConfig'.mp hatt
    have hlt : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re < 1 := fun ρ hρ => hρ.2.2
    obtain ⟨K, hK⟩ := exists_nat_gt (2 * w / ℓ)
    have hKℓ : 2 * w < K * ℓ := by rwa [div_lt_iff₀ hℓ] at hK
    set B := ∫ t, ‖scaledBumpPolarFree w 0 t‖ ^ 2 with hB
    have hB0 : 0 ≤ B := integral_nonneg fun _ => sq_nonneg _
    have hmW : ∀ k : ℕ, max N K ≤ k → -(2 * B * max C 0 * Real.exp (0 * (k * ℓ))) ≤
        (zetaZeroConfig.W (twoBump (scaledBumpPolarFree w 0) (k * ℓ) (-1))
          (twoBump (scaledBumpPolarFree w 0) (k * ℓ) (-1))).re := fun k hk => by
      have hkN : N ≤ k := le_trans (le_max_left _ _) hk
      have hkK : K ≤ k := le_trans (le_max_right _ _) hk
      have h2w : 2 * w < k * ℓ := lt_of_lt_of_le hKℓ
        (mul_le_mul_of_nonneg_right (by exact_mod_cast hkK) hℓ.le)
      have hray := two_mul_ccmRestrictedWeilPolarGroundEnergy_le_re_W_polarFree_twoBump hw 0 h2w
      have hfloor := hm k hkN
      have hC : C ≤ max C 0 := le_max_left _ _
      simp only [zero_mul, Real.exp_zero, mul_one]
      nlinarith
    obtain ⟨ρ', hρ', hgt⟩ := exists_re_gt_of_grid_polarFree_lag_ge_neg_exp zetaZeroConfig
      temperedConfig_zetaZeroConfig hlt hw hgood hℓ hres le_rfl hmW hρ₀ (by linarith)
    have := hmax ρ' hρ'
    linarith

/-! ### Global arithmetic window floor for all apertures and all lags -/

/-- The prime shift mass `Σ_{n ≤ ⌊e^{2R}⌋} Λ(n) n^{-1/2}` entering a window of half-width `R`. -/
def aperturePrimeSum (R : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 0 ⌊Real.exp (2 * R)⌋₊, vonMangoldtAtom n

/-- The global pole-free window floor at half-width `R > 0`:
`w₀(R) = -log(2R) - (3/2)R - (γ + log π) - 2 Σ_{n ≤ ⌊e^{2R}⌋} Λ(n) n^{-1/2}`. -/
def polarWindowFloor (R : ℝ) : ℝ :=
  -Real.log (2 * R) - 3 / 2 * R - 2 * archConstantReal - 2 * aperturePrimeSum R

/-- The explicit elementary global pole-free window floor at half-width `R > 0`:
`w₀^{expl}(R) = -log(2R) - (3/2)R - (γ + log π) - 8 R e^R`. -/
def explicitPolarWindowFloor (R : ℝ) : ℝ :=
  -Real.log (2 * R) - 3 / 2 * R - 2 * archConstantReal - 8 * R * Real.exp R

theorem aperturePrimeSum_nonneg (R : ℝ) : 0 ≤ aperturePrimeSum R :=
  Finset.sum_nonneg fun n _ => vonMangoldtAtom_nonneg n

theorem aperturePrimeSum_mono {R₁ R₂ : ℝ} (h : R₁ ≤ R₂) :
    aperturePrimeSum R₁ ≤ aperturePrimeSum R₂ := by
  unfold aperturePrimeSum
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun n _ _ => vonMangoldtAtom_nonneg n
  intro n hn
  rw [Finset.mem_Icc] at hn ⊢
  exact ⟨hn.1, hn.2.trans (Nat.floor_mono (Real.exp_le_exp.mpr (by linarith)))⟩

/-- Below the first prime (`2R < log 2`), the aperture prime sum vanishes identically. -/
theorem aperturePrimeSum_eq_zero_of_lt_log_two {R : ℝ} (hR : 2 * R < Real.log 2) :
    aperturePrimeSum R = 0 := by
  unfold aperturePrimeSum
  refine Finset.sum_eq_zero fun n hn => ?_
  have hexp : Real.exp (2 * R) < 2 := (Real.exp_lt_exp.mpr hR).trans_eq (Real.exp_log two_pos)
  have hfl : ⌊Real.exp (2 * R)⌋₊ < 2 :=
    (Nat.floor_lt (Real.exp_pos _).le).mpr (by exact_mod_cast hexp)
  have hnle := (Finset.mem_Icc.mp hn).2
  unfold vonMangoldtAtom
  rw [if_neg (by omega)]

/-- Below the first prime (`2R < log 2`), `polarWindowFloor R` improves `windowFloor R` by removing
the `4R³` odd-pole penalty. -/
theorem polarWindowFloor_eq_windowFloor_add_four_mul_cube {R : ℝ} (hR : 2 * R < Real.log 2) :
    polarWindowFloor R = windowFloor R + 4 * R ^ 3 := by
  unfold polarWindowFloor windowFloor
  rw [aperturePrimeSum_eq_zero_of_lt_log_two hR]
  ring

theorem polarWindowFloor_antitoneOn : AntitoneOn polarWindowFloor (Ioi 0) := by
  intro R₁ hR₁ R₂ hR₂ hle
  unfold polarWindowFloor
  have hlog : Real.log (2 * R₁) ≤ Real.log (2 * R₂) :=
    Real.log_le_log (by linarith [mem_Ioi.mp hR₁]) (by linarith)
  have hp := aperturePrimeSum_mono hle
  linarith

/-- Every prime-power atom satisfies `Λ(n) n^{-1/2} ≤ (log n) n^{-1/2}`. -/
theorem vonMangoldtAtom_le_log_div_sqrt (n : ℕ) :
    vonMangoldtAtom n ≤ Real.log n / Real.sqrt n := by
  unfold vonMangoldtAtom
  split_ifs with h2
  · exact div_le_div_of_nonneg_right ArithmeticFunction.vonMangoldt_le_log (Real.sqrt_nonneg _)
  · rcases n with _ | _ | n
    · simp
    · simp
    · omega

/-- Every prime-power atom satisfies `Λ(n) n^{-1/2} ≤ 1`. -/
theorem vonMangoldtAtom_le_one (n : ℕ) : vonMangoldtAtom n ≤ 1 := by
  unfold vonMangoldtAtom
  split_ifs with h2
  · have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hsq : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn
    rw [div_le_one hsq]
    have h1 := Real.log_le_sub_one_of_pos (div_pos hsq two_pos)
    rw [Real.log_div hsq.ne' two_ne_zero, Real.log_sqrt hn.le] at h1
    have h2' := Real.log_two_lt_d9
    linarith [ArithmeticFunction.vonMangoldt_le_log (n := n)]
  · norm_num

/-- Comparison with Chebyshev's `ψ(e^{2R})`: `aperturePrimeSum R ≤ ψ(e^{2R}) / √2`. -/
theorem aperturePrimeSum_le_psiSum_div_sqrt_two (R : ℝ) :
    aperturePrimeSum R ≤
      GaloisForLFunctions.ArithmeticCriticalityTheory.psiSum (Real.exp (2 * R)) / Real.sqrt 2 := by
  unfold aperturePrimeSum GaloisForLFunctions.ArithmeticCriticalityTheory.psiSum
  rw [Finset.sum_div]
  refine Finset.sum_le_sum fun n _ => ?_
  unfold vonMangoldtAtom
  split_ifs with h2
  · exact div_le_div_of_nonneg_left ArithmeticFunction.vonMangoldt_nonneg
      (Real.sqrt_pos.mpr two_pos) (Real.sqrt_le_sqrt (by exact_mod_cast h2))
  · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)

/-- Elementary telescoping step `1 / √(k + 1) ≤ 2 (√(k + 1) - √k)`. -/
theorem one_div_sqrt_succ_le_two_mul_sub (k : ℕ) :
    1 / Real.sqrt ((k + 1 : ℕ) : ℝ) ≤
      2 * Real.sqrt ((k + 1 : ℕ) : ℝ) - 2 * Real.sqrt (k : ℝ) := by
  set a := Real.sqrt (k : ℝ)
  set b := Real.sqrt ((k + 1 : ℕ) : ℝ)
  have ha2 : a ^ 2 = (k : ℝ) := Real.sq_sqrt (Nat.cast_nonneg k)
  have hb2 : b ^ 2 = (k : ℝ) + 1 := by
    change Real.sqrt ((k + 1 : ℕ) : ℝ) ^ 2 = (k : ℝ) + 1
    rw [show ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 by push_cast; ring]
    exact Real.sq_sqrt (by positivity)
  have hb0 : 0 < b := Real.sqrt_pos.mpr (by exact_mod_cast Nat.succ_pos k)
  have hab : 2 * a * b ≤ a ^ 2 + b ^ 2 := two_mul_le_add_sq a b
  rw [div_le_iff₀ hb0]
  nlinarith

/-- **Explicit global `4 R e^R` bound on the aperture prime sum.** For every `R ≥ 0`,
`aperturePrimeSum R ≤ 4 R e^R`. -/
theorem aperturePrimeSum_le_four_mul_mul_exp {R : ℝ} (hR : 0 ≤ R) :
    aperturePrimeSum R ≤ 4 * R * Real.exp R := by
  set N := ⌊Real.exp (2 * R)⌋₊ with hNdef
  have hIcc : Finset.Icc 0 N = Finset.range (N + 1) := by ext n; simp
  unfold aperturePrimeSum
  rw [← hNdef, hIcc, Finset.sum_range_succ',
    show vonMangoldtAtom 0 = 0 by unfold vonMangoldtAtom; simp, add_zero]
  have hterm : ∀ k ∈ Finset.range N,
      vonMangoldtAtom (k + 1) ≤
        2 * R * (2 * Real.sqrt ((k + 1 : ℕ) : ℝ) - 2 * Real.sqrt (k : ℝ)) := by
    intro k hk
    have hkN : k + 1 ≤ N := Finset.mem_range.mp hk
    have hkexp : ((k + 1 : ℕ) : ℝ) ≤ Real.exp (2 * R) :=
      (Nat.cast_le.mpr hkN).trans (Nat.floor_le (Real.exp_pos _).le)
    have hkpos : (0 : ℝ) < (k + 1 : ℕ) := by exact_mod_cast Nat.succ_pos k
    have hlog : Real.log ((k + 1 : ℕ) : ℝ) ≤ 2 * R := by
      rw [← Real.log_exp (2 * R)]
      exact Real.log_le_log hkpos hkexp
    have hinv := one_div_sqrt_succ_le_two_mul_sub k
    have hsub0 : 0 ≤ 2 * Real.sqrt ((k + 1 : ℕ) : ℝ) - 2 * Real.sqrt (k : ℝ) :=
      le_trans (by positivity) hinv
    calc vonMangoldtAtom (k + 1)
        ≤ Real.log ((k + 1 : ℕ) : ℝ) / Real.sqrt ((k + 1 : ℕ) : ℝ) :=
          vonMangoldtAtom_le_log_div_sqrt (k + 1)
      _ ≤ (2 * R) * (1 / Real.sqrt ((k + 1 : ℕ) : ℝ)) := by
          rw [div_eq_mul_one_div]
          exact mul_le_mul_of_nonneg_right hlog (by positivity)
      _ ≤ 2 * R * (2 * Real.sqrt ((k + 1 : ℕ) : ℝ) - 2 * Real.sqrt (k : ℝ)) :=
          mul_le_mul_of_nonneg_left hinv (by linarith)
  have hsum := Finset.sum_le_sum hterm
  rw [← Finset.mul_sum, Finset.sum_range_sub (fun k : ℕ => 2 * Real.sqrt (k : ℝ)) N,
    Nat.cast_zero, Real.sqrt_zero, mul_zero, sub_zero] at hsum
  have hsqrtN : Real.sqrt (N : ℝ) ≤ Real.exp R := by
    rw [← Real.sqrt_sq (Real.exp_pos R).le]
    refine Real.sqrt_le_sqrt ?_
    calc (N : ℝ) ≤ Real.exp (2 * R) := Nat.floor_le (Real.exp_pos _).le
      _ = Real.exp R ^ 2 := by rw [← Real.exp_nat_mul]; ring_nf
  calc ∑ k ∈ Finset.range N, vonMangoldtAtom (k + 1)
      ≤ 2 * R * (2 * Real.sqrt (N : ℝ)) := hsum
    _ ≤ 2 * R * (2 * Real.exp R) := by gcongr
    _ = 4 * R * Real.exp R := by ring

/-- For every `R ≥ 0`, `explicitPolarWindowFloor R ≤ polarWindowFloor R`. -/
theorem explicitPolarWindowFloor_le_polarWindowFloor {R : ℝ} (hR : 0 ≤ R) :
    explicitPolarWindowFloor R ≤ polarWindowFloor R := by
  unfold explicitPolarWindowFloor polarWindowFloor
  have := aperturePrimeSum_le_four_mul_mul_exp hR
  linarith

/-- **Global truncation of the prime shift sum on a window.** If `M` vanishes outside `(-R, R)`,
then at every `|x| < R` all prime shifts with `n > ⌊e^{2R}⌋` miss `(-R, R)`. -/
theorem profilePrimeSum_eq_sum_Icc {M : ℝ → ℝ} {R x : ℝ} (hsupp : ∀ y, R ≤ |y| → M y = 0)
    (hx : |x| < R) :
    profilePrimeSum M x =
      ∑ n ∈ Finset.Icc 0 ⌊Real.exp (2 * R)⌋₊,
        vonMangoldtAtom n * (M (x + Real.log n) + M (x - Real.log n)) := by
  have hR0 : 0 < R := lt_of_le_of_lt (abs_nonneg x) hx
  unfold profilePrimeSum
  refine tsum_eq_sum fun n hn => ?_
  rcases Nat.lt_or_ge n 2 with h2 | h2
  · unfold vonMangoldtAtom
    rw [if_neg (by omega), zero_mul]
  · have hgt : ⌊Real.exp (2 * R)⌋₊ < n := by
      by_contra hle
      exact hn (Finset.mem_Icc.mpr ⟨Nat.zero_le n, not_lt.mp hle⟩)
    have hexp : Real.exp (2 * R) < (n : ℝ) := Nat.lt_of_floor_lt hgt
    have hlog : 2 * R < Real.log n := by
      rw [← Real.log_exp (2 * R)]
      exact Real.log_lt_log (Real.exp_pos _) hexp
    have hlog0 : 0 ≤ Real.log n := by linarith
    rw [hsupp (x + Real.log n) ?_, hsupp (x - Real.log n) ?_, add_zero, mul_zero]
    · rw [abs_sub_comm]
      have := abs_sub_abs_le_abs_sub (Real.log n) x
      rw [abs_of_nonneg hlog0] at this
      linarith
    · have := abs_sub_abs_le_abs_sub (Real.log n) (-x)
      rw [abs_of_nonneg hlog0, abs_neg, sub_neg_eq_add, add_comm] at this
      linarith

/-- **Global bound on the prime shift sum of a window gauge.** For any gauge `0 ≤ M ≤ 1` vanishing
outside `(-R, R)` and any `|x| < R`, `profilePrimeSum M x ≤ 2 * aperturePrimeSum R`. -/
theorem profilePrimeSum_le_two_mul_aperturePrimeSum {M : ℝ → ℝ} {R x : ℝ}
    (hle : ∀ y, M y ≤ 1) (hsupp : ∀ y, R ≤ |y| → M y = 0) (hx : |x| < R) :
    profilePrimeSum M x ≤ 2 * aperturePrimeSum R := by
  rw [profilePrimeSum_eq_sum_Icc hsupp hx, aperturePrimeSum, Finset.mul_sum]
  refine Finset.sum_le_sum fun n _ => ?_
  have h1 := hle (x + Real.log n)
  have h2 := hle (x - Real.log n)
  have hΛ := vonMangoldtAtom_nonneg n
  nlinarith

/-- **Global potential lower bound at a plateau point (all `R > 0`).** Removing `2R < log 2` from
`neg_poleFreeWeilOperator_ge`: for any continuous Lipschitz gauge `M ≤ 1` vanishing outside
`(-R, R)` and any `|x| < R` with `M x = 1`, `polarWindowFloor R ≤ -poleFreeWeilOperator M x`. -/
theorem neg_poleFreeWeilOperator_ge_polarWindowFloor {M : ℝ → ℝ} {K R x : ℝ}
    (hMc : Continuous M) (hLip : ∀ a b, |M a - M b| ≤ K * |a - b|)
    (hle : ∀ y, M y ≤ 1) (hsupp : ∀ y, R ≤ |y| → M y = 0) (hx : |x| < R) (hMx : M x = 1) :
    polarWindowFloor R ≤ -poleFreeWeilOperator M x := by
  have ha : 0 < R - x := by linarith [le_abs_self x]
  have hb : 0 < R + x := by linarith [neg_abs_le x]
  have hI := integral_profileArchTerm_ge hMc hLip hle hsupp hx hMx
  have hNa := neg_half_log_one_sub_exp_ge ha
  have hNb := neg_half_log_one_sub_exp_ge hb
  have hprod : Real.log (2 * (R - x)) + Real.log (2 * (R + x)) ≤ 2 * Real.log (2 * R) := by
    rw [← Real.log_mul (by positivity) (by positivity), ← Real.log_rpow (by linarith),
      Real.rpow_two]
    exact Real.log_le_log (by positivity) (by nlinarith [sq_nonneg x])
  have hP := profilePrimeSum_le_two_mul_aperturePrimeSum hle hsupp hx
  unfold poleFreeWeilOperator polarWindowFloor
  rw [hMx]
  linarith

/-- **Global coercivity of `markovEnergy` on every window `[-r, r]` (`r < R`).** Holds for all
`R > 0`, without the `2R < log 2` or `R ≤ 2` restrictions. -/
theorem markovEnergy_ge_polarWindowFloor {F : ℝ → ℝ} {r R : ℝ} (hrR : r < R)
    (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F) (hsupp : ∀ x, r < |x| → F x = 0) :
    polarWindowFloor R * ∫ x, F x ^ 2 ≤ markovEnergy (fun x => (F x : ℂ)) := by
  set δ := R - r with hδdef
  have hδ : 0 < δ := by linarith
  set M := plateauGauge R δ with hMdef
  have hMd : ContDiff ℝ 2 M := contDiff_plateauGauge R δ
  have hMcs : HasCompactSupport M := hasCompactSupport_plateauGauge hδ
  have hnn : ∀ y, 0 ≤ M y := plateauGauge_nonneg R δ
  have hle : ∀ y, M y ≤ 1 := plateauGauge_le_one R δ
  have hzero : ∀ y, R ≤ |y| → M y = 0 := fun y hy => plateauGauge_eq_zero hδ hy
  have hFM : ∀ x, F x ≠ 0 → M x = 1 := fun x hx => by
    refine plateauGauge_eq_one hδ ?_
    by_contra h
    exact hx (hsupp x (by have := not_le.mp h; linarith))
  have hFx : ∀ x, F x ≠ 0 → |x| < R := fun x hx => by
    by_contra h
    exact hx (by
      have := hzero x (not_lt.mp h)
      rw [hFM x hx] at this
      norm_num at this)
  obtain ⟨K, -, hK⟩ := exists_lipschitz_bound_of_compactSupport (hMd.of_le (by norm_num)) hMcs
  have hLip : ∀ a b, |M a - M b| ≤ K * |a - b| := fun a b => hK b a
  have hC12 := markovEnergy_eq_gauge_window hF hFc hMd hMcs hle hnn hzero hFM
  have hJ := signedJumpEnergy_nonneg_of_nonneg (F := F) hnn
  have hdec8 : ∀ y, |M y| ≤ Real.exp (8 * |R|) * Real.exp (-(8 * |y|)) := by
    intro y
    by_cases hy : |y| < R
    · rw [abs_of_nonneg (hnn y), ← Real.exp_add]
      exact (hle y).trans (Real.one_le_exp (by nlinarith [le_abs_self R]))
    · rw [hzero y (not_lt.mp hy), abs_zero]
      positivity
  have hg : Continuous fun x => -poleFreeWeilOperator M x :=
    (continuous_poleFreeWeilOperator hMd.continuous hLip hdec8).neg
  have hF2 : Integrable fun x => F x ^ 2 :=
    (hF.continuous.pow 2).integrable_of_hasCompactSupport (hasCompactSupport_sq hFc)
  have hpot : polarWindowFloor R * ∫ x, F x ^ 2 ≤
      ∫ x, F x ^ 2 * M x * -poleFreeWeilOperator M x := by
    rw [← integral_const_mul]
    refine integral_mono (hF2.const_mul _) ((((hF.continuous.pow 2).mul hMd.continuous).mul
      hg).integrable_of_hasCompactSupport ((hasCompactSupport_sq hFc).mul_right.mul_right)) fun x => ?_
    by_cases h : F x = 0
    · simp [h]
    · have hW := neg_poleFreeWeilOperator_ge_polarWindowFloor hMd.continuous hLip hle hzero
        (hFx x h) (hFM x h)
      rw [hFM x h, mul_one]
      nlinarith [sq_nonneg (F x)]
  rw [hC12]
  linarith

/-- **Global coercivity of `fullZeroForm` on tests with `oddPoleMoment F = 0` (`r < R`).** -/
theorem fullZeroForm_ge_polarWindowFloor_of_oddPoleMoment_eq_zero {F : ℝ → ℝ} {r R : ℝ}
    (hrR : r < R) (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F)
    (hsupp : ∀ x, r < |x| → F x = 0) (hS : oddPoleMoment F = 0) :
    polarWindowFloor R * ∫ x, F x ^ 2 ≤ fullZeroForm F := by
  have hM := markovEnergy_ge_polarWindowFloor hrR hF hFc hsupp
  have hE := sq_nonneg (evenPoleMoment F)
  unfold fullZeroForm
  rw [hS]
  linarith

/-- For a polar-constrained smooth interior source `u`, both `Re u` and `Im u` have vanishing odd
pole moment. -/
theorem oddPoleMoment_re_im_eq_zero_of_isPolarConstrained {A : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource A) (hu : IsPolarConstrained A u.toCCMFormVector) :
    oddPoleMoment (fun x => (u x).re) = 0 ∧ oddPoleMoment (fun x => (u x).im) = 0 := by
  have hp := hu.1
  have hm := hu.2
  rw [inner_ccmPolarApertureVector_ccmComplexSmoothFormVector] at hp hm
  have hre_c : Continuous fun x => (u x).re := Complex.continuous_re.comp u.smooth.continuous
  have him_c : Continuous fun x => (u x).im := Complex.continuous_im.comp u.smooth.continuous
  have hre_cs : HasCompactSupport fun x => (u x).re := u.hasCompactSupport.comp_left Complex.zero_re
  have him_cs : HasCompactSupport fun x => (u x).im := u.hasCompactSupport.comp_left Complex.zero_im
  have hip : Integrable fun x : ℝ => (Real.exp (1 / 2 * x) : ℂ) * u x :=
    ((Complex.continuous_ofReal.comp (Real.continuous_exp.comp
      (continuous_const.mul continuous_id))).mul u.smooth.continuous).integrable_of_hasCompactSupport
      u.hasCompactSupport.mul_left
  have him' : Integrable fun x : ℝ => (Real.exp (-1 / 2 * x) : ℂ) * u x :=
    ((Complex.continuous_ofReal.comp (Real.continuous_exp.comp
      (continuous_const.mul continuous_id))).mul u.smooth.continuous).integrable_of_hasCompactSupport
      u.hasCompactSupport.mul_left
  have hre_p : expHalfMoment (fun x => (u x).re) = 0 := by
    have h := (integral_re hip).symm
    simp only [hp, map_zero, RCLike.re_to_complex] at h
    refine (integral_congr_ae (Eventually.of_forall fun x => ?_)).trans h.symm
    show (u x).re * Real.exp (x / 2) = (((Real.exp (1 / 2 * x) : ℂ) * u x).re)
    rw [Complex.re_ofReal_mul, show 1 / 2 * x = x / 2 by ring, mul_comm]
  have hre_m : expNegHalfMoment (fun x => (u x).re) = 0 := by
    have h := (integral_re him').symm
    simp only [hm, map_zero, RCLike.re_to_complex] at h
    refine (integral_congr_ae (Eventually.of_forall fun x => ?_)).trans h.symm
    show (u x).re * Real.exp (-(x / 2)) = (((Real.exp (-1 / 2 * x) : ℂ) * u x).re)
    rw [Complex.re_ofReal_mul, show -1 / 2 * x = -(x / 2) by ring, mul_comm]
  have him_p : expHalfMoment (fun x => (u x).im) = 0 := by
    have h := (integral_im hip).symm
    simp only [hp, map_zero, RCLike.im_to_complex] at h
    refine (integral_congr_ae (Eventually.of_forall fun x => ?_)).trans h.symm
    show (u x).im * Real.exp (x / 2) = (((Real.exp (1 / 2 * x) : ℂ) * u x).im)
    rw [Complex.im_ofReal_mul, show 1 / 2 * x = x / 2 by ring, mul_comm]
  have him_m : expNegHalfMoment (fun x => (u x).im) = 0 := by
    have h := (integral_im him').symm
    simp only [hm, map_zero, RCLike.im_to_complex] at h
    refine (integral_congr_ae (Eventually.of_forall fun x => ?_)).trans h.symm
    show (u x).im * Real.exp (-(x / 2)) = (((Real.exp (-1 / 2 * x) : ℂ) * u x).im)
    rw [Complex.im_ofReal_mul, show -1 / 2 * x = -(x / 2) by ring, mul_comm]
  have h1 := expHalfMoment_eq hre_c hre_cs
  have h2 := expNegHalfMoment_eq hre_c hre_cs
  have h3 := expHalfMoment_eq him_c him_cs
  have h4 := expNegHalfMoment_eq him_c him_cs
  exact ⟨by linarith, by linarith⟩

/-- Every polar-constrained smooth interior source at aperture `A` satisfies
`polarWindowFloor A.1 * ‖u‖² ≤ Q_A(u)`. -/
theorem polarWindowFloor_mul_le_ccmRestrictedWeilSourceQuadratic (A : SuzukiPositiveAperture)
    (u : CCMComplexSmoothInteriorSource A) (hu : IsPolarConstrained A u.toCCMFormVector) :
    polarWindowFloor A.1 * ‖ccmArchimedeanFormToAperture A u.toCCMFormVector‖ ^ (2 : ℕ) ≤
      ccmRestrictedWeilSourceQuadratic A u.toCCMFormVector := by
  obtain ⟨b, hbA, hsupp⟩ := exists_strict_smaller_aperture_of_compact_tsupport A u
  have hu2 : ContDiff ℝ 2 (u : ℝ → ℂ) := u.smooth.of_le (WithTop.coe_le_coe.mpr le_top)
  have hre : ContDiff ℝ 2 fun x => (u x).re := Complex.reCLM.contDiff.comp hu2
  have him : ContDiff ℝ 2 fun x => (u x).im := Complex.imCLM.contDiff.comp hu2
  have hrec : HasCompactSupport fun x => (u x).re := u.hasCompactSupport.comp_left Complex.zero_re
  have himc : HasCompactSupport fun x => (u x).im := u.hasCompactSupport.comp_left Complex.zero_im
  have hzero : ∀ x, b.1 < |x| → u x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => by
      have := hsupp h
      exact absurd (abs_lt.mpr ⟨this.1, this.2⟩) (not_lt.mpr hx.le)
  obtain ⟨hSre, hSim⟩ := oddPoleMoment_re_im_eq_zero_of_isPolarConstrained u hu
  have h1 := fullZeroForm_ge_polarWindowFloor_of_oddPoleMoment_eq_zero hbA hre hrec
    (fun x hx => by simp [hzero x hx]) hSre
  have h2 := fullZeroForm_ge_polarWindowFloor_of_oddPoleMoment_eq_zero hbA him himc
    (fun x hx => by simp [hzero x hx]) hSim
  have hsplit := GaloisForLFunctions.ArithmeticPositivityTheory.zeta_W_re_eq_fullZeroForm_re_add_im
    hu2 u.hasCompactSupport
  have i1 : Integrable fun x => (u x).re ^ 2 :=
    (hre.continuous.pow 2).integrable_of_hasCompactSupport (hasCompactSupport_sq hrec)
  have i2 : Integrable fun x => (u x).im ^ 2 :=
    (him.continuous.pow 2).integrable_of_hasCompactSupport (hasCompactSupport_sq himc)
  have hnorm : (∫ x, ‖u x‖ ^ 2) = (∫ x, (u x).re ^ 2) + ∫ x, (u x).im ^ 2 := by
    rw [← integral_add i1 i2]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  rw [norm_sq_ccmArchimedeanFormToAperture_toCCMFormVector,
    ccmRestrictedWeilSource_complexSmooth_eq_zetaWeil]
  change polarWindowFloor A.1 * ∫ x, ‖u x‖ ^ 2 ≤ (zetaZeroConfig.W (u : ℝ → ℂ) (u : ℝ → ℂ)).re
  rw [hsplit, hnorm, mul_add]
  linarith

/-- **Global Arithmetic Ground-Energy Theorem.** For **every** aperture `A : SuzukiPositiveAperture`
(`A > 0`), the pole-vanishing ground energy satisfies `polarWindowFloor A.1 ≤ μ₀(A)`. -/
theorem polarWindowFloor_le_ccmRestrictedWeilPolarGroundEnergy (A : SuzukiPositiveAperture) :
    polarWindowFloor A.1 ≤ ccmRestrictedWeilPolarGroundEnergy A := by
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨g, hg, hgne, hlt⟩ := exists_polarConstrained_smooth_rayleigh_lt A hε
  have hpos : 0 < ‖ccmArchimedeanFormToAperture A g.toCCMFormVector‖ ^ (2 : ℕ) :=
    pow_pos (norm_pos_iff.mpr hgne) 2
  have hfl := (le_div_iff₀ hpos).mpr
    (polarWindowFloor_mul_le_ccmRestrictedWeilSourceQuadratic A g hg)
  exact lt_of_le_of_lt hfl hlt

/-- **Explicit Elementary Global Ground-Energy Bound.** For **every** aperture
`A : SuzukiPositiveAperture` (`A > 0`),
`-log(2A) - (3/2)A - 2 archConstantReal - 8 A e^A ≤ μ₀(A)`. -/
theorem explicit_global_le_ccmRestrictedWeilPolarGroundEnergy (A : SuzukiPositiveAperture) :
    explicitPolarWindowFloor A.1 ≤ ccmRestrictedWeilPolarGroundEnergy A :=
  (explicitPolarWindowFloor_le_polarWindowFloor A.2.le).trans
    (polarWindowFloor_le_ccmRestrictedWeilPolarGroundEnergy A)

/-- **Global Closed-Aperture Floor for `fullZeroForm`.** For every `A : SuzukiPositiveAperture` and
every real smooth `F` supported in `[-A, A]` with `evenPoleMoment F = 0` and `oddPoleMoment F = 0`,
`polarWindowFloor A.1 * ∫ F² ≤ fullZeroForm F`. -/
theorem polarWindowFloor_mul_le_fullZeroForm_Icc (A : SuzukiPositiveAperture) {F : ℝ → ℝ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hFs : tsupport F ⊆ Icc (-A.1) A.1)
    (hC : evenPoleMoment F = 0) (hS : oddPoleMoment F = 0) :
    polarWindowFloor A.1 * ∫ x, F x ^ 2 ≤ fullZeroForm F :=
  (mul_le_mul_of_nonneg_right (polarWindowFloor_le_ccmRestrictedWeilPolarGroundEnergy A)
    (integral_nonneg fun _ => sq_nonneg _)).trans
    (polarGroundEnergy_mul_le_fullZeroForm_Icc A hF hFs hC hS)

/-- **Global Arithmetic Mean-Zero Variation Inequality (Closed Support `[-A, A]`, All `A > 0`).**
For every shift `a > 0`, every aperture `A > 0`, and every smooth even `μ_a`-mean-zero profile `u`
supported in `[-A, A]`,
`D_a(u) + polarWindowFloor(A) ∫ (m_a u)² ≤ 2 S_a(u) + V_a(u)`. -/
theorem reflectedDifferenceEnergy_add_polarWindowFloor_le_poleFree_of_meanZero_Icc {a : ℝ}
    {u : ℝ → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) (heven : ∀ x, u (-x) = u x)
    (hmean : profileMoment a u = 0) (ha : 0 < a) (A : SuzukiPositiveAperture)
    (hsupp : tsupport u ⊆ Icc (-A.1) A.1) :
    reflectedDifferenceEnergy (shiftedGroundState a) u +
        polarWindowFloor A.1 *
          ∫ x, phiDoobTest (fun y => shiftedGroundState a y * u y) x ^ 2 ≤
      2 * sameSideEnergy (shiftedGroundState a) u + profileVariance a u := by
  have h := reflectedDifferenceEnergy_add_le_poleFree_of_meanZero_Icc hu heven hmean ha A hsupp
  have hfl := polarWindowFloor_le_ccmRestrictedWeilPolarGroundEnergy A
  have hI : 0 ≤ ∫ x, phiDoobTest (fun y => shiftedGroundState a y * u y) x ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  nlinarith

/-- **Explicit Elementary Global Mean-Zero Variation Inequality (`All A > 0`).** -/
theorem reflectedDifferenceEnergy_add_explicit_le_poleFree_of_meanZero_Icc {a : ℝ}
    {u : ℝ → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) (heven : ∀ x, u (-x) = u x)
    (hmean : profileMoment a u = 0) (ha : 0 < a) (A : SuzukiPositiveAperture)
    (hsupp : tsupport u ⊆ Icc (-A.1) A.1) :
    reflectedDifferenceEnergy (shiftedGroundState a) u +
        explicitPolarWindowFloor A.1 *
          ∫ x, phiDoobTest (fun y => shiftedGroundState a y * u y) x ^ 2 ≤
      2 * sameSideEnergy (shiftedGroundState a) u + profileVariance a u := by
  have h := reflectedDifferenceEnergy_add_polarWindowFloor_le_poleFree_of_meanZero_Icc hu heven
    hmean ha A hsupp
  have hfl := explicitPolarWindowFloor_le_polarWindowFloor A.2.le
  have hI : 0 ≤ ∫ x, phiDoobTest (fun y => shiftedGroundState a y * u y) x ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  nlinarith

/-- **Global Arithmetic Floor on Pole-Free Dyadic Prime Windows (All Lags `v > 2w`, All Heights `ω`).**
For every `0 < w` with `2w < log 2`, every height `ω`, and every lag `v > 2w`,
`2 ‖κ_{2,w,ω}‖₂² polarWindowFloor(v/2 + w) ≤ Arch(polarFreeKernel w ω v (-1)) - PrimeWindow(polarFreeKernel w ω v (-1))`. -/
theorem two_mul_polarWindowFloor_le_arch_sub_primeWindow_polarFree {w v : ℝ}
    (hw : 0 < w) (hw2 : 2 * w < Real.log 2) (ω : ℝ) (hv : 2 * w < v) :
    2 * (∫ t, ‖scaledBumpPolarFree w ω t‖ ^ 2) * polarWindowFloor (v / 2 + w) ≤
      ((1 / (2 * π) : ℂ) * ∫ r : ℝ, paperFT (polarFreeKernel w ω v (-1)) r *
        (EF.gammaBracket r : ℂ)).re -
      (∑ n ∈ lagPrimeWindow v w, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
        (polarFreeKernel w ω v (-1) (Real.log n) +
          polarFreeKernel w ω v (-1) (-Real.log n))).re := by
  have hray := two_mul_ccmRestrictedWeilPolarGroundEnergy_le_arch_sub_primeWindow_polarFree
    hw hw2 ω hv
  have hfl := polarWindowFloor_le_ccmRestrictedWeilPolarGroundEnergy ⟨v / 2 + w, by linarith⟩
  have hB0 : 0 ≤ ∫ t, ‖scaledBumpPolarFree w ω t‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  nlinarith

/-- **Explicit Elementary Global Floor on Pole-Free Dyadic Prime Windows (`All v > 2w`).** -/
theorem two_mul_explicit_le_arch_sub_primeWindow_polarFree {w v : ℝ}
    (hw : 0 < w) (hw2 : 2 * w < Real.log 2) (ω : ℝ) (hv : 2 * w < v) :
    2 * (∫ t, ‖scaledBumpPolarFree w ω t‖ ^ 2) * explicitPolarWindowFloor (v / 2 + w) ≤
      ((1 / (2 * π) : ℂ) * ∫ r : ℝ, paperFT (polarFreeKernel w ω v (-1)) r *
        (EF.gammaBracket r : ℂ)).re -
      (∑ n ∈ lagPrimeWindow v w, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
        (polarFreeKernel w ω v (-1) (Real.log n) +
          polarFreeKernel w ω v (-1) (-Real.log n))).re := by
  have h := two_mul_polarWindowFloor_le_arch_sub_primeWindow_polarFree hw hw2 ω hv
  have hfl := explicitPolarWindowFloor_le_polarWindowFloor (R := v / 2 + w) (by linarith)
  have hB0 : 0 ≤ ∫ t, ‖scaledBumpPolarFree w ω t‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  nlinarith

end GaloisForLFunctions.SquareRootThreshold

end
