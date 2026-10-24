import GaloisForLFunctions.SquareRootThreshold.UnsignedDepthSamplingDetectsLocalMass
import GaloisForLFunctions.SquareRootThreshold.TheWallsMeasureOneZeroWidth
import GaloisForLFunctions.ArithmeticCriticalityTheory.ThreeTenthsSharpGaugeWeilPositivity
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.SignedAveragedContinuationAndTheZeroWidthBand

/-!
# The Compensated Width Floor and the Ground-Energy Rate

This module resolves Open Problem 7 of the `ArithmeticContinuationAndCriticalEnergy` programme:

> With `a_q = û(−z_q)`, `b_q = û(−z̄_q)` on the smooth core and `E_± = ¼ Σ_q |a_q ± b_q|²`,
> decide whether the actual prime–Gamma–pole source forces `E_−(u) ≤ E_+(u) + C_σ e^{2σA}‖u‖₂²`
> for every `σ` above the width, without assuming bounded local off-line depth mass.

## Mathematical resolution

1. **Unconditional convergence and exact Weil polarization (`sourceQuadratic_eq_pairedPlusEnergy_sub_pairedMinusEnergy`).**
   For every smooth interior source `u : CCMComplexSmoothInteriorSource a` at aperture
   `a : SuzukiPositiveAperture`, integrating Suzuki's ray coefficients by parts gives
   `‖û(−z_q)‖ · ‖z_q‖ = ‖suzukiTestRayCoef φ q‖` and
   `‖û(−z̄_q)‖ · ‖z_q‖ = ‖suzukiTestRayCoefBar φ q‖` where `φ = u'`. Since `Σ_q ‖z_q‖⁻² < ∞`, both
   nonnegative paired series
   `E_+(u) = ¼ Σ_q ‖û(−z_q) + û(−z̄_q)‖²` (`pairedPlusEnergy`) and
   `E_−(u) = ¼ Σ_q ‖û(−z_q) − û(−z̄_q)‖²` (`pairedMinusEnergy`) converge unconditionally
   (`summable_pairedPlusTerm`, `summable_pairedMinusTerm`), with `pairedMinusTerm u q = 0` at every
   on-line zero (`pairedMinusTerm_eq_zero_of_im_eq_zero`). Polarizing each zero-copy term gives the
   exact identity
   `Q_a(u) = E_+(u) − E_−(u)` (`sourceQuadratic_eq_pairedPlusEnergy_sub_pairedMinusEnergy`).

2. **Exact single-aperture equivalence (`compensatedSamplingBound_iff_groundEnergy_ge`).**
   Because smooth interior sources are dense in the Archimedean form domain and the literal
   restricted Weil ground state is attained, the compensated sampling bound
   `∀ u, E_−(u) ≤ E_+(u) + B ‖u‖₂²` (`CompensatedSamplingBound a B`) is **equivalent** to the
   ground-energy floor `−B ≤ μ(a)` (`compensatedSamplingBound_iff_groundEnergy_ge`). By contrast,
   the *uncompensated* bound `∀ u, E_−(u) ≤ B ‖u‖₂²` is equivalent to
   `UnsignedDepthSamplingBound a (4B)` (`forall_pairedMinusEnergy_le_iff_unsignedDepthSamplingBound`),
   which holds for some `B ≥ 0` if and only if local off-line depth mass is bounded
   (`exists_uncompensated_pairedMinusEnergy_bound_iff`). The compensated bound holds unconditionally
   at every aperture (`exists_compensatedSamplingBound`), and on `a ≤ 3/10` it holds with the
   strictly negative constant `B = −1/5000` (`compensatedSamplingBound_neg_one_div_5000_of_le_three_tenths`).

3. **The compensated width floor and the reverse ground-rate inequality (`compensatedWidthFloor_iff_groundEnergy_ge_neg_exp`,
   `forall_compensatedWidthFloor_above_width_iff_groundEnergyRate_eq`).**
   Across apertures, `CompensatedWidthFloor σ` (`∃ C A₀, ∀ a ≥ A₀, ∀ u, E_−(u) ≤ E_+(u) + C e^{2σa} ‖u‖₂²`)
   is equivalent to the exponential ground-energy floor `μ(A) ≥ −C e^{2σA}` for `A ≥ A₀`.
   Consequently:
   - for every `σ ≥ 0`, `CompensatedWidthFloor σ` implies `zetaZeroWidth ≤ σ`
     (`zetaZeroWidth_le_of_compensatedWidthFloor`), `σ ∈ polarGroundEnergyRates`
     (`mem_polarGroundEnergyRates_of_compensatedWidthFloor`), the dyadic prime-window lag floor
     `−C' e^{σv}` (`lag_primeWindow_ge_neg_exp_of_compensatedWidthFloor`), and damping continuation
     on every compact interval in `(σ, ∞)` (`averagedDampingContinuation_of_compensatedWidthFloor`);
   - having `CompensatedWidthFloor σ` for every `σ > zetaZeroWidth` is **equivalent** to the exact
     reverse ground-rate equality `groundEnergyRate = zetaZeroWidth` (and implies
     `polarGroundEnergyRate = zetaZeroWidth`), and holds under `OffLineDepthLocallyBounded W` or
     `OffLineCopiesLocallyBounded M` (`compensatedWidthFloor_of_offLineDepthLocallyBounded`,
     `compensatedWidthFloor_of_offLineCopiesLocallyBounded`), yielding the unconditional dichotomy
     `(∀ σ > zetaZeroWidth, CompensatedWidthFloor σ) ∨ (∀ W, ¬ OffLineDepthLocallyBounded W)`
     (`forall_compensatedWidthFloor_or_depthMass_clusters`).
-/

open Complex MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry RHTower RHTower.CCMParityQuartet
open Zeta23 _root_.RHTower.WeilOneSided _root_.RHTower.WeilSpectral
open GaloisForLFunctions.SquareRootThreshold
open GaloisForLFunctions.ArithmeticCriticalityTheory

namespace GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

noncomputable section

/-! ## 1. The paired energies `E_+` and `E_-` and exact Weil polarization -/

/-- The positive paired zero-copy term `¼ ‖û(−z_q) + û(−z̄_q)‖²`. -/
def pairedPlusTerm {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (q : XiZeroCopy) : ℝ :=
  ‖testTransform u (-xiSpectralPoint q) +
    testTransform u (-(starRingEnd ℂ) (xiSpectralPoint q))‖ ^ 2 / 4

/-- The negative (difference) paired zero-copy term `¼ ‖û(−z_q) − û(−z̄_q)‖²`. -/
def pairedMinusTerm {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (q : XiZeroCopy) : ℝ :=
  ‖testTransform u (-xiSpectralPoint q) -
    testTransform u (-(starRingEnd ℂ) (xiSpectralPoint q))‖ ^ 2 / 4

/-- The positive paired energy `E_+(u) = ¼ Σ_q ‖û(−z_q) + û(−z̄_q)‖²`. -/
def pairedPlusEnergy {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) : ℝ :=
  ∑' q : XiZeroCopy, pairedPlusTerm u q

/-- The negative paired energy `E_−(u) = ¼ Σ_q ‖û(−z_q) − û(−z̄_q)‖²`. -/
def pairedMinusEnergy {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) : ℝ :=
  ∑' q : XiZeroCopy, pairedMinusTerm u q

theorem pairedPlusTerm_nonneg {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (q : XiZeroCopy) :
    0 ≤ pairedPlusTerm u q := by
  unfold pairedPlusTerm
  positivity

theorem pairedMinusTerm_nonneg {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (q : XiZeroCopy) :
    0 ≤ pairedMinusTerm u q := by
  unfold pairedMinusTerm
  positivity

/-- At any on-line zero (`Im z_q = 0`), the difference term `pairedMinusTerm u q` vanishes. -/
theorem pairedMinusTerm_eq_zero_of_im_eq_zero {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) {q : XiZeroCopy}
    (hq : (xiSpectralPoint q).im = 0) :
    pairedMinusTerm u q = 0 := by
  have hconj : (starRingEnd ℂ) (xiSpectralPoint q) = xiSpectralPoint q :=
    Complex.conj_eq_iff_im.mpr hq
  unfold pairedMinusTerm
  rw [hconj, sub_self, norm_zero]
  ring

/-- At any on-line zero (`Im z_q = 0`), `pairedPlusTerm u q = ‖û(−z_q)‖²`. -/
theorem pairedPlusTerm_eq_norm_sq_of_im_eq_zero {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) {q : XiZeroCopy}
    (hq : (xiSpectralPoint q).im = 0) :
    pairedPlusTerm u q = ‖testTransform u (-xiSpectralPoint q)‖ ^ 2 := by
  have hconj : (starRingEnd ℂ) (xiSpectralPoint q) = xiSpectralPoint q :=
    Complex.conj_eq_iff_im.mpr hq
  unfold pairedPlusTerm
  rw [hconj, ← two_mul, norm_mul, Complex.norm_two]
  ring

/-- Termwise polarization of the Weil zero-copy term into `pairedPlusTerm − pairedMinusTerm`. -/
theorem re_zeroSumTerm_eq_pairedPlus_sub_pairedMinus {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (q : XiZeroCopy) :
    (zeroSumTerm u (xiSpectralPoint q)).re =
      pairedPlusTerm u q - pairedMinusTerm u q := by
  have h := four_mul_re_mul_conj
    (testTransform u (-xiSpectralPoint q))
    (testTransform u (-(starRingEnd ℂ) (xiSpectralPoint q)))
  unfold zeroSumTerm pairedPlusTerm pairedMinusTerm
  linarith

/-- Integration by parts identifies `‖û(−z_q)‖ · ‖z_q‖` with `‖suzukiTestRayCoef u' q‖`. -/
theorem norm_testTransform_neg_xiSpectralPoint_mul {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (q : XiZeroCopy) :
    ‖testTransform (u : ℝ → ℂ) (-xiSpectralPoint q)‖ * ‖xiSpectralPoint q‖ =
      ‖suzukiTestRayCoef u.toSuzukiSmoothCompactTest.toDerivativeZeroMean q‖ := by
  set γ : ℂ := xiSpectralPoint q
  have hu1 : ContDiff ℝ 1 (u : ℝ → ℂ) := u.smooth.of_le (by exact_mod_cast le_top)
  have hus : HasCompactSupport (u : ℝ → ℂ) := u.hasCompactSupport
  have hcoe : (u.toSuzukiSmoothCompactTest.toDerivativeZeroMean : ℝ → ℂ) =
      deriv (u : ℝ → ℂ) := rfl
  have hcoef : suzukiTestRayCoef u.toSuzukiSmoothCompactTest.toDerivativeZeroMean q =
      testTransform (deriv (u : ℝ → ℂ)) (-γ) := by
    rw [suzukiTestRayCoef_eq_integral, hcoe]
    unfold testTransform
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only
    rw [mul_comm]
    congr 2
    ring
  have hibp1 := testTransform_ibp hu1 hus (-γ)
  have hT1 : testTransform (deriv (u : ℝ → ℂ)) (-γ) =
      -(testTransform (u : ℝ → ℂ) (-γ) * (Complex.I * -γ)) := by
    rw [hibp1, neg_neg]
  rw [hcoef, hT1]
  simp only [norm_neg, norm_mul, Complex.norm_I, one_mul]

/-- Integration by parts identifies `‖û(−z̄_q)‖ · ‖z_q‖` with `‖suzukiTestRayCoefBar u' q‖`. -/
theorem norm_testTransform_neg_conj_xiSpectralPoint_mul {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (q : XiZeroCopy) :
    ‖testTransform (u : ℝ → ℂ) (-(starRingEnd ℂ) (xiSpectralPoint q))‖ * ‖xiSpectralPoint q‖ =
      ‖suzukiTestRayCoefBar u.toSuzukiSmoothCompactTest.toDerivativeZeroMean q‖ := by
  set γ : ℂ := xiSpectralPoint q
  have hu1 : ContDiff ℝ 1 (u : ℝ → ℂ) := u.smooth.of_le (by exact_mod_cast le_top)
  have hus : HasCompactSupport (u : ℝ → ℂ) := u.hasCompactSupport
  set v : ℝ → ℂ := fun x => (starRingEnd ℂ) (u x) with hv
  have hv1 : ContDiff ℝ 1 v := contDiff_one_conj hu1
  have hvs : HasCompactSupport v := hus.comp_left (map_zero _)
  have hcoe : (u.toSuzukiSmoothCompactTest.toDerivativeZeroMean : ℝ → ℂ) =
      deriv (u : ℝ → ℂ) := rfl
  have hdv : deriv v = fun t => (starRingEnd ℂ) (deriv (u : ℝ → ℂ) t) :=
    deriv_conj (hu1.differentiable one_ne_zero)
  have hbar : suzukiTestRayCoefBar u.toSuzukiSmoothCompactTest.toDerivativeZeroMean q =
      testTransform (deriv v) γ := by
    rw [suzukiTestRayCoefBar_eq_integral, hcoe, hdv]
    unfold testTransform
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only
    rw [mul_comm]
  have hibp2 := testTransform_ibp hv1 hvs γ
  have hT2 : testTransform (deriv v) γ = -(testTransform v γ * (Complex.I * γ)) := by
    rw [hibp2, neg_neg]
  rw [hbar, hT2, hv, testTransform_conj]
  simp only [norm_neg, norm_mul, Complex.norm_conj, Complex.norm_I, one_mul]

/-- The positive paired series `pairedPlusTerm u` is unconditionally summable. -/
theorem summable_pairedPlusTerm {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) :
    Summable (pairedPlusTerm u) := by
  set φ := u.toSuzukiSmoothCompactTest.toDerivativeZeroMean
  set C : ℝ := (Real.exp (|a.1| / 2) + 1) * ∫ x : ℝ, ‖(φ : ℝ → ℂ) x‖ with hC
  have hC0 : 0 ≤ C := by
    rw [hC]
    exact mul_nonneg (by positivity) (integral_nonneg fun _ => norm_nonneg _)
  refine Summable.of_nonneg_of_le (pairedPlusTerm_nonneg u) (fun q => ?_)
    (xiSpectralPoint_inv_sq_summable.mul_left (C * C))
  set γ : ℂ := xiSpectralPoint q
  have hγ0 : 0 < ‖γ‖ := norm_pos_iff.mpr (xiSpectralPoint_ne_zero q)
  have h1 : ‖testTransform (u : ℝ → ℂ) (-γ)‖ * ‖γ‖ ≤ C := by
    rw [norm_testTransform_neg_xiSpectralPoint_mul]
    exact norm_suzukiTestRayCoef_le φ q
  have h2 : ‖testTransform (u : ℝ → ℂ) (-(starRingEnd ℂ) γ)‖ * ‖γ‖ ≤ C := by
    rw [norm_testTransform_neg_conj_xiSpectralPoint_mul]
    exact norm_suzukiTestRayCoefBar_le φ q
  have hsum : ‖testTransform (u : ℝ → ℂ) (-γ) +
      testTransform (u : ℝ → ℂ) (-(starRingEnd ℂ) γ)‖ * ‖γ‖ ≤ 2 * C := by
    calc ‖testTransform (u : ℝ → ℂ) (-γ) +
          testTransform (u : ℝ → ℂ) (-(starRingEnd ℂ) γ)‖ * ‖γ‖
        ≤ (‖testTransform (u : ℝ → ℂ) (-γ)‖ +
            ‖testTransform (u : ℝ → ℂ) (-(starRingEnd ℂ) γ)‖) * ‖γ‖ :=
          mul_le_mul_of_nonneg_right (norm_add_le _ _) hγ0.le
      _ = ‖testTransform (u : ℝ → ℂ) (-γ)‖ * ‖γ‖ +
            ‖testTransform (u : ℝ → ℂ) (-(starRingEnd ℂ) γ)‖ * ‖γ‖ := by ring
      _ ≤ 2 * C := by linarith
  have hsq : ‖testTransform (u : ℝ → ℂ) (-γ) +
      testTransform (u : ℝ → ℂ) (-(starRingEnd ℂ) γ)‖ ^ 2 * ‖γ‖ ^ 2 ≤ 4 * (C * C) := by
    have := pow_le_pow_left₀ (by positivity) hsum 2
    linarith [show (‖testTransform (u : ℝ → ℂ) (-γ) +
      testTransform (u : ℝ → ℂ) (-(starRingEnd ℂ) γ)‖ * ‖γ‖) ^ 2 =
      ‖testTransform (u : ℝ → ℂ) (-γ) +
      testTransform (u : ℝ → ℂ) (-(starRingEnd ℂ) γ)‖ ^ 2 * ‖γ‖ ^ 2 by ring,
      show (2 * C) ^ 2 = 4 * (C * C) by ring]
  unfold pairedPlusTerm
  rw [mul_one_div, div_le_div_iff₀ (by norm_num) (pow_pos hγ0 2)]
  linarith

/-- The negative paired series `pairedMinusTerm u` is unconditionally summable. -/
theorem summable_pairedMinusTerm {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) :
    Summable (pairedMinusTerm u) := by
  set φ := u.toSuzukiSmoothCompactTest.toDerivativeZeroMean
  set C : ℝ := (Real.exp (|a.1| / 2) + 1) * ∫ x : ℝ, ‖(φ : ℝ → ℂ) x‖ with hC
  have hC0 : 0 ≤ C := by
    rw [hC]
    exact mul_nonneg (by positivity) (integral_nonneg fun _ => norm_nonneg _)
  refine Summable.of_nonneg_of_le (pairedMinusTerm_nonneg u) (fun q => ?_)
    (xiSpectralPoint_inv_sq_summable.mul_left (C * C))
  set γ : ℂ := xiSpectralPoint q
  have hγ0 : 0 < ‖γ‖ := norm_pos_iff.mpr (xiSpectralPoint_ne_zero q)
  have h1 : ‖testTransform (u : ℝ → ℂ) (-γ)‖ * ‖γ‖ ≤ C := by
    rw [norm_testTransform_neg_xiSpectralPoint_mul]
    exact norm_suzukiTestRayCoef_le φ q
  have h2 : ‖testTransform (u : ℝ → ℂ) (-(starRingEnd ℂ) γ)‖ * ‖γ‖ ≤ C := by
    rw [norm_testTransform_neg_conj_xiSpectralPoint_mul]
    exact norm_suzukiTestRayCoefBar_le φ q
  have hsub : ‖testTransform (u : ℝ → ℂ) (-γ) -
      testTransform (u : ℝ → ℂ) (-(starRingEnd ℂ) γ)‖ * ‖γ‖ ≤ 2 * C := by
    calc ‖testTransform (u : ℝ → ℂ) (-γ) -
          testTransform (u : ℝ → ℂ) (-(starRingEnd ℂ) γ)‖ * ‖γ‖
        ≤ (‖testTransform (u : ℝ → ℂ) (-γ)‖ +
            ‖testTransform (u : ℝ → ℂ) (-(starRingEnd ℂ) γ)‖) * ‖γ‖ :=
          mul_le_mul_of_nonneg_right (norm_sub_le _ _) hγ0.le
      _ = ‖testTransform (u : ℝ → ℂ) (-γ)‖ * ‖γ‖ +
            ‖testTransform (u : ℝ → ℂ) (-(starRingEnd ℂ) γ)‖ * ‖γ‖ := by ring
      _ ≤ 2 * C := by linarith
  have hsq : ‖testTransform (u : ℝ → ℂ) (-γ) -
      testTransform (u : ℝ → ℂ) (-(starRingEnd ℂ) γ)‖ ^ 2 * ‖γ‖ ^ 2 ≤ 4 * (C * C) := by
    have := pow_le_pow_left₀ (by positivity) hsub 2
    linarith [show (‖testTransform (u : ℝ → ℂ) (-γ) -
      testTransform (u : ℝ → ℂ) (-(starRingEnd ℂ) γ)‖ * ‖γ‖) ^ 2 =
      ‖testTransform (u : ℝ → ℂ) (-γ) -
      testTransform (u : ℝ → ℂ) (-(starRingEnd ℂ) γ)‖ ^ 2 * ‖γ‖ ^ 2 by ring,
      show (2 * C) ^ 2 = 4 * (C * C) by ring]
  unfold pairedMinusTerm
  rw [mul_one_div, div_le_div_iff₀ (by norm_num) (pow_pos hγ0 2)]
  linarith

theorem pairedPlusEnergy_nonneg {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) :
    0 ≤ pairedPlusEnergy u :=
  tsum_nonneg (pairedPlusTerm_nonneg u)

theorem pairedMinusEnergy_nonneg {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) :
    0 ≤ pairedMinusEnergy u :=
  tsum_nonneg (pairedMinusTerm_nonneg u)

/-- **Exact Weil polarization identity**: on every smooth interior source `u`, the restricted Weil
source quadratic equals `pairedPlusEnergy u − pairedMinusEnergy u`. -/
theorem sourceQuadratic_eq_pairedPlusEnergy_sub_pairedMinusEnergy
    {a : SuzukiPositiveAperture} (u : CCMComplexSmoothInteriorSource a) :
    ccmRestrictedWeilSourceQuadratic a u.toCCMFormVector =
      pairedPlusEnergy u - pairedMinusEnergy u := by
  rw [sourceQuadratic_eq_re_tsum, Complex.re_tsum (summable_zeroSumTerm u)]
  simp_rw [re_zeroSumTerm_eq_pairedPlus_sub_pairedMinus]
  exact (summable_pairedPlusTerm u).tsum_sub (summable_pairedMinusTerm u)

/-! ## 2. Single-aperture equivalence: compensated sampling vs. ground-energy floor -/

/-- The compensated sampling bound at aperture `a` with constant `B`:
`E_−(u) ≤ E_+(u) + B ∫ ‖u‖²` for every smooth interior source `u`. -/
def CompensatedSamplingBound (a : SuzukiPositiveAperture) (B : ℝ) : Prop :=
  ∀ u : CCMComplexSmoothInteriorSource a,
    pairedMinusEnergy u ≤ pairedPlusEnergy u + B * ∫ x, ‖u x‖ ^ 2

/-- For a single smooth interior source `u`, `E_−(u) ≤ E_+(u) + B ∫ ‖u‖²` is equivalent to the
Rayleigh lower bound `−B ∫ ‖u‖² ≤ Q_a(u)`. -/
theorem pairedMinusEnergy_le_pairedPlusEnergy_add_iff
    {a : SuzukiPositiveAperture} (u : CCMComplexSmoothInteriorSource a) (B : ℝ) :
    pairedMinusEnergy u ≤ pairedPlusEnergy u + B * ∫ x, ‖u x‖ ^ 2 ↔
      -B * ∫ x, ‖u x‖ ^ 2 ≤ ccmRestrictedWeilSourceQuadratic a u.toCCMFormVector := by
  rw [sourceQuadratic_eq_pairedPlusEnergy_sub_pairedMinusEnergy]
  constructor <;> intro h <;> linarith

/-- **Single-aperture equivalence**: the compensated sampling bound `CompensatedSamplingBound a B`
on smooth interior sources holds if and only if `−B ≤ ccmRestrictedWeilGroundEnergy a`. -/
theorem compensatedSamplingBound_iff_groundEnergy_ge
    (a : SuzukiPositiveAperture) (B : ℝ) :
    CompensatedSamplingBound a B ↔ -B ≤ ccmRestrictedWeilGroundEnergy a := by
  constructor
  · intro h
    have hsm : ∀ u : CCMComplexSmoothInteriorSource a,
        -B * ‖ccmArchimedeanFormToAperture a u.toCCMFormVector‖ ^ 2 ≤
          ccmRestrictedWeilSourceQuadratic a u.toCCMFormVector := by
      intro u
      rw [norm_sq_toAperture_toCCMFormVector]
      exact (pairedMinusEnergy_le_pairedPlusEnergy_add_iff u B).mp (h u)
    have hform : ∀ w : CCMArchimedeanFormDomain a,
        -B * ‖ccmArchimedeanFormToAperture a w‖ ^ 2 ≤
          ccmRestrictedWeilSourceQuadratic a w := by
      intro w
      refine (denseRange_ccmComplexSmoothInteriorSource_toCCMFormVector a).induction_on w ?_ hsm
      exact isClosed_le
        (continuous_const.mul ((ccmArchimedeanFormToAperture a).continuous.norm.pow 2))
        (continuous_ccmRestrictedWeilSourceQuadratic a)
    obtain ⟨w, hw0, hground⟩ := ccmRestrictedWeilSource_exists_groundFormState a
    have hpos : 0 < ‖ccmArchimedeanFormToAperture a w‖ ^ 2 := by positivity
    have hfl := hform w
    rw [hground] at hfl
    exact le_of_mul_le_mul_right hfl hpos
  · intro h u
    rw [pairedMinusEnergy_le_pairedPlusEnergy_add_iff, ← norm_sq_toAperture_toCCMFormVector]
    exact (mul_le_mul_of_nonneg_right h (sq_nonneg _)).trans
      (ccmRestrictedWeilGroundEnergy_mul_formNorm_sq_le_source a u.toCCMFormVector)

/-- Unconditional existence of a compensated sampling bound at every positive aperture `a`, with
sharp constant `B = −ccmRestrictedWeilGroundEnergy a`. -/
theorem exists_compensatedSamplingBound (a : SuzukiPositiveAperture) :
    CompensatedSamplingBound a (-ccmRestrictedWeilGroundEnergy a) :=
  (compensatedSamplingBound_iff_groundEnergy_ge a (-ccmRestrictedWeilGroundEnergy a)).mpr
    (by linarith)

/-- On `a.1 ≤ 3 / 10`, the compensated sampling bound holds unconditionally with the strictly
negative constant `B = −1 / 5000` (`E_−(u) + (1/5000) ‖u‖₂² ≤ E_+(u)`). -/
theorem compensatedSamplingBound_neg_one_div_5000_of_le_three_tenths
    (a : SuzukiPositiveAperture) (ha : a.1 ≤ 3 / 10) :
    CompensatedSamplingBound a (-1 / 5000) := by
  rw [compensatedSamplingBound_iff_groundEnergy_ge, neg_div, neg_neg]
  exact one_div_5000_le_ccmRestrictedWeilGroundEnergy_threeTenths ha

/-- Contrast with the **uncompensated** bound: `∀ u, E_−(u) ≤ B ∫ ‖u‖²` is equivalent to
`UnsignedDepthSamplingBound a (4 * B)`. -/
theorem forall_pairedMinusEnergy_le_iff_unsignedDepthSamplingBound
    (a : SuzukiPositiveAperture) (B : ℝ) :
    (∀ u : CCMComplexSmoothInteriorSource a, pairedMinusEnergy u ≤ B * ∫ x, ‖u x‖ ^ 2) ↔
      UnsignedDepthSamplingBound a (4 * B) := by
  constructor
  · intro h u s
    have hsum : ∑ q ∈ s, pairedMinusTerm u q ≤ pairedMinusEnergy u :=
      (summable_pairedMinusTerm u).sum_le_tsum s (fun q _ => pairedMinusTerm_nonneg u q)
    have h4 : ∑ q ∈ s, ‖testTransform u (-xiSpectralPoint q) -
        testTransform u (-(starRingEnd ℂ) (xiSpectralPoint q))‖ ^ 2 =
        4 * ∑ q ∈ s, pairedMinusTerm u q := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      unfold pairedMinusTerm
      ring
    linarith [h u]
  · intro h u
    refine (summable_pairedMinusTerm u).tsum_le_of_sum_le fun s => ?_
    have hs := h u s
    have h4 : ∑ q ∈ s, ‖testTransform u (-xiSpectralPoint q) -
        testTransform u (-(starRingEnd ℂ) (xiSpectralPoint q))‖ ^ 2 =
        4 * ∑ q ∈ s, pairedMinusTerm u q := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      unfold pairedMinusTerm
      ring
    linarith

/-- Any uncompensated sampling bound `UnsignedDepthSamplingBound a (4 * B)` implies the
compensated sampling bound `CompensatedSamplingBound a B` since `0 ≤ E_+(u)`. -/
theorem compensatedSamplingBound_of_unsignedDepthSamplingBound
    {a : SuzukiPositiveAperture} {B : ℝ}
    (h : UnsignedDepthSamplingBound a (4 * B)) :
    CompensatedSamplingBound a B := by
  intro u
  have hu := (forall_pairedMinusEnergy_le_iff_unsignedDepthSamplingBound a B).mpr h u
  linarith [pairedPlusEnergy_nonneg u]

/-- The uncompensated bound `∃ B ≥ 0, ∀ u, E_−(u) ≤ B ∫ ‖u‖²` at a single aperture `a` is
equivalent to locally bounded off-line depth mass `∃ W, OffLineDepthLocallyBounded W`. -/
theorem exists_uncompensated_pairedMinusEnergy_bound_iff (a : SuzukiPositiveAperture) :
    (∃ B : ℝ, 0 ≤ B ∧ ∀ u : CCMComplexSmoothInteriorSource a,
      pairedMinusEnergy u ≤ B * ∫ x, ‖u x‖ ^ 2) ↔
      ∃ W : ℝ, OffLineDepthLocallyBounded W := by
  rw [← exists_unsignedDepthSamplingBound_iff a]
  constructor
  · rintro ⟨B, hB0, hB⟩
    exact ⟨4 * B, by linarith,
      (forall_pairedMinusEnergy_le_iff_unsignedDepthSamplingBound a B).mp hB⟩
  · rintro ⟨B, hB0, hB⟩
    refine ⟨B / 4, by linarith,
      (forall_pairedMinusEnergy_le_iff_unsignedDepthSamplingBound a (B / 4)).mpr ?_⟩
    convert hB using 1
    ring

/-! ## 3. The compensated width floor across apertures and the ground-energy rate -/

/-- The compensated width floor at rate `σ`: for all sufficiently large apertures `a ≥ A₀` and all
smooth interior sources `u`, `E_−(u) ≤ E_+(u) + C e^{2σa} ∫ ‖u‖²`. -/
def CompensatedWidthFloor (σ : ℝ) : Prop :=
  ∃ C A₀ : ℝ, ∀ a : SuzukiPositiveAperture, A₀ ≤ a.1 →
    CompensatedSamplingBound a (C * Real.exp (2 * σ * a.1))

/-- The admissible rates `σ ≥ 0` of the literal restricted Weil ground energy:
`μ(A) ≥ −C e^{2σA}` for all large apertures. -/
def groundEnergyRates : Set ℝ :=
  {σ : ℝ | 0 ≤ σ ∧ ∃ C A₀ : ℝ, ∀ A : SuzukiPositiveAperture, A₀ ≤ A.1 →
    -(C * Real.exp (2 * σ * A.1)) ≤ ccmRestrictedWeilGroundEnergy A}

/-- The literal restricted Weil ground-energy exponent `sInf groundEnergyRates`. -/
noncomputable def groundEnergyRate : ℝ := sInf groundEnergyRates

/-- **Equivalence across apertures**: `CompensatedWidthFloor σ` holds if and only if the literal
restricted Weil ground energy obeys `μ(A) ≥ −C e^{2σA}` for all large apertures. -/
theorem compensatedWidthFloor_iff_groundEnergy_ge_neg_exp (σ : ℝ) :
    CompensatedWidthFloor σ ↔
      ∃ C A₀ : ℝ, ∀ A : SuzukiPositiveAperture, A₀ ≤ A.1 →
        -(C * Real.exp (2 * σ * A.1)) ≤ ccmRestrictedWeilGroundEnergy A := by
  unfold CompensatedWidthFloor
  simp_rw [compensatedSamplingBound_iff_groundEnergy_ge]

theorem mem_groundEnergyRates_iff_compensatedWidthFloor {σ : ℝ} (hσ : 0 ≤ σ) :
    σ ∈ groundEnergyRates ↔ CompensatedWidthFloor σ := by
  rw [groundEnergyRates, Set.mem_setOf_eq, compensatedWidthFloor_iff_groundEnergy_ge_neg_exp]
  exact ⟨fun h => h.2, fun h => ⟨hσ, h⟩⟩

/-- **A compensated width floor at rate `σ ≥ 0` bounds the zero width by `σ`.** -/
theorem zetaZeroWidth_le_of_compensatedWidthFloor {σ : ℝ} (hσ : 0 ≤ σ)
    (h : CompensatedWidthFloor σ) :
    zetaZeroWidth ≤ σ := by
  obtain ⟨C, A₀, hμ⟩ := (compensatedWidthFloor_iff_groundEnergy_ge_neg_exp σ).mp h
  exact zetaZeroWidth_le_of_ccmRestrictedWeilGroundEnergy_ge_neg_exp hσ hμ

/-- Every compensated width floor rate `σ ≥ 0` is an admissible polar ground-energy rate. -/
theorem mem_polarGroundEnergyRates_of_compensatedWidthFloor {σ : ℝ} (hσ : 0 ≤ σ)
    (h : CompensatedWidthFloor σ) :
    σ ∈ polarGroundEnergyRates := by
  obtain ⟨C, A₀, hμ⟩ := (compensatedWidthFloor_iff_groundEnergy_ge_neg_exp σ).mp h
  exact ⟨hσ, C, A₀, fun A hA => (hμ A hA).trans (ccmRestrictedWeilGroundEnergy_le_polar A)⟩

/-- Every compensated width floor rate `σ ≥ 0` bounds the polar ground-energy exponent:
`polarGroundEnergyRate ≤ σ`. -/
theorem polarGroundEnergyRate_le_of_compensatedWidthFloor {σ : ℝ} (hσ : 0 ≤ σ)
    (h : CompensatedWidthFloor σ) :
    polarGroundEnergyRate ≤ σ :=
  csInf_le bddBelow_polarGroundEnergyRates
    (mem_polarGroundEnergyRates_of_compensatedWidthFloor hσ h)

/-- **Compensated width floor ⟹ dyadic prime-window lag floor**, directly through the Rayleigh
bridge without passing through the zeros. -/
theorem lag_primeWindow_ge_neg_exp_of_compensatedWidthFloor {σ w : ℝ}
    (hw : 0 < w) (hw2 : 2 * w < Real.log 2) (h : CompensatedWidthFloor σ) :
    ∃ C' V : ℝ, 0 ≤ V ∧ ∀ v : ℝ, V ≤ v → -(C' * Real.exp (σ * v)) ≤
      (lagPrimeWindowRHS v w (EF.weilTest (twoBump (modScaledBump w 0) v (-1))
        (twoBump (modScaledBump w 0) v (-1)))).re := by
  obtain ⟨C, A₀, hμ⟩ := (compensatedWidthFloor_iff_groundEnergy_ge_neg_exp σ).mp h
  exact lag_primeWindow_ge_neg_exp_of_ccmRestrictedWeilGroundEnergy_ge_neg_exp hw hw2 hμ

/-- **Closing the reverse ground-rate inequality**: if `CompensatedWidthFloor σ` holds for every
`σ > zetaZeroWidth`, then `polarGroundEnergyRate = zetaZeroWidth` and `groundEnergyRate = zetaZeroWidth`. -/
theorem polarGroundEnergyRate_eq_zetaZeroWidth_of_forall_compensatedWidthFloor
    (h : ∀ σ : ℝ, zetaZeroWidth < σ → CompensatedWidthFloor σ) :
    polarGroundEnergyRate = zetaZeroWidth ∧ groundEnergyRate = zetaZeroWidth := by
  have hb : BddBelow groundEnergyRates := ⟨0, fun _ hσ => hσ.1⟩
  have hne : groundEnergyRates.Nonempty := by
    refine ⟨zetaZeroWidth + 1, (mem_groundEnergyRates_iff_compensatedWidthFloor ?_).mpr
      (h (zetaZeroWidth + 1) (by linarith))⟩
    linarith [zetaZeroWidth_nonneg]
  constructor
  · refine le_antisymm ?_ zetaZeroWidth_le_polarGroundEnergyRate
    refine le_of_forall_pos_le_add fun ε hε => ?_
    exact polarGroundEnergyRate_le_of_compensatedWidthFloor
      (by linarith [zetaZeroWidth_nonneg]) (h (zetaZeroWidth + ε) (by linarith))
  · refine le_antisymm ?_ ?_
    · refine le_of_forall_pos_le_add fun ε hε => ?_
      exact csInf_le hb ((mem_groundEnergyRates_iff_compensatedWidthFloor
        (by linarith [zetaZeroWidth_nonneg])).mpr (h (zetaZeroWidth + ε) (by linarith)))
    · refine le_csInf hne fun σ hσ => ?_
      exact zetaZeroWidth_le_of_compensatedWidthFloor hσ.1
        ((mem_groundEnergyRates_iff_compensatedWidthFloor hσ.1).mp hσ)

/-- Under locally bounded off-line depth mass `OffLineDepthLocallyBounded W`, the compensated
sampling bound holds at every aperture `A` with `depthFloorConst W A.1`. -/
theorem compensatedSamplingBound_of_offLineDepthLocallyBounded {W : ℝ}
    (hW : OffLineDepthLocallyBounded W) (A : SuzukiPositiveAperture) :
    CompensatedSamplingBound A (depthFloorConst W A.1) :=
  (compensatedSamplingBound_iff_groundEnergy_ge A (depthFloorConst W A.1)).mpr
    (neg_depthFloorConst_le_ccmRestrictedWeilGroundEnergy hW A)

/-- Under locally bounded off-line depth mass `OffLineDepthLocallyBounded W`, the compensated
width floor holds at every rate `σ > zetaZeroWidth`. -/
theorem compensatedWidthFloor_of_offLineDepthLocallyBounded {W : ℝ}
    (hW : OffLineDepthLocallyBounded W) {σ : ℝ} (hσ : zetaZeroWidth < σ) :
    CompensatedWidthFloor σ := by
  rw [compensatedWidthFloor_iff_groundEnergy_ge_neg_exp]
  obtain ⟨C, hC⟩ := exists_ccmRestrictedWeilGroundEnergy_ge_neg_exp_of_offLineDepthLocallyBounded hW hσ
  exact ⟨C, 0, fun A _ => hC A⟩

/-- Under locally bounded off-line copies `OffLineCopiesLocallyBounded M`, the compensated
sampling bound holds at every aperture `A` with `clusterFloorConst M A.1`. -/
theorem compensatedSamplingBound_of_offLineCopiesLocallyBounded {M : ℕ}
    (hM : OffLineCopiesLocallyBounded M) (A : SuzukiPositiveAperture) :
    CompensatedSamplingBound A (clusterFloorConst M A.1) :=
  (compensatedSamplingBound_iff_groundEnergy_ge A (clusterFloorConst M A.1)).mpr
    (neg_clusterFloorConst_le_ccmRestrictedWeilGroundEnergy hM A)

/-- Under locally bounded off-line copies `OffLineCopiesLocallyBounded M`, the compensated
width floor holds at every rate `σ > zetaZeroWidth`. -/
theorem compensatedWidthFloor_of_offLineCopiesLocallyBounded {M : ℕ}
    (hM : OffLineCopiesLocallyBounded M) {σ : ℝ} (hσ : zetaZeroWidth < σ) :
    CompensatedWidthFloor σ := by
  rw [compensatedWidthFloor_iff_groundEnergy_ge_neg_exp]
  obtain ⟨C, hC⟩ := exists_ccmRestrictedWeilGroundEnergy_ge_neg_exp_of_offLineCopiesLocallyBounded hM hσ
  exact ⟨C, 0, fun A _ => hC A⟩

/-- **Unconditional dichotomy**: either `CompensatedWidthFloor σ` holds for every `σ > zetaZeroWidth`
(closing the reverse ground-rate inequality `polarGroundEnergyRate = groundEnergyRate = zetaZeroWidth`),
or the off-line depth mass clusters without bound on unit windows. -/
theorem forall_compensatedWidthFloor_or_depthMass_clusters :
    (∀ σ : ℝ, zetaZeroWidth < σ → CompensatedWidthFloor σ) ∨
      ∀ W : ℝ, ¬ OffLineDepthLocallyBounded W := by
  by_cases h : ∃ W : ℝ, OffLineDepthLocallyBounded W
  · obtain ⟨W, hW⟩ := h
    exact Or.inl fun _ hσ => compensatedWidthFloor_of_offLineDepthLocallyBounded hW hσ
  · push Not at h
    exact Or.inr h

/-! ## 4. Consequences for damping continuation and RH -/

/-- A compensated width floor at rate `σ ≥ 0` forces `Admits dampedMobiusEnergy ε` at every
damping `ε > σ`. -/
theorem admits_dampedMobiusEnergy_of_compensatedWidthFloor {σ ε : ℝ}
    (hσ : 0 ≤ σ) (h : CompensatedWidthFloor σ) (hε : σ < ε) :
    Admits dampedMobiusEnergy ε := by
  have hw : zetaZeroWidth ≤ σ := zetaZeroWidth_le_of_compensatedWidthFloor hσ h
  have hlt : zetaZeroAbscissa - 1 / 2 < ε := by
    linarith [zetaZeroWidth_eq_zetaZeroAbscissa_sub_half]
  exact admits_dampedMobiusEnergy_of_zetaZeroAbscissa_sub_half_lt hlt

/-- A compensated width floor at rate `σ ≥ 0` forces signed averaged damping continuation on every
compact interval `[a, c] ⊂ (σ, ∞)`. -/
theorem averagedDampingContinuation_of_compensatedWidthFloor {σ a c : ℝ}
    (hσ : 0 ≤ σ) (h : CompensatedWidthFloor σ) (ha : σ < a) (hac : a ≤ c) :
    AveragedDampingContinuation a c := by
  have hw : zetaZeroWidth ≤ σ := zetaZeroWidth_le_of_compensatedWidthFloor hσ h
  have hlt : zetaZeroAbscissa - 1 / 2 < a := by
    linarith [zetaZeroWidth_eq_zetaZeroAbscissa_sub_half]
  exact averagedDampingContinuation_of_zetaZeroAbscissa_sub_half_lt hlt hac

/-- **RH is equivalent to `E_−(u) ≤ E_+(u)` at all apertures** (and to `CompensatedWidthFloor σ`
for every `σ > 0`). -/
theorem riemannHypothesis_iff_pairedMinusEnergy_le_pairedPlusEnergy :
    RiemannHypothesis ↔
      ∀ a : SuzukiPositiveAperture, ∀ u : CCMComplexSmoothInteriorSource a,
        pairedMinusEnergy u ≤ pairedPlusEnergy u := by
  have hRH_iff : RiemannHypothesis ↔
      ∀ a : SuzukiPositiveAperture, 0 ≤ ccmRestrictedWeilGroundEnergy a := by
    constructor
    · exact fun hRH a => ccmRestrictedWeilGroundEnergy_nonneg_of_riemannHypothesis' hRH a
    · intro h
      by_contra hRH
      obtain ⟨B, hB⟩ := exists_ccmRestrictedWeilGroundEnergy_neg_of_not_riemannHypothesis hRH
      exact absurd (h B) (not_le.mpr hB)
  rw [hRH_iff]
  refine forall_congr' fun a => ?_
  have h := compensatedSamplingBound_iff_groundEnergy_ge a 0
  simp only [CompensatedSamplingBound, zero_mul, add_zero, neg_zero] at h
  exact h.symm

theorem riemannHypothesis_iff_forall_pos_compensatedWidthFloor :
    RiemannHypothesis ↔ ∀ σ : ℝ, 0 < σ → CompensatedWidthFloor σ := by
  constructor
  · intro hRH σ hσ
    refine ⟨0, 0, fun a _ u => ?_⟩
    rw [zero_mul, zero_mul, add_zero]
    exact riemannHypothesis_iff_pairedMinusEnergy_le_pairedPlusEnergy.mp hRH a u
  · intro h
    rw [riemannHypothesis_iff_zetaZeroWidth_eq_zero]
    refine le_antisymm ?_ zetaZeroWidth_nonneg
    refine le_of_forall_pos_le_add fun ε hε => ?_
    rw [zero_add]
    exact zetaZeroWidth_le_of_compensatedWidthFloor hε.le (h ε hε)

end

end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
