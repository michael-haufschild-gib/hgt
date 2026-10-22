import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmSoninCartanWeylEscapeReconstruction
import GaloisForLFunctions.RHTower.SourceHorizontalGammaSixPairedDefectGaussHodgeCurvature
import GaloisForLFunctions.RHTower.BurnolSoninProjectedEvaluationTransport

/-!
# Hedenmalm--Sonin Cartan/Gamma-six mass shell

The squared norms of the two entire Mellin-orientation legs give a nonnegative
trace excess and a signed orientation current.  Their determinant-one law puts
these observables on one exact hyperbolic mass shell.  The trace excess is
precisely the Gamma-six opposite-boundary curvature, while the current is the
coefficient of the actual Burnol bilateral aperture defect energy.

Thus Gamma-six curvature and Burnol signed holonomy are two coordinates of one
Cartan mode, not independent constraints.  Their common neutral locus is the
critical wall and is also the unit lower-gain locus of the Weyl quotient.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped InnerProductSpace

noncomputable section

namespace RHTower

def burnolSoninCartanEnergyTraceExcess (r : ℝ) (w : ℂ) : ℝ :=
  ‖(burnolSoninMellinOrientationPair r w).1‖ ^ 2 +
    ‖(burnolSoninMellinOrientationPair r w).2‖ ^ 2 - 2

def burnolSoninCartanEnergyOrientationCurrent (r : ℝ) (w : ℂ) : ℝ :=
  ‖(burnolSoninMellinOrientationPair r w).1‖ ^ 2 -
    ‖(burnolSoninMellinOrientationPair r w).2‖ ^ 2

theorem burnolSoninCartanEnergyTraceExcess_eq_gammaSixCurvature
    {r : ℝ} (hr : 0 < r) (w : ℂ) :
    burnolSoninCartanEnergyTraceExcess r w =
      sourceHorizontalGammaSixUnitOppositeBoundaryCurvature
        (Real.log r * (2 * w.re - 1)) := by
  rw [burnolSoninCartanEnergyTraceExcess,
    burnolSoninMellinOrientationPair, norm_inv,
    norm_burnolMellinDilationCharacter_sq r hr w,
    norm_burnolMellinDilationCharacter_inv_sq r hr w,
    sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_eq,
    Real.cosh_eq, Real.rpow_def_of_pos hr, Real.rpow_def_of_pos hr]
  ring_nf

theorem burnolSoninCartanEnergyOrientationCurrent_eq_rpow
    {r : ℝ} (hr : 0 < r) (w : ℂ) :
    burnolSoninCartanEnergyOrientationCurrent r w =
      r ^ (2 * w.re - 1) - r ^ (1 - 2 * w.re) := by
  rw [burnolSoninCartanEnergyOrientationCurrent,
    burnolSoninMellinOrientationPair, norm_inv,
    norm_burnolMellinDilationCharacter_sq r hr w,
    norm_burnolMellinDilationCharacter_inv_sq r hr w]

theorem burnolSoninCartan_energy_product_eq_one
    {r : ℝ} (hr : 0 < r) (w : ℂ) :
    ‖(burnolSoninMellinOrientationPair r w).1‖ ^ 2 *
        ‖(burnolSoninMellinOrientationPair r w).2‖ ^ 2 = 1 := by
  calc
    ‖(burnolSoninMellinOrientationPair r w).1‖ ^ 2 *
          ‖(burnolSoninMellinOrientationPair r w).2‖ ^ 2 =
        (‖(burnolSoninMellinOrientationPair r w).1‖ *
          ‖(burnolSoninMellinOrientationPair r w).2‖) ^ 2 := by ring
    _ = ‖(burnolSoninMellinOrientationPair r w).1 *
          (burnolSoninMellinOrientationPair r w).2‖ ^ 2 := by rw [norm_mul]
    _ = 1 := by rw [burnolSoninMellinOrientationPair_mul_eq_one hr]; norm_num

theorem burnolSoninCartan_mass_shell
    {r : ℝ} (hr : 0 < r) (w : ℂ) :
    (burnolSoninCartanEnergyTraceExcess r w + 2) ^ 2 -
        burnolSoninCartanEnergyOrientationCurrent r w ^ 2 = 4 := by
  have hprod := burnolSoninCartan_energy_product_eq_one hr w
  rw [burnolSoninCartanEnergyTraceExcess,
    burnolSoninCartanEnergyOrientationCurrent]
  nlinarith

theorem burnolSoninCartan_curvature_current_identity
    {r : ℝ} (hr : 0 < r) (w : ℂ) :
    burnolSoninCartanEnergyTraceExcess r w *
        (burnolSoninCartanEnergyTraceExcess r w + 4) =
      burnolSoninCartanEnergyOrientationCurrent r w ^ 2 := by
  have h := burnolSoninCartan_mass_shell hr w
  nlinarith

theorem burnolSoninCartanEnergyTraceExcess_nonneg
    {r : ℝ} (hr : 0 < r) (w : ℂ) :
    0 ≤ burnolSoninCartanEnergyTraceExcess r w := by
  rw [burnolSoninCartanEnergyTraceExcess_eq_gammaSixCurvature hr]
  exact sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_nonneg _

theorem burnolSoninCartanEnergyTraceExcess_pos_iff
    {r : ℝ} (hr : 1 < r) (w : ℂ) :
    0 < burnolSoninCartanEnergyTraceExcess r w ↔ w.re ≠ 1 / 2 := by
  rw [burnolSoninCartanEnergyTraceExcess_eq_gammaSixCurvature
      (zero_lt_one.trans hr),
    sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_pos_iff]
  have hlog : Real.log r ≠ 0 := (Real.log_pos hr).ne'
  constructor
  · intro h hw
    apply h
    rw [hw]
    norm_num
  · intro h hw
    apply h
    have hrate : 2 * w.re - 1 = 0 :=
      (mul_eq_zero.mp hw).resolve_left hlog
    linarith

theorem burnolExtended_bilateralApertureDefectEnergy_eq_cartanCurrent
    {w : ℂ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1)
    {a r : ℝ} (ha : 0 < a) (hr : 1 < r) :
    ‖burnolExtendedApertureDefectMinus hlo hhi ha hr‖ ^ 2 -
        ‖burnolExtendedApertureDefectPlus hlo hhi ha hr‖ ^ 2 =
      burnolSoninCartanEnergyOrientationCurrent r w *
        ‖burnolExtendedSoninEvaluationVector w a hlo hhi ha‖ ^ 2 := by
  rw [burnolExtended_bilateralApertureDefectEnergy hlo hhi ha hr,
    burnolSoninCartanEnergyOrientationCurrent_eq_rpow (zero_lt_one.trans hr)]

theorem burnolSoninCartanEnergyTraceExcess_eq_zero_iff
    {r : ℝ} (hr : 1 < r) (w : ℂ) :
    burnolSoninCartanEnergyTraceExcess r w = 0 ↔ w.re = 1 / 2 := by
  rw [burnolSoninCartanEnergyTraceExcess_eq_gammaSixCurvature
      (zero_lt_one.trans hr),
    sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_eq_zero_iff]
  have hlog : Real.log r ≠ 0 := (Real.log_pos hr).ne'
  constructor
  · intro h
    have hrate : 2 * w.re - 1 = 0 :=
      (mul_eq_zero.mp h).resolve_left hlog
    linarith
  · intro h
    rw [h]
    norm_num

theorem burnolSoninCartanEnergyOrientationCurrent_eq_zero_iff
    {r : ℝ} (hr : 1 < r) (w : ℂ) :
    burnolSoninCartanEnergyOrientationCurrent r w = 0 ↔ w.re = 1 / 2 := by
  rw [burnolSoninCartanEnergyOrientationCurrent_eq_rpow (zero_lt_one.trans hr)]
  exact burnol_rpowOrientation_zero_iff r w.re hr

theorem burnolSoninCartan_neutrality_equivalences
    {r : ℝ} (hr : 1 < r) (w : ℂ) :
    (burnolSoninCartanEnergyTraceExcess r w = 0 ↔
      burnolSoninCartanEnergyOrientationCurrent r w = 0) ∧
    (burnolSoninCartanEnergyOrientationCurrent r w = 0 ↔
      min ‖(burnolSoninMellinOrientationPair r w).1‖
        ‖(burnolSoninMellinOrientationPair r w).2‖ = 1) := by
  rw [burnolSoninCartanEnergyTraceExcess_eq_zero_iff hr,
    burnolSoninCartanEnergyOrientationCurrent_eq_zero_iff hr,
    burnolSoninMellinOrientationPair_lower_gain_eq_one_iff hr]
  exact ⟨Iff.rfl, Iff.rfl⟩

theorem burnolSoninCartanEnergyTraceExcess_xi
    (q : XiZeroCopy) (hoff : (xiSpectralPoint q).im ≠ 0)
    {r : ℝ} (hr : 1 < r) :
    burnolSoninCartanEnergyTraceExcess r
        (((xiSoninRightOrientedCopy q).1 : ℂ)) =
      2 * (Real.cosh
        (2 * Real.log r * thetaXiSoninApertureLyapunovRate q) - 1) := by
  rw [burnolSoninCartanEnergyTraceExcess_eq_gammaSixCurvature
      (zero_lt_one.trans hr),
    sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_eq]
  have hneg := xiSpectralPoint_im_xiSoninRightOrientedCopy_neg q hoff
  have habs := xiSpectralPoint_im_xiSoninRightOrientedCopy_abs q
  rw [abs_of_neg hneg] at habs
  have hw :
      (((xiSoninRightOrientedCopy q).1 : ℂ)).re - 1 / 2 =
        thetaXiSoninApertureLyapunovRate q := by
    rw [← criticalAffine_xiSoninRightOrientedCopy, re_centeredSpectralPoint]
    linarith [habs]
  have harg :
      Real.log r *
          (2 * (((xiSoninRightOrientedCopy q).1 : ℂ)).re - 1) =
        2 * Real.log r * thetaXiSoninApertureLyapunovRate q := by
    rw [show 2 * (((xiSoninRightOrientedCopy q).1 : ℂ)).re - 1 =
      2 * ((((xiSoninRightOrientedCopy q).1 : ℂ)).re - 1 / 2) by ring, hw]
    ring
  rw [harg]

end RHTower
