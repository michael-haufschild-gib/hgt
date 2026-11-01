import GaloisForLFunctions.TransMetzlerWeilPositivity.ReceiverRate.TheScaleAveragedSincProfile
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheNormalizedAtomicTransform
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.EveryProfileWithoutRealFourierZerosKeepsAGammaReserve
import GaloisForLFunctions.RHTower.CosineTranslatedWeilTests
import GaloisForLFunctions.RHTower.EvenSectorFullPositivity

/-!
# A zero-free logarithmic Denjoy–Carleman profile on the unit interval

Translate the mass-preserving eightfold dilation of the averaged sinc profile.
The resulting profile has unit mass, support in `[0,1]`, and derivative bounds
`‖φ⁽q⁾‖₁ ≤ 32·96^q·dcLogWeight q`. Its real Fourier transform never vanishes.
-/

noncomputable section
set_option autoImplicit false

open MeasureTheory Filter Topology Zeta23
open scoped ContDiff FourierTransform

namespace GaloisForLFunctions.TransMetzlerWeilPositivity

open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics ArithmeticCastelnuovoSeveri

/-- Unit-mass normalization of the scale-averaged sinc autocorrelation. -/
def zeroFreeLogProfile (x : ℝ) : ℝ :=
  dilate 8 averagedSincProfile (x - 1 / 2)

theorem contDiff_zeroFreeLogProfile : ContDiff ℝ ∞ zeroFreeLogProfile :=
  (contDiff_const.mul (contDiff_averagedSincProfile.comp
    (contDiff_const.mul contDiff_id))).comp (contDiff_id.sub contDiff_const)

theorem zeroFreeLogProfile_nonneg (x : ℝ) : 0 ≤ zeroFreeLogProfile x :=
  mul_nonneg (by norm_num) (averagedSincProfile_nonneg _)

theorem zeroFreeLogProfile_eq_zero (x : ℝ) (hx : x ∉ Set.Icc 0 1) :
    zeroFreeLogProfile x = 0 := by
  have hb : 4 < |8 * (x - 1 / 2)| := by
    by_contra hn
    have h := abs_le.mp (le_of_not_gt hn)
    apply hx
    constructor <;> linarith only [h.1, h.2]
  rw [zeroFreeLogProfile, dilate, averagedSincProfile_vanishesOff _ hb, mul_zero]

theorem hasCompactSupport_zeroFreeLogProfile : HasCompactSupport zeroFreeLogProfile :=
  hasCompactSupport_of_unitSupport zeroFreeLogProfile_eq_zero

theorem integral_zeroFreeLogProfile : ∫ x, zeroFreeLogProfile x = 1 := by
  change (∫ x, dilate 8 averagedSincProfile (x - 1 / 2)) = 1
  rw [integral_sub_right_eq_self (dilate 8 averagedSincProfile) (1 / 2),
    integral_dilate (by norm_num : (0 : ℝ) < 8), integral_averagedSincProfile]

/-- Affine normalization preserves the logarithmic derivative class. -/
theorem integral_abs_iteratedDeriv_zeroFreeLogProfile_le (q : ℕ) :
    ∫ x, |iteratedDeriv q zeroFreeLogProfile x| ≤ 32 * 96 ^ q * dcLogWeight q := by
  have heq : zeroFreeLogProfile = fun x => dilate 8 averagedSincProfile (-(1 / 2) + x) := by
    funext x
    rw [zeroFreeLogProfile, sub_eq_neg_add]
  rw [heq, iteratedDeriv_comp_const_add,
    integral_add_left_eq_self (fun x => |iteratedDeriv q (dilate 8 averagedSincProfile) x|)
      (-(1 / 2)),
    integral_abs_iteratedDeriv_dilate contDiff_averagedSincProfile (by norm_num)]
  calc
    (8 : ℝ) ^ q * (∫ x, |iteratedDeriv q averagedSincProfile x|)
        ≤ 8 ^ q * (32 * 12 ^ q * dcLogWeight q) :=
      mul_le_mul_of_nonneg_left (integral_abs_iteratedDeriv_averagedSincProfile_le q)
        (by positivity)
    _ = 32 * 96 ^ q * dcLogWeight q := by
      rw [show (96 : ℝ) = 8 * 12 by norm_num, mul_pow]
      ring

theorem paperFT_zeroFreeLogProfile (z : ℂ) :
    Zeta23.paperFT (cx zeroFreeLogProfile) z =
      Complex.exp (Complex.I * z * (1 / 2)) *
        Zeta23.paperFT (cx averagedSincProfile) (z / 8) := by
  change Zeta23.paperFT (fun x => (dilate 8 averagedSincProfile (x - 1 / 2) : ℂ)) z = _
  rw [_root_.RHTower.paperFT_comp_sub (fun u => (dilate 8 averagedSincProfile u : ℂ)) (1 / 2) z,
    paperFT_massPreservingDilate (by norm_num)]
  norm_num

/-- Translation only changes phase; real conjugation selects positive Fourier frequencies. -/
theorem norm_paperFT_zeroFreeLogProfile (r : ℝ) :
    ‖Zeta23.paperFT (cx zeroFreeLogProfile) (r : ℂ)‖ =
      ‖𝓕 (fun x => (averagedSincProfile x : ℂ)) (r / (16 * Real.pi))‖ := by
  calc
    _ = ‖Zeta23.paperFT (cx averagedSincProfile) ((r : ℂ) / 8)‖ := by
      rw [paperFT_zeroFreeLogProfile, norm_mul, Complex.norm_exp]
      simp
    _ = ‖Zeta23.paperFT (cx averagedSincProfile) (-((r : ℂ) / 8))‖ := by
      rw [_root_.RHTower.EvenSector.paperFT_ofReal_neg_conj]
      simp [cx]
    _ = _ := by
      rw [RHTower.WeilDeletion.fourier_eq_paperFT]
      congr 2
      push_cast
      field_simp [Real.pi_ne_zero]
      <;> ring

theorem paperFT_zeroFreeLogProfile_ne_zero (r : ℝ) :
    Zeta23.paperFT (cx zeroFreeLogProfile) (r : ℂ) ≠ 0 := by
  apply norm_pos_iff.mp
  rw [norm_paperFT_zeroFreeLogProfile]
  exact norm_pos_iff.mpr (fourier_averagedSincProfile_ne_zero _)

theorem integral_zeroFreeLogProfile_sq_pos : 0 < ∫ x, zeroFreeLogProfile x ^ 2 :=
  integral_sq_pos_of_noRealZero (contDiff_zeroFreeLogProfile.of_le (natCast_le_infty 2))
    zeroFreeLogProfile_eq_zero paperFT_zeroFreeLogProfile_ne_zero

/-- Squared-transform floor on the band from `c` to `101c`. -/
def zeroFreeLogBandFloor (c : ℝ) : ℝ :=
  Real.exp (-(202 * sincTailConst *
    ((c / (16 * Real.pi)) / Real.log (c / (16 * Real.pi)) ^ 2)))

theorem zeroFreeLogBandFloor_pos (c : ℝ) : 0 < zeroFreeLogBandFloor c :=
  Real.exp_pos _

theorem eventually_zeroFreeLogProfile_band_floor :
    ∀ᶠ c : ℝ in atTop, ∀ r ∈ Set.Icc c (101 * c),
      zeroFreeLogBandFloor c ≤ ‖Zeta23.paperFT (cx zeroFreeLogProfile) (r : ℂ)‖ ^ 2 := by
  obtain ⟨A, hA⟩ := eventually_atTop.mp eventually_fourier_averagedSincProfile_band_ge
  have hd : 0 < 16 * Real.pi := by positivity
  filter_upwards [eventually_ge_atTop (A * (16 * Real.pi))] with c hc
  have hcA : A ≤ c / (16 * Real.pi) := (le_div_iff₀ hd).mpr hc
  intro r hr
  have hband : r / (16 * Real.pi) ∈
      Set.Icc (c / (16 * Real.pi)) (101 * (c / (16 * Real.pi))) := by
    constructor
    · exact div_le_div_of_nonneg_right hr.1 hd.le
    · have h := div_le_div_of_nonneg_right hr.2 hd.le
      simpa only [mul_div_assoc] using h
  have hfloor := hA _ hcA _ hband
  rw [norm_paperFT_zeroFreeLogProfile, norm_fourier_averagedSincProfile_eq_re]
  have heq : zeroFreeLogBandFloor c =
      Real.exp (-(101 * sincTailConst *
        ((c / (16 * Real.pi)) / Real.log (c / (16 * Real.pi)) ^ 2))) ^ 2 := by
    rw [zeroFreeLogBandFloor]
    rw [pow_two (Real.exp _), ← Real.exp_add]
    congr 1
    ring
  rw [heq]
  exact pow_le_pow_left₀ (Real.exp_pos _).le hfloor 2

end GaloisForLFunctions.TransMetzlerWeilPositivity

#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.integral_abs_iteratedDeriv_zeroFreeLogProfile_le
#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.paperFT_zeroFreeLogProfile_ne_zero
#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.eventually_zeroFreeLogProfile_band_floor
