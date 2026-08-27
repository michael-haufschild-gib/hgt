import GaloisForLFunctions.RHTower.XiPhysicalPrimeApertureThetaAbelLandauNoMaximum
import GaloisForLFunctions.RHTower.XiGuinandWeilSpectralRectangle
import GaloisForLFunctions.RHTower.RectangularWindowAmplitudeAnalytic
import GaloisForLFunctions.RHTower.CCMRectangularWeilCompleteness

/-!
# Physical theta--Abel energy Weil source detector

The scalarized physical theta--Abel response has an apparent pole from the
restored factor `(z + 1) / z`.  Multiplying it by the physical logarithmic
window cancels that pole exactly and produces an entire mode amplitude.
Squaring this mode gives a nonvanishing inverse-square coefficient system.

This file welds that exact physical energy to a bilateral entire Weil test,
proves an aperture-uniform summable remainder, folds the full Xi divisor to
the right divisor, and transfers Landau oscillation to both the complete Weil
value and exact continued prime--archimedean source contours.
-/

open Complex Filter Topology Set

namespace RHTower

noncomputable section

/-- Entire one-edge amplitude of the scalarized physical theta--Abel response. -/
def xiPhysicalThetaAbelEntireModeAmplitude
    (L A c : ℝ) (w : ℂ) : ℂ :=
  rectangularWindowAmplitude L w *
    (w + 1 / 2) * rectangularWindowAmplitude c (1 / 2 - w) *
    rectangularWindowAmplitude A (w - 1 / 2)

theorem xiPhysicalThetaAbelEntireModeAmplitude_eq_physical
    (L A c : ℝ) (q : XiRightZeroCopy) :
    xiPhysicalThetaAbelEntireModeAmplitude L A c (xiRightCenteredZero q) =
      rectangularWindowAmplitude L (xiRightCenteredZero q) *
        xiPhysicalLogWindowModeMultiplier c (xiRightThetaAbelExponent q) *
        ((xiRightThetaAbelExponent q + 1) / xiRightThetaAbelExponent q) *
        rectangularWindowAmplitude A (xiRightThetaAbelExponent q) := by
  let z := xiRightThetaAbelExponent q
  have hz0 : z ≠ 0 := xiRightThetaAbelExponent_ne_zero q
  have hw : xiRightCenteredZero q = z + 1 / 2 := by
    dsimp [z, xiRightThetaAbelExponent]
    ring
  rw [xiPhysicalThetaAbelEntireModeAmplitude,
    xiPhysicalLogWindowModeMultiplier_eq_mul_rectangularWindowAmplitude]
  rw [hw]
  change rectangularWindowAmplitude L (z + 1 / 2) *
      (z + 1 / 2 + 1 / 2) * rectangularWindowAmplitude c (1 / 2 - (z + 1 / 2)) *
        rectangularWindowAmplitude A (z + 1 / 2 - 1 / 2) =
    rectangularWindowAmplitude L (z + 1 / 2) *
      (z * rectangularWindowAmplitude c (-z)) * ((z + 1) / z) *
        rectangularWindowAmplitude A z
  field_simp [hz0]
  ring

theorem xiPhysicalThetaAbelEntireModeAmplitude_ne_zero
    {L A c : ℝ} (hL : 0 < L) (hA : 0 < A) (hc : 0 < c)
    (q : XiRightZeroCopy) :
    xiPhysicalThetaAbelEntireModeAmplitude L A c (xiRightCenteredZero q) ≠ 0 := by
  rw [xiPhysicalThetaAbelEntireModeAmplitude_eq_physical]
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_
  · exact rectangularWindowAmplitude_ne_zero hL (xiRightCenteredZero_re_pos q)
  · exact xiPhysicalLogWindowModeMultiplier_ne_zero hc
      (xiRightThetaAbelExponent_re_neg q)
  · exact div_ne_zero
      (by
        intro hsum
        apply xiRightThetaAbelExponent_ne_neg_one q
        linear_combination hsum)
      (xiRightThetaAbelExponent_ne_zero q)
  · exact rectangularWindowAmplitude_ne_zero_of_re_neg hA
      (xiRightThetaAbelExponent_re_neg q)

theorem norm_xiPhysicalThetaAbelEntireModeAmplitude_xiRight_le
    {A c : ℝ} (hA : 0 < A) (hc : 0 < c)
    (L : ℝ) (q : XiRightZeroCopy) :
    ‖xiPhysicalThetaAbelEntireModeAmplitude L A c (xiRightCenteredZero q)‖ ≤
      (4 * (1 + Real.exp (A / 2)) * (1 + Real.exp (|L| / 2))) /
        ‖xiSpectralPoint q.1‖ := by
  have hbase := norm_rectangularWindowAmplitude_le L
    (xiRightCenteredZero_ne_zero q)
    (le_of_lt (abs_xiRightCenteredZero_re_lt_half q))
  have hwindow := norm_xiPhysicalLogWindowModeMultiplier_le_two_of_re_neg
    hc (xiRightThetaAbelExponent_re_neg q)
  have hrestore := norm_xiRightThetaAbel_restoredFactor_le_two q
  have haperture := norm_rectangularWindowAmplitude_xiRightThetaAbel_le hA q
  rw [xiPhysicalThetaAbelEntireModeAmplitude_eq_physical,
    norm_mul, norm_mul, norm_mul]
  have hbase' : ‖rectangularWindowAmplitude L (xiRightCenteredZero q)‖ ≤
      (1 + Real.exp (|L| / 2)) / ‖xiSpectralPoint q.1‖ := by
    simpa [xiRightCenteredZero] using hbase
  calc
    ‖rectangularWindowAmplitude L (xiRightCenteredZero q)‖ *
          ‖xiPhysicalLogWindowModeMultiplier c (xiRightThetaAbelExponent q)‖ *
        ‖(xiRightThetaAbelExponent q + 1) / xiRightThetaAbelExponent q‖ *
        ‖rectangularWindowAmplitude A (xiRightThetaAbelExponent q)‖
        ≤ ((1 + Real.exp (|L| / 2)) / ‖xiSpectralPoint q.1‖) *
            2 * 2 * (1 + Real.exp (A / 2)) := by
          gcongr
    _ = (4 * (1 + Real.exp (A / 2)) * (1 + Real.exp (|L| / 2))) /
        ‖xiSpectralPoint q.1‖ := by ring

/-- Energy coefficient: square of the entire scalar physical mode amplitude. -/
def xiPhysicalThetaAbelEnergyCoefficient
    (L A c : ℝ) (q : XiRightZeroCopy) : ℂ :=
  xiPhysicalThetaAbelEntireModeAmplitude L A c (xiRightCenteredZero q) ^ 2

theorem xiPhysicalThetaAbelEntireModeAmplitude_conj
    (L A c : ℝ) (w : ℂ) :
    xiPhysicalThetaAbelEntireModeAmplitude L A c ((starRingEnd ℂ) w) =
      (starRingEnd ℂ) (xiPhysicalThetaAbelEntireModeAmplitude L A c w) := by
  have hcarg : (starRingEnd ℂ) (1 / 2 - w) =
      1 / 2 - (starRingEnd ℂ) w := by
    simp only [map_sub, map_div₀, map_one, map_ofNat]
  have hAarg : (starRingEnd ℂ) (w - 1 / 2) =
      (starRingEnd ℂ) w - 1 / 2 := by
    simp only [map_sub, map_div₀, map_one, map_ofNat]
  rw [xiPhysicalThetaAbelEntireModeAmplitude,
    xiPhysicalThetaAbelEntireModeAmplitude]
  rw [← rectangularWindowAmplitude_conj L w,
    ← hcarg, ← rectangularWindowAmplitude_conj c (1 / 2 - w),
    ← hAarg, ← rectangularWindowAmplitude_conj A (w - 1 / 2)]
  simp only [map_mul, map_add, map_div₀, map_one, map_ofNat]

theorem xiPhysicalThetaAbelEnergyCoefficient_conj
    (L A c : ℝ) (q : XiRightZeroCopy) :
    xiPhysicalThetaAbelEnergyCoefficient L A c (xiRightZeroCopyConjEquiv q) =
      (starRingEnd ℂ) (xiPhysicalThetaAbelEnergyCoefficient L A c q) := by
  rw [xiPhysicalThetaAbelEnergyCoefficient, xiPhysicalThetaAbelEnergyCoefficient,
    xiRightCenteredZero_conj, xiPhysicalThetaAbelEntireModeAmplitude_conj, map_pow]

theorem xiPhysicalThetaAbelEnergyCoefficient_eq_of_support_eq
    (L A c : ℝ) {q r : XiRightZeroCopy} (h : q.1.1 = r.1.1) :
    xiPhysicalThetaAbelEnergyCoefficient L A c q =
      xiPhysicalThetaAbelEnergyCoefficient L A c r := by
  rw [xiPhysicalThetaAbelEnergyCoefficient, xiPhysicalThetaAbelEnergyCoefficient,
    xiRightCenteredZero_eq_of_support_eq h]

def xiPhysicalThetaAbelEnergyCoefficientSystem
    {L A c : ℝ} (hL : 0 < L) (hA : 0 < A) (hc : 0 < c) :
    XiRightCoefficientSystem where
  coefficient := xiPhysicalThetaAbelEnergyCoefficient L A c
  normBound :=
    (4 * (1 + Real.exp (A / 2)) * (1 + Real.exp (|L| / 2))) ^ 2
  normBound_nonneg := sq_nonneg _
  norm_le q := by
    rw [xiPhysicalThetaAbelEnergyCoefficient, norm_pow]
    have h := norm_xiPhysicalThetaAbelEntireModeAmplitude_xiRight_le hA hc L q
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    rw [div_pow] at h2
    exact h2
  conjugate q := xiPhysicalThetaAbelEnergyCoefficient_conj L A c q
  support_eq {q r} h := xiPhysicalThetaAbelEnergyCoefficient_eq_of_support_eq L A c h
  nonzero q := pow_ne_zero 2
    (xiPhysicalThetaAbelEntireModeAmplitude_ne_zero hL hA hc q)

def xiPhysicalThetaAbelEnergyLandauResponse
    (L A c : ℝ) (n : ℕ) : ℝ :=
  (2 * ∑' q : XiRightZeroCopy,
    xiPhysicalThetaAbelEnergyCoefficient L A c q *
      (n : ℂ) ^ xiRightCenteredZero q).re

theorem xiPhysicalThetaAbelEnergyLandauResponse_eq_weighted
    {L A c : ℝ} (hL : 0 < L) (hA : 0 < A) (hc : 0 < c) (n : ℕ) :
    xiPhysicalThetaAbelEnergyLandauResponse L A c n =
      xiWeightedRightDirichletCoefficientReal
        (xiPhysicalThetaAbelEnergyCoefficientSystem hL hA hc) n := by
  rfl

theorem xiPhysicalThetaAbelEnergyLandauResponse_cofinally_unbounded_below
    {L A c : ℝ} (hL : 0 < L) (hA : 0 < A) (hc : 0 < c)
    (hne : Nonempty XiRightZeroCopy) :
    ∀ B : ℝ, ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      xiPhysicalThetaAbelEnergyLandauResponse L A c n < B := by
  simpa only [xiPhysicalThetaAbelEnergyLandauResponse_eq_weighted hL hA hc] using
    xiWeightedRightDirichletCoefficientReal_cofinally_unbounded_below
      (xiPhysicalThetaAbelEnergyCoefficientSystem hL hA hc) hne

theorem norm_xiPhysicalThetaAbelEntireModeAmplitude_le_of_strip
    {A c : ℝ} (hA : 0 < A) (hc : 0 < c)
    (L : ℝ) {w : ℂ} (hstrip : |w.re| < 1 / 2) (hheight : 1 < |w.im|) :
    ‖xiPhysicalThetaAbelEntireModeAmplitude L A c w‖ ≤
      (4 * (1 + Real.exp A) * (1 + Real.exp (|L| / 2))) / ‖w‖ := by
  let z := w - 1 / 2
  have hw0 : w ≠ 0 := by
    intro hw
    rw [hw] at hheight
    norm_num at hheight
  have hzneg : z.re < 0 := by
    dsimp [z]
    have := (abs_lt.mp hstrip).2
    norm_num at this ⊢
    linarith
  have hzlower : -(1 : ℝ) < z.re := by
    dsimp [z]
    have := (abs_lt.mp hstrip).1
    norm_num at this ⊢
    linarith
  have hz0 : z ≠ 0 := by
    intro hz
    rw [hz] at hzneg
    simp at hzneg
  have him : z.im = w.im := by simp [z]
  have hzheight : 1 < |z.im| := by simpa [him] using hheight
  have hznorm : 1 < ‖z‖ := hzheight.trans_le (Complex.abs_im_le_norm z)
  have hznorm0 : 0 < ‖z‖ := zero_lt_one.trans hznorm
  have hbase := norm_rectangularWindowAmplitude_le L hw0 hstrip.le
  have hwindow := norm_xiPhysicalLogWindowModeMultiplier_le_two_of_re_neg hc hzneg
  have hrestore : ‖(z + 1) / z‖ ≤ 2 := by
    rw [norm_div]
    calc
      ‖z + 1‖ / ‖z‖ ≤ (‖z‖ + 1) / ‖z‖ := by
        gcongr
        simpa using norm_add_le z (1 : ℂ)
      _ ≤ 2 := by
        rw [div_le_iff₀ hznorm0]
        linarith
  have haperture : ‖rectangularWindowAmplitude A z‖ ≤ 1 + Real.exp A := by
    rw [rectangularWindowAmplitude_eq_div hz0, norm_div]
    have hnum : ‖1 - Complex.exp (-(A : ℂ) * z)‖ ≤ 1 + Real.exp A := by
      calc
        ‖1 - Complex.exp (-(A : ℂ) * z)‖ ≤
            ‖(1 : ℂ)‖ + ‖Complex.exp (-(A : ℂ) * z)‖ := norm_sub_le _ _
        _ = 1 + Real.exp ((-(A : ℂ) * z).re) := by
          rw [Complex.norm_exp]
          norm_num
        _ ≤ 1 + Real.exp A := by
          gcongr
          have hre : (-(A : ℂ) * z).re = -A * z.re := by
            simp [Complex.mul_re]
          rw [hre]
          nlinarith
    calc
      ‖1 - Complex.exp (-(A : ℂ) * z)‖ / ‖z‖ ≤
          (1 + Real.exp A) / ‖z‖ := by gcongr
      _ ≤ 1 + Real.exp A := by
        apply div_le_self
        · positivity
        · exact hznorm.le
  have hphysical :
      ‖(w + 1 / 2) * rectangularWindowAmplitude c (1 / 2 - w) *
          rectangularWindowAmplitude A (w - 1 / 2)‖ ≤
        4 * (1 + Real.exp A) := by
    have hwz : w = z + 1 / 2 := by dsimp [z]; ring
    have hfactor :
        (w + 1 / 2) * rectangularWindowAmplitude c (1 / 2 - w) *
            rectangularWindowAmplitude A (w - 1 / 2) =
          xiPhysicalLogWindowModeMultiplier c z * ((z + 1) / z) *
            rectangularWindowAmplitude A z := by
      rw [xiPhysicalLogWindowModeMultiplier_eq_mul_rectangularWindowAmplitude, hwz]
      field_simp [hz0]
      ring
    rw [hfactor, norm_mul, norm_mul]
    calc
      ‖xiPhysicalLogWindowModeMultiplier c z‖ * ‖(z + 1) / z‖ *
          ‖rectangularWindowAmplitude A z‖ ≤ 2 * 2 * (1 + Real.exp A) := by
        gcongr
      _ = 4 * (1 + Real.exp A) := by ring
  calc
    ‖xiPhysicalThetaAbelEntireModeAmplitude L A c w‖ =
        ‖rectangularWindowAmplitude L w‖ *
          ‖(w + 1 / 2) * rectangularWindowAmplitude c (1 / 2 - w) *
            rectangularWindowAmplitude A (w - 1 / 2)‖ := by
              simp only [xiPhysicalThetaAbelEntireModeAmplitude, norm_mul]
              ring
    _ ≤ ((1 + Real.exp (|L| / 2)) / ‖w‖) *
        (4 * (1 + Real.exp A)) := by gcongr
    _ = (4 * (1 + Real.exp A) * (1 + Real.exp (|L| / 2))) / ‖w‖ := by ring

theorem xiPhysicalThetaAbelEntireModeAmplitude_differentiable (L A c : ℝ) :
    Differentiable ℂ (xiPhysicalThetaAbelEntireModeAmplitude L A c) := by
  unfold xiPhysicalThetaAbelEntireModeAmplitude
  have hL := rectangularWindowAmplitude_differentiable L
  have hlin : Differentiable ℂ (fun w : ℂ => w + 1 / 2) :=
    differentiable_id.add (differentiable_const _)
  have hcarg : Differentiable ℂ (fun w : ℂ => 1 / 2 - w) :=
    (differentiable_const _).sub differentiable_id
  have hAarg : Differentiable ℂ (fun w : ℂ => w - 1 / 2) :=
    differentiable_id.sub (differentiable_const _)
  exact (((hL.mul hlin).mul
    ((rectangularWindowAmplitude_differentiable c).comp hcarg)).mul
      ((rectangularWindowAmplitude_differentiable A).comp hAarg))

theorem xiZeroCenteredCoordinate_height (q : XiZeroCopy) :
    1 < |(I * xiSpectralPoint q).im| := by
  rw [I_mul_xiSpectralPoint]
  simpa using xiDivisorSupport_one_lt_abs_im q.1

theorem norm_xiPhysicalThetaAbelEntireModeAmplitude_xiZero_le
    {A c : ℝ} (hA : 0 < A) (hc : 0 < c) (L : ℝ)
    (q : XiZeroCopy) :
    ‖xiPhysicalThetaAbelEntireModeAmplitude L A c (I * xiSpectralPoint q)‖ ≤
      (4 * (1 + Real.exp A) * (1 + Real.exp (|L| / 2))) /
        ‖xiSpectralPoint q‖ := by
  have h := norm_xiPhysicalThetaAbelEntireModeAmplitude_le_of_strip hA hc L
    (abs_re_I_mul_xiSpectralPoint_le_half q)
    (xiZeroCenteredCoordinate_height q)
  rw [norm_mul, norm_I, one_mul] at h
  exact h

theorem norm_xiPhysicalThetaAbelEntireModeAmplitude_neg_xiZero_le
    {A c : ℝ} (hA : 0 < A) (hc : 0 < c) (L : ℝ)
    (q : XiZeroCopy) :
    ‖xiPhysicalThetaAbelEntireModeAmplitude L A c (-(I * xiSpectralPoint q))‖ ≤
      (4 * (1 + Real.exp A) * (1 + Real.exp (|L| / 2))) /
        ‖xiSpectralPoint q‖ := by
  have hstrip : |(-(I * xiSpectralPoint q)).re| < 1 / 2 := by
    simpa using abs_re_I_mul_xiSpectralPoint_le_half q
  have hheight : 1 < |(-(I * xiSpectralPoint q)).im| := by
    simpa using xiZeroCenteredCoordinate_height q
  have h := norm_xiPhysicalThetaAbelEntireModeAmplitude_le_of_strip hA hc L
    hstrip hheight
  rw [norm_neg, norm_mul, norm_I, one_mul] at h
  exact h

/-- Even physical two-edge transform built from the entire scalar mode amplitude. -/
def xiPhysicalThetaAbelEnergyTwoEdgeTransform
    (L A c a : ℝ) (s : ℂ) : ℂ :=
  let w := I * s
  Complex.exp ((a : ℂ) * w) * xiPhysicalThetaAbelEntireModeAmplitude L A c w +
    Complex.exp (-(a : ℂ) * w) * xiPhysicalThetaAbelEntireModeAmplitude L A c (-w)

theorem xiPhysicalThetaAbelEnergyTwoEdgeTransform_neg
    (L A c a : ℝ) (s : ℂ) :
    xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a (-s) =
      xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a s := by
  rw [xiPhysicalThetaAbelEnergyTwoEdgeTransform,
    xiPhysicalThetaAbelEnergyTwoEdgeTransform]
  have hws : I * (-s) = -(I * s) := by ring
  rw [hws]
  simp only [neg_neg]
  ring

theorem xiPhysicalThetaAbelEnergyTwoEdgeTransform_conj
    (L A c a : ℝ) (s : ℂ) :
    (starRingEnd ℂ) (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a s) =
      xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a ((starRingEnd ℂ) s) := by
  have hpos :
      (starRingEnd ℂ) (xiPhysicalThetaAbelEntireModeAmplitude L A c (I * s)) =
        xiPhysicalThetaAbelEntireModeAmplitude L A c
          (-(I * (starRingEnd ℂ) s)) := by
    rw [← xiPhysicalThetaAbelEntireModeAmplitude_conj]
    congr 1
    simp only [map_mul, conj_I]
    ring
  have hneg :
      (starRingEnd ℂ) (xiPhysicalThetaAbelEntireModeAmplitude L A c (-(I * s))) =
        xiPhysicalThetaAbelEntireModeAmplitude L A c
          (I * (starRingEnd ℂ) s) := by
    rw [← xiPhysicalThetaAbelEntireModeAmplitude_conj]
    congr 1
    simp only [map_neg, map_mul, conj_I]
    ring
  rw [xiPhysicalThetaAbelEnergyTwoEdgeTransform,
    xiPhysicalThetaAbelEnergyTwoEdgeTransform]
  simp only [map_add, map_mul, ← Complex.exp_conj,
    Complex.conj_ofReal, conj_I, hpos, hneg, map_neg]
  ring

theorem xiWeilSharp_xiPhysicalThetaAbelEnergyTwoEdgeTransform
    (L A c a : ℝ) (s : ℂ) :
    xiWeilSharp (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a) s =
      xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a s := by
  rw [xiWeilSharp,
    ← xiPhysicalThetaAbelEnergyTwoEdgeTransform_conj]
  simp

theorem norm_xiPhysicalThetaAbelEnergyTwoEdgeTransform_xiZero_le
    {A c : ℝ} (hA : 0 < A) (hc : 0 < c) (L a : ℝ)
    (q : XiZeroCopy) :
    ‖xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a (xiSpectralPoint q)‖ ≤
      (2 * Real.exp (|a| / 2) *
        (4 * (1 + Real.exp A) * (1 + Real.exp (|L| / 2)))) /
          ‖xiSpectralPoint q‖ := by
  let w := I * xiSpectralPoint q
  let C0 := 4 * (1 + Real.exp A) * (1 + Real.exp (|L| / 2))
  have hamp := norm_xiPhysicalThetaAbelEntireModeAmplitude_xiZero_le hA hc L q
  have hampneg := norm_xiPhysicalThetaAbelEntireModeAmplitude_neg_xiZero_le hA hc L q
  have hstrip := le_of_lt (abs_re_I_mul_xiSpectralPoint_le_half q)
  have hpos : ‖Complex.exp ((a : ℂ) * w)‖ ≤ Real.exp (|a| / 2) := by
    rw [Complex.norm_exp, Real.exp_le_exp]
    change ((a : ℂ) * (I * xiSpectralPoint q)).re ≤ |a| / 2
    calc
      ((a : ℂ) * (I * xiSpectralPoint q)).re =
          a * (I * xiSpectralPoint q).re := by simp [Complex.mul_re]
      _ ≤ |a| * |(I * xiSpectralPoint q).re| := by
        calc
          a * (I * xiSpectralPoint q).re ≤
              |a * (I * xiSpectralPoint q).re| := le_abs_self _
          _ = _ := abs_mul _ _
      _ ≤ |a| * (1 / 2) :=
        mul_le_mul_of_nonneg_left hstrip (abs_nonneg a)
      _ = |a| / 2 := by ring
  have hneg : ‖Complex.exp (-(a : ℂ) * w)‖ ≤ Real.exp (|a| / 2) := by
    rw [Complex.norm_exp, Real.exp_le_exp]
    change (-(a : ℂ) * (I * xiSpectralPoint q)).re ≤ |a| / 2
    calc
      (-(a : ℂ) * (I * xiSpectralPoint q)).re =
          (-a) * (I * xiSpectralPoint q).re := by simp [Complex.mul_re]
      _ ≤ |-a| * |(I * xiSpectralPoint q).re| := by
        calc
          (-a) * (I * xiSpectralPoint q).re ≤
              |(-a) * (I * xiSpectralPoint q).re| := le_abs_self _
          _ = _ := abs_mul _ _
      _ ≤ |-a| * (1 / 2) :=
        mul_le_mul_of_nonneg_left hstrip (abs_nonneg (-a))
      _ = |a| / 2 := by rw [abs_neg]; ring
  rw [xiPhysicalThetaAbelEnergyTwoEdgeTransform]
  calc
    ‖Complex.exp ((a : ℂ) * w) * xiPhysicalThetaAbelEntireModeAmplitude L A c w +
        Complex.exp (-(a : ℂ) * w) *
          xiPhysicalThetaAbelEntireModeAmplitude L A c (-w)‖ ≤
      ‖Complex.exp ((a : ℂ) * w) * xiPhysicalThetaAbelEntireModeAmplitude L A c w‖ +
        ‖Complex.exp (-(a : ℂ) * w) *
          xiPhysicalThetaAbelEntireModeAmplitude L A c (-w)‖ := norm_add_le _ _
    _ ≤ Real.exp (|a| / 2) * (C0 / ‖xiSpectralPoint q‖) +
        Real.exp (|a| / 2) * (C0 / ‖xiSpectralPoint q‖) := by
      rw [norm_mul, norm_mul]
      gcongr
    _ = (2 * Real.exp (|a| / 2) * C0) / ‖xiSpectralPoint q‖ := by ring

theorem xiPhysicalThetaAbelEnergyTwoEdgeTransform_squareSummable
    {A c : ℝ} (hA : 0 < A) (hc : 0 < c) (L a : ℝ) :
    XiWeilSquareSummable (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a) := by
  let C : ℝ := 2 * Real.exp (|a| / 2) *
    (4 * (1 + Real.exp A) * (1 + Real.exp (|L| / 2)))
  have hmajor : Summable (fun q : XiZeroCopy =>
      C ^ 2 * (1 / ‖xiSpectralPoint q‖ ^ 2)) :=
    xiSpectralPoint_inv_sq_summable.mul_left (C ^ 2)
  refine Summable.of_nonneg_of_le (fun q => sq_nonneg _) (fun q => ?_) hmajor
  have h := norm_xiPhysicalThetaAbelEnergyTwoEdgeTransform_xiZero_le hA hc L a q
  calc
    ‖xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a (xiSpectralPoint q)‖ ^ 2 ≤
        (C / ‖xiSpectralPoint q‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = C ^ 2 * (1 / ‖xiSpectralPoint q‖ ^ 2) := by field_simp

theorem xiPhysicalThetaAbelEnergyTwoEdgeTransform_sq_analyticOnNhd
    (L A c a : ℝ) :
    AnalyticOnNhd ℂ
      (fun s => xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a s ^ 2)
      Set.univ := by
  have hw : Differentiable ℂ (fun s : ℂ => I * s) :=
    (differentiable_const _).mul differentiable_id
  have hwneg : Differentiable ℂ (fun s : ℂ => -(I * s)) := hw.neg
  have hamp := xiPhysicalThetaAbelEntireModeAmplitude_differentiable L A c
  have hpos : Differentiable ℂ (fun s : ℂ => Complex.exp ((a : ℂ) * (I * s))) := by
    fun_prop
  have hneg : Differentiable ℂ (fun s : ℂ => Complex.exp (-(a : ℂ) * (I * s))) := by
    fun_prop
  have htransform : Differentiable ℂ
      (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a) := by
    change Differentiable ℂ (fun s : ℂ =>
      Complex.exp ((a : ℂ) * (I * s)) *
          xiPhysicalThetaAbelEntireModeAmplitude L A c (I * s) +
        Complex.exp (-(a : ℂ) * (I * s)) *
          xiPhysicalThetaAbelEntireModeAmplitude L A c (-(I * s)))
    exact (hpos.mul (hamp.comp hw)).add (hneg.mul (hamp.comp hwneg))
  exact (htransform.pow 2).differentiableOn.analyticOnNhd isOpen_univ

/-- Sign-selected growing edge for the exact physical-energy amplitude. -/
def xiPhysicalThetaAbelEnergyTwoEdgeDominantCore
    (L A c a : ℝ) (w : ℂ) : ℂ :=
  if 0 < w.re then
    xiPhysicalThetaAbelEntireModeAmplitude L A c w ^ 2 *
      Complex.exp (2 * (a : ℂ) * w)
  else if w.re < 0 then
    xiPhysicalThetaAbelEntireModeAmplitude L A c (-w) ^ 2 *
      Complex.exp (-2 * (a : ℂ) * w)
  else 0

/-- Uniform reciprocal-square remainder constant for the physical-energy
two-edge detector. -/
def xiPhysicalThetaAbelEnergyTwoEdgeRemainderBound
    (L A : ℝ) : ℝ :=
  4 * (4 * (1 + Real.exp A) * (1 + Real.exp (|L| / 2))) ^ 2

theorem xiPhysicalThetaAbelEnergyTwoEdgeTransform_sq_decomposition
    (L A c a : ℝ) (s : ℂ) :
    xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a s ^ 2 =
      xiPhysicalThetaAbelEntireModeAmplitude L A c (I * s) ^ 2 *
          Complex.exp (2 * (a : ℂ) * (I * s)) +
        2 * xiPhysicalThetaAbelEntireModeAmplitude L A c (I * s) *
          xiPhysicalThetaAbelEntireModeAmplitude L A c (-(I * s)) +
        xiPhysicalThetaAbelEntireModeAmplitude L A c (-(I * s)) ^ 2 *
          Complex.exp (-2 * (a : ℂ) * (I * s)) := by
  let w : ℂ := I * s
  have hp : Complex.exp ((a : ℂ) * w) ^ 2 =
      Complex.exp (2 * (a : ℂ) * w) := by
    rw [pow_two, ← Complex.exp_add]
    congr 1
    ring
  have hn : Complex.exp (-(a : ℂ) * w) ^ 2 =
      Complex.exp (-2 * (a : ℂ) * w) := by
    rw [pow_two, ← Complex.exp_add]
    congr 1
    ring
  have hinv : Complex.exp ((a : ℂ) * w) *
      Complex.exp (-(a : ℂ) * w) = 1 := by
    rw [← Complex.exp_add]
    simp
  rw [xiPhysicalThetaAbelEnergyTwoEdgeTransform, add_sq, mul_pow, mul_pow]
  change
    Complex.exp ((a : ℂ) * w) ^ 2 *
          xiPhysicalThetaAbelEntireModeAmplitude L A c w ^ 2 +
        2 * (Complex.exp ((a : ℂ) * w) *
          xiPhysicalThetaAbelEntireModeAmplitude L A c w) *
          (Complex.exp (-(a : ℂ) * w) *
            xiPhysicalThetaAbelEntireModeAmplitude L A c (-w)) +
        Complex.exp (-(a : ℂ) * w) ^ 2 *
          xiPhysicalThetaAbelEntireModeAmplitude L A c (-w) ^ 2 =
      xiPhysicalThetaAbelEntireModeAmplitude L A c w ^ 2 *
          Complex.exp (2 * (a : ℂ) * w) +
        2 * xiPhysicalThetaAbelEntireModeAmplitude L A c w *
          xiPhysicalThetaAbelEntireModeAmplitude L A c (-w) +
        xiPhysicalThetaAbelEntireModeAmplitude L A c (-w) ^ 2 *
          Complex.exp (-2 * (a : ℂ) * w)
  rw [hp, hn]
  rw [show 2 * (Complex.exp ((a : ℂ) * w) *
      xiPhysicalThetaAbelEntireModeAmplitude L A c w) *
      (Complex.exp (-(a : ℂ) * w) *
        xiPhysicalThetaAbelEntireModeAmplitude L A c (-w)) =
      2 * (Complex.exp ((a : ℂ) * w) *
        Complex.exp (-(a : ℂ) * w)) *
        xiPhysicalThetaAbelEntireModeAmplitude L A c w *
        xiPhysicalThetaAbelEntireModeAmplitude L A c (-w) by ring, hinv]
  ring

theorem xiPhysicalThetaAbelEnergyTwoEdgeDominantCore_even
    (L A c a : ℝ) (w : ℂ) :
    xiPhysicalThetaAbelEnergyTwoEdgeDominantCore L A c a (-w) =
      xiPhysicalThetaAbelEnergyTwoEdgeDominantCore L A c a w := by
  rcases lt_trichotomy w.re 0 with hneg | hzero | hpos
  · have hnpos : 0 < (-w).re := by simpa using neg_pos.mpr hneg
    rw [xiPhysicalThetaAbelEnergyTwoEdgeDominantCore, if_pos hnpos,
      xiPhysicalThetaAbelEnergyTwoEdgeDominantCore,
      if_neg (not_lt.mpr hneg.le), if_pos hneg]
    rw [show 2 * (a : ℂ) * (-w) = -2 * (a : ℂ) * w by ring]
  · rw [xiPhysicalThetaAbelEnergyTwoEdgeDominantCore,
      if_neg (by simp [hzero]), if_neg (by simp [hzero]),
      xiPhysicalThetaAbelEnergyTwoEdgeDominantCore,
      if_neg (by simp [hzero]), if_neg (by simp [hzero])]
  · have hnneg : (-w).re < 0 := by simpa using neg_lt_zero.mpr hpos
    rw [xiPhysicalThetaAbelEnergyTwoEdgeDominantCore,
      if_neg (not_lt.mpr hnneg.le), if_pos hnneg,
      xiPhysicalThetaAbelEnergyTwoEdgeDominantCore, if_pos hpos]
    rw [show -2 * (a : ℂ) * (-w) = 2 * (a : ℂ) * w by ring]
    simp only [neg_neg]

theorem xiPhysicalThetaAbelEnergyTwoEdgeDominantCore_logSample_of_pos
    (L A c : ℝ) {n : ℕ} (hn : 1 ≤ n) {w : ℂ} (hwre : 0 < w.re) :
    xiPhysicalThetaAbelEnergyTwoEdgeDominantCore L A c (Real.log n / 2) w =
      xiPhysicalThetaAbelEntireModeAmplitude L A c w ^ 2 * (n : ℂ) ^ w := by
  rw [xiPhysicalThetaAbelEnergyTwoEdgeDominantCore, if_pos hwre]
  congr 1
  rw [Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr (by omega : n ≠ 0))]
  have hlog : Complex.log (n : ℂ) = (Real.log n : ℂ) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg n)]
  rw [hlog]
  congr 1
  push_cast
  ring

/-- Physical-energy dominant edge in the centered Xi spectral coordinate. -/
def xiPhysicalThetaAbelEnergyTwoEdgeDominant
    (L A c a : ℝ) (z : ℂ) : ℂ :=
  xiPhysicalThetaAbelEnergyTwoEdgeDominantCore L A c a (I * z)

/-- Multiplicity-exact physical-energy two-edge remainder term. -/
def xiPhysicalThetaAbelEnergyTwoEdgeRemainderTerm
    (L A c a : ℝ) (q : XiZeroCopy) : ℂ :=
  xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a (xiSpectralPoint q) ^ 2 -
    xiPhysicalThetaAbelEnergyTwoEdgeDominant L A c a (xiSpectralPoint q)

theorem xiPhysicalThetaAbelEnergyTwoEdgeTransform_sq_sub_dominant_of_pos
    (L A c a : ℝ) {s : ℂ} (hpos : 0 < (I * s).re) :
    xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a s ^ 2 -
        xiPhysicalThetaAbelEnergyTwoEdgeDominant L A c a s =
      2 * xiPhysicalThetaAbelEntireModeAmplitude L A c (I * s) *
          xiPhysicalThetaAbelEntireModeAmplitude L A c (-(I * s)) +
        xiPhysicalThetaAbelEntireModeAmplitude L A c (-(I * s)) ^ 2 *
          Complex.exp (-2 * (a : ℂ) * (I * s)) := by
  rw [xiPhysicalThetaAbelEnergyTwoEdgeTransform_sq_decomposition,
    xiPhysicalThetaAbelEnergyTwoEdgeDominant,
    xiPhysicalThetaAbelEnergyTwoEdgeDominantCore, if_pos hpos]
  ring

theorem xiPhysicalThetaAbelEnergyTwoEdgeTransform_sq_sub_dominant_of_neg
    (L A c a : ℝ) {s : ℂ} (hneg : (I * s).re < 0) :
    xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a s ^ 2 -
        xiPhysicalThetaAbelEnergyTwoEdgeDominant L A c a s =
      2 * xiPhysicalThetaAbelEntireModeAmplitude L A c (-(I * s)) *
          xiPhysicalThetaAbelEntireModeAmplitude L A c (I * s) +
        xiPhysicalThetaAbelEntireModeAmplitude L A c (I * s) ^ 2 *
          Complex.exp (2 * (a : ℂ) * (I * s)) := by
  rw [xiPhysicalThetaAbelEnergyTwoEdgeTransform_sq_decomposition,
    xiPhysicalThetaAbelEnergyTwoEdgeDominant,
    xiPhysicalThetaAbelEnergyTwoEdgeDominantCore,
    if_neg (not_lt.mpr hneg.le), if_pos hneg]
  ring

@[simp] theorem xiPhysicalThetaAbelEnergyTwoEdgeDominant_of_re_eq_zero
    (L A c a : ℝ) {s : ℂ} (hzero : (I * s).re = 0) :
    xiPhysicalThetaAbelEnergyTwoEdgeDominant L A c a s = 0 := by
  rw [xiPhysicalThetaAbelEnergyTwoEdgeDominant,
    xiPhysicalThetaAbelEnergyTwoEdgeDominantCore,
    if_neg (by linarith), if_neg (by linarith)]

theorem norm_xiPhysicalThetaAbelEnergyTwoEdgeRemainderTerm_le
    {A c : ℝ} (hA : 0 < A) (hc : 0 < c) (L : ℝ)
    {a : ℝ} (ha : 0 ≤ a) (q : XiZeroCopy) :
    ‖xiPhysicalThetaAbelEnergyTwoEdgeRemainderTerm L A c a q‖ ≤
      xiPhysicalThetaAbelEnergyTwoEdgeRemainderBound L A /
        ‖xiSpectralPoint q‖ ^ 2 := by
  let w : ℂ := I * xiSpectralPoint q
  let C0 : ℝ := 4 * (1 + Real.exp A) * (1 + Real.exp (|L| / 2))
  let B : ℝ := C0 / ‖xiSpectralPoint q‖
  have hC0 : 0 ≤ C0 := by
    dsimp only [C0]
    positivity
  have hB : 0 ≤ B := div_nonneg hC0 (norm_nonneg _)
  have hP : ‖xiPhysicalThetaAbelEntireModeAmplitude L A c w‖ ≤ B :=
    norm_xiPhysicalThetaAbelEntireModeAmplitude_xiZero_le hA hc L q
  have hPn : ‖xiPhysicalThetaAbelEntireModeAmplitude L A c (-w)‖ ≤ B :=
    norm_xiPhysicalThetaAbelEntireModeAmplitude_neg_xiZero_le hA hc L q
  rcases lt_trichotomy w.re 0 with hneg | hzero | hpos
  · have hdecRe : (2 * (a : ℂ) * w).re ≤ 0 := by
      norm_num [Complex.mul_re]
      nlinarith
    have hdec : ‖Complex.exp (2 * (a : ℂ) * w)‖ ≤ 1 := by
      rw [Complex.norm_exp, ← Real.exp_zero]
      exact Real.exp_le_exp.mpr hdecRe
    have hfirst : 2 * ‖xiPhysicalThetaAbelEntireModeAmplitude L A c (-w)‖ *
        ‖xiPhysicalThetaAbelEntireModeAmplitude L A c w‖ ≤ 2 * B * B := by
      gcongr
    have hP2 : ‖xiPhysicalThetaAbelEntireModeAmplitude L A c w‖ ^ 2 ≤ B ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hP 2
    have hsecond : ‖xiPhysicalThetaAbelEntireModeAmplitude L A c w‖ ^ 2 *
        ‖Complex.exp (2 * (a : ℂ) * w)‖ ≤ B ^ 2 := by
      calc
        _ ≤ B ^ 2 * 1 :=
          mul_le_mul hP2 hdec (norm_nonneg _) (sq_nonneg B)
        _ = B ^ 2 := mul_one _
    rw [xiPhysicalThetaAbelEnergyTwoEdgeRemainderTerm,
      xiPhysicalThetaAbelEnergyTwoEdgeTransform_sq_sub_dominant_of_neg
        L A c a hneg]
    calc
      ‖2 * xiPhysicalThetaAbelEntireModeAmplitude L A c (-w) *
            xiPhysicalThetaAbelEntireModeAmplitude L A c w +
          xiPhysicalThetaAbelEntireModeAmplitude L A c w ^ 2 *
            Complex.exp (2 * (a : ℂ) * w)‖ ≤
        ‖2 * xiPhysicalThetaAbelEntireModeAmplitude L A c (-w) *
            xiPhysicalThetaAbelEntireModeAmplitude L A c w‖ +
          ‖xiPhysicalThetaAbelEntireModeAmplitude L A c w ^ 2 *
            Complex.exp (2 * (a : ℂ) * w)‖ := norm_add_le _ _
      _ ≤ 2 * B * B + B ^ 2 := by
        simp only [norm_mul, norm_ofNat, norm_pow]
        exact add_le_add hfirst hsecond
      _ ≤ 4 * B ^ 2 := by nlinarith [sq_nonneg B]
      _ = xiPhysicalThetaAbelEnergyTwoEdgeRemainderBound L A /
          ‖xiSpectralPoint q‖ ^ 2 := by
        dsimp only [B, C0, xiPhysicalThetaAbelEnergyTwoEdgeRemainderBound]
        field_simp
  · have hp : ‖Complex.exp ((a : ℂ) * w)‖ = 1 := by
      rw [Complex.norm_exp, show ((a : ℂ) * w).re = 0 by
        simp [Complex.mul_re, hzero], Real.exp_zero]
    have hn : ‖Complex.exp (-(a : ℂ) * w)‖ = 1 := by
      rw [Complex.norm_exp, show (-(a : ℂ) * w).re = 0 by
        simp [Complex.mul_re, hzero], Real.exp_zero]
    have hF : ‖xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a
        (xiSpectralPoint q)‖ ≤ 2 * B := by
      rw [xiPhysicalThetaAbelEnergyTwoEdgeTransform]
      change ‖Complex.exp ((a : ℂ) * w) *
          xiPhysicalThetaAbelEntireModeAmplitude L A c w +
        Complex.exp (-(a : ℂ) * w) *
          xiPhysicalThetaAbelEntireModeAmplitude L A c (-w)‖ ≤ _
      calc
        _ ≤ ‖Complex.exp ((a : ℂ) * w) *
              xiPhysicalThetaAbelEntireModeAmplitude L A c w‖ +
            ‖Complex.exp (-(a : ℂ) * w) *
              xiPhysicalThetaAbelEntireModeAmplitude L A c (-w)‖ := norm_add_le _ _
        _ ≤ B + B := by
          rw [norm_mul, norm_mul, hp, hn, one_mul, one_mul]
          gcongr
        _ = 2 * B := by ring
    rw [xiPhysicalThetaAbelEnergyTwoEdgeRemainderTerm,
      xiPhysicalThetaAbelEnergyTwoEdgeDominant_of_re_eq_zero L A c a hzero,
      sub_zero, norm_pow]
    calc
      ‖xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a
          (xiSpectralPoint q)‖ ^ 2 ≤ (2 * B) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hF 2
      _ = xiPhysicalThetaAbelEnergyTwoEdgeRemainderBound L A /
          ‖xiSpectralPoint q‖ ^ 2 := by
        dsimp only [B, C0, xiPhysicalThetaAbelEnergyTwoEdgeRemainderBound]
        field_simp
        ring
  · have hdecRe : (-2 * (a : ℂ) * w).re ≤ 0 := by
      norm_num [Complex.mul_re]
      nlinarith
    have hdec : ‖Complex.exp (-2 * (a : ℂ) * w)‖ ≤ 1 := by
      rw [Complex.norm_exp, ← Real.exp_zero]
      exact Real.exp_le_exp.mpr hdecRe
    have hfirst : 2 * ‖xiPhysicalThetaAbelEntireModeAmplitude L A c w‖ *
        ‖xiPhysicalThetaAbelEntireModeAmplitude L A c (-w)‖ ≤ 2 * B * B := by
      gcongr
    have hPn2 : ‖xiPhysicalThetaAbelEntireModeAmplitude L A c (-w)‖ ^ 2 ≤ B ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hPn 2
    have hsecond : ‖xiPhysicalThetaAbelEntireModeAmplitude L A c (-w)‖ ^ 2 *
        ‖Complex.exp (-2 * (a : ℂ) * w)‖ ≤ B ^ 2 := by
      calc
        _ ≤ B ^ 2 * 1 :=
          mul_le_mul hPn2 hdec (norm_nonneg _) (sq_nonneg B)
        _ = B ^ 2 := mul_one _
    rw [xiPhysicalThetaAbelEnergyTwoEdgeRemainderTerm,
      xiPhysicalThetaAbelEnergyTwoEdgeTransform_sq_sub_dominant_of_pos
        L A c a hpos]
    calc
      ‖2 * xiPhysicalThetaAbelEntireModeAmplitude L A c w *
            xiPhysicalThetaAbelEntireModeAmplitude L A c (-w) +
          xiPhysicalThetaAbelEntireModeAmplitude L A c (-w) ^ 2 *
            Complex.exp (-2 * (a : ℂ) * w)‖ ≤
        ‖2 * xiPhysicalThetaAbelEntireModeAmplitude L A c w *
            xiPhysicalThetaAbelEntireModeAmplitude L A c (-w)‖ +
          ‖xiPhysicalThetaAbelEntireModeAmplitude L A c (-w) ^ 2 *
            Complex.exp (-2 * (a : ℂ) * w)‖ := norm_add_le _ _
      _ ≤ 2 * B * B + B ^ 2 := by
        simp only [norm_mul, norm_ofNat, norm_pow]
        exact add_le_add hfirst hsecond
      _ ≤ 4 * B ^ 2 := by nlinarith [sq_nonneg B]
      _ = xiPhysicalThetaAbelEnergyTwoEdgeRemainderBound L A /
          ‖xiSpectralPoint q‖ ^ 2 := by
        dsimp only [B, C0, xiPhysicalThetaAbelEnergyTwoEdgeRemainderBound]
        field_simp

theorem xiPhysicalThetaAbelEnergyTwoEdgeRemainderTerm_summable
    {A c : ℝ} (hA : 0 < A) (hc : 0 < c) (L : ℝ)
    {a : ℝ} (ha : 0 ≤ a) :
    Summable (xiPhysicalThetaAbelEnergyTwoEdgeRemainderTerm L A c a) := by
  apply Summable.of_norm_bounded
    (xiSpectralPoint_inv_sq_summable.mul_left
      (xiPhysicalThetaAbelEnergyTwoEdgeRemainderBound L A))
  intro q
  calc
    ‖xiPhysicalThetaAbelEnergyTwoEdgeRemainderTerm L A c a q‖ ≤
        xiPhysicalThetaAbelEnergyTwoEdgeRemainderBound L A /
          ‖xiSpectralPoint q‖ ^ 2 :=
      norm_xiPhysicalThetaAbelEnergyTwoEdgeRemainderTerm_le hA hc L ha q
    _ = xiPhysicalThetaAbelEnergyTwoEdgeRemainderBound L A *
        (1 / ‖xiSpectralPoint q‖ ^ 2) := by ring

theorem xiWeilPolarization_physicalThetaAbelEnergy_eq_tsum_sq
    (L A c a : ℝ) :
    xiWeilPolarization (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a)
        (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a) =
      ∑' q : XiZeroCopy,
        xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a
          (xiSpectralPoint q) ^ 2 := by
  unfold xiWeilPolarization
  apply tsum_congr
  intro q
  rw [xiWeilSharp_xiPhysicalThetaAbelEnergyTwoEdgeTransform]
  ring

theorem xiPhysicalThetaAbelEnergyTwoEdgeTransform_sq_summable
    {A c : ℝ} (hA : 0 < A) (hc : 0 < c) (L a : ℝ) :
    Summable (fun q : XiZeroCopy =>
      xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a
        (xiSpectralPoint q) ^ 2) := by
  apply Summable.of_norm
  simpa only [XiWeilSquareSummable, norm_pow] using
    xiPhysicalThetaAbelEnergyTwoEdgeTransform_squareSummable hA hc L a

theorem xiPhysicalThetaAbelEnergyTwoEdgeDominant_summable
    {A c : ℝ} (hA : 0 < A) (hc : 0 < c) (L : ℝ)
    {a : ℝ} (ha : 0 ≤ a) :
    Summable (fun q : XiZeroCopy =>
      xiPhysicalThetaAbelEnergyTwoEdgeDominant L A c a
        (xiSpectralPoint q)) := by
  have hsq := xiPhysicalThetaAbelEnergyTwoEdgeTransform_sq_summable
    hA hc L a
  have hrem := xiPhysicalThetaAbelEnergyTwoEdgeRemainderTerm_summable
    hA hc L ha
  refine (hsq.sub hrem).congr (fun q => ?_)
  rw [xiPhysicalThetaAbelEnergyTwoEdgeRemainderTerm]
  ring

theorem norm_xiWeilPolarization_physicalThetaAbelEnergy_sub_dominant_le
    {A c : ℝ} (hA : 0 < A) (hc : 0 < c) (L : ℝ)
    {a : ℝ} (ha : 0 ≤ a) :
    ‖xiWeilPolarization (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a)
          (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a) -
        ∑' q : XiZeroCopy,
          xiPhysicalThetaAbelEnergyTwoEdgeDominant L A c a
            (xiSpectralPoint q)‖ ≤
      xiPhysicalThetaAbelEnergyTwoEdgeRemainderBound L A *
        ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2 := by
  rw [xiWeilPolarization_physicalThetaAbelEnergy_eq_tsum_sq]
  have hsq := xiPhysicalThetaAbelEnergyTwoEdgeTransform_sq_summable
    hA hc L a
  have hdom := xiPhysicalThetaAbelEnergyTwoEdgeDominant_summable
    hA hc L ha
  rw [← hsq.tsum_sub hdom]
  have hrem := xiPhysicalThetaAbelEnergyTwoEdgeRemainderTerm_summable
    hA hc L ha
  have hmajor := xiSpectralPoint_inv_sq_summable.mul_left
    (xiPhysicalThetaAbelEnergyTwoEdgeRemainderBound L A)
  calc
    ‖∑' q : XiZeroCopy,
        (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a
              (xiSpectralPoint q) ^ 2 -
          xiPhysicalThetaAbelEnergyTwoEdgeDominant L A c a
            (xiSpectralPoint q))‖ =
      ‖∑' q : XiZeroCopy,
        xiPhysicalThetaAbelEnergyTwoEdgeRemainderTerm L A c a q‖ := by rfl
    _ ≤ ∑' q : XiZeroCopy,
        ‖xiPhysicalThetaAbelEnergyTwoEdgeRemainderTerm L A c a q‖ :=
      norm_tsum_le_tsum_norm hrem.norm
    _ ≤ ∑' q : XiZeroCopy,
        xiPhysicalThetaAbelEnergyTwoEdgeRemainderBound L A *
          (1 / ‖xiSpectralPoint q‖ ^ 2) := by
      exact hrem.norm.tsum_le_tsum (fun q => by
        calc
          ‖xiPhysicalThetaAbelEnergyTwoEdgeRemainderTerm L A c a q‖ ≤
              xiPhysicalThetaAbelEnergyTwoEdgeRemainderBound L A /
                ‖xiSpectralPoint q‖ ^ 2 :=
            norm_xiPhysicalThetaAbelEnergyTwoEdgeRemainderTerm_le hA hc L ha q
          _ = xiPhysicalThetaAbelEnergyTwoEdgeRemainderBound L A *
              (1 / ‖xiSpectralPoint q‖ ^ 2) := by ring) hmajor
    _ = xiPhysicalThetaAbelEnergyTwoEdgeRemainderBound L A *
        ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2 := by
      rw [tsum_mul_left]

theorem xiPhysicalThetaAbelEnergyTwoEdgeDominant_reflect
    (L A c a : ℝ) (q : XiZeroCopy) :
    xiPhysicalThetaAbelEnergyTwoEdgeDominant L A c a
        (xiSpectralPoint (xiZeroCopyReflectEquiv q)) =
      xiPhysicalThetaAbelEnergyTwoEdgeDominant L A c a
        (xiSpectralPoint q) := by
  rw [xiPhysicalThetaAbelEnergyTwoEdgeDominant,
    xiPhysicalThetaAbelEnergyTwoEdgeDominant, xiSpectralPoint_reflect,
    mul_neg]
  exact xiPhysicalThetaAbelEnergyTwoEdgeDominantCore_even
    L A c a (I * xiSpectralPoint q)

theorem tsum_xiPhysicalThetaAbelEnergyTwoEdgeDominant_left_eq_right
    (L A c a : ℝ) :
    (∑' q : XiLeftZeroCopy,
      xiPhysicalThetaAbelEnergyTwoEdgeDominant L A c a
        (xiSpectralPoint q.1)) =
    ∑' q : XiRightZeroCopy,
      xiPhysicalThetaAbelEnergyTwoEdgeDominant L A c a
        (xiSpectralPoint q.1) := by
  calc
    _ = ∑' q : XiRightZeroCopy,
        xiPhysicalThetaAbelEnergyTwoEdgeDominant L A c a
          (xiSpectralPoint (xiRightLeftReflectEquiv q).1) :=
      (xiRightLeftReflectEquiv.tsum_eq
        (fun q : XiLeftZeroCopy =>
          xiPhysicalThetaAbelEnergyTwoEdgeDominant L A c a
            (xiSpectralPoint q.1))).symm
    _ = _ := by
      apply tsum_congr
      intro q
      exact xiPhysicalThetaAbelEnergyTwoEdgeDominant_reflect L A c a q.1

theorem tsum_xiPhysicalThetaAbelEnergyTwoEdgeDominant_eq_two_mul_right
    {A c : ℝ} (hA : 0 < A) (hc : 0 < c) (L : ℝ)
    {a : ℝ} (ha : 0 ≤ a) :
    (∑' q : XiZeroCopy,
      xiPhysicalThetaAbelEnergyTwoEdgeDominant L A c a
        (xiSpectralPoint q)) =
    2 * ∑' q : XiRightZeroCopy,
      xiPhysicalThetaAbelEnergyTwoEdgeDominant L A c a
        (xiSpectralPoint q.1) := by
  let g : XiZeroCopy → ℂ := fun q =>
    xiPhysicalThetaAbelEnergyTwoEdgeDominant L A c a (xiSpectralPoint q)
  let P : Set XiZeroCopy := {q | 0 < (I * xiSpectralPoint q).re}
  let M : Set XiZeroCopy := {q | (I * xiSpectralPoint q).re < 0}
  have hsum : Summable g :=
    xiPhysicalThetaAbelEnergyTwoEdgeDominant_summable hA hc L ha
  have hpoint : g = P.indicator g + M.indicator g := by
    funext q
    rcases lt_trichotomy (I * xiSpectralPoint q).re 0 with hneg | hzero | hpos
    · rw [Pi.add_apply, Set.indicator_of_notMem, Set.indicator_of_mem]
      · simp only [zero_add]
      · exact hneg
      · exact not_lt.mpr hneg.le
    · rw [Pi.add_apply, Set.indicator_of_notMem, Set.indicator_of_notMem,
        add_zero]
      · dsimp only [g, xiPhysicalThetaAbelEnergyTwoEdgeDominant]
        rw [xiPhysicalThetaAbelEnergyTwoEdgeDominantCore,
          if_neg (by linarith), if_neg (by linarith)]
      · change ¬(I * xiSpectralPoint q).re < 0
        linarith
      · change ¬0 < (I * xiSpectralPoint q).re
        linarith
    · rw [Pi.add_apply, Set.indicator_of_mem, Set.indicator_of_notMem,
        add_zero]
      · exact not_lt.mpr hpos.le
      · exact hpos
  calc
    (∑' q : XiZeroCopy,
        xiPhysicalThetaAbelEnergyTwoEdgeDominant L A c a
          (xiSpectralPoint q)) = ∑' q : XiZeroCopy, g q := rfl
    _ = ∑' q : XiZeroCopy, (P.indicator g q + M.indicator g q) := by
      apply tsum_congr
      intro q
      exact congrFun hpoint q
    _ = (∑' q : XiZeroCopy, P.indicator g q) +
        ∑' q : XiZeroCopy, M.indicator g q :=
      (hsum.indicator P).tsum_add (hsum.indicator M)
    _ = (∑' q : P, g q.1) + ∑' q : M, g q.1 := by
      rw [tsum_subtype, tsum_subtype]
    _ = (∑' q : XiRightZeroCopy,
          xiPhysicalThetaAbelEnergyTwoEdgeDominant L A c a
            (xiSpectralPoint q.1)) +
        ∑' q : XiLeftZeroCopy,
          xiPhysicalThetaAbelEnergyTwoEdgeDominant L A c a
            (xiSpectralPoint q.1) := rfl
    _ = (∑' q : XiRightZeroCopy,
          xiPhysicalThetaAbelEnergyTwoEdgeDominant L A c a
            (xiSpectralPoint q.1)) +
        ∑' q : XiRightZeroCopy,
          xiPhysicalThetaAbelEnergyTwoEdgeDominant L A c a
            (xiSpectralPoint q.1) := by
      rw [tsum_xiPhysicalThetaAbelEnergyTwoEdgeDominant_left_eq_right]
    _ = 2 * ∑' q : XiRightZeroCopy,
        xiPhysicalThetaAbelEnergyTwoEdgeDominant L A c a
          (xiSpectralPoint q.1) := by ring

theorem xiPhysicalThetaAbelEnergyTwoEdgeDominant_logSample_of_right
    {L A c : ℝ} (hL : 0 < L) (hA : 0 < A) (hc : 0 < c)
    {n : ℕ} (hn : 1 ≤ n) (q : XiRightZeroCopy) :
    xiPhysicalThetaAbelEnergyTwoEdgeDominant L A c (Real.log n / 2)
        (xiSpectralPoint q.1) =
      (xiPhysicalThetaAbelEnergyCoefficientSystem hL hA hc).coefficient q *
        (n : ℂ) ^ xiRightCenteredZero q := by
  simpa only [xiPhysicalThetaAbelEnergyTwoEdgeDominant,
    xiRightCenteredZero, xiPhysicalThetaAbelEnergyCoefficientSystem,
    xiPhysicalThetaAbelEnergyCoefficient] using
    xiPhysicalThetaAbelEnergyTwoEdgeDominantCore_logSample_of_pos
      L A c hn q.2

theorem tsum_xiPhysicalThetaAbelEnergyTwoEdgeDominant_logSample_eq_ofReal_energyLandau
    {L A c : ℝ} (hL : 0 < L) (hA : 0 < A) (hc : 0 < c)
    {n : ℕ} (hn : 1 ≤ n) :
    (∑' q : XiZeroCopy,
      xiPhysicalThetaAbelEnergyTwoEdgeDominant L A c (Real.log n / 2)
        (xiSpectralPoint q)) =
      (xiPhysicalThetaAbelEnergyLandauResponse L A c n : ℂ) := by
  have ha : 0 ≤ Real.log n / 2 := by
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    positivity
  rw [tsum_xiPhysicalThetaAbelEnergyTwoEdgeDominant_eq_two_mul_right
    hA hc L ha]
  rw [xiPhysicalThetaAbelEnergyLandauResponse_eq_weighted hL hA hc,
    ofReal_xiWeightedRightDirichletCoefficientReal,
    xiWeightedRightDirichletComplex]
  congr 1
  apply tsum_congr
  intro q
  exact xiPhysicalThetaAbelEnergyTwoEdgeDominant_logSample_of_right
    hL hA hc hn q

theorem xiWeilPolarization_physicalThetaAbelEnergy_logSample_cofinally_unbounded_below
    {L A c : ℝ} (hL : 0 < L) (hA : 0 < A) (hc : 0 < c)
    (hne : Nonempty XiRightZeroCopy) :
    ∀ B : ℝ, ∀ N0 : ℕ, ∃ n : ℕ,
      N0 ≤ n ∧ L < Real.log n / 2 ∧
      (xiWeilPolarization
        (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c (Real.log n / 2))
        (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c
          (Real.log n / 2))).re < B := by
  intro B N0
  let K : ℝ := xiPhysicalThetaAbelEnergyTwoEdgeRemainderBound L A *
    ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2
  obtain ⟨N : ℕ, hN⟩ := exists_nat_gt
    (max (N0 : ℝ) (Real.exp (2 * L)))
  have hN0 : N0 ≤ N := by
    exact_mod_cast (le_max_left (N0 : ℝ) (Real.exp (2 * L))).trans hN.le
  have hNexp : Real.exp (2 * L) < (N : ℝ) :=
    (le_max_right (N0 : ℝ) (Real.exp (2 * L))).trans_lt hN
  obtain ⟨n, hnN, hcoeff⟩ :=
    xiPhysicalThetaAbelEnergyLandauResponse_cofinally_unbounded_below
      hL hA hc hne (B - K) N
  have hn0 : N0 ≤ n := hN0.trans hnN
  have hnexp : Real.exp (2 * L) < (n : ℝ) := by
    exact hNexp.trans_le (by exact_mod_cast hnN)
  have hnpos : 0 < (n : ℝ) := (Real.exp_pos _).trans hnexp
  have hnNatPos : 0 < n := by exact_mod_cast hnpos
  have hn1 : 1 ≤ n := hnNatPos
  have hlog : 2 * L < Real.log n :=
    (Real.lt_log_iff_exp_lt hnpos).2 hnexp
  have hLa : L < Real.log n / 2 := by linarith
  have ha : 0 ≤ Real.log n / 2 := by
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    positivity
  refine ⟨n, hn0, hLa, ?_⟩
  have hrem :=
    norm_xiWeilPolarization_physicalThetaAbelEnergy_sub_dominant_le
      hA hc L ha
  rw [tsum_xiPhysicalThetaAbelEnergyTwoEdgeDominant_logSample_eq_ofReal_energyLandau
    hL hA hc hn1] at hrem
  have hre := Complex.re_le_norm
    (xiWeilPolarization
        (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c (Real.log n / 2))
        (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c (Real.log n / 2)) -
      (xiPhysicalThetaAbelEnergyLandauResponse L A c n : ℂ))
  change
    (xiWeilPolarization
        (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c (Real.log n / 2))
        (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c
          (Real.log n / 2))).re -
      xiPhysicalThetaAbelEnergyLandauResponse L A c n ≤
      ‖xiWeilPolarization
          (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c (Real.log n / 2))
          (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c
            (Real.log n / 2)) -
        (xiPhysicalThetaAbelEnergyLandauResponse L A c n : ℂ)‖ at hre
  dsimp only [K] at hcoeff ⊢
  linarith

theorem not_riemannHypothesis_implies_physicalThetaAbelEnergy_weil_cofinally_unbounded_below
    {L A c : ℝ} (hL : 0 < L) (hA : 0 < A) (hc : 0 < c)
    (hRH : ¬RiemannHypothesis) :
    ∀ B : ℝ, ∀ N0 : ℕ, ∃ n : ℕ,
      N0 ≤ n ∧ L < Real.log n / 2 ∧
      (xiWeilPolarization
        (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c (Real.log n / 2))
        (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c
          (Real.log n / 2))).re < B := by
  exact xiWeilPolarization_physicalThetaAbelEnergy_logSample_cofinally_unbounded_below
    hL hA hc (nonempty_xiRightZeroCopy_of_not_riemannHypothesis hRH)

/-- A single positive physical window, aperture, and scalarization width is
already a complete RH detector on the logarithmic mesh. -/
theorem riemannHypothesis_iff_physicalThetaAbelEnergy_logSample_weil_nonneg
    {L A c : ℝ} (hL : 0 < L) (hA : 0 < A) (hc : 0 < c) :
    RiemannHypothesis ↔
      ∀ n : ℕ, L < Real.log n / 2 →
        0 ≤ (xiWeilPolarization
          (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c (Real.log n / 2))
          (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c
            (Real.log n / 2))).re := by
  constructor
  · intro hRH n hn
    exact (riemannHypothesis_iff_xiWeilPolarization_nonneg.mp hRH)
      (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c (Real.log n / 2))
      (xiPhysicalThetaAbelEnergyTwoEdgeTransform_squareSummable
        hA hc L (Real.log n / 2))
  · intro hnonneg
    by_contra hRH
    obtain ⟨n, _hn0, hLn, hneg⟩ :=
      not_riemannHypothesis_implies_physicalThetaAbelEnergy_weil_cofinally_unbounded_below
        hL hA hc hRH 0 0
    exact (not_lt_of_ge (hnonneg n hLn)) hneg

/-- Closed, premise-free physical-energy Weil criterion. -/
theorem riemannHypothesis_iff_unitPhysicalThetaAbelEnergy_logSample_weil_nonneg :
    RiemannHypothesis ↔
      ∀ n : ℕ, 1 < Real.log n / 2 →
        0 ≤ (xiWeilPolarization
          (xiPhysicalThetaAbelEnergyTwoEdgeTransform 1 1 1 (Real.log n / 2))
          (xiPhysicalThetaAbelEnergyTwoEdgeTransform 1 1 1
            (Real.log n / 2))).re := by
  exact riemannHypothesis_iff_physicalThetaAbelEnergy_logSample_weil_nonneg
    (by norm_num) (by norm_num) (by norm_num)

/-- Exact finite continued prime--archimedean source contour for the squared
physical-energy detector. -/
theorem exists_admissible_rectIntegral_physicalThetaAbelEnergySource_eq_sum_containing
    (t : Finset XiZeroCopy) (L A c a : ℝ) :
    ∃ z₁ z₂ : ℂ,
      z₁.re < z₂.re ∧ z₁.im < z₂.im ∧
      (∀ q ∈ t, q ∈ xiZeroCopyClosedRectangle z₁ z₂) ∧
      rectIntegral (fun z =>
          xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a z ^ 2 *
            continuedPrimeArchSourceRelativeTrace z) z₁ z₂ =
        2 * Real.pi * I * ∑ q ∈ xiZeroCopyClosedRectangle z₁ z₂,
          xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a
            (xiSpectralPoint q) ^ 2 :=
  exists_admissible_rectIntegral_source_eq_xiZeroCopy_sum_containing t
    (xiPhysicalThetaAbelEnergyTwoEdgeTransform_sq_analyticOnNhd L A c a)

/-- Normalized continued prime--archimedean source contour of the exact
physical-energy detector. -/
def xiPhysicalThetaAbelEnergyNormalizedSourceContour
    (L A c a : ℝ) (z₁ z₂ : ℂ) : ℂ :=
  (2 * Real.pi * I)⁻¹ * rectIntegral (fun z =>
    xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a z ^ 2 *
      continuedPrimeArchSourceRelativeTrace z) z₁ z₂

/-- Full physical-energy Weil value is a cofinal limit of exact continued
prime--archimedean source contours. -/
theorem exists_admissible_physicalThetaAbelEnergySourceContour_approximates_weil
    {A c : ℝ} (hA : 0 < A) (hc : 0 < c) (L a : ℝ)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ z₁ z₂ : ℂ,
      z₁.re < z₂.re ∧ z₁.im < z₂.im ∧
      dist (xiPhysicalThetaAbelEnergyNormalizedSourceContour L A c a z₁ z₂)
        (xiWeilPolarization
          (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a)
          (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a)) < epsilon := by
  let f : XiZeroCopy → ℂ := fun q =>
    xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a
      (xiSpectralPoint q) ^ 2
  have hsum : Summable f :=
    xiPhysicalThetaAbelEnergyTwoEdgeTransform_sq_summable hA hc L a
  have hball : Metric.ball (∑' q, f q) epsilon ∈ nhds (∑' q, f q) :=
    Metric.ball_mem_nhds _ hepsilon
  have hevent : ∀ᶠ s : Finset XiZeroCopy in atTop,
      ∑ q ∈ s, f q ∈ Metric.ball (∑' q, f q) epsilon :=
    hsum.hasSum.eventually hball
  rw [eventually_atTop] at hevent
  obtain ⟨t, ht⟩ := hevent
  obtain ⟨z₁, z₂, hre, him, hcontains, hcontour⟩ :=
    exists_admissible_rectIntegral_physicalThetaAbelEnergySource_eq_sum_containing
      t L A c a
  refine ⟨z₁, z₂, hre, him, ?_⟩
  have hpacket : t ≤ xiZeroCopyClosedRectangle z₁ z₂ := by
    intro q hq
    exact hcontains q hq
  have hnear := ht (xiZeroCopyClosedRectangle z₁ z₂) hpacket
  rw [Metric.mem_ball] at hnear
  have hfactor : (2 * Real.pi * I : ℂ) ≠ 0 := by
    apply mul_ne_zero
    · apply mul_ne_zero
      · norm_num
      · exact_mod_cast Real.pi_ne_zero
    · exact I_ne_zero
  rw [xiPhysicalThetaAbelEnergyNormalizedSourceContour, hcontour,
    xiWeilPolarization_physicalThetaAbelEnergy_eq_tsum_sq]
  rw [← mul_assoc, inv_mul_cancel₀ hfactor, one_mul]
  simpa only [f] using hnear

/-- False RH forces continued prime--archimedean physical-energy source
contours below every real level at arbitrarily late logarithmic apertures. -/
theorem not_riemannHypothesis_implies_physicalThetaAbelEnergy_sourceContour_cofinally_unbounded_below
    {L A c : ℝ} (hL : 0 < L) (hA : 0 < A) (hc : 0 < c)
    (hRH : ¬RiemannHypothesis) :
    ∀ B : ℝ, ∀ N0 : ℕ, ∃ n : ℕ, ∃ z₁ z₂ : ℂ,
      N0 ≤ n ∧ L < Real.log n / 2 ∧
      z₁.re < z₂.re ∧ z₁.im < z₂.im ∧
      (xiPhysicalThetaAbelEnergyNormalizedSourceContour
        L A c (Real.log n / 2) z₁ z₂).re < B := by
  intro B N0
  obtain ⟨n, hn0, hLn, hweil⟩ :=
    not_riemannHypothesis_implies_physicalThetaAbelEnergy_weil_cofinally_unbounded_below
      hL hA hc hRH (B - 1) N0
  obtain ⟨z₁, z₂, hre, him, hdist⟩ :=
    exists_admissible_physicalThetaAbelEnergySourceContour_approximates_weil
      hA hc L (Real.log n / 2) (by norm_num : (0 : ℝ) < 1 / 2)
  refine ⟨n, z₁, z₂, hn0, hLn, hre, him, ?_⟩
  have hreal := Complex.re_le_norm
    (xiPhysicalThetaAbelEnergyNormalizedSourceContour
        L A c (Real.log n / 2) z₁ z₂ -
      xiWeilPolarization
        (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c (Real.log n / 2))
        (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c (Real.log n / 2)))
  rw [dist_eq] at hdist
  change
    (xiPhysicalThetaAbelEnergyNormalizedSourceContour
        L A c (Real.log n / 2) z₁ z₂).re -
      (xiWeilPolarization
        (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c (Real.log n / 2))
        (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c
          (Real.log n / 2))).re ≤
      ‖xiPhysicalThetaAbelEnergyNormalizedSourceContour
          L A c (Real.log n / 2) z₁ z₂ -
        xiWeilPolarization
          (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c (Real.log n / 2))
          (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c
            (Real.log n / 2))‖ at hreal
  linarith

end

end RHTower
