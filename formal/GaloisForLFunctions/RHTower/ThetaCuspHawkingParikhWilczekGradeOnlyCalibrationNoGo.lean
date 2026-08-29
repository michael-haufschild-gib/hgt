import GaloisForLFunctions.RHTower.ThetaCuspHawkingParikhWilczekSignedMatrixThreeMomentClassification

/-!
# Parikh--Wilczek grade-only calibration no-go

The calibrated PW-B endpoint divides grade `k` by its full residual
`X(s) + 4k(k+1)`.  This file determines whether that spectral dependence can be replaced by a
fixed physical coupling depending only on grade.

At one off-wall spectral point, exact wall recovery uniquely forces the reciprocal residual.
More sharply, if fixed scalars make two distinct recoil grades agree at two off-wall points with
different spectral coordinates, both scalars vanish.  The explicit probes `1/4 + I` and
`1/4 + 2I` therefore rule out every nondegenerate grade-only diagonal calibration on the open
critical strip.

This kills the PW-B branch

`fixed grade-only recoil coupling -> common oriented wall channel -> endpoint tomography -> RH`.

The exact positive survivor is spectral dependence: a diagonal calibration recovering the wall
must use `(X(s) + 4k(k+1))⁻¹`.  Any source-side replacement must instead introduce spectral
feedback or genuinely non-diagonal/nonlocal grade mixing.

`[NEW] [RIGIDITY] [NO-GO] [PAPER-PROVED] [LEAN-PROVED]`
-/

open Complex

namespace RHTower

noncomputable section

/-- Exact wall recovery at one off-wall strip point uniquely forces reciprocal-residual
calibration.  Thus the normalization used by calibrated endpoint tomography is not a freely
adjustable grade weight. -/
theorem schwarzschildParikhWilczekWallCalibration_unique
    (s : ℂ) (k : ℕ) (a : ℝ)
    (hs0 : 0 < s.re) (hs1 : s.re < 1)
    (hwall : schwarzschildParikhWilczekBorelWallFactor s ≠ 0)
    (hcal : a * (schwarzschildParikhWilczekBorelRecoilHolonomy s k).im =
      schwarzschildParikhWilczekBorelWallFactor s) :
    a = (schwarzschildParikhWilczekBorelGradeResidual s k)⁻¹ := by
  rw [schwarzschildParikhWilczekBorelRecoilHolonomy_im_factorization] at hcal
  have hres := schwarzschildParikhWilczekBorelGradeResidual_pos s k hs0 hs1
  have hmul : a * schwarzschildParikhWilczekBorelGradeResidual s k = 1 := by
    apply (mul_left_cancel₀ hwall)
    calc
      schwarzschildParikhWilczekBorelWallFactor s *
          (a * schwarzschildParikhWilczekBorelGradeResidual s k) =
        a * (schwarzschildParikhWilczekBorelWallFactor s *
          schwarzschildParikhWilczekBorelGradeResidual s k) := by ring
      _ = schwarzschildParikhWilczekBorelWallFactor s := hcal
      _ = schwarzschildParikhWilczekBorelWallFactor s * 1 := by ring
  calc
    a = (a * schwarzschildParikhWilczekBorelGradeResidual s k) *
        (schwarzschildParikhWilczekBorelGradeResidual s k)⁻¹ := by
      field_simp
    _ = (schwarzschildParikhWilczekBorelGradeResidual s k)⁻¹ := by
      rw [hmul, one_mul]

/-- Sharp two-probe rigidity.  Fixed scalar calibration of two distinct affine residuals at two
distinct spectral coordinates is necessarily the zero calibration. -/
theorem schwarzschildParikhWilczekGradeOnlyCalibration_twoPoint_rigidity
    (s t : ℂ) (i j : ℕ) (a b : ℝ)
    (hws : schwarzschildParikhWilczekBorelWallFactor s ≠ 0)
    (hwt : schwarzschildParikhWilczekBorelWallFactor t ≠ 0)
    (hcoord : schwarzschildParikhWilczekBorelSpectralCoordinate s ≠
      schwarzschildParikhWilczekBorelSpectralCoordinate t)
    (hshift : schwarzschildParikhWilczekBorelGradeShift i ≠
      schwarzschildParikhWilczekBorelGradeShift j)
    (hs : a * (schwarzschildParikhWilczekBorelRecoilHolonomy s i).im =
      b * (schwarzschildParikhWilczekBorelRecoilHolonomy s j).im)
    (ht : a * (schwarzschildParikhWilczekBorelRecoilHolonomy t i).im =
      b * (schwarzschildParikhWilczekBorelRecoilHolonomy t j).im) :
    a = 0 ∧ b = 0 := by
  rw [schwarzschildParikhWilczekBorelRecoilHolonomy_im_factorization,
    schwarzschildParikhWilczekBorelRecoilHolonomy_im_factorization,
    schwarzschildParikhWilczekBorelGradeResidual_eq_coordinate_add_shift,
    schwarzschildParikhWilczekBorelGradeResidual_eq_coordinate_add_shift] at hs ht
  have hs' :
      a * (schwarzschildParikhWilczekBorelSpectralCoordinate s +
        schwarzschildParikhWilczekBorelGradeShift i) =
      b * (schwarzschildParikhWilczekBorelSpectralCoordinate s +
        schwarzschildParikhWilczekBorelGradeShift j) := by
    apply (mul_left_cancel₀ hws)
    calc
      schwarzschildParikhWilczekBorelWallFactor s *
          (a * (schwarzschildParikhWilczekBorelSpectralCoordinate s +
            schwarzschildParikhWilczekBorelGradeShift i)) =
          a * (schwarzschildParikhWilczekBorelWallFactor s *
            (schwarzschildParikhWilczekBorelSpectralCoordinate s +
              schwarzschildParikhWilczekBorelGradeShift i)) := by ring
      _ = b * (schwarzschildParikhWilczekBorelWallFactor s *
            (schwarzschildParikhWilczekBorelSpectralCoordinate s +
              schwarzschildParikhWilczekBorelGradeShift j)) := hs
      _ = schwarzschildParikhWilczekBorelWallFactor s *
          (b * (schwarzschildParikhWilczekBorelSpectralCoordinate s +
            schwarzschildParikhWilczekBorelGradeShift j)) := by ring
  have ht' :
      a * (schwarzschildParikhWilczekBorelSpectralCoordinate t +
        schwarzschildParikhWilczekBorelGradeShift i) =
      b * (schwarzschildParikhWilczekBorelSpectralCoordinate t +
        schwarzschildParikhWilczekBorelGradeShift j) := by
    apply (mul_left_cancel₀ hwt)
    calc
      schwarzschildParikhWilczekBorelWallFactor t *
          (a * (schwarzschildParikhWilczekBorelSpectralCoordinate t +
            schwarzschildParikhWilczekBorelGradeShift i)) =
          a * (schwarzschildParikhWilczekBorelWallFactor t *
            (schwarzschildParikhWilczekBorelSpectralCoordinate t +
              schwarzschildParikhWilczekBorelGradeShift i)) := by ring
      _ = b * (schwarzschildParikhWilczekBorelWallFactor t *
            (schwarzschildParikhWilczekBorelSpectralCoordinate t +
              schwarzschildParikhWilczekBorelGradeShift j)) := ht
      _ = schwarzschildParikhWilczekBorelWallFactor t *
          (b * (schwarzschildParikhWilczekBorelSpectralCoordinate t +
            schwarzschildParikhWilczekBorelGradeShift j)) := by ring
  have hab : a = b := by
    by_contra hab
    apply hcoord
    have hab' : a - b ≠ 0 := sub_ne_zero.mpr hab
    apply (mul_left_cancel₀ hab')
    nlinarith [hs', ht']
  subst b
  have ha0 : a = 0 := by
    by_contra ha
    apply hshift
    apply (mul_left_cancel₀ ha)
    nlinarith [hs']
  exact ⟨ha0, ha0⟩

/-- Fixed nonzero diagonal grade weights that make every raw recoil grade report one common
orientation throughout the open critical strip. -/
def SchwarzschildParikhWilczekGradeOnlyDiagonalCalibration
    (scale : ℕ → ℝ) : Prop :=
  (∀ k, scale k ≠ 0) ∧
    ∀ s : ℂ, 0 < s.re → s.re < 1 → ∀ i j : ℕ,
      scale i * (schwarzschildParikhWilczekBorelRecoilHolonomy s i).im =
        scale j * (schwarzschildParikhWilczekBorelRecoilHolonomy s j).im

/-- **PW-B grade-only branch no-go.**  No spectrally independent, nondegenerate diagonal
calibration can turn all raw recoil grades into one common oriented wall channel. -/
theorem no_schwarzschildParikhWilczekGradeOnlyDiagonalCalibration :
    ¬ ∃ scale : ℕ → ℝ, SchwarzschildParikhWilczekGradeOnlyDiagonalCalibration scale := by
  rintro ⟨scale, hnonzero, halign⟩
  let s : ℂ := (1 / 4 : ℂ) + I
  let t : ℂ := (1 / 4 : ℂ) + 2 * I
  have hsre : 0 < s.re := by norm_num [s]
  have hsre1 : s.re < 1 := by norm_num [s]
  have htre : 0 < t.re := by norm_num [t]
  have htre1 : t.re < 1 := by norm_num [t]
  have hws : schwarzschildParikhWilczekBorelWallFactor s ≠ 0 := by
    norm_num [s, schwarzschildParikhWilczekBorelWallFactor]
  have hwt : schwarzschildParikhWilczekBorelWallFactor t ≠ 0 := by
    norm_num [t, schwarzschildParikhWilczekBorelWallFactor]
  have hcoord : schwarzschildParikhWilczekBorelSpectralCoordinate s ≠
      schwarzschildParikhWilczekBorelSpectralCoordinate t := by
    norm_num [s, t, schwarzschildParikhWilczekBorelSpectralCoordinate]
  have hshift : schwarzschildParikhWilczekBorelGradeShift 0 ≠
      schwarzschildParikhWilczekBorelGradeShift 1 := by
    norm_num [schwarzschildParikhWilczekBorelGradeShift]
  have hzero :=
    schwarzschildParikhWilczekGradeOnlyCalibration_twoPoint_rigidity
      s t 0 1 (scale 0) (scale 1) hws hwt hcoord hshift
        (halign s hsre hsre1 0 1) (halign t htre htre1 0 1)
  exact (hnonzero 0) hzero.1

end

end RHTower
