import GaloisForLFunctions.RHTower.XiGaussianFullPhaseDebt
import GaloisForLFunctions.RHTower.XiAbsoluteHeightCells
import GaloisForLFunctions.HTGeometry.GaussianPacketMaximizers
import GaloisForLFunctions.HTGeometry.GaussianLogWeightedSampling

/-!
# Actual Xi amplitudes as absolute-height cell samples

Evenness folds sample positions onto the positive half-line. The divisor carrier
is unchanged: every original copy keeps its own cell and vertical displacement.
-/

open scoped Real SchwartzMap NNReal
open Complex MeasureTheory GaloisForLFunctions
noncomputable section
namespace RHTower

/-- The fractional position of an actual copy within its absolute-height cell. -/
def xiAbsoluteHeightCellPosition (q : XiZeroCopy) : Set.Icc (0 : ℝ) 1 :=
  ⟨|(q.1 : ℂ).im| - ⌊|(q.1 : ℂ).im|⌋₊,
    sub_nonneg.mpr (Nat.floor_le (abs_nonneg _)),
    by have h := Nat.lt_floor_add_one |(q.1 : ℂ).im|; linarith only [h]⟩

theorem xiAbsoluteHeightCell_position_identity (q : XiZeroCopy) :
    (⌊|(q.1 : ℂ).im|⌋₊ : ℝ) + (xiAbsoluteHeightCellPosition q : ℝ) = |(q.1 : ℂ).im| := by
  change _ + (|(q.1 : ℂ).im| - _) = _
  ring

/-- The complete even Gaussian has exact sign symmetry at complex arguments. -/
theorem entirePolynomialGaussian_evenSquare_neg (P : Polynomial ℝ) (z : ℂ) :
    entirePolynomialGaussian (evenSquarePolynomial P) (-z) =
      entirePolynomialGaussian (evenSquarePolynomial P) z := by
  simp only [entirePolynomialGaussian, evenSquarePolynomial, Polynomial.eval₂_comp,
    Polynomial.eval₂_pow, Polynomial.eval₂_X, neg_sq]

/-- Folding the real coordinate changes the displacement's sign, without altering its size. -/
def xiAbsoluteGaussianDisplacement (r : {r : ℝ // 0 < r}) (q : XiZeroCopy) :
    Set.Icc (-((r : ℝ) / 2)) ((r : ℝ) / 2) :=
  ⟨(r : ℝ) * (if 0 ≤ (q.1 : ℂ).im then (xiSpectralPoint q).im else -(xiSpectralPoint q).im), by
    have hr := r.property
    have hs := xi_divisor_support_re_mem_open_unit q.1
    have he : (xiSpectralPoint q).im = -((q.1 : ℂ).re - 1 / 2) := by simp [xiSpectralPoint]
    have hi : |(xiSpectralPoint q).im| ≤ 1 / 2 := by
      rw [he, abs_le]
      constructor <;> linarith only [hs.1, hs.2]
    apply abs_le.mp
    rw [abs_mul, abs_of_pos hr]
    split_ifs
    · nlinarith only [mul_le_mul_of_nonneg_left hi hr.le]
    · rw [abs_neg]
      nlinarith only [mul_le_mul_of_nonneg_left hi hr.le]⟩

/-- Every actual amplitude is exactly a sample in its absolute-height cell. -/
theorem xiScaledEvenGaussianAmplitude_absolute_cell (P : Polynomial ℝ)
    (r : {r : ℝ // 0 < r}) (q : XiZeroCopy) :
    xiScaledEvenGaussianAmplitude P r q =
      entirePolynomialGaussian (evenSquarePolynomial P)
        ((((r : ℝ) * ((⌊|(q.1 : ℂ).im|⌋₊ : ℝ) +
          (xiAbsoluteHeightCellPosition q : ℝ)) : ℝ) : ℂ) +
          ((xiAbsoluteGaussianDisplacement r q : ℝ) : ℂ) * Complex.I) := by
  rw [xiAbsoluteHeightCell_position_identity]
  have hre : (xiSpectralPoint q).re = (q.1 : ℂ).im := by simp [xiSpectralPoint]
  change entirePolynomialGaussian (evenSquarePolynomial P) ((r : ℝ) * xiSpectralPoint q) = _
  by_cases hp : 0 ≤ (q.1 : ℂ).im
  · have hz : ((((r : ℝ) * |(q.1 : ℂ).im| : ℝ) : ℂ) +
        ((xiAbsoluteGaussianDisplacement r q : ℝ) : ℂ) * Complex.I) =
        (r : ℝ) * xiSpectralPoint q := by
      apply Complex.ext <;> simp [xiAbsoluteGaussianDisplacement, hp, abs_of_nonneg hp, hre]
    rw [hz]
  · have hz : ((((r : ℝ) * |(q.1 : ℂ).im| : ℝ) : ℂ) +
        ((xiAbsoluteGaussianDisplacement r q : ℝ) : ℂ) * Complex.I) =
        -((r : ℝ) * xiSpectralPoint q) := by
      apply Complex.ext <;>
        simp [xiAbsoluteGaussianDisplacement, hp, abs_of_nonpos (le_of_not_ge hp), hre]
    rw [hz, entirePolynomialGaussian_evenSquare_neg]

/-- The full imaginary-square contribution is controlled by its exact folded sample error. -/
theorem xiScaledEvenGaussian_im_sq_le_absolute_error (P : Polynomial ℝ)
    (r : {r : ℝ // 0 < r}) (q : XiZeroCopy) :
    (xiScaledEvenGaussianAmplitude P r q).im ^ 2 ≤
      ‖entirePolynomialGaussianVerticalError (evenSquarePolynomial P)
        (((⌊|(q.1 : ℂ).im|⌋₊ : ℝ) + (xiAbsoluteHeightCellPosition q : ℝ)) * (r : ℝ))
          (xiAbsoluteGaussianDisplacement r q)‖ ^ 2 := by
  have ha := xiScaledEvenGaussianAmplitude_absolute_cell P r q
  rw [mul_comm (r : ℝ)] at ha
  rw [ha]
  unfold entirePolynomialGaussianVerticalError
  rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_im]
  simp only [polyGaussSchwartz_apply, Complex.ofReal_im, sub_zero]
  nlinarith only [sq_nonneg (entirePolynomialGaussian (evenSquarePolynomial P)
    (((((⌊|(q.1 : ℂ).im|⌋₊ : ℝ) + (xiAbsoluteHeightCellPosition q : ℝ)) * (r : ℝ)) : ℂ) +
      ((xiAbsoluteGaussianDisplacement r q : ℝ) : ℂ) * Complex.I) -
    polyGaussSchwartz (evenSquarePolynomial P)
      (((⌊|(q.1 : ℂ).im|⌋₊ : ℝ) + (xiAbsoluteHeightCellPosition q : ℝ)) * (r : ℝ))).re]

end RHTower
