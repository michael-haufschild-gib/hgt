import GaloisForLFunctions.RHTower.SteinhausModel
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

open MeasureTheory Complex
open scoped ComplexConjugate

noncomputable section
namespace RHTower
namespace SteinhausModel

theorem continuous_charFactor (k : ℤ) : Continuous (charFactor k) := by
  unfold charFactor
  fun_prop

theorem integrable_charFactor (k : ℤ) :
    Integrable (charFactor k) (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
  (continuous_charFactor k).integrableOn_Icc

theorem charFactor_add (k l : ℤ) (x : ℝ) :
    charFactor (k + l) x = charFactor k x * charFactor l x := by
  unfold charFactor
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem charFactor_neg (k : ℤ) (x : ℝ) :
    charFactor (-k) x = conj (charFactor k x) := by
  unfold charFactor
  rw [← Complex.exp_conj]
  congr 1
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]

theorem norm_charFactor (k : ℤ) (x : ℝ) : ‖charFactor k x‖ = 1 := by
  unfold charFactor
  rw [Complex.norm_exp]
  simp [Complex.mul_re, Complex.mul_im]

end SteinhausModel
open SteinhausModel

/-- A finite Fourier density prescribing a small complex mean on the original uniform phase interval. -/
def steinhausAffineCircleWeight (m : ℂ) (x : ℝ) : ℝ :=
  1 + 2 * (conj m * charFactor 1 x).re

theorem continuous_steinhausAffineCircleWeight (m : ℂ) : Continuous (steinhausAffineCircleWeight m) := by
  unfold steinhausAffineCircleWeight charFactor
  fun_prop

theorem steinhausAffineCircleWeight_nonneg {m : ℂ} (hm : ‖m‖ ≤ 1 / 2) (x : ℝ) :
    0 ≤ steinhausAffineCircleWeight m x := by
  have hnorm : ‖conj m * charFactor 1 x‖ = ‖m‖ := by
    rw [norm_mul, norm_conj, norm_charFactor, mul_one]
  have hre := Complex.abs_re_le_norm (conj m * charFactor 1 x)
  rw [hnorm] at hre
  have hlow := neg_abs_le (conj m * charFactor 1 x).re
  unfold steinhausAffineCircleWeight
  linarith

/-- The actual real density has exactly the three Fourier modes -1, 0 and 1. -/
theorem steinhausAffineCircleWeight_coe (m : ℂ) (x : ℝ) :
    (steinhausAffineCircleWeight m x : ℂ) =
      1 + conj m * charFactor 1 x + m * charFactor (-1) x := by
  rw [charFactor_neg]
  apply Complex.ext <;>
    simp [steinhausAffineCircleWeight, Complex.mul_re, Complex.mul_im] <;> ring

/-- The prescribed-mean density is normalized in the original uniform phase law. -/
theorem integral_steinhausAffineCircleWeight (m : ℂ) :
    (∫ x, steinhausAffineCircleWeight m x ∂(volume.restrict (Set.Icc (0 : ℝ) 1))) = 1 := by
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simp_rw [steinhausAffineCircleWeight_coe]
  have h0 : Integrable (fun x => (1 : ℂ) + conj m * charFactor 1 x)
      (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    (integrable_const (1 : ℂ)).add ((integrable_charFactor 1).const_mul (conj m))
  rw [integral_add h0 ((integrable_charFactor (-1)).const_mul m),
    integral_add (integrable_const (1 : ℂ)) ((integrable_charFactor 1).const_mul (conj m)),
    integral_const_mul, integral_const_mul]
  simp [charInt]

/-- The first complex moment is exactly the requested mean, without an asymptotic approximation. -/
theorem integral_steinhausAffineCircleWeight_mul_phase (m : ℂ) :
    (∫ x, (steinhausAffineCircleWeight m x : ℂ) * charFactor 1 x
      ∂(volume.restrict (Set.Icc (0 : ℝ) 1))) = m := by
  have hp (x : ℝ) : (steinhausAffineCircleWeight m x : ℂ) * charFactor 1 x =
      charFactor 1 x + conj m * charFactor 2 x + m := by
    have hs : charFactor 1 x * charFactor 1 x = charFactor 2 x := by
      simpa using (charFactor_add 1 1 x).symm
    have hi : charFactor (-1) x * charFactor 1 x = 1 := by
      simpa only [neg_add_cancel, charFactor_zero] using (charFactor_add (-1) 1 x).symm
    rw [steinhausAffineCircleWeight_coe]
    calc
      _ = charFactor 1 x + conj m * (charFactor 1 x * charFactor 1 x) +
          m * (charFactor (-1) x * charFactor 1 x) := by ring
      _ = _ := by rw [hs, hi, mul_one]
  simp_rw [hp]
  have h0 : Integrable (fun x => charFactor 1 x + conj m * charFactor 2 x)
      (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    (integrable_charFactor 1).add ((integrable_charFactor 2).const_mul (conj m))
  rw [integral_add h0 (integrable_const m),
    integral_add (integrable_charFactor 1) ((integrable_charFactor 2).const_mul (conj m)), integral_const_mul]
  simp [charInt]

end RHTower
