import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheAtomCrossMatrixIsCloseToItsCenterKernel
import GaloisForLFunctions.ArithmeticLorentzianGeometry.TheHodgeIndexHoldsAtAFixedFractionOfTheSpacing
import GaloisForLFunctions.RHTower.EvenSectorAbelLaplace

/-!
# Quadratic dilation error of the two pole moments

On a shrinking support the exponential weights differ from one by a quantity
linear in the width. Their product, divided by atom mass, therefore differs
from its unweighted value by a quantity quadratic in the width. Both signs of
the bump and both exponential pole moments are retained.
-/

noncomputable section

open MeasureTheory

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open ArithmeticLorentzianGeometry SpacingScaleHarmonicAnalysis

/-- The actual exponential moment at a real pole parameter. -/
def atomExponentialMoment (g : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ u, g u * Real.exp (t * u)

private theorem abs_exp_mul_sub_one_le {t u w : ℝ}
    (ht : |t| ≤ 1 / 2) (hu : u ∈ Set.Icc 0 w) (hw : w ≤ 1) :
    |Real.exp (t * u) - 1| ≤ w / 2 * Real.exp (1 / 2) := by
  have htu : |t * u| ≤ w / 2 := by
    rw [abs_mul, abs_of_nonneg hu.1]
    exact (mul_le_mul_of_nonneg_right ht hu.1).trans (by linarith only [hu.2])
  have htu1 : |t * u| ≤ 1 / 2 := htu.trans (by linarith only [hw])
  exact (_root_.RHTower.EvenSector.abs_exp_sub_one_le_mul_exp (t * u)).trans
    (mul_le_mul htu (Real.exp_le_exp.mpr htu1) (Real.exp_pos _).le
      (by linarith only [hu.1, hu.2]))

/-- The moment differs from the integral by at most width times the absolute mass. -/
theorem abs_atomExponentialMoment_sub_integral_le {g : ℝ → ℝ} {t w : ℝ}
    (hg : Continuous g) (hgc : HasCompactSupport g)
    (hsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0)
    (ht : |t| ≤ 1 / 2) (hw : w ≤ 1) :
    |atomExponentialMoment g t - ∫ u, g u| ≤
      w / 2 * Real.exp (1 / 2) * ∫ u, |g u| := by
  have hi : Integrable g := hg.integrable_of_hasCompactSupport hgc
  have hie : Integrable (fun u => g u * Real.exp (t * u)) :=
    (hg.mul (by fun_prop)).integrable_of_hasCompactSupport hgc.mul_right
  have h := abs_integral_shift_mul_le hg hgc hsupp
    (φ := fun u => Real.exp (t * u) - 1) (c := 0) (by fun_prop)
    (M := w / 2 * Real.exp (1 / 2)) (fun u hu =>
      abs_exp_mul_sub_one_le ht (by simpa only [zero_add] using hu) hw)
  simp only [sub_zero] at h
  rw [atomExponentialMoment, ← integral_sub hie hi]
  convert h using 2
  congr 1
  funext u
  ring

/-- The pole moment itself is bounded by a fixed multiple of absolute atom mass. -/
theorem abs_atomExponentialMoment_le {g : ℝ → ℝ} {t w : ℝ}
    (hg : Continuous g) (hgc : HasCompactSupport g)
    (hsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0)
    (ht : |t| ≤ 1 / 2) (hw : w ≤ 1) :
    |atomExponentialMoment g t| ≤ Real.exp (1 / 2) * ∫ u, |g u| := by
  have h := abs_integral_shift_mul_le hg hgc hsupp
    (φ := fun u => Real.exp (t * u)) (c := 0) (by fun_prop)
    (M := Real.exp (1 / 2)) (fun u hu => by
      rw [abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      have hu0 : 0 ≤ u := hu.1
      have hu1 : u ≤ 1 := by have h := hu.2; linarith only [h, hw]
      have ht' := (le_abs_self t).trans ht
      exact (mul_le_mul_of_nonneg_right ht' hu0).trans (by linarith only [hu1]))
  simpa only [sub_zero, atomExponentialMoment] using h

/-- A symmetric scalar product estimate keeps both moment errors. -/
private theorem abs_product_sub_sq_le {p m I A D E : ℝ}
    (hp : |p - I| ≤ D) (hm : |m - I| ≤ D)
    (hp0 : |p| ≤ E * A) (hI : |I| ≤ A) (hA : 0 ≤ A) (hD : 0 ≤ D) :
    |m * p - I ^ 2| ≤ D * (E + 1) * A := by
  have heq : m * p - I ^ 2 = (m - I) * p + I * (p - I) := by ring
  rw [heq]
  calc
    _ ≤ |m - I| * |p| + |I| * |p - I| := by
      simpa only [abs_mul] using abs_add_le ((m - I) * p) (I * (p - I))
    _ ≤ D * (E * A) + A * D := add_le_add
      (mul_le_mul hm hp0 (abs_nonneg _) hD)
      (mul_le_mul hI hp (abs_nonneg _) hA)
    _ = _ := by ring

/-- Explicit signed-profile constant for the normalized two-pole product. -/
def atomPoleMomentErrorConstant (φ : ℝ → ℝ) : ℝ :=
  (Real.exp (1 / 2) * (Real.exp (1 / 2) + 1) / 2) *
    (∫ u, |φ u|) ^ 2 / (∫ u, φ u ^ 2)

/-- Both actual pole moments have a quadratic error after atom-mass normalization. -/
theorem abs_dilated_pole_product_sub_le {φ : ℝ → ℝ} {w : ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) (hw0 : 0 < w) (hw1 : w ≤ 1) :
    |atomExponentialMoment (atomDilate φ w) (-(1 / 2)) *
        atomExponentialMoment (atomDilate φ w) (1 / 2) /
          (∫ u, atomDilate φ w u ^ 2) - w * (∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2)| ≤
      atomPoleMomentErrorConstant φ * w ^ 2 := by
  obtain ⟨hg, hgs, hgc⟩ := atomDilate_facts hφ hsupp hw0
  have hA : 0 ≤ ∫ u, |atomDilate φ w u| := integral_nonneg fun u => abs_nonneg _
  have hD : 0 ≤ w / 2 * Real.exp (1 / 2) * ∫ u, |atomDilate φ w u| := by positivity
  have hI : |∫ u, atomDilate φ w u| ≤ ∫ u, |atomDilate φ w u| :=
    abs_integral_le_integral_abs
  have h := abs_product_sub_sq_le
    (abs_atomExponentialMoment_sub_integral_le hg.continuous hgc hgs
      (t := 1 / 2) (by norm_num) hw1)
    (abs_atomExponentialMoment_sub_integral_le hg.continuous hgc hgs
      (t := -(1 / 2)) (by norm_num) hw1)
    (abs_atomExponentialMoment_le hg.continuous hgc hgs
      (t := 1 / 2) (by norm_num) hw1) hI hA hD
  have hmass := integral_atomDilate_sq (φ := φ) hw0
  have hmasspos : 0 < ∫ u, atomDilate φ w u ^ 2 := by rw [hmass]; positivity
  have hint : (∫ u, atomDilate φ w u) = w * ∫ u, φ u := by
    simp only [atomDilate]
    rw [MeasureTheory.Measure.integral_comp_div (fun u => φ u) w]
    rw [abs_of_pos hw0, smul_eq_mul]
  have habs := integral_abs_atomDilate (φ := φ) hw0
  have hdiv : |(atomExponentialMoment (atomDilate φ w) (-(1 / 2)) *
      atomExponentialMoment (atomDilate φ w) (1 / 2) -
        (∫ u, atomDilate φ w u) ^ 2) / (∫ u, atomDilate φ w u ^ 2)| ≤
      (w / 2 * Real.exp (1 / 2) * (∫ u, |atomDilate φ w u|) *
        (Real.exp (1 / 2) + 1) * ∫ u, |atomDilate φ w u|) /
          (∫ u, atomDilate φ w u ^ 2) := by
    rw [abs_div, abs_of_pos hmasspos]
    exact div_le_div_of_nonneg_right h hmasspos.le
  rw [hint, habs, hmass] at hdiv
  rw [hmass]
  convert hdiv using 1
  · congr 1
    field_simp [hw0.ne', hM.ne']
  · simp only [atomPoleMomentErrorConstant]
    field_simp [hw0.ne', hM.ne']

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
