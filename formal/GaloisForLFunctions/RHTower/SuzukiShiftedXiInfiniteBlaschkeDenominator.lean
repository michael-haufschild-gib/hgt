import GaloisForLFunctions.HTGeometry.IndexedBlaschkeMultiplier
import GaloisForLFunctions.RHTower.SuzukiShiftedXiInfiniteUpperKernelInertia

open Complex Filter Topology Metric
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- The strict-right shifted Xi pole divisor satisfies the disk Blaschke condition, with
multiplicity copies retained. -/
theorem summable_one_sub_norm_xiShiftPoleDiskCoordinate
    {omega : ℝ} (homega : 0 ≤ omega) :
    Summable (fun q : XiShiftRightZeroCopy omega =>
      1 - ‖xiShiftPoleDiskCoordinate omega q‖) := by
  have hbound : ∀ q : XiShiftRightZeroCopy omega,
      1 - ‖xiShiftPoleDiskCoordinate omega q‖ ≤
        8 / ‖xiSpectralPoint q.1‖ ^ (2 : ℕ) := by
    intro q
    let mu : ℂ := xiSpectralPoint q.1
    let p : ℂ := xiShiftPoleCoordinate omega q
    have hmuImSq : mu.im ^ (2 : ℕ) < 1 / 4 := by
      have hstrip := xi_divisor_support_centered_re_sq_lt_quarter q.1.1
      have him : mu.im = -(((q.1.1 : ℂ).re) - 1 / 2) := by
        simp [mu, xiSpectralPoint]
      rw [him, neg_sq]
      exact hstrip
    have hpim : 0 < p.im := xiShiftPoleCoordinate_im_pos omega q
    have hpimHalf : p.im < 1 / 2 := by
      have hmuNeg : -mu.im < 1 / 2 := by
        nlinarith [sq_nonneg (mu.im + 1 / 2)]
      dsimp only [p, xiShiftPoleCoordinate]
      simp only [sub_im, neg_im, mul_im, ofReal_re, ofReal_im, I_re, I_im,
        mul_zero, mul_one, add_zero]
      linarith
    have hden : p + I ≠ 0 := by
      intro hzero
      have him := congrArg Complex.im hzero
      norm_num at him
      linarith
    have hcoord : xiShiftPoleDiskCoordinate omega q = upperToDiskCayley p := rfl
    have hrlt : ‖upperToDiskCayley p‖ < 1 := by
      simpa [hcoord] using norm_xiShiftPoleDiskCoordinate_lt_one omega q
    have hdefect := one_sub_norm_upperToDiskCayley_sq hden
    have hdenOne : 1 ≤ ‖p + I‖ := by
      have hsq := Complex.sq_norm (p + I)
      rw [Complex.normSq_apply] at hsq
      have him : (p + I).im = p.im + 1 := by simp
      rw [him] at hsq
      nlinarith [sq_nonneg (p + I).re, norm_nonneg (p + I)]
    have homegaHalf : omega < 1 / 2 := by
      have hselected := q.2
      norm_num [mul_re] at hselected
      have hmuNeg : -mu.im < 1 / 2 := by
        nlinarith [sq_nonneg (mu.im + 1 / 2)]
      dsimp only [mu] at hmuNeg
      linarith
    have hshiftNorm : ‖(((1 - omega : ℝ) : ℂ) * I)‖ ≤ 1 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by linarith), norm_I, mul_one]
      linarith
    have hmuEq : mu = -(p + I) + (((1 - omega : ℝ) : ℂ) * I) := by
      dsimp only [mu, p, xiShiftPoleCoordinate]
      push_cast
      ring
    have hmuLe : ‖mu‖ ≤ 2 * ‖p + I‖ := by
      calc
        ‖mu‖ = ‖-(p + I) + (((1 - omega : ℝ) : ℂ) * I)‖ := by rw [hmuEq]
        _ ≤ ‖-(p + I)‖ + ‖(((1 - omega : ℝ) : ℂ) * I)‖ :=
          norm_add_le _ _
        _ ≤ ‖-(p + I)‖ + 1 := add_le_add le_rfl hshiftNorm
        _ = ‖p + I‖ + 1 := by rw [norm_neg]
        _ ≤ 2 * ‖p + I‖ := by linarith
    have hmuSqLe : ‖mu‖ ^ (2 : ℕ) ≤ 4 * ‖p + I‖ ^ (2 : ℕ) := by
      nlinarith [norm_nonneg mu, norm_nonneg (p + I)]
    have hmuPos : 0 < ‖mu‖ := norm_pos_iff.mpr (xiSpectralPoint_ne_zero q.1)
    have hdenPos : 0 < ‖p + I‖ := norm_pos_iff.mpr hden
    rw [hcoord]
    calc
      1 - ‖upperToDiskCayley p‖ ≤ 1 - ‖upperToDiskCayley p‖ ^ (2 : ℕ) := by
        nlinarith [norm_nonneg (upperToDiskCayley p)]
      _ = 4 * p.im / ‖p + I‖ ^ (2 : ℕ) := hdefect
      _ ≤ 8 / ‖mu‖ ^ (2 : ℕ) := by
        apply (div_le_div_iff₀ (sq_pos_of_pos hdenPos) (sq_pos_of_pos hmuPos)).2
        have hleft : 4 * p.im * ‖mu‖ ^ (2 : ℕ) ≤ 2 * ‖mu‖ ^ (2 : ℕ) := by
          exact mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg ‖mu‖)
        have hright : 2 * ‖mu‖ ^ (2 : ℕ) ≤ 8 * ‖p + I‖ ^ (2 : ℕ) := by
          linarith
        exact hleft.trans hright
      _ = 8 / ‖xiSpectralPoint q.1‖ ^ (2 : ℕ) := rfl
  have hbase : Summable (fun q : XiShiftRightZeroCopy omega =>
      1 / ‖xiSpectralPoint q.1‖ ^ (2 : ℕ)) :=
    xiSpectralPoint_inv_sq_summable.subtype
      (fun q => omega < (I * xiSpectralPoint q).re)
  have hmajor : Summable (fun q : XiShiftRightZeroCopy omega =>
      8 / ‖xiSpectralPoint q.1‖ ^ (2 : ℕ)) := by
    refine (hbase.mul_left 8).congr fun q => ?_
    ring
  exact Summable.of_nonneg_of_le
    (fun q => sub_nonneg.mpr (norm_xiShiftPoleDiskCoordinate_lt_one omega q).le)
    hbound hmajor

/-- Literal disk Blaschke denominator over every strict-right shifted-Xi pole copy. -/
def xiShiftPoleBlaschkeMultiplier
    {omega : ℝ} (homega : 0 ≤ omega) : DiskMultiplier :=
  indexedBlaschkeMultiplier
    (xiShiftPoleDiskCoordinate omega)
    (norm_xiShiftPoleDiskCoordinate_lt_one omega)
    (summable_one_sub_norm_xiShiftPoleDiskCoordinate homega)

/-- With no strict-right shifted-Xi zero copy, the full denominator is pointwise one. -/
theorem xiShiftPoleBlaschkeMultiplier_fn_eq_one_of_isEmpty
    {omega : ℝ} (homega : 0 ≤ omega)
    [IsEmpty (XiShiftRightZeroCopy omega)] :
    (xiShiftPoleBlaschkeMultiplier homega).fn = fun _ => 1 :=
  indexedBlaschkeMultiplier_fn_eq_one_of_isEmpty
    (xiShiftPoleDiskCoordinate omega)
    (norm_xiShiftPoleDiskCoordinate_lt_one omega)
    (summable_one_sub_norm_xiShiftPoleDiskCoordinate homega)

/-- Every strict-right shifted-Xi pole copy is an exact zero of the literal denominator. -/
theorem xiShiftPoleBlaschkeMultiplier_apply_zero
    {omega : ℝ} (homega : 0 ≤ omega)
    (q : XiShiftRightZeroCopy omega) :
    (xiShiftPoleBlaschkeMultiplier homega).fn
      (xiShiftPoleDiskCoordinate omega q) = 0 :=
  indexedBlaschkeMultiplier_apply_zero
    (xiShiftPoleDiskCoordinate omega)
    (norm_xiShiftPoleDiskCoordinate_lt_one omega)
    (summable_one_sub_norm_xiShiftPoleDiskCoordinate homega) q

/-- An infinite literal strict-right shifted-Xi divisor has an infinite-dimensional denominator
model space. -/
theorem not_finiteDimensional_xiShiftPoleBlaschkeMultiplier_modelSpace
    {omega : ℝ} (homega : 0 ≤ omega)
    [Infinite (XiShiftRightZeroCopy omega)] :
    ¬ FiniteDimensional ℂ
      (hardyMultiplierModelSpace (xiShiftPoleBlaschkeMultiplier homega)) := by
  apply not_finiteDimensional_indexedBlaschkeMultiplier_modelSpace
  intro k
  obtain ⟨q, hq⟩ := exists_xiShiftPoleCoordinate_injective_packet omega k
  refine ⟨q, ?_⟩
  intro i j hij
  apply hq
  have hpi : xiShiftPoleCoordinate omega (q i) + I ≠ 0 := by
    intro hzero
    have him := congrArg Complex.im hzero
    norm_num at him
    linarith [xiShiftPoleCoordinate_im_pos omega (q i)]
  have hpj : xiShiftPoleCoordinate omega (q j) + I ≠ 0 := by
    intro hzero
    have him := congrArg Complex.im hzero
    norm_num at him
    linarith [xiShiftPoleCoordinate_im_pos omega (q j)]
  change lineCayley (xiShiftPoleCoordinate omega (q i)) =
    lineCayley (xiShiftPoleCoordinate omega (q j)) at hij
  have hinv := congrArg GaloisForLFunctions.RHTower.suzukiUpperCayleyInv hij
  rw [GaloisForLFunctions.RHTower.suzukiUpperCayleyInv_lineCayley hpi,
    GaloisForLFunctions.RHTower.suzukiUpperCayleyInv_lineCayley hpj] at hinv
  exact hinv

end

end RHTower
