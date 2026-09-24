import GaloisForLFunctions.RHTower.XiMeromorphicCauchyPairCenteredCorrection
import GaloisForLFunctions.RHTower.XiResolventMassBudget

open Complex Finset
open scoped BigOperators

namespace RHTower

theorem egc_all_copy_centered_re_neg
    {eps : ℝ} (heps : 0 < eps) (heps1 : eps ≤ 1) (q : XiZeroCopy) :
    (meromorphicCauchyPairShiftResidueCorrection eps 0 (xiSpectralPoint q)).re < 0 := by
  let a := xiSpectralPoint q
  have ha : 32 < a.re ^ (2 : ℕ) := xiSpectral_re_sq_gt_thirtytwo q
  have hb : a.im ^ (2 : ℕ) < 1 / 4 := xiSpectralPoint_im_sq_lt_quarter q
  have hepsSq : eps ^ (2 : ℕ) ≤ 1 := by nlinarith
  have hcast : ((eps : ℂ) ^ (2 : ℕ)).re = eps ^ (2 : ℕ) := by
    simp [pow_two, Complex.mul_re]
  have hcastim : ((eps : ℂ) ^ (2 : ℕ)).im = 0 := by
    simp [pow_two, Complex.mul_im]
  have hzre : 0 < (a ^ (2 : ℕ) - (eps : ℂ) ^ (2 : ℕ)).re := by
    rw [Complex.sub_re, hcast]
    rw [pow_two, Complex.mul_re]
    nlinarith
  have hden : a ^ (2 : ℕ) - (eps : ℂ) ^ (2 : ℕ) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.zero_re] at hre
    linarith
  have hminus : a - 0 - (eps : ℂ) ≠ 0 := by
    intro h
    have hreal := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.zero_re, Complex.ofReal_re] at hreal
    have : a.re = eps := by linarith
    rw [this] at ha
    nlinarith
  have hplus : a - 0 + (eps : ℂ) ≠ 0 := by
    intro h
    have hreal := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.add_re, Complex.zero_re, Complex.ofReal_re] at hreal
    have : a.re = -eps := by linarith
    rw [this] at ha
    nlinarith
  rw [meromorphicCauchyPairShiftResidueCorrection_eq_negative_square_div
    eps 0 a hminus hplus]
  let z : ℂ := a ^ (2 : ℕ) - (eps : ℂ) ^ (2 : ℕ)
  have hz : 0 < z.re := hzre
  have hzsq : 0 < Complex.normSq z := by
    rw [Complex.normSq_apply]
    nlinarith [sq_nonneg z.im]
  simp only [sub_zero]
  change (-((eps : ℂ) ^ (2 : ℕ)) / z).re < 0
  have hformula : (-((eps : ℂ) ^ (2 : ℕ)) / z).re =
      -(eps ^ (2 : ℕ) * (z.re / Complex.normSq z)) := by
    rw [div_eq_mul_inv]
    simp [Complex.mul_re, Complex.inv_re, hcast, hcastim]
  rw [hformula]
  exact neg_lt_zero.mpr (mul_pos (sq_pos_of_pos heps) (div_pos hz hzsq))

theorem egc_all_copy_centered_finite_sum_re_neg
    {eps : ℝ} (heps : 0 < eps) (heps1 : eps ≤ 1)
    (S : Finset XiZeroCopy) (hS : S.Nonempty) :
    (∑ q ∈ S,
      meromorphicCauchyPairShiftResidueCorrection eps 0 (xiSpectralPoint q)).re < 0 := by
  rw [Complex.re_sum]
  exact Finset.sum_neg (fun q hq => egc_all_copy_centered_re_neg heps heps1 q) hS

end RHTower
