import Mathlib

/-!
# Positive-source quadratic stability

A right-half-plane channel satisfying one transverse sector inequality and one positive-axis
first-moment cap has a universal zero-free quadratic completion. No analyticity is required:
the theorem is pointwise.

For `Re(s)>0`, the nonreal proof converts a hypothetical zero into

`‖κ²-s²‖ ≤ κ²-‖s‖²`.

The squared defect is `4κ² Im(s)²`, so this is impossible off the positive real axis. On that
axis the first-moment cap makes the completion strictly negative.
-/

open Complex Real

namespace HTGeometry

noncomputable section

/-- A transverse sector channel cannot meet its first-moment quadratic target away from the
positive real axis. -/
theorem firstMomentQuadraticCompletion_ne_zero_of_im_ne_zero
    {kappa M : ℝ} {s b : ℂ}
    (hkappa : 0 < kappa) (hM : 0 < M)
    (hsre : 0 < s.re) (hsim : s.im ≠ 0)
    (hcone : s.re * ‖b‖ ≤ ‖s‖ * b.re) :
    ((kappa : ℂ) ^ 2 - s ^ 2) * b -
        ((kappa : ℂ) ^ 2 * (M : ℂ)) * s ≠ 0 := by
  intro hzero
  let D : ℂ := (kappa : ℂ) ^ 2 - s ^ 2
  let x : ℝ := s.re
  let y : ℝ := s.im
  let A : ℝ := kappa ^ 2 - x ^ 2 + y ^ 2
  let C : ℝ := -2 * x * y
  let N : ℝ := Complex.normSq D
  have hs0 : s ≠ 0 := by
    intro hs
    subst s
    simp at hsre
  have htarget : D * b = ((kappa : ℂ) ^ 2 * (M : ℂ)) * s := by
    exact sub_eq_zero.mp hzero
  have hD0 : D ≠ 0 := by
    intro hD
    rw [hD, zero_mul] at htarget
    have hrhs :
        ((kappa : ℂ) ^ 2 * (M : ℂ)) * s ≠ 0 := by
      exact mul_ne_zero
        (mul_ne_zero
          (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr hkappa.ne'))
          (Complex.ofReal_ne_zero.mpr hM.ne'))
        hs0
    exact hrhs htarget.symm
  have hDre : D.re = A := by
    dsimp [D, A, x, y]
    simp [pow_two, Complex.mul_re]
    ring
  have hDim : D.im = C := by
    dsimp [D, C, x, y]
    simp [pow_two, Complex.mul_im]
    ring
  have hN : N = A ^ 2 + C ^ 2 := by
    dsimp only [N]
    rw [Complex.normSq_apply, hDre, hDim]
    ring
  have hNnorm : N = ‖D‖ ^ 2 := by
    dsimp only [N]
    rw [← Complex.sq_norm]
  have hDnormpos : 0 < ‖D‖ := norm_pos_iff.mpr hD0
  have hsNormpos : 0 < ‖s‖ := norm_pos_iff.mpr hs0
  have htargetNorm := congrArg norm htarget
  have hnormRelation :
      ‖D‖ * ‖b‖ = kappa ^ 2 * M * ‖s‖ := by
    norm_num [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hkappa, abs_of_pos hM] at htargetNorm
    nlinarith
  have hre := congrArg Complex.re htarget
  have him := congrArg Complex.im htarget
  have hkpow : (kappa : ℂ) ^ 2 = ((kappa ^ 2 : ℝ) : ℂ) := by
    norm_num
  have hcoef :
      (kappa : ℂ) ^ 2 * (M : ℂ) =
        ((kappa ^ 2 * M : ℝ) : ℂ) := by
    rw [hkpow]
    norm_num
  have hkRe : ((kappa : ℂ) ^ 2).re = kappa ^ 2 := by
    norm_num [pow_two, Complex.mul_re]
  have hkIm : ((kappa : ℂ) ^ 2).im = 0 := by
    norm_num [pow_two, Complex.mul_im]
  have hrhsRe :
      (((kappa : ℂ) ^ 2 * (M : ℂ)) * s).re =
        kappa ^ 2 * M * x := by
    dsimp only [x]
    simp [Complex.mul_re, hkRe, hkIm]
  have hrhsIm :
      (((kappa : ℂ) ^ 2 * (M : ℂ)) * s).im =
        kappa ^ 2 * M * y := by
    dsimp only [y]
    simp [Complex.mul_im, hkRe, hkIm]
  have hre' : A * b.re - C * b.im = kappa ^ 2 * M * x := by
    simpa only [Complex.mul_re, hDre, hDim, hrhsRe] using hre
  have him' : A * b.im + C * b.re = kappa ^ 2 * M * y := by
    simpa only [Complex.mul_im, hDre, hDim, hrhsIm] using him
  have hNbRe :
      N * b.re = kappa ^ 2 * M * x *
        (kappa ^ 2 - (x ^ 2 + y ^ 2)) := by
    rw [hN]
    dsimp only [A, C]
    linear_combination A * hre' + C * him'
  have hsNormSq : ‖s‖ ^ 2 = x ^ 2 + y ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    dsimp only [x, y]
    ring
  have hscaledCone :
      x * N * ‖b‖ ≤ ‖s‖ * N * b.re := by
    have hNnonneg : 0 ≤ N := by rw [hNnorm]; positivity
    have hcone' : x * ‖b‖ ≤ ‖s‖ * b.re := by
      simpa only [x] using hcone
    have hmul := mul_le_mul_of_nonneg_right hcone' hNnonneg
    nlinarith only [hmul]
  have hleft :
      x * N * ‖b‖ =
        x * ‖D‖ * (kappa ^ 2 * M * ‖s‖) := by
    rw [hNnorm]
    calc
      x * ‖D‖ ^ 2 * ‖b‖ =
          x * ‖D‖ * (‖D‖ * ‖b‖) := by ring
      _ = x * ‖D‖ * (kappa ^ 2 * M * ‖s‖) := by
        rw [hnormRelation]
  have hright :
      ‖s‖ * N * b.re =
        ‖s‖ * (kappa ^ 2 * M * x *
          (kappa ^ 2 - (x ^ 2 + y ^ 2))) := by
    calc
      ‖s‖ * N * b.re = ‖s‖ * (N * b.re) := by ring
      _ = ‖s‖ * (kappa ^ 2 * M * x *
          (kappa ^ 2 - (x ^ 2 + y ^ 2))) := by rw [hNbRe]
  rw [hleft, hright] at hscaledCone
  have hpositive : 0 < x * (kappa ^ 2 * M * ‖s‖) := by
    dsimp only [x]
    positivity
  have hDle :
      ‖D‖ ≤ kappa ^ 2 - (x ^ 2 + y ^ 2) := by
    have hcancel :
        x * (kappa ^ 2 * M * ‖s‖) * ‖D‖ ≤
          x * (kappa ^ 2 * M * ‖s‖) *
            (kappa ^ 2 - (x ^ 2 + y ^ 2)) := by
      nlinarith only [hscaledCone]
    exact le_of_mul_le_mul_left hcancel hpositive
  have hrightNonneg :
      0 ≤ kappa ^ 2 - (x ^ 2 + y ^ 2) :=
    le_trans (norm_nonneg D) hDle
  have hsquare :
      ‖D‖ ^ 2 ≤ (kappa ^ 2 - (x ^ 2 + y ^ 2)) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg D) hrightNonneg).2 hDle
  have hidentity :
      N - (kappa ^ 2 - (x ^ 2 + y ^ 2)) ^ 2 =
        4 * kappa ^ 2 * y ^ 2 := by
    rw [hN]
    dsimp only [A, C]
    ring
  rw [← hNnorm] at hsquare
  have hySq : y ^ 2 ≤ 0 := by
    nlinarith only [hsquare, hidentity, sq_pos_of_pos hkappa]
  have hyzero : y = 0 :=
    sq_eq_zero_iff.mp (le_antisymm hySq (sq_nonneg y))
  exact hsim (by simpa only [y] using hyzero)

/-- The first-moment cap gives strict negativity on the positive real axis. -/
theorem firstMomentQuadraticCompletion_real_neg
    {kappa M r b : ℝ}
    (hkappa : 0 < kappa) (hM : 0 < M) (hr : 0 < r)
    (hb0 : 0 ≤ b) (hbM : b ≤ M * r) :
    (kappa ^ 2 - r ^ 2) * b - kappa ^ 2 * M * r < 0 := by
  by_cases hrk : r < kappa
  · have hcoef : 0 < kappa ^ 2 - r ^ 2 := by nlinarith
    have hmul :
        (kappa ^ 2 - r ^ 2) * b ≤
          (kappa ^ 2 - r ^ 2) * (M * r) :=
      mul_le_mul_of_nonneg_left hbM hcoef.le
    have hMr3 : 0 < M * r ^ 3 := mul_pos hM (pow_pos hr 3)
    nlinarith
  · have hcoef : kappa ^ 2 - r ^ 2 ≤ 0 := by
      nlinarith
    have hfirst :
        (kappa ^ 2 - r ^ 2) * b ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hcoef hb0
    have hpenalty : 0 < kappa ^ 2 * M * r := by positivity
    nlinarith

/-- Quadratic completion selected by a channel and its positive first-moment scale. -/
def firstMomentQuadraticCompletion
    (kappa M : ℝ) (B : ℂ → ℂ) (s : ℂ) : ℂ :=
  ((kappa : ℂ) ^ 2 - s ^ 2) * B s -
    ((kappa : ℂ) ^ 2 * (M : ℂ)) * s

/-- Universal first-moment quadratic stability law. No analyticity is needed: the sector cone
excludes nonreal right-half-plane zeros and the moment cap excludes positive-real zeros. -/
theorem firstMomentQuadraticCompletion_ne_zero
    {kappa M : ℝ} {B : ℂ → ℂ}
    (hkappa : 0 < kappa) (hM : 0 < M)
    (hcone : ∀ s : ℂ, 0 < s.re → s.im ≠ 0 →
      s.re * ‖B s‖ ≤ ‖s‖ * (B s).re)
    (haxis : ∀ r : ℝ, 0 < r →
      ∃ b : ℝ, 0 ≤ b ∧ b ≤ M * r ∧ B (r : ℂ) = (b : ℂ))
    {s : ℂ} (hs : 0 < s.re) :
    firstMomentQuadraticCompletion kappa M B s ≠ 0 := by
  by_cases hsim : s.im = 0
  · let r : ℝ := s.re
    have hr : 0 < r := by simpa only [r] using hs
    obtain ⟨b, hb0, hbM, hb⟩ := haxis r hr
    have hsreal : s = (r : ℂ) := by
      apply Complex.ext
      · simp [r]
      · simp [hsim]
    have hneg :=
      firstMomentQuadraticCompletion_real_neg hkappa hM hr hb0 hbM
    rw [hsreal]
    unfold firstMomentQuadraticCompletion
    rw [hb]
    intro hzero
    have hzeroRe := congrArg Complex.re hzero
    norm_num [pow_two, Complex.mul_re] at hzeroRe
    nlinarith
  · unfold firstMomentQuadraticCompletion
    exact firstMomentQuadraticCompletion_ne_zero_of_im_ne_zero
      hkappa hM hs hsim (hcone s hs hsim)

end

end HTGeometry
