import GaloisForLFunctions.RHTower.XiEulerSafeCauchyLoss
import GaloisForLFunctions.RHTower.XiShiftLoewnerFlow

namespace RHTower

open Complex Set
open scoped ComplexConjugate

noncomputable section

/-- Horizontal Xi monotonicity in the centered `W` coordinate. -/
theorem strictMonoOn_norm_xiCent_horizontal_euler (b : ℝ) :
    StrictMonoOn
      (fun a : ℝ => ‖xiCent ((a : ℂ) + (b : ℂ) * I)‖)
      (Set.Ici (1 / 2 : ℝ)) := by
  intro a ha c hc hac
  have h := strictMonoOn_norm_XiC_horizontal_of_halfPlaneBound
    (by norm_num : (0 : ℝ) ≤ 1 / 2) xiZeroHalfPlaneBound_half b ha hc hac
  change ‖xiCent ((a : ℂ) + (b : ℂ) * I)‖ <
    ‖xiCent ((c : ℂ) + (b : ℂ) * I)‖
  rw [xiCent_eq_XiC, xiCent_eq_XiC]
  convert h using 1 <;>
    congr 2 <;>
    apply Complex.ext <;>
    simp

/-- The actual shifted completed-Xi quotient is strictly contractive throughout
the Euler-safe half-plane. -/
theorem norm_xiShiftTheta_lt_one_of_eulerRegion
    {ω : ℝ} (hω : 0 < ω) {W : ℂ} (hW : 1 / 2 + ω < W.re) :
    ‖xiShiftTheta ω W‖ < 1 := by
  let a : ℝ := W.re - ω
  let c : ℝ := W.re + ω
  let b : ℝ := W.im
  have ha : a ∈ Set.Ici (1 / 2 : ℝ) := by
    change 1 / 2 ≤ W.re - ω
    linarith
  have hc : c ∈ Set.Ici (1 / 2 : ℝ) := by
    change 1 / 2 ≤ W.re + ω
    linarith
  have hac : a < c := by
    dsimp [a, c]
    linarith
  have hmono := strictMonoOn_norm_xiCent_horizontal_euler b ha hc hac
  have hminus : W - (ω : ℂ) = (a : ℂ) + (b : ℂ) * I := by
    apply Complex.ext <;> simp [a, b]
  have hplus : W + (ω : ℂ) = (c : ℂ) + (b : ℂ) * I := by
    apply Complex.ext <;> simp [c, b]
  change ‖xiCent ((a : ℂ) + (b : ℂ) * I)‖ <
    ‖xiCent ((c : ℂ) + (b : ℂ) * I)‖ at hmono
  rw [← hminus, ← hplus] at hmono
  have hden : 0 < ‖xiCent (W + (ω : ℂ))‖ :=
    norm_pos_iff.mpr (xiCent_ne_zero_of_half_lt_re (by
      simp only [Complex.add_re, Complex.ofReal_re]
      linarith))
  rw [xiShiftTheta, norm_div]
  exact (div_lt_one hden).mpr hmono

/-- Every one-node shifted-Xi Pick test in the Euler region is strictly positive. -/
theorem re_xiShiftPick_diagonal_pos_of_eulerRegion
    {ω : ℝ} (hω : 0 < ω) {W : ℂ} (hW : 1 / 2 + ω < W.re) :
    0 < (xiShiftPick ω W W).re := by
  have htheta := norm_xiShiftTheta_lt_one_of_eulerRegion hω hW
  have hnormSq : Complex.normSq (xiShiftTheta ω W) < 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg (xiShiftTheta ω W)]
  have hRe : 0 < W.re := by linarith
  rw [xiShiftPick]
  have hden : W + conj W = (2 * W.re : ℝ) := by
    apply Complex.ext
    · simp
      ring
    · simp
  rw [hden, Complex.mul_conj]
  norm_num [Complex.div_re, Complex.normSq_apply]
  apply div_pos
  · apply mul_pos
    · simpa [Complex.normSq_apply] using sub_pos.mpr hnormSq
    · positivity
  · positivity

/-- Shifted completed-Xi quotient in the card's upper-half-plane coordinate. -/
def eulerXiShiftTheta (ω : ℝ) (z : ℂ) : ℂ :=
  xiShiftTheta ω (-I * z)

/-- Shifted completed-Xi Pick kernel in the card's upper-half-plane coordinate. -/
def eulerXiShiftPick (ω : ℝ) (z w : ℂ) : ℂ :=
  I / (z - conj w) *
    (1 - eulerXiShiftTheta ω z * conj (eulerXiShiftTheta ω w))

/-- Exact rotation between centered right-half-plane and upper-half-plane kernels. -/
theorem eulerXiShiftPick_eq_xiShiftPick (ω : ℝ) (z w : ℂ) :
    eulerXiShiftPick ω z w = xiShiftPick ω (-I * z) (-I * w) := by
  simp [eulerXiShiftPick, eulerXiShiftTheta, xiShiftPick]
  have hden : -(I * z) + I * conj w = -I * (z - conj w) := by ring
  rw [hden]
  by_cases hzw : z - conj w = 0
  · simp [hzw]
  · field_simp [hzw]
    rw [show I ^ 2 = (-1 : ℂ) by simp [pow_two]]
    ring

/-- Strict contractivity in the literal Euler sampling region `Im z > 1/2+ω`. -/
theorem norm_eulerXiShiftTheta_lt_one
    {ω : ℝ} (hω : 0 < ω) {z : ℂ} (hz : 1 / 2 + ω < z.im) :
    ‖eulerXiShiftTheta ω z‖ < 1 := by
  apply norm_xiShiftTheta_lt_one_of_eulerRegion hω
  simpa [Complex.mul_re] using hz

/-- Every literal one-node Euler-region Pick test is strictly positive. -/
theorem re_eulerXiShiftPick_diagonal_pos
    {ω : ℝ} (hω : 0 < ω) {z : ℂ} (hz : 1 / 2 + ω < z.im) :
    0 < (eulerXiShiftPick ω z z).re := by
  rw [eulerXiShiftPick_eq_xiShiftPick]
  apply re_xiShiftPick_diagonal_pos_of_eulerRegion hω
  simpa [Complex.mul_re] using hz

end

end RHTower
