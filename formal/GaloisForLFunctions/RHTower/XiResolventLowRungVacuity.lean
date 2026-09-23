import GaloisForLFunctions.RHTower.XiResolventHankelLadder
import GaloisForLFunctions.RHTower.XiWardCriticalBudgetProbe
import GaloisForLFunctions.HTGeometry.SectorPowerPositivity

/-!
# The low rungs of the resolvent ladder are unconditionally vacuous

The resolvent criterion asks for nonnegativity of the moments
`R n X = sum_q (w q + X)^(-(n+1))`, `w q = xiSpectralPoint q ^ 2`.  This file measures how far up
that ladder one must climb before the condition can say anything at all.

Every shifted squared spectral point lies in a narrow sector about the positive axis: the strip
gives `|Im (alpha)| < 1/2`, hence `|Im (w q)| = 2 |Re alpha| |Im alpha| < |Re alpha|`, while the
computation-free height floor `32 < (Re alpha)^(2 : ℕ)` gives
`Re (w q) + X >= (Re alpha)^(2 : ℕ) - 1/4 >= 5 |Re alpha|`.  So

`|Im (w q + X)| <= Re (w q + X) / 5`

for every copy and every `X >= 0`, unconditionally.  Powers stay in the right half-plane while the
tangent budget lasts (`SectorPowerPositivity`), so the first seven moments have nonnegative real
part **whether or not RH holds**.  Those rungs therefore carry no information about off-critical
zeros; the ladder can only begin to detect at order eight, and the threshold moves up as the
height floor improves.
-/

open Complex
open scoped BigOperators

namespace RHTower

noncomputable section

/-- **The unconditional sector bound.**  Every shifted squared spectral point lies in the tangent
sector `1/5` about the positive real axis. -/
theorem abs_im_xiSpectralSq_add_le_fifth {X : ℝ} (hX : 0 ≤ X) (q : XiZeroCopy) :
    |(xiSpectralPoint q ^ 2 + (X : ℂ)).im| ≤
      (xiSpectralPoint q ^ 2 + (X : ℂ)).re / 5 := by
  set a : ℝ := (xiSpectralPoint q).re with ha
  set b : ℝ := (xiSpectralPoint q).im with hb
  have hheight : 32 < a ^ 2 := by
    rw [ha]; exact xiSpectral_re_sq_gt_thirtytwo q
  have hbhalf : |b| < 1 / 2 := by rw [hb]; exact abs_im_xiSpectralPoint_lt_half q
  have hre : (xiSpectralPoint q ^ 2 + (X : ℂ)).re = a ^ 2 - b ^ 2 + X := by
    simp only [Complex.add_re, Complex.ofReal_re, pow_two, Complex.mul_re, ← ha, ← hb]
  have him : (xiSpectralPoint q ^ 2 + (X : ℂ)).im = 2 * (a * b) := by
    simp only [Complex.add_im, Complex.ofReal_im, add_zero, pow_two, Complex.mul_im,
      ← ha, ← hb]
    ring
  have habs : (5 : ℝ) * |a| ≤ a ^ 2 - 1 / 4 := by
    have habs2 : |a| ^ 2 = a ^ 2 := sq_abs a
    have hpos : 0 ≤ |a| := abs_nonneg a
    nlinarith [hheight, habs2, hpos]
  have hbsq : b ^ 2 < 1 / 4 := by
    have := sq_abs b
    nlinarith [hbhalf, abs_nonneg b]
  rw [hre, him, le_div_iff₀ (by norm_num : (0:ℝ) < 5), abs_mul, abs_two]
  have : |a * b| = |a| * |b| := abs_mul a b
  rw [this]
  nlinarith [abs_nonneg a, abs_nonneg b, hbhalf, habs, hbsq, hX]

/-- Every one of the first seven resolvent powers has nonnegative real part at every copy. -/
theorem re_xiResolventPoint_pow_nonneg {X : ℝ} (hX : 0 ≤ X) {n : ℕ} (hn : n ≤ 6)
    (q : XiZeroCopy) :
    0 ≤ (xiResolventPoint X q ^ (n + 1)).re := by
  have hre : 0 < (xiSpectralPoint q ^ 2 + (X : ℂ)).re :=
    xiSpectralSq_add_ofReal_re_pos hX q
  have hsector := abs_im_xiSpectralSq_add_le_fifth hX q
  have hpow : 0 < ((xiSpectralPoint q ^ 2 + (X : ℂ)) ^ (n + 1)).re :=
    GaloisForLFunctions.HTGeometry.re_pow_pos_of_abs_im_le_fifth hre hsector
      (Nat.succ_le_succ (Nat.zero_le n)) (by omega)
  have hinv : xiResolventPoint X q ^ (n + 1) =
      ((xiSpectralPoint q ^ 2 + (X : ℂ)) ^ (n + 1))⁻¹ := by
    rw [xiResolventPoint, inv_pow]
  rw [hinv, Complex.inv_re]
  exact div_nonneg hpow.le (Complex.normSq_nonneg _)

/-- **The first seven rungs of the resolvent ladder hold unconditionally.**  Hence they carry no
information about off-critical zeros: the criterion can only begin to detect at order eight, and
the threshold rises as the height floor `32 < (Re alpha)^(2 : ℕ)` is improved. -/
theorem re_xiResolventMoment_nonneg {X : ℝ} (hX : 0 ≤ X) {n : ℕ} (hn : n ≤ 6) :
    0 ≤ (xiResolventMoment n X).re := by
  rw [xiResolventMoment, Complex.re_tsum (summable_xiResolventPoint_pow hX n)]
  exact tsum_nonneg fun q => re_xiResolventPoint_pow_nonneg hX hn q

end

end RHTower
