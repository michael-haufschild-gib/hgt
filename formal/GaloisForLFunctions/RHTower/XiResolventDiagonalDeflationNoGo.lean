import GaloisForLFunctions.RHTower.XiResolventDiagonalEdgeDetection

/-!
# Diagonal resolvent edge detection cannot be iterated by atom subtraction

The diagonal edge theorem extracts one real maximal-modulus atom from nonnegative power moments.
This file closes the tempting induction: subtracting that certified positive edge atom need not
preserve diagonal moment nonnegativity, even when the remaining atoms form a strict-smaller
reflection-conjugate pair.

Thus diagonal signs alone cannot deflate successive Xi zeros.  An iterative route must prove a
residual/localized positivity law (equivalently, positivity after an edge-annihilating polynomial),
not merely reapply the first-edge theorem.
-/

open Complex

namespace RHTower

noncomputable section

/-- Three-atom reflection-stable moment model: one positive edge atom and a smaller conjugate
off-axis pair. -/
def xiResolventDiagonalDeflationCounterMoment (n : ℕ) : ℂ :=
  1 + (Complex.I / 4) ^ (n + 1) + (-Complex.I / 4) ^ (n + 1)

/-- Moment sequence after subtracting the contribution of the positive edge atom `1`. -/
def xiResolventDiagonalDeflationCounterResidual (n : ℕ) : ℂ :=
  xiResolventDiagonalDeflationCounterMoment n - 1

/-- The two subleading atoms are exchanged by complex reflection. -/
theorem conj_xiResolventDiagonalDeflationCounterAtom :
    starRingEnd ℂ (Complex.I / 4) = -Complex.I / 4 := by
  simp only [map_div₀, conj_I, conj_ofNat]

/-- Both reflected atoms have modulus `1/4`, strictly below the positive edge modulus `1`. -/
theorem norm_xiResolventDiagonalDeflationCounterAtom :
    ‖Complex.I / 4‖ = (1 / 4 : ℝ) ∧
      ‖-Complex.I / 4‖ = (1 / 4 : ℝ) := by
  constructor <;> norm_num

/-- Despite the off-axis reflected pair, every original diagonal moment has strictly positive real
part.  The positive edge masks all oscillation of the smaller pair. -/
theorem xiResolventDiagonalDeflationCounterMoment_re_pos (n : ℕ) :
    0 < (xiResolventDiagonalDeflationCounterMoment n).re := by
  let tail : ℂ :=
    (Complex.I / 4) ^ (n + 1) + (-Complex.I / 4) ^ (n + 1)
  have hpow : (1 / 4 : ℝ) ^ (n + 1) ≤ (1 / 4 : ℝ) := by
    simpa using pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
      (by norm_num : (1 / 4 : ℝ) ≤ 1) (by omega : 1 ≤ n + 1)
  have htailNorm : ‖tail‖ ≤ 1 / 2 := by
    calc
      ‖tail‖ ≤ ‖(Complex.I / 4) ^ (n + 1)‖ +
          ‖(-Complex.I / 4) ^ (n + 1)‖ := norm_add_le _ _
      _ = 2 * (1 / 4 : ℝ) ^ (n + 1) := by
        rw [norm_pow, norm_pow]
        norm_num
        ring
      _ ≤ 1 / 2 := by linarith
  have htailRe : -(1 / 2 : ℝ) ≤ tail.re := by
    have habs : |tail.re| ≤ 1 / 2 := Complex.abs_re_le_norm tail |>.trans htailNorm
    exact (neg_le_of_abs_le habs)
  rw [xiResolventDiagonalDeflationCounterMoment]
  rw [add_assoc]
  change 0 < (1 + ((Complex.I / 4) ^ (n + 1) +
    (-Complex.I / 4) ^ (n + 1))).re
  change 0 < (1 + tail).re
  rw [Complex.add_re, Complex.one_re]
  linarith

/-- After deleting the certified positive edge atom, the second residual moment is strictly
negative.  Diagonal nonnegativity is therefore not hereditary under edge deflation. -/
theorem xiResolventDiagonalDeflationCounterResidual_one_re_neg :
    (xiResolventDiagonalDeflationCounterResidual 1).re < 0 := by
  rw [xiResolventDiagonalDeflationCounterResidual,
    xiResolventDiagonalDeflationCounterMoment]
  norm_num [pow_two]

/-- Exact no-go package for iterating diagonal edge detection by subtraction, with a
reflection-conjugate smaller remainder. -/
theorem exists_reflectionConjugate_diagonalMomentPositive_not_deflationStable :
    ∃ moment residual : ℕ → ℂ,
      (∀ n, 0 < (moment n).re) ∧
      (∀ n, residual n = moment n - 1) ∧
      (residual 1).re < 0 := by
  exact ⟨xiResolventDiagonalDeflationCounterMoment,
    xiResolventDiagonalDeflationCounterResidual,
    xiResolventDiagonalDeflationCounterMoment_re_pos,
    fun _ => rfl,
    xiResolventDiagonalDeflationCounterResidual_one_re_neg⟩

end

end RHTower
