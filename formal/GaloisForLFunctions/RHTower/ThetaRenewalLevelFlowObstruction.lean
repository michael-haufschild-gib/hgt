import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# A negative-level flow obstruction for renewal divisor orientation

In the right upper quadrant, every negative real level of
`P(z) = (z²-(a²-b²))² + 4a²b²` has positive real logarithmic derivative.
Yet `a+ib` is a zero for arbitrary positive `a,b`.

The exact positive survivor is the inverse-flow formula on the full real-level
hyperbola. It measures distance to the displaced endpoint, so a favorable
slope sign cannot force landing on the imaginary axis.

This elementary counterexample tests a proposed analytic inference in route RN.
It is not a theta-source counterexample or a rejection of the renewal route.
The parameter `a` here is the zero's displacement, not the fixed renewal seam.
-/

open Complex

namespace RHTower.RenewalLevelFlow

noncomputable section


def quartet (a b : ℝ) (z : ℂ) : ℂ :=
  (z ^ 2 - ((a ^ 2 - b ^ 2 : ℝ) : ℂ)) ^ 2 + (4 * a ^ 2 * b ^ 2 : ℝ)

def quartetSlope (a b : ℝ) (z : ℂ) : ℂ :=
  4 * z * (z ^ 2 - ((a ^ 2 - b ^ 2 : ℝ) : ℂ))

theorem quartet_hasDerivAt (a b : ℝ) (z : ℂ) :
    HasDerivAt (quartet a b) (quartetSlope a b z) z := by
  have h := (((hasDerivAt_pow 2 z).sub_const
    ((a ^ 2 - b ^ 2 : ℝ) : ℂ)).pow 2).add_const
      ((4 * a ^ 2 * b ^ 2 : ℝ) : ℂ)
  change HasDerivAt
    (fun w : ℂ => (w ^ 2 - ((a ^ 2 - b ^ 2 : ℝ) : ℂ)) ^ 2 +
      ((4 * a ^ 2 * b ^ 2 : ℝ) : ℂ))
    (4 * z * (z ^ 2 - ((a ^ 2 - b ^ 2 : ℝ) : ℂ))) z
  apply h.congr_deriv
  ring

theorem quartet_parts (a b x y : ℝ) :
    (quartet a b (x + I * y)).im =
      4 * x * y * (x ^ 2 - y ^ 2 - (a ^ 2 - b ^ 2)) ∧
    (quartet a b (x + I * y)).re =
      (x ^ 2 - y ^ 2 - (a ^ 2 - b ^ 2)) ^ 2 -
        4 * x ^ 2 * y ^ 2 + 4 * a ^ 2 * b ^ 2 := by
  constructor <;> simp [quartet, pow_two, mul_re, mul_im] <;> ring

theorem quartet_root (a b : ℝ) : quartet a b (a + I * b) = 0 := by
  apply Complex.ext
  · rw [(quartet_parts a b a b).2]
    simp
  · rw [(quartet_parts a b a b).1]
    simp

theorem quartet_real_level_iff {a b x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (quartet a b (x + I * y)).im = 0 ↔
      x ^ 2 - y ^ 2 = a ^ 2 - b ^ 2 := by
  rw [(quartet_parts a b x y).1]
  have hp : 4 * x * y ≠ 0 := ne_of_gt (by positivity)
  rw [mul_eq_zero, or_iff_right hp, sub_eq_zero]

theorem quartet_negative_level (a b x y : ℝ)
    (hlevel : x ^ 2 - y ^ 2 = a ^ 2 - b ^ 2) :
    (quartet a b (x + I * y)).re =
      -4 * (x ^ 2 - a ^ 2) * (x ^ 2 + b ^ 2) := by
  rw [(quartet_parts a b x y).2, hlevel]
  nlinarith [sq_nonneg (x ^ 2 - a ^ 2)]

theorem quartet_slope_re (a b x y : ℝ)
    (hlevel : x ^ 2 - y ^ 2 = a ^ 2 - b ^ 2) :
    (quartetSlope a b (x + I * y)).re = -8 * x * y ^ 2 := by
  have h : (quartetSlope a b (x + I * y)).re =
      4 * x * (x ^ 2 - y ^ 2 - (a ^ 2 - b ^ 2)) - 8 * x * y ^ 2 := by
    simp [quartetSlope, pow_two, mul_re, mul_im]
    ring
  rw [h, hlevel]
  ring

theorem quartet_negative_level_log_slope_pos {a b x y : ℝ}
    (hx : 0 < x) (hy : 0 < y)
    (hlevel : (quartet a b (x + I * y)).im = 0)
    (hneg : (quartet a b (x + I * y)).re < 0) :
    0 < (quartetSlope a b (x + I * y) / quartet a b (x + I * y)).re := by
  have heq := (quartet_real_level_iff hx hy).mp hlevel
  have hn : quartet a b (x + I * y) ≠ 0 := by
    intro h
    simp [h] at hneg
  rw [Complex.div_re, hlevel, mul_zero, zero_div, add_zero,
    quartet_slope_re a b x y heq]
  exact div_pos (mul_pos_of_neg_of_neg (by nlinarith [sq_pos_of_pos hy]) hneg)
    (Complex.normSq_pos.mpr hn)

theorem quartet_inverse_slope (a b x y : ℝ)
    (hlevel : x ^ 2 - y ^ 2 = a ^ 2 - b ^ 2)
    (hx : x ≠ 0) (hy : y ≠ 0) :
    (quartet a b (x + I * y) / quartetSlope a b (x + I * y)).re =
      (x ^ 2 - a ^ 2) * (x ^ 2 + b ^ 2) /
        (2 * x * (x ^ 2 + y ^ 2)) := by
  have hs : quartetSlope a b (x + I * y) =
      ((-8 * x * y ^ 2 : ℝ) : ℂ) + I * ((8 * x ^ 2 * y : ℝ) : ℂ) := by
    apply Complex.ext
    · simp only [add_re, ofReal_re, mul_re, I_re, zero_mul, ofReal_im, I_im,
        mul_zero, sub_zero, add_zero]
      exact quartet_slope_re a b x y hlevel
    · have h : (quartetSlope a b (x + I * y)).im =
          4 * y * (x ^ 2 - y ^ 2 - (a ^ 2 - b ^ 2)) + 8 * x ^ 2 * y := by
        simp [quartetSlope, pow_two, mul_re, mul_im]
        ring
      rw [h, hlevel]
      simp only [sub_self, mul_zero, zero_add, add_im, ofReal_im, mul_im,
        I_re, I_im, ofReal_re, one_mul]
  rw [Complex.div_re, (quartet_parts a b x y).1, hlevel]
  simp only [sub_self, mul_zero]
  rw [quartet_negative_level a b x y hlevel, hs]
  have hxy : x ^ 2 + y ^ 2 ≠ 0 := ne_of_gt (by positivity)
  simp only [add_re, ofReal_re, mul_re, I_re, zero_mul, ofReal_im, I_im, mul_zero,
    sub_zero, add_zero, normSq_apply, add_im, mul_im, one_mul, zero_add]
  field_simp
  ring

end

end RHTower.RenewalLevelFlow
