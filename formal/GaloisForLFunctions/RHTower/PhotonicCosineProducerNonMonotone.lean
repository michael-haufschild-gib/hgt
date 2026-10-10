import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# A lossless producer at one depth does not bound the depth of the zeros

For the even real quartic `F(z) = (z² + 1)(z² + 3)`, with zeros `±i` and `±i√3`, the cosine shift is

  `A_h(z) = (F(z + ih) + F(z − ih))/2 = z⁴ + (4 − 6h²) z² + (h² − 1)(h² − 3)`

(`cosineShift_quartic_eq`). Therefore:

* at `h² = 9/10` every zero of `A_h` is real (`cosineShift_quartic_zeros_real`), although `F` has
  the zero `i` of depth `1 > h`;
* at `h² = 2` the shift is `z⁴ − 8z² − 1`, with the purely imaginary zero `i(√17 − 4)^{1/2}`
  (`cosineShift_quartic_exists_nonreal`). So real-rootedness in `h` is not monotone: real at
  `h² = 9/10`, not real at `h² = 2`, and real again for `h² ≥ 3` (de Bruijn).

For the PTR producer `cos(hD)Ξ` this means a lossless medium at a single depth `h` carries no bound
on the depth of the zeros. Only the whole family `h > 0` (equivalently its limit `h → 0`) decides
RH. Defects can be hidden at intermediate depths by the interaction of the zero quadruples.
-/

open Complex

namespace RHTower

noncomputable section

/-- The quartic `(z² + 1)(z² + 3)`. -/
def quarticF (z : ℂ) : ℂ := (z ^ 2 + 1) * (z ^ 2 + 3)

theorem cosineShift_quartic_eq (h : ℝ) (z : ℂ) :
    (quarticF (z + h * I) + quarticF (z - h * I)) / 2 =
      z ^ 4 + (4 - 6 * (h : ℂ) ^ 2) * z ^ 2 + ((h : ℂ) ^ 2 - 1) * ((h : ℂ) ^ 2 - 3) := by
  have e1 : (z + (h : ℂ) * I) ^ 2 = z ^ 2 - (h : ℂ) ^ 2 + 2 * h * z * I := by
    linear_combination (h : ℂ) ^ 2 * Complex.I_sq
  have e2 : (z - (h : ℂ) * I) ^ 2 = z ^ 2 - (h : ℂ) ^ 2 - 2 * h * z * I := by
    linear_combination (h : ℂ) ^ 2 * Complex.I_sq
  unfold quarticF
  rw [e1, e2]
  linear_combination (2 * (h : ℂ) * z) ^ 2 * Complex.I_sq

theorem quarticF_I : quarticF I = 0 := by
  unfold quarticF; rw [Complex.I_sq]; ring

/-- If `z²` is a positive real number, `z` is real. -/
theorem im_eq_zero_of_sq_eq_pos {z : ℂ} {r : ℝ} (hr : 0 < r) (hz : z ^ 2 = r) : z.im = 0 := by
  have hre : (z ^ 2).re = r := by rw [hz]; simp
  have him : (z ^ 2).im = 0 := by rw [hz]; simp
  rw [sq, Complex.mul_re] at hre
  rw [sq, Complex.mul_im] at him
  have hxy : z.re * z.im = 0 := by linarith
  rcases mul_eq_zero.mp hxy with h0 | h0
  · rw [h0] at hre; nlinarith [sq_nonneg z.im]
  · exact h0

/-- **Lossless at `h² = 9/10` despite a zero of depth `1`.** -/
theorem cosineShift_quartic_zeros_real {z : ℂ}
    (hz : (quarticF (z + (Real.sqrt (9 / 10) : ℝ) * I) +
      quarticF (z - (Real.sqrt (9 / 10) : ℝ) * I)) / 2 = 0) : z.im = 0 := by
  rw [cosineShift_quartic_eq] at hz
  have hs : ((Real.sqrt (9 / 10) : ℝ) : ℂ) ^ 2 = 9 / 10 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; push_cast; ring
  rw [hs] at hz
  set r₁ : ℝ := (7 + 2 * Real.sqrt 7) / 10
  set r₂ : ℝ := (7 - 2 * Real.sqrt 7) / 10
  have h7 : Real.sqrt 7 ^ 2 = 7 := Real.sq_sqrt (by norm_num)
  have h7lt : 2 * Real.sqrt 7 < 7 := by nlinarith [Real.sqrt_nonneg 7]
  have h7pos : 0 < Real.sqrt 7 := Real.sqrt_pos.mpr (by norm_num)
  have hfac : (z ^ 2 - r₁) * (z ^ 2 - r₂) = 0 := by
    have e : (z ^ 2 - (r₁ : ℂ)) * (z ^ 2 - (r₂ : ℂ)) =
        z ^ 4 + (4 - 6 * (9 / 10 : ℂ)) * z ^ 2 + ((9 / 10 : ℂ) - 1) * ((9 / 10 : ℂ) - 3) := by
      have h7c : ((Real.sqrt 7 : ℝ) : ℂ) ^ 2 = 7 := by rw [← Complex.ofReal_pow, h7]; push_cast; ring
      simp only [r₁, r₂]
      push_cast
      linear_combination (-(4 : ℂ) / 100) * h7c
    rw [e]; exact hz
  rcases mul_eq_zero.mp hfac with h1 | h1
  · exact im_eq_zero_of_sq_eq_pos (r := r₁) (by positivity) (sub_eq_zero.mp h1)
  · exact im_eq_zero_of_sq_eq_pos (r := r₂) (by simp only [r₂]; linarith) (sub_eq_zero.mp h1)

/-- **Not lossless at `h² = 2`.** The shift has a purely imaginary zero. -/
theorem cosineShift_quartic_exists_nonreal :
    ∃ z : ℂ, z.im ≠ 0 ∧
      (quarticF (z + (Real.sqrt 2 : ℝ) * I) + quarticF (z - (Real.sqrt 2 : ℝ) * I)) / 2 = 0 := by
  -- `w = z²` solves `w² − 8w − 1 = 0`; take `w = 4 − √17 < 0`, `z = i √(√17 − 4)`
  set a : ℝ := Real.sqrt (Real.sqrt 17 - 4)
  have h17 : Real.sqrt 17 ^ 2 = 17 := Real.sq_sqrt (by norm_num)
  have h17gt : 4 < Real.sqrt 17 := by
    rw [show (4 : ℝ) = Real.sqrt 16 by rw [show (16 : ℝ) = 4 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have ha2 : a ^ 2 = Real.sqrt 17 - 4 := Real.sq_sqrt (by linarith)
  have hapos : 0 < a := Real.sqrt_pos.mpr (by linarith)
  refine ⟨(a : ℂ) * I, by simp [hapos.ne'], ?_⟩
  rw [cosineShift_quartic_eq]
  have hs : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; push_cast; ring
  rw [hs]
  have hz2 : ((a : ℂ) * I) ^ 2 = -((Real.sqrt 17 : ℂ) - 4) := by
    rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, ha2]; push_cast; ring
  have hz4 : ((a : ℂ) * I) ^ 4 = ((Real.sqrt 17 : ℂ) - 4) ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, hz2]; ring
  rw [hz4, hz2]
  have h17c : ((Real.sqrt 17 : ℝ) : ℂ) ^ 2 = 17 := by
    rw [← Complex.ofReal_pow, h17]; push_cast; ring
  linear_combination h17c

end

end RHTower
