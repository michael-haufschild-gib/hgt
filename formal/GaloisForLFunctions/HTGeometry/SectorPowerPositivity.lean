import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Powers stay in a right half-plane while the sector budget lasts

A complex number with `0 < Re z` and `|Im z| <= c * Re z` lies in a sector of half-angle
`arctan c` about the positive axis.  Multiplying two such numbers adds the angles, which in tangent
coordinates is the addition law `(c + d) / (1 - c d)`.  Iterating from `d = c` therefore keeps
`Re (z ^ m) > 0` for every `m` before the tangent budget diverges, with no trigonometry: the whole
argument is the pair of identities

`Re (z w) = Re z Re w - Im z Im w`,   `Im (z w) = Re z Im w + Im z Re w`

together with the triangle inequality.

For `c = 1/5` the rounded budgets are `1/5, 1/2, 4/5, 5/4, 2, 4, 21`, and the seventh power is the
last one the budget covers.
-/

open Complex

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- **The sector multiplication step.**  Two numbers in tangent sectors `c` and `d` with
`c d < 1` multiply into the sector `(c + d) / (1 - c d)`, and the product has positive real part. -/
theorem re_mul_pos_and_abs_im_le {z w : ℂ} {c d e : ℝ}
    (hz : 0 < z.re) (hzc : |z.im| ≤ c * z.re)
    (hw : 0 < w.re) (hwd : |w.im| ≤ d * w.re)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hcd : c * d < 1)
    (he : (c + d) / (1 - c * d) ≤ e) :
    0 < (z * w).re ∧ |(z * w).im| ≤ e * (z * w).re := by
  obtain ⟨hz1, hz2⟩ := abs_le.mp hzc
  obtain ⟨hw1, hw2⟩ := abs_le.mp hwd
  have hcdpos : 0 < 1 - c * d := by linarith
  have hprod : 0 < z.re * w.re := mul_pos hz hw
  have hre : z.re * w.re * (1 - c * d) ≤ (z * w).re := by
    rw [Complex.mul_re]
    nlinarith [hz1, hz2, hw1, hw2, hz.le, hw.le]
  have hrepos : 0 < (z * w).re := lt_of_lt_of_le (by nlinarith) hre
  refine ⟨hrepos, ?_⟩
  have him : |(z * w).im| ≤ (c + d) * (z.re * w.re) := by
    rw [Complex.mul_im]
    rw [abs_le]
    constructor <;> nlinarith [hz1, hz2, hw1, hw2, hz.le, hw.le]
  have henn : 0 ≤ e := le_trans (by positivity) he
  have hkey : (c + d) * (z.re * w.re) ≤ e * (z * w).re := by
    have h1 : (c + d) / (1 - c * d) * (z.re * w.re * (1 - c * d)) =
        (c + d) * (z.re * w.re) := by
      field_simp
    calc
      (c + d) * (z.re * w.re)
          = (c + d) / (1 - c * d) * (z.re * w.re * (1 - c * d)) := h1.symm
      _ ≤ e * (z.re * w.re * (1 - c * d)) := by
            apply mul_le_mul_of_nonneg_right he
            positivity
      _ ≤ e * (z * w).re := mul_le_mul_of_nonneg_left hre henn
  linarith

/-- **Seven powers of a `1/5`-sector number stay in the right half-plane.**  The rounded tangent
budgets `1/5, 1/2, 4/5, 5/4, 2, 4, 21` all keep the product `c d` below one. -/
theorem re_pow_pos_of_abs_im_le_fifth {z : ℂ} (hz : 0 < z.re)
    (him : |z.im| ≤ z.re / 5) {m : ℕ} (hm : 1 ≤ m) (hm7 : m ≤ 7) :
    0 < (z ^ m).re := by
  have hc : |z.im| ≤ (1 / 5 : ℝ) * z.re := by linarith [him]
  have h1 : 0 < (z ^ 1).re ∧ |(z ^ 1).im| ≤ (1 / 5 : ℝ) * (z ^ 1).re := by
    rw [pow_one]
    exact ⟨hz, hc⟩
  have h2 := re_mul_pos_and_abs_im_le hz hc h1.1 h1.2 (by norm_num) (by norm_num)
    (by norm_num) (show ((1:ℝ)/5 + 1/5) / (1 - (1/5) * (1/5)) ≤ 1 / 2 by norm_num)
  rw [← pow_succ'] at h2
  have h3 := re_mul_pos_and_abs_im_le hz hc h2.1 h2.2 (by norm_num) (by norm_num)
    (by norm_num) (show ((1:ℝ)/5 + 1/2) / (1 - (1/5) * (1/2)) ≤ 4 / 5 by norm_num)
  rw [← pow_succ'] at h3
  have h4 := re_mul_pos_and_abs_im_le hz hc h3.1 h3.2 (by norm_num) (by norm_num)
    (by norm_num) (show ((1:ℝ)/5 + 4/5) / (1 - (1/5) * (4/5)) ≤ 5 / 4 by norm_num)
  rw [← pow_succ'] at h4
  have h5 := re_mul_pos_and_abs_im_le hz hc h4.1 h4.2 (by norm_num) (by norm_num)
    (by norm_num) (show ((1:ℝ)/5 + 5/4) / (1 - (1/5) * (5/4)) ≤ 2 by norm_num)
  rw [← pow_succ'] at h5
  have h6 := re_mul_pos_and_abs_im_le hz hc h5.1 h5.2 (by norm_num) (by norm_num)
    (by norm_num) (show ((1:ℝ)/5 + 2) / (1 - (1/5) * 2) ≤ 4 by norm_num)
  rw [← pow_succ'] at h6
  have h7 := re_mul_pos_and_abs_im_le hz hc h6.1 h6.2 (by norm_num) (by norm_num)
    (by norm_num) (show ((1:ℝ)/5 + 4) / (1 - (1/5) * 4) ≤ 21 by norm_num)
  rw [← pow_succ'] at h7
  norm_num at h1 h2 h3 h4 h5 h6 h7
  rcases (by omega : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa using h1.1
  · exact h2.1
  · exact h3.1
  · exact h4.1
  · exact h5.1
  · exact h6.1
  · exact h7.1


/-- **The sector budget chain.**  If a nonnegative sequence `d` starts above `c` and satisfies the
tangent-addition step at every index, then every power of a `c`-sector number stays in the right
half-plane and inside the sector `d m`.  Specializing `d` records exactly how many powers a given
sector constant covers. -/
theorem re_pow_pos_and_abs_im_le_of_chain {z : ℂ} (hz : 0 < z.re) {c : ℝ} (hc : 0 ≤ c)
    (him : |z.im| ≤ c * z.re) (d : ℕ → ℝ) (hd1 : c ≤ d 1) (hdnn : ∀ k, 0 ≤ d k)
    (hstep : ∀ k, 1 ≤ k → c * d k < 1 ∧ (c + d k) / (1 - c * d k) ≤ d (k + 1)) :
    ∀ m, 1 ≤ m → 0 < (z ^ m).re ∧ |(z ^ m).im| ≤ d m * (z ^ m).re := by
  intro m
  induction m with
  | zero => intro h; exact absurd h (by norm_num)
  | succ n ih =>
    intro _
    rcases Nat.eq_zero_or_pos n with rfl | hn1
    · simp only [zero_add, pow_one]
      exact ⟨hz, le_trans him (mul_le_mul_of_nonneg_right hd1 hz.le)⟩
    · obtain ⟨hpos, hbound⟩ := ih hn1
      obtain ⟨hlt, hle⟩ := hstep n hn1
      have := re_mul_pos_and_abs_im_le hz him hpos hbound hc (hdnn n) hlt hle
      rwa [← pow_succ'] at this

/-- **Sector positivity for every exponent.**  A nonzero `z` whose argument satisfies
`|n · arg z| < π/2` has `Re (z ^ n) > 0`.  Writing `z` in polar form gives
`Re (z ^ n) = ‖z‖ ^ n · cos (n · arg z)`, and the hypothesis places the rotated angle strictly inside
the right half-plane.

Unlike the tangent-budget iteration above, this carries no upper bound on `n`: the budget list
`1/5, 1/2, 4/5, 5/4, 2, 4, 21` and its cutoff at the seventh power are exactly the statement that
`n · c < π/2` fails first at `n = 8` when `c = 1/5`. -/
theorem re_pow_pos_of_abs_arg_lt {z : ℂ} (hz : z ≠ 0) {n : ℕ}
    (h : |(n : ℝ) * Complex.arg z| < Real.pi / 2) : 0 < (z ^ n).re := by
  have hpolar : z = (‖z‖ : ℂ) * Complex.exp (Complex.arg z * Complex.I) :=
    (Complex.norm_mul_exp_arg_mul_I z).symm
  have hzn : z ^ n =
      ((‖z‖ ^ n : ℝ) : ℂ) * Complex.exp ((((n : ℝ) * Complex.arg z : ℝ) : ℂ) * Complex.I) := by
    conv_lhs => rw [hpolar]
    rw [mul_pow, ← Complex.exp_nat_mul]
    push_cast
    ring_nf
  have hre : (z ^ n).re = ‖z‖ ^ n * Real.cos ((n : ℝ) * Complex.arg z) := by
    rw [hzn, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  rw [hre]
  have hnorm : 0 < ‖z‖ ^ n := pow_pos (norm_pos_iff.mpr hz) n
  have hcos : 0 < Real.cos ((n : ℝ) * Complex.arg z) :=
    Real.cos_pos_of_mem_Ioo (abs_lt.mp h)
  positivity

end GaloisForLFunctions.HTGeometry

end
