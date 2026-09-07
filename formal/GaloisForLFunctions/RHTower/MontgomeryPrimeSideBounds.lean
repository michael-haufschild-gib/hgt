import GaloisForLFunctions.RHTower.MontgomeryPrimeSideIdentity

/-!
# Bounds for the remainder blocks of Montgomery's lemma

The three non-prime blocks of `tsum_montgomeryZeroTerm_eq_primeSide` are bounded, for `x ≥ 1`:

* `‖polarRemainder x t‖ ≤ 4x/(1+t²)`;
* `‖xbBlock x t‖ ≤ x^{−1/2} (C + log(|t|+4))` with an explicit constant `C`;
* `‖trivialBlock x t‖ ≤ 16 x^{−2}/(1+|t|)`.

Hence the zero side of Montgomery's lemma is the prime side up to
`O(x/(1+t²) + x^{−1/2} log(|t|+4) + x^{−2}/(1+|t|))`, which is Lemma 1 of
Baluyot–Goldston–Suriajaya–Turnage-Butterbaugh in the normalisation of `montgomeryZeroTerm`.
-/

open Complex Filter Topology
open GaloisForLFunctions.HTGeometry
open ArithmeticFunction (vonMangoldt)

namespace RHTower

/-! ## The polar remainder -/

theorem polarRemainder_eq (x t : ℝ) :
    polarRemainder x t = 2 * (x : ℂ) / ((1 - montgomeryPoleUp t) * montgomeryPoleUp (-t)) := by
  unfold polarRemainder
  have h1 := one_sub_montgomeryPoleUp_ne_zero t
  have h2 := montgomeryPoleUp_ne_zero (-t)
  rw [div_sub_div _ _ h1 h2, div_eq_div_iff (mul_ne_zero h1 h2) (mul_ne_zero h1 h2)]
  simp only [montgomeryPoleUp]
  push_cast
  ring

theorem normSq_one_sub_montgomeryPoleUp (t : ℝ) :
    Complex.normSq (1 - montgomeryPoleUp t) = 1 / 4 + t ^ 2 := by
  rw [Complex.normSq_apply]
  simp only [montgomeryPoleUp, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.one_re, Complex.one_im]
  ring

theorem normSq_montgomeryPoleUp (t : ℝ) :
    Complex.normSq (montgomeryPoleUp t) = 9 / 4 + t ^ 2 := by
  rw [Complex.normSq_apply]
  simp only [montgomeryPoleUp, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  ring

/-- `‖polarRemainder x t‖ ≤ 4x/(1+t²)` for `x ≥ 0`. -/
theorem norm_polarRemainder_le {x : ℝ} (hx : 0 ≤ x) (t : ℝ) :
    ‖polarRemainder x t‖ ≤ 4 * x / (1 + t ^ 2) := by
  rw [polarRemainder_eq, norm_div, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hx]
  have hn1 : ‖1 - montgomeryPoleUp t‖ = Real.sqrt (1 / 4 + t ^ 2) := by
    rw [Complex.norm_eq_sqrt_normSq, normSq_one_sub_montgomeryPoleUp]
  have hn2 : ‖montgomeryPoleUp (-t)‖ = Real.sqrt (9 / 4 + t ^ 2) := by
    rw [Complex.norm_eq_sqrt_normSq, normSq_montgomeryPoleUp]; congr 1; ring
  rw [hn1, hn2, ← Real.sqrt_mul (by positivity)]
  have hkey : ((1 + t ^ 2) / 2) ^ 2 ≤ (1 / 4 + t ^ 2) * (9 / 4 + t ^ 2) := by
    nlinarith [sq_nonneg t, sq_nonneg (t ^ 2)]
  have hsq : (1 + t ^ 2) / 2 ≤ Real.sqrt ((1 / 4 + t ^ 2) * (9 / 4 + t ^ 2)) := by
    rw [Real.le_sqrt (by positivity) (by positivity)]; exact hkey
  have hpos : 0 < Real.sqrt ((1 / 4 + t ^ 2) * (9 / 4 + t ^ 2)) := Real.sqrt_pos.mpr (by positivity)
  rw [div_le_div_iff₀ hpos (by positivity)]
  nlinarith

/-! ## The trivial-zero block -/

theorem norm_ge_half_abs_re_add_abs_im (z : ℂ) : (|z.re| + |z.im|) / 2 ≤ ‖z‖ := by
  have h1 := Complex.abs_re_le_norm z
  have h2 := Complex.abs_im_le_norm z
  linarith

theorem trivialPole_sub_montgomeryPoleUp_re (k : ℕ) (t : ℝ) :
    (trivialPole k - montgomeryPoleUp t).re = -(2 * (k : ℝ) + 7 / 2) := by
  rw [Complex.sub_re, trivialPole_re, montgomeryPoleUp_re]; ring

theorem trivialPole_sub_montgomeryPoleUp_im (k : ℕ) (t : ℝ) :
    (trivialPole k - montgomeryPoleUp t).im = -t := by
  simp [trivialPole, montgomeryPoleUp]

theorem trivialPole_sub_montgomeryPoleDown_re (k : ℕ) (t : ℝ) :
    (trivialPole k - montgomeryPoleDown t).re = -(2 * (k : ℝ) + 3 / 2) := by
  rw [Complex.sub_re, trivialPole_re, montgomeryPoleDown_re]; ring

theorem trivialPole_sub_montgomeryPoleDown_im (k : ℕ) (t : ℝ) :
    (trivialPole k - montgomeryPoleDown t).im = -t := by
  simp [trivialPole, montgomeryPoleDown]

/-- `‖T_k‖ ≤ 4 x^{−2} / (2k + 3/2 + |t|)²` for `x ≥ 1`. -/
theorem norm_montgomeryTrivialTerm_le_height {x : ℝ} (hx : 1 ≤ x) (t : ℝ) (k : ℕ) :
    ‖montgomeryTrivialTerm x t k‖ ≤ 4 * (x ^ 2)⁻¹ / (2 * (k : ℝ) + 3 / 2 + |t|) ^ 2 := by
  have hx0 : 0 < x := by linarith
  unfold montgomeryTrivialTerm
  rw [norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0, trivialPole_re]
  have hpow : x ^ (-(2 * ((k : ℝ) + 1))) ≤ (x ^ 2)⁻¹ := by
    rw [← Real.rpow_two, ← Real.rpow_neg hx0.le]
    apply Real.rpow_le_rpow_of_exponent_le hx
    linarith [Nat.cast_nonneg (α := ℝ) k]
  have hA : (2 * (k : ℝ) + 7 / 2 + |t|) / 2 ≤ ‖trivialPole k - montgomeryPoleUp t‖ := by
    have := norm_ge_half_abs_re_add_abs_im (trivialPole k - montgomeryPoleUp t)
    rw [trivialPole_sub_montgomeryPoleUp_re, trivialPole_sub_montgomeryPoleUp_im, abs_neg, abs_neg,
      abs_of_nonneg (by positivity)] at this
    exact this
  have hB : (2 * (k : ℝ) + 3 / 2 + |t|) / 2 ≤ ‖trivialPole k - montgomeryPoleDown t‖ := by
    have := norm_ge_half_abs_re_add_abs_im (trivialPole k - montgomeryPoleDown t)
    rw [trivialPole_sub_montgomeryPoleDown_re, trivialPole_sub_montgomeryPoleDown_im, abs_neg,
      abs_neg, abs_of_nonneg (by positivity)] at this
    exact this
  have hc : 0 < 2 * (k : ℝ) + 3 / 2 + |t| := by positivity
  have hprod : (2 * (k : ℝ) + 3 / 2 + |t|) ^ 2 / 4
      ≤ ‖trivialPole k - montgomeryPoleUp t‖ * ‖trivialPole k - montgomeryPoleDown t‖ := by
    calc (2 * (k : ℝ) + 3 / 2 + |t|) ^ 2 / 4
        = ((2 * (k : ℝ) + 3 / 2 + |t|) / 2) * ((2 * (k : ℝ) + 3 / 2 + |t|) / 2) := by ring
      _ ≤ ((2 * (k : ℝ) + 7 / 2 + |t|) / 2) * ((2 * (k : ℝ) + 3 / 2 + |t|) / 2) := by
          gcongr; linarith
      _ ≤ _ := mul_le_mul hA hB (by positivity) (norm_nonneg _)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hp := Real.rpow_nonneg hx0.le (-(2 * ((k : ℝ) + 1)))
  calc x ^ (-(2 * ((k : ℝ) + 1))) * (2 * (k : ℝ) + 3 / 2 + |t|) ^ 2
      ≤ (x ^ 2)⁻¹ * (2 * (k : ℝ) + 3 / 2 + |t|) ^ 2 := by gcongr
    _ = 4 * (x ^ 2)⁻¹ * ((2 * (k : ℝ) + 3 / 2 + |t|) ^ 2 / 4) := by ring
    _ ≤ 4 * (x ^ 2)⁻¹ * (‖trivialPole k - montgomeryPoleUp t‖
        * ‖trivialPole k - montgomeryPoleDown t‖) := by gcongr

/-- `Σ_{k≥0} 1/(2k+c)² ≤ 2/c` for `c ≥ 1`. -/
theorem tsum_inv_sq_two_mul_add_le {c : ℝ} (hc : 1 ≤ c) :
    ∑' k : ℕ, 1 / (2 * (k : ℝ) + c) ^ 2 ≤ 2 / c := by
  have hc0 : 0 < c := by linarith
  have hsum : Summable (fun k : ℕ => 1 / (2 * (k : ℝ) + c) ^ 2) := by
    have h := (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
    refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
      (h.mul_left 1)
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
      sorry
    · sorry
  sorry

end RHTower
