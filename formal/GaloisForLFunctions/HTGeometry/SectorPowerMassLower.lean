import GaloisForLFunctions.HTGeometry.SectorPowerPositivity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Quantitative real-part lower bound for powers in a quadratic sector

If a complex number lies in the right-half-plane sector

`Im(z)² ≤ Re(z)² / 84`,

then its `k`th power retains at least

`(1 - k² / 168) ‖z‖ᵏ`

in the real direction.  This is the algebraic sector-to-mass connector needed by shifted
complex-moment arguments.  It remains valid for every exponent; applications that need a positive
lower mass specialize to `k² < 168`.
-/

open Complex

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The real arctangent contracts absolute value. -/
theorem abs_arctan_le_abs (x : ℝ) :
    |Real.arctan x| ≤ |x| := by
  have key : ∀ y : ℝ, 0 ≤ y → Real.arctan y ≤ y := by
    intro y hy
    rcases eq_or_lt_of_le hy with h | h
    · rw [← h, Real.arctan_zero]
    · exact (lt_of_lt_of_eq
        (Real.lt_tan (Real.arctan_pos.mpr h) (Real.arctan_lt_pi_div_two y))
        (Real.tan_arctan y)).le
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx, abs_of_nonneg]
    · exact key x hx
    · exact Real.arctan_nonneg.mpr hx
  · have hx' : 0 ≤ -x := le_of_lt (neg_pos.mpr (lt_of_not_ge hx))
    have hatan : 0 ≤ Real.arctan (-x) := Real.arctan_nonneg.mpr hx'
    calc
      |Real.arctan x| = |Real.arctan (-x)| := by
        rw [Real.arctan_neg, abs_neg]
      _ ≤ |-x| := by
        simpa only [abs_of_nonneg hatan, abs_of_nonneg hx'] using key (-x) hx'
      _ = |x| := abs_neg x

/-- On the open right half-plane, principal argument is the arctangent of slope. -/
theorem complexArg_eq_arctan_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    z.arg = Real.arctan (z.im / z.re) := by
  obtain ⟨h1, h2⟩ := abs_lt.mp
    (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz))
  rw [← Complex.tan_arg]
  exact (Real.arctan_tan h1 h2).symm

/-- Polar-coordinate formula for the real part of an integral complex power. -/
theorem re_pow_eq_norm_pow_mul_cos_arg (z : ℂ) (k : ℕ) :
    (z ^ k).re = ‖z‖ ^ k * Real.cos ((k : ℝ) * z.arg) := by
  have hcomplex : z ^ k =
      ((‖z‖ ^ k : ℝ) : ℂ) *
        Complex.exp ((((k : ℝ) * z.arg : ℝ) : ℂ) * Complex.I) := by
    calc
      z ^ k =
          (((‖z‖ : ℝ) : ℂ) *
            Complex.exp ((z.arg : ℂ) * Complex.I)) ^ k := by
        rw [Complex.norm_mul_exp_arg_mul_I]
      _ = (((‖z‖ : ℝ) : ℂ) ^ k) *
            (Complex.exp ((z.arg : ℂ) * Complex.I) ^ k) := by
        rw [mul_pow]
      _ = (((‖z‖ : ℝ) : ℂ) ^ k) *
            Complex.exp ((k : ℂ) * ((z.arg : ℂ) * Complex.I)) := by
        rw [← Complex.exp_nat_mul]
      _ = ((‖z‖ ^ k : ℝ) : ℂ) *
            Complex.exp ((((k : ℝ) * z.arg : ℝ) : ℂ) * Complex.I) := by
        congr 1
        · norm_num
        · push_cast
          ring_nf
  rw [hcomplex, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.exp_re, Complex.mul_re, Complex.I_re, Complex.I_im]
  norm_num

/-- A `1/84` quadratic-sector point retains the quadratic-cosine fraction of every absolute
power in the real direction. -/
theorem re_pow_lower_of_re_pos_of_im_sq_le_one_div_eightyFour
    {z : ℂ} (hre : 0 < z.re)
    (hsector : z.im ^ (2 : ℕ) ≤ (1 / 84 : ℝ) * z.re ^ (2 : ℕ))
    (k : ℕ) :
    (1 - (k : ℝ) ^ (2 : ℕ) / 168) * ‖z‖ ^ k ≤ (z ^ k).re := by
  have harg :
      |z.arg| ≤ |z.im / z.re| := by
    rw [complexArg_eq_arctan_of_re_pos hre]
    exact abs_arctan_le_abs _
  have hreSq : 0 < z.re ^ (2 : ℕ) := sq_pos_of_pos hre
  have hratioSq : (z.im / z.re) ^ (2 : ℕ) ≤ (1 / 84 : ℝ) := by
    rw [div_pow]
    exact (div_le_iff₀ hreSq).2 hsector
  have hargSq : z.arg ^ (2 : ℕ) ≤ (1 / 84 : ℝ) := by
    exact (sq_le_sq.mpr harg).trans hratioSq
  have hangleSq :
      ((k : ℝ) * z.arg) ^ (2 : ℕ) ≤ (k : ℝ) ^ (2 : ℕ) / 84 := by
    rw [mul_pow]
    have hdiff : 0 ≤ (1 / 84 : ℝ) - z.arg ^ (2 : ℕ) := by
      linarith
    nlinarith [mul_nonneg (sq_nonneg (k : ℝ)) hdiff]
  have hcos := Real.one_sub_sq_div_two_le_cos
    (x := (k : ℝ) * z.arg)
  have hlower :
      1 - (k : ℝ) ^ (2 : ℕ) / 168 ≤
        Real.cos ((k : ℝ) * z.arg) := by
    nlinarith
  rw [re_pow_eq_norm_pow_mul_cos_arg]
  simpa only [mul_comm] using
    mul_le_mul_of_nonneg_right hlower (pow_nonneg (norm_nonneg z) k)

/-- The exact fourteenth-power endpoint margin for the `1/84` sector.

Unlike the quadratic cosine bound, which ceases to be positive at exponent thirteen, the exact
real-part polynomial retains more than `2/41` of the fourteenth absolute power. The constant is
matched to the reciprocal-square Xi endpoint radius used by the RHTower source. -/
theorem re_pow_fourteen_gt_two_over_fortyOne_norm_pow_of_sector
    {z : ℂ} (hre : 0 < z.re)
    (hsector : z.im ^ (2 : ℕ) ≤ (1 / 84 : ℝ) * z.re ^ (2 : ℕ)) :
    (2 / 41 : ℝ) * ‖z‖ ^ (14 : ℕ) < (z ^ (14 : ℕ)).re := by
  let x : ℝ := z.re
  let y : ℝ := z.im
  let X : ℝ := x ^ (2 : ℕ)
  let Y : ℝ := y ^ (2 : ℕ)
  let D : ℝ := X - 84 * Y
  have hx : 0 < x := by simpa only [x] using hre
  have hX : 0 < X := sq_pos_of_pos hx
  have hY : 0 ≤ Y := sq_nonneg y
  have hD : 0 ≤ D := by
    dsimp only [D, X, Y, x, y]
    norm_num at hsector ⊢
    nlinarith
  have hsector' : Y ≤ X / 84 := by
    dsimp only [X, Y, x, y]
    norm_num at hsector ⊢
    nlinarith
  let C : ℝ :=
    X ^ (3 : ℕ) - 91 * X ^ (2 : ℕ) * Y + 1001 * X * Y ^ (2 : ℕ) - 3003 * Y ^ (3 : ℕ)
  have hCidentity :
      C - (4 / 75 : ℝ) * X ^ (3 : ℕ) =
        (71 / 75 : ℝ) * D ^ (3 : ℕ) +
          (11067 / 75 : ℝ) * D ^ (2 : ℕ) * Y +
          (431403 / 75 : ℝ) * D * Y ^ (2 : ℕ) +
          (5859 / 75 : ℝ) * Y ^ (3 : ℕ) := by
    dsimp only [C, D]
    ring
  have hC : (4 / 75 : ℝ) * X ^ (3 : ℕ) < C := by
    by_cases hY0 : Y = 0
    · subst Y
      dsimp only [C, D] at hCidentity ⊢
      nlinarith [pow_pos hX 3]
    · have hYpos : 0 < Y := lt_of_le_of_ne hY (Ne.symm hY0)
      have hD3 : 0 ≤ D ^ (3 : ℕ) := pow_nonneg hD 3
      have hD2Y : 0 ≤ D ^ (2 : ℕ) * Y :=
        mul_nonneg (pow_nonneg hD 2) hY
      have hDY2 : 0 ≤ D * Y ^ (2 : ℕ) :=
        mul_nonneg hD (pow_nonneg hY 2)
      have hY3 : 0 < Y ^ (3 : ℕ) := pow_pos hYpos 3
      nlinarith
  have htailOne :
      0 ≤ X ^ (2 : ℕ) * Y ^ (4 : ℕ) * (3003 * X - 1001 * Y) := by
    have hfactor : 0 ≤ 3003 * X - 1001 * Y := by
      nlinarith
    positivity
  have htailTwo :
      0 ≤ Y ^ (6 : ℕ) * (91 * X - Y) := by
    have hfactor : 0 ≤ 91 * X - Y := by
      nlinarith
    positivity
  have htwoRe : (z ^ (2 : ℕ)).re = x ^ (2 : ℕ) - y ^ (2 : ℕ) := by
    rw [show z ^ (2 : ℕ) = z * z by ring, Complex.mul_re]
    dsimp only [x, y]
    ring
  have htwoIm : (z ^ (2 : ℕ)).im = 2 * x * y := by
    rw [show z ^ (2 : ℕ) = z * z by ring, Complex.mul_im]
    dsimp only [x, y]
    ring
  have hfourRe :
      (z ^ (4 : ℕ)).re = x ^ (4 : ℕ) - 6 * x ^ (2 : ℕ) * y ^ (2 : ℕ) + y ^ (4 : ℕ) := by
    rw [show z ^ (4 : ℕ) = z ^ (2 : ℕ) * z ^ (2 : ℕ) by ring, Complex.mul_re, htwoRe, htwoIm]
    ring
  have hfourIm :
      (z ^ (4 : ℕ)).im = 4 * x ^ (3 : ℕ) * y - 4 * x * y ^ (3 : ℕ) := by
    rw [show z ^ (4 : ℕ) = z ^ (2 : ℕ) * z ^ (2 : ℕ) by ring, Complex.mul_im, htwoRe, htwoIm]
    ring
  have heightRe :
      (z ^ (8 : ℕ)).re =
        x ^ (8 : ℕ) - 28 * x ^ (6 : ℕ) * y ^ (2 : ℕ) + 70 * x ^ (4 : ℕ) * y ^ (4 : ℕ) -
          28 * x ^ (2 : ℕ) * y ^ (6 : ℕ) + y ^ (8 : ℕ) := by
    rw [show z ^ (8 : ℕ) = z ^ (4 : ℕ) * z ^ (4 : ℕ) by ring, Complex.mul_re, hfourRe, hfourIm]
    ring
  have heightIm :
      (z ^ (8 : ℕ)).im =
        8 * x ^ (7 : ℕ) * y - 56 * x ^ (5 : ℕ) * y ^ (3 : ℕ) + 56 * x ^ (3 : ℕ) * y ^ (5 : ℕ) -
          8 * x * y ^ (7 : ℕ) := by
    rw [show z ^ (8 : ℕ) = z ^ (4 : ℕ) * z ^ (4 : ℕ) by ring, Complex.mul_im, hfourRe, hfourIm]
    ring
  have hre14 :
      (z ^ (14 : ℕ)).re =
        X ^ (7 : ℕ) - 91 * X ^ (6 : ℕ) * Y + 1001 * X ^ (5 : ℕ) * Y ^ (2 : ℕ) -
          3003 * X ^ (4 : ℕ) * Y ^ (3 : ℕ) + 3003 * X ^ (3 : ℕ) * Y ^ (4 : ℕ) -
          1001 * X ^ (2 : ℕ) * Y ^ (5 : ℕ) + 91 * X * Y ^ (6 : ℕ) - Y ^ (7 : ℕ) := by
    rw [show z ^ (14 : ℕ) = (z ^ (8 : ℕ) * z ^ (4 : ℕ)) * z ^ (2 : ℕ) by ring,
      Complex.mul_re, Complex.mul_re, Complex.mul_im,
      heightRe, heightIm, hfourRe, hfourIm, htwoRe, htwoIm]
    dsimp only [x, y, X, Y]
    ring
  have hreLower : (4 / 75 : ℝ) * X ^ (7 : ℕ) < (z ^ (14 : ℕ)).re := by
    rw [hre14]
    have hCdiff : 0 < C - (4 / 75 : ℝ) * X ^ (3 : ℕ) :=
      sub_pos.mpr hC
    have hmain :
        0 < X ^ (4 : ℕ) * (C - (4 / 75 : ℝ) * X ^ (3 : ℕ)) :=
      mul_pos (pow_pos hX 4) hCdiff
    dsimp only [C] at hmain
    nlinarith
  have hnorm14 : ‖z‖ ^ (14 : ℕ) = (X + Y) ^ (7 : ℕ) := by
    rw [show ‖z‖ ^ (14 : ℕ) = (‖z‖ ^ (2 : ℕ)) ^ (7 : ℕ) by ring,
      Complex.sq_norm, Complex.normSq_apply]
    dsimp only [X, Y, x, y]
    ring
  have hXY : X + Y ≤ (85 / 84 : ℝ) * X := by
    nlinarith
  have hpow :
      (X + Y) ^ (7 : ℕ) ≤ ((85 / 84 : ℝ) * X) ^ (7 : ℕ) :=
    pow_le_pow_left₀ (by positivity) hXY 7
  have hratio : (85 / 84 : ℝ) ^ (7 : ℕ) < 82 / 75 := by norm_num
  have hnormUpper : ‖z‖ ^ (14 : ℕ) < (82 / 75 : ℝ) * X ^ (7 : ℕ) := by
    rw [hnorm14]
    calc
      (X + Y) ^ (7 : ℕ) ≤ ((85 / 84 : ℝ) * X) ^ (7 : ℕ) := hpow
      _ = (85 / 84 : ℝ) ^ (7 : ℕ) * X ^ (7 : ℕ) := by rw [mul_pow]
      _ < (82 / 75 : ℝ) * X ^ (7 : ℕ) :=
        mul_lt_mul_of_pos_right hratio (pow_pos hX 7)
  calc
    (2 / 41 : ℝ) * ‖z‖ ^ (14 : ℕ) <
        (2 / 41 : ℝ) * ((82 / 75 : ℝ) * X ^ (7 : ℕ)) := by
      exact mul_lt_mul_of_pos_left hnormUpper (by norm_num)
    _ = (4 / 75 : ℝ) * X ^ (7 : ℕ) := by ring
    _ < (z ^ (14 : ℕ)).re := hreLower

end

end GaloisForLFunctions.HTGeometry
