import GaloisForLFunctions.RHTower.XiSquaredSeamDyadicHalfPlaneRigidity

/-!
# Unconditional low squared-Xi dyadic rungs

The critical strip and unconditional off-line squared-height gap put the fixed-shift squared-Xi
coordinate in a sector narrow enough to make powers `1`, `2`, `4`, and `8` strictly positive.
The existing order-sixteen source theorem supplies power `16`.  Consequently RH is equivalent to
the remaining dyadic tail beginning at power `32`.
-/

open Complex

namespace RHTower

noncomputable section

theorem complex_pow_two_re_pos_of_eightyFive_sector
    {z : ℂ} (hsector : 85 * z.im ^ (2 : ℕ) < z.re ^ (2 : ℕ)) :
    0 < (z ^ (2 : ℕ)).re := by
  rw [pow_two, Complex.mul_re]
  nlinarith

theorem complex_pow_four_re_pos_of_eightyFive_sector
    {z : ℂ} (hre : 0 < z.re) (hsector : 85 * z.im ^ (2 : ℕ) < z.re ^ (2 : ℕ)) :
    0 < (z ^ (4 : ℕ)).re := by
  have hformula :
      (z ^ (4 : ℕ)).re = z.re ^ (4 : ℕ) - 6 * z.re ^ (2 : ℕ) * z.im ^ (2 : ℕ) + z.im ^ (4 : ℕ) := by
    simp [pow_succ, Complex.mul_re]
    ring
  rw [hformula]
  have hscale := mul_lt_mul_of_pos_right hsector (sq_pos_of_pos hre)
  nlinarith [sq_nonneg (z.im ^ (2 : ℕ))]

theorem complex_pow_eight_re_pos_of_eightyFive_sector
    {z : ℂ} (hre : 0 < z.re) (hsector : 85 * z.im ^ (2 : ℕ) < z.re ^ (2 : ℕ)) :
    0 < (z ^ (8 : ℕ)).re := by
  let s : ℝ := z.re ^ (2 : ℕ)
  let t : ℝ := z.im ^ (2 : ℕ)
  have hs : 0 < s := by dsimp only [s]; positivity
  have ht : 0 ≤ t := by dsimp only [t]; positivity
  have hst : 85 * t < s := by simpa only [s, t] using hsector
  have hts : t ≤ s := by nlinarith
  have ht2s2 : t ^ (2 : ℕ) ≤ s ^ (2 : ℕ) := by
    have hprod := mul_nonneg (sub_nonneg.mpr hts) (add_nonneg hs.le ht)
    nlinarith
  have hcompare : s * t ^ (3 : ℕ) ≤ s ^ (3 : ℕ) * t := by
    have hmul := mul_le_mul_of_nonneg_left ht2s2 (mul_nonneg hs.le ht)
    nlinarith
  have hscaled := mul_lt_mul_of_pos_right hst (pow_pos hs 3)
  have h56 : 56 * s ^ (3 : ℕ) * t < s ^ (4 : ℕ) := by
    have hnonneg : 0 ≤ s ^ (3 : ℕ) * t := mul_nonneg (pow_nonneg hs.le 3) ht
    nlinarith
  have hformula :
      (z ^ (8 : ℕ)).re =
        s ^ (4 : ℕ) - 28 * s ^ (3 : ℕ) * t + 70 * s ^ (2 : ℕ) * t ^ (2 : ℕ) -
          28 * s * t ^ (3 : ℕ) + t ^ (4 : ℕ) := by
    have hfourRe :
        (z ^ (4 : ℕ)).re = z.re ^ (4 : ℕ) - 6 * z.re ^ (2 : ℕ) * z.im ^ (2 : ℕ) + z.im ^ (4 : ℕ) := by
      simp [pow_succ, Complex.mul_re]
      ring
    have hfourIm :
        (z ^ (4 : ℕ)).im = 4 * z.re ^ (3 : ℕ) * z.im - 4 * z.re * z.im ^ (3 : ℕ) := by
      simp [pow_succ, Complex.mul_im]
      ring
    rw [show z ^ (8 : ℕ) = z ^ (4 : ℕ) * z ^ (4 : ℕ) by ring, Complex.mul_re, hfourRe, hfourIm]
    dsimp only [s, t]
    ring
  rw [hformula]
  nlinarith [mul_nonneg (sq_nonneg s) (sq_nonneg t), pow_nonneg ht 4]

theorem xiSquaredSeamOneCoordinate_re_formula (q : XiZeroCopy) :
    (xiSquaredSeamOneCoordinate q).re =
      xiSquaredSeamOneRadialA q /
        (xiSquaredSeamOneRadialA q ^ (2 : ℕ) + xiSquaredSeamTransverseB q ^ (2 : ℕ)) := by
  rw [xiSquaredSeamOneCoordinate, Complex.inv_re, Complex.normSq_apply]
  norm_num [Complex.mul_re, Complex.mul_im]
  ring

theorem xiSquaredSeamOneCoordinate_re_pos (q : XiZeroCopy) :
    0 < (xiSquaredSeamOneCoordinate q).re := by
  rw [xiSquaredSeamOneCoordinate_re_formula]
  have hA := xiSquaredSeamOneRadialA_pos q
  have hden : 0 < xiSquaredSeamOneRadialA q ^ (2 : ℕ) + xiSquaredSeamTransverseB q ^ (2 : ℕ) := by
    nlinarith [sq_pos_of_pos hA, sq_nonneg (xiSquaredSeamTransverseB q)]
  positivity

/-- The fixed-shift squared-Xi coordinate lies in the strict sector
`85 * Im(z)^(2 : ℕ) < Re(z)^(2 : ℕ)`. -/
theorem xiSquaredSeamOneCoordinate_eightyFive_sector (q : XiZeroCopy) :
    85 * (xiSquaredSeamOneCoordinate q).im ^ (2 : ℕ) <
      (xiSquaredSeamOneCoordinate q).re ^ (2 : ℕ) := by
  by_cases hoff : (q.1 : ℂ).re = 1 / 2
  · have hre := xiSquaredSeamOneCoordinate_re_pos q
    have him : (xiSquaredSeamOneCoordinate q).im = 0 := by
      simp [xiSquaredSeamOneCoordinate, xiSquaredSeamTransverseB, hoff]
    rw [him]
    norm_num
    exact sq_pos_of_pos hre
  · let u : ℝ := ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ)
    let v : ℝ := (q.1 : ℂ).im ^ (2 : ℕ)
    let A : ℝ := xiSquaredSeamOneRadialA q
    let B : ℝ := xiSquaredSeamTransverseB q
    have hu : u < 1 / 4 :=
      xi_divisor_support_centered_re_sq_lt_quarter q.1
    have hv : 85 < v := by
      simpa only [v] using xiZeroCopy_offLine_eightyFive_lt_im_sq q hoff
    have hv0 : 0 < v := by linarith
    have hBsq : B ^ (2 : ℕ) = 4 * u * v := by
      dsimp only [B, u, v, xiSquaredSeamTransverseB]
      ring
    have hBv : B ^ (2 : ℕ) < v := by
      rw [hBsq]
      have h4u : 4 * u < 1 := by nlinarith
      have hmul := mul_lt_mul_of_pos_right h4u hv0
      nlinarith
    have hAv : v < A := by
      dsimp only [A, v, u, xiSquaredSeamOneRadialA]
      nlinarith [(xi_divisor_support_re_mem_open_unit q.1).1,
        (xi_divisor_support_re_mem_open_unit q.1).2]
    have hA0 : 0 < A := hv0.trans hAv
    have hAvsq : v ^ (2 : ℕ) < A ^ (2 : ℕ) := (sq_lt_sq₀ hv0.le hA0.le).2 hAv
    have hvscaled : 85 * v < v ^ (2 : ℕ) := by
      have hmul := mul_lt_mul_of_pos_right hv hv0
      nlinarith
    have hAB : 85 * B ^ (2 : ℕ) < A ^ (2 : ℕ) := by nlinarith
    rw [xiSquaredSeamOneCoordinate_im_formula,
      xiSquaredSeamOneCoordinate_re_formula]
    change 85 * (B / (A ^ (2 : ℕ) + B ^ (2 : ℕ))) ^ (2 : ℕ) <
      (A / (A ^ (2 : ℕ) + B ^ (2 : ℕ))) ^ (2 : ℕ)
    have hD : 0 < A ^ (2 : ℕ) + B ^ (2 : ℕ) := by
      nlinarith [sq_pos_of_pos hA0, sq_nonneg B]
    field_simp [hD.ne']
    nlinarith

theorem xiSquaredSeamDyadic_rung_zero_pos (q : XiZeroCopy) :
    0 < ((xiSquaredSeamOneCoordinate q) ^ (2 ^ (0 : ℕ))).re := by
  simpa using xiSquaredSeamOneCoordinate_re_pos q

theorem xiSquaredSeamDyadic_rung_one_pos (q : XiZeroCopy) :
    0 < ((xiSquaredSeamOneCoordinate q) ^ (2 ^ (1 : ℕ))).re := by
  norm_num
  exact complex_pow_two_re_pos_of_eightyFive_sector
    (xiSquaredSeamOneCoordinate_eightyFive_sector q)

theorem xiSquaredSeamDyadic_rung_two_pos (q : XiZeroCopy) :
    0 < ((xiSquaredSeamOneCoordinate q) ^ (2 ^ (2 : ℕ))).re := by
  norm_num
  exact complex_pow_four_re_pos_of_eightyFive_sector
    (xiSquaredSeamOneCoordinate_re_pos q)
    (xiSquaredSeamOneCoordinate_eightyFive_sector q)

theorem xiSquaredSeamDyadic_rung_three_pos (q : XiZeroCopy) :
    0 < ((xiSquaredSeamOneCoordinate q) ^ (2 ^ (3 : ℕ))).re := by
  norm_num
  exact complex_pow_eight_re_pos_of_eightyFive_sector
    (xiSquaredSeamOneCoordinate_re_pos q)
    (xiSquaredSeamOneCoordinate_eightyFive_sector q)

/-- Remaining fixed-shift dyadic atom signs beginning at power `32`. -/
def XiSquaredSeamDyadicTailFromFive : Prop :=
  ∀ q : XiZeroCopy, ∀ k : ℕ, 5 ≤ k →
    0 ≤ ((xiSquaredSeamOneCoordinate q) ^ (2 ^ k)).re

/-- The tail beginning at power `32`, together with the unconditional prefix, supplies the
complete dyadic half-plane condition. -/
theorem xiSquaredSeamDyadicHalfPlane_of_tailFromFive
    (h : XiSquaredSeamDyadicTailFromFive) : XiSquaredSeamDyadicHalfPlane := by
  intro q k
  by_cases hk : 5 ≤ k
  · exact h q k hk
  · have hklt : k < 5 := by omega
    interval_cases k
    · exact (xiSquaredSeamDyadic_rung_zero_pos q).le
    · exact (xiSquaredSeamDyadic_rung_one_pos q).le
    · exact (xiSquaredSeamDyadic_rung_two_pos q).le
    · exact (xiSquaredSeamDyadic_rung_three_pos q).le
    · exact (xiSquaredSeamDyadic_rung_four_pos q).le

/-- **Tail-from-32 RH law.**  All lower dyadic rungs are unconditional, so only powers
`32, 64, 128, ...` remain in the criterion. -/
theorem xiSquaredSeamDyadicTailFromFive_iff_riemannHypothesis :
    XiSquaredSeamDyadicTailFromFive ↔ RiemannHypothesis := by
  constructor
  · intro h
    exact riemannHypothesis_of_xiSquaredSeamDyadicHalfPlane
      (xiSquaredSeamDyadicHalfPlane_of_tailFromFive h)
  · intro hRH q k _
    exact xiSquaredSeamDyadicHalfPlane_of_riemannHypothesis hRH q k

end


end RHTower
