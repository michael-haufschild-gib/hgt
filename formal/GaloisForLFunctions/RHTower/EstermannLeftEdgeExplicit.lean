import GaloisForLFunctions.RHTower.EstermannRightEdgeExplicit
import GaloisForLFunctions.RHTower.ZetaVerticalStripPolynomialBound
import GaloisForLFunctions.HTGeometry.GammaReciprocalExpBound

/-!
# The left edge of the Estermann strip, explicit in the modulus

The functional equation

`D(1−s, a/q) = 2 q^{2s−1} (2π)^{−2s} Γ(s)² (D(s, ā/q) + cos(πs) D(s, −ā/q))`

evaluated on `Re s = 2` has every factor explicitly controlled: `‖q^{2s−1}‖ = q³`,
`‖(2π)^{−2s}‖ = (2π)^{−4}`, `‖Γ(s)‖ ≤ Γ(2) = 1`, `‖cos(πs)‖ ≤ e^{π|Im s|}`, and both Estermann
values on the right edge are bounded by the modulus-free constant `∑_N d(N)/N²`.  Hence

`‖D(−1 + it, a/q)‖ ≤ 4 (2π)^{−4} (∑_N d(N)/N²) · q³ · e^{π|t|}`,

with an absolute constant.  This is the `q`-dependent edge of the convexity argument: together with
the modulus-free right edge it isolates `q³` as the entire modulus dependence to be interpolated.
-/

open Complex

namespace RHTower

noncomputable section

/-- The absolute constant of the left edge. -/
def estermannLeftEdgeConstant : ℝ := 4 * divisorSquareMass * (2 * Real.pi) ^ (-(4 : ℝ))

theorem estermannLeftEdgeConstant_nonneg : 0 ≤ estermannLeftEdgeConstant := by
  rw [estermannLeftEdgeConstant]
  have := divisorSquareMass_nonneg
  positivity

/-- **The left edge, explicit in the modulus.**  `‖D(−1 + it, a/q)‖ ≤ K q³ e^{π|t|}` with `K`
absolute. -/
theorem norm_estermannZeta_left_edge_le (q : ℕ) [NeZero q] (a : (ZMod q)ˣ) (t : ℝ) :
    ‖estermannZeta q ((a : ZMod q)) (((-1 : ℝ) : ℂ) + (t : ℂ) * I)‖
      ≤ estermannLeftEdgeConstant * (q : ℝ) ^ (3 : ℕ) * Real.exp (Real.pi * |t|) := by
  set s : ℂ := ((2 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I with hsdef
  have hsre : s.re = 2 := by rw [hsdef]; simp
  have hsim : s.im = -t := by rw [hsdef]; simp
  have hone : (1 : ℂ) - s = ((-1 : ℝ) : ℂ) + (t : ℂ) * I := by
    rw [hsdef]; push_cast; ring
  have hne : ∀ n : ℕ, s ≠ 1 - (n : ℂ) := by
    intro n hcon
    have hc := congrArg Complex.re hcon
    rw [hsre] at hc
    simp only [Complex.sub_re, Complex.one_re, Complex.natCast_re] at hc
    have : (n : ℝ) = -1 := by linarith
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hFE := estermannZeta_one_sub (q := q) a hne
  rw [hone] at hFE
  rw [hFE]
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
    have := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    exact_mod_cast this
  have hq0 : (0 : ℝ) < (q : ℝ) := by linarith
  -- the modulus power
  have h2s : 2 * s - 1 = ((3 : ℝ) : ℂ) + ((-2 * t : ℝ) : ℂ) * I := by
    rw [hsdef]; push_cast; ring
  have hqpow : ‖(q : ℂ) ^ (2 * s - 1)‖ = (q : ℝ) ^ (3 : ℕ) := by
    rw [h2s, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero (NeZero.ne q))]
    have hre3 : (((3 : ℝ) : ℂ) + ((-2 * t : ℝ) : ℂ) * I).re = 3 := by simp
    rw [hre3, ← Real.rpow_natCast (q : ℝ) 3]
    norm_num
  -- the archimedean power
  have hpi0 : (0 : ℝ) < 2 * Real.pi := by positivity
  have hneg2s : -(2 * s) = ((-4 : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * I := by
    rw [hsdef]; push_cast; ring
  have hpipow : ‖(2 * (Real.pi : ℂ)) ^ (-(2 * s))‖ = (2 * Real.pi) ^ (-(4 : ℝ)) := by
    have h2pi : ((2 : ℂ) * (Real.pi : ℂ)) = (((2 * Real.pi : ℝ) : ℝ) : ℂ) := by push_cast; ring
    rw [h2pi, hneg2s, Complex.norm_cpow_eq_rpow_re_of_pos hpi0]
    congr 1
    simp
  -- the Gamma factor
  have hGamma : ‖Complex.Gamma s ^ (2 : ℕ)‖ ≤ 1 := by
    rw [norm_pow]
    have hg := GaloisForLFunctions.HTGeometry.norm_Gamma_le_Gamma_re (s := s) (by rw [hsre]; norm_num)
    rw [hsre] at hg
    have hg2 : Real.Gamma 2 = 1 := Real.Gamma_two
    rw [hg2] at hg
    nlinarith [norm_nonneg (Complex.Gamma s), hg]
  -- the two Estermann values on the right edge
  have hD1 : ‖estermannZeta q ((a⁻¹ : (ZMod q)ˣ) : ZMod q) s‖ ≤ divisorSquareMass :=
    norm_estermannZeta_le_divisorSquareMass q _ (by rw [hsre])
  have hD2 : ‖estermannZeta q (-((a⁻¹ : (ZMod q)ˣ) : ZMod q)) s‖ ≤ divisorSquareMass :=
    norm_estermannZeta_le_divisorSquareMass q _ (by rw [hsre])
  have hcos : ‖Complex.cos ((Real.pi : ℂ) * s)‖ ≤ Real.exp (Real.pi * |t|) := by
    refine (norm_cos_le_exp_abs_im _).trans ?_
    have him : ((Real.pi : ℂ) * s).im = Real.pi * (-t) := by
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hsre, hsim]
      ring
    rw [him, abs_mul, abs_of_pos Real.pi_pos, abs_neg]
  -- assemble
  have hexp1 : (1 : ℝ) ≤ Real.exp (Real.pi * |t|) :=
    Real.one_le_exp (by positivity)
  have hinner : ‖estermannZeta q ((a⁻¹ : (ZMod q)ˣ) : ZMod q) s
      + Complex.cos ((Real.pi : ℂ) * s) * estermannZeta q (-((a⁻¹ : (ZMod q)ˣ) : ZMod q)) s‖
      ≤ 2 * divisorSquareMass * Real.exp (Real.pi * |t|) := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul]
    have h1 : ‖estermannZeta q ((a⁻¹ : (ZMod q)ˣ) : ZMod q) s‖
        ≤ divisorSquareMass * Real.exp (Real.pi * |t|) := by
      nlinarith [hD1, divisorSquareMass_nonneg, hexp1]
    have h2 : ‖Complex.cos ((Real.pi : ℂ) * s)‖ *
        ‖estermannZeta q (-((a⁻¹ : (ZMod q)ˣ) : ZMod q)) s‖
        ≤ Real.exp (Real.pi * |t|) * divisorSquareMass :=
      mul_le_mul hcos hD2 (norm_nonneg _) (Real.exp_pos _).le
    nlinarith [h1, h2]
  calc ‖2 * (q : ℂ) ^ (2 * s - 1) * (2 * (Real.pi : ℂ)) ^ (-(2 * s)) * Complex.Gamma s ^ (2 : ℕ) *
        (estermannZeta q ((a⁻¹ : (ZMod q)ˣ) : ZMod q) s
          + Complex.cos ((Real.pi : ℂ) * s) *
            estermannZeta q (-((a⁻¹ : (ZMod q)ˣ) : ZMod q)) s)‖
      = 2 * ‖(q : ℂ) ^ (2 * s - 1)‖ * ‖(2 * (Real.pi : ℂ)) ^ (-(2 * s))‖ *
          ‖Complex.Gamma s ^ (2 : ℕ)‖ *
          ‖estermannZeta q ((a⁻¹ : (ZMod q)ˣ) : ZMod q) s
            + Complex.cos ((Real.pi : ℂ) * s) *
              estermannZeta q (-((a⁻¹ : (ZMod q)ˣ) : ZMod q)) s‖ := by
        rw [norm_mul, norm_mul, norm_mul, norm_mul]
        simp
    _ ≤ 2 * ((q : ℝ) ^ (3 : ℕ)) * ((2 * Real.pi) ^ (-(4 : ℝ))) * 1 *
          (2 * divisorSquareMass * Real.exp (Real.pi * |t|)) := by
        rw [hqpow, hpipow]
        have hA : (0 : ℝ) ≤ 2 * ((q : ℝ) ^ (3 : ℕ)) * ((2 * Real.pi) ^ (-(4 : ℝ))) := by
          positivity
        have hstep : ‖Complex.Gamma s ^ (2 : ℕ)‖ *
            ‖estermannZeta q ((a⁻¹ : (ZMod q)ˣ) : ZMod q) s
              + Complex.cos ((Real.pi : ℂ) * s) *
                estermannZeta q (-((a⁻¹ : (ZMod q)ˣ) : ZMod q)) s‖
            ≤ 1 * (2 * divisorSquareMass * Real.exp (Real.pi * |t|)) :=
          mul_le_mul hGamma hinner (norm_nonneg _) zero_le_one
        nlinarith [mul_le_mul_of_nonneg_left hstep hA]
    _ = estermannLeftEdgeConstant * (q : ℝ) ^ (3 : ℕ) * Real.exp (Real.pi * |t|) := by
        rw [estermannLeftEdgeConstant]
        ring

end

end RHTower
