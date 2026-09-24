import GaloisForLFunctions.RHTower.EstermannLeftEdgeExplicit
import GaloisForLFunctions.HTGeometry.GammaVerticalModulus

/-!
# The left edge is polynomial, with the modulus dependence `q³`

`EstermannLeftEdgeExplicit` discards the decay of the Gamma factor and so retains the growth
`e^{π|t|}` of the cosine.  The explicit vertical modulus bound
`‖Γ(2 + it)‖ ≤ √(2π|t|/(1−e^{−2})) · 3|t| · e^{−π|t|/2}` cancels that growth exactly:

`‖Γ(2 + it)‖² · ‖cos(π(2 − it))‖ ≤ (18π/(1−e^{−2})) |t|³`,

leaving a purely polynomial left edge

`‖D(−1 + it, a/q)‖ ≤ K q³ |t|³`  for `|t| ≥ 1`,

with `K` absolute.  Together with the modulus-free right edge this is a pair of `q`-free polynomial
edges for `q^{s−2} D(s)`, the form a Phragmén–Lindelöf interpolation needs in order to produce the
convexity exponent `q^{3/2}` on the critical line.
-/

open Complex

namespace RHTower

noncomputable section

/-- The absolute constant of the polynomial left edge. -/
def estermannLeftEdgePolyConstant : ℝ :=
  4 * divisorSquareMass * (2 * Real.pi) ^ (-(4 : ℝ)) *
    (18 * Real.pi / (1 - Real.exp (-2)))

theorem one_sub_exp_neg_two_pos : (0 : ℝ) < 1 - Real.exp (-2) := by
  have h : Real.exp (-2) < 1 := by
    rw [Real.exp_lt_one_iff]
    norm_num
  linarith

theorem estermannLeftEdgePolyConstant_nonneg : 0 ≤ estermannLeftEdgePolyConstant := by
  rw [estermannLeftEdgePolyConstant]
  have := divisorSquareMass_nonneg
  have := one_sub_exp_neg_two_pos
  positivity

/-- **The polynomial left edge.**  `‖D(−1 + it, a/q)‖ ≤ K q³ |t|³` for `|t| ≥ 1`, `K` absolute. -/
theorem norm_estermannZeta_left_edge_poly_le (q : ℕ) [NeZero q] (a : (ZMod q)ˣ) {t : ℝ}
    (ht : 1 ≤ |t|) :
    ‖estermannZeta q ((a : ZMod q)) (((-1 : ℝ) : ℂ) + (t : ℂ) * I)‖
      ≤ estermannLeftEdgePolyConstant * (q : ℝ) ^ (3 : ℕ) * |t| ^ (3 : ℕ) := by
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
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hFE := estermannZeta_one_sub (q := q) a hne
  rw [hone] at hFE
  rw [hFE]
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
    have := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    exact_mod_cast this
  have hq0 : (0 : ℝ) < (q : ℝ) := by linarith
  have h2s : 2 * s - 1 = ((3 : ℝ) : ℂ) + ((-2 * t : ℝ) : ℂ) * I := by
    rw [hsdef]; push_cast; ring
  have hqpow : ‖(q : ℂ) ^ (2 * s - 1)‖ = (q : ℝ) ^ (3 : ℕ) := by
    rw [h2s, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero (NeZero.ne q))]
    have hre3 : (((3 : ℝ) : ℂ) + ((-2 * t : ℝ) : ℂ) * I).re = 3 := by simp
    rw [hre3, ← Real.rpow_natCast (q : ℝ) 3]
    norm_num
  have hpi0 : (0 : ℝ) < 2 * Real.pi := by positivity
  have hneg2s : -(2 * s) = ((-4 : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * I := by
    rw [hsdef]; push_cast; ring
  have hpipow : ‖(2 * (Real.pi : ℂ)) ^ (-(2 * s))‖ = (2 * Real.pi) ^ (-(4 : ℝ)) := by
    have h2pi : ((2 : ℂ) * (Real.pi : ℂ)) = (((2 * Real.pi : ℝ) : ℝ) : ℂ) := by push_cast; ring
    rw [h2pi, hneg2s, Complex.norm_cpow_eq_rpow_re_of_pos hpi0]
    congr 1
    simp
  -- the explicit Gamma modulus
  have habs : |(-t : ℝ)| = |t| := abs_neg t
  have hGbound := (GaloisForLFunctions.HTGeometry.norm_Gamma_one_add_nat_bounds 1
    (t := -t) (by rwa [habs])).2
  have hGs : Complex.Gamma s = Complex.Gamma (1 + ((-t : ℝ) : ℂ) * I + ((1 : ℕ) : ℂ)) := by
    congr 1
    rw [hsdef]
    push_cast
    ring
  have hA0 : (0 : ℝ) < 1 - Real.exp (-2) := one_sub_exp_neg_two_pos
  have hGnorm : ‖Complex.Gamma s‖
      ≤ Real.sqrt (2 * Real.pi * |t| / (1 - Real.exp (-2))) * (3 * |t|) *
          Real.exp (-(Real.pi * |t| / 2)) := by
    rw [hGs]
    rw [habs] at hGbound
    have hshape : (((2 : ℝ) + (1 : ℕ)) * |t|) ^ (1 : ℕ) = 3 * |t| := by push_cast; ring
    rw [hshape] at hGbound
    exact hGbound
  have ht0 : (0 : ℝ) < |t| := by linarith
  have hGsq : ‖Complex.Gamma s ^ (2 : ℕ)‖
      ≤ (18 * Real.pi / (1 - Real.exp (-2))) * |t| ^ (3 : ℕ) *
          Real.exp (-(Real.pi * |t|)) := by
    rw [norm_pow]
    have hsq : (Real.sqrt (2 * Real.pi * |t| / (1 - Real.exp (-2))) * (3 * |t|) *
        Real.exp (-(Real.pi * |t| / 2))) ^ (2 : ℕ)
        = (2 * Real.pi * |t| / (1 - Real.exp (-2))) * (9 * |t| ^ (2 : ℕ)) *
            Real.exp (-(Real.pi * |t|)) := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), ← Real.exp_nat_mul]
      ring_nf
    have hmono : ‖Complex.Gamma s‖ ^ (2 : ℕ)
        ≤ (Real.sqrt (2 * Real.pi * |t| / (1 - Real.exp (-2))) * (3 * |t|) *
            Real.exp (-(Real.pi * |t| / 2))) ^ (2 : ℕ) := by
      have hnn : (0 : ℝ) ≤ ‖Complex.Gamma s‖ := norm_nonneg _
      nlinarith [hGnorm, hnn]
    refine hmono.trans ?_
    rw [hsq]
    have heq : (2 * Real.pi * |t| / (1 - Real.exp (-2))) * (9 * |t| ^ (2 : ℕ))
        = (18 * Real.pi / (1 - Real.exp (-2))) * |t| ^ (3 : ℕ) := by
      field_simp
      ring
    rw [heq]
  -- the cosine
  have hcos : ‖Complex.cos ((Real.pi : ℂ) * s)‖ ≤ Real.exp (Real.pi * |t|) := by
    refine (norm_cos_le_exp_abs_im _).trans ?_
    have him : ((Real.pi : ℂ) * s).im = Real.pi * (-t) := by
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hsre, hsim]
      ring
    rw [him, abs_mul, abs_of_pos Real.pi_pos, abs_neg]
  have hD1 : ‖estermannZeta q ((a⁻¹ : (ZMod q)ˣ) : ZMod q) s‖ ≤ divisorSquareMass :=
    norm_estermannZeta_le_divisorSquareMass q _ (by rw [hsre])
  have hD2 : ‖estermannZeta q (-((a⁻¹ : (ZMod q)ˣ) : ZMod q)) s‖ ≤ divisorSquareMass :=
    norm_estermannZeta_le_divisorSquareMass q _ (by rw [hsre])
  set A : ℝ := 18 * Real.pi / (1 - Real.exp (-2)) with hAdef
  have hA0' : 0 ≤ A := by rw [hAdef]; positivity
  have hexple : Real.exp (-(Real.pi * |t|)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith [Real.pi_pos, ht0]
  -- the whole Gamma-times-inner factor
  have hkey : ‖Complex.Gamma s ^ (2 : ℕ)‖ *
      ‖estermannZeta q ((a⁻¹ : (ZMod q)ˣ) : ZMod q) s
        + Complex.cos ((Real.pi : ℂ) * s) *
          estermannZeta q (-((a⁻¹ : (ZMod q)ˣ) : ZMod q)) s‖
      ≤ 2 * A * |t| ^ (3 : ℕ) * divisorSquareMass := by
    have hGnn : (0 : ℝ) ≤ ‖Complex.Gamma s ^ (2 : ℕ)‖ := norm_nonneg _
    have hsplit : ‖estermannZeta q ((a⁻¹ : (ZMod q)ˣ) : ZMod q) s
        + Complex.cos ((Real.pi : ℂ) * s) *
          estermannZeta q (-((a⁻¹ : (ZMod q)ˣ) : ZMod q)) s‖
        ≤ divisorSquareMass +
            Real.exp (Real.pi * |t|) * divisorSquareMass := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul]
      have := mul_le_mul hcos hD2 (norm_nonneg _) (Real.exp_pos _).le
      linarith [hD1, this]
    have hGexp : ‖Complex.Gamma s ^ (2 : ℕ)‖ ≤ A * |t| ^ (3 : ℕ) * Real.exp (-(Real.pi * |t|)) := by
      rw [hAdef]; exact hGsq
    have hGplain : ‖Complex.Gamma s ^ (2 : ℕ)‖ ≤ A * |t| ^ (3 : ℕ) := by
      have hpow : (0 : ℝ) ≤ A * |t| ^ (3 : ℕ) := by positivity
      have hstep := mul_le_mul_of_nonneg_left hexple hpow
      linarith [hGexp, hstep]
    have hexpid : Real.exp (-(Real.pi * |t|)) * Real.exp (Real.pi * |t|) = 1 := by
      rw [← Real.exp_add]
      simp
    have hcancel : ‖Complex.Gamma s ^ (2 : ℕ)‖ * (Real.exp (Real.pi * |t|) * divisorSquareMass)
        ≤ A * |t| ^ (3 : ℕ) * divisorSquareMass := by
      have hED : (0 : ℝ) ≤ Real.exp (Real.pi * |t|) * divisorSquareMass := by
        have := divisorSquareMass_nonneg
        positivity
      have h1 := mul_le_mul_of_nonneg_right hGexp hED
      have h2 : (A * |t| ^ (3 : ℕ) * Real.exp (-(Real.pi * |t|))) *
          (Real.exp (Real.pi * |t|) * divisorSquareMass)
          = A * |t| ^ (3 : ℕ) * divisorSquareMass := by
        calc (A * |t| ^ (3 : ℕ) * Real.exp (-(Real.pi * |t|))) *
              (Real.exp (Real.pi * |t|) * divisorSquareMass)
            = A * |t| ^ (3 : ℕ) *
                (Real.exp (-(Real.pi * |t|)) * Real.exp (Real.pi * |t|)) *
                divisorSquareMass := by ring
          _ = A * |t| ^ (3 : ℕ) * divisorSquareMass := by rw [hexpid]; ring
      linarith [h1, h2]
    have hfirst : ‖Complex.Gamma s ^ (2 : ℕ)‖ * divisorSquareMass
        ≤ A * |t| ^ (3 : ℕ) * divisorSquareMass :=
      mul_le_mul_of_nonneg_right hGplain divisorSquareMass_nonneg
    have hmul := mul_le_mul_of_nonneg_left hsplit hGnn
    have hexpand : ‖Complex.Gamma s ^ (2 : ℕ)‖ *
        (divisorSquareMass + Real.exp (Real.pi * |t|) * divisorSquareMass)
        = ‖Complex.Gamma s ^ (2 : ℕ)‖ * divisorSquareMass +
          ‖Complex.Gamma s ^ (2 : ℕ)‖ * (Real.exp (Real.pi * |t|) * divisorSquareMass) := by
      ring
    linarith [hmul, hexpand, hfirst, hcancel]
  calc ‖2 * (q : ℂ) ^ (2 * s - 1) * (2 * (Real.pi : ℂ)) ^ (-(2 * s)) * Complex.Gamma s ^ (2 : ℕ) *
        (estermannZeta q ((a⁻¹ : (ZMod q)ˣ) : ZMod q) s
          + Complex.cos ((Real.pi : ℂ) * s) *
            estermannZeta q (-((a⁻¹ : (ZMod q)ˣ) : ZMod q)) s)‖
      = 2 * ((q : ℝ) ^ (3 : ℕ)) * ((2 * Real.pi) ^ (-(4 : ℝ))) *
          (‖Complex.Gamma s ^ (2 : ℕ)‖ *
            ‖estermannZeta q ((a⁻¹ : (ZMod q)ˣ) : ZMod q) s
              + Complex.cos ((Real.pi : ℂ) * s) *
                estermannZeta q (-((a⁻¹ : (ZMod q)ˣ) : ZMod q)) s‖) := by
        rw [norm_mul, norm_mul, norm_mul, norm_mul, hqpow, hpipow]
        simp
        ring
    _ ≤ 2 * ((q : ℝ) ^ (3 : ℕ)) * ((2 * Real.pi) ^ (-(4 : ℝ))) *
          (2 * A * |t| ^ (3 : ℕ) * divisorSquareMass) := by
        have hfac : (0 : ℝ) ≤ 2 * ((q : ℝ) ^ (3 : ℕ)) * ((2 * Real.pi) ^ (-(4 : ℝ))) := by
          positivity
        exact mul_le_mul_of_nonneg_left hkey hfac
    _ = estermannLeftEdgePolyConstant * (q : ℝ) ^ (3 : ℕ) * |t| ^ (3 : ℕ) := by
        rw [estermannLeftEdgePolyConstant, hAdef]
        ring

end

end RHTower
