import GaloisForLFunctions.RHTower.EstermannKloostermanLeftEdge
import GaloisForLFunctions.RHTower.EstermannLeftEdgePolynomial

/-!
# The saved left edge is polynomial

The explicit vertical modulus bound for the Gamma factor cancels the growth of the cosine exactly,
so the Weil-saved left edge of the additive twist is polynomial in the height:

`‖∑_a e(ab/p) D(-1+it, a/p)‖ ≤ K p³ √p |t|³`  for `|t| ≥ 1`,

with `K` absolute.  This is the `q`-free polynomial edge that a Phragmén–Lindelöf interpolation
needs, now carrying `p³√p` where the per-residue estimate carries `p³φ(p)`.
-/

open Complex

namespace RHTower

noncomputable section

/-- The absolute constant of the saved polynomial left edge. -/
def estermannAddTwistLeftEdgePolyConstant : ℝ :=
  8 * divisorMass 2 * (2 * Real.pi) ^ (-(4 : ℝ)) *
    (18 * Real.pi / (1 - Real.exp (-2)))

theorem estermannAddTwistLeftEdgePolyConstant_nonneg :
    0 ≤ estermannAddTwistLeftEdgePolyConstant := by
  rw [estermannAddTwistLeftEdgePolyConstant]
  have h1 := divisorMass_nonneg 2
  have h2 := one_sub_exp_neg_two_pos
  positivity

/-- **The polynomial left edge with the Weil saving.** -/
theorem norm_estermannAddTwist_left_edge_poly_le (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2)
    {b : ZMod p} (hb : b ≠ 0) {t : ℝ} (ht : 1 ≤ |t|) :
    ‖estermannAddTwist p b (((-1 : ℝ) : ℂ) + (t : ℂ) * I)‖
      ≤ estermannAddTwistLeftEdgePolyConstant * (p : ℝ) ^ (3 : ℕ) * Real.sqrt p *
          |t| ^ (3 : ℕ) := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
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
  have hFE := estermannAddTwist_one_sub p b hne
  rw [hone] at hFE
  rw [hFE]
  have hq1 : (1 : ℝ) ≤ (p : ℝ) := by
    have := Nat.one_le_iff_ne_zero.mpr (NeZero.ne p)
    exact_mod_cast this
  have hq0 : (0 : ℝ) < (p : ℝ) := by linarith
  have h2s : 2 * s - 1 = ((3 : ℝ) : ℂ) + ((-2 * t : ℝ) : ℂ) * I := by
    rw [hsdef]; push_cast; ring
  have hqpow : ‖(p : ℂ) ^ (2 * s - 1)‖ = (p : ℝ) ^ (3 : ℕ) := by
    rw [h2s, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero (NeZero.ne p))]
    have hre3 : (((3 : ℝ) : ℂ) + ((-2 * t : ℝ) : ℂ) * I).re = 3 := by simp
    rw [hre3, ← Real.rpow_natCast (p : ℝ) 3]
    norm_num
  have hpi0 : (0 : ℝ) < 2 * Real.pi := by positivity
  have hneg2s : -(2 * s) = ((-4 : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * I := by
    rw [hsdef]; push_cast; ring
  have hpipow : ‖(2 * (Real.pi : ℂ)) ^ (-(2 * s))‖ = (2 * Real.pi) ^ (-(4 : ℝ)) := by
    have h2pi : ((2 : ℂ) * (Real.pi : ℂ)) = (((2 * Real.pi : ℝ) : ℝ) : ℂ) := by push_cast; ring
    rw [h2pi, hneg2s, Complex.norm_cpow_eq_rpow_re_of_pos hpi0]
    congr 1
    simp
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
  have hcos : ‖Complex.cos ((Real.pi : ℂ) * s)‖ ≤ Real.exp (Real.pi * |t|) := by
    refine (norm_cos_le_exp_abs_im _).trans ?_
    have him : ((Real.pi : ℂ) * s).im = Real.pi * (-t) := by
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hsre, hsim]
      ring
    rw [him, abs_mul, abs_of_pos Real.pi_pos, abs_neg]
  set B : ℝ := 2 * Real.sqrt p * divisorMass 2 with hBdef
  have hB0 : (0 : ℝ) ≤ B := by
    rw [hBdef]
    have := divisorMass_nonneg 2
    positivity
  have hD1 : ‖estermannInvTwist p b s‖ ≤ B := by
    have h := norm_estermannInvTwist_le_weil p hp2 hb (s := s) (by rw [hsre]; norm_num)
    rwa [hsre] at h
  have hD2 : ‖estermannInvTwist p (-b) s‖ ≤ B := by
    have h := norm_estermannInvTwist_le_weil p hp2 (neg_ne_zero.mpr hb) (s := s)
      (by rw [hsre]; norm_num)
    rwa [hsre] at h
  set A : ℝ := 18 * Real.pi / (1 - Real.exp (-2)) with hAdef
  have hA0' : 0 ≤ A := by rw [hAdef]; positivity
  have hexple : Real.exp (-(Real.pi * |t|)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith [Real.pi_pos, ht0]
  have hkey : ‖Complex.Gamma s ^ (2 : ℕ)‖ *
      ‖estermannInvTwist p b s
        + Complex.cos ((Real.pi : ℂ) * s) * estermannInvTwist p (-b) s‖
      ≤ 2 * A * |t| ^ (3 : ℕ) * B := by
    have hGnn : (0 : ℝ) ≤ ‖Complex.Gamma s ^ (2 : ℕ)‖ := norm_nonneg _
    have hsplit : ‖estermannInvTwist p b s
        + Complex.cos ((Real.pi : ℂ) * s) * estermannInvTwist p (-b) s‖
        ≤ B + Real.exp (Real.pi * |t|) * B := by
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
    have hcancel : ‖Complex.Gamma s ^ (2 : ℕ)‖ * (Real.exp (Real.pi * |t|) * B)
        ≤ A * |t| ^ (3 : ℕ) * B := by
      have hED : (0 : ℝ) ≤ Real.exp (Real.pi * |t|) * B := by positivity
      have h1 := mul_le_mul_of_nonneg_right hGexp hED
      have h2 : (A * |t| ^ (3 : ℕ) * Real.exp (-(Real.pi * |t|))) *
          (Real.exp (Real.pi * |t|) * B) = A * |t| ^ (3 : ℕ) * B := by
        calc (A * |t| ^ (3 : ℕ) * Real.exp (-(Real.pi * |t|))) *
              (Real.exp (Real.pi * |t|) * B)
            = A * |t| ^ (3 : ℕ) *
                (Real.exp (-(Real.pi * |t|)) * Real.exp (Real.pi * |t|)) * B := by ring
          _ = A * |t| ^ (3 : ℕ) * B := by rw [hexpid]; ring
      linarith [h1, h2]
    have hfirst : ‖Complex.Gamma s ^ (2 : ℕ)‖ * B ≤ A * |t| ^ (3 : ℕ) * B :=
      mul_le_mul_of_nonneg_right hGplain hB0
    have hmul := mul_le_mul_of_nonneg_left hsplit hGnn
    have hexpand : ‖Complex.Gamma s ^ (2 : ℕ)‖ * (B + Real.exp (Real.pi * |t|) * B)
        = ‖Complex.Gamma s ^ (2 : ℕ)‖ * B +
          ‖Complex.Gamma s ^ (2 : ℕ)‖ * (Real.exp (Real.pi * |t|) * B) := by ring
    linarith [hmul, hexpand, hfirst, hcancel]
  calc ‖2 * (p : ℂ) ^ (2 * s - 1) * (2 * (Real.pi : ℂ)) ^ (-(2 * s)) * Complex.Gamma s ^ (2 : ℕ) *
        (estermannInvTwist p b s
          + Complex.cos ((Real.pi : ℂ) * s) * estermannInvTwist p (-b) s)‖
      = 2 * ‖(p : ℂ) ^ (2 * s - 1)‖ * ‖(2 * (Real.pi : ℂ)) ^ (-(2 * s))‖ *
          ‖Complex.Gamma s ^ (2 : ℕ)‖ *
          ‖estermannInvTwist p b s
            + Complex.cos ((Real.pi : ℂ) * s) * estermannInvTwist p (-b) s‖ := by
        rw [norm_mul, norm_mul, norm_mul, norm_mul]
        simp
    _ = 2 * ((p : ℝ) ^ (3 : ℕ)) * ((2 * Real.pi) ^ (-(4 : ℝ))) *
          (‖Complex.Gamma s ^ (2 : ℕ)‖ *
            ‖estermannInvTwist p b s
              + Complex.cos ((Real.pi : ℂ) * s) * estermannInvTwist p (-b) s‖) := by
        rw [hqpow, hpipow]
        ring
    _ ≤ 2 * ((p : ℝ) ^ (3 : ℕ)) * ((2 * Real.pi) ^ (-(4 : ℝ))) * (2 * A * |t| ^ (3 : ℕ) * B) := by
        have hA : (0 : ℝ) ≤ 2 * ((p : ℝ) ^ (3 : ℕ)) * ((2 * Real.pi) ^ (-(4 : ℝ))) := by
          positivity
        exact mul_le_mul_of_nonneg_left hkey hA
    _ = estermannAddTwistLeftEdgePolyConstant * (p : ℝ) ^ (3 : ℕ) * Real.sqrt p *
          |t| ^ (3 : ℕ) := by
        rw [estermannAddTwistLeftEdgePolyConstant, hAdef, hBdef]
        ring

end

end RHTower
