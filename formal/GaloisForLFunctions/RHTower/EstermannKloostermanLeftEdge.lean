import GaloisForLFunctions.RHTower.EstermannTwistInversion
import GaloisForLFunctions.RHTower.EstermannLeftEdgeExplicit

/-!
# The Weil saving crosses the critical line

The additive twist average has no cancellation over the reduced residues: on the right edge it is
bounded only by `φ(q)` times the divisor mass.  Its left edge is a different matter.  There the
functional equation replaces it by the inverse twist at `Re s = 2`, where Weil's bound applies to
every Kloosterman coefficient, so the left edge carries `q³·√q` instead of `q³·φ(q)`:

`‖∑_{a} e(ab/p) D(-1+it, a/p)‖ ≤ K p³ √p e^{π|t|}`,  `K = 8 (2π)^{-4} ∑_N d(N)N^{-2}`.

The modulus-aspect cancellation proved by Weil's theorem on one edge of the strip therefore becomes
a saving of `√p` for the divisor function in arithmetic progressions on the other edge.
-/

open Complex

namespace RHTower

noncomputable section

/-- The Weil bound in twist-average notation. -/
theorem norm_estermannInvTwist_le_weil (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) {b : ZMod p}
    (hb : b ≠ 0) {s : ℂ} (hs : 1 < s.re) :
    ‖estermannInvTwist p b s‖ ≤ 2 * Real.sqrt p * divisorMass s.re := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rw [estermannInvTwist]
  exact norm_estermann_invTwist_le_weil p hp2 hb hs

/-- The right edge of the additive twist: `φ(q)` terms, no cancellation. -/
theorem norm_estermannAddTwist_right_edge_le (q : ℕ) [NeZero q] (b : ZMod q) {s : ℂ}
    (hs : 2 ≤ s.re) :
    ‖estermannAddTwist q b s‖ ≤ (Nat.totient q : ℝ) * divisorSquareMass := by
  classical
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ a : (ZMod q)ˣ,
      ‖(ZMod.stdAddChar ((a : ZMod q) * b) : ℂ) * estermannZeta q ((a : ZMod q)) s‖
        ≤ divisorSquareMass := by
    intro a
    rw [norm_mul]
    have h1 : ‖(ZMod.stdAddChar ((a : ZMod q) * b) : ℂ)‖ = 1 := by
      simp
    rw [h1, one_mul]
    exact norm_estermannZeta_le_divisorSquareMass q _ hs
  calc ∑ a : (ZMod q)ˣ, ‖(ZMod.stdAddChar ((a : ZMod q) * b) : ℂ) *
        estermannZeta q ((a : ZMod q)) s‖
      ≤ ∑ _a : (ZMod q)ˣ, divisorSquareMass := Finset.sum_le_sum (fun a _ => hterm a)
    _ = (Nat.totient q : ℝ) * divisorSquareMass := by
        rw [Finset.sum_const, Finset.card_univ, ZMod.card_units_eq_totient, nsmul_eq_mul]

/-- The absolute constant of the saved left edge. -/
def estermannAddTwistLeftEdgeConstant : ℝ :=
  8 * divisorMass 2 * (2 * Real.pi) ^ (-(4 : ℝ))

theorem estermannAddTwistLeftEdgeConstant_nonneg : 0 ≤ estermannAddTwistLeftEdgeConstant := by
  rw [estermannAddTwistLeftEdgeConstant]
  have := divisorMass_nonneg 2
  positivity

/-- **The left edge of the additive twist carries Weil's saving.** -/
theorem norm_estermannAddTwist_left_edge_le (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2)
    {b : ZMod p} (hb : b ≠ 0) (t : ℝ) :
    ‖estermannAddTwist p b (((-1 : ℝ) : ℂ) + (t : ℂ) * I)‖
      ≤ estermannAddTwistLeftEdgeConstant * (p : ℝ) ^ (3 : ℕ) * Real.sqrt p *
          Real.exp (Real.pi * |t|) := by
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
    have hn : (n : ℝ) = -1 := by linarith
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hFE := estermannAddTwist_one_sub p b hne
  rw [hone] at hFE
  rw [hFE]
  have hq1 : (1 : ℝ) ≤ (p : ℝ) := by
    have := Nat.one_le_iff_ne_zero.mpr (NeZero.ne p)
    exact_mod_cast this
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
  have hGamma : ‖Complex.Gamma s ^ (2 : ℕ)‖ ≤ 1 := by
    rw [norm_pow]
    have hg := GaloisForLFunctions.HTGeometry.norm_Gamma_le_Gamma_re (s := s) (by rw [hsre]; norm_num)
    rw [hsre] at hg
    rw [Real.Gamma_two] at hg
    nlinarith [norm_nonneg (Complex.Gamma s), hg]
  have hM0 : (0 : ℝ) ≤ divisorMass 2 := divisorMass_nonneg 2
  have hsq0 : (0 : ℝ) ≤ Real.sqrt p := Real.sqrt_nonneg _
  have hF1 : ‖estermannInvTwist p b s‖ ≤ 2 * Real.sqrt p * divisorMass 2 := by
    have h := norm_estermannInvTwist_le_weil p hp2 hb (s := s) (by rw [hsre]; norm_num)
    rwa [hsre] at h
  have hF2 : ‖estermannInvTwist p (-b) s‖ ≤ 2 * Real.sqrt p * divisorMass 2 := by
    have h := norm_estermannInvTwist_le_weil p hp2 (neg_ne_zero.mpr hb) (s := s)
      (by rw [hsre]; norm_num)
    rwa [hsre] at h
  have hcos : ‖Complex.cos ((Real.pi : ℂ) * s)‖ ≤ Real.exp (Real.pi * |t|) := by
    refine (norm_cos_le_exp_abs_im _).trans ?_
    have him : ((Real.pi : ℂ) * s).im = Real.pi * (-t) := by
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hsre, hsim]
      ring
    rw [him, abs_mul, abs_of_pos Real.pi_pos, abs_neg]
  have hexp1 : (1 : ℝ) ≤ Real.exp (Real.pi * |t|) := Real.one_le_exp (by positivity)
  have hinner : ‖estermannInvTwist p b s
      + Complex.cos ((Real.pi : ℂ) * s) * estermannInvTwist p (-b) s‖
      ≤ 4 * Real.sqrt p * divisorMass 2 * Real.exp (Real.pi * |t|) := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul]
    have hnn : (0 : ℝ) ≤ 2 * Real.sqrt p * divisorMass 2 := by positivity
    have h1 : ‖estermannInvTwist p b s‖
        ≤ 2 * Real.sqrt p * divisorMass 2 * Real.exp (Real.pi * |t|) :=
      hF1.trans (le_mul_of_one_le_right hnn hexp1)
    have h2 : ‖Complex.cos ((Real.pi : ℂ) * s)‖ * ‖estermannInvTwist p (-b) s‖
        ≤ 2 * Real.sqrt p * divisorMass 2 * Real.exp (Real.pi * |t|) := by
      have hmul := mul_le_mul hcos hF2 (norm_nonneg _) (Real.exp_pos _).le
      rw [show Real.exp (Real.pi * |t|) * (2 * Real.sqrt p * divisorMass 2)
          = 2 * Real.sqrt p * divisorMass 2 * Real.exp (Real.pi * |t|) from by ring] at hmul
      exact hmul
    linarith [h1, h2]
  calc ‖2 * (p : ℂ) ^ (2 * s - 1) * (2 * (Real.pi : ℂ)) ^ (-(2 * s)) * Complex.Gamma s ^ (2 : ℕ) *
        (estermannInvTwist p b s
          + Complex.cos ((Real.pi : ℂ) * s) * estermannInvTwist p (-b) s)‖
      = 2 * ‖(p : ℂ) ^ (2 * s - 1)‖ * ‖(2 * (Real.pi : ℂ)) ^ (-(2 * s))‖ *
          ‖Complex.Gamma s ^ (2 : ℕ)‖ *
          ‖estermannInvTwist p b s
            + Complex.cos ((Real.pi : ℂ) * s) * estermannInvTwist p (-b) s‖ := by
        rw [norm_mul, norm_mul, norm_mul, norm_mul]
        simp
    _ ≤ 2 * ((p : ℝ) ^ (3 : ℕ)) * ((2 * Real.pi) ^ (-(4 : ℝ))) * 1 *
          (4 * Real.sqrt p * divisorMass 2 * Real.exp (Real.pi * |t|)) := by
        rw [hqpow, hpipow]
        have hA : (0 : ℝ) ≤ 2 * ((p : ℝ) ^ (3 : ℕ)) * ((2 * Real.pi) ^ (-(4 : ℝ))) := by
          positivity
        have hstep : ‖Complex.Gamma s ^ (2 : ℕ)‖ *
            ‖estermannInvTwist p b s
              + Complex.cos ((Real.pi : ℂ) * s) * estermannInvTwist p (-b) s‖
            ≤ 1 * (4 * Real.sqrt p * divisorMass 2 * Real.exp (Real.pi * |t|)) :=
          mul_le_mul hGamma hinner (norm_nonneg _) zero_le_one
        nlinarith [mul_le_mul_of_nonneg_left hstep hA]
    _ = estermannAddTwistLeftEdgeConstant * (p : ℝ) ^ (3 : ℕ) * Real.sqrt p *
          Real.exp (Real.pi * |t|) := by
        rw [estermannAddTwistLeftEdgeConstant]
        ring

end

end RHTower
