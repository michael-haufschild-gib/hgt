import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Exact cross-prime Gram law for the CCM Hardy pole vectors

This module formalizes the local-factor Hardy vectors used in the
Connes--Consani--Moscovici semilocal construction. It computes their
cross-scale Gram kernel exactly and identifies the normalized kernel with the
Laplace inner product of exponentially damped prime-clock characters.

The theorem is unconditional: the scales are arbitrary positive real numbers.
For prime scales one substitutes L = log p.
-/

open scoped BigOperators ComplexConjugate
open MeasureTheory Set

noncomputable section

namespace RHTower

def ccmPrimePolePoint (L : ℝ) (n : ℤ) : ℂ :=
  ((((4 * Real.pi * (n : ℝ) : ℝ) : ℂ) - Complex.I * L) /
    (((4 * Real.pi * (n : ℝ) : ℝ) : ℂ) + 3 * Complex.I * L))

def ccmPrimePoleCoefficient (L : ℝ) (n : ℤ) : ℂ :=
  ((2 * Real.sqrt 2 * Real.sqrt L : ℝ) : ℂ) /
    (((4 * Real.pi * (n : ℝ) : ℝ) : ℂ) + 3 * Complex.I * L)

def ccmPrimePoleSequence (L : ℝ) (n : ℤ) (k : ℕ) : ℂ :=
  ccmPrimePoleCoefficient L n * ccmPrimePolePoint L n ^ k

lemma ccmPrimePolePoint_norm_lt_one {L : ℝ} (hL : 0 < L) (n : ℤ) :
    ‖ccmPrimePolePoint L n‖ < 1 := by
  rw [ccmPrimePolePoint, Complex.norm_div]
  rw [div_lt_one]
  · rw [← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)]
    simp only [Complex.sq_norm, Complex.normSq_apply]
    simp
    nlinarith [sq_pos_of_pos hL]
  · rw [norm_pos_iff]
    intro h
    have him := congrArg Complex.im h
    simp at him
    linarith

lemma ccmPrimePolePoint_cross_norm_lt_one {Lp Lq : ℝ} (hp : 0 < Lp) (hq : 0 < Lq)
    (n r : ℤ) :
    ‖star (ccmPrimePolePoint Lq r) * ccmPrimePolePoint Lp n‖ < 1 := by
  rw [norm_mul, norm_star]
  have hq' := ccmPrimePolePoint_norm_lt_one hq r
  have hp' := ccmPrimePolePoint_norm_lt_one hp n
  have hqn := norm_nonneg (ccmPrimePolePoint Lq r)
  have hpn := norm_nonneg (ccmPrimePolePoint Lp n)
  nlinarith [mul_pos (sub_pos.mpr hq') (sub_pos.mpr hp')]

lemma ccmPrimePoleSequence_cross_tsum_raw {Lp Lq : ℝ} (hp : 0 < Lp) (hq : 0 < Lq)
    (n r : ℤ) :
    (∑' k : ℕ, star (ccmPrimePoleSequence Lq r k) * ccmPrimePoleSequence Lp n k) =
      star (ccmPrimePoleCoefficient Lq r) * ccmPrimePoleCoefficient Lp n *
        (1 - star (ccmPrimePolePoint Lq r) * ccmPrimePolePoint Lp n)⁻¹ := by
  have hs := ccmPrimePolePoint_cross_norm_lt_one hp hq n r
  calc
    (∑' k : ℕ, star (ccmPrimePoleSequence Lq r k) * ccmPrimePoleSequence Lp n k) =
        ∑' k : ℕ, (star (ccmPrimePoleCoefficient Lq r) * ccmPrimePoleCoefficient Lp n) *
          (star (ccmPrimePolePoint Lq r) * ccmPrimePolePoint Lp n) ^ k := by
            apply tsum_congr
            intro k
            simp only [ccmPrimePoleSequence, star_mul', star_pow]
            rw [mul_pow]
            ring
    _ = (star (ccmPrimePoleCoefficient Lq r) * ccmPrimePoleCoefficient Lp n) *
        ∑' k : ℕ, (star (ccmPrimePolePoint Lq r) * ccmPrimePolePoint Lp n) ^ k := by
          rw [tsum_mul_left]
    _ = _ := by rw [tsum_geometric_of_norm_lt_one hs]

lemma ccmPrimePoleDenominator_ne {L : ℝ} (hL : 0 < L) (n : ℤ) :
    (((4 * Real.pi * (n : ℝ) : ℝ) : ℂ) + 3 * Complex.I * L) ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  simp at him
  linarith

lemma ccmPrimePoleConjugateDenominator_ne {L : ℝ} (hL : 0 < L) (n : ℤ) :
    (((4 * Real.pi * (n : ℝ) : ℝ) : ℂ) - 3 * Complex.I * L) ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  simp at him
  linarith

lemma ccm_one_sub_div_mul_div {a b c d : ℂ} (hb : b ≠ 0) (hd : d ≠ 0) :
    1 - (a / b) * (c / d) = (b * d - a * c) / (b * d) := by
  field_simp

lemma one_sub_star_ccmPrimePolePoint_mul {Lp Lq : ℝ} (hp : 0 < Lp) (hq : 0 < Lq)
    (n r : ℤ) :
    1 - star (ccmPrimePolePoint Lq r) * ccmPrimePolePoint Lp n =
      8 * ((Lp * Lq : ℝ) + 2 * Real.pi * Complex.I *
        ((r : ℝ) * Lp - (n : ℝ) * Lq)) /
      ((((4 * Real.pi * (r : ℝ) : ℝ) : ℂ) - 3 * Complex.I * Lq) *
        (((4 * Real.pi * (n : ℝ) : ℝ) : ℂ) + 3 * Complex.I * Lp)) := by
  have hstar : star (ccmPrimePolePoint Lq r) =
      ((((4 * Real.pi * (r : ℝ) : ℝ) : ℂ) + Complex.I * Lq) /
        (((4 * Real.pi * (r : ℝ) : ℝ) : ℂ) - 3 * Complex.I * Lq)) := by
    simp only [ccmPrimePolePoint, RCLike.star_def, map_div₀, map_sub, map_add, map_mul,
      Complex.conj_ofReal, Complex.conj_I, map_ofNat]
    ring
  rw [hstar, ccmPrimePolePoint]
  rw [ccm_one_sub_div_mul_div (ccmPrimePoleConjugateDenominator_ne hq r) (ccmPrimePoleDenominator_ne hp n)]
  apply congrArg (fun z : ℂ => z /
    ((((4 * Real.pi * (r : ℝ) : ℝ) : ℂ) - 3 * Complex.I * Lq) *
      (((4 * Real.pi * (n : ℝ) : ℝ) : ℂ) + 3 * Complex.I * Lp)))
  push_cast
  ring_nf
  rw [show Complex.I ^ 2 = (-1 : ℂ) by norm_num]
  ring

lemma star_ccmPrimePoleCoefficient_mul {Lp Lq : ℝ} (n r : ℤ) :
    star (ccmPrimePoleCoefficient Lq r) * ccmPrimePoleCoefficient Lp n =
      (8 * (Real.sqrt Lq * Real.sqrt Lp : ℝ) : ℂ) /
      ((((4 * Real.pi * (r : ℝ) : ℝ) : ℂ) - 3 * Complex.I * Lq) *
        (((4 * Real.pi * (n : ℝ) : ℝ) : ℂ) + 3 * Complex.I * Lp)) := by
  have hstar : star (ccmPrimePoleCoefficient Lq r) =
      ((2 * Real.sqrt 2 * Real.sqrt Lq : ℝ) : ℂ) /
        (((4 * Real.pi * (r : ℝ) : ℝ) : ℂ) - 3 * Complex.I * Lq) := by
    rw [ccmPrimePoleCoefficient, star_div₀]
    simp only [RCLike.star_def, Complex.conj_ofReal, map_add, map_mul,
      Complex.conj_I, map_ofNat]
    ring
  rw [hstar, ccmPrimePoleCoefficient, div_mul_div_comm]
  apply congrArg (fun z : ℂ => z /
    ((((4 * Real.pi * (r : ℝ) : ℝ) : ℂ) - 3 * Complex.I * Lq) *
      (((4 * Real.pi * (n : ℝ) : ℝ) : ℂ) + 3 * Complex.I * Lp)))
  norm_cast
  calc
    2 * Real.sqrt 2 * Real.sqrt Lq * (2 * Real.sqrt 2 * Real.sqrt Lp) =
        4 * (Real.sqrt 2) ^ 2 * (Real.sqrt Lq * Real.sqrt Lp) := by ring
    _ = 8 * (Real.sqrt Lq * Real.sqrt Lp) := by
      rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      ring

lemma ccm_scaled_div_mul_inv_scaled_div {s C D : ℂ} (hC : C ≠ 0) (hD : D ≠ 0) :
    (8 * s / D) * (8 * C / D)⁻¹ = s / C := by
  field_simp

lemma ccmPrimePoleCrossDenominator_ne {Lp Lq : ℝ} (hp : 0 < Lp) (hq : 0 < Lq)
    (n r : ℤ) :
    ((Lp * Lq : ℝ) + 2 * Real.pi * Complex.I *
      ((r : ℝ) * Lp - (n : ℝ) * Lq)) ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  simp at hre
  rcases hre with hp0 | hq0
  · exact hp.ne' hp0
  · exact hq.ne' hq0

theorem ccmPrimePoleSequence_cross_tsum {Lp Lq : ℝ} (hp : 0 < Lp) (hq : 0 < Lq)
    (n r : ℤ) :
    (∑' k : ℕ, star (ccmPrimePoleSequence Lq r k) * ccmPrimePoleSequence Lp n k) =
      (Real.sqrt (Lp * Lq) : ℂ) /
        ((Lp * Lq : ℝ) + 2 * Real.pi * Complex.I * ((r : ℝ) * Lp - (n : ℝ) * Lq)) := by
  rw [ccmPrimePoleSequence_cross_tsum_raw hp hq]
  rw [star_ccmPrimePoleCoefficient_mul, one_sub_star_ccmPrimePolePoint_mul hp hq]
  have hsqrt : Real.sqrt Lq * Real.sqrt Lp = Real.sqrt (Lp * Lq) := by
    rw [mul_comm Lp Lq, Real.sqrt_mul hq.le]
  rw [hsqrt]
  exact ccm_scaled_div_mul_inv_scaled_div
    (ccmPrimePoleCrossDenominator_ne hp hq n r)
    (mul_ne_zero (ccmPrimePoleConjugateDenominator_ne hq r) (ccmPrimePoleDenominator_ne hp n))

def ccmNormalizedPrimePoleSequence (L : ℝ) (n : ℤ) (k : ℕ) : ℂ :=
  (Real.sqrt L : ℂ) * ccmPrimePoleSequence L n k

theorem ccmNormalizedPrimePoleSequence_cross_tsum {Lp Lq : ℝ} (hp : 0 < Lp) (hq : 0 < Lq)
    (n r : ℤ) :
    (∑' k : ℕ, star (ccmNormalizedPrimePoleSequence Lq r k) * ccmNormalizedPrimePoleSequence Lp n k) =
      1 / (1 + 2 * Real.pi * Complex.I *
        ((r : ℝ) / Lq - (n : ℝ) / Lp)) := by
  calc
    (∑' k : ℕ, star (ccmNormalizedPrimePoleSequence Lq r k) * ccmNormalizedPrimePoleSequence Lp n k) =
        ∑' k : ℕ, ((Real.sqrt Lq * Real.sqrt Lp : ℝ) : ℂ) *
          (star (ccmPrimePoleSequence Lq r k) * ccmPrimePoleSequence Lp n k) := by
      apply tsum_congr
      intro k
      simp only [ccmNormalizedPrimePoleSequence, star_mul', RCLike.star_def, Complex.conj_ofReal,
        Complex.ofReal_mul]
      ac_rfl
    _ = ((Real.sqrt Lq * Real.sqrt Lp : ℝ) : ℂ) *
          ∑' k : ℕ, star (ccmPrimePoleSequence Lq r k) * ccmPrimePoleSequence Lp n k := by
      rw [tsum_mul_left]
    _ = ((Real.sqrt Lq * Real.sqrt Lp : ℝ) : ℂ) *
        ((Real.sqrt (Lp * Lq) : ℂ) /
          ((Lp * Lq : ℝ) + 2 * Real.pi * Complex.I *
            ((r : ℝ) * Lp - (n : ℝ) * Lq))) := by
      rw [ccmPrimePoleSequence_cross_tsum hp hq]
    _ = _ := by
      have hsqrt : Real.sqrt Lq * Real.sqrt Lp = Real.sqrt (Lp * Lq) := by
        rw [mul_comm Lp Lq, Real.sqrt_mul hq.le]
      rw [hsqrt]
      have hsqC : (Real.sqrt (Lp * Lq) : ℂ) * Real.sqrt (Lp * Lq) =
          (Lp * Lq : ℝ) := by
        norm_cast
        exact Real.mul_self_sqrt (mul_nonneg hp.le hq.le)
      rw [← mul_div_assoc, hsqC]
      have hD : ((Lp * Lq : ℝ) + 2 * Real.pi * Complex.I *
          ((r : ℝ) * Lp - (n : ℝ) * Lq) : ℂ) ≠ 0 :=
        ccmPrimePoleCrossDenominator_ne hp hq n r
      have hE : (1 + 2 * Real.pi * Complex.I *
          ((r : ℝ) / Lq - (n : ℝ) / Lp) : ℂ) ≠ 0 := by
        intro hzero
        have hre := congrArg Complex.re hzero
        norm_num at hre
      apply (div_eq_div_iff hD hE).2
      have hp0 : (Lp : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hp.ne'
      have hq0 : (Lq : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq.ne'
      field_simp [hp0, hq0]
      rw [Complex.ofReal_mul]
      ring

def ccmDampedLaplaceCharacter (L : ℝ) (n : ℤ) (t : ℝ) : ℂ :=
  Complex.exp ((-1 / 2 : ℂ) * t) *
    Complex.exp (Complex.I * (2 * Real.pi * (n : ℝ) / L) * t)

lemma star_ccmDampedLaplaceCharacter_mul
    (Lp Lq : ℝ) (n r : ℤ) (t : ℝ) :
    star (ccmDampedLaplaceCharacter Lq r t) * ccmDampedLaplaceCharacter Lp n t =
      Complex.exp
        ((-1 + Complex.I *
          (2 * Real.pi * ((n : ℝ) / Lp - (r : ℝ) / Lq)) : ℂ) * t) := by
  change conj (ccmDampedLaplaceCharacter Lq r t) * ccmDampedLaplaceCharacter Lp n t = _
  simp only [ccmDampedLaplaceCharacter, map_mul]
  rw [← Complex.exp_conj, ← Complex.exp_conj]
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_div₀,
    map_neg, map_ofNat, map_one]
  rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem ccmDampedLaplaceCharacter_inner_integral (Lp Lq : ℝ) (n r : ℤ) :
    ∫ t : ℝ in Ioi 0, star (ccmDampedLaplaceCharacter Lq r t) * ccmDampedLaplaceCharacter Lp n t =
      1 / (1 + 2 * Real.pi * Complex.I * ((r : ℝ) / Lq - (n : ℝ) / Lp)) := by
  simp_rw [star_ccmDampedLaplaceCharacter_mul]
  let a : ℂ :=
    -1 + Complex.I * (2 * Real.pi * ((n : ℝ) / Lp - (r : ℝ) / Lq))
  have ha : a.re < 0 := by simp [a]
  rw [integral_exp_mul_complex_Ioi (a := a) ha 0]
  dsimp [a]
  simp only [mul_zero, Complex.exp_zero, neg_div, one_div]
  calc
    -(-1 + Complex.I * (2 * Real.pi * ((n : ℝ) / Lp - (r : ℝ) / Lq)))⁻¹ =
        (-(-1 + Complex.I *
          (2 * Real.pi * ((n : ℝ) / Lp - (r : ℝ) / Lq))))⁻¹ := by
          rw [inv_neg]
    _ = (1 + 2 * Real.pi * Complex.I * ((r : ℝ) / Lq - (n : ℝ) / Lp))⁻¹ := by
      congr 1
      ring

theorem ccmNormalizedPrimePoleSequence_cross_tsum_eq_dampedLaplace_inner
    {Lp Lq : ℝ} (hp : 0 < Lp) (hq : 0 < Lq) (n r : ℤ) :
    (∑' k : ℕ, star (ccmNormalizedPrimePoleSequence Lq r k) * ccmNormalizedPrimePoleSequence Lp n k) =
      ∫ t : ℝ in Ioi 0,
        star (ccmDampedLaplaceCharacter Lq r t) * ccmDampedLaplaceCharacter Lp n t := by
  rw [ccmNormalizedPrimePoleSequence_cross_tsum hp hq,
    ccmDampedLaplaceCharacter_inner_integral]

/-- Every normalized CCM pole vector has squared `ℓ²` norm one. -/
theorem ccmNormalizedPrimePoleSequence_self_tsum {L : ℝ} (hL : 0 < L) (n : ℤ) :
    (∑' k : ℕ,
      star (ccmNormalizedPrimePoleSequence L n k) * ccmNormalizedPrimePoleSequence L n k) = 1 := by
  simpa using ccmNormalizedPrimePoleSequence_cross_tsum hL hL n n

/-- The corresponding damped Laplace character has squared `L²` norm one. -/
theorem ccmDampedLaplaceCharacter_self_inner_integral (L : ℝ) (n : ℤ) :
    ∫ t : ℝ in Ioi 0,
      star (ccmDampedLaplaceCharacter L n t) * ccmDampedLaplaceCharacter L n t = 1 := by
  simpa using ccmDampedLaplaceCharacter_inner_integral L L n n

end RHTower
