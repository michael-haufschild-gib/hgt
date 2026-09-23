import GaloisForLFunctions.RHTower.SuzukiWeilFrakPLaplace
import GaloisForLFunctions.RHTower.SuzukiWeilPropThreeOne
import GaloisForLFunctions.RHTower.XiHedenmalmDeBrangesSeam
import GaloisForLFunctions.RHTower.XiRelativeResolventFlux

/-!
# Vertical decay toolkit for Suzuki's `S_t`

Everything Suzuki's Proposition 1.2 needs about the *individual blocks* of eq. (1.6) on the real
axis, assembled without a single appeal to a Titchmarsh-type zero-density or `zeta'/zeta` bound.

The mechanism replacing Titchmarsh 9.6(A) and 9.2 is elementary.  On the real axis `A = XiC` and
`A'` are real, so the Schwarz partner `E# = A - i A'` has `|E#|^(2 : ℕ) = A^(2 : ℕ) + A'^(2 : ℕ)`; hence *both*
quotients

`|A / E#| <= 1`   and   `|A' / E#| <= 1`

hold everywhere on the line.  Substituting the completed split
`zeta'/zeta(1/2 - i x) = i (A'/A)(x) - (log archFactor)'(1/2 - i x)` into the singular block of
eq. (1.6) and multiplying by `A/E#` therefore turns the pole at every real Xi zero into the
*bounded* quantity `i A'/E#`.  No zero counting is needed.

The remaining blocks decay because the Lerch kernel does: with `A_n = n + 1/4` and `B = |x|/2`,
weighted AM-GM gives `|n + 1/4 - i x/2| >= A_n^{1/4} B^{3/4}`, so

`|Lerch kernel|  <=  (|x|/2)^{-3/4} * sum_n (n+1/4)^{-5/4}`,

an exponent comfortably better than the `1/2` that a plain Cauchy-Schwarz split would give, and
enough for square integrability.  Both the uniform bound (near the origin) and this decaying bound
are packaged into a single weight `decayW x = (1+|x|)^{-3/4}`.

Since the same Gauss bridge expresses `psi(1/4 - i x/2)` through the kernel, the archimedean
logarithmic derivative on the critical line is bounded by `M + (|x|/4) * |kernel|` with an absolute
`M`; that product is exactly what the `2/|x|` half of the exponential-slope bound absorbs.
-/

open Complex Filter Topology MeasureTheory Set
open GaloisForLFunctions.RHTower

open Complex Filter Topology MeasureTheory Set
open GaloisForLFunctions.RHTower

namespace RHTower
noncomputable section

/-! ## Reality of the centered Xi jet on the real axis -/

theorem XiC_ofReal_im (x : ℝ) : (XiC (x : ℂ)).im = 0 := by
  have h := XiC_conj ((x : ℂ))
  rw [Complex.conj_ofReal] at h
  exact Complex.conj_eq_iff_im.mp h.symm

theorem deriv_XiC_ofReal_im (x : ℝ) : (deriv XiC (x : ℂ)).im = 0 := by
  have h := deriv_XiC_conj ((x : ℂ))
  rw [Complex.conj_ofReal] at h
  exact Complex.conj_eq_iff_im.mp h.symm

theorem XiC_ofReal_eq (x : ℝ) : XiC (x : ℂ) = (((XiC (x : ℂ)).re : ℝ) : ℂ) := by
  apply Complex.ext <;> simp [XiC_ofReal_im]

theorem deriv_XiC_ofReal_eq (x : ℝ) :
    deriv XiC (x : ℂ) = (((deriv XiC (x : ℂ)).re : ℝ) : ℂ) := by
  apply Complex.ext <;> simp [deriv_XiC_ofReal_im]

/-- On the real axis the Schwarz partner is `a - i b` with `a, b` the real Xi jet. -/
theorem norm_sq_xiHedenmalmDeBrangesESharp_ofReal (x : ℝ) :
    ‖xiHedenmalmDeBrangesESharp (x : ℂ)‖ ^ 2
      = (XiC (x : ℂ)).re ^ 2 + (deriv XiC (x : ℂ)).re ^ 2 := by
  have hE : xiHedenmalmDeBrangesESharp (x : ℂ)
      = Complex.mk ((XiC (x : ℂ)).re) (-(deriv XiC (x : ℂ)).re) := by
    rw [xiHedenmalmDeBrangesESharp]
    apply Complex.ext <;>
      simp [Complex.mul_re, Complex.mul_im, XiC_ofReal_im, deriv_XiC_ofReal_im]
  rw [hE, Complex.sq_norm, Complex.normSq_mk]
  ring

theorem norm_XiC_div_ESharp_le_one (x : ℝ) :
    ‖XiC (x : ℂ) / xiHedenmalmDeBrangesESharp (x : ℂ)‖ ≤ 1 := by
  rcases eq_or_ne (xiHedenmalmDeBrangesESharp (x : ℂ)) 0 with h | h
  · rw [h, div_zero, norm_zero]
    norm_num
  · have hpos : (0 : ℝ) < ‖xiHedenmalmDeBrangesESharp (x : ℂ)‖ := norm_pos_iff.mpr h
    rw [norm_div, div_le_one hpos]
    have hA : ‖XiC (x : ℂ)‖ ^ 2 = (XiC (x : ℂ)).re ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, XiC_ofReal_im]
      ring
    have hkey : ‖XiC (x : ℂ)‖ ^ 2 ≤ ‖xiHedenmalmDeBrangesESharp (x : ℂ)‖ ^ 2 := by
      rw [hA, norm_sq_xiHedenmalmDeBrangesESharp_ofReal]
      nlinarith [sq_nonneg ((deriv XiC (x : ℂ)).re)]
    nlinarith [norm_nonneg (XiC (x : ℂ)), hpos]

theorem norm_deriv_XiC_div_ESharp_le_one (x : ℝ) :
    ‖deriv XiC (x : ℂ) / xiHedenmalmDeBrangesESharp (x : ℂ)‖ ≤ 1 := by
  rcases eq_or_ne (xiHedenmalmDeBrangesESharp (x : ℂ)) 0 with h | h
  · rw [h, div_zero, norm_zero]
    norm_num
  · have hpos : (0 : ℝ) < ‖xiHedenmalmDeBrangesESharp (x : ℂ)‖ := norm_pos_iff.mpr h
    rw [norm_div, div_le_one hpos]
    have hA : ‖deriv XiC (x : ℂ)‖ ^ 2 = (deriv XiC (x : ℂ)).re ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, deriv_XiC_ofReal_im]
      ring
    have hkey : ‖deriv XiC (x : ℂ)‖ ^ 2 ≤ ‖xiHedenmalmDeBrangesESharp (x : ℂ)‖ ^ 2 := by
      rw [hA, norm_sq_xiHedenmalmDeBrangesESharp_ofReal]
      nlinarith [sq_nonneg ((XiC (x : ℂ)).re)]
    nlinarith [norm_nonneg (deriv XiC (x : ℂ)), hpos]

/-! ## The `zeta'/zeta` bridge through the centered Xi function -/

theorem logDeriv_xi_reflected (z : ℂ) :
    logDeriv xi (1 / 2 - I * z) = I * logDeriv XiC z := by
  have h := logDeriv_xi_reciprocity (1 / 2 + z * I)
  rw [show (1 : ℂ) - (1 / 2 + z * I) = 1 / 2 - I * z by ring] at h
  rw [h, logDeriv_XiC_eq_mul_I_logDeriv_xi]
  linear_combination (-(logDeriv xi (1 / 2 + z * I))) * Complex.I_sq

theorem logDeriv_riemannZeta_vertical_eq {x : ℝ} (hx : XiC (x : ℂ) ≠ 0) :
    logDeriv riemannZeta (1 / 2 - I * (x : ℂ))
      = I * logDeriv XiC (x : ℂ) - logDeriv archFactor (1 / 2 - I * (x : ℂ)) := by
  have hsre : ((1 : ℂ) / 2 - I * (x : ℂ)).re = 1 / 2 := by
    simp [Complex.sub_re, Complex.mul_re]
  have h0 : (1 : ℂ) / 2 - I * (x : ℂ) ≠ 0 := by
    intro h
    rw [h] at hsre
    norm_num at hsre
  have h1 : (1 : ℂ) / 2 - I * (x : ℂ) ≠ 1 := by
    intro h
    rw [h] at hsre
    norm_num at hsre
  have hpole : ∀ m : ℕ, ((1 : ℂ) / 2 - I * (x : ℂ)) / 2 ≠ -(m : ℂ) := by
    intro m hc
    have hre : (((1 : ℂ) / 2 - I * (x : ℂ)) / 2).re = (-(m : ℂ)).re := by rw [hc]
    rw [Complex.div_re] at hre
    simp at hre
    nlinarith [Nat.cast_nonneg (α := ℝ) m]
  have hz : riemannZeta ((1 : ℂ) / 2 - I * (x : ℂ)) ≠ 0 :=
    riemannZeta_ne_zero_of_XiC_ne_zero hx h0 h1 (by rw [hsre]; norm_num)
  have hsplit := seamFluxCochain_eq_infinitePrimeFlux_add_archimedean_off_poles hpole h1 hz
  rw [seamFluxCochain, infinitePrimeFlux] at hsplit
  have hxi := logDeriv_xi_reflected ((x : ℂ))
  linear_combination hsplit + hxi

end
end RHTower

namespace RHTower
noncomputable section
open Complex Filter Topology MeasureTheory Set
open GaloisForLFunctions.RHTower

/-! ## Vertical decay of the Lerch kernel -/

/-- The convergent tail constant `∑ₙ (n + 1/4)^{-5/4}`. -/
def lerchQuarterTail : ℝ := ∑' n : ℕ, ((n : ℝ) + 1 / 4) ^ (-(5 / 4) : ℝ)

theorem summable_lerchQuarterTerm :
    Summable (fun n : ℕ => ((n : ℝ) + 1 / 4) ^ (-(5 / 4) : ℝ)) := by
  have hs : Summable (fun n : ℕ =>
      (4 : ℝ) ^ (5 / 4 : ℝ) * ((1 : ℝ) / ((n : ℝ) + 1) ^ (5 / 4 : ℝ))) :=
    (summable_one_div_nat_add_one_rpow (by norm_num)).mul_left _
  refine Summable.of_nonneg_of_le (fun n => Real.rpow_nonneg (by positivity) _)
    (fun n => ?_) hs
  have hn : (0 : ℝ) < (n : ℝ) + 1 / 4 := by positivity
  have hn1 : (0 : ℝ) < ((n : ℝ) + 1) / 4 := by positivity
  have hle : ((n : ℝ) + 1) / 4 ≤ (n : ℝ) + 1 / 4 := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hp : (((n : ℝ) + 1) / 4) ^ (5 / 4 : ℝ) ≤ ((n : ℝ) + 1 / 4) ^ (5 / 4 : ℝ) :=
    Real.rpow_le_rpow hn1.le hle (by norm_num)
  have hpos2 : (0 : ℝ) < (((n : ℝ) + 1) / 4) ^ (5 / 4 : ℝ) := Real.rpow_pos_of_pos hn1 _
  have hq : (((n : ℝ) + 1) / 4) ^ (5 / 4 : ℝ)
      = ((n : ℝ) + 1) ^ (5 / 4 : ℝ) / (4 : ℝ) ^ (5 / 4 : ℝ) :=
    Real.div_rpow (by positivity : (0:ℝ) ≤ (n : ℝ) + 1) (by norm_num : (0:ℝ) ≤ (4:ℝ)) _
  have hfour : (0 : ℝ) < (4 : ℝ) ^ (5 / 4 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  have hnp : (0 : ℝ) < ((n : ℝ) + 1) ^ (5 / 4 : ℝ) := Real.rpow_pos_of_pos (by positivity) _
  rw [Real.rpow_neg hn.le]
  calc (((n : ℝ) + 1 / 4) ^ (5 / 4 : ℝ))⁻¹
      ≤ ((((n : ℝ) + 1) / 4) ^ (5 / 4 : ℝ))⁻¹ := by
        exact inv_anti₀ hpos2 hp
    _ = (4 : ℝ) ^ (5 / 4 : ℝ) * ((1 : ℝ) / ((n : ℝ) + 1) ^ (5 / 4 : ℝ)) := by
        rw [hq]
        field_simp

theorem norm_sq_nat_add_vertical (x : ℝ) (n : ℕ) :
    ‖(n : ℂ) + ((1 : ℂ) / 4 - I * (x : ℂ) / 2)‖ ^ 2
      = ((n : ℝ) + 1 / 4) ^ 2 + (|x| / 2) ^ 2 := by
  have hre : ((n : ℂ) + ((1 : ℂ) / 4 - I * (x : ℂ) / 2)).re = (n : ℝ) + 1 / 4 := by
    simp [Complex.add_re, Complex.sub_re, Complex.mul_re]
  have him : ((n : ℂ) + ((1 : ℂ) / 4 - I * (x : ℂ) / 2)).im = -(x / 2) := by
    simp [Complex.add_im, Complex.sub_im, Complex.mul_im]
  rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
  linear_combination (-(1 : ℝ) / 4) * sq_abs x

theorem le_norm_nat_add_vertical {x : ℝ} (hx : 0 < |x|) (n : ℕ) :
    ((n : ℝ) + 1 / 4) ^ (1 / 4 : ℝ) * (|x| / 2) ^ (3 / 4 : ℝ)
      ≤ ‖(n : ℂ) + ((1 : ℂ) / 4 - I * (x : ℂ) / 2)‖ := by
  set A : ℝ := (n : ℝ) + 1 / 4 with hA
  set B : ℝ := |x| / 2 with hB
  have hA0 : (0 : ℝ) < A := by rw [hA]; positivity
  have hB0 : (0 : ℝ) < B := by rw [hB]; positivity
  set N : ℝ := ‖(n : ℂ) + ((1 : ℂ) / 4 - I * (x : ℂ) / 2)‖ with hN
  have hsq : N ^ 2 = A ^ 2 + B ^ 2 := norm_sq_nat_add_vertical x n
  have hN0 : (0 : ℝ) ≤ N := norm_nonneg _
  have hAN : A ≤ N := by nlinarith [sq_nonneg B, sq_nonneg (A - N), sq_nonneg (A + N)]
  have hBN : B ≤ N := by nlinarith [sq_nonneg A, sq_nonneg (B - N), sq_nonneg (B + N)]
  have hAM := Real.geom_mean_le_arith_mean2_weighted (w₁ := 1 / 4) (w₂ := 3 / 4)
    (p₁ := A) (p₂ := B) (by norm_num) (by norm_num) hA0.le hB0.le (by norm_num)
  linarith

theorem norm_suzukiLerchKernelTerm_vertical_le {t : ℝ} (ht : 0 ≤ t) {x : ℝ} (hx : 0 < |x|)
    (n : ℕ) :
    ‖suzukiLerchKernelTerm t ((1 : ℂ) / 4 - I * (x : ℂ) / 2) n‖
      ≤ (|x| / 2) ^ (-(3 / 4) : ℝ) * ((n : ℝ) + 1 / 4) ^ (-(5 / 4) : ℝ) := by
  set A : ℝ := (n : ℝ) + 1 / 4 with hA
  set B : ℝ := |x| / 2 with hB
  have hA0 : (0 : ℝ) < A := by rw [hA]; positivity
  have hB0 : (0 : ℝ) < B := by rw [hB]; positivity
  have hlow := le_norm_nat_add_vertical hx n
  have hq : ‖((n : ℂ) + 1 / 4)‖ = A := by rw [norm_nat_add_quarter]
  have hprod : A ^ (1 / 4 : ℝ) * B ^ (3 / 4 : ℝ) * A
      ≤ ‖(n : ℂ) + ((1 : ℂ) / 4 - I * (x : ℂ) / 2)‖ * ‖((n : ℂ) + 1 / 4)‖ := by
    rw [hq]
    exact mul_le_mul_of_nonneg_right hlow hA0.le
  have hpos : (0 : ℝ) < A ^ (1 / 4 : ℝ) * B ^ (3 / 4 : ℝ) * A := by
    have h1 : (0 : ℝ) < A ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hA0 _
    have h2 : (0 : ℝ) < B ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos hB0 _
    positivity
  have hexp : ‖((Real.exp (-(2 * (n : ℝ) * t)) : ℝ) : ℂ)‖ ≤ 1 := norm_exp_block_le ht n
  have hval : A ^ (1 / 4 : ℝ) * B ^ (3 / 4 : ℝ) * A = B ^ (3 / 4 : ℝ) * A ^ (5 / 4 : ℝ) := by
    have hone : A ^ (1 / 4 : ℝ) * A ^ (1 : ℝ) = A ^ (5 / 4 : ℝ) := by
      rw [← Real.rpow_add hA0]
      norm_num
    have this : A ^ (1 / 4 : ℝ) * A = A ^ (5 / 4 : ℝ) := by
      rw [← hone, Real.rpow_one]
    calc A ^ (1 / 4 : ℝ) * B ^ (3 / 4 : ℝ) * A = (A ^ (1 / 4 : ℝ) * A) * B ^ (3 / 4 : ℝ) := by
          ring
      _ = B ^ (3 / 4 : ℝ) * A ^ (5 / 4 : ℝ) := by rw [this]; ring
  rw [suzukiLerchKernelTerm, norm_div, norm_mul,
    Real.rpow_neg hB0.le, Real.rpow_neg hA0.le]
  rw [div_le_iff₀ (lt_of_lt_of_le hpos hprod)]
  calc ‖((Real.exp (-(2 * (n : ℝ) * t)) : ℝ) : ℂ)‖ ≤ 1 := hexp
    _ = (B ^ (3 / 4 : ℝ))⁻¹ * (A ^ (5 / 4 : ℝ))⁻¹ * (A ^ (1 / 4 : ℝ) * B ^ (3 / 4 : ℝ) * A) := by
        rw [hval]
        field_simp
    _ ≤ (B ^ (3 / 4 : ℝ))⁻¹ * (A ^ (5 / 4 : ℝ))⁻¹
          * (‖(n : ℂ) + ((1 : ℂ) / 4 - I * (x : ℂ) / 2)‖ * ‖((n : ℂ) + 1 / 4)‖) := by
        refine mul_le_mul_of_nonneg_left hprod ?_
        have h1 : (0 : ℝ) < B ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos hB0 _
        have h2 : (0 : ℝ) < A ^ (5 / 4 : ℝ) := Real.rpow_pos_of_pos hA0 _
        positivity

theorem norm_suzukiLerchKernel_vertical_le {t : ℝ} (ht : 0 ≤ t) {x : ℝ} (hx : 0 < |x|) :
    ‖suzukiLerchKernel t ((1 : ℂ) / 4 - I * (x : ℂ) / 2)‖
      ≤ (|x| / 2) ^ (-(3 / 4) : ℝ) * lerchQuarterTail := by
  have hsum : Summable (fun n : ℕ =>
      (|x| / 2) ^ (-(3 / 4) : ℝ) * ((n : ℝ) + 1 / 4) ^ (-(5 / 4) : ℝ)) :=
    summable_lerchQuarterTerm.mul_left _
  calc ‖suzukiLerchKernel t ((1 : ℂ) / 4 - I * (x : ℂ) / 2)‖
      ≤ ∑' n : ℕ, (|x| / 2) ^ (-(3 / 4) : ℝ) * ((n : ℝ) + 1 / 4) ^ (-(5 / 4) : ℝ) :=
        tsum_of_norm_bounded hsum.hasSum (fun n =>
          norm_suzukiLerchKernelTerm_vertical_le ht hx n)
    _ = (|x| / 2) ^ (-(3 / 4) : ℝ) * lerchQuarterTail := by
        rw [lerchQuarterTail, tsum_mul_left]

end
end RHTower

namespace RHTower
noncomputable section
open Complex Filter Topology MeasureTheory Set
open GaloisForLFunctions.RHTower

/-! ## The decay weight -/

/-- The `L²` decay weight `(1+|x|)^{-3/4}`. -/
def decayW (x : ℝ) : ℝ := (1 + |x|) ^ (-(3 / 4) : ℝ)

theorem decayW_pos (x : ℝ) : 0 < decayW x :=
  Real.rpow_pos_of_pos (by positivity) _

theorem inv_one_add_abs_le_decayW (x : ℝ) : (1 + |x|)⁻¹ ≤ decayW x := by
  have hb : (1 : ℝ) ≤ 1 + |x| := le_add_of_nonneg_right (abs_nonneg x)
  have h : (1 + |x|) ^ (-1 : ℝ) ≤ (1 + |x|) ^ (-(3 / 4) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hb (by norm_num)
  rwa [Real.rpow_neg_one] at h

theorem half_le_decayW_of_le_one {x : ℝ} (hx : |x| ≤ 1) : (1 : ℝ) / 2 ≤ decayW x := by
  have hb : (0 : ℝ) < 1 + |x| := by positivity
  have hb2 : (1 + |x|) ≤ 2 := by linarith
  have h1 : (1 + |x|) ^ (3 / 4 : ℝ) ≤ (2 : ℝ) ^ (3 / 4 : ℝ) :=
    Real.rpow_le_rpow hb.le hb2 (by norm_num)
  have h2 : (2 : ℝ) ^ (3 / 4 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  rw [Real.rpow_one] at h2
  have hpos : (0 : ℝ) < (1 + |x|) ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos hb _
  rw [decayW, Real.rpow_neg hb.le]
  rw [le_inv_comm₀ (by norm_num) hpos]
  calc (1 + |x|) ^ (3 / 4 : ℝ) ≤ 2 := le_trans h1 h2
    _ = ((1 : ℝ) / 2)⁻¹ := by norm_num

theorem third_le_decayW_of_le_two {x : ℝ} (hx : |x| ≤ 2) : (1 : ℝ) / 3 ≤ decayW x := by
  have hb : (0 : ℝ) < 1 + |x| := by positivity
  have hb2 : (1 + |x|) ≤ 3 := by linarith
  have h1 : (1 + |x|) ^ (3 / 4 : ℝ) ≤ (3 : ℝ) ^ (3 / 4 : ℝ) :=
    Real.rpow_le_rpow hb.le hb2 (by norm_num)
  have h2 : (3 : ℝ) ^ (3 / 4 : ℝ) ≤ (3 : ℝ) ^ (1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  rw [Real.rpow_one] at h2
  have hpos : (0 : ℝ) < (1 + |x|) ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos hb _
  rw [decayW, Real.rpow_neg hb.le]
  rw [le_inv_comm₀ (by norm_num) hpos]
  calc (1 + |x|) ^ (3 / 4 : ℝ) ≤ 3 := le_trans h1 h2
    _ = ((1 : ℝ) / 3)⁻¹ := by norm_num

theorem half_abs_rpow_le_decayW {x : ℝ} (hx : 2 ≤ |x|) :
    (|x| / 2) ^ (-(3 / 4) : ℝ) ≤ 3 * decayW x := by
  have hb : (0 : ℝ) < 1 + |x| := by positivity
  have hx0 : (0 : ℝ) < |x| / 2 := by linarith
  have hle : (1 + |x|) / 3 ≤ |x| / 2 := by linarith
  have hpos : (0 : ℝ) < (1 + |x|) / 3 := by positivity
  have hmono : (|x| / 2) ^ (-(3 / 4) : ℝ) ≤ ((1 + |x|) / 3) ^ (-(3 / 4) : ℝ) :=
    Real.rpow_le_rpow_of_nonpos hpos hle (by norm_num)
  have hsplit : ((1 + |x|) / 3) ^ (-(3 / 4) : ℝ)
      = (1 + |x|) ^ (-(3 / 4) : ℝ) / (3 : ℝ) ^ (-(3 / 4) : ℝ) :=
    Real.div_rpow (le_of_lt hb) (by norm_num : (0:ℝ) ≤ (3:ℝ)) _
  have h3 : (3 : ℝ) ^ (-(3 / 4) : ℝ) = ((3 : ℝ) ^ (3 / 4 : ℝ))⁻¹ := by
    rw [Real.rpow_neg (by norm_num)]
  have h4 : (3 : ℝ) ^ (3 / 4 : ℝ) ≤ 3 := by
    have := Real.rpow_le_rpow_of_exponent_le (x := (3:ℝ)) (by norm_num) (show (3/4:ℝ) ≤ 1 by norm_num)
    rwa [Real.rpow_one] at this
  have h5 : (0 : ℝ) < (3 : ℝ) ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  have hconv : (1 + |x|) ^ (-(3 / 4) : ℝ) / ((3 : ℝ) ^ (3 / 4 : ℝ))⁻¹
      = (1 + |x|) ^ (-(3 / 4) : ℝ) * (3 : ℝ) ^ (3 / 4 : ℝ) := by
    field_simp
  rw [hsplit, h3, hconv] at hmono
  calc (|x| / 2) ^ (-(3 / 4) : ℝ)
      ≤ (1 + |x|) ^ (-(3 / 4) : ℝ) * (3 : ℝ) ^ (3 / 4 : ℝ) := hmono
    _ ≤ (1 + |x|) ^ (-(3 / 4) : ℝ) * 3 :=
        mul_le_mul_of_nonneg_left h4 (Real.rpow_nonneg hb.le _)
    _ = 3 * decayW x := by rw [decayW]; ring

end
end RHTower

namespace RHTower
noncomputable section
open Complex Filter Topology MeasureTheory Set
open GaloisForLFunctions.RHTower

/-! ## Uniform and decaying kernel bounds on the quarter line -/

theorem quarterLine_re (x : ℝ) : ((1 : ℂ) / 4 - I * (x : ℂ) / 2).re = 1 / 4 := by
  simp [Complex.sub_re, Complex.mul_re]

theorem norm_suzukiLerchKernel_quarterLine_le {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    ‖suzukiLerchKernel t ((1 : ℂ) / 4 - I * (x : ℂ) / 2)‖
      ≤ 16 * ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2 := by
  have hre : (1 : ℝ) / 4 ≤ ((1 : ℂ) / 4 - I * (x : ℂ) / 2).re := by
    rw [quarterLine_re]
  have hsum : Summable (fun n : ℕ => 16 * (1 / ((n : ℝ) + 1) ^ 2)) :=
    summable_one_div_nat_add_one_sq.mul_left 16
  calc ‖suzukiLerchKernel t ((1 : ℂ) / 4 - I * (x : ℂ) / 2)‖
      ≤ ∑' n : ℕ, 16 * (1 / ((n : ℝ) + 1) ^ 2) := by
        refine tsum_of_norm_bounded hsum.hasSum fun n => ?_
        have h := norm_suzukiLerchKernelTerm_le ht (c := 1 / 4) (by norm_num) (by norm_num) hre n
        norm_num at h ⊢
        linarith
    _ = 16 * ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2 := tsum_mul_left

theorem lerchQuarterTail_nonneg : 0 ≤ lerchQuarterTail :=
  tsum_nonneg fun n => Real.rpow_nonneg (by positivity) _

theorem zetaTwoTail_nonneg : (0 : ℝ) ≤ ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2 :=
  tsum_nonneg fun n => by positivity

/-- The explicit constant in the uniform quarter-line kernel bound. -/
def suzukiKernelConst : ℝ :=
  max (48 * ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2) (3 * lerchQuarterTail)

theorem suzukiKernelConst_nonneg : 0 ≤ suzukiKernelConst :=
  le_max_of_le_left (by positivity)

/-- One weight controls the archimedean Lerch kernel on the whole quarter line. -/
theorem norm_suzukiLerchKernel_le_decayW {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    ‖suzukiLerchKernel t ((1 : ℂ) / 4 - I * (x : ℂ) / 2)‖ ≤ suzukiKernelConst * decayW x := by
  rw [suzukiKernelConst]
  rcases le_or_gt |x| 2 with hx | hx
  · have hb := norm_suzukiLerchKernel_quarterLine_le ht x
    have hw := third_le_decayW_of_le_two hx
    have hz := zetaTwoTail_nonneg
    calc ‖suzukiLerchKernel t ((1 : ℂ) / 4 - I * (x : ℂ) / 2)‖
        ≤ 16 * ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2 := hb
      _ = (48 * ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2) * (1 / 3) := by ring
      _ ≤ (48 * ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2) * decayW x :=
          mul_le_mul_of_nonneg_left hw (by positivity)
      _ ≤ max (48 * ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2) (3 * lerchQuarterTail) * decayW x :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (decayW_pos x).le
  · have hx2 : (2 : ℝ) ≤ |x| := hx.le
    have hxpos : (0 : ℝ) < |x| := by linarith
    have hb := norm_suzukiLerchKernel_vertical_le ht hxpos
    have hw := half_abs_rpow_le_decayW hx2
    calc ‖suzukiLerchKernel t ((1 : ℂ) / 4 - I * (x : ℂ) / 2)‖
        ≤ (|x| / 2) ^ (-(3 / 4) : ℝ) * lerchQuarterTail := hb
      _ ≤ (3 * decayW x) * lerchQuarterTail :=
          mul_le_mul_of_nonneg_right hw lerchQuarterTail_nonneg
      _ = (3 * lerchQuarterTail) * decayW x := by ring
      _ ≤ max (48 * ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2) (3 * lerchQuarterTail) * decayW x :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (decayW_pos x).le

end
end RHTower

namespace RHTower
noncomputable section
open Complex Filter Topology MeasureTheory Set
open GaloisForLFunctions.RHTower

/-! ## The exponential slope -/

theorem norm_I_mul_ofReal (x : ℝ) : ‖I * (x : ℂ)‖ = |x| := by
  rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]

theorem norm_expSlope_le_abs (x c : ℝ) :
    ‖(Complex.exp (-(I * (x : ℂ) * (c : ℂ))) - 1) / (I * (x : ℂ))‖ ≤ |c| := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have hIx : ‖I * (x : ℂ)‖ = |x| := norm_I_mul_ofReal x
    have hrw : -(I * (x : ℂ) * (c : ℂ)) = I * ((-(x * c) : ℝ) : ℂ) := by push_cast; ring
    have hnum : ‖Complex.exp (-(I * (x : ℂ) * (c : ℂ))) - 1‖ ≤ |x| * |c| := by
      rw [hrw]
      have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := -(x * c))
      rw [Real.norm_eq_abs, abs_neg, abs_mul] at h
      exact h
    rw [norm_div, hIx, div_le_iff₀ (abs_pos.mpr hx)]
    calc ‖Complex.exp (-(I * (x : ℂ) * (c : ℂ))) - 1‖ ≤ |x| * |c| := hnum
      _ = |c| * |x| := by ring

theorem norm_expSlope_le_two_div (x c : ℝ) :
    ‖(Complex.exp (-(I * (x : ℂ) * (c : ℂ))) - 1) / (I * (x : ℂ))‖ ≤ 2 / |x| := by
  have hIx : ‖I * (x : ℂ)‖ = |x| := norm_I_mul_ofReal x
  have hrw : -(I * (x : ℂ) * (c : ℂ)) = I * ((-(x * c) : ℝ) : ℂ) := by push_cast; ring
  have h1 : ‖Complex.exp (-(I * (x : ℂ) * (c : ℂ)))‖ = 1 := by
    rw [hrw, Complex.norm_exp]
    simp
  have hnum : ‖Complex.exp (-(I * (x : ℂ) * (c : ℂ))) - 1‖ ≤ 2 := by
    calc ‖Complex.exp (-(I * (x : ℂ) * (c : ℂ))) - 1‖
        ≤ ‖Complex.exp (-(I * (x : ℂ) * (c : ℂ)))‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [h1]; norm_num
  rw [norm_div, hIx]
  exact div_le_div_of_nonneg_right hnum (abs_nonneg x)

theorem norm_expSlope_le_decayW {x c : ℝ} (hc : 0 ≤ c) :
    ‖(Complex.exp (-(I * (x : ℂ) * (c : ℂ))) - 1) / (I * (x : ℂ))‖ ≤ (2 * c + 4) * decayW x := by
  rcases le_or_gt |x| 1 with hx | hx
  · have h1 := norm_expSlope_le_abs x c
    have h2 := half_le_decayW_of_le_one hx
    rw [abs_of_nonneg hc] at h1
    nlinarith [decayW_pos x]
  · have hxpos : (0 : ℝ) < |x| := by linarith
    have hx0 : x ≠ 0 := by
      intro h
      rw [h, abs_zero] at hxpos
      linarith
    have h1 := norm_expSlope_le_two_div x c
    have h2 : 2 / |x| ≤ 4 / (1 + |x|) := by
      rw [div_le_div_iff₀ hxpos (by positivity)]
      nlinarith
    have h3 : (4 : ℝ) / (1 + |x|) = 4 * (1 + |x|)⁻¹ := by
      rw [div_eq_mul_inv]
    have h4 := inv_one_add_abs_le_decayW x
    have h5 : (4 : ℝ) * (1 + |x|)⁻¹ ≤ 4 * decayW x := by linarith
    nlinarith [decayW_pos x]

/-! ## The archimedean factor on the critical line -/

theorem norm_digamma_quarterLine_le (x : ℝ) :
    ‖Complex.digamma ((1 : ℂ) / 4 - I * (x : ℂ) / 2)‖
      ≤ ‖Complex.digamma (1 / 4 : ℂ)‖
        + (|x| / 2) * ‖suzukiLerchKernel 0 ((1 : ℂ) / 4 - I * (x : ℂ) / 2)‖ := by
  have hwre : (0 : ℝ) < ((1 : ℂ) / 4 - I * (x : ℂ) / 2).re := by
    rw [quarterLine_re]; norm_num
  have hbridge := digamma_sub_quarter_eq hwre
  have hfac := suzukiLerchDiff_eq (t := 0) hwre
  have hquarter : (1 : ℂ) / 4 - ((1 : ℂ) / 4 - I * (x : ℂ) / 2) = I * (x : ℂ) / 2 := by ring
  rw [hfac, hquarter] at hbridge
  have hval : Complex.digamma ((1 : ℂ) / 4 - I * (x : ℂ) / 2)
      = Complex.digamma (1 / 4 : ℂ)
        - I * (x : ℂ) / 2 * suzukiLerchKernel 0 ((1 : ℂ) / 4 - I * (x : ℂ) / 2) := by
    linear_combination hbridge
  have hcoef : ‖I * (x : ℂ) / 2‖ = |x| / 2 := by
    rw [norm_div, norm_I_mul_ofReal]
    norm_num
  calc ‖Complex.digamma ((1 : ℂ) / 4 - I * (x : ℂ) / 2)‖
      ≤ ‖Complex.digamma (1 / 4 : ℂ)‖
          + ‖I * (x : ℂ) / 2 * suzukiLerchKernel 0 ((1 : ℂ) / 4 - I * (x : ℂ) / 2)‖ := by
        rw [hval]; exact norm_sub_le _ _
    _ = ‖Complex.digamma (1 / 4 : ℂ)‖
          + (|x| / 2) * ‖suzukiLerchKernel 0 ((1 : ℂ) / 4 - I * (x : ℂ) / 2)‖ := by
        rw [norm_mul, hcoef]

/-- The explicit constant in the archimedean bound on the critical line. -/
def suzukiArchConst : ℝ :=
  4 + |Real.log Real.pi| / 2 + ‖Complex.digamma (1 / 4 : ℂ)‖ / 2

theorem suzukiArchConst_nonneg : 0 ≤ suzukiArchConst := by
  rw [suzukiArchConst]; positivity

theorem norm_logDeriv_archFactor_vertical_le (x : ℝ) :
    ‖logDeriv archFactor ((1 : ℂ) / 2 - I * (x : ℂ))‖
      ≤ suzukiArchConst + (|x| / 4) * ‖suzukiLerchKernel 0 ((1 : ℂ) / 4 - I * (x : ℂ) / 2)‖ := by
  rw [suzukiArchConst]
  have hsre : ((1 : ℂ) / 2 - I * (x : ℂ)).re = 1 / 2 := by
    simp [Complex.sub_re, Complex.mul_re]
  have h0 : (1 : ℂ) / 2 - I * (x : ℂ) ≠ 0 := by
    intro h; rw [h] at hsre; norm_num at hsre
  have h1 : (1 : ℂ) / 2 - I * (x : ℂ) ≠ 1 := by
    intro h; rw [h] at hsre; norm_num at hsre
  have hpole : ∀ m : ℕ, ((1 : ℂ) / 2 - I * (x : ℂ)) / 2 ≠ -(m : ℂ) := by
    intro m hc
    have hre : ((((1 : ℂ) / 2 - I * (x : ℂ)) / 2)).re = (-(m : ℂ)).re := by rw [hc]
    rw [Complex.div_re] at hre
    simp at hre
    nlinarith [Nat.cast_nonneg (α := ℝ) m]
  rw [logDeriv_archFactor_closed_off_poles hpole h0 h1,
    GaloisForLFunctions.gammaRealLogConnection]
  have hhalf : ((1 : ℂ) / 2 - I * (x : ℂ)) / 2 = (1 : ℂ) / 4 - I * (x : ℂ) / 2 := by ring
  rw [hhalf]
  have hs1 : (1 : ℝ) / 2 ≤ ‖(1 : ℂ) / 2 - I * (x : ℂ)‖ := by
    have := Complex.abs_re_le_norm ((1 : ℂ) / 2 - I * (x : ℂ))
    rw [hsre] at this
    rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)] at this
    exact this
  have hs2re : ((1 : ℂ) / 2 - I * (x : ℂ) - 1).re = -(1 / 2) := by
    simp [Complex.sub_re, Complex.mul_re]
    norm_num
  have hs2 : (1 : ℝ) / 2 ≤ ‖(1 : ℂ) / 2 - I * (x : ℂ) - 1‖ := by
    have := Complex.abs_re_le_norm ((1 : ℂ) / 2 - I * (x : ℂ) - 1)
    rw [hs2re, abs_neg, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)] at this
    exact this
  have hinv1 : ‖(1 : ℂ) / ((1 : ℂ) / 2 - I * (x : ℂ))‖ ≤ 2 := by
    rw [norm_div, norm_one]
    rw [div_le_iff₀ (lt_of_lt_of_le (by norm_num) hs1)]
    linarith
  have hinv2 : ‖(1 : ℂ) / ((1 : ℂ) / 2 - I * (x : ℂ) - 1)‖ ≤ 2 := by
    rw [norm_div, norm_one]
    rw [div_le_iff₀ (lt_of_lt_of_le (by norm_num) hs2)]
    linarith
  have hlog : ‖(-(((Real.log Real.pi : ℝ) : ℂ) / 2))‖ = |Real.log Real.pi| / 2 := by
    rw [norm_neg, norm_div, Complex.norm_real, Real.norm_eq_abs]
    norm_num
  have hdig := norm_digamma_quarterLine_le x
  have hnorm2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  have hdig2 : ‖Complex.digamma ((1 : ℂ) / 4 - I * (x : ℂ) / 2) / 2‖
      = ‖Complex.digamma ((1 : ℂ) / 4 - I * (x : ℂ) / 2)‖ / 2 := by
    rw [norm_div, hnorm2]
  have htri : ‖(1 : ℂ) / ((1 : ℂ) / 2 - I * (x : ℂ)) + 1 / ((1 : ℂ) / 2 - I * (x : ℂ) - 1)
        + (-(((Real.log Real.pi : ℝ) : ℂ) / 2)
            + Complex.digamma ((1 : ℂ) / 4 - I * (x : ℂ) / 2) / 2)‖
      ≤ ‖(1 : ℂ) / ((1 : ℂ) / 2 - I * (x : ℂ))‖ + ‖(1 : ℂ) / ((1 : ℂ) / 2 - I * (x : ℂ) - 1)‖
          + (‖(-(((Real.log Real.pi : ℝ) : ℂ) / 2))‖
            + ‖Complex.digamma ((1 : ℂ) / 4 - I * (x : ℂ) / 2) / 2‖) := by
    refine le_trans (norm_add_le _ _) ?_
    have h1 := norm_add_le ((1 : ℂ) / ((1 : ℂ) / 2 - I * (x : ℂ)))
      ((1 : ℂ) / ((1 : ℂ) / 2 - I * (x : ℂ) - 1))
    have h2 := norm_add_le (-(((Real.log Real.pi : ℝ) : ℂ) / 2))
      (Complex.digamma ((1 : ℂ) / 4 - I * (x : ℂ) / 2) / 2)
    linarith
  linarith

end
end RHTower
