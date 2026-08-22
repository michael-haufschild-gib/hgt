import GaloisForLFunctions.RHTower.SuzukiWeilVerticalDecay
import GaloisForLFunctions.RHTower.XiWeilDivisorHilbert
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# Suzuki, Proposition 1.2: `S_t` is square integrable on the real line

Masatoshi Suzuki, *On the Hilbert space derived from the Weil distribution* (arXiv:2301.00421v3),
Proposition 1.2 (`prop_101`): for every fixed `t`, the function

`S_t(z) = i (1 + Theta_xi^#(z))/2 * P_t(z)`     (eq. 1.5)

belongs to `L^2(R)` as a function of the real variable.  Unconditional.

The published proof runs through Titchmarsh 9.6(A) (`zeta'/zeta` equals the sum over nearby zeros
up to `O(log t)`) and Titchmarsh 9.2 (the local zero count is `O(log t)`), obtaining
`S_t(x) << log|x| / |x|`.  This file proves the weaker but sufficient decay
`S_t(x) << (1+|x|)^{-3/4}` by a route that needs neither: see
`GaloisForLFunctions.RHTower.SuzukiWeilVerticalDecay` for the mechanism.  The decisive identity is

`S_t = i (A/E#) * (polar + prime + kernels)
      + i * expSlope * ( i (A'/E#) - (A/E#) * (log archFactor)'(1/2 - i x) )`,

in which no pole survives (`suzukiFrakS_ofReal_decomp`).

For the `L^2` statement itself one more thing is needed: a *measurable* representative.  The
displayed formula for `S_t` involves `zeta'/zeta`, whose measurability is not available off the
shelf.  It is avoided by working with `suzukiFrakSModel`, which is the same decomposition with the
digamma traded for the Lerch kernel through the Gauss bridge; the model is built from `XiC`, `deriv
XiC`, exponentials and one convergent series, hence manifestly measurable, and agrees with `S_t`
off the countable set of real Xi zeros together with the origin.
-/

open Complex Filter Topology MeasureTheory Set
open GaloisForLFunctions.RHTower

namespace RHTower
noncomputable section
open Complex Filter Topology MeasureTheory Set
open GaloisForLFunctions.RHTower

/-! ## Suzuki eq. (1.5) -/

/-- The Schwarz partner `Θ_ξ^♯ = E_ξ / E_ξ^♯` of the meromorphic inner function of the
Hedenmalm--de Branges pair. -/
def suzukiThetaSharp (z : ℂ) : ℂ :=
  xiHedenmalmDeBrangesE z / xiHedenmalmDeBrangesESharp z

/-- **Suzuki eq. (1.5).**  `𝔖_t(z) = i(1 + Θ_ξ^♯(z))/2 · 𝔓_t(z)`. -/
def suzukiFrakS (t : ℝ) (z : ℂ) : ℂ :=
  I * (1 + suzukiThetaSharp z) / 2 * suzukiFrakP t z

theorem xiHedenmalmDeBrangesESharp_ofReal_ne_zero {x : ℝ} (hx : XiC (x : ℂ) ≠ 0) :
    xiHedenmalmDeBrangesESharp (x : ℂ) ≠ 0 := by
  intro h
  apply hx
  have hsq := norm_sq_xiHedenmalmDeBrangesESharp_ofReal x
  rw [h, norm_zero] at hsq
  have h1 : (XiC (x : ℂ)).re = 0 := by
    nlinarith [sq_nonneg ((XiC (x : ℂ)).re), sq_nonneg ((deriv XiC (x : ℂ)).re)]
  refine Complex.ext ?_ ?_
  · rw [h1]; simp
  · rw [XiC_ofReal_im]; simp

theorem suzukiFrakS_ofReal_eq (t : ℝ) {x : ℝ} (hx : XiC (x : ℂ) ≠ 0) :
    suzukiFrakS t (x : ℂ)
      = I * (XiC (x : ℂ) / xiHedenmalmDeBrangesESharp (x : ℂ)) * suzukiFrakP t (x : ℂ) := by
  have hE := xiHedenmalmDeBrangesESharp_ofReal_ne_zero hx
  have hadd := xiHedenmalmDeBrangesE_add_sharp ((x : ℂ))
  rw [suzukiFrakS, suzukiThetaSharp]
  congr 1
  field_simp
  linear_combination hadd

/-- **The pole-free decomposition of `𝔖_t` on the real axis.**  The apparent poles of the
`ζ'/ζ` block at the real zeros of `ξ(1/2-iz)` are removed by the factor `A/E^♯`, whose companion
`A'/E^♯` is bounded by one. -/
theorem suzukiFrakS_ofReal_decomp (t : ℝ) {x : ℝ} (hx : x ≠ 0) (hXi : XiC (x : ℂ) ≠ 0) :
    suzukiFrakS t (x : ℂ)
      = I * (XiC (x : ℂ) / xiHedenmalmDeBrangesESharp (x : ℂ)) *
          (suzukiFrakPPolar t (x : ℂ) + suzukiFrakPPrime t (x : ℂ)
            + suzukiLerchKernel 0 ((1 : ℂ) / 4 - I * (x : ℂ) / 2) / 4
            - ((Real.exp (-(t / 2)) : ℝ) : ℂ)
              * suzukiLerchKernel t ((1 : ℂ) / 4 - I * (x : ℂ) / 2) / 4)
        + I * ((Complex.exp (-(I * (x : ℂ) * (t : ℂ))) - 1) / (I * (x : ℂ))) *
            (I * (deriv XiC (x : ℂ) / xiHedenmalmDeBrangesESharp (x : ℂ))
              - (XiC (x : ℂ) / xiHedenmalmDeBrangesESharp (x : ℂ))
                * logDeriv archFactor ((1 : ℂ) / 2 - I * (x : ℂ))) := by
  have hE := xiHedenmalmDeBrangesESharp_ofReal_ne_zero hXi
  have hz0 : ((x : ℝ) : ℂ) ≠ 0 := by
    simpa using hx
  have hwre : 0 < ((1 : ℂ) / 4 - I * (x : ℂ) / 2).re := by rw [quarterLine_re]; norm_num
  have hreg := suzukiFrakP_eq_reg_of_re_pos t hz0 hwre
  have hbridge := logDeriv_riemannZeta_vertical_eq hXi
  have hkey : (XiC (x : ℂ) / xiHedenmalmDeBrangesESharp (x : ℂ)) * logDeriv XiC (x : ℂ)
      = deriv XiC (x : ℂ) / xiHedenmalmDeBrangesESharp (x : ℂ) := by
    rw [logDeriv_apply]
    field_simp
  rw [suzukiFrakS_ofReal_eq t hXi, hreg, suzukiFrakPReg, suzukiFrakPPolar, suzukiFrakPPrime]
  linear_combination (I * (XiC (x : ℂ) / xiHedenmalmDeBrangesESharp (x : ℂ))
      * ((Complex.exp (-(I * (x : ℂ) * (t : ℂ))) - 1) / (I * (x : ℂ)))) * hbridge
    + (I ^ 2 * ((Complex.exp (-(I * (x : ℂ) * (t : ℂ))) - 1) / (I * (x : ℂ)))) * hkey

end
end RHTower

namespace RHTower
noncomputable section
open Complex Filter Topology MeasureTheory Set
open GaloisForLFunctions.RHTower

/-! ## Blockwise bounds on the real axis -/

theorem half_one_add_abs_le_norm_one_add (x : ℝ) :
    (1 + |x|) / 2 ≤ ‖(1 : ℂ) + 2 * I * (x : ℂ)‖ := by
  have hre : ((1 : ℂ) + 2 * I * (x : ℂ)).re = 1 := by simp [Complex.add_re, Complex.mul_re]
  have him : ((1 : ℂ) + 2 * I * (x : ℂ)).im = 2 * x := by simp [Complex.add_im, Complex.mul_im]
  have h1 : (1 : ℝ) ≤ ‖(1 : ℂ) + 2 * I * (x : ℂ)‖ := by
    have h := Complex.abs_re_le_norm ((1 : ℂ) + 2 * I * (x : ℂ))
    rw [hre] at h
    simpa using h
  have h2 : 2 * |x| ≤ ‖(1 : ℂ) + 2 * I * (x : ℂ)‖ := by
    have h := Complex.abs_im_le_norm ((1 : ℂ) + 2 * I * (x : ℂ))
    rw [him, abs_mul] at h
    simpa using h
  linarith

theorem half_one_add_abs_le_norm_one_sub (x : ℝ) :
    (1 + |x|) / 2 ≤ ‖(1 : ℂ) - 2 * I * (x : ℂ)‖ := by
  have hre : ((1 : ℂ) - 2 * I * (x : ℂ)).re = 1 := by simp [Complex.sub_re, Complex.mul_re]
  have him : ((1 : ℂ) - 2 * I * (x : ℂ)).im = -(2 * x) := by
    simp [Complex.sub_im, Complex.mul_im]
  have h1 : (1 : ℝ) ≤ ‖(1 : ℂ) - 2 * I * (x : ℂ)‖ := by
    have h := Complex.abs_re_le_norm ((1 : ℂ) - 2 * I * (x : ℂ))
    rw [hre] at h
    simpa using h
  have h2 : 2 * |x| ≤ ‖(1 : ℂ) - 2 * I * (x : ℂ)‖ := by
    have h := Complex.abs_im_le_norm ((1 : ℂ) - 2 * I * (x : ℂ))
    rw [him, abs_neg, abs_mul] at h
    simpa using h
  linarith

theorem norm_div_le_two_mul_decayW {x : ℝ} {a d : ℂ} (hd : (1 + |x|) / 2 ≤ ‖d‖) :
    ‖a / d‖ ≤ 2 * ‖a‖ * decayW x := by
  have hpos : (0 : ℝ) < 1 + |x| := by positivity
  have hdpos : (0 : ℝ) < ‖d‖ := lt_of_lt_of_le (by linarith) hd
  have hwpos : (0 : ℝ) < decayW x := decayW_pos x
  have hcnn : (0 : ℝ) ≤ 2 * ‖a‖ * decayW x :=
    mul_nonneg (by positivity) hwpos.le
  rw [norm_div, div_le_iff₀ hdpos]
  have hinvcancel : (1 + |x|)⁻¹ * ((1 + |x|) / 2) = 1 / 2 := by field_simp
  have h2 : 2 * ‖a‖ * ((1 + |x|)⁻¹) ≤ 2 * ‖a‖ * decayW x :=
    mul_le_mul_of_nonneg_left (inv_one_add_abs_le_decayW x) (by positivity)
  calc ‖a‖ = 2 * ‖a‖ * ((1 + |x|)⁻¹) * ((1 + |x|) / 2) := by
        rw [mul_assoc, hinvcancel]; ring
    _ ≤ 2 * ‖a‖ * decayW x * ((1 + |x|) / 2) := mul_le_mul_of_nonneg_right h2 (by linarith)
    _ ≤ 2 * ‖a‖ * decayW x * ‖d‖ := mul_le_mul_of_nonneg_left hd hcnn

theorem norm_suzukiFrakPPolar_ofReal_le (t : ℝ) (x : ℝ) :
    ‖suzukiFrakPPolar t (x : ℂ)‖
      ≤ (2 * ‖4 * ((Real.exp (t / 2) : ℂ) - 1)‖
          + 2 * ‖4 * ((Real.exp (-(t / 2)) : ℂ) - 1)‖) * decayW x := by
  have hA := norm_div_le_two_mul_decayW (a := 4 * ((Real.exp (t / 2) : ℂ) - 1))
    (half_one_add_abs_le_norm_one_add x)
  have hB := norm_div_le_two_mul_decayW (a := 4 * ((Real.exp (-(t / 2)) : ℂ) - 1))
    (half_one_add_abs_le_norm_one_sub x)
  have htri : ‖suzukiFrakPPolar t (x : ℂ)‖
      ≤ ‖4 * ((Real.exp (t / 2) : ℂ) - 1) / ((1 : ℂ) + 2 * I * (x : ℂ))‖
        + ‖4 * ((Real.exp (-(t / 2)) : ℂ) - 1) / ((1 : ℂ) - 2 * I * (x : ℂ))‖ := by
    rw [suzukiFrakPPolar]
    exact norm_add_le _ _
  nlinarith [htri, hA, hB]

theorem norm_suzukiFrakPPrime_ofReal_le (t : ℝ) (x : ℝ) :
    ‖suzukiFrakPPrime t (x : ℂ)‖
      ≤ ((∑ n ∈ Finset.Icc 2 ⌊Real.exp t⌋₊, screwPrimeWeight n) * (2 * t + 4)) * decayW x := by
  have hwpos : (0 : ℝ) < decayW x := decayW_pos x
  have hterm : ∀ n ∈ Finset.Icc 2 ⌊Real.exp t⌋₊,
      ‖(screwPrimeWeight n : ℂ) *
          ((Complex.exp (-(I * (x : ℂ) * ((t : ℂ) - (Real.log n : ℂ)))) - 1) / (I * (x : ℂ)))‖
        ≤ screwPrimeWeight n * (2 * t + 4) * decayW x := by
    intro n hn
    have hnN : n ≤ ⌊Real.exp t⌋₊ := (Finset.mem_Icc.mp hn).2
    have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
    have hlog : Real.log (n : ℝ) ≤ t := by
      have h1 : ((n : ℕ) : ℝ) ≤ Real.exp t :=
        le_trans (by exact_mod_cast hnN) (Nat.floor_le (Real.exp_pos t).le)
      have h2 : Real.log (n : ℝ) ≤ Real.log (Real.exp t) :=
        Real.log_le_log (by positivity) h1
      rwa [Real.log_exp] at h2
    have hc : (0 : ℝ) ≤ t - Real.log n := by linarith
    have hcast : -(I * (x : ℂ) * ((t : ℂ) - (Real.log n : ℂ)))
        = -(I * (x : ℂ) * (((t - Real.log n : ℝ)) : ℂ)) := by push_cast; ring
    have hslope := norm_expSlope_le_decayW (x := x) (c := t - Real.log n) hc
    rw [← hcast] at hslope
    have hwn : (0 : ℝ) ≤ screwPrimeWeight n := screwPrimeWeight_nonneg n
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hwn]
    have hmono : 2 * (t - Real.log n) + 4 ≤ 2 * t + 4 := by
      have : (0 : ℝ) ≤ Real.log n := Real.log_nonneg (by exact_mod_cast Nat.one_le_of_lt hn2)
      linarith
    have step1 : screwPrimeWeight n
          * ‖(Complex.exp (-(I * (x : ℂ) * ((t : ℂ) - (Real.log n : ℂ)))) - 1) / (I * (x : ℂ))‖
        ≤ screwPrimeWeight n * ((2 * (t - Real.log n) + 4) * decayW x) :=
      mul_le_mul_of_nonneg_left hslope hwn
    have step2 : screwPrimeWeight n * ((2 * (t - Real.log n) + 4) * decayW x)
        ≤ screwPrimeWeight n * ((2 * t + 4) * decayW x) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hmono hwpos.le) hwn
    linarith [step1, step2]
  calc ‖suzukiFrakPPrime t (x : ℂ)‖
      ≤ ∑ n ∈ Finset.Icc 2 ⌊Real.exp t⌋₊, screwPrimeWeight n * (2 * t + 4) * decayW x := by
        rw [suzukiFrakPPrime]
        exact le_trans (norm_sum_le _ _) (Finset.sum_le_sum hterm)
    _ = ((∑ n ∈ Finset.Icc 2 ⌊Real.exp t⌋₊, screwPrimeWeight n) * (2 * t + 4)) * decayW x := by
        rw [Finset.sum_mul, Finset.sum_mul]

end
end RHTower

namespace RHTower
noncomputable section
open Complex Filter Topology MeasureTheory Set
open GaloisForLFunctions.RHTower

/-! ## The master bound: `𝔖_t` decays like `(1+|x|)^{-3/4}` on the real axis -/

theorem exists_norm_suzukiFrakS_le {t : ℝ} (ht : 0 ≤ t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, x ≠ 0 → XiC (x : ℂ) ≠ 0 →
      ‖suzukiFrakS t (x : ℂ)‖ ≤ C * decayW x := by
  obtain ⟨K, hK0, hK⟩ := exists_norm_suzukiLerchKernel_le_decayW
  obtain ⟨M, hM0, hM⟩ := exists_norm_logDeriv_archFactor_vertical_le
  have hP : (0 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 ⌊Real.exp t⌋₊, screwPrimeWeight n :=
    Finset.sum_nonneg fun n _ => screwPrimeWeight_nonneg n
  refine ⟨2 * ‖4 * ((Real.exp (t / 2) : ℂ) - 1)‖ + 2 * ‖4 * ((Real.exp (-(t / 2)) : ℂ) - 1)‖
      + (∑ n ∈ Finset.Icc 2 ⌊Real.exp t⌋₊, screwPrimeWeight n) * (2 * t + 4)
      + K / 4 + Real.exp (-(t / 2)) * K / 4
      + (2 * t + 4) * (1 + M) + K / 2, ?_, ?_⟩
  · have h2t : (0 : ℝ) ≤ 2 * t + 4 := by linarith
    have hexp : (0 : ℝ) < Real.exp (-(t / 2)) := Real.exp_pos _
    nlinarith [norm_nonneg (4 * ((Real.exp (t / 2) : ℂ) - 1)),
      norm_nonneg (4 * ((Real.exp (-(t / 2)) : ℂ) - 1)), hK0, hM0, hP, h2t, hexp]
  intro x hx hXi
  have hwpos : (0 : ℝ) < decayW x := decayW_pos x
  have hxpos : (0 : ℝ) < |x| := abs_pos.mpr hx
  have hnorm4 : ‖(4 : ℂ)‖ = 4 := by norm_num
  -- the four regular blocks
  have hpolar := norm_suzukiFrakPPolar_ofReal_le t x
  have hprime := norm_suzukiFrakPPrime_ofReal_le t x
  have hker0 : ‖suzukiLerchKernel 0 ((1 : ℂ) / 4 - I * (x : ℂ) / 2) / 4‖ ≤ (K / 4) * decayW x := by
    rw [norm_div, hnorm4]
    have := hK 0 le_rfl x
    linarith
  have hkerT : ‖((Real.exp (-(t / 2)) : ℝ) : ℂ)
      * suzukiLerchKernel t ((1 : ℂ) / 4 - I * (x : ℂ) / 2) / 4‖
      ≤ (Real.exp (-(t / 2)) * K / 4) * decayW x := by
    rw [mul_div_assoc, norm_mul, norm_div, hnorm4, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    have h1 := hK t ht x
    have h2 : (0 : ℝ) < Real.exp (-(t / 2)) := Real.exp_pos _
    have h3 : Real.exp (-(t / 2)) * (‖suzukiLerchKernel t ((1 : ℂ) / 4 - I * (x : ℂ) / 2)‖ / 4)
        ≤ Real.exp (-(t / 2)) * ((K * decayW x) / 4) := by
      refine mul_le_mul_of_nonneg_left ?_ h2.le
      linarith
    calc Real.exp (-(t / 2)) * (‖suzukiLerchKernel t ((1 : ℂ) / 4 - I * (x : ℂ) / 2)‖ / 4)
        ≤ Real.exp (-(t / 2)) * ((K * decayW x) / 4) := h3
      _ = Real.exp (-(t / 2)) * K / 4 * decayW x := by ring
  -- the singular block
  have hQ : ‖I * (XiC (x : ℂ) / xiHedenmalmDeBrangesESharp (x : ℂ))‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_I, one_mul]
    exact norm_XiC_div_ESharp_le_one x
  have hQ0 : ‖XiC (x : ℂ) / xiHedenmalmDeBrangesESharp (x : ℂ)‖ ≤ 1 :=
    norm_XiC_div_ESharp_le_one x
  have hQ1 : ‖deriv XiC (x : ℂ) / xiHedenmalmDeBrangesESharp (x : ℂ)‖ ≤ 1 :=
    norm_deriv_XiC_div_ESharp_le_one x
  have hS1 : ‖(Complex.exp (-(I * (x : ℂ) * (t : ℂ))) - 1) / (I * (x : ℂ))‖
      ≤ (2 * t + 4) * decayW x := norm_expSlope_le_decayW ht
  have hS2 : ‖(Complex.exp (-(I * (x : ℂ) * (t : ℂ))) - 1) / (I * (x : ℂ))‖ ≤ 2 / |x| :=
    norm_expSlope_le_two_div x t
  have hLa := hM x
  have hZ : ‖I * (deriv XiC (x : ℂ) / xiHedenmalmDeBrangesESharp (x : ℂ))
      - (XiC (x : ℂ) / xiHedenmalmDeBrangesESharp (x : ℂ))
        * logDeriv archFactor ((1 : ℂ) / 2 - I * (x : ℂ))‖
      ≤ 1 + ‖logDeriv archFactor ((1 : ℂ) / 2 - I * (x : ℂ))‖ := by
    refine le_trans (norm_sub_le _ _) ?_
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul]
    have h1 := mul_le_mul_of_nonneg_right hQ0
      (norm_nonneg (logDeriv archFactor ((1 : ℂ) / 2 - I * (x : ℂ))))
    linarith
  have hSZ : ‖I * ((Complex.exp (-(I * (x : ℂ) * (t : ℂ))) - 1) / (I * (x : ℂ))) *
      (I * (deriv XiC (x : ℂ) / xiHedenmalmDeBrangesESharp (x : ℂ))
        - (XiC (x : ℂ) / xiHedenmalmDeBrangesESharp (x : ℂ))
          * logDeriv archFactor ((1 : ℂ) / 2 - I * (x : ℂ)))‖
      ≤ ((2 * t + 4) * (1 + M) + K / 2) * decayW x := by
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul]
    set S : ℝ := ‖(Complex.exp (-(I * (x : ℂ) * (t : ℂ))) - 1) / (I * (x : ℂ))‖ with hSdef
    set Kx : ℝ := ‖suzukiLerchKernel 0 ((1 : ℂ) / 4 - I * (x : ℂ) / 2)‖ with hKxdef
    have hS0 : (0 : ℝ) ≤ S := norm_nonneg _
    have hKx0 : (0 : ℝ) ≤ Kx := norm_nonneg _
    have hpart : S * ‖I * (deriv XiC (x : ℂ) / xiHedenmalmDeBrangesESharp (x : ℂ))
        - (XiC (x : ℂ) / xiHedenmalmDeBrangesESharp (x : ℂ))
          * logDeriv archFactor ((1 : ℂ) / 2 - I * (x : ℂ))‖
        ≤ S * (1 + (M + (|x| / 4) * Kx)) := by
      refine mul_le_mul_of_nonneg_left ?_ hS0
      linarith
    have hmain : S * (1 + (M + (|x| / 4) * Kx))
        ≤ ((2 * t + 4) * (1 + M) + K / 2) * decayW x := by
      have hA : S * (1 + M) ≤ ((2 * t + 4) * decayW x) * (1 + M) :=
        mul_le_mul_of_nonneg_right hS1 (by linarith)
      have hB : S * ((|x| / 4) * Kx) ≤ (2 / |x|) * ((|x| / 4) * Kx) :=
        mul_le_mul_of_nonneg_right hS2 (by positivity)
      have hC : (2 / |x|) * ((|x| / 4) * Kx) = Kx / 2 := by
        field_simp
        ring
      have hD : Kx ≤ K * decayW x := hK 0 le_rfl x
      nlinarith [hA, hB, hD]
    linarith
  -- assemble
  rw [suzukiFrakS_ofReal_decomp t hx hXi]
  have hsplit : ‖I * (XiC (x : ℂ) / xiHedenmalmDeBrangesESharp (x : ℂ)) *
        (suzukiFrakPPolar t (x : ℂ) + suzukiFrakPPrime t (x : ℂ)
          + suzukiLerchKernel 0 ((1 : ℂ) / 4 - I * (x : ℂ) / 2) / 4
          - ((Real.exp (-(t / 2)) : ℝ) : ℂ)
            * suzukiLerchKernel t ((1 : ℂ) / 4 - I * (x : ℂ) / 2) / 4)
      + I * ((Complex.exp (-(I * (x : ℂ) * (t : ℂ))) - 1) / (I * (x : ℂ))) *
          (I * (deriv XiC (x : ℂ) / xiHedenmalmDeBrangesESharp (x : ℂ))
            - (XiC (x : ℂ) / xiHedenmalmDeBrangesESharp (x : ℂ))
              * logDeriv archFactor ((1 : ℂ) / 2 - I * (x : ℂ)))‖
      ≤ ‖I * (XiC (x : ℂ) / xiHedenmalmDeBrangesESharp (x : ℂ))‖ *
          ‖suzukiFrakPPolar t (x : ℂ) + suzukiFrakPPrime t (x : ℂ)
            + suzukiLerchKernel 0 ((1 : ℂ) / 4 - I * (x : ℂ) / 2) / 4
            - ((Real.exp (-(t / 2)) : ℝ) : ℂ)
              * suzukiLerchKernel t ((1 : ℂ) / 4 - I * (x : ℂ) / 2) / 4‖
        + ((2 * t + 4) * (1 + M) + K / 2) * decayW x := by
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_mul]
    linarith
  have hRbound : ‖suzukiFrakPPolar t (x : ℂ) + suzukiFrakPPrime t (x : ℂ)
      + suzukiLerchKernel 0 ((1 : ℂ) / 4 - I * (x : ℂ) / 2) / 4
      - ((Real.exp (-(t / 2)) : ℝ) : ℂ)
        * suzukiLerchKernel t ((1 : ℂ) / 4 - I * (x : ℂ) / 2) / 4‖
      ≤ ((2 * ‖4 * ((Real.exp (t / 2) : ℂ) - 1)‖
          + 2 * ‖4 * ((Real.exp (-(t / 2)) : ℂ) - 1)‖)
        + (∑ n ∈ Finset.Icc 2 ⌊Real.exp t⌋₊, screwPrimeWeight n) * (2 * t + 4)
        + K / 4 + Real.exp (-(t / 2)) * K / 4) * decayW x := by
    have h1 := norm_add_le (suzukiFrakPPolar t (x : ℂ) + suzukiFrakPPrime t (x : ℂ))
      (suzukiLerchKernel 0 ((1 : ℂ) / 4 - I * (x : ℂ) / 2) / 4)
    have h2 := norm_add_le (suzukiFrakPPolar t (x : ℂ)) (suzukiFrakPPrime t (x : ℂ))
    have h3 := norm_sub_le (suzukiFrakPPolar t (x : ℂ) + suzukiFrakPPrime t (x : ℂ)
        + suzukiLerchKernel 0 ((1 : ℂ) / 4 - I * (x : ℂ) / 2) / 4)
      (((Real.exp (-(t / 2)) : ℝ) : ℂ)
        * suzukiLerchKernel t ((1 : ℂ) / 4 - I * (x : ℂ) / 2) / 4)
    nlinarith [h1, h2, h3, hpolar, hprime, hker0, hkerT]
  have hRnn : (0 : ℝ) ≤ ‖suzukiFrakPPolar t (x : ℂ) + suzukiFrakPPrime t (x : ℂ)
      + suzukiLerchKernel 0 ((1 : ℂ) / 4 - I * (x : ℂ) / 2) / 4
      - ((Real.exp (-(t / 2)) : ℝ) : ℂ)
        * suzukiLerchKernel t ((1 : ℂ) / 4 - I * (x : ℂ) / 2) / 4‖ := norm_nonneg _
  nlinarith [hsplit, hRbound, hQ, hRnn, hwpos]

end
end RHTower

namespace RHTower
noncomputable section
open Complex Filter Topology MeasureTheory Set
open GaloisForLFunctions.RHTower

/-! ## An everywhere-measurable model for `𝔖_t` on the real axis -/

theorem continuous_XiC : Continuous XiC :=
  continuous_iff_continuousAt.mpr fun x => (XiC_analytic x (Set.mem_univ x)).continuousAt

theorem digamma_quarterLine_eq (x : ℝ) :
    Complex.digamma ((1 : ℂ) / 4 - I * (x : ℂ) / 2)
      = Complex.digamma (1 / 4 : ℂ)
        - I * (x : ℂ) / 2 * suzukiLerchKernel 0 ((1 : ℂ) / 4 - I * (x : ℂ) / 2) := by
  have hwre : (0 : ℝ) < ((1 : ℂ) / 4 - I * (x : ℂ) / 2).re := by
    rw [quarterLine_re]; norm_num
  have hbridge := digamma_sub_quarter_eq hwre
  have hfac := suzukiLerchDiff_eq (t := 0) hwre
  have hquarter : (1 : ℂ) / 4 - ((1 : ℂ) / 4 - I * (x : ℂ) / 2) = I * (x : ℂ) / 2 := by ring
  rw [hfac, hquarter] at hbridge
  linear_combination hbridge

/-- The archimedean logarithmic derivative on the critical line, written without any Gamma
function: the digamma is traded for the Lerch kernel through the Gauss bridge. -/
def suzukiArchModel (x : ℝ) : ℂ :=
  1 / ((1 : ℂ) / 2 - I * (x : ℂ)) + 1 / ((1 : ℂ) / 2 - I * (x : ℂ) - 1)
    + (-(((Real.log Real.pi : ℝ) : ℂ) / 2)
      + (Complex.digamma (1 / 4 : ℂ)
          - I * (x : ℂ) / 2 * suzukiLerchKernel 0 ((1 : ℂ) / 4 - I * (x : ℂ) / 2)) / 2)

theorem logDeriv_archFactor_eq_archModel (x : ℝ) :
    logDeriv archFactor ((1 : ℂ) / 2 - I * (x : ℂ)) = suzukiArchModel x := by
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
  have hhalf : ((1 : ℂ) / 2 - I * (x : ℂ)) / 2 = (1 : ℂ) / 4 - I * (x : ℂ) / 2 := by ring
  rw [logDeriv_archFactor_closed_off_poles hpole h0 h1,
    GaloisForLFunctions.gammaRealLogConnection, hhalf, digamma_quarterLine_eq, suzukiArchModel]

/-- The measurable model of `𝔖_t` on the real axis. -/
def suzukiFrakSModel (t : ℝ) (x : ℝ) : ℂ :=
  I * (XiC (x : ℂ) / xiHedenmalmDeBrangesESharp (x : ℂ)) *
      (suzukiFrakPPolar t (x : ℂ) + suzukiFrakPPrime t (x : ℂ)
        + suzukiLerchKernel 0 ((1 : ℂ) / 4 - I * (x : ℂ) / 2) / 4
        - ((Real.exp (-(t / 2)) : ℝ) : ℂ)
          * suzukiLerchKernel t ((1 : ℂ) / 4 - I * (x : ℂ) / 2) / 4)
    + I * ((Complex.exp (-(I * (x : ℂ) * (t : ℂ))) - 1) / (I * (x : ℂ))) *
        (I * (deriv XiC (x : ℂ) / xiHedenmalmDeBrangesESharp (x : ℂ))
          - (XiC (x : ℂ) / xiHedenmalmDeBrangesESharp (x : ℂ)) * suzukiArchModel x)

theorem suzukiFrakS_eq_model (t : ℝ) {x : ℝ} (hx : x ≠ 0) (hXi : XiC (x : ℂ) ≠ 0) :
    suzukiFrakS t (x : ℂ) = suzukiFrakSModel t x := by
  rw [suzukiFrakS_ofReal_decomp t hx hXi, suzukiFrakSModel, logDeriv_archFactor_eq_archModel]

theorem measurable_suzukiLerchKernel_vertical (t : ℝ) :
    Measurable (fun x : ℝ => suzukiLerchKernel t ((1 : ℂ) / 4 - I * (x : ℂ) / 2)) := by
  refine Measurable.tsum fun n => ?_
  unfold suzukiLerchKernelTerm
  fun_prop

theorem measurable_suzukiFrakSModel (t : ℝ) : Measurable (suzukiFrakSModel t) := by
  have hX : Measurable (fun x : ℝ => XiC ((x : ℝ) : ℂ)) :=
    continuous_XiC.measurable.comp Complex.measurable_ofReal
  have hD : Measurable (fun x : ℝ => deriv XiC ((x : ℝ) : ℂ)) :=
    (measurable_deriv XiC).comp Complex.measurable_ofReal
  have hE : Measurable (fun x : ℝ => xiHedenmalmDeBrangesESharp ((x : ℝ) : ℂ)) := by
    simp only [xiHedenmalmDeBrangesESharp]
    exact hX.sub (measurable_const.mul hD)
  have hk0 := measurable_suzukiLerchKernel_vertical 0
  have hkt := measurable_suzukiLerchKernel_vertical t
  unfold suzukiFrakSModel suzukiArchModel suzukiFrakPPolar suzukiFrakPPrime
  fun_prop

theorem null_XiC_realZeros :
    volume ({x : ℝ | XiC ((x : ℝ) : ℂ) = 0}) = 0 := by
  have hc : ({x : ℝ | XiC ((x : ℝ) : ℂ) = 0}).Countable := by
    have := XiC_zeroSet_countable.preimage Complex.ofReal_injective
    exact this
  exact hc.measure_zero volume

theorem ae_ne_zero_and_XiC_ne_zero :
    ∀ᵐ x : ℝ, x ≠ 0 ∧ XiC ((x : ℝ) : ℂ) ≠ 0 := by
  have h1 : ∀ᵐ x : ℝ, x ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    simp
  have h2 : ∀ᵐ x : ℝ, XiC ((x : ℝ) : ℂ) ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    simpa using null_XiC_realZeros
  filter_upwards [h1, h2] with x hx1 hx2
  exact ⟨hx1, hx2⟩

/-! ## Suzuki, Proposition 1.2 -/

theorem memLp_decayW (C : ℝ) : MemLp (fun x : ℝ => C * decayW x) 2 volume := by
  have hcont : Continuous fun x : ℝ => decayW x := by
    have hb : Continuous fun x : ℝ => 1 + |x| := by fun_prop
    exact hb.rpow_const fun x => Or.inl (by positivity)
  have hmeas : AEStronglyMeasurable (fun x : ℝ => C * decayW x) volume :=
    (continuous_const.mul hcont).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  have hint : Integrable (fun x : ℝ => (1 + ‖x‖) ^ (-(3 / 2) : ℝ)) volume := by
    refine integrable_one_add_norm ?_
    simp [Module.finrank_self]
    norm_num
  have heq : ∀ x : ℝ, ‖C * decayW x‖ ^ 2 = C ^ 2 * (1 + ‖x‖) ^ (-(3 / 2) : ℝ) := by
    intro x
    have hb : (0 : ℝ) < 1 + |x| := by positivity
    have hsq : (decayW x) ^ 2 = (1 + |x|) ^ (-(3 / 2) : ℝ) := by
      rw [decayW, ← Real.rpow_natCast ((1 + |x|) ^ (-(3 / 4) : ℝ)) 2, ← Real.rpow_mul hb.le]
      norm_num
    have hexp : ‖C * decayW x‖ ^ 2 = C ^ 2 * (decayW x) ^ 2 := by
      rw [Real.norm_eq_abs, abs_mul, mul_pow, sq_abs, sq_abs]
    rw [hexp, hsq, Real.norm_eq_abs]
  refine (hint.const_mul (C ^ 2)).congr ?_
  filter_upwards with x
  rw [heq x]

/-- **Suzuki, Proposition 1.2.**  For every `t ≥ 0` the function `𝔖_t` of eq. (1.5) belongs to
`L²(ℝ)` as a function on the real axis.  Unconditional. -/
theorem memLp_suzukiFrakS {t : ℝ} (ht : 0 ≤ t) :
    MemLp (fun x : ℝ => suzukiFrakS t ((x : ℝ) : ℂ)) 2 volume := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_suzukiFrakS_le ht
  have hnull := ae_ne_zero_and_XiC_ne_zero
  have hae : (fun x : ℝ => suzukiFrakS t ((x : ℝ) : ℂ)) =ᵐ[volume] suzukiFrakSModel t := by
    filter_upwards [hnull] with x hx
    exact suzukiFrakS_eq_model t hx.1 hx.2
  have hmeas : AEStronglyMeasurable (fun x : ℝ => suzukiFrakS t ((x : ℝ) : ℂ)) volume :=
    ((measurable_suzukiFrakSModel t).aestronglyMeasurable).congr hae.symm
  refine (memLp_decayW C).of_le hmeas ?_
  filter_upwards [hnull] with x hx
  have hw : (0 : ℝ) ≤ C * decayW x := mul_nonneg hC0 (decayW_pos x).le
  rw [Real.norm_eq_abs, abs_of_nonneg hw]
  exact hC x hx.1 hx.2

end
end RHTower

