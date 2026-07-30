import GaloisForLFunctions.RHTower.MobiusMertensEvenConvolutionOrderLaw
import Mathlib.Data.Finset.NatAntidiagonal

/-!
# Mixed additive-convolution law for complex reciprocal coefficients

The even Möbius law uses a real sequence.  Primitive complex Dirichlet characters require the
Hermitian replacement: convolve the `k`-fold additive power with its coefficientwise conjugate.
This module proves the reusable algebraic core.  Every mixed coefficient is real, and its Abel
sum is exactly the squared norm of the corresponding `k`-th power.

No Dirichlet character, zero-abscissa, or GRH assertion is postulated here.
-/

open Complex Filter Set MeasureTheory Asymptotics
open scoped Topology BigOperators

namespace RHTower

noncomputable section

/-- Hermitian mixed additive convolution of the `k`-fold additive power of `a` with its
coefficientwise conjugate. -/
def mixedAdditiveConvolutionPower (a : ℕ → ℂ) (k N : ℕ) : ℂ :=
  ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal (A := ℕ) N,
    additiveConvolutionPower a k ab.1 *
      (starRingEnd ℂ) (additiveConvolutionPower a k ab.2)

private theorem sum_antidiagonal_mixedAdditiveConvolutionPower_weighted_eq
    (a : ℕ → ℂ) (q : ℂ) (k N : ℕ) :
    (∑ ab ∈ Finset.HasAntidiagonal.antidiagonal (A := ℕ) N,
      (additiveConvolutionPower a k ab.1 * q ^ ab.1) *
        ((starRingEnd ℂ) (additiveConvolutionPower a k ab.2) * q ^ ab.2)) =
      mixedAdditiveConvolutionPower a k N * q ^ N := by
  rw [mixedAdditiveConvolutionPower, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ab hab
  have hsum : ab.1 + ab.2 = N :=
    Finset.HasAntidiagonal.mem_antidiagonal.mp hab
  rw [← hsum, pow_add]
  ring_nf

/-- The Hermitian mixed coefficient is fixed by conjugation. -/
theorem star_mixedAdditiveConvolutionPower
    (a : ℕ → ℂ) (k N : ℕ) :
    (starRingEnd ℂ) (mixedAdditiveConvolutionPower a k N) =
      mixedAdditiveConvolutionPower a k N := by
  rw [mixedAdditiveConvolutionPower, map_sum]
  simp only [map_mul, Complex.conj_conj]
  refine Finset.sum_nbij' Prod.swap Prod.swap ?_ ?_ ?_ ?_ ?_
  · intro ab hab
    exact Finset.HasAntidiagonal.mem_antidiagonal.mpr (by
      rw [Prod.swap_prod_mk]
      simpa [add_comm] using Finset.HasAntidiagonal.mem_antidiagonal.mp hab)
  · intro ab hab
    exact Finset.HasAntidiagonal.mem_antidiagonal.mpr (by
      rw [Prod.swap_prod_mk]
      simpa [add_comm] using Finset.HasAntidiagonal.mem_antidiagonal.mp hab)
  · intro ab _
    exact Prod.swap_swap ab
  · intro ab _
    exact Prod.swap_swap ab
  · intro ab _
    rcases ab with ⟨i, j⟩
    simp only [Prod.swap_prod_mk]
    ring

/-- In particular, every Hermitian mixed additive coefficient is real. -/
theorem mixedAdditiveConvolutionPower_im_eq_zero
    (a : ℕ → ℂ) (k N : ℕ) :
    (mixedAdditiveConvolutionPower a k N).im = 0 :=
  Complex.conj_eq_iff_im.mp (star_mixedAdditiveConvolutionPower a k N)

/-- Absolute summability of the mixed Abel series follows from absolute summability of the
original Abel series. -/
theorem summable_norm_mixedAdditiveConvolutionPower_mul_pow
    (a : ℕ → ℂ) (q : ℂ)
    (ha : Summable (fun N : ℕ => ‖a N * q ^ N‖)) (k : ℕ) :
    Summable (fun N : ℕ =>
      ‖mixedAdditiveConvolutionPower a k N * q ^ N‖) := by
  have hp : Summable (fun N : ℕ =>
      ‖additiveConvolutionPower a k N * q ^ N‖) :=
    summable_norm_additiveConvolutionPower_mul_pow a q ha k
  have hpStar : Summable (fun N : ℕ =>
      ‖(starRingEnd ℂ) (additiveConvolutionPower a k N) * q ^ N‖) := by
    convert hp using 1
    funext N
    simp only [norm_mul, RCLike.norm_conj]
  have hconv :=
    summable_norm_sum_mul_antidiagonal_of_summable_norm hp hpStar
  convert hconv using 1
  funext N
  rw [sum_antidiagonal_mixedAdditiveConvolutionPower_weighted_eq]

/-- Exact Hermitian Abel identity.  When `q` is fixed by conjugation (in particular, when it is
real), the mixed generating series is the squared norm of the `k`-th additive power. -/
theorem pow_mul_star_pow_eq_tsum_mixedAdditiveConvolutionPower_mul_pow
    (a : ℕ → ℂ) (q : ℂ)
    (hq : (starRingEnd ℂ) q = q)
    (ha : Summable (fun N : ℕ => ‖a N * q ^ N‖)) (k : ℕ) :
    (∑' N : ℕ, a N * q ^ N) ^ k *
        (starRingEnd ℂ) ((∑' N : ℕ, a N * q ^ N) ^ k) =
      ∑' N : ℕ, mixedAdditiveConvolutionPower a k N * q ^ N := by
  have hp : Summable (fun N : ℕ =>
      ‖additiveConvolutionPower a k N * q ^ N‖) :=
    summable_norm_additiveConvolutionPower_mul_pow a q ha k
  have hpStar : Summable (fun N : ℕ =>
      ‖(starRingEnd ℂ) (additiveConvolutionPower a k N) * q ^ N‖) := by
    convert hp using 1
    funext N
    simp only [norm_mul, RCLike.norm_conj]
  have hpow := tsum_additiveConvolutionPower_mul_pow a q ha k
  have hstar :
      (starRingEnd ℂ)
          (∑' N : ℕ, additiveConvolutionPower a k N * q ^ N) =
        ∑' N : ℕ,
          (starRingEnd ℂ) (additiveConvolutionPower a k N) * q ^ N := by
    rw [Complex.conj_tsum]
    apply tsum_congr
    intro N
    rw [map_mul, map_pow, hq]
  calc
    (∑' N : ℕ, a N * q ^ N) ^ k *
        (starRingEnd ℂ) ((∑' N : ℕ, a N * q ^ N) ^ k) =
        (∑' N : ℕ, additiveConvolutionPower a k N * q ^ N) *
          (∑' N : ℕ,
            (starRingEnd ℂ) (additiveConvolutionPower a k N) * q ^ N) := by
      rw [hpow, hstar]
    _ = ∑' N : ℕ,
        ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal (A := ℕ) N,
        (additiveConvolutionPower a k ab.1 * q ^ ab.1) *
          ((starRingEnd ℂ) (additiveConvolutionPower a k ab.2) * q ^ ab.2) := by
      exact tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hp hpStar
    _ = ∑' N : ℕ, mixedAdditiveConvolutionPower a k N * q ^ N := by
      apply tsum_congr
      intro N
      exact sum_antidiagonal_mixedAdditiveConvolutionPower_weighted_eq a q k N

/-- Norm-squared form of the exact Hermitian Abel identity. -/
theorem norm_sq_pow_eq_re_tsum_mixedAdditiveConvolutionPower_mul_pow
    (a : ℕ → ℂ) (q : ℂ)
    (hq : (starRingEnd ℂ) q = q)
    (ha : Summable (fun N : ℕ => ‖a N * q ^ N‖)) (k : ℕ) :
    ‖(∑' N : ℕ, a N * q ^ N) ^ k‖ ^ 2 =
      (∑' N : ℕ, mixedAdditiveConvolutionPower a k N * q ^ N).re := by
  have h := congrArg Complex.re
    (pow_mul_star_pow_eq_tsum_mixedAdditiveConvolutionPower_mul_pow a q hq ha k)
  rw [Complex.mul_conj'] at h
  norm_cast at h

/-- Generic one-sided comparison for the Hermitian mixed Abel series.  Only upper control of the
real mixed coefficients is used; negative coefficients can be discarded. -/
theorem norm_sq_pow_le_tsum_of_mixedAdditiveConvolutionPower_upper
    (a : ℕ → ℂ) (k : ℕ) (r : ℝ) (hr : 0 ≤ r)
    (ha : Summable (fun N : ℕ => ‖a N * (r : ℂ) ^ N‖))
    (b : ℕ → ℝ)
    (hupper : ∀ N : ℕ, (mixedAdditiveConvolutionPower a k N).re ≤ b N)
    (hb : Summable (fun N : ℕ => b N * r ^ N)) :
    ‖(∑' N : ℕ, a N * (r : ℂ) ^ N) ^ k‖ ^ 2 ≤
      ∑' N : ℕ, b N * r ^ N := by
  have hmixNorm :=
    summable_norm_mixedAdditiveConvolutionPower_mul_pow a (r : ℂ) ha k
  have hmixC : Summable (fun N : ℕ =>
      mixedAdditiveConvolutionPower a k N * (r : ℂ) ^ N) :=
    hmixNorm.of_norm
  have hterm (N : ℕ) :
      (mixedAdditiveConvolutionPower a k N * (r : ℂ) ^ N).re =
        (mixedAdditiveConvolutionPower a k N).re * r ^ N := by
    rw [Complex.mul_re, mixedAdditiveConvolutionPower_im_eq_zero, zero_mul, sub_zero]
    norm_cast
  have hmixR : Summable (fun N : ℕ =>
      (mixedAdditiveConvolutionPower a k N).re * r ^ N) := by
    have hmap := hmixC.map Complex.reCLM Complex.reCLM.continuous
    convert hmap using 1
    funext N
    exact (hterm N).symm
  have hle :
      (∑' N : ℕ, (mixedAdditiveConvolutionPower a k N).re * r ^ N) ≤
        ∑' N : ℕ, b N * r ^ N := by
    apply Summable.tsum_le_tsum (fun N => ?_) hmixR hb
    exact mul_le_mul_of_nonneg_right (hupper N) (pow_nonneg hr N)
  calc
    ‖(∑' N : ℕ, a N * (r : ℂ) ^ N) ^ k‖ ^ 2 =
        (∑' N : ℕ,
          mixedAdditiveConvolutionPower a k N * (r : ℂ) ^ N).re :=
      norm_sq_pow_eq_re_tsum_mixedAdditiveConvolutionPower_mul_pow
        a (r : ℂ) (by simp) ha k
    _ = ∑' N : ℕ,
        (mixedAdditiveConvolutionPower a k N).re * r ^ N := by
      rw [Complex.re_tsum hmixC]
      apply tsum_congr
      exact hterm
    _ ≤ ∑' N : ℕ, b N * r ^ N := hle

/-- At the first mixed order, the coefficient is the explicit quadratic Hermitian convolution. -/
theorem mixedAdditiveConvolutionPower_one
    (a : ℕ → ℂ) (N : ℕ) :
    mixedAdditiveConvolutionPower a 1 N =
      ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal (A := ℕ) N,
        a ab.1 * (starRingEnd ℂ) (a ab.2) := by
  simp only [mixedAdditiveConvolutionPower, additiveConvolutionPower_one]

/-- The `k`-fold additive convolution power is the `N`-th coefficient of the `k`-th power of the
generating power series `∑ a(n) Xⁿ`. -/
theorem additiveConvolutionPower_eq_coeff_pow (a : ℕ → ℂ) (k N : ℕ) :
    additiveConvolutionPower a k N = (PowerSeries.coeff (R := ℂ) N) ((PowerSeries.mk a) ^ k) := by
  induction k generalizing N with
  | zero =>
    rw [pow_zero, PowerSeries.coeff_one]
    simp only [additiveConvolutionPower]
  | succ k ih =>
    rw [additiveConvolutionPower, pow_succ, PowerSeries.coeff_mul]
    refine Finset.sum_congr rfl (fun ab _ => ?_)
    rw [ih ab.1, PowerSeries.coeff_mk]

/-- **Convolution semigroup law.**  The `(m+n)`-fold additive convolution power is the antidiagonal
convolution of the `m`-fold and `n`-fold powers.  Immediate from `pow_add` on the generating
series and the power-series coefficient product. -/
theorem additiveConvolutionPower_add (a : ℕ → ℂ) (m n N : ℕ) :
    additiveConvolutionPower a (m + n) N
      = ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal (A := ℕ) N,
          additiveConvolutionPower a m ab.1 * additiveConvolutionPower a n ab.2 := by
  rw [additiveConvolutionPower_eq_coeff_pow, pow_add, PowerSeries.coeff_mul]
  refine Finset.sum_congr rfl (fun ab _ => ?_)
  rw [additiveConvolutionPower_eq_coeff_pow, additiveConvolutionPower_eq_coeff_pow]

/-- **Zeta specialization: the complex mixed law reduces to the real even law.**  For a real
reciprocal-coefficient sequence (`(a N).im = 0`, the conductor-one/zeta case where the twisted
Mertens function is real), the Hermitian mixed `2k`-convolution equals the plain `2k`-fold even
additive convolution `additiveConvolutionPower a (2 * k)`.  This connects the complex Dirichlet
mixed module to the all-even-order framework of `MobiusMertensEvenConvolutionOrderLaw`: the two
laws coincide exactly on real sequences. -/
theorem mixedAdditiveConvolutionPower_eq_additiveConvolutionPower_two_mul_of_real
    (a : ℕ → ℂ) (ha : ∀ N : ℕ, (a N).im = 0) (k N : ℕ) :
    mixedAdditiveConvolutionPower a k N = additiveConvolutionPower a (2 * k) N := by
  rw [mixedAdditiveConvolutionPower, two_mul, additiveConvolutionPower_add]
  refine Finset.sum_congr rfl (fun ab _ => ?_)
  congr 1
  exact Complex.conj_eq_iff_im.mpr (additiveConvolutionPower_im_eq_zero a ha k ab.2)

end

end RHTower
