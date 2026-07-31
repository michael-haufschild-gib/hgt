import GaloisForLFunctions.RHTower.MobiusLaplacePolylogBoundaryMultiplicity
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
# Additive Möbius triangle behind the discrete Laplace square

The square of the discrete Möbius--Laplace transform is the ordinary generating function of the
additive self-convolution of `mu`.  Cumulative coefficients are triangular sums

`sum_{m+n <= N} mu(m) mu(n)`.

This is the finite arithmetic source isolated by the companion research card.  A linear-polylog
upper bound for those cumulative coefficients would imply the already formalized half-polylog
source criterion.
-/

open Complex Filter Set MeasureTheory Asymptotics
open scoped Topology BigOperators

namespace RHTower

noncomputable section

/-- Möbius coefficient embedded in `ℂ`; its value at zero is already zero. -/
def mobiusComplexCoefficient (n : ℕ) : ℂ :=
  ((ArithmeticFunction.moebius n : ℤ) : ℂ)

/-- Additive self-convolution coefficient `sum_{m+n=k} mu(m)mu(n)`. -/
def mobiusAdditiveConvolution (k : ℕ) : ℂ :=
  ∑ mn ∈ Finset.HasAntidiagonal.antidiagonal (A := ℕ) k,
    mobiusComplexCoefficient mn.1 * mobiusComplexCoefficient mn.2

/-- Cumulative additive self-convolution over the lattice triangle `m+n<=N`. -/
def mobiusAdditiveTriangle (N : ℕ) : ℂ :=
  ∑ k ∈ Finset.range (N + 1), mobiusAdditiveConvolution k

/-- Every complex-embedded Möbius coefficient has norm at most one. -/
theorem norm_mobiusComplexCoefficient_le_one (n : ℕ) :
    ‖mobiusComplexCoefficient n‖ ≤ 1 := by
  rw [mobiusComplexCoefficient, Complex.norm_intCast]
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)

/-- Crude linear bound for one additive-convolution coefficient. -/
theorem norm_mobiusAdditiveConvolution_le (k : ℕ) :
    ‖mobiusAdditiveConvolution k‖ ≤ (k + 1 : ℕ) := by
  rw [mobiusAdditiveConvolution]
  calc
    ‖∑ mn ∈ Finset.HasAntidiagonal.antidiagonal (A := ℕ) k,
        mobiusComplexCoefficient mn.1 * mobiusComplexCoefficient mn.2‖ ≤
        ∑ mn ∈ Finset.HasAntidiagonal.antidiagonal (A := ℕ) k,
          ‖mobiusComplexCoefficient mn.1 * mobiusComplexCoefficient mn.2‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _mn ∈ Finset.HasAntidiagonal.antidiagonal (A := ℕ) k, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro mn _hmn
      rw [norm_mul]
      simpa using mul_le_mul
        (norm_mobiusComplexCoefficient_le_one mn.1)
        (norm_mobiusComplexCoefficient_le_one mn.2)
        (norm_nonneg _) (by norm_num)
    _ = (k + 1 : ℕ) := by simp [Finset.Nat.card_antidiagonal]

/-- Crude quadratic bound for the cumulative additive triangle.  This is only a convergence
majorant; the frontier source conjecture asks for linear-polylog cancellation. -/
theorem norm_mobiusAdditiveTriangle_le (N : ℕ) :
    ‖mobiusAdditiveTriangle N‖ ≤ ((N : ℝ) + 1) ^ 2 := by
  rw [mobiusAdditiveTriangle]
  calc
    ‖∑ k ∈ Finset.range (N + 1), mobiusAdditiveConvolution k‖ ≤
        ∑ k ∈ Finset.range (N + 1), ‖mobiusAdditiveConvolution k‖ :=
      norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range (N + 1), ((k : ℝ) + 1) := by
      apply Finset.sum_le_sum
      intro k _hk
      exact_mod_cast norm_mobiusAdditiveConvolution_le k
    _ ≤ ∑ _k ∈ Finset.range (N + 1), ((N : ℝ) + 1) := by
      apply Finset.sum_le_sum
      intro k hk
      have hkN : k ≤ N := by simpa using Finset.mem_range.mp hk
      exact_mod_cast Nat.add_le_add_right hkN 1
    _ = ((N : ℝ) + 1) ^ 2 := by
      simp
      ring

/-- Additive Möbius convolution coefficients are real. -/
theorem mobiusAdditiveConvolution_im_eq_zero (k : ℕ) :
    (mobiusAdditiveConvolution k).im = 0 := by
  simp [mobiusAdditiveConvolution, mobiusComplexCoefficient, Complex.mul_im]

/-- Cumulative additive Möbius triangles are real. -/
theorem mobiusAdditiveTriangle_im_eq_zero (N : ℕ) :
    (mobiusAdditiveTriangle N).im = 0 := by
  simp [mobiusAdditiveTriangle, mobiusAdditiveConvolution,
    mobiusComplexCoefficient, Complex.mul_im]

/-- Abel summation for a power series, stated with exactly the two summability hypotheses needed
at the boundary between analytic and arithmetic inputs. -/
theorem tsum_mul_pow_eq_one_sub_mul_tsum_partialSums
    {K : Type*} [NormedField K] [CompleteSpace K]
    (c : ℕ → K) (r : K)
    (hc : Summable (fun n : ℕ => c n * r ^ n))
    (hT : Summable (fun N : ℕ =>
      (∑ k ∈ Finset.range (N + 1), c k) * r ^ N)) :
    (∑' n : ℕ, c n * r ^ n) =
      (1 - r) * ∑' N : ℕ,
        (∑ k ∈ Finset.range (N + 1), c k) * r ^ N := by
  let T : ℕ → K := fun N => ∑ k ∈ Finset.range (N + 1), c k
  have hT0 : T 0 = c 0 := by
    simp [T]
  have hTsucc (n : ℕ) : T (n + 1) = T n + c (n + 1) := by
    simp only [T, Finset.sum_range_succ]
  have hshift : Summable (fun n : ℕ => T (n + 1) * r ^ (n + 1)) := by
    exact hT.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  have hrshift : Summable (fun n : ℕ => T n * r ^ (n + 1)) := by
    simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using hT.mul_left r
  have hdiff : Summable (fun n : ℕ => c (n + 1) * r ^ (n + 1)) := by
    have := hshift.sub hrshift
    simpa only [hTsucc, add_mul, add_sub_cancel_left] using this
  rw [hc.tsum_eq_zero_add]
  simp only [pow_zero, mul_one]
  rw [show (∑' n : ℕ, c (n + 1) * r ^ (n + 1)) =
      (∑' n : ℕ, T (n + 1) * r ^ (n + 1)) -
        ∑' n : ℕ, T n * r ^ (n + 1) by
    rw [← hshift.tsum_sub hrshift]
    apply tsum_congr
    intro n
    rw [hTsucc, add_mul, add_sub_cancel_left]]
  rw [show (∑' n : ℕ, T (n + 1) * r ^ (n + 1)) =
      (∑' n : ℕ, T n * r ^ n) - T 0 by
    rw [hT.tsum_eq_zero_add]
    ring]
  rw [show (∑' n : ℕ, T n * r ^ (n + 1)) =
      r * ∑' n : ℕ, T n * r ^ n by
    rw [← hT.tsum_mul_left r]
    apply tsum_congr
    intro n
    rw [pow_succ]
    ring]
  rw [hT0]
  change c 0 + ((∑' n : ℕ, T n * r ^ n) - c 0 -
    r * ∑' n : ℕ, T n * r ^ n) = _
  ring

/-- First differentiated geometric-series identity. -/
theorem tsum_natSucc_mul_pow_eq_inv_sq {r : ℝ} (hr : |r| < 1) :
    (∑' N : ℕ, ((N : ℝ) + 1) * r ^ N) = (1 - r)⁻¹ ^ 2 := by
  have hrnorm : ‖r‖ < 1 := by simpa [Real.norm_eq_abs] using hr
  have hgeom : Summable (fun N : ℕ => r ^ N) :=
    summable_geometric_of_norm_lt_one hrnorm
  have hnat : Summable (fun N : ℕ => (N : ℝ) * r ^ N) := by
    simpa only [pow_one] using
      summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hrnorm
  have hsucc : Summable (fun N : ℕ => ((N : ℝ) + 1) * r ^ N) := by
    simpa only [add_mul, one_mul] using hnat.add hgeom
  have habel := tsum_mul_pow_eq_one_sub_mul_tsum_partialSums
    (fun _ : ℕ => (1 : ℝ)) r (by simpa using hgeom) (by
      simpa [Finset.sum_const, Finset.card_range] using hsucc)
  have hrne : 1 - r ≠ 0 := by
    have : r < 1 := lt_of_abs_lt hr
    linarith
  simp only [one_mul, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_one, mul_one] at habel
  rw [tsum_geometric_of_norm_lt_one hrnorm] at habel
  field_simp [hrne] at habel ⊢
  nlinarith

private theorem sum_antidiagonal_mobiusDiscreteLaplaceTerm_eq
    (x : ℝ) (k : ℕ) :
    (∑ mn ∈ Finset.HasAntidiagonal.antidiagonal (A := ℕ) k,
      mobiusDiscreteLaplaceTerm x mn.1 * mobiusDiscreteLaplaceTerm x mn.2) =
      mobiusAdditiveConvolution k * Complex.exp (-((k : ℝ) * x : ℝ)) := by
  rw [mobiusAdditiveConvolution, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro mn hmn
  have hsum : mn.1 + mn.2 = k :=
    Finset.HasAntidiagonal.mem_antidiagonal.mp hmn
  rw [mobiusDiscreteLaplaceTerm, mobiusDiscreteLaplaceTerm]
  change (mobiusComplexCoefficient mn.1 *
      Complex.exp (-((mn.1 : ℝ) * x : ℝ))) *
      (mobiusComplexCoefficient mn.2 *
        Complex.exp (-((mn.2 : ℝ) * x : ℝ))) = _
  have hexp : Complex.exp (-((mn.1 : ℝ) * x : ℝ)) *
      Complex.exp (-((mn.2 : ℝ) * x : ℝ)) =
      Complex.exp (-((k : ℝ) * x : ℝ)) := by
    rw [← Complex.exp_add]
    congr 1
    norm_cast
    have hsumR : (mn.1 : ℝ) + (mn.2 : ℝ) = (k : ℝ) := by
      exact_mod_cast hsum
    rw [← hsumR]
    ring
  rw [← hexp]
  ring

/-- The additive-convolution exponential series is absolutely summable at every positive scale. -/
theorem summable_additiveConvolution_mul_exp_neg_nat
    {x : ℝ} (hx : 0 < x) :
    Summable (fun k : ℕ => mobiusAdditiveConvolution k *
      Complex.exp (-((k : ℝ) * x : ℝ))) := by
  have hnorm : Summable (fun n : ℕ => ‖mobiusDiscreteLaplaceTerm x n‖) :=
    (summable_mobiusDiscreteLaplaceTerm hx).norm
  have hconv := summable_norm_sum_mul_antidiagonal_of_summable_norm hnorm hnorm
  apply Summable.of_norm
  exact hconv.congr (fun k => by
    rw [sum_antidiagonal_mobiusDiscreteLaplaceTerm_eq])

/-- Exponential weights at integral multiples are geometric powers. -/
theorem exp_neg_nat_mul_eq_pow (x : ℝ) (k : ℕ) :
    Complex.exp (-((k : ℝ) * x : ℝ)) =
      Complex.exp (-(x : ℂ)) ^ k := by
  rw [← Complex.exp_nat_mul]
  congr 1
  norm_cast
  ring

/-- Norm of the geometric exponential weight. -/
theorem norm_exp_neg_pow_eq (x : ℝ) (N : ℕ) :
    ‖Complex.exp (-(x : ℂ)) ^ N‖ = Real.exp (-((N : ℝ) * x)) := by
  rw [norm_pow, Complex.norm_exp]
  change Real.exp (-x) ^ N = _
  rw [← Real.exp_nat_mul]
  congr 1
  ring

/-- Real part of a weighted triangle term. -/
theorem mobiusAdditiveTriangle_mul_exp_pow_re_eq (x : ℝ) (N : ℕ) :
    (mobiusAdditiveTriangle N * Complex.exp (-(x : ℂ)) ^ N).re =
      (mobiusAdditiveTriangle N).re * Real.exp (-x) ^ N := by
  have hexp : Complex.exp (-(x : ℂ)) = (Real.exp (-x) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    norm_cast
  rw [Complex.mul_re, mobiusAdditiveTriangle_im_eq_zero, zero_mul, sub_zero]
  congr 1
  have hp := congrArg (fun z : ℂ => (z ^ N).re) hexp
  calc
    (Complex.exp (-(x : ℂ)) ^ N).re =
        (((Real.exp (-x) : ℝ) : ℂ) ^ N).re := hp
    _ = Real.exp (-x) ^ N := by norm_cast

/-- Quadratic coefficient growth is enough to make the additive-triangle Abel series converge at
every positive Laplace scale. -/
theorem summable_mobiusAdditiveTriangle_mul_exp_neg
    {x : ℝ} (hx : 0 < x) :
    Summable (fun N : ℕ => mobiusAdditiveTriangle N *
      Complex.exp (-(x : ℂ)) ^ N) := by
  have h0 := summable_pow_mul_exp_neg 0 hx
  have h1 := summable_pow_mul_exp_neg 1 hx
  have h2 := summable_pow_mul_exp_neg 2 hx
  have hmajor : Summable (fun N : ℕ =>
      (((N : ℝ) + 1) ^ 2) * Real.exp (-((N : ℝ) * x))) := by
    have hs := h2.add ((h1.mul_left 2).add h0)
    convert hs using 1
    funext N
    ring
  apply Summable.of_norm
  refine Summable.of_nonneg_of_le (fun N => norm_nonneg _) (fun N => ?_) hmajor
  rw [norm_mul, norm_exp_neg_pow_eq]
  exact mul_le_mul_of_nonneg_right
    (norm_mobiusAdditiveTriangle_le N) (Real.exp_pos _).le

/-- The discrete Möbius--Laplace square is exactly the exponential generating series of its
additive-convolution coefficients. -/
theorem mobiusDiscreteLaplaceTransform_sq_eq_tsum_additiveConvolution
    {x : ℝ} (hx : 0 < x) :
    mobiusDiscreteLaplaceTransform x * mobiusDiscreteLaplaceTransform x =
      ∑' k : ℕ, mobiusAdditiveConvolution k *
        Complex.exp (-((k : ℝ) * x : ℝ)) := by
  have hnorm : Summable (fun n : ℕ => ‖mobiusDiscreteLaplaceTerm x n‖) :=
    (summable_mobiusDiscreteLaplaceTerm hx).norm
  rw [mobiusDiscreteLaplaceTransform,
    tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hnorm hnorm]
  apply tsum_congr
  exact sum_antidiagonal_mobiusDiscreteLaplaceTerm_eq x

/-- Exact Abel bridge from the cumulative additive Möbius triangle to the square of the discrete
Laplace transform.  The remaining hypothesis is only convergence of the triangle series. -/
theorem mobiusDiscreteLaplaceTransform_sq_eq_one_sub_exp_mul_tsum_additiveTriangle_of_summable
    {x : ℝ} (hx : 0 < x)
    (htriangle : Summable (fun N : ℕ => mobiusAdditiveTriangle N *
      Complex.exp (-(x : ℂ)) ^ N)) :
    mobiusDiscreteLaplaceTransform x * mobiusDiscreteLaplaceTransform x =
      (1 - Complex.exp (-(x : ℂ))) *
        ∑' N : ℕ, mobiusAdditiveTriangle N * Complex.exp (-(x : ℂ)) ^ N := by
  have hconv : Summable (fun k : ℕ => mobiusAdditiveConvolution k *
      Complex.exp (-(x : ℂ)) ^ k) := by
    simpa only [exp_neg_nat_mul_eq_pow] using
      summable_additiveConvolution_mul_exp_neg_nat hx
  calc
    mobiusDiscreteLaplaceTransform x * mobiusDiscreteLaplaceTransform x =
        ∑' k : ℕ, mobiusAdditiveConvolution k *
          Complex.exp (-((k : ℝ) * x : ℝ)) :=
      mobiusDiscreteLaplaceTransform_sq_eq_tsum_additiveConvolution hx
    _ = ∑' k : ℕ, mobiusAdditiveConvolution k *
          Complex.exp (-(x : ℂ)) ^ k := by
      apply tsum_congr
      intro k
      rw [exp_neg_nat_mul_eq_pow]
    _ = (1 - Complex.exp (-(x : ℂ))) *
        ∑' N : ℕ, mobiusAdditiveTriangle N *
          Complex.exp (-(x : ℂ)) ^ N := by
      simpa only [mobiusAdditiveTriangle] using
        tsum_mul_pow_eq_one_sub_mul_tsum_partialSums
          mobiusAdditiveConvolution (Complex.exp (-(x : ℂ))) hconv htriangle

/-- Unconditional exact Abel identity for the additive Möbius triangle. -/
theorem mobiusDiscreteLaplaceTransform_sq_eq_one_sub_exp_mul_tsum_additiveTriangle
    {x : ℝ} (hx : 0 < x) :
    mobiusDiscreteLaplaceTransform x * mobiusDiscreteLaplaceTransform x =
      (1 - Complex.exp (-(x : ℂ))) *
        ∑' N : ℕ, mobiusAdditiveTriangle N * Complex.exp (-(x : ℂ)) ^ N :=
  mobiusDiscreteLaplaceTransform_sq_eq_one_sub_exp_mul_tsum_additiveTriangle_of_summable
    hx (summable_mobiusAdditiveTriangle_mul_exp_neg hx)

/-- One-sided linear cancellation in the cumulative additive Möbius triangle.  Unlike an absolute
bound, only the upper sign is needed because the corresponding Abel sum is a real square. -/
def MobiusAdditiveTriangleLinearUpperBound : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
    (mobiusAdditiveTriangle N).re ≤ C * ((N : ℝ) + 1)

/-- A one-sided linear triangle bound controls the square of the Möbius--Laplace transform by one
geometric pole. -/
theorem norm_sq_mobiusDiscreteLaplaceTransform_le_of_additiveTriangleLinearUpperBound
    {C : ℝ}
    (hupper : ∀ N : ℕ,
      (mobiusAdditiveTriangle N).re ≤ C * ((N : ℝ) + 1))
    {x : ℝ} (hx : 0 < x) :
    ‖mobiusDiscreteLaplaceTransform x‖ ^ 2 ≤
      C * (1 - Real.exp (-x))⁻¹ := by
  let r : ℝ := Real.exp (-x)
  have hrPos : 0 < r := Real.exp_pos _
  have hrLt : r < 1 := by
    dsimp [r]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hrAbs : |r| < 1 := by rw [abs_of_pos hrPos]; exact hrLt
  have hrNorm : ‖r‖ < 1 := by simpa [Real.norm_eq_abs] using hrAbs
  have htriangleC := summable_mobiusAdditiveTriangle_mul_exp_neg hx
  have htriangleR : Summable (fun N : ℕ =>
      (mobiusAdditiveTriangle N).re * r ^ N) := by
    have hmap := htriangleC.map Complex.reCLM Complex.reCLM.continuous
    convert hmap using 1
    funext N
    simpa [Function.comp_def, r] using
      (mobiusAdditiveTriangle_mul_exp_pow_re_eq x N).symm
  have hgeom : Summable (fun N : ℕ => r ^ N) :=
    summable_geometric_of_norm_lt_one hrNorm
  have hnat : Summable (fun N : ℕ => (N : ℝ) * r ^ N) := by
    simpa only [pow_one] using
      summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hrNorm
  have hsucc : Summable (fun N : ℕ => ((N : ℝ) + 1) * r ^ N) := by
    simpa only [add_mul, one_mul] using hnat.add hgeom
  have hmajor : Summable (fun N : ℕ => C * ((N : ℝ) + 1) * r ^ N) := by
    simpa only [mul_assoc] using hsucc.mul_left C
  have htsumLe :
      (∑' N : ℕ, (mobiusAdditiveTriangle N).re * r ^ N) ≤
        ∑' N : ℕ, C * ((N : ℝ) + 1) * r ^ N := by
    apply Summable.tsum_le_tsum (fun N => ?_) htriangleR hmajor
    exact mul_le_mul_of_nonneg_right (hupper N) (pow_nonneg hrPos.le N)
  have hmajorEq :
      (∑' N : ℕ, C * ((N : ℝ) + 1) * r ^ N) =
        C * (1 - r)⁻¹ ^ 2 := by
    calc
      (∑' N : ℕ, C * ((N : ℝ) + 1) * r ^ N) =
          ∑' N : ℕ, C * (((N : ℝ) + 1) * r ^ N) := by
        apply tsum_congr
        intro N
        ring
      _ = C * ∑' N : ℕ, ((N : ℝ) + 1) * r ^ N := hsucc.tsum_mul_left C
      _ = C * (1 - r)⁻¹ ^ 2 := by rw [tsum_natSucc_mul_pow_eq_inv_sq hrAbs]
  have hleft :
      (mobiusDiscreteLaplaceTransform x * mobiusDiscreteLaplaceTransform x).re =
        ‖mobiusDiscreteLaplaceTransform x‖ ^ 2 := by
    rw [Complex.mul_re, mobiusDiscreteLaplaceTransform_im_eq_zero hx,
      zero_mul, sub_zero, Complex.sq_norm, Complex.normSq_apply,
      mobiusDiscreteLaplaceTransform_im_eq_zero hx]
    ring
  have hright :
      ((1 - Complex.exp (-(x : ℂ))) *
        ∑' N : ℕ, mobiusAdditiveTriangle N * Complex.exp (-(x : ℂ)) ^ N).re =
      (1 - r) * ∑' N : ℕ, (mobiusAdditiveTriangle N).re * r ^ N := by
    rw [Complex.mul_re]
    have haRe : (1 - Complex.exp (-(x : ℂ))).re = 1 - r := by
      dsimp [r]
      rw [show -(x : ℂ) = ((-x : ℝ) : ℂ) by norm_num, Complex.exp_ofReal_re]
    have haIm : (1 - Complex.exp (-(x : ℂ))).im = 0 := by
      simp only [Complex.sub_im, Complex.one_im]
      rw [show -(x : ℂ) = ((-x : ℝ) : ℂ) by norm_num, Complex.exp_ofReal_im]
      ring
    rw [haRe, haIm, zero_mul, sub_zero, Complex.re_tsum htriangleC]
    congr 1
    apply tsum_congr
    intro N
    exact mobiusAdditiveTriangle_mul_exp_pow_re_eq x N
  have heq : ‖mobiusDiscreteLaplaceTransform x‖ ^ 2 =
      (1 - r) * ∑' N : ℕ, (mobiusAdditiveTriangle N).re * r ^ N := by
    calc
      ‖mobiusDiscreteLaplaceTransform x‖ ^ 2 =
          (mobiusDiscreteLaplaceTransform x * mobiusDiscreteLaplaceTransform x).re := hleft.symm
      _ = ((1 - Complex.exp (-(x : ℂ))) *
          ∑' N : ℕ, mobiusAdditiveTriangle N *
            Complex.exp (-(x : ℂ)) ^ N).re := by
        rw [mobiusDiscreteLaplaceTransform_sq_eq_one_sub_exp_mul_tsum_additiveTriangle hx]
      _ = (1 - r) * ∑' N : ℕ,
          (mobiusAdditiveTriangle N).re * r ^ N := hright
  rw [heq]
  calc
    (1 - r) * (∑' N : ℕ, (mobiusAdditiveTriangle N).re * r ^ N) ≤
        (1 - r) * (∑' N : ℕ, C * ((N : ℝ) + 1) * r ^ N) :=
      mul_le_mul_of_nonneg_left htsumLe (sub_nonneg.mpr hrLt.le)
    _ = (1 - r) * (C * (1 - r)⁻¹ ^ 2) := by rw [hmajorEq]
    _ = C * (1 - r)⁻¹ := by
      have hrne : 1 - r ≠ 0 := sub_ne_zero.mpr hrLt.ne'
      field_simp [hrne]
    _ = C * (1 - Real.exp (-x))⁻¹ := by rfl

/-- Elementary lower bound converting the geometric pole to the Laplace half-power scale. -/
theorem half_mul_le_one_sub_exp_neg {x : ℝ} (hx : 0 < x) (hxOne : x ≤ 1) :
    x / 2 ≤ 1 - Real.exp (-x) := by
  have hInv : Real.exp (-x) ≤ (1 + x)⁻¹ := by
    rw [Real.exp_neg]
    exact (inv_le_inv₀ (Real.exp_pos x) (by linarith)).2 (by
      simpa [add_comm] using Real.add_one_le_exp x)
  have hfrac : x / 2 ≤ 1 - (1 + x)⁻¹ := by
    have hxadd : 0 < 1 + x := by linarith
    rw [inv_eq_one_div]
    field_simp [ne_of_gt hxadd]
    nlinarith
  linarith

/-- **One-sided additive-triangle source theorem.** A linear upper bound, without any lower or
absolute bound, yields exact critical half-decay. -/
theorem mobiusAdditiveTriangleLinearUpperBound_implies_halfDecay
    (hupper : MobiusAdditiveTriangleLinearUpperBound) :
    MobiusDiscreteLaplaceHalfPolylogDecay 0 := by
  rcases hupper with ⟨C, hC, hsource⟩
  refine ⟨Real.sqrt (2 * C), 1, Real.sqrt_nonneg _, zero_lt_one, ?_⟩
  intro x hx hxOne
  have hsq :=
    norm_sq_mobiusDiscreteLaplaceTransform_le_of_additiveTriangleLinearUpperBound
      hsource hx
  have hdenPos : 0 < 1 - Real.exp (-x) := by
    exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  have hhalf := half_mul_le_one_sub_exp_neg hx hxOne.le
  have hinv : (1 - Real.exp (-x))⁻¹ ≤ (x / 2)⁻¹ :=
    (inv_le_inv₀ hdenPos (half_pos hx)).2 hhalf
  have hsq' : ‖mobiusDiscreteLaplaceTransform x‖ ^ 2 ≤ 2 * C * x⁻¹ := by
    calc
      ‖mobiusDiscreteLaplaceTransform x‖ ^ 2 ≤
          C * (1 - Real.exp (-x))⁻¹ := hsq
      _ ≤ C * (x / 2)⁻¹ := mul_le_mul_of_nonneg_left hinv hC
      _ = 2 * C * x⁻¹ := by field_simp
  have hrpowSq : (x ^ (-(1 / 2 : ℝ))) ^ 2 = x⁻¹ := by
    calc
      (x ^ (-(1 / 2 : ℝ))) ^ 2 =
          (x ^ (-(1 / 2 : ℝ))) ^ (2 : ℝ) :=
        (Real.rpow_natCast (x ^ (-(1 / 2 : ℝ))) 2).symm
      _ = x ^ (-(1 / 2 : ℝ) * 2) :=
        (Real.rpow_mul hx.le (-(1 / 2 : ℝ)) 2).symm
      _ = x ^ (-1 : ℝ) := by ring_nf
      _ = x⁻¹ := Real.rpow_neg_one x
  have hboundNonneg :
      0 ≤ Real.sqrt (2 * C) * x ^ (-(1 / 2 : ℝ)) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hx.le _)
  have hboundSq :
      (Real.sqrt (2 * C) * x ^ (-(1 / 2 : ℝ))) ^ 2 = 2 * C * x⁻¹ := by
    rw [mul_pow, Real.sq_sqrt (mul_nonneg (by norm_num) hC), hrpowSq]
  have hnorm := norm_nonneg (mobiusDiscreteLaplaceTransform x)
  have : ‖mobiusDiscreteLaplaceTransform x‖ ≤
      Real.sqrt (2 * C) * x ^ (-(1 / 2 : ℝ)) := by
    nlinarith
  simpa [mobiusLaplaceHalfPolylogKernel] using this

/-- The degree-zero polylog presentation is the original exact half-power interface.  Thus the
one-sided additive-triangle source discharges `MobiusDiscreteLaplaceHalfDecay` itself, rather than
only a parametrized surrogate. -/
theorem mobiusAdditiveTriangleLinearUpperBound_implies_discreteLaplaceHalfDecay
    (hupper : MobiusAdditiveTriangleLinearUpperBound) :
    MobiusDiscreteLaplaceHalfDecay := by
  obtain ⟨C, delta, hC, hdelta, hbound⟩ :=
    mobiusAdditiveTriangleLinearUpperBound_implies_halfDecay hupper
  exact ⟨C, delta, hC, hdelta, fun x hx hxd => by
    simpa [mobiusLaplaceHalfPolylogKernel] using hbound x hx hxd⟩

/-- A one-sided linear additive-triangle bound implies RH. -/
theorem mobiusAdditiveTriangleLinearUpperBound_implies_riemannHypothesis
    (hupper : MobiusAdditiveTriangleLinearUpperBound) : RiemannHypothesis :=
  mobiusDiscreteLaplaceHalfPolylogDecay_implies_riemannHypothesis
    (mobiusAdditiveTriangleLinearUpperBound_implies_halfDecay hupper)

/-- The same source condition also forces every critical-line zeta zero to be simple. -/
theorem mobiusAdditiveTriangleLinearUpperBound_implies_riemannHypothesis_and_simpleZeros
    (hupper : MobiusAdditiveTriangleLinearUpperBound) :
    RiemannHypothesis ∧
      ∀ rho : ℂ, rho.re = 1 / 2 → riemannZeta rho = 0 →
        (analyticOrderAt riemannZeta rho).toNat ≤ 1 := by
  simpa using
    mobiusDiscreteLaplaceHalfPolylogDecay_implies_riemannHypothesis_and_multiplicityCap
      (mobiusAdditiveTriangleLinearUpperBound_implies_halfDecay hupper)

end

end RHTower
