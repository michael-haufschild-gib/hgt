import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Abel-prefix mixed Gamma--Hankel sign law

For `f_x(t) = x² exp (-x*t)`, the normalized Gamma inner product of its
frequency derivatives has kernel `abelPrefixGramKernel δ x y`, where the
Gamma parameter is `5+δ`. The integral identification is proved on paper
in the companion research card; this module closes the exact algebraic
kernel, its quantitative sign geometry, and the finite Abel identity.

The sign law does not bound the Möbius-weighted quadratic form: the
prefixes multiplying these Gram entries retain their arithmetic signs.
-/

namespace RHTower

/-- Scale-ratio polynomial appearing in the mixed derivative Gram. -/
def abelPrefixGramCore (x y : ℝ) : ℝ := 3*x*y-x^2-y^2

/-- Numerator of the mixed derivative Gamma--Hankel kernel. -/
def abelPrefixGramNumerator (δ x y : ℝ) : ℝ :=
  (6+2*δ)*abelPrefixGramCore x y + δ*(1+δ)*(x*y)

theorem abelPrefixGramNumerator_formula (δ x y : ℝ) :
    abelPrefixGramNumerator δ x y =
      (4-2*(5+δ))*(x+y)^2+(5+δ)*(6+δ)*x*y := by
  unfold abelPrefixGramNumerator abelPrefixGramCore
  ring

/-- Within a factor of two, the numerator has a sharp uniform positive margin. -/
theorem abelPrefixGramNumerator_ge_three_mul
    {δ x y : ℝ} (hδ : 0 ≤ δ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxy : x ≤ 2*y) (hyx : y ≤ 2*x) :
    3*x*y ≤ abelPrefixGramNumerator δ x y := by
  have hC : 0 ≤ x*y := mul_nonneg hx hy
  have hp : (x-2*y)*(2*x-y) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  have hA : x*y ≤ 2*abelPrefixGramCore x y := by
    unfold abelPrefixGramCore
    nlinarith
  have hcoeff : 0 ≤ 6+2*δ := by linarith
  have hm := mul_nonneg hcoeff (sub_nonneg.mpr hA)
  have hdc : 0 ≤ δ*(2+δ) := mul_nonneg hδ (by linarith)
  have ht := mul_nonneg hdc hC
  unfold abelPrefixGramNumerator
  nlinarith

/-- Beyond a factor of three, the numerator has a sharp uniform negative margin. -/
theorem abelPrefixGramNumerator_le_neg_two_thirds
    {δ x y : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hy : 0 ≤ y) (hxy : 3*y ≤ x) :
    3*abelPrefixGramNumerator δ x y ≤ -2*x*y := by
  have hx : 0 ≤ x := by linarith
  have hC : 0 ≤ x*y := mul_nonneg hx hy
  have hp : 0 ≤ (x-3*y)*(3*x-y) :=
    mul_nonneg (by linarith) (by linarith)
  have hA : 3*abelPrefixGramCore x y+x*y ≤ 0 := by
    unfold abelPrefixGramCore
    nlinarith
  have hcoeff : 0 ≤ 6+2*δ := by linarith
  have hm := mul_nonpos_of_nonneg_of_nonpos hcoeff hA
  have hd2 : δ^2 ≤ δ := by
    nlinarith [mul_nonneg hδ0 (by linarith : 0 ≤ 1-δ)]
  have hfactor : 3*δ*(1+δ)-(6+2*δ) ≤ -2 := by nlinarith
  have ht := mul_le_mul_of_nonneg_right hfactor hC
  unfold abelPrefixGramNumerator
  nlinarith

/-- The algebraic mixed derivative Gram kernel. -/
noncomputable def abelPrefixGramKernel (δ x y : ℝ) : ℝ :=
  x*y/(x+y)^(7+δ) * abelPrefixGramNumerator δ x y

theorem abelPrefixGramKernel_pos_of_comparable
    {δ x y : ℝ} (hδ : 0 ≤ δ) (hx : 0 < x) (hy : 0 < y)
    (hxy : x ≤ 2*y) (hyx : y ≤ 2*x) :
    0 < abelPrefixGramKernel δ x y := by
  have hB : 0 < abelPrefixGramNumerator δ x y := by
    have h := abelPrefixGramNumerator_ge_three_mul hδ hx.le hy.le hxy hyx
    nlinarith [mul_pos hx hy]
  have hden : 0 < (x+y)^(7+δ) := Real.rpow_pos_of_pos (by linarith) _
  unfold abelPrefixGramKernel
  exact mul_pos (div_pos (mul_pos hx hy) hden) hB

theorem abelPrefixGramKernel_neg_of_separated
    {δ x y : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hy : 0 < y) (hxy : 3*y ≤ x) :
    abelPrefixGramKernel δ x y < 0 := by
  have hx : 0 < x := by linarith
  have hB : abelPrefixGramNumerator δ x y < 0 := by
    have h := abelPrefixGramNumerator_le_neg_two_thirds hδ0 hδ1 hy.le hxy
    nlinarith [mul_pos hx hy]
  have hden : 0 < (x+y)^(7+δ) := Real.rpow_pos_of_pos (by linarith) _
  unfold abelPrefixGramKernel
  exact mul_neg_of_pos_of_neg (div_pos (mul_pos hx hy) hden) hB

/-- Exact finite Abel rewrite, ready for literal Möbius coefficients and Laplace atoms. -/
theorem abelPrefix_finite_identity (a f : ℕ → ℝ) (N : ℕ) :
    (∑ i ∈ Finset.range N, f i * a i) =
      f (N-1) * (∑ i ∈ Finset.range N, a i) -
      ∑ i ∈ Finset.range (N-1),
        (f (i+1)-f i) * (∑ j ∈ Finset.range (i+1), a j) := by
  simpa only [smul_eq_mul] using Finset.sum_range_by_parts f a N

end RHTower
