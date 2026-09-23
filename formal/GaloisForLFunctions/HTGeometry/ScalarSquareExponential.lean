import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-!
# The exponential of an element whose square is a negative scalar

In a complete normed complex algebra, an element `M` with `M * M = -(r^(2 : ℕ)) • 1` has scalar even
powers and scalar multiples of itself as odd powers, so the exponential series splits into a cosine
half on the identity and a cardinal sine half on the element:

`exp M = cos r • 1 + sinc r • M`.

Normalizing the odd half by `Real.sinc` makes the statement uniform in `r`, with no separate
degenerate case at `r = 0`.
-/

open scoped BigOperators

namespace HTGeometry

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

omit [CompleteSpace A] in
/-- Even powers of a scalar-square element are scalars. -/
theorem pow_two_mul_of_mul_self_eq (M : A) (r : ℝ)
    (h : M * M = (-((r : ℂ) ^ (2 : ℕ))) • (1 : A)) (k : ℕ) :
    M ^ (2 * k) = ((-((r : ℂ) ^ (2 : ℕ))) ^ k) • (1 : A) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hidx : 2 * (k + 1) = 2 * k + 2 := by ring
      rw [hidx, pow_add, ih, pow_two M, h, smul_mul_smul_comm, one_mul, ← pow_succ]

omit [CompleteSpace A] in
/-- Odd powers of a scalar-square element are scalar multiples of the element. -/
theorem pow_two_mul_add_one_of_mul_self_eq (M : A) (r : ℝ)
    (h : M * M = (-((r : ℂ) ^ (2 : ℕ))) • (1 : A)) (k : ℕ) :
    M ^ (2 * k + 1) = ((-((r : ℂ) ^ (2 : ℕ))) ^ k) • M := by
  rw [pow_succ, pow_two_mul_of_mul_self_eq M r h k, smul_mul_assoc, one_mul]

private theorem hasSum_expTerms (M : A) :
    HasSum (fun n : ℕ => ((n.factorial : ℂ))⁻¹ • M ^ n) (NormedSpace.exp M) :=
  (NormedSpace.expSeries_hasSum_exp (𝕂 := ℂ) M).congr_fun fun n =>
    (NormedSpace.expSeries_apply_eq (𝕂 := ℂ) M n).symm

/-- **The cardinal sine series.**  Dividing the sine series by its argument gives a series with only
even powers, summing to `sinc` at every real point, the origin included. -/
theorem hasSum_sincSeries (r : ℝ) :
    HasSum (fun k : ℕ => (-1 : ℂ) ^ k * (r : ℂ) ^ (2 * k) / ((2 * k + 1).factorial : ℂ))
      ((Real.sinc r : ℝ) : ℂ) := by
  by_cases hr : r = 0
  · subst hr
    have hfun : (fun k : ℕ => (-1 : ℂ) ^ k * ((0 : ℝ) : ℂ) ^ (2 * k) /
        ((2 * k + 1).factorial : ℂ)) = fun k : ℕ => if k = 0 then (1 : ℂ) else 0 := by
      funext k
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · norm_num
      · have h2k : 2 * k ≠ 0 := by omega
        have hk0 : k ≠ 0 := by omega
        simp [hk0, zero_pow h2k]
    have hval : ((Real.sinc (0 : ℝ) : ℝ) : ℂ) = 1 := by simp [Real.sinc]
    rw [hfun, hval]
    simpa using hasSum_ite_eq (0 : ℕ) (1 : ℂ)
  · have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr
    have hval : Complex.sin (r : ℂ) / (r : ℂ) = ((Real.sinc r : ℝ) : ℂ) := by
      rw [← Complex.ofReal_sin, Real.sinc_of_ne_zero hr, Complex.ofReal_div]
    have hsin := (Complex.hasSum_sin (r : ℂ)).div_const (r : ℂ)
    rw [hval] at hsin
    refine hsin.congr_fun fun k => ?_
    have hfac : ((2 * k + 1).factorial : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    field_simp
    ring

/-- **The exponential of a scalar-square element.**  If `M * M = -(r^(2 : ℕ)) • 1` in a complete normed
complex algebra, then `exp M = cos r • 1 + sinc r • M`. -/
theorem exp_of_mul_self_eq_neg_sq_smul_one (M : A) (r : ℝ)
    (h : M * M = (-((r : ℂ) ^ (2 : ℕ))) • (1 : A)) :
    NormedSpace.exp M
      = ((Real.cos r : ℝ) : ℂ) • (1 : A) + ((Real.sinc r : ℝ) : ℂ) • M := by
  have heven : HasSum (fun k : ℕ => (((2 * k).factorial : ℂ))⁻¹ • M ^ (2 * k))
      (((Real.cos r : ℝ) : ℂ) • (1 : A)) := by
    have hcos := (Complex.hasSum_cos (r : ℂ)).smul_const (1 : A)
    rw [← Complex.ofReal_cos] at hcos
    refine hcos.congr_fun fun k => ?_
    rw [pow_two_mul_of_mul_self_eq M r h k, smul_smul, neg_pow, ← pow_mul, div_eq_inv_mul]
  have hodd : HasSum (fun k : ℕ => (((2 * k + 1).factorial : ℂ))⁻¹ • M ^ (2 * k + 1))
      (((Real.sinc r : ℝ) : ℂ) • M) := by
    have hsin := (hasSum_sincSeries r).smul_const M
    refine hsin.congr_fun fun k => ?_
    rw [pow_two_mul_add_one_of_mul_self_eq M r h k, smul_smul, neg_pow, ← pow_mul,
      div_eq_inv_mul]
  exact (hasSum_expTerms M).unique (heven.even_add_odd hodd)

end HTGeometry
