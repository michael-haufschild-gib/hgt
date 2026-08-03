import Mathlib

/-!
# Jensen's inequality for the exponential against a discrete probability weighting

For nonnegative weights summing to one,

`exp (∑ p i · x i) ≤ ∑ p i · exp (x i)`.

The proof needs no convexity API: shift by the mean `m = ∑ p i x i`, apply `1 + t ≤ exp t` termwise,
and observe that the linear lower bound sums to exactly one.

The intended use is the comparison of the *mean* index of a power series with its *modal* index.
Weighting `n` by `‖a n‖ r^n` and taking `x n = n log(s/r)`, the inequality says that the majorant
grows at least like `(s/r)` to the mean index, which is the counterpart of the growth law that the
maximum term satisfies with the modal index.
-/

namespace GaloisForLFunctions.HTGeometry

/-- **Discrete Jensen for the exponential.** -/
theorem exp_tsum_mul_le_tsum_mul_exp {ι : Type*} (p x : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hpsum : Summable p) (hp1 : ∑' i, p i = 1)
    (hpx : Summable fun i => p i * x i)
    (hpe : Summable fun i => p i * Real.exp (x i)) :
    Real.exp (∑' i, p i * x i) ≤ ∑' i, p i * Real.exp (x i) := by
  set m : ℝ := ∑' i, p i * x i with hm
  have hexpm : (0 : ℝ) < Real.exp m := Real.exp_pos m
  -- the shifted family
  have hshift : ∀ i, p i * Real.exp (x i) = Real.exp m * (p i * Real.exp (x i - m)) := by
    intro i
    rw [Real.exp_sub]
    field_simp
  have hsum_shift : Summable fun i => p i * Real.exp (x i - m) := by
    refine (hpe.mul_left (Real.exp (-m))).congr fun i => ?_
    rw [Real.exp_sub, Real.exp_neg]
    field_simp
  -- the linear lower bound
  have hpm : Summable fun i => p i * m := hpsum.mul_right m
  have hlin : Summable fun i => p i + (p i * x i - p i * m) :=
    hpsum.add (hpx.sub hpm)
  have hcmp : ∑' i, (p i + (p i * x i - p i * m)) ≤ ∑' i, p i * Real.exp (x i - m) := by
    refine Summable.tsum_le_tsum (fun i => ?_) hlin hsum_shift
    have hexp := Real.add_one_le_exp (x i - m)
    have := mul_le_mul_of_nonneg_left hexp (hp i)
    nlinarith [this, hp i]
  have hone : ∑' i, (p i + (p i * x i - p i * m)) = 1 := by
    rw [Summable.tsum_add hpsum (hpx.sub hpm), Summable.tsum_sub hpx hpm,
      tsum_mul_right, hp1, ← hm]
    ring
  rw [hone] at hcmp
  -- assemble
  have hfinal : ∑' i, p i * Real.exp (x i)
      = Real.exp m * ∑' i, p i * Real.exp (x i - m) := by
    rw [← tsum_mul_left]
    exact tsum_congr hshift
  rw [hfinal]
  calc Real.exp m = Real.exp m * 1 := (mul_one _).symm
    _ ≤ Real.exp m * ∑' i, p i * Real.exp (x i - m) :=
        mul_le_mul_of_nonneg_left hcmp hexpm.le

end GaloisForLFunctions.HTGeometry
