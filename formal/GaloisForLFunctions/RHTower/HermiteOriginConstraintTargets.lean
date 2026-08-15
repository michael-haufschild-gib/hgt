import GaloisForLFunctions.HTGeometry.HermiteOriginValues
import GaloisForLFunctions.RHTower.ConstraintCoordinateHermiteValues

/-!
# The constrained-prolate coordinate targets are origin values of the Hermite basis

`ConstraintCoordinateHermiteValues` records the four CCM constraint-coordinate targets

```text
2^{1/4} ,   2^{−1/4} ,   √3·2^{−5/4} ,   √5·2^{−7/4}
```

as `√2 · H_n(0)²/(2ⁿ n!)` in squared form, an algebraic identity about the constants alone.  Here
they are identified with the actual analytic object: the value at the origin of the `n`-th member of
the orthonormal Hermite basis built in `HermiteOrthogonality`, in the self-dual normalization
`h_n = p_n · e^{−πx²}` whose Gaussian is a Fourier fixed point.

That is the normalization the constrained-prolate problem produces: the prolate operator at aperture
`λ` scales to the harmonic oscillator with bandwidth `c = 2πλ²`, so the concentration length is
`λ/√c = (2π)^{−1/2}` — an absolute constant — and the limiting profile is exactly `e^{−πx²}`.  The
four quoted constants therefore need no separate `(2π)^{1/4}` bookkeeping factor; they are literally
`|ĥ_n(0)|` for `n = 0, 2, 4, 6`.
-/

open scoped Real

noncomputable section

namespace RHTower

open GaloisForLFunctions

/-! ## Powers of two -/

theorem two_rpow_half : (2 : ℝ) ^ ((1 : ℝ) / 2) = Real.sqrt 2 :=
  (Real.sqrt_eq_rpow 2).symm

theorem two_rpow_sq (a : ℝ) : ((2 : ℝ) ^ a) ^ 2 = (2 : ℝ) ^ (2 * a) := by
  rw [← Real.rpow_natCast ((2 : ℝ) ^ a) 2, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  norm_num
  ring_nf

theorem two_rpow_five_halves : (2 : ℝ) ^ ((5 : ℝ) / 2) = 4 * Real.sqrt 2 := by
  rw [show (5 : ℝ) / 2 = 2 + 1 / 2 by norm_num,
    Real.rpow_add (by norm_num : (0:ℝ) < 2), two_rpow_half]
  norm_num [Real.rpow_natCast]

theorem two_rpow_seven_halves : (2 : ℝ) ^ ((7 : ℝ) / 2) = 8 * Real.sqrt 2 := by
  rw [show (7 : ℝ) / 2 = 3 + 1 / 2 by norm_num,
    Real.rpow_add (by norm_num : (0:ℝ) < 2), two_rpow_half]
  norm_num [Real.rpow_natCast]

/-! ## The four targets -/

/-- A positive number is determined by its square. -/
theorem abs_eq_of_sq_eq_sq {v t : ℝ} (ht : 0 ≤ t) (h : v ^ 2 = t ^ 2) : |v| = t := by
  have hv : |v| ^ 2 = t ^ 2 := by rw [sq_abs]; exact h
  have := congrArg Real.sqrt hv
  rwa [Real.sqrt_sq (abs_nonneg v), Real.sqrt_sq ht] at this

theorem abs_hermiteOriginValue_zero :
    |hermiteOriginValue 0| = (2 : ℝ) ^ ((1 : ℝ) / 4) := by
  refine abs_eq_of_sq_eq_sq (by positivity) ?_
  rw [hermiteOriginValue_sq_zero, two_rpow_sq]
  norm_num
  exact two_rpow_half.symm

theorem abs_hermiteOriginValue_two :
    |hermiteOriginValue 2| = (2 : ℝ) ^ (-(1 : ℝ) / 4) := by
  refine abs_eq_of_sq_eq_sq (by positivity) ?_
  rw [hermiteOriginValue_sq_two, two_rpow_sq]
  have h : (2 : ℝ) ^ (2 * (-(1 : ℝ) / 4)) = ((2 : ℝ) ^ ((1 : ℝ) / 2))⁻¹ := by
    rw [← Real.rpow_neg_one ((2 : ℝ) ^ ((1 : ℝ) / 2)), ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  rw [h, two_rpow_half]
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  field_simp
  linarith [hsq]

theorem abs_hermiteOriginValue_four :
    |hermiteOriginValue 4| = Real.sqrt 3 / (2 : ℝ) ^ ((5 : ℝ) / 4) := by
  refine abs_eq_of_sq_eq_sq (by positivity) ?_
  rw [hermiteOriginValue_sq_four, div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3), two_rpow_sq]
  have h : (2 : ℝ) ^ (2 * ((5 : ℝ) / 4)) = (2 : ℝ) ^ ((5 : ℝ) / 2) := by norm_num
  rw [h, two_rpow_five_halves]
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  field_simp
  linarith [hsq]

theorem abs_hermiteOriginValue_six :
    |hermiteOriginValue 6| = Real.sqrt 5 / (2 : ℝ) ^ ((7 : ℝ) / 4) := by
  refine abs_eq_of_sq_eq_sq (by positivity) ?_
  rw [hermiteOriginValue_sq_six, div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5), two_rpow_sq]
  have h : (2 : ℝ) ^ (2 * ((7 : ℝ) / 4)) = (2 : ℝ) ^ ((7 : ℝ) / 2) := by norm_num
  rw [h, two_rpow_seven_halves]
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  field_simp
  linarith [hsq]

/-! ## Agreement with the recorded squared targets -/

theorem hermiteOriginValue_sq_eq_targetSq_zero :
    hermiteOriginValue 0 ^ 2 = hermiteOriginTargetSq 1 0 := by
  rw [hermiteOriginValue_sq_zero, hermiteOriginTargetSq_zero]

theorem hermiteOriginValue_sq_eq_targetSq_two :
    hermiteOriginValue 2 ^ 2 = hermiteOriginTargetSq (-2) 2 := by
  rw [hermiteOriginValue_sq_two, hermiteOriginTargetSq_two]

theorem hermiteOriginValue_sq_eq_targetSq_four :
    hermiteOriginValue 4 ^ 2 = hermiteOriginTargetSq 12 4 := by
  rw [hermiteOriginValue_sq_four, hermiteOriginTargetSq_four]

theorem hermiteOriginValue_sq_eq_targetSq_six :
    hermiteOriginValue 6 ^ 2 = hermiteOriginTargetSq (-120) 6 := by
  rw [hermiteOriginValue_sq_six, hermiteOriginTargetSq_six]

/-- **The two constrained ground-state seed weights are Hermite origin values.**  Their ratio is the
`8/11` of the CCM two-mode ground state. -/
theorem ccm_seed_weights_eq_hermiteOriginValues :
    |hermiteOriginValue 0| = (2 : ℝ) ^ ((1 : ℝ) / 4) ∧
      |hermiteOriginValue 4| = Real.sqrt 3 / (2 : ℝ) ^ ((5 : ℝ) / 4) :=
  ⟨abs_hermiteOriginValue_zero, abs_hermiteOriginValue_four⟩

end RHTower

end
