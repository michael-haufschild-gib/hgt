import Mathlib

/-!
# Energy bound from bounded Satake parameters

A sum of `d` complex numbers of modulus at most one has modulus at most `d`, with equality only when
every summand has modulus exactly one.  Squaring and weighting gives, for a coefficient sequence of
the form `a p = ∑_{j<d} α j p` with `‖α j p‖ ≤ 1`,

```text
∑_{p ∈ s} ‖a p‖² w p ≤ d² ∑_{p ∈ s} w p     for any nonnegative weight w .
```

For an element of the Selberg class possessing a polynomial Euler product of local degree at most `d`
with Satake parameters bounded by one, this reads `∑_{p ≤ x}|a_F(p)|²/p ≤ d² ∑_{p≤x} 1/p`, so the
prime energy density is at most `d²`; equality would force all Satake parameters at a prime to
coincide and be unimodular, which happens only for a `d`-th power of a degree-one element.
-/

open Finset

namespace HTGeometry

/-- A sum of `card ι` complex numbers of modulus at most one has modulus at most `card ι`. -/
theorem norm_sum_le_card {ι : Type*} [Fintype ι] (v : ι → ℂ) (hle : ∀ i, ‖v i‖ ≤ 1) :
    ‖∑ i, v i‖ ≤ (Fintype.card ι : ℝ) := by
  calc ‖∑ i, v i‖ ≤ ∑ i, ‖v i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : ι, (1 : ℝ) := Finset.sum_le_sum fun i _ => hle i
    _ = (Fintype.card ι : ℝ) := by simp [Finset.card_univ]

/-- **Rigidity of the equality case.**  If the modulus of the sum attains `card ι`, every summand has
modulus exactly one. -/
theorem norm_eq_one_of_norm_sum_eq_card {ι : Type*} [Fintype ι] (v : ι → ℂ)
    (hle : ∀ i, ‖v i‖ ≤ 1) (h : ‖∑ i, v i‖ = (Fintype.card ι : ℝ)) :
    ∀ i, ‖v i‖ = 1 := by
  have h1 : ‖∑ i, v i‖ ≤ ∑ i, ‖v i‖ := norm_sum_le _ _
  have h2 : ∑ i, ‖v i‖ ≤ (Fintype.card ι : ℝ) := by
    calc ∑ i, ‖v i‖ ≤ ∑ _i : ι, (1 : ℝ) := Finset.sum_le_sum fun i _ => hle i
      _ = (Fintype.card ι : ℝ) := by simp [Finset.card_univ]
  have hsum : ∑ i, ‖v i‖ = (Fintype.card ι : ℝ) := le_antisymm h2 (by rw [← h]; exact h1)
  have hzero : ∑ i, (1 - ‖v i‖) = 0 := by
    rw [Finset.sum_sub_distrib, hsum]
    simp [Finset.card_univ]
  intro i
  have hnn : ∀ j ∈ (Finset.univ : Finset ι), 0 ≤ 1 - ‖v j‖ := fun j _ => by
    linarith [hle j]
  have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hzero i (Finset.mem_univ i)
  linarith

/-- **Weighted energy bound.**  With `‖a p‖ ≤ D` on the index set and a nonnegative weight, the
weighted square sum is at most `D²` times the weight total. -/
theorem weighted_sq_le {ι : Type*} (s : Finset ι) (a : ι → ℂ) (w : ι → ℝ) (D : ℝ)
    (hD : 0 ≤ D) (hw : ∀ i ∈ s, 0 ≤ w i) (ha : ∀ i ∈ s, ‖a i‖ ≤ D) :
    ∑ i ∈ s, ‖a i‖ ^ 2 * w i ≤ D ^ 2 * ∑ i ∈ s, w i := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  have h1 : ‖a i‖ ^ 2 ≤ D ^ 2 := by
    have := ha i hi
    nlinarith [norm_nonneg (a i), hD]
  exact mul_le_mul_of_nonneg_right h1 (hw i hi)

end HTGeometry
