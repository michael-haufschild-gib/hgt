import Mathlib

/-!
# The Cauchy transform of a finite atomic measure is an explicit rational function

A finite weighted sum of Cauchy kernels at distinct nodes clears its common denominator exactly:

`∑ₖ wₖ/(xₖ − z) = (∑ₖ wₖ ∏_{j ≠ k} (x_j − z)) / ∏_j (x_j − z)`.

Both sides are polynomial data in `z` once the nodes and weights are fixed, and the numerator has
degree strictly below the denominator.  This is the finite-stage identity behind the Weyl-disc
description of an indeterminate moment problem: at stage `n` the Cauchy transform of the Gauss
quadrature measure is the ratio of the second-kind polynomial to the orthogonal polynomial, and the
nesting of the discs is a statement about this ratio as the node set grows.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The cleared numerator of a finite weighted Cauchy sum. -/
noncomputable def atomicCauchyNumerator (x w : ι → ℂ) (z : ℂ) : ℂ :=
  ∑ k, w k * ∏ j ∈ Finset.univ.erase k, (x j - z)

/-- The common denominator of a finite weighted Cauchy sum. -/
noncomputable def atomicCauchyDenominator (x : ι → ℂ) (z : ℂ) : ℂ :=
  ∏ j, (x j - z)

omit [DecidableEq ι] in
theorem atomicCauchyDenominator_ne_zero {x : ι → ℂ} {z : ℂ} (hne : ∀ j, x j - z ≠ 0) :
    atomicCauchyDenominator x z ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun j _ => hne j

/-- **Clearing the denominator of a finite weighted Cauchy sum.** -/
theorem sum_div_mul_atomicCauchyDenominator (x w : ι → ℂ) {z : ℂ} (hne : ∀ j, x j - z ≠ 0) :
    (∑ k, w k / (x k - z)) * atomicCauchyDenominator x z = atomicCauchyNumerator x w z := by
  rw [atomicCauchyDenominator, atomicCauchyNumerator, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.mul_prod_erase Finset.univ (fun j => x j - z) (Finset.mem_univ k)]
  have hk : x k - z ≠ 0 := hne k
  rw [mul_comm (x k - z), div_mul_eq_mul_div, ← mul_assoc, mul_div_assoc, div_self hk, mul_one]

/-- **The finite weighted Cauchy sum is an explicit rational function of the evaluation point.** -/
theorem sum_div_eq_atomicCauchy_ratio (x w : ι → ℂ) {z : ℂ} (hne : ∀ j, x j - z ≠ 0) :
    (∑ k, w k / (x k - z))
      = atomicCauchyNumerator x w z / atomicCauchyDenominator x z := by
  rw [eq_div_iff (atomicCauchyDenominator_ne_zero hne)]
  exact sum_div_mul_atomicCauchyDenominator x w hne

/-- The numerator vanishes identically exactly when every weight does, provided the nodes are
distinct: evaluating at a node isolates its weight. -/
theorem weights_eq_zero_of_atomicCauchyNumerator_eq_zero {x w : ι → ℂ}
    (hinj : Function.Injective x) (h : ∀ z, atomicCauchyNumerator x w z = 0) (k : ι) :
    w k = 0 := by
  have hval := h (x k)
  rw [atomicCauchyNumerator, Finset.sum_eq_single k] at hval
  · have hprod : ∏ j ∈ Finset.univ.erase k, (x j - x k) ≠ 0 := by
      refine Finset.prod_ne_zero_iff.mpr fun j hj => ?_
      rw [Finset.mem_erase] at hj
      exact sub_ne_zero.mpr fun hcon => hj.1 (hinj hcon)
    exact (mul_eq_zero.mp hval).resolve_right hprod
  · intro b _ hbk
    have hmem : k ∈ Finset.univ.erase b := Finset.mem_erase.mpr ⟨fun hcon => hbk hcon.symm,
      Finset.mem_univ k⟩
    have : ∏ j ∈ Finset.univ.erase b, (x j - x k) = 0 :=
      Finset.prod_eq_zero hmem (by simp)
    rw [this, mul_zero]
  · intro hcon
    exact absurd (Finset.mem_univ k) hcon

/-! ## The `Finset`-indexed form, for quadrature node sets -/

/-- The cleared numerator over an explicit finite node set. -/
noncomputable def atomicCauchyNumeratorOn (T : Finset ι) (x w : ι → ℂ) (z : ℂ) : ℂ :=
  ∑ k ∈ T, w k * ∏ j ∈ T.erase k, (x j - z)

/-- The common denominator over an explicit finite node set. -/
noncomputable def atomicCauchyDenominatorOn (T : Finset ι) (x : ι → ℂ) (z : ℂ) : ℂ :=
  ∏ j ∈ T, (x j - z)

omit [Fintype ι] [DecidableEq ι] in
theorem atomicCauchyDenominatorOn_ne_zero {T : Finset ι} {x : ι → ℂ} {z : ℂ}
    (hne : ∀ j ∈ T, x j - z ≠ 0) : atomicCauchyDenominatorOn T x z ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr hne

omit [Fintype ι] in
theorem sum_div_mul_atomicCauchyDenominatorOn (T : Finset ι) (x w : ι → ℂ) {z : ℂ}
    (hne : ∀ j ∈ T, x j - z ≠ 0) :
    (∑ k ∈ T, w k / (x k - z)) * atomicCauchyDenominatorOn T x z
      = atomicCauchyNumeratorOn T x w z := by
  rw [atomicCauchyDenominatorOn, atomicCauchyNumeratorOn, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [← Finset.mul_prod_erase T (fun j => x j - z) hk]
  have hkz : x k - z ≠ 0 := hne k hk
  rw [mul_comm (x k - z), div_mul_eq_mul_div, ← mul_assoc, mul_div_assoc, div_self hkz, mul_one]

omit [Fintype ι] in
/-- **Quadrature form.**  Over an explicit finite node set the weighted Cauchy sum is the ratio of
the cleared numerator to `∏_{j ∈ T} (x_j − z)`.  Applied to `T = gaussNodes s n`, `x` the inclusion
of the nodes and `w` the Christoffel weights, this is the finite-stage Cauchy transform of the
Gauss quadrature measure. -/
theorem sum_div_eq_atomicCauchy_ratioOn (T : Finset ι) (x w : ι → ℂ) {z : ℂ}
    (hne : ∀ j ∈ T, x j - z ≠ 0) :
    (∑ k ∈ T, w k / (x k - z))
      = atomicCauchyNumeratorOn T x w z / atomicCauchyDenominatorOn T x z := by
  rw [eq_div_iff (atomicCauchyDenominatorOn_ne_zero hne)]
  exact sum_div_mul_atomicCauchyDenominatorOn T x w hne


end GaloisForLFunctions.HTGeometry
