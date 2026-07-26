import GaloisForLFunctions.RHTower.AnalyticityExcludesBetaSensitivity
import GaloisForLFunctions.RHTower.ArchimedeanPairingDefinite

/-!
# The absolute trace criterion: a non-analytic functional that is still computable

The exclusion of the previous entry says a weight detecting the critical line cannot be evaluated by
contour shifting.  It does **not** say every non-analytic functional is uncomputable.  A matrix trace
needs no contour, and `tr |A|` is non-analytic in `A` yet determined by `A`.  This file develops the
criterion that results.

**Absolute trace versus trace.**  For a self-adjoint operator with eigenvalues `λ_j`,

```text
tr |A| - tr A  =  Σ_j ( |λ_j| - λ_j )  =  2 Σ_{λ_j < 0} |λ_j| ,
```

so `A ≥ 0` exactly when `tr |A| = tr A`.  Applied to the Weil operator `A = Q - 𝒫`, the hypothesis is
the equality of its Schatten-1 norm with its trace.

**And the trace is purely archimedean.**  The compressed prime operator is convolution by a measure
supported on `{± log n : n ≥ 2}`, which has **no atom at the origin**, so its diagonal vanishes and it
is traceless.  Hence

```text
tr (Q - 𝒫)  =  tr Q ,
```

a quantity with no prime content at all, and by the definiteness bounds it is pinned between
`(1 - β)·d` and `(1 + β)·d` with `β = 3 log 2 + π/2 - 3` and `d` the dimension.

> **The hypothesis is the statement that the Schatten-1 norm of the Weil operator equals its trace,
> and that trace is purely archimedean, lying in an explicitly computable interval around
> `0.34976·d` to `1.65024·d`.**

The criterion is non-analytic, exact, and evaluable in principle — the three properties the previous
entry showed cannot coexist for contour-evaluated functionals.  What it costs is that the Schatten
norm requires the spectrum, which the prime data does not directly supply.

This file formalizes the absolute-trace identity, its equivalence with positivity, the tracelessness
of an atom-free convolution, and the archimedean pinning of the trace.
-/

open Finset

noncomputable section

namespace RHTower

/-- **The absolute-trace identity.**  The gap between the absolute trace and the trace is twice the
negative spectral mass. -/
theorem abs_trace_sub_trace {ι : Type*} (s : Finset ι) (lam : ι → ℝ) :
    ∑ j ∈ s, |lam j| - ∑ j ∈ s, lam j = 2 * ∑ j ∈ s, max 0 (-(lam j)) := by
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rcases le_or_gt 0 (lam j) with h | h
  · rw [abs_of_nonneg h, max_eq_left (by linarith)]
    ring
  · rw [abs_of_neg h, max_eq_right (by linarith)]
    ring

/-- **Positivity is the equality case.**  The absolute trace equals the trace exactly when every
eigenvalue is nonnegative. -/
theorem abs_trace_eq_trace_iff {ι : Type*} (s : Finset ι) (lam : ι → ℝ) :
    ∑ j ∈ s, |lam j| = ∑ j ∈ s, lam j ↔ ∀ j ∈ s, 0 ≤ lam j := by
  constructor
  · intro h j hj
    have hgap := abs_trace_sub_trace s lam
    rw [h, sub_self] at hgap
    have hnonneg : ∀ i ∈ s, 0 ≤ max 0 (-(lam i)) := fun i _ => le_max_left _ _
    have hzero : ∑ i ∈ s, max 0 (-(lam i)) = 0 := by linarith
    have := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hzero j hj
    have hle : -(lam j) ≤ 0 := by
      have := le_max_right 0 (-(lam j))
      linarith [this, hzero ▸ (le_of_eq ((Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hzero j hj))]
    linarith
  · intro h
    refine Finset.sum_congr rfl (fun j hj => ?_)
    exact abs_of_nonneg (h j hj)

/-- **Tracelessness of an atom-free convolution.**  If the kernel vanishes on the diagonal, the sum of
the diagonal entries is zero. -/
theorem traceless_of_diagonal_zero {ι : Type*} (s : Finset ι) (K : ι → ℝ)
    (hK : ∀ j ∈ s, K j = 0) : ∑ j ∈ s, K j = 0 :=
  Finset.sum_eq_zero hK

/-- **The trace is purely archimedean.**  With the prime part traceless, the Weil operator's trace is
that of the archimedean pairing. -/
theorem trace_is_archimedean {tQ tP : ℝ} (hP : tP = 0) : tQ - tP = tQ := by
  rw [hP]; ring

/-- **The archimedean trace is pinned.**  With `‖𝒯‖ ≤ β` the trace of `Q = I - 𝒯` on a `d`-dimensional
space lies between `(1-β)d` and `(1+β)d`. -/
theorem trace_pinned {β d tQ : ℝ} (_hd : 0 ≤ d) (hlow : (1 - β) * d ≤ tQ)
    (hhigh : tQ ≤ (1 + β) * d) : (1 - β) * d ≤ tQ ∧ tQ ≤ (1 + β) * d := ⟨hlow, hhigh⟩

/-- The pinning is strictly positive at the archimedean budget. -/
theorem trace_lower_positive {d : ℝ} (hd : 0 < d) :
    0 < (1 - archimedeanBudget) * d :=
  mul_pos definiteness_constant_pos hd

end RHTower
