import Mathlib

/-!
# Coordinates of a free module modulo an ideal

```text
mem_smul_top_finsupp_iff   ** an element of a finite free module lies in I • ⊤ exactly when every
                              coordinate lies in I **
sub_eval_mem_span          modulo the ideal of a point, a polynomial is its value there
C_mem_span_iff             and a constant lies in that ideal only if it is zero
```

The first is the free half of the fibre count: modulo `I` a finite free module has one coordinate per
basis element, so its fibre has the rank as dimension at *every* point.  The other two identify those
coordinates concretely over the base line — division by `X - lam` is evaluation at `lam` — which is
what turns the count into a basis.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Pointwise

variable {A : Type*} [CommRing A] {n : ℕ}

theorem mem_smul_top_finsupp_iff (I : Ideal A) (f : Fin n →₀ A) :
    f ∈ I • (⊤ : Submodule A (Fin n →₀ A)) ↔ ∀ i, f i ∈ I := by
  constructor
  · intro hf
    refine Submodule.smul_induction_on hf ?_ ?_
    · intro r hr g _ i
      exact Ideal.mul_mem_right _ _ hr
    · intro a b ha hb i
      exact Ideal.add_mem _ (ha i) (hb i)
  · intro hf
    have hsum : f = ∑ i ∈ f.support, Finsupp.single i (f i) := by
      ext j
      rw [Finsupp.finsetSum_apply]
      by_cases hj : j ∈ f.support
      · rw [← Finset.add_sum_erase _ _ hj, Finsupp.single_eq_same,
          show (∑ i ∈ f.support.erase j, (Finsupp.single i (f i) : Fin n →₀ A) j) = 0 from ?_,
          add_zero]
        refine Finset.sum_eq_zero fun i hi => ?_
        exact Finsupp.single_eq_of_ne (Ne.symm (Finset.mem_erase.mp hi).1)
      · rw [Finsupp.notMem_support_iff] at hj
        rw [hj]
        refine (Finset.sum_eq_zero fun i hi => ?_).symm
        refine Finsupp.single_eq_of_ne (fun hij => ?_)
        subst hij
        exact (Finsupp.mem_support_iff.mp hi) hj
    rw [hsum]
    refine Submodule.sum_mem _ fun i _ => ?_
    have : (Finsupp.single i (f i) : Fin n →₀ A) = (f i) • Finsupp.single i (1 : A) := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [this]
    exact Submodule.smul_mem_smul (hf i) Submodule.mem_top

section Free

open Polynomial Module

variable {K : Type*} [Field K]

/-- Coordinates modulo the ideal of a point are given by evaluation. -/
theorem sub_eval_mem_span (lam : K) (p : K[X]) :
    p - C (p.eval lam) ∈ Ideal.span {(X - C lam : K[X])} :=
  Ideal.mem_span_singleton.mpr Polynomial.X_sub_C_dvd_sub_C_eval

theorem C_mem_span_iff (lam : K) (c : K) :
    (C c : K[X]) ∈ Ideal.span {(X - C lam : K[X])} ↔ c = 0 := by
  constructor
  · intro hc
    obtain ⟨g, hg⟩ := Ideal.mem_span_singleton.mp hc
    have := congrArg (Polynomial.eval lam) hg
    simpa using this
  · intro hc
    rw [hc, map_zero]
    exact Ideal.zero_mem _

end Free

end GaloisForLFunctions.HTGeometry

