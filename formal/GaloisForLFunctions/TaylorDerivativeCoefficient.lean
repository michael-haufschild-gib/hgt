import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# Iterated formal-derivative coefficients (rising-factorial law)

The Taylor-magnitude hypertranscendence cards expand a differential polynomial on the generic power
series `F = ∑ Xₙ zⁿ` and read off the `z^N` coefficient identity.  The "derivative factors are
falling/rising factorials" step — the `k`-th coefficient of the `j`-th formal derivative of a power
series is a rising factorial times a shifted coefficient — is the load-bearing arithmetic of that
expansion.  mathlib provides only the single-derivative case (`PowerSeries.coeff_derivative`); this
file proves the iterated law.
-/

open PowerSeries Finset

namespace GaloisForLFunctions

variable {R : Type*} [CommSemiring R]

/-- **Iterated formal-derivative coefficient.**  The `n`-th coefficient of the `j`-th formal
derivative of `f` is the `(n+j)`-th coefficient of `f` times the rising factorial
`(n+1)(n+2)⋯(n+j) = ∏_{i<j}(n+1+i)`. -/
theorem coeff_iterate_derivative (f : R⟦X⟧) (j : ℕ) : ∀ n : ℕ,
    coeff n ((⇑(d⁄dX R))^[j] f)
      = coeff (n + j) f * ∏ i ∈ Finset.range j, ((n + 1 + i : ℕ) : R) := by
  induction j with
  | zero => intro n; simp
  | succ j ih =>
    intro n
    rw [Function.iterate_succ_apply', coeff_derivative, ih (n + 1), Finset.prod_range_succ']
    have harg : n + 1 + j = n + (j + 1) := by omega
    rw [harg]
    have hprod : ∏ i ∈ Finset.range j, ((n + 1 + (i + 1) : ℕ) : R)
        = ∏ i ∈ Finset.range j, ((n + 1 + 1 + i : ℕ) : R) :=
      Finset.prod_congr rfl fun i _ => by ring_nf
    rw [hprod]
    push_cast
    ring

end GaloisForLFunctions
