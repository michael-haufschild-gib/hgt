import GaloisForLFunctions.TaylorDerivativeCoefficient

/-!
# Formal derivatives preserve lacunary support

Over a characteristic-zero field the rising-factorial weight of the iterated-derivative
coefficient never vanishes, so the `j`-th formal derivative has a nonzero coefficient at `k`
exactly when `f` does at `k + j` (`coeff_iterate_derivative_ne_zero_iff`).  The support of
`f^{(j)}` is therefore the support of `f` shifted down by `j`; in particular a series supported
on a lacunary exponent set has derivatives supported on the same set shifted
(`coeff_iterate_derivative_ne_zero_mem`).  This lifts the exponent-gap structure through
differentiation — the input needed to pass from transcendence of a superlacunary gap series to
its differential transcendence.
-/

open PowerSeries Finset

namespace GaloisForLFunctions

variable {R : Type*} [Field R] [CharZero R]

/-- **Derivative coefficient nonvanishing.**  Over a characteristic-zero field, the `j`-th
formal derivative of `f` has a nonzero `k`-th coefficient iff `f` has a nonzero coefficient at
`k + j`; the rising-factorial weight is a nonzero natural cast. -/
theorem coeff_iterate_derivative_ne_zero_iff (f : R⟦X⟧) (j k : ℕ) :
    coeff k ((⇑(d⁄dX R))^[j] f) ≠ 0 ↔ coeff (k + j) f ≠ 0 := by
  have hweight : (∏ i ∈ Finset.range j, ((k + 1 + i : ℕ) : R)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    exact fun i _ => Nat.cast_ne_zero.mpr (by omega)
  rw [coeff_iterate_derivative, mul_ne_zero_iff, and_iff_left hweight]

/-- **Support shift.**  If `f` is supported on `S` (every nonzero coefficient index lies in
`S`), then every nonzero coefficient index `k` of `f^{(j)}` has `k + j ∈ S`.  Differentiation
shifts the support down by `j` and preserves lacunarity. -/
theorem coeff_iterate_derivative_ne_zero_mem {f : R⟦X⟧} {S : Set ℕ}
    (hf : ∀ k, coeff k f ≠ 0 → k ∈ S) (j k : ℕ)
    (h : coeff k ((⇑(d⁄dX R))^[j] f) ≠ 0) : k + j ∈ S :=
  hf (k + j) ((coeff_iterate_derivative_ne_zero_iff f j k).mp h)

end GaloisForLFunctions
