import GaloisForLFunctions.HTGeometry.BarnesLadderGenusOne

/-!
# The ladder correction factors at every genus

The two numerators of the ladder correction are `1 - D/w_n` and `1 - D/w_{n+e_j}`, so their
difference is `D` times the difference of the inverse cone values.  Factoring the difference of
`N`-th powers through the geometric identity

```text
(∑_{k<N} u^k v^{N-1-k}) (u - v) = u^N - v^N
```

therefore cancels the denominator entirely:

```text
A_n(z + ω_j) - A_{n+e_j}(z)
  = (1/w_{n+e_j} - 1/w_n) · ∑_{k<N} u^k v^{N-1-k},
```

with `u` and `v` the two numerators.  The correction carries no pole at any genus, and the
telescoping factor `1/w_{n+e_j} - 1/w_n` is exactly the genus-one answer, now multiplied by a
bounded polynomial factor.
-/

open Complex Set Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## The numerator difference -/

theorem barnesNumerator_sub (ω : ι → ℂ) (n : ι → ℕ) (j : ι) (z : ℂ)
    (hw : conePeriod ω n ≠ 0) (hw' : conePeriod ω (n + Pi.single j 1) ≠ 0) :
    -((z + ω j) / conePeriod ω n) - -(z / conePeriod ω (n + Pi.single j 1)) =
      (conePeriod ω (n + Pi.single j 1) + z) *
        ((conePeriod ω (n + Pi.single j 1))⁻¹ - (conePeriod ω n)⁻¹) := by
  have hshift : conePeriod ω (n + Pi.single j 1) = conePeriod ω n + ω j :=
    conePeriod_add_single ω n j
  rw [hshift] at hw' ⊢
  field_simp
  ring

/-! ## The factorization of the correction -/

/-- **The ladder correction factors at every genus.**  The telescoping difference of inverse cone
values times a polynomial in the two numerators; in particular the correction has no pole. -/
theorem barnesAtom_shift_sub_eq_geom (ω : ι → ℂ) {n : ι → ℕ} (hn : n ≠ 0) (j : ι) (z : ℂ)
    (hw : conePeriod ω n ≠ 0) (hw' : conePeriod ω (n + Pi.single j 1) ≠ 0)
    (hD : conePeriod ω (n + Pi.single j 1) + z ≠ 0) :
    barnesAtom ω n (z + ω j) - barnesAtom ω (n + Pi.single j 1) z =
      ((conePeriod ω (n + Pi.single j 1))⁻¹ - (conePeriod ω n)⁻¹) *
        ∑ k ∈ Finset.range (Fintype.card ι),
          (-((z + ω j) / conePeriod ω n)) ^ k *
            (-(z / conePeriod ω (n + Pi.single j 1))) ^ (Fintype.card ι - 1 - k) := by
  set u : ℂ := -((z + ω j) / conePeriod ω n) with hu
  set v : ℂ := -(z / conePeriod ω (n + Pi.single j 1)) with hv
  set D : ℂ := conePeriod ω (n + Pi.single j 1) + z with hDdef
  set t : ℂ := (conePeriod ω (n + Pi.single j 1))⁻¹ - (conePeriod ω n)⁻¹ with ht
  have hgeom := geom_sum₂_mul u v (Fintype.card ι)
  have huv : u - v = D * t := barnesNumerator_sub ω n j z hw hw'
  rw [barnesAtom_shift_sub ω hn j z, div_eq_iff hD, ← hgeom, huv]
  ring

end

end GaloisForLFunctions
