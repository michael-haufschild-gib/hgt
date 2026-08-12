# Compact-observer local-gauge and cofinal-horizon law — Lean certificate

- **ID:** `cmr-compact-observer-local-gauge-cofinal-horizon-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `compact-observer-local-gauge-cofinal-horizon-law.md` (same directory).
- **Status:** `[UNCONDITIONAL]` `[NO SORRY / NO AXIOM / NO PROP INTERFACE]`

## Lean module

`formal/GaloisForLFunctions/HTGeometry/ConstraintMotiveRelativity/CompactObserverHorizon.lean`,
namespace `HTGeometry.ConstraintMotiveRelativity`, imported by `GaloisForLFunctions.HTGeometry`.

It builds on the corpus theorem the card itself names,
`GaloisForLFunctions.HTGeometry.finiteDimensional_of_isCompactOperator_of_bounded_below` in
`HTGeometry/CompactOperatorBoundedBelow.lean`.  That theorem was stated for an endomorphism
`E →L[𝕜] E`; it is now stated for an arbitrary compact `E →L[𝕜] F₀`, which is what a source-to-
observer operator is.  The generalization is verbatim — only the codomain type changes — and the
endomorphism case is the instance `F₀ := E`.

## Formal statement chain

### §2 — the finite local gauges and the cofinal horizon (Theorem 2.1)

1. `chartSphere`, `obsFloor` — `(COH.3)`: the unit sphere of a source chart and the observation
   floor `σ(S) = inf { ‖K x‖ : x ∈ S, ‖x‖ = 1 }`, with `bddBelow_obsSet`, `obsFloor_nonneg`,
   `obsFloor_le_of_mem`.
2. **`obsFloor_mul_le`** — the floor is the exact chart coercivity constant: `σ(S)‖x‖ ≤ ‖K x‖` on
   the chart.
3. `chartSphere_eq_image`, **`exists_norm_eq_obsFloor`** — Theorem 2.1 (1), attainment: the unit
   sphere of a nonzero finite-dimensional chart is compact, so the floor is attained.
4. **`obsFloor_pos`** — Theorem 2.1 (1): injectivity on the chart makes the floor positive.
5. `chartSphere_nonempty`, **`obsFloor_antitone`** — Theorem 2.1 (2), monotonicity: a larger chart
   has a smaller floor.
6. **`isLeast_reconstruction_constant`** — Theorem 2.1 (3)–(4), `(COH.3a)`: `σ(S)⁻¹` is the *least*
   constant with `‖x‖ ≤ c‖K x‖` on the chart, i.e. exactly the reconstruction norm `‖R_S‖`.
7. **`tendsto_obsFloor_zero`** — Theorem 2.1 (2): along a nested cofinal tower of nonzero charts
   the floors tend to zero.  A uniform floor would extend by density to the whole source, and a
   compact operator bounded below has finite-dimensional domain.
8. **`tendsto_reconstruction_norm_atTop`** and **`tendsto_reconstruction_energy_atTop`** —
   `(COH.3a)`: the reconstruction norms `σ_n⁻¹` and energies `σ_n⁻²` diverge.
9. **`not_exists_bounded_left_inverse`** — Theorem 2.1 (5): a compact observer on an
   infinite-dimensional source has no bounded left inverse at all.

### §3 — the positive Gram shadow

10. `gram` — `(COH.5)`: `A = K*K`.
11. **`gram_inner_self`** — `re ⟪A x, x⟫ = ‖K x‖²`.
12. **`gram_floor`** — `(COH.6)`: the compressed positive metric attains the same floor `σ(S)²` on
    the chart sphere and is bounded below by it there, so `λ_min(A_S) = σ(S)² → 0`.
13. **`gram_isometry`** — `(COH.7)`: `(W K)*(W K) = K*K` for every output linear isometry `W`; the
    Gram shadow is blind to the polar partial-isometry datum.

### §4 — compact observed image and open source history

14. **`isCompact_closure_image_of_bounded`** — `(COH.8)`: the observed image of a bounded source
    history has compact closure.
15. **`norm_sub_orthonormal`** — `(COH.9)`: an orthonormal source family stays `√2`-separated.
16. **`tendsto_norm_image_orthonormal`** — `(COH.9)`: a compact observer sends every orthonormal
    source sequence to zero.  The observed history closes at one point while the source history is
    uniformly separated, hence not precompact.  Proof: the adjoint plus Bessel gives weak
    convergence to zero; a subsequence in the compact closure of the image of the unit ball would
    otherwise converge in norm to a nonzero limit, contradicting weak convergence.

## Verification

```
lake env lean GaloisForLFunctions/HTGeometry/ConstraintMotiveRelativity/CompactObserverHorizon.lean
lake build GaloisForLFunctions.HTGeometry.ConstraintMotiveRelativity.CompactObserverHorizon
```

Green with no warnings.  `#print axioms` on `exists_norm_eq_obsFloor`, `obsFloor_pos`,
`obsFloor_antitone`, `obsFloor_mul_le`, `isLeast_reconstruction_constant`, `tendsto_obsFloor_zero`,
`tendsto_reconstruction_norm_atTop`, `tendsto_reconstruction_energy_atTop`,
`not_exists_bounded_left_inverse`, `gram_inner_self`, `gram_floor`, `gram_isometry`,
`isCompact_closure_image_of_bounded`, `norm_sub_orthonormal` and
`tendsto_norm_image_orthonormal` reports only `propext`, `Classical.choice`, `Quot.sound`.

## Scope notes

`obsFloor_antitone` carries the nonemptiness hypothesis `chartSphere S ≠ ∅`, and
`tendsto_obsFloor_zero` the tower hypothesis `Hn n ≠ ⊥`.  Both are forced: the floor of the zero
chart is the infimum of the empty set, namely `0`, below which no positive floor of a larger chart
can lie.  The card's `(COH.2)` tower `H₁ ⊂ H₂ ⊂ ⋯` consists of nonzero subspaces, so this is the
card's own setup rather than an added assumption.

§4's diagonal model is formalized in the stronger form that makes it work: instead of constructing
one particular diagonal operator on `ℓ²`, items 15–16 prove the phenomenon for *every* compact
observer and *every* orthonormal source sequence, which is what the card's Loop A and Loop B use.

§5's condition-number corollary `κ(K_n) = ‖K_n‖‖R_n‖ → ∞` follows from item 8 together with
`‖K_n‖ ≥ ‖K_1‖ > 0`, which is the trivial monotonicity of an operator norm along a nested tower;
the divergence content is item 8 and is proved.

§§1, 6–11 are route scope, falsifier tables and no-go bookkeeping and claim no further theorem.
