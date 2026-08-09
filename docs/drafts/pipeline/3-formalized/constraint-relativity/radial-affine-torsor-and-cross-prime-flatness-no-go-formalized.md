# Radial affine torsor and cross-prime flatness no-go — formalized

- **ID:** `radial-affine-torsor-and-cross-prime-flatness-no-go-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `radial-affine-torsor-and-cross-prime-flatness-no-go.md` (same directory)
- **Status:** `[LEAN COMPLETE] [UNCONDITIONAL] [NO SORRY] [NO NEW AXIOMS]`

## Lean modules

| Module | Path |
|---|---|
| `GaloisForLFunctions.HTGeometry.ConstraintRelativity.RadialAffineTorsor` | `formal/GaloisForLFunctions/HTGeometry/ConstraintRelativity/RadialAffineTorsor.lean` |

Wired into `GaloisForLFunctions.HTGeometry`.

## Realization

The two-grade component is realized as `ℝ × ℝ` with the radial character acting by `g^c` on the
first grade and `h^c` on the second (`radialAction`); the cross-grade relation line
`L_λ = ℂ(x_g + λ x_h)` of card `(1)` is `gradeLine λ = span{(1, λ)}`.

The slope profile of Theorem 2 is realized over an arbitrary index type with an arbitrary nonzero
weight function `w`; the prime instance takes `w p = log p`, whose nonvanishing is **proved** from
primality (`log_prime_ne_zero`) rather than assumed.

## Formal theorem chain

All declarations live in namespace `HTGeometry.ConstraintRelativity`.

Theorem 1 — two-grade relations are one radial torsor:

1. `radialAction`, `radialAction_apply` — the radial character action.
2. `map_gradeLine` — **card `(2)`**: `Γ_c L_λ = L_{λ (h/g)^c}`.
3. `exists_unique_radial_parameter` — **freeness and transitivity**: for distinct positive grades
   and positive parameters there is exactly one `c` with `λ (h/g)^c = λ'`.
4. `radial_stabilizer_trivial` — every member has trivial stabilizer, so no radial-equivariant
   datum can select one.

Theorem 2 — complete cross-prime orbit invariant:

5. `slopeAction` — **card `(3)`**: `(c · b)_p = b_p + c log p`.
6. `crossCurvature` — **card `(4)`**: `κ_pq = b_p/log p − b_q/log q`.
7. `crossCurvature_slopeAction` — **card `(5)`**, invariance.
8. `exists_slopeAction_of_crossCurvature_eq` — **card `(5)`**, completeness: equal curvatures
   force the same radial orbit.

Corollary 3 — flatness never selects the critical slope:

9. `crossCurvature_eq_zero_iff` — **card `(6)`–`(7)`**: flat exactly when `b_p = a log p`, so the
   flat locus is one full orbit, not a point.
10. `riemannProfile_flat`, `riemannProfile_prime_flat` — **card `(8)`**: the Riemann slope profile
    `b_p(ρ) = (2 Re ρ − 1) log p` has identically vanishing cross-prime curvature for **every** `ρ`,
    on or off the critical line.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstraintRelativity/RadialAffineTorsor.lean  # clean
lake build GaloisForLFunctions.HTGeometry                                                  # green
```
