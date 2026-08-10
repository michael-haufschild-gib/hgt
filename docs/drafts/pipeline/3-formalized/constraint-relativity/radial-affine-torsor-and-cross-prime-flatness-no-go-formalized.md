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

Theorem 4 — finite algebraic radial invariants are constant:

11. `radialExpChar`, `radialExpChar_injective`, `linearIndependent_radialExpChar` — **card `(10)`**: the radial
    character of a frequency is a monoid homomorphism of the additive flow, distinct frequencies
    give distinct characters, and Artin's independence of characters
    (`linearIndependent_monoidHom`) makes them linearly independent.
12. `coeff_eq_zero_of_expSum_eq_zero`, `expSum_const_iff` — **Theorem 4**: a finite combination of
    distinct radial frequencies that is constant along the flow, with every frequency nonzero, has
    all coefficients zero and constant zero.  No nonconstant finite algebraic invariant survives
    the radial flow.
13. `primeFrequency_injective` — **card `(9)`**: distinct integer exponent vectors give distinct
    radial frequencies, from the `ℤ`-independence of prime logarithms
    (`GaloisForLFunctions.logPrime_linearIndependent_int`, reused, not rebuilt).  This is what makes
    the Laurent exponents visible along `γ(t) = (p^t)`.

Theorem 5 — a trace-one tensor does not frame individual legs:

14. `exists_unique_factorization_scale` — **card `(11)`**: pure factorizations of a fixed nonzero
    product form a `ℂˣ`-torsor, `(x, y) ↦ (r x, r⁻¹ y)`, with the scale unique.
15. `span_transverse_scale` — **card `(12)`**: the torsor action moves the transverse line
    `ℂ(x + y)` to `ℂ(x + r⁻² y)`.
16. `span_transverse_ne` — the no-go: for `r² ≠ 1` those are different lines, so no transverse line
    is natural from `(L₊, L₋, ω)` alone.  Product normalization does not determine a same-fibre
    individual-leg frame.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstraintRelativity/RadialAffineTorsor.lean  # clean
lake build GaloisForLFunctions.HTGeometry                                                  # green
```
