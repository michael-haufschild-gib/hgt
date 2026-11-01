# PM: Mayer scattering and energy escape

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** [PM tasks](../../../reports/review-0111/route-PM.md), [current frontier](../../../reports/rh-current-frontier-map.md#pm).

## Required conclusions

| Task | Required mathematical result | Status |
|---|---|---|
| Mayer 1 | Exact Mayer–Selberg product, oriented/unoriented multiplicities, geometric lengths, and scattering normalization | Primitive-pair logarithm certified; Euler product and geometric/scattering identifications open |
| Mayer 2 | Faithful equivalence between actual right-strip zeta zeros and scattering-sector eigenvalue events | Open; operator and parameter conventions must be identified exactly |
| Mayer 3 | Actual Hermitian structure including scattering, recovering a classical zero-free region from transfer positivity | Open |
| Mayer 4 | Separation of cusp events from scattering events by that form | Open |
| Mayer 5 | Quantitative scattering-sector spectral gap yielding a fixed zero-free strip | Open |
| Mayer 6 | Exclusion of all off-line resonances through partner saturation | Open; RH-complete |
| Escape a | Divergent actual receiver energy produces two-prime Euler laws modulo finite energy | Open |
| Escape b | Positive gauge mass for an actual escape state at some damping below one half | Open |
| Escape c | Exterior tightness excluding escape to infinite height | Open |
| Escape d | Cofinal complete-energy bounds, equivalently visibility of every actual subcritical cofactor limit | Open; RH-complete |

## First unresolved source identity

The [certified primitive-orbit logarithm](../3-formalized/gauss-mayer-primitive-orbit-logarithm.md)
is absolutely convergent near spectral parameter zero for `Re w>1`, and on
`|z|≤1` for `Re w>2`. Its literal summands are

```text
z^(2rℓ(c))/r · (λ_c^r)^(−w)/(1−(λ_c^r)⁻²).
```

Expand the positive geometric denominator, justify absolute interchange with
cycle and repetition sums, and exponentiate the Taylor logarithm. The target
is the [actual primitive-orbit Euler product](gauss-mayer-primitive-orbit-product.md).
This alone does not identify a scattering determinant or exclude resonances.

## Integrity and placement

No missing source identity, summability bound, positivity, or spectral gap may
be introduced as a premise. Inverse classes retain the proved integral
conjugacy criterion; no extra unoriented quotient is imposed silently.
Gauss–Mayer results belong in `RenormalizedIntersectionTheory`.
Route-specific results without another clear mathematical owner belong in
`RHTower/routePM/`.
