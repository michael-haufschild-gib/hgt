# PM: Mayer scattering and energy escape

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** [PM tasks](../../../reports/review-0111/route-PM.md), [current frontier](../../../reports/rh-current-frontier-map.md#pm).

## Required conclusions

| Task | Required mathematical result | Status |
|---|---|---|
| Mayer 1 | Exact Mayer–Selberg product, oriented/unoriented multiplicities, geometric lengths, and scattering normalization | Euler product and actual translation lengths certified; closed-geodesic multiplicities and scattering comparison open |
| Mayer 2 | Faithful equivalence between actual right-strip zeta zeros and scattering-sector eigenvalue events | Open; operator and parameter conventions must be identified exactly |
| Mayer 3 | Actual Hermitian structure including scattering, recovering a classical zero-free region from transfer positivity | Open |
| Mayer 4 | Separation of cusp events from scattering events by that form | Open |
| Mayer 5 | Quantitative scattering-sector spectral gap yielding a fixed zero-free strip | Open |
| Mayer 6 | Exclusion of all off-line resonances through partner saturation | Open; RH-complete |
| Escape a | Divergent actual receiver energy produces two-prime Euler laws modulo finite energy | Open |
| Escape b | Positive gauge mass for an actual escape state at some damping below one half | Open |
| Escape c | Exterior tightness excluding escape to infinite height | Open |
| Escape d | Cofinal complete-energy bounds, equivalently visibility of every actual subcritical cofactor limit | Open; RH-complete |

## Certified primitive-orbit product

The [actual primitive-orbit Euler product](../3-formalized/gauss-mayer-primitive-orbit-product.md)
is absolutely convergent near `z=0` for `Re w>1`, and throughout `|z|≤1`
for `Re w>2`, including `z=1`:

```text
D(w,z)D(w,−z) = ∏_c ∏_(m≥0) (1−z^(2ℓ(c)) λ_c^(−w−2m)).
```

The joint product has the same value and summable absolute deviations from
one. The [actual translation length](../3-formalized/gauss-mayer-hyperbolic-translation-length.md)
is the attained displacement minimum `L_c=2 log λ_c`, so each factor is
`1−z^(2ℓ(c)) exp(−(w/2+m)L_c)`. The [inverse-orientation multiplicities](../2-fully-proven/gauss-mayer-inverse-orientation-multiplicities.md),
closed-geodesic identification, and actual scattering comparison remain open.

## Operator convention

`MayerFredholm.determinant_eq_zero_iff_eigenvector` concerns the full actual
operator `MayerCutoff.regularized = ζ(w)P + remainderSum`, with eigenvalue
`z⁻¹`. It does not identify the spectrum of the holomorphic remainder alone.
The faithful scattering comparison must preserve this distinction.

The inspected `SelbergEisensteinScatteringEntry.phiσ` is an actual constant
term, proved holomorphic for `Re s>1/2`, `s≠1`. Its arithmetic factor contains
the Möbius Dirichlet series at `2s`. Those theorems do not continue this
literal series into `Re(2s)<1`; the required meromorphic continuation and
Mayer comparison remain separate analytic obligations.

## Escape receiver boundary

`exists_tendsto_normGram_of_dominant_split` consumes an actual power-row
decomposition with a subdominant remainder; it does not construct that
decomposition from energy divergence. The exact visibility criterion
`riemannHypothesis_iff_forall_gaugeMass_pos` requires every actual cofactor
limit at every subcritical damping. Existence of limits or the conditional
zero-mass law under power growth does not supply positive gauge mass.

## Integrity and placement

No missing source identity, summability bound, positivity, or spectral gap may
be introduced as a premise. Inverse classes retain the proved integral
conjugacy criterion; no extra unoriented quotient is imposed silently.
Gauss–Mayer results belong in `RenormalizedIntersectionTheory`.
Route-specific results without another clear mathematical owner belong in
`RHTower/routePM/`.
