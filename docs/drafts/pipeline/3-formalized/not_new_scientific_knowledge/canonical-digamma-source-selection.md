# Canonical digamma source selection

- **ID:** `canonical-digamma-source-selection`
- **Stage:** 3-formalized
- **Type:** THEOREM / EXPLICIT SOURCE RIGIDITY
- **Scientific status:** `[PROVED HERE] [FORMALIZED] [BRIDGE] [NOT NEW IN ISOLATION]`
- **Target paper:**
  `../../4-publication-ready/universal-constraint-orientation-product-law/main.tex`

## Statement

Put

```text
G_star(z) = digamma(z + 1/2) + EulerGamma,
c(z)      = 1 / (z + 1/2).
```

On the open right half-plane, `G_star` satisfies

```text
G_star(z+1) - G_star(z) = c(z),
G_star(z+N) - log(z+N) -> EulerGamma.
```

It is the unique function on that half-plane with these two properties.  In particular, the
closed-form Herglotz source is forced by its half-integer shift cocycle and logarithmic
normalization; it is not selected from the residual source phase.

## Proof

If `F` is a second normalized solution, then `H=F-G_star` satisfies

```text
H(z+1)=H(z).
```

Thus `H(z+N)=H(z)` for every natural number `N`.  The common logarithmic asymptotic gives
`H(z+N)->0`, hence `H(z)=0`.

The full complex asymptotic used here is derived from the positive-integer digamma asymptotic,
the uniform shift estimate

```text
|digamma(w+N)-digamma(N+1)| <= 2|w-1|/N,
```

and continuity of the principal logarithm at `1` applied to
`(w+N)/(N+1)->1`.

## Scientific role

The digamma recurrence and asymptotic are classical.  The source-selection argument is elementary
rigidity.  Its role is to close the manuscript's source-choice boundary: the residual prime-log
Cauchy phase remains the robust generic model, while the half-integer Herglotz realization has a
canonical normalized source.  The scientific claim of the paper remains the resulting combined
constraint--orientation geometry, not this uniqueness lemma by itself.

## Formal theorem surface

The implementation is
`formal/GaloisForLFunctions/HTGeometry/CanonicalDigammaSourceSelection.lean` and contains:

- `explicitDigammaHerglotzSource_add_one`;
- `complex_log_add_nat_sub_log_nat_tendsto`;
- `digamma_add_nat_sub_log_add_nat_tendsto`;
- `explicitDigammaHerglotzSource_sub_log_tendsto`;
- `eqOn_rightHalfPlane_of_same_unitCocycle_and_tendsto_sub_zero`;
- `eqOn_rightHalfPlane_of_same_unitCocycle_and_common_asymptotic`;
- `explicitDigammaHerglotzSource_unique_of_cocycle_and_log_asymptotic`.

## Gates

- [x] exact canonical normalization stated
- [x] unit-shift cocycle proved
- [x] full complex translated logarithmic asymptotic proved
- [x] periodic ambiguity killed unconditionally
- [x] explicit source uniqueness proved on the right half-plane
- [x] narrow module check passed
- [x] axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`
- [x] project lint passed and generated indexes refreshed
