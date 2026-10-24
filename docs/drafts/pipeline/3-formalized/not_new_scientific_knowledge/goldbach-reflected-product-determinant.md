# Exact determinant coordinates of reflected product pairs

- **ID:** goldbach-reflected-product-determinant
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean); classical arithmetic bridge; no novelty claim
- **Parent:** [flat prime-dilation dispersion](../../2-fully-proven/goldbach-flat-prime-dilation-dispersion.md)
- **Module:** `formal/GaloisForLFunctions/goldbach/ReflectedProductDeterminant.lean`

## Exact statement

For every positive integer p and all integers q,h,T,R,u,v,

    ∃r∈ℤ: 0<r≤R, h|r, u+pr=T, v+qr=T
      ↔ qu−pv=T(q−p), u≡T (mod ph), 0<T−u≤Rp.

Whenever the conditions hold, r is unique. There is no primality or
coprimality premise, h and q may be zero or negative, and R may be negative.

Substituting the actual products of coordinates in `(X,2X]` gives
an equality of finite quadruple sets. Thus every count or weighted
sum on those sets is preserved, with both parameter endpoints and
the full modulus ph retained.

## Paper proof [PROVED HERE]

From u+pr=T obtain T−u=pr. Subtract p times the second equation
from q times the first to obtain the determinant identity. If r=hs,
then T−u=phs, which is the displayed congruence. Positivity of p
transports 0<r≤R exactly to 0<T−u≤Rp.

Conversely, the congruence gives T−u=phs for some integer s. Set
r=hs. The same positive multiplication equivalences give its exact
range and the first equation. The determinant identity then gives
p(v+qr−T)=0. Since p is nonzero, v+qr=T. If another parameter has
the first equation, cancelling p shows it equals r.

The finite sets use the existing coordinates
`balancedIntervalValue i = X + i.val + 1` for `i : Fin X`. Their
membership predicates are precisely the two sides of the proved
integer equivalence. Finite-set extensionality proves equality; no
infinite or asymptotic argument is used.

## Lean certificate

The three unconditional roots in `GaloisForLFunctions.Goldbach` are:

- `reflectedValues_determinant_iff`
- `reflectedValues_existsUnique_iff_determinant`
- `reflectedProductPairs_eq_determinantProductPairs`

The finite sets are `reflectedProductPairs` and `determinantProductPairs`;
their products are the actual integer-valued `reflectedBoxProduct`.

Direct final check from `formal/`:

```text
lake --old env lean GaloisForLFunctions/goldbach/ReflectedProductDeterminant.lean
```

Exit 0, no warnings or errors. All three transitive `#print axioms`
closures contain only `propext`, `Classical.choice`, and `Quot.sound`.
No added axiom, analytic premise, hole, or increased elaboration
limit occurs. Log: `/tmp/hgt-goldbach-reflected-determinant-audit.log`.
Audit directives were removed after verification. The leaf is wired
into `goldbach/Main.lean`; no umbrella build was run.

## Remaining obligation

This is exact parameter elimination. It does not yet combine the two
row congruences into their product modulus, bound the curved region,
or prove the dispersion estimate. The full flat dispersion theorem,
signed Möbius cancellation, and Goldbach remain open in Lean.

## Log

- 2026-10-24 — Formalized exact parameter elimination, uniqueness, and
  equality of the actual finite quadruple sets. All three closures pass.
