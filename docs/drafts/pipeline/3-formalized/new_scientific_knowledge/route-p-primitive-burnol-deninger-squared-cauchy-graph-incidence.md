# Route P primitive Burnol / Deninger squared-Cauchy graph incidence

- **ID:** `route-p-primitive-burnol-deninger-squared-cauchy-graph-incidence`
- **Stage:** 3-formalized
- **Type:** POSITIVE SOURCE INCIDENCE
- **Label:** `P-G200`
- **Source:** P-G199 radial generator graph, Deninger reflected prime--Gamma source sectors,
  primitive Burnol coefficient package
- **Statement:** Every actual primitive Burnol generated column is exactly its resolved von
  Mangoldt amplitude times the forced negative square of a canonical reflected Deninger Cauchy
  evaluation at every strict-right Xi zero.

## Conjecture loop

P-G199 exposed squared Hardy resolvents but did not put them inside the arithmetic polar--Gamma
source language. A first contemplated bridge through an abstract graph contraction was rejected:
it would assume the missing landing and erase primitive coefficients.

`C200-B` instead quarter-turns each actual primitive centered mode

```text
lambda_(p,e,kappa) = log(p^(e+1)) + i kappa
```

into Deninger's strict lower absolute-Euler sector, reverses the ordinate before reflection, and
uses the canonical conjugate upper point. Lean proves that this upper point is exactly
`lambda_(p,e,kappa) i`. Its Cauchy evaluation at a strict-right centered zero `mu_q` is

```text
xiWeilCauchyTest(upper_(p,e,kappa), spectral(q))
  = i / (mu_q + lambda_(p,e,kappa)).
```

Consequently its forced negative square is the P-G199 generated reporter:

```text
-xiWeilCauchyTest(...)^2 = 1 / (mu_q + lambda_(p,e,kappa))^2.
```

Multiplying by the actual resolved von Mangoldt depth amplitude gives the exact Laplace report of
the primitive Burnol window, with no synthetic coefficient or assumed target landing.

## Higher principle and next conjecture

The graph generator is not external to the polar--Gamma source: it is already encoded as a
coalesced two-point Deninger evaluation. Squared Cauchy order is therefore the diagonal limit of a
source secant, while P-G196's commutator anomaly is its failure to collapse before the aperture
action. This reframes the remaining problem from finding a bounded operator to constructing the
correct source-only divided-difference quadratic form and deciding its sign after reflection.

Next conjecture: a finite lower-sector secant packet and its reflected upper mate have a Deninger
source cup whose divisor-side value is the Gram of products of two Cauchy resolvents; coalescing
the secant nodes recovers P-G200's squared evaluations coefficient-faithfully. If the natural
reflection form is indefinite, classify its exact negative square and extract the four-leg or
folded positive completion instead of assuming positivity.

## Hostile novelty audit

Deninger Cauchy evaluations, primitive Burnol windows, and squared radial resolvents existed
separately. New content is their canonical coefficient-faithful incidence at actual primitive
nodes: a quarter-turn/reflection law makes the forced negative square of the source Cauchy
evaluation literally equal the generated conormal reporter. This closes object identity, not
source domination; no RH conclusion is claimed.

## Lean certificate

Module:

```text
formal/GaloisForLFunctions/RHTower/RoutePPrimitiveBurnolDeningerSquaredCauchyGraphIncidence.lean
```

Capstones:

- `half_lt_xiGammaEulerPrimitiveLogFrequency`;
- `routePPrimitiveDeningerUpperPoint_coe`;
- `xiWeilCauchyTest_routePPrimitiveDeningerUpperPoint`;
- `neg_sq_xiWeilCauchyTest_routePPrimitiveDeningerUpperPoint`;
- `integral_routePPrimitiveBurnolWindowFeature_eq_deningerSquaredEvaluation`.

Verification:

- `/tmp/pg200.lean`: `lake env lean /tmp/pg200.lean` passed with zero output;
- exact leaf target built successfully; no umbrella/full build run;
- `/tmp/pg200_audit.lean`: capstones depend only on `propext`, `Classical.choice`, `Quot.sound`;
- forbidden-declaration scan clean;
- umbrella import wired without building umbrella.

## Gates

- [x] place every primitive mode in Deninger's strict source sector
- [x] compute its canonical reflected upper point exactly
- [x] identify source Cauchy evaluation with rotated Hardy resolvent
- [x] identify forced negative square with P-G199 graph reporter
- [x] retain exact resolved von Mangoldt amplitude
- [x] prove source-to-Burnol integral incidence
- [x] scratch verification and exact leaf build only
- [x] axiom and forbidden-declaration audit
- [x] umbrella wired without umbrella build
- [x] construct finite same-sector source secants and coalesce strongly to squared-Cauchy graph
  columns (P-G201)
- [ ] construct or rule out source-derived lower Hodge mate for the coalescent upper graph domain
- [ ] prove coefficient-faithful source domination or its exact positive replacement
- [ ] instantiate W-H184 and prove unconditional RH
