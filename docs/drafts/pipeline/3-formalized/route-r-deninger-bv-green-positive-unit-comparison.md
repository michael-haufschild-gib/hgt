# Route-R / Deninger BV--Green positive-unit comparison

- **ID:** `route-r-deninger-bv-green-positive-unit-comparison`
- **Stage:** 3-formalized
- **Type:** CROSS-ROUTE SOURCE COMPARISON
- **Scientific status:** `[PROVED HERE] [FORMALIZED] [CROSS-ROUTE BRIDGE]`
- **Routes:** Route R rational-adelic Rees corona; Deninger ordinary-integer BV--Green boundary;
  Calderon--Witt Gamma mate curvature

## Exact claim

Put

```text
a(rho)   = 2 Re(rho) - 1,
kappa(p) = (1-p^-1)(2-p^-1)/(2 log p),
K(p,rho) = a(rho) kappa(p),
sinhc(x) = 1                         if x=0,
           sinh(x)/x                otherwise,
U(p,rho) = 2 log(6) sinhc(a(rho) log(6)) / kappa(p).
```

Prove, without choosing or dividing by a Xi coefficient,

```text
0 < U(p,rho),
deningerTensorSquareRadialMateCurvature 6 rho = U(p,rho) K(p,rho),
6 * (BVGreenEval 6 rho - BVGreenEval 6 (1-conj rho)) = U(p,rho) K(p,rho).
```

Consequently the explicit Route-R Hodge-mate coefficient vanishes iff the literal reflected
ordinary-integer BV--Green boundary evaluation vanishes.  The same source boundary condition is
equivalent to Route R's fixed same-fibre norm identity and source-dagger identity.

## Conjecturing log

### C1 — arbitrary quotient comparison

Define the transfer as curvature divided by `K` away from `K=0` and arbitrarily at zero.

**Verdict:** rejected.  It proves only equality of zero sets and hides orientation/regularity at
the critical fibre.

### C2 — canonical hyperbolic secant comparison

Use `sinhc`; the identity `sinh x = x sinhc x` gives a division-free comparison at `x=0`.

**Verdict:** sign error; mate curvature has the same sign as centered rate, so a positive
hyperbolic-sinc, not a secant, is required.

### C3 — canonical hyperbolic-sinc positive unit

For `x != 0`, strict monotonicity/sign of `sinh` gives `sinh x / x > 0`; at zero the value is one.
Since `log 6 > 0` and `kappa(p) > 0`, `U(p,rho)>0`.  Substitution gives

```text
U K
= 2 log(6) sinhc(a log(6)) / kappa(p) * (a kappa(p))
= 2 sinh(a log(6)).
```

The Deninger tensor-square theorem identifies the last term with mate curvature.  The
ordinary-integer reflected-difference theorem identifies curvature with the literal BV--Green
boundary at degree six.

**Verdict:** proved on paper and formalized.  Exact, coefficient-faithful, positive in both Gamma
orientations, and division-free at the critical fibre.

## Frontier gain

This comparison replaces two apparently different scalar producers by one explicit source
boundary.  Any future source Stokes/Cartier theorem need only descend the fixed degree-six
ordinary-integer Hochschild boundary to its physical reflected marginal; positivity then carries
its vanishing to every Route-R prime attenuation without a primewise sign choice.  It does **not**
assert that the physical marginal is cyclic: that descent remains RH-bearing.

## Hostile audit

- Equality of zero sets alone is already known; positive-unit identity is stronger.
- No Xi jet is divided out, so multiplicity and non-erasure are not assumed.
- Hochschild-boundary exactness does not imply physical marginal vanishing; physical evaluation is
  not silently declared cyclic.
- Source operator exists before divisor enumeration, but evaluation at `rho` remains explicit.
- This does not produce barrelled pointwise boundedness or source-normal all-prime admission.

## Collision audit

Internal corpus contains the two input identities separately but no exact positive-unit
comparison between Route R's adjacent Hodge-mate coefficient and Deninger's ordinary-integer
BV--Green boundary.  Targeted primary-literature search found Deninger-style regularized
determinant/Lefschetz constructions and THH realizations over finite fields, but no ordinary-prime
BV--Wold/Route-R coefficient comparison.  Novelty is claimed only for this corpus-specific exact
bridge, not for `sinhc` positivity or Deninger determinant philosophy.

## Gates

- [x] exact internal frontier isolated
- [x] dead quotient normalization rejected
- [x] canonical paper proof completed
- [x] hostile audit completed
- [x] unconditional Lean formalization
- [x] umbrella wiring and direct Lean audit
- [x] axiom audit: `[propext, Classical.choice, Quot.sound]`
- [x] final targeted module build
- [ ] consolidated repository lint: current run is blocked only by five unrelated, concurrently
  added HTGeometry modules missing from the HTGeometry umbrella

## Lean surface

Formal module:
`GaloisForLFunctions/RHTower/RouteRDeningerBVGreenPositiveUnitComparison.lean`.

- `routeRDeningerHyperbolicSinc_pos`
- `mul_routeRDeningerHyperbolicSinc`
- `routeRDeningerBVGreenPositiveUnit_pos`
- `deningerTensorSquareRadialMateCurvature_six_eq_routeR_positiveUnit_mul`
- `routeRDeningerBVGreenReflectedBoundary_eq_positiveUnit_mul`
- `deningerCalderonWittBaseGammaBoundaryDefectCoefficient_eq_routeR_positiveUnit_mul`
- `routeRDeningerBVGreenReflectedBoundary_eq_zero_iff_hodgeMateCoefficient_eq_zero`
- `routeRDeningerBVGreenReflectedBoundary_eq_zero_iff_sameFiberNormIdentity`
- `routeRDeningerBVGreenReflectedBoundary_eq_zero_iff_sourceDaggerIdentity`
- `routeRDeningerBVGreenReflectedBoundary_eq_zero_iff_cofinalEquicontinuity`
- `routeRDeningerBVGreenReflectedBoundary_eq_zero_iff_singularStokesFlat`
- `PrimeDepthBVWoldBarrelledSourceCertificate.routeRDeningerBoundary_eq_zero`
- `forall_routeRDeningerBVGreenReflectedBoundary_eq_zero_iff_riemannHypothesis`
