# Hedenmalm critical-feature holomorphic-sector coercivity

- **ID:** `hedenmalm-critical-feature-holomorphic-sector-coercivity`
- **Stage:** `1-in-progress`
- **Status:** `[OWN CONJECTURE LEAN-PROVED] [AXIOM-AUDITED] [NOT YET 75%]`
- **Parent:** `zeta23-beyond-bandwidth-one-proportion.md`

## Exact claim

For real `t` and `z=x+iy` with `|y|<1/2`, put

```text
F_t(z)=2/[1+(z-t)^2],
A=1+(x-t)^2-y^2,
B=2(x-t)y.
```

Then

```text
A^2-3B^2
 = ((x-t)^2-(1-y^2))^2 + 4(x-t)^2(1-4y^2) >= 0,
Re(F_t(z)^2) >= (1/2)|F_t(z)|^2.                       (SC1)
```

The second inequality is equivalent, after multiplying by the positive denominator
`(A^2+B^2)^2`, to `A^2>=3B^2`.

Because `F_t` has real coefficients, `xiWeilSharp F_t=F_t`. Therefore

```text
sum_q |F_t(z_q)|^2
 <= 2 Re xiWeilPolarization(F_t,F_t),                  (SC2)
```

and the right side has the existing exact four-term absolute-Euler prime--Gamma formula. Combining
`(SC2)` with the proved Ward--Green domination gives

```text
WardGreenTrace(t)
 <= 2 C_W Re PrimeGammaCriticalFeaturePolarization(t,t). (SC3)
```

This is an unconditional arithmetic upper bound for the singular same-copy Hermitian trace. It
does not by itself prove the dyadic `N/8` budget; the lattice-summed leading constant must be
audited next.

## Hostile audit

1. Generic Weil diagonals do not equal Hermitian energy off RH; `(SC1)` is feature-specific.
2. No zero-dependent center is used in `(SC1)`--`(SC3)`; `t` is any fixed real source center.
3. Critical-line copies are charged by the majorant even though Ward--Green current vanishes there;
   constant audit must account for this loss.
4. No density claim is allowed before a source-side sum over a fixed height-local center family is
   bounded below the exact `N/8` receiver threshold.

## Gates

- [x] exact factorization and paper proof
- [x] Lean pointwise sector coercivity
- [x] Lean summed Hermitian-to-Weil comparison
- [x] Lean Ward--Green prime--Gamma trace majorant
- [x] targeted build, forbidden scan, axiom audit, umbrella wiring
- [ ] dyadic lattice constant audit

## Lean certificate

Module `HedenmalmCriticalFeatureHolomorphicSectorCoercivity.lean` proves `(SC1)`--`(SC3)`.
Targeted build completed over 12,972 jobs.  The key theorems depend only on `propext`,
`Classical.choice`, and `Quot.sound`; the module contains no `sorry`, `admit`, `axiom`, `opaque`,
or `unsafe` declaration and is imported by the `RHTower` umbrella.
