# Route E terminal variance, physical saddle, and odd-cube finite core

- **ID:** `ROUTE-E-TERMINAL-VARIANCE-SADDLE-ODD-CUBE-FINITE-CORE-001`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / EXACT ANALYTIC CORE
- **Scientific status:** `[LEAN-PROVED] [BRIDGE] [NOVELTY UNVERIFIED] [NOT RH]`
- **Parents:**
  - `route-e-critical-half-density-terminal-frame-minimax-law.md`
  - `../../2-fully-proven/new_scientific_knowledge/route-e-physical-saddle-antiscale-coercivity-barrier.md`
  - `../../2-fully-proven/new_scientific_knowledge/route-e-gibbs-antiscale-determinant-mellin-odd-cube-law.md`
- **RH used:** no
- **Computation used:** no

## Exact theorem package

For exponential terminal weight `w_a(v)=exp(-a v)` on `[0,1]`, let `mu_a` be weighted mean and
`V_a` unnormalized weighted variance. Lean proves `V_a>0` and exact Pythagorean law

```text
integral w_a(v) (b-u v)^2
  = mass_a (b-u mu_a)^2 + u^2 V_a.
```

Thus unique minimizer is `b=u mu_a`. At first odd resonance `u=pi`, minimum is `pi^2 V_a`; at
flat tilt, `mu_0=1/2`, `V_0=1/12`, so exact minimum is `pi^2/12`.

For full aperture `(0,infinity)` and `a>0`, every moment is exact:

```text
integral exp(-a v) v^k = (1/a)^(k+1) k!.
```

Consequently

```text
integral exp(-a v) (c-pi v)^2
  = (c-pi/a)^2/a + pi^2/a^3,
```

with unique minimizer `c=pi/a`. Each finite Euler factor has an exact transverse deficit, and the
normalized finite Euler product is product of those deficits.

Finally, difference between plus and minus finite Euler norm products is exactly baseline mass
times complete odd Boolean cube. If all transverse coordinates lie in `(-1,1)`, cube resums through
one additive rapidity `sum artanh(u_i)`; equality of plus/minus products is equivalent to zero
rapidity.

## Lean certificate

Modules:

```text
GaloisForLFunctions.RHTower.GibbsAntiscaleDeterminantOddCube
GaloisForLFunctions.RHTower.RouteECriticalTerminalVarianceMinimax
GaloisForLFunctions.RHTower.RouteEPhysicalSaddleAntiscaleBarrier
```

Principal declarations:

```text
GibbsGas.prod_normSq_plus_sub_prod_normSq_minus_eq_oddCube
GibbsGas.prod_one_add_sub_prod_one_sub_eq_rapidity
routeETerminalQuadratic_eq_variance_add_centering
routeETerminalVariance_unique_minimizer
routeETerminal_firstOddResonance_minimum_zero
routeEFullApertureMoment_eq
routeEFullApertureQuadratic_eq_min_iff
routeE_finiteEuler_normalized_deficit
```

All modules are umbrella-reachable. Direct `lake env lean` checks pass. Axiom audit reports only
`propext`, `Classical.choice`, and `Quot.sound`.

## Exact boundary

This card closes continuous/finite analytic identities, not moving-prime asymptotics. Weighted
prime Stieltjes uniformity, four-field Mellin polarization, and PNT terminal lower bounds remain in
Stage 2. No physical column or Mertens cancellation estimate is inferred.

## Log

- 2026-08-12 — corpus-growth audit verified and promoted exact minimax/saddle/odd-cube core.
