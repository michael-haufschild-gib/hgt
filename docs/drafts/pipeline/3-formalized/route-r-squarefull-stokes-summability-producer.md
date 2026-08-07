# Route R squarefull Stokes summability producer

- **ID:** route-r-squarefull-stokes-summability-producer
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Route R squarefull-tail Gamma--Cartier index
- **Statement:** The reflected difference of the explicit local level-two Euler activation masses is summable exactly when the squarefull-tail projection is balanced.

## Goal

Replace the discontinuous tail-probability target by one explicit coefficient-faithful diagonal
Stokes boundary on the prime source. This does not assume tail balance. It identifies a normality
property that existing rational-adelic trace-class machinery can meaningfully produce:

```text
b_sigma(p) = p^(-2 sigma)/(1+p^(-sigma))
           - p^(-2(1-sigma))/(1+p^(-(1-sigma))).
```

For `0 < sigma < 1`, prove

```text
Summable b_sigma  iff  sigma = 1/2.
```

At `sigma = Re(rho)`, this must be equivalent to
`RouteREulerGammaSquarefullTailBalanced rho`, hence to the Route R Gamma--Cartier port vanishing.

## Gates

- [x] 0 → 1 in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3 formalized: Lean theorem, targeted build green, axiom audit PASS
- [ ] 3 → 4 publication-ready: standalone paper and external novelty audit

## Conjecture loop

### C1 — source Real reflection transports the two activation products

`[FALSIFIED]`. Rational-adelic Real structure reflects signs and conjugates coefficients; it does
not change valuation exponent `sigma` to `1-sigma`. Off-center activation products are mutually
singular, so a same-state argument would assume the desired conclusion.

**Positive survivor:** Real structure preserves the level-two tail projection, but supplies no
transport of its two marginals.

### C2 — finite rational-adelic transport supplies a tail coupling

`[FALSIFIED]`. Finite-support adelic actions remain inside finite-modification orbits. They preserve
every tail event pointwise and do not extend automatically to a normal coupling between mutually
singular product states. Existing finite-Rees no-sewing laws make this obstruction exact.

**Positive survivor:** Any successful comparison must carry a genuinely cofinal normal current,
not another finite-stage chain identity.

### C3 — construct the full cofinal current first

`[FALSIFIED AS NEXT MOVE]`. Hybrid finite-coordinate product states telescope on cylinder
observables, but extending their current normally to the tail sigma-algebra is already equivalent to
tail balance. Building the full current adds unused representation theory.

**Positive survivor:** Only its level-two diagonal boundary is needed. Its coefficient is the
reflected difference `b_sigma` above.

### C4 — diagonal Stokes summability

`[SURVIVES HOSTILE AUDIT]`. Each summand is the actual one-prime probability of valuation depth at
least two. The level-cascade theorem gives summability of the first term exactly for
`sigma > 1/2`, and of the reflected term exactly for `sigma < 1/2`. If their difference were
summable off-center, adding the already summable face would make the nonsummable face summable, a
contradiction. At the center the boundary vanishes termwise.

This is not tail balance disguised as a hypothesis: it constructs a concrete prime coefficient and
proves its exact normality locus. Remaining producer burden becomes a trace-class/summability theorem
for that coefficient, a category already present in the pre-divisor rational-adelic source.

## Approach

1. Define local squarefull mass from the Euler activation parameter.
2. Identify it with the real value of the local activation measure on `{k | 2 <= k}`.
3. Define reflected Stokes coefficient as the difference of the two orientations.
4. Use the level-two summability threshold on each face to prove the exact summability locus.
5. Specialize to Xi divisor support and bridge to tail balance and arithmetic globalization.

## Paper proof

`[PROVED HERE]` Fix `0 < sigma < 1` and write

```text
a_sigma(p) = p^(-2 sigma)/(1+p^(-sigma)),
b_sigma(p) = a_sigma(p)-a_(1-sigma)(p).
```

The local activation formula at level two gives

```text
a_sigma(p) = mu_(p,sigma)({k | 2 <= k}).
```

The proved level-cascade threshold, specialized to `m=2`, says

```text
Summable a_sigma  iff  1 < 2 sigma  iff  1/2 < sigma.       (1)
```

Apply the same statement to `1-sigma`:

```text
Summable a_(1-sigma)  iff  1/2 < 1-sigma  iff  sigma < 1/2. (2)
```

If `sigma < 1/2`, then (1) says `a_sigma` is not summable and (2) says
`a_(1-sigma)` is summable. Were `b_sigma` summable, the pointwise identity
`a_sigma=b_sigma+a_(1-sigma)` would make `a_sigma` summable, contradiction.

If `sigma > 1/2`, then (1) says `a_sigma` is summable and (2) says
`a_(1-sigma)` is not. Were `b_sigma` summable, the identity
`a_(1-sigma)=a_sigma-b_sigma` would make the reflected face summable, contradiction.

If `sigma=1/2`, the two local masses agree termwise, so `b_sigma=0` and is summable. Therefore

```text
Summable b_sigma  iff  sigma=1/2.                            (3)
```

For Xi divisor support `rho`, open-strip support permits (3) with
`sigma=Re(rho)`. The already proved squarefull-tail index gives

```text
RouteREulerGammaSquarefullTailBalanced rho iff Re(rho)=1/2.
```

Combining with (3) proves that tail balance, Gamma--Cartier port vanishing, and summability of this
explicit local Stokes boundary are equivalent. No divisor placement, port vanishing, RH,
same-fibre norm, or source-dagger identity enters the proof.

## Novelty audit

- **Internal:** no existing module defines the reflected local squarefull boundary or its exact
  summability/Route R equivalence. Existing level cascade treats each orientation separately; the
  squarefull-tail index treats only the completed 0/1 event.
- **External parents:** Borel--Cantelli/Kakutani product-measure dichotomy and trace-class diagonal
  criteria are standard. Project-specific content is the coefficient-faithful bridge from the
  level-two Euler boundary to Route R's Gamma--Cartier port.
- **Boundary:** this theorem does not prove the coefficient summable at Xi zeros. That remains the
  independent source theorem.

## Lean formalization

Module:

```text
GaloisForLFunctions.RHTower.RouteRSquarefullStokesSummabilityProducer
```

Principal declarations:

```text
routeREulerSquarefullLocalMass
diagonalActivationMeasure_squarefull_toReal_eq_localMass
routeREulerGammaSquarefullStokesCoefficient
routeREulerGammaSquarefullStokesCoefficient_reflection
summable_routeREulerGammaSquarefullStokesCoefficient_iff
routeREulerGammaSquarefullStokesSummable_iff_tailBalanced
routeREulerGammaSquarefullStokesSummable_iff_port_eq_zero
routeRTwoThreeGammaArithmeticCorona_globalization_iff_squarefullStokesSummable
```

Audit:

- `lake env lean GaloisForLFunctions/RHTower/RouteRSquarefullStokesSummabilityProducer.lean`: PASS;
- `lake build GaloisForLFunctions.RHTower.RouteRSquarefullStokesSummabilityProducer`: PASS;
- axiom audit: `[propext, Classical.choice, Quot.sound]`;
- wired into `GaloisForLFunctions.RHTower` umbrella;
- whole-tree lint reached only four unrelated concurrent umbrella omissions:
  `ConstrainedProlateSpectralIdentification`, `ProlateFourierSignSectors`,
  `SlepianKernelScaledFubini`, and `HTGeometry.SobolevWeightDecay`. No lint error names this module.

Exact remaining producer theorem is now

```text
forall rho : XiDivisorSupport,
  RouteREulerGammaSquarefullStokesSummable rho
```

Equivalently: prove the explicit reflected level-two diagonal boundary is trace-class/`ℓ¹` from
pre-divisor rational-adelic/Euler--Gamma Stokes structure. This is strictly narrower and more
source-compatible than comparing full GNS representations or singular tail states.

## Log

- 2026-08-07 — created in 1-in-progress after three producer conjectures failed; C4 survived.
- 2026-08-07 — dependency-closed paper proof completed; ready for Lean formalization.
- 2026-08-07 — formalized, module-only build and axiom audit passed; umbrella wired.
