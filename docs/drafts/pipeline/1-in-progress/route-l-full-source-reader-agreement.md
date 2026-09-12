# Route L: full-source fixed-reader agreement

- **ID:** RH-L-C53
- **Stage:** 1-in-progress
- **Type:** CANDIDATE — comparison remains unproved
- **Source:** rh-current-frontier-map.md, Route L; user request, 2026-09-12
- **Statement:** Derive the fixed physical reader's agreement with the normalized cyclic source reader on the complete original Green/BV boundary from the actual source equations.

## Exact objective

Proof chain: complete original source → fixed physical-reader agreement → conormal vanishing → RH. Preserve the original prime, native Tate depth, every multiplicity copy, Xi coefficient, Gamma normalization and horizontal anchor. No critical-line placement, reader agreement, source stationarity or isometry may be supplied as a hypothesis.

The checked degree-six comparison is `RouteRDegreeSixBVGreenFixedReaderEquality rho` in `RouteRDegreeSixGammaCoronaLocalGlobalFracture.lean`. The canonical reader is `(5/6) • d₁ + d₆`; it kills the literal Hochschild boundary. Its physical reflected readout is `routeRDeningerBVGreenReflectedBoundary rho`. Existing theorems identify equality with this readout's vanishing and hence with `rho.re = 1/2`. Those equivalences isolate the missing theorem; they do not prove it.

C51 admits the original source at fixed real damping `a > 1`. C52 proves the scalar damping continuation has pole order twice the actual zero multiplicity, and supplies its exact nonzero regularized coefficient. Neither result supplies reader agreement or a zero-damping source-domain limit.

## Conjecture / proof-or-failure log

### A. Actual-source Ward cancellation — insufficient for the retained reader

**Conjecture tested:** The unconditional cancellation of the theta-source quadratic ghost and cyclic boundary anomaly forces the physical boundary readout to vanish.

**Source inspection:** `FrankensteinXiGreenStokesQuadraticGhostNormalForm.lean` proves the literal identity `ghost + anomaly = 0`, preserving prime and multiplicity. But `XiResolvedStokesWardCharacter.lean` resolves the pair as `(ghost, -ghost)`: its codiagonal is zero while its relative character is `2 • ghost`. The pinned mean of that relative character is `-2*m*oppositeBoundaryCurvature(log(p)*centeredRate rho)`. The physical derivative-range admission of either component is equivalent to critical-line placement. Killing the pair's sum does not establish the fixed reader's annihilation of either retained component.

**Positive survivor:** The already-formalized resolved Ward double retains an exact relative character despite total cancellation. No new Lean wrapper is warranted. The next attempt must derive an actual comparison/transgression for the fixed reader, with its residual term included.

## Search audit

`route-l-full-source-reader-defect-search.json`: generation 879115; 57,036 inventoried files (47,426 Lean, 9,610 prose), partial text/source/decomposition coverage under the deadline, compiler coverage mostly pending. All 20 candidate statements, 20 method records and returned ingredient groups inspected. Actual Ward cancellation above was the substantive new lead. Other hits required domain/decay, self-duality, retained equivariance or the comparison itself. Definition records labeled as proof methods were not treated as proved producers. The proposed cyclic-symmetry ingredient group never establishes physical-reader agreement.

## Validation and remaining work

No C53 Lean code or proof claim yet. C52 has its own leaf-build record. Do not repeat axiom printing, enlarge elaboration limits, or run umbrella/full builds. Investigate a source-derived comparison that preserves the relative character, then formalize only a dependency-closed mathematical advance.

## Log

- 2026-09-12 — Direct comparison investigation opened after the user's request to establish full-source reader agreement. Candidate A checked against actual definitions and rejected as a proof of fixed-reader agreement; original objective remains open.
