# Tilted Xi has no Laurent outer factor on an entire unit

- **ID:** RH-XILLF-20261007
- **Stage:** 3-formalized
- **Parent:** `../2-fully-proven/xi-finite-cover-monodromy.md`
- **Predecessor:** `xi-polynomial-left-factors.md`
- **Verdict:** BRIDGE; classical Schottky consequence, no novelty claim

## Exact result and proof

For every real a, polynomials P,Q over C and entire nowhere-zero h,
P(h(s))+Q(1/h(s)) cannot equal xi(s)*exp(-a*s) identically. Degrees are
unrestricted. Every Laurent polynomial has this presentation.

Choose an actual Xi zero rho and set b=h(rho)!=0. On the zero-free right
half-plane h omits 0,b, and 1/h omits 0,1/b. Schottky bounds both by an
exponential on the real ray. Polynomial transport and the triangle inequality
do the same for their Laurent expression, contradicting actual Xi ray growth.
The zero comes from the imported unconditional corpus theorem; no zero or
simple-zero premise is supplied by the caller.

## Lean and validation

- `HTGeometry/SchottkyLaurentGrowth.lean`:
  `GaloisForLFunctions.HTGeometry.exists_exp_ray_bound_laurent`.
- `RHTower/XiLaurentLeftFactors.lean`:
  `RHTower.xi_not_laurent_of_entire_unit`.

Both targeted builds and final actual-source `lake env lean` checks passed.
Both public axiom closures use only `propext`, `Classical.choice`, `Quot.sound`.
Each umbrella import occurs once. Both obsolete proof scratches were removed
after exact comparison with final sources. No heartbeat change or numerical
computation. Evidence: `/tmp/rh-xi-laurent-axioms.log`,
`/tmp/rh-final-SchottkyLaurentGrowth.log`, `/tmp/rh-final-XiLaurentLeftFactors.log`,
`/tmp/rh-schottky-laurent-build.log`, `/tmp/rh-xi-laurent-build.log`.

Index refresh passed. Lint failed only on six unrelated unwired H leaves:
`ApertureConeCalculus`, `ApertureConeWinding`, `ApertureLogTranslation`,
`ApertureOpenHistoryIdeal`, `BoundaryCoronaCStarAlgebra`, `CosineCornerUnfolding`.
The global gate is not clean; there is no own-leaf error.

## Scientific assessment

This closes the second punctured-sphere factor case in the parent's paper
proof. It is classical analytic rigidity, not new scientific knowledge by
itself. No full finite-cover/profinite or RH theorem has been formalized.
Corpus and primary audits are on the parent. No hard step was deferred for
effort. Next tackle actual meromorphic pole removal and the remaining cover
reduction; avoid presenting short supporting lemmas as discoveries.
