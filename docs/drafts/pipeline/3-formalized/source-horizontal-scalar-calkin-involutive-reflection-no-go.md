# Source-horizontal scalar-Calkin involutive reflection no-go

- **ID:** SH-SCIR
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** shared HB/FZZ-P/PW-B/RBH source-horizontal producer
- **Chain:** source reflection → fixed Ward orientation → shared receiver extinction → RH

## Theorem

An involutive bounded linear quadratic reflection receiving every finite off-wall source-horizontal packet cannot be a compact perturbation of any real scalar operator. Both reflection sectors `(I+T)/2` and `(I-T)/2` are noncompact.

## Proof core

Put `K=T-cI`. If `c²≠1`, compactness of `K` makes `K(T+cI)=(1-c²)I` compact, so the carrier and hence `range K` are finite-dimensional. If `c²=1`, `(-c/2)K` is a compact idempotent, hence has finite-dimensional range. Both cases contradict the formal all-packet theorem forcing `T-cI` to have unbounded operational rank for every `c`.

## Result

- Killed: every scalar-Calkin bounded involutive shared-source reflection.
- Sharp survivor: two noncompact essential reflection sectors, or nonlinear, unbounded/singular, or domain-changing dynamics.
- Abstract compact-idempotent mechanism: `REDISCOVERED`.
- Exact four-route source consequence: no prior corpus or literature result found through August 2026.

## Lean closure

- Module: `GaloisForLFunctions.RHTower.SourceHorizontalScalarCalkinInvolutiveReflectionNoGo`
- Closed capstone: `sourceHorizontalScalarCalkinInvolutiveReflectionRouteKilled`
- Positive survivors: `sourceZeroHorizontalSharedReservoir_allBoundedInvolutiveReflectionLandings_forces_noncompactPerturbation`, `sourceZeroHorizontalSharedReservoir_allBoundedInvolutiveReflectionLandings_forces_bothEssentialSectors`
- Direct check and target-only build pass.
- `#print axioms`: only `propext`, `Classical.choice`, `Quot.sound`.
- Imported by `GaloisForLFunctions.RHTower`; umbrella build intentionally not run.
- Formal lint reports no issue in this module; repository-wide exit remains nonzero only for unrelated concurrently unwired modules.

## Gates

- [x] corpus and literature frontier
- [x] hostile falsity/rediscovery audit
- [x] dependency-closed paper proof
- [x] exact Lean theorem and positive survivor
