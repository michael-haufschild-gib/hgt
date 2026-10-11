# Finite Weil joint transport: exact exponent boundary

Status: formalised and audited. All couplings have infinite infinity cost at every rank and index; the explicit coupling converges to zero exactly at the finite exponents.

## Exact target

For every rank and index, every coupling of the actual finite Weil joint law with its diagonal Gaussian limit has infinite essential supremum of the displacement norm. For the existing explicit coupling along every quadratic-index sequence, convergence of its Lp error to zero holds exactly for finite `ENNReal` exponents.

## Local inputs and prior check

The preceding increment proves convergence for every `NNReal` exponent in `WeilLogShiftJointQuantileLpLimit`. `WeilLogShiftJointQuantileLaw` realizes both marginals on the common uniform interval and identifies every interior source quantile with a finite atom. Installed Lean's Gaussian measure is mutually absolutely continuous with volume at positive variance. Installed Lean supplies the essential supremum characterization of `MemLp` at infinity and transport through measurable pushforwards.

Local lexical search `gaussian eLpNorm top` has no hits. Broader `gaussian bounded` has 569 eligible hits, with the 20 returned hits concerning other Gaussian/RH boundedness questions; no candidate discharges this endpoint. Source searches locate the exact measure and Lp APIs above. Mathematical sources: local Lean only.

## Dependency-closed argument

1. A finite collection of source atoms has a finite common norm bound. The actual joint quantile takes values in this collection almost everywhere, hence lies in `MemLp` at infinity. Exact pushforward gives the same boundedness for the source marginal identity.
2. An almost-everywhere upper bound for a nondegenerate scalar Gaussian would, by absolute continuity of volume with respect to that Gaussian, hold volume-almost-everywhere. Its complement is a half-line of nonzero volume, contradiction. The first coordinate of the diagonal embedding is the original scalar, bounded above by its vector norm; therefore the diagonal Gaussian identity is not in `MemLp` at infinity.
3. For every coupling, pull the source and target identities back through its two marginal maps. If displacement were essentially bounded, subtracting it from the bounded source coordinate would make the target coordinate essentially bounded, contradicting step 2. Thus the infinity norm is exactly top. This is independent of the choice of coupling.
4. The already-constructed actual coupling supplies an unconditional concrete endpoint theorem. Its exact common-uniform pair pushforward gives the identical endpoint for the joint quantile realization.
5. Combine the endpoint with the existing all-finite-order convergence theorem. Every finite `ENNReal` exponent is a coerced `NNReal`. At top the error norm is constantly top and cannot converge to zero. This gives an exact iff classification, the positive statement extracted from the endpoint obstruction.

## Formalized leaves and audit

- `HTGeometry.BoundedTransportInfinity`: reusable bounded-marginal transport argument.
- `RHTower.WeilLogShiftJointInfinityMarginals`: actual source boundedness and actual Gaussian unboundedness.
- `RHTower.WeilLogShiftJointTransportInfinity`: all-coupling endpoint and exact convergence classification.

All three leaves have terminal native exit 0 and empty logs. Each has exactly one umbrella import. All seven direct dependencies are fresh, and all five incoming imports were inspected. Metadata issues: none. No full builds, numerical experiments, heartbeat changes, or external reading.

The native scratch audit `/tmp/hgt-joint-infinity-final-audit.lean` checks all eleven new theorems and twenty local API references. It exits 0; parsed axiom dependencies contain only `propext`, `Classical.choice`, and `Quot.sound`. The refreshed local lexical index returns all five final roots, with complete scoped coverage and no proof markers. Scoped `git diff --check` passes.

Final roots in `RHTower.WeilLogShiftJointTransportInfinity`:

- `finiteWeilCanonicalJointCoupling_eLpNorm_top`: every coupling, represented by the natural coupling subtype, has infinity norm equal to top.
- `finiteWeilCanonicalJointGaussianCoupling_eLpNorm_top`: the already-constructed actual coupling has infinity norm equal to top.
- `finiteWeilCanonicalJointQuantile_eLpNorm_top`: the common-uniform quantile realization has the same infinity norm.
- `tendsto_finiteWeilCanonicalJointGaussianCoupling_eLpNorm_zero_iff`: convergence of the actual coupling's error norm is equivalent to `q ≠ ⊤` for every `q : ENNReal` and every quadratic-index offset sequence.
- `tendsto_finiteWeilCanonicalJointQuantile_eLpNorm_zero_iff`: identical exponent classification for the common-uniform realization.

The positive statement exposed by the infinity obstruction is now dependency-closed on paper and formalized: an exact exponent classification, together with independence of the endpoint obstruction from the choice of coupling. The obstruction is a marginal support phenomenon; changing the coupling cannot remove it.

Global `scripts/formal_tools.py lint` reports eight unrelated errors and 367 warnings. Seven modules are unreachable from their umbrellas: `RHTower.CCMPolarOddPrimeJumps`, `RHTower.PaperDeningerFiniteCurvature`, `RHTower.PaperDeningerFramedCurvature`, `RHTower.PaperDeningerMateOperator`, `RHTower.PaperDeningerMateProfile`, `HTGeometry.PaperHilbertOffDiagonal`, and `HTGeometry.QKrawtchoukCompanionTriangular`. The remaining error is `sorry` in `CCMPolarOddPrimeJumps.lean:104`. No error or warning references this increment's three leaves.

Artifacts use `/tmp/hgt-joint-infinity-*`; native leaf logs use `/tmp/hgt-<Leaf>.log`. API lessons: `ae_iff` has two universe parameters; explicitly identify the exceptional set with a half-line before rewriting its volume; normalize the identity composition with `change` before applying the essential supremum characterization.
