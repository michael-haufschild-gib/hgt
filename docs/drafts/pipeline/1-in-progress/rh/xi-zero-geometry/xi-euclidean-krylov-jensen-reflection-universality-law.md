# Xi Euclidean--Krylov--Jensen reflection universality law

- **ID:** xi-euclidean-krylov-jensen-reflection-universality-law
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper-proved and Lean-formalized; hostile literature audit passed)
- **Source:** Post-Law-40 terminal spectral/thermal ledger
- **Statement:** Euclidean spectral realization of the prime--Gamma moment tower, exact
  nonterminating complex Krylov realization, centered radial Jensen saturation, intrinsic
  Cassini Jensen/jet cancellation, inward theta-boundary saturation, and Cassini/thermal/operator
  reflection-defect cancellation form one ten-chart positive/failure phase.

## Gates

- [x] Complete source declarations read
- [x] Existing-law overlap audit
- [x] Internal noncollision audit
- [x] Complete paper proof
- [x] Lean direct check
- [x] Hostile literature noncollision audit
- [ ] Final module build, lint, and axiom audit

## Existing-law overlap audit

Source-marked Gibbs free-energy zero was rejected because Law 20 already contains that exact
projective diagonal endpoint. Repackaging the full projective--thermal master spectrum was also
rejected because its clauses already have a common consumer. Remaining four-module component had
no consumer for its Euclidean, Krylov, radial-Jensen, and Cassini-reflection endpoints.

## Paper proof

RH constructs the canonical infinite-support Euclidean spectrum. Forgetting support yields the
weak spectral chart. Strict source Hankel determinants make every finite canonical reflection
packet linearly independent, hence every Gram--Schmidt/Krylov residual is nonzero. RH saturates the
radial Jensen mass; equality supplies its inequality. RH also cancels the intrinsic Cassini
Jensen/jet residual and saturates the inward theta boundary. Existing direct welds transport that
boundary to the Cassini reflection defect; the thermal energy identity transports its zero fibre
to the anti-Hermitian Hilbert--Schmidt defect. Any first positive chart recovers RH, and negating
each exact reverse implication synchronizes all ten failures. `[PROVED HERE]`

## Lean formalization

- Module:
  `formal/GaloisForLFunctions/RHTower/XiEuclideanKrylovJensenReflectionUniversalityLaw.lean`
- Positive certificate: `XiEuclideanKrylovJensenReflectionUniversalCertificate`
- Failure certificate: `XiEuclideanKrylovJensenReflectionFailureUniversalCertificate`

Exact direct check passed:

```text
lake env lean GaloisForLFunctions/RHTower/XiEuclideanKrylovJensenReflectionUniversalityLaw.lean
```

One initial check exposed source-newer-than-cache Krylov/Cassini endpoint declarations. No
dependency build was run. Final proof reconstructs Krylov nontermination locally from cached
strict Hankel determinants and imports the cache-visible thermal identity directly.

## Hostile literature noncollision audit

Post-proof searches covered Riemann-Xi Euclidean spectral measures, Krylov/Hankel chains, radial
Jensen criteria, Cassini reflection, and Hilbert--Schmidt anti-Hermitian defects. Nearest results
concern Jensen-polynomial hyperbolicity (`arXiv:1910.01227`), generic Hankel/Riemann--Hilbert
determinants (`arXiv:2205.15007`), and semilocal spectral approaches. None states this ten-chart
spectral-reflection synchronization. Verdict: `NO COLLISION FOUND`; no priority claim.

## Log

- 2026-07-21 — Derived bottom-up after overlap rejection. Paper proof and internal duplicate audit
  passed. Direct Lean passed after cache-safe local Krylov reconstruction.
- 2026-07-21 — Targeted post-proof hostile literature audit passed. Exhaustion restarted.
