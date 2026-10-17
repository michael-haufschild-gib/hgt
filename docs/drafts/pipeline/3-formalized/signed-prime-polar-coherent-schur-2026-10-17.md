# Coherent annular Schur coupling for actual signed prime–polar transport

- **ID:** signed-prime-polar-coherent-schur
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** `1-in-progress/signed-prime-polar-transport-2026-10-17.md`
- **Scope:** one contribution; continuous-source collar construction and joint transport geometry.

## Statement and significance

For every f in C_c(R,R), form the actual backward annular average g. Its source
covariance is C=H(0), its energy B is the full double collar Gram integral, and
its covariance with the actual signed packet P_N is the exact Chebyshev work W.
Write R=||f||², D=<f,P_N>, Q=||P_N||². Prove without hypotheses:

(W-CD/R)² ≤ (B-C²/R)(Q-D²/R),
(D-W)² ≤ Q(R+B-2C), and 0≤B≤R.

Transfer to the literal half-line scalar pairing and work using the source cutoff.
Retain all collar cross-correlations, mixed prime–polar terms, actual weights,
and signs. The Schur budget removes source-parallel energy from both factors.
No cutoff-uniform estimate of Q is asserted.

## Evidence and critique

Searches: `/tmp/spp4-search.json` (partial=false), `/tmp/spp4-schur-search.json`
(partial=true); errors=[] in both, refresh deferred to the running indexer.
Read actual finite-packet projection in `ProjectedHyperbolicGramControl.lean`
and abstract Schur coupling declarations. They provide projection precedents,
not this continuum annular source paired with the actual mixed signed packet.
Neighbor `HyperbolicGaugeChebyshevEnergyRepresentation.lean` uses a C¹ source;
this theorem instead applies to arbitrary compact continuous sources.
No external novelty claim. Do not count projection algebra or helper lemmas separately.

## Proof and verification plan

- [x] Corpus search, source comparison, and mathematical critique.
- [x] Dependency-closed paper proof in `SignedPrimePolarCoherentSchur.md`.
- [x] Construct collar source, support, continuity, and actual mixed Fubini.
- [x] Identify C, B, and W with explicit correlation/Chebyshev quantities.
- [x] Prove source residual energy, coherent transport, and Schur inequalities.
- [x] Transfer endpoints to the admitted full-half-line scalar domain.
- [x] Direct leaf builds, scratch axioms/signatures, umbrella wiring, lint/index.
- [x] Promote card and update facts ledger; count only the entire package.

Both `AnnularCorrelationSource.lean` and `SignedPrimePolarCoherentSchur.lean` pass
direct `lake --old env lean <leaf> -o <leaf.olean>` with empty diagnostic logs
`/tmp/spp4-source-build.log` and `/tmp/spp4-schur-build.log`. Imports are wired.
Final scratch audit exits 0: ten endpoint reports contain only propext,
Classical.choice, and Quot.sound, with no extra premises in the main signatures.
`/tmp/spp4-final-axioms.log` records the audit. Index refresh passes. Global lint
flags three unrelated unwired modules; exact names and evidence are in the ledger.
No umbrella build was run. This package is contribution 4/100.

README `formal/GaloisForLFunctions/BiScaleUncertainty/README.md` stays read-only.
One foreground Lean process at a time; no numerical experiments or umbrella builds.
