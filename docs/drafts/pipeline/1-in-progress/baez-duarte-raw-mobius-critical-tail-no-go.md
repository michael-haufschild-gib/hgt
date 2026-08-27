# Raw Möbius Baez--Duarte critical-tail obstruction

- **ID:** NBBD-RMCT
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / NO-GO CANDIDATE
- **Source:** `rh-current-frontier-map.md` NB/BD branch (read-only ledger)
- **Statement:** Canonical raw Möbius full-error decay forces an impossible little-o square-root harmonic charge; determine and formalize the sharp surviving tail obstruction.

## Goal
Decide the literal complementary-tail premise for the canonical raw Möbius modular approximants. If false, prove more than its negation: identify the sharp critical-scale lower obstruction and the coefficient correction forced by critical-line zeta zeros.

## Gates
- [x] 0 → 1  in-progress: source-pure statement, exact corpus reduction, falsifiable boundary mechanism
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem, exact module build green, axiom audit PASS
- [ ] 3 → 4  publication-ready: standalone paper and external novelty review

## Corpus-led conjecture loop
- **NBBD-RMCT.1:** `bdMobiusFullErrorEnergy → 0` forces `N · deningerHarmonicPartial N ^ 2 → 0` and hence `sqrt N · |deningerHarmonicPartial N| → 0`. First implication already exists in Lean; square-root normalization remains to package.
- **NBBD-RMCT.2:** Little-o square-root harmonic charge forces little-o half-power decay of the canonical discrete Möbius--Laplace source.
- **NBBD-RMCT.3:** Little-o half-power source decay makes `r · Mellin(source)(rho+r) → 0` at every critical-line point. Combined with the corpus Mellin--zeta identity, differentiability of the pole-filled zeta factor, and existence of a critical-line zero after the RH consequence, this is contradictory.
- **NBBD-RMCT.4:** Therefore raw full-error decay and canonical complementary-tail decay are impossible. Seek strongest survivor: a frequent/limsup positive critical-scale floor rather than a restated nonconvergence theorem.

## Approach
Reuse `BaezDuarteMobiusPrefixApproximation`, `MobiusLaplaceBoundaryMultiplicity`, and `XiHeatCassiniWoldCriticalGraphNoGo`. Build only missing little-o Abel transport. At every failed strengthening, retain exact boundary law exposed by failure.

## No-go closure
- **Exact killing theorem/mechanism:** Open; proposed critical-zero radial residue versus little-o Abel vanishing.
- **Strongest positive survivor:** Open; target frequent positive values of `N · deningerHarmonicPartial N ^ 2`, then transfer through the existing full-error lower bound.
- **New insight:** Raw canonical coefficients may be too rigid at critical scale; logarithmic prefix decay does not address unavoidable critical zero residues in the complementary tail.
- **Status:** Paper proof and Lean formalization in progress. Novelty unverified.

## Log
- 2026-08-27 — created directly in stage 1 after corpus search isolated exact boundary contradiction route; frontier map left untouched.
