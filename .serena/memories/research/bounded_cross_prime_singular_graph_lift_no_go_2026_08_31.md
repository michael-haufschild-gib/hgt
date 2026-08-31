# Bounded cross-prime singular-graph lift no-go (2026-08-31)

Qualifying result: killed bounded post-completion irreducible cross-prime source lift as common HB/FZZ-P/PW-B/RBH Ward producer.

## New Lean module
- `formal/GaloisForLFunctions/RHTower/DeningerBigWittCrossPrimeSingularGraphLiftNoGo.lean`
- umbrella import in `formal/GaloisForLFunctions/RHTower.lean`

## Main theorem
- `RHTower.boundedCrossPrimeSingularGraphLiftRouteKilled`
- Stronger theorem: `no_continuousAt_zero_crossPrimeAmbient_to_oneLegGraph_reconstruction`
- Positive survivor: `crossPrime_oneLegGraph_reconstruction_not_continuousAt_zero`

## Mathematics
Canonical source-normalized prime-two/right-prime Big-Witt rows have ambient Calderón–Witt `ℓ²` admissions tending to zero, while their exact one-leg graph admissions tend to the nonzero vertical trace generator. Any exact finite-packet reconstruction continuous at ambient zero would send same sequence to both zero and nonzero generator, contradicting Hausdorff uniqueness. No linearity assumption needed. Bounded linear lift is a corollary.

Killed chain:
`bounded cross-prime source lift → singular one-leg Gamma reporter → joint source/Gamma naturality → SharedFourRouteWardEndpoint → HB/FZZ-P/PW-B/RBH → RH`.

Survivor: viable common Ward producer must change source topology before completion and be singular/unbounded at origin; no bounded/nonlinear origin-regular repair after existing `ℓ²` completion.

## Documentation
- `docs/drafts/pipeline/3-formalized/bounded-cross-prime-singular-graph-lift-no-go.md`
- `docs/drafts/pipeline/5-failed/bounded-postcompletion-cross-prime-source-lift.md`
- frontier map remained read-only.

## Verification
- direct `lake env lean` PASS
- targeted `lake build GaloisForLFunctions.RHTower.DeningerBigWittCrossPrimeSingularGraphLiftNoGo` PASS (11486 jobs)
- five new theorem axiom audits: `[propext, Classical.choice, Quot.sound]`
- corpus research tool indexes all declarations
- lint: new module clean; repo-global failure only unrelated concurrent/pre-existing `HTGeometry.DominantConstantTermWild`, `HTGeometry.RittLevelThreeSeed`, and `sorry` at `RittLevelThreeSeed.lean:203`
- scratch files removed; no own Lean processes left.

## Novelty audit
Corpus search found two limiting statements separately, not graph-valued reconstruction no-go. External primary audit: Deninger arXiv:1807.06400 and arXiv:2508.05329; Connes–Consani arXiv:1910.14368. No exact collision found; novelty claim limited to exact formal architecture.
