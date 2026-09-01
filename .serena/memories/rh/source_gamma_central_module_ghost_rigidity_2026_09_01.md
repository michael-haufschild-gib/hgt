# Source–Gamma central-module ghost rigidity (2026-09-01)

- New module: `formal/GaloisForLFunctions/RHTower/SourceGammaCentralModuleGhostRigidity.lean`.
- Corpus basis: scalar shared-ghost rigidity, channel-resolved naturality no-go, PSD scalarization no-go.
- Theorem `primeGammaCentralModuleGhost_two_three_rigidity`: for any real module, nonzero prime-independent forward/reflected legs satisfying central physical Gamma Ward equations at primes 2 and 3 force `t=0`.
- Closed theorem `sharedWardFiniteMatrixCentralGammaGhostRouteKilled`: for every positive finite matrix rank, pointwise ghost existence iff neutral grade; universal Xi-support existence iff `SharedFourRouteWardEndpoint` iff RH.
- Killed class: arbitrary singular/non-Hermitian/indefinite finite matrices, and generically any real-module enrichment, while Gamma action is central and legs are prime-independent.
- Survivor: genuinely prime-mixing/noncentral source dynamics before projection/scalarization.
- Direct Lean, targeted module build pass. Axioms only `propext`, `Classical.choice`, `Quot.sound`. Umbrella wired. Global lint failure is unrelated pre-existing unreachable modules.
