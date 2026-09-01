# Source–Gamma central-module ghost rigidity

- **ID:** SHARED-WARD-CENTRAL-GHOST
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Nonzero prime-independent module-valued ghost legs satisfying central physical Gamma Ward equations at primes two and three force neutral horizontal grade.

## Consequence

For every positive finite matrix rank, universal central-ghost descent over Xi support is equivalent both to the shared HB/FZZ-P/PW-B/RBH Ward endpoint and RH. This kills all matrix/rank enrichment that leaves Gamma action central. Survivor: genuinely prime-mixing, noncentral source dynamics before projection/scalarization.

## Proof

One-prime Ward gives `v = p^(2t) • u`. Primes `2,3` give `2^(2t) • u = 3^(2t) • u`; `u ≠ 0` and real-module torsion-freeness give equality of scalars; logarithmic injectivity gives `t=0`. Neutral grade supplies a nonzero matrix witness at every positive rank.

## Lean certificate

- Module: `GaloisForLFunctions.RHTower.SourceGammaCentralModuleGhostRigidity`
- Generic theorem: `primeGammaCentralModuleGhost_two_three_rigidity`
- Closed certificate: `sharedWardFiniteMatrixCentralGammaGhostRouteKilled`
- Umbrella: `GaloisForLFunctions.RHTower`
- Direct `lake env lean`: PASS
- Targeted `lake build GaloisForLFunctions.RHTower.SourceGammaCentralModuleGhostRigidity`: PASS
- Axioms: only `propext`, `Classical.choice`, `Quot.sound`
- Formal lint: new module reachable and clean; repository lint still fails on unrelated pre-existing unreachable modules.

## Novelty audit

Corpus had scalar shared-ghost rigidity, direct-sum projection no-go, and fixed PSD scalarization no-go, but no module-valued central-character classification. August-2026 primary-source audit found screw/operator RH criteria and limiting self-adjoint constructions, not this cross-prime rigidity theorem.
