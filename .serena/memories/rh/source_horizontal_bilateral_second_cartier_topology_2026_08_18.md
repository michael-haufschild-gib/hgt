# Source-horizontal bilateral second-Cartier topology (2026-08-18)

## Result
Constructed unconditional literal-source, non-scalar bilateral Hardy descent.

Let A = Z[q,q^-1], g=q-1, I=(g), Q=A/I^3. In Q:
- F=[g], R=[sigma(g)], G=[g^2].
- F+R=G.
- G != 0.
- F,R are integrally independent, so generated lattice L is Z^2.
- inversion is involutive on g and fixes G modulo I^3.

L is defined literally as range of the coordinate map Z^2 -> Q. Canonical complexification L -> C^2 is injective. For lambda != 0, Hardy descent (a,b) |-> a h_+(lambda)+b h_-(lambda) is continuous, injective, range finrank 2. It sends F,R,G to positive half, negative half, bilateral eigenfamily; G image is Stokes-flat.

Actual Xi/Gamma-Julia endpoint composite has domain L, preserves nonzero Euler-Wold endpoint coefficient and Xi support multiplicity. For strict-right Xi, G image is not moderate. General sharp firewall:
- G image moderate iff norm lambda=1.
- both orientation images moderate iff norm lambda=1.
Therefore theorem is not RH; open core is a source-derived physical order/moderation law for nonzero G after Xi selection, or impossibility of such law.

## Files
- formal/GaloisForLFunctions/RHTower/SourceHorizontalBilateralSecondCartierTopology.lean
- docs/drafts/pipeline/3-formalized/source-horizontal-bilateral-second-cartier-topology.md
- wired import in formal/GaloisForLFunctions/RHTower.lean (umbrella not built)

## Key theorem
sourceHorizontalActualXiEndpointSecondCartierHardyDescent_capstone

## Verification
- direct lake env lean leaf passed cleanly
- exact leaf lake build passed
- axiom audit: only propext, Classical.choice, Quot.sound
- no sorry/admit/axiom/opaque/unsafe in module
- lint recognizes module as umbrella-reachable; unrelated concurrent unreachable modules remain
- no stale Lean process

## Research judgment
Initial abstract C^2 construction was rejected as insufficiently source-derived. Final proof includes literal quotient range lattice, canonical base-change diagram, and actual Xi endpoint composite. Augmentation algebra is classical; exact cross-corpus identification is NOVELTY UNVERIFIED.