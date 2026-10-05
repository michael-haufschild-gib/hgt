# BAG growing joint unlabelled source — Lean audited

Paper: [joint growing source law](../2-fully-proven/bag-growing-joint-base-limit.md).
Source: ChiRamanujanJointBaseLimit.lean, 251 lines, two public theorems,
one definition. The entire unlabelled valuation trace retains both original
coprime cofactors, growing cutoff, and logarithmic Mellin displacements.

Production87210: lake --old env lean on this leaf with its own -o target,
exit0 and empty output. Axiom44838 checks all three public declarations:
only propext, Classical.choice, Quot.sound. Index29284 passed; all three
API entries verified. Umbrella import occurs once. Lint40654 reports
43 unrelated unreachable modules and 174 existing warnings; no finding
in either new leaf. Global lint is NOT clean.

The full cofactor-completed Euler product tends to exp(J) for every fixed
complex displacement pair. With both displacements nonzero, the actual
completed weightedTrace has the same moving double-pole residue. The
regular cubic correction tends to1 via local uniform convergence along
the cofinal prime cutoffs. No replacement cofactor or factorized physical
profile is assumed.

This does not establish the complete distinguished-label source limit,
compact-uniform parameter convergence, or physical axes cancellation.
The exact collision-aware assembly and continuity proof plan remain in
P1 bag-growing-near-pole-source. No new axiom, numerical experiment,
heartbeat override, subagent, full build or umbrella build.
