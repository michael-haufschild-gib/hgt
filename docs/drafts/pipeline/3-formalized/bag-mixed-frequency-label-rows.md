# BAG actual mixed label rows, collisions and masked assembly

For fixed complex u,v and nonzero real tau, put L=log N,
s=1+u/L, t=1+v/L+i*tau. The ORIGINAL four distinguished-label rows
over primes<=N, divided by L, tend to1-E(u),1,1-E(u),1-E(u).
Every ORIGINAL pair/triple collision divided by L tends to0.
The collision theorem is stronger: it holds for every real tau, including0.
The COMPLETE original masked response divided by L^3 tends to(1-E(u))^2,
retaining both exclusions and the allowed first/second coincidence.

Proof: retain the prime phase as a compact unit-circle parameter in the
exact rational profiles. Compact zero-slice continuity controls the entire
prime tail; the fixed-prime denominator (1-theta/p)/(1-1/p) is nonzero.
Actual oscillatory prime windows remove the remaining phase terms.
The continuous weight -z*log z vanishes on the collision slice. The exact
masked expansion includes every pair correction and the triple term.
No prime estimate, row bound, convergence, or RH premise is assumed.

Leaf: `formal/GaloisForLFunctions/RHTower/ChiRamanujanMixedLabelRows.lean`,664lines/API5.
Actual-source theorems:
`criticalMixedMellinResponseRow_tendsto`,
`criticalMixedMellinCollisionMoment_tendsto`,
`criticalMixedMaskedMellinResponse_tendsto`.
Scratch14241 emptyPASS for rows/collisions; final foreground production7092
emptyPASS for full leaf via `lake --old env lean ... -o ...olean`.
Axiom35601 PASS: all5 public declarations use standard3 only.
Index41583 PASS/API5; umbrella import once. Lint66985 terminal1:
11 unrelated unreachable-module errors,174 warnings; none in either01ar leaf.
No computations, added axioms, placeholders, heartbeat changes,
full/umbrella builds, commits or pushes. P2 paper and stronger collision
re-audit: `bag-mixed-frequency-label-rows`.

This closes M5, not full M1. The original mixed unlabelled/cofactor and
completed labelled assembly still await Lean formalization; P2
`bag-mixed-frequency-completed-source` gives the complete pointwise paper
proof. Compact-uniform source control, actual moving physical profiles and
tails, signed axes norm saving, growing moments/cofactors and deterministic
common-height return remain hard open obligations. RH goal ACTIVE.
