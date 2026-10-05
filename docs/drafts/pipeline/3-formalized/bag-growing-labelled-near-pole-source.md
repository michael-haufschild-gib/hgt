# BAG full growing labelled near-pole source — Lean audited

Paper: [full source law](../2-fully-proven/bag-growing-labelled-near-pole-source.md).
Original criticalCompletedConeEuler with both growing cofactors and both label
exclusions has the explicit pointwise joint logarithmic double-pole limit.
All four actual response rows and all exact collision corrections are handled.
No additional analytic or RH premise occurs in the actual-family theorem.

Production leaves, each audited with lake --old env lean and its own -o target:
- ChiRamanujanMovingResponseWindow:164lines,2theorems;57016 empty PASS.
- ChiRamanujanMovingLabelRows:381lines,2theorems/4defs;3369 empty PASS.
- ChiRamanujanGrowingLabeledSource:81lines,2theorems;88601 empty PASS.
- Updated ChiRamanujanMovingCofactorLimit:454lines,8theorems/2defs;95159 empty PASS.
- ChiRamanujanMaskedMellinSource:294lines,4theorems/6defs;22902 empty PASS.

Axiom71945 audits all30 public declarations across these five leaves: only
propext, Classical.choice, Quot.sound. Index69878 passed, API30/30 and each
umbrella import once verified. Lint66470:23 unrelated unreachable modules,
174 warnings; no finding in these leaves. Global lint is NOT clean.

New analytic mechanism: zero-slice compact continuity plus fixed-prime-head
continuity suffices for a moving logarithmic prime window. The continuous
collision weight -z*log(z) has zero zero-slice, so every exact collision
moment divided by logN tends to zero with no uniform-norm premise.

The conclusion is pointwise for fixed nonzero complex pairs (Complex units),
not compact-uniform convergence and not signed physical saving. Next work:
actual moving-line Mellin pairing, uniform profiles/tails and coupled physical
cancellation. No numerical experiment, subagent, added axiom, heartbeat hack,
full build or umbrella build. All audits are targeted leaves.
