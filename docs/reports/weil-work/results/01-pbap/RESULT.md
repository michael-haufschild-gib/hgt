# WP01 interim result

**Verdict: BRIDGE. Full PBAP remains open.**

Lean module `RHTower/WeilWorkPBAPNullRepair.lean` constructs an explicit positive correction of every finite logarithmic defect. The repaired mixture satisfies all integer-null constraints exactly, and its full pole-plus-archimedean energy changes by at most a specified weighted total defect. The correction tests are smooth. Targeted build, direct Lean source audit, and capstone axiom audit pass. Only standard Lean axioms occur. Module is wired into `RHTower.lean`.

`RHTower/WeilWorkPBAPGramPackets.lean` now realizes every finite PSD matrix by smooth compact Weil tests, with exact autocorrelation samples at all rational logarithms of bounded denominator. Finitely many zero divisibility-diagonal sums give cancellation at **all** integer nodes. The capstone supplies an actual nonnegative finitely supported mixture in the full PBAP interface and retains its exact mass. Direct source compilation, targeted `--old` leaf build, and ten-theorem axiom audit pass. Only standard Lean axioms occur; umbrella import added.

`RHTower/WeilWorkPBAPMomentPackets.lean` now connects actual representing probability measures on the prime torus to these packets. Its integral moment matrix is proved positive semidefinite, with zero divisible entries and explicit trace. The capstone constructs a smooth, nonnegative finite mixture with mass exactly one, every integer-null constraint, and rational samples equal to the target measure's moment times the finite coefficient correlation. Direct compilation and targeted `--old` leaf build pass; final audits are recorded in `EVIDENCE.md`.

These are concrete realization and correction bridges. None supplies a sign theorem; none is claimed as a significant scientific frontier advance.

Two proposed routes failed novelty audits: scalarization already appears in corpus L248 and classical convolution-root theory; the contemplated small two-window positivity sector is covered by the current full-support theorem. The unresolved problem is still arbitrary signed mixtures with aggregate integer cancellation and both pole terms retained.

`PROOF.md` gives the exact repair proof and labels the unformalized scalarization argument. `EVIDENCE.md` records commands, sources, and lint outcomes. `TORUS-DENSITY.md` contains the closed finite-realization proof and the larger construction of exact integer-null mixtures approximating prime-torus representing measures, with an explicit obstruction to the stronger Jensen claim. The representing-measure connection and packet-mixture normalization are formalized. Prime-exponent-box counting, spectral pushforward, weak convergence, and Jensen transfer remain unformalized. The Jensen route is not retired as a proved no-go. The working card `docs/drafts/pipeline/1-in-progress/weil-work-01-pbap.md` tracks continuation. No producer or solution is claimed.
