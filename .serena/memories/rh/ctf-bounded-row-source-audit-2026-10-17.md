# CTF bounded-row source audit — 2026-10-17

Selected CTF for the unbounded cross-route RH objective. No qualifying contribution. Original chronological bounded-row construction remains unresolved; no repository Lean changes. Preserve the read-only frontier and concurrent work.

Own card: `docs/drafts/pipeline/1-in-progress/ctf-bounded-row-arithmetic-inversion-2026-10-17.md`. It records nine mechanisms, evidence, verification, and remaining gaps.

Key source findings:
- `ChronologicalMobiusEscape`: raw/sharp Mobius rows converge pointwise; even a bounded L2 subsequence implies RH via weak convergence and Banach-Saks. Pointwise convergence does not imply full-norm convergence.
- `ChronologicalRawHeatObstruction`: raw errors unconditionally do NOT converge to zero in full L2, using a critical-line zero. Existing positive survivors: cofinal positive raw-error floor; successful arrays need a nonvanishing correction cofinally.
- `ChronologicalDampedRepair` admits bounded arithmetic coefficients and a small infinite-response error, but finite residuals retain raw errors at N/d. `ChronologicalDampingRigidity` plus the raw obstruction excludes every vanishing geometric-response damping schedule in [0,1/2].
- `ChronologicalArithmeticAveraging`: positive decreasing weights with terminal weight tending to one preserve the raw zero-convergence condition. Successful power damping cannot have epsilon_N log N tending to zero; a cofinal positive scale floor already exists. Substantial averaging remains open.
- `ChronologicalRepairCoefficientBoundary`: deep nonlinear Fermi repair under a fixed coefficient budget is exactly a Mobius prefix with at most its first terminal correction; the next coefficient costs at least m-1.
- `ChronologicalLeastNormMomentRepair`: every fixed-order tail moment repair has a cofinal positive floor. `ChronologicalGrowingMomentSource` already constructs unit-bounded, zero-charge rows with a half-length exact Mobius prefix and increasing exact odd moments. Full L2 convergence still needs the shrinking (0, log N/N) window. `ChronologicalGrowingSignedProjection` retains signed Mertens and harmonic channels; no new window cancellation was found.
- `ChronologicalBoseDilateCompleteness`: prime dilates are already complete without coefficient control. `ChronologicalBoundedRowMobiusRigidity` proves positive floors for bounded prime-only and one-plus-primes rows. Density does not provide a bounded source.
- `ChronologicalDilationDifferenceFreedom`: small differences have binomial coefficients and do not by themselves construct residual cancellation within the prescribed coefficient box.
- `ChronologicalMobiusSubsetSums`: greedy rounding is available, but the successful Riesz input uses RH. This supplies no unconditional subset selection.
- `ChronologicalDualSamplingCriterion`: full Mobius inversion is still needed on the entire L2 domain with absolutely summable Bose samples. Scalar absolute convergence and dense-core validity alone do not justify pairing with the pointwise raw limit. Continuous real-dilation regularization inspected in the Fermi witness source has no established transfer to integer-only chronological samples.

Two documented deep searches used; second was partial because filter/judge returned malformed/incomplete JSON. Available Lean hits were used; no repeated retry, web, historical research Markdown, numerical experiment, or novelty audit. Compiler metadata largely pending/stale; ten selected direct source/olean timestamps were checked, without claiming a dependency rebuild.

A scratch import/name/axiom audit of 22 existing declarations passed `lake --old env lean /tmp/hgt_ctf_audit.lean`, exit 0, no errors/warnings. All use only propext, Classical.choice, Quot.sound. Final direct source verification and scratch cleanup are recorded in the card. No new theorem was manufactured from the existing exclusions or receivers. Full cross-route goal remains incomplete.
