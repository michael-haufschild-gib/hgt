# Complete the review's 31 work tasks

- **ID:** review-2910-work-programme
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / integration programme
- **Source:** [obstacles summary, §2.1](../../../reports/review-2910/obstacles-summary.md)
- **Statement:** Finish and formally audit every deliverable W01–W31, preserving each task's scope.

## Scope and completion gates

The source table is the authoritative specification. The attachment explicitly excludes the
`hgtl7` skill and numerical computations. Finite-table tasks therefore require exact symbolic
identities or proof-certified analytic enclosures; exploratory numerical output is not evidence.
Conditional compositions requested by the table must prove the complete implication/equivalence,
without assuming any additional analytic input. No conditional theorem counts as proving RH.

For each row: inspect current Lean statements and dependencies; search the local corpus before
mathlib; record the full paper argument; formalize it; check each affected leaf with
`lake --old env lean`; inspect transitive axioms; wire umbrella imports without compiling umbrellas.
No row is complete merely because a related theorem already exists or a weaker conclusion checks.

## Deliverables

| ID | Required scope | Status / evidence |
|---|---|---|
| W01 | Maximal reach of the Trans-Metzler perturbation scheme; certified floor as a function of overlap. | Exact optimum of the current three displayed bounds formalized and audited; reference-floor and analytic-constant improvements remain. [Card](review-2910-w01-optimal-certified-perturbation-floor.md). |
| W02 | Single-prime flips p≥11 and cofinite flips: fixed-ratio positivity or negative atomic witnesses. | Open. |
| W03 | Optimize Robin–Euler profile threshold and narrow twin survival; decide sharp transition. | Open. |
| W04 | Steklov weights q!(log q)^((1+ε)q), receiver β>1, exact quasi-analytic edge. | Open. |
| W05 | Dependency-closed integration: ZeroSideStratum, LiouvilleTwinSelectivity, AKLT, ASRP, CACT touching, ACS Haar prime edges, loop spherical function. | Open; preserve existing workspace edits. |
| W06 | Explicit head sizes in every finite-index theorem; growing-prime first-layer constants versus detail reserve. | Open. |
| W07 | Actual ζ kernel: finite-support tower-Hasse theorem, infinitely many positive towers or one non-blind tower. | Complete: [proof and audit](../3-formalized/review-2910-w07-actual-zeta-tower-hasse.md). |
| W08 | Certified translated Weil entries and Stirling smooth/sawtooth inversion tables, retaining cancellation. | Open. |
| W09 | Complete multiresolution Grams: orbits, details, cross-level blocks, Gamma, both poles. | Open. |
| W10 | Chen–Gupta–Li continuation/contour capstone; exponent/modulus threshold; q=1 specializations. | Source conflation found: CGL proves density; linked OpenAI strip argument is separate. Original endpoint retained for independent audit. [Correction and plan](review-2910-w10-distinguish-density-and-zero-exclusion.md). |
| W11 | Optimal positive-definite-majorant narrow-strip pair-energy bound; comparison with E(1/9)≤4. | Open. |
| W12 | Explicit shallow and deep energy constants; comparison with 3/20. | Open. |
| W13 | 70% or simple near-line off-line dichotomy with explicit forced proportion. | Complete: [proof and audit](../3-formalized/review-2910-w13-seventy-percent-near-line.md). |
| W14 | Slack on [3/4,1), 70%/75% displacement thresholds, actual-Gram negative-part credit. | Complete: exact model thresholds and actual projected displacement credit, [proof and audit](../3-formalized/review-2910-w14-displacement-credit.md). |
| W15 | Gabor-pinching slack optimization. | Open. |
| W16 | Compact-time heat counts, 2/3-horizon constants, near-axis count tables. | Open. |
| W17 | Localized heat-energy evolution from pair/exterior forces and forward simplicity. | Actual simple-time derivative, finite-packet flux, collision-continuous observables and global comparison proved; dissipation capstone and final audits remain. [Card](review-2910-w17-localized-heat-energy.md). |
| W18 | Ordered Chebyshev block-pair integrals with certified ψ and VK bounds. | Open. |
| W19 | Projections, Schur residuals, radicals, bounded-window transport constants. | Open. |
| W20 | Fixed-conductor Ramanujan residual/Gram estimates; infinite-pattern greatest gaps. | Open. |
| W21 | Hecke removable values, class recombination, normalized FE, gauge finite parts. | Open; frontier reports newer existing FE sources. |
| W22 | Complete scheduling/history/cross-block/endpoint ledgers and finite-range RP escape constant. | Open. |
| W23 | Finite Möbius/pronic/Vaughan/Báez–Duarte rows with separate readout and centered energy. | Open. |
| W24 | Every supplied-strip dictionary, including balanced windows, Cesàro energy and Siegel half. | Open. |
| W25 | Compact cofactor Grams, effective pole orders, record-minimum diagonals. | Open. |
| W26 | Finite-aperture ground energies, blind minima, feasibility, shell relaxations. | Open. |
| W27 | Finite heat/Jensen/Hankel heads, both Gaussian grids, Laguerre data, first-atom analytic tail. | Open. |
| W28 | Newton/Ward/renewal/transgression/Schur/recurrence certificates; Robin/Cayley–Li/Suzuki ranges. | Open. |
| W29 | Genus-one affine A₁ arithmetic quotient, measures, convergence, constant term and imaginary roots; Garland/Q construction. | Open. |
| W30 | All named candidate calibrations, including PW-B. | Open. |
| W31 | All seven named literature topics: primary sources, proof intake and precise local applicability. | Open. |

## Working-state safeguards

Initial worktree already contained CACT affine-unit-average changes, AKLT integrality changes,
frontier/killed-route edits, and infinite-symmetry polar-divisor/chamber changes. These are not
new work of this programme and must not be reverted or silently credited as verified.

## Log

- 2026-10-29 — Read attachment and source task table. Started current-source audit; no task
  certified complete. Full scope remains W01–W31.
- 2026-10-29 — W07 leaf passed direct check and four transitive-axiom audits; umbrella wired.
  W01 optimal convex use of the existing bounds and W13 general census threshold are written,
  awaiting checks. Remaining rows retain their full original scope.
- 2026-10-29 — W13 passed direct leaf check and three standard-only transitive-axiom audits;
  root umbrella import wired. General threshold theorem specializes to 70% with coefficient
  `HD(1)−2/5−1/A−ε`.
- 2026-10-29 — W14's two leaves passed direct checks and seven standard-only axiom audits;
  both umbrella imports wired. Actual credit may vanish; no census gain is inferred.
