# Source-native reflection comparison and RH selection interface

- **ID:** ULF-ISDM-2
- **Stage:** 1-in-progress
- **Type:** PRODUCER THEOREM / RECIPROCAL FORMATION / RH SELECTION INTERFACE
- **Status:** [OPEN PRODUCER] [NOT PAPER-PROVED] [NOT LEAN-READY] [NONCIRCULARITY REQUIRED]
- **Parent:** `source-formation-interaction-work-qfi-conservation-and-cofinal-phase-law.md`

## Exact open target

Construct, without using a Xi zero or its real part, a source-native comparison between the
formations at `sigma` and `2-sigma` that intertwines functional-equation reflection and preserves
the global interaction-formation phase.

The proved executor is already available:

\[
 \operatorname{Phase}(\sigma)=\operatorname{Phase}(2-\sigma)
 \quad\Longleftrightarrow\quad \sigma=1
 \qquad(0<\sigma<2).
\]

With `sigma = 2 Re rho`, a noncircular producer satisfying that comparison would force
`Re rho = 1/2`. The producer itself is not supplied by the phase classifier.

## Required gates

- [ ] source construction specified independently of any zero
- [ ] reflection intertwining proved on paper
- [ ] preservation of global formation phase proved on paper
- [ ] hostile audit rules out fitting from `rho` or `Re rho`
- [ ] novelty and dependency audit
- [ ] only after paper closure, exact Lean formalization and RH executor

## Hostile boundary

The implication from phase preservation to `sigma=1` is proved and formalized. Existence of a
source-native phase-preserving comparison is open. Treating the classifier as that producer would
be circular and is forbidden.
