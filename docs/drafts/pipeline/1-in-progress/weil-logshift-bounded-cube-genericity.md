# Generic moment divergence inside the bounded-history cube

- **ID:** weil-logshift-bounded-cube-genericity
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper); Lean pending
- **Source:** local Lean corpus: adaptive antipodal recovery, generic moment divergence, cofinal recovery cutoffs, and one-sided local divergence laws.
- **Statement:** In [-1,1]^ℕ, all three log-2 moments are nonsummable on a dense residual set. For every bounded history, the three summability conditions are equivalent. Generic nonsummability also holds at every shift with |y|≥log 2.

## Scope and audit
Only local Lean corpus and installed Lean API checks. Previous turn proved generic nowhere summability in unrestricted history space. That result does not imply genericity in the bounded cube. Direct corpus search and exhaustive relevant source search found no bounded-cube theorem or finite-prefix antipodal extension.

## Dependency-closed paper proof
[PROVED HERE] Modify the existing adaptive policy only at the first M steps, choosing a prescribed bounded history there. Thereafter choose ±1 opposite the current probe. Triangular stabilization still gives exact samples; each later correction has probe magnitude at least 1, and the existing diagonal/full-kernel comparison forces every later absolute log-2-weighted deviation term to be at least 1/2. Every final history value lies in [-1,1]. No new builder is needed.

For each N, the event that some n≥N+2 has absolute weighted term greater than 1/4 is open in the bounded product cube, since reconstructed coefficients depend continuously on history. It is dense: the finite-prefix antipodal extensions converge coordinatewise to any target bounded history. Their countable intersection is dense and residual by the existing corpus category theorem and the cube's Baire property. Its weighted terms fail to tend to zero, hence signed summability fails.

For any bounded history, signed summability implies both one-sided summability conditions. Conversely, either finite one-sided moment together with signed nonsummability would force the actual probe to tend to minus or plus infinity along all real cutoffs. The cofinal bounded recovery mesh excludes both alternatives. Thus the three local summability conditions at log 2 are equivalent, without any extra analytic hypothesis on cube elements.

Inward transfer extends nonsummability to every shift with |y|≥log 2. This does not assert anything about shifts |y|<log 2, nor boundedness at intervening real cutoffs.

## Plan
1. Check bounded product's category/topology APIs.
2. Generalize the existing antipodal theorem to preserve finite prefixes, factor its bounded-mesh one-sided implication, and expose shared deviation continuity; preserve existing APIs.
3. Formalize bounded prefix extensions, open dense tail events, moment equivalence, category classification, and outer-shift transfer.
4. Compile touched leaves, audit every public declaration, wire imports, refresh index, run lint, update memory, clean scratch.

## Gates
- [x] Corpus audit and dependency-closed paper proof.
- [ ] Exact Lean declarations compiled and axiom-audited.
- [ ] Imports, index, scoped checks, and global lint recorded.

## Log
- 2026-10-09 — previous turn classified verified progress; bounded-cube theorem and exact one-sided equivalence derived from existing Lean results.
- 2026-10-09 — bounded product compactness/Baire APIs verified. Generalized antipodal construction and factored bounded-mesh implication compile/export cleanly; original counterexamples retained. Shared deviation continuity compiling; bounded-cube leaf written, verification pending.
- 2026-10-09 — shared deviation continuity and all prior generic-moment declarations compile/export cleanly. New bounded-cube leaf is compiling on owned session 43948. Audit list contains all 35 public declarations across the three touched leaves.
