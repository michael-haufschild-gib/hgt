# Goal ledger: 100 significant new cross-route theorems

Status: ACTIVE. Count verified for this goal: 1 / 100.

## User requirements

Completion requires 100 significant new cross-route theorems, using the whole
local Lean corpus for leads. Each must structurally overcome a hard obstacle
and enable a new class of solutions in at least one RH route. Improved bounds,
new RH equivalences, receivers with the missing input assumed, routine bridges,
and bookkeeping lemmas do not satisfy the requested standard.

All proofs must be unconditional and audited in Lean without new axioms,
unproved source premises, numerical experiments, full builds, or heartbeat
increases. Keep one owned build process at a time, wire finished leaves into
their umbrellas, and clean owned temporary artifacts. No web research or old
research Markdown as evidence. Preserve unrelated worktree changes.

## Counting rule

Count an independently meaningful mathematical result only after its exact
statement, complete paper proof, local-corpus comparison, cross-route inputs,
structural consequence, Lean leaf audit, axiom audit, and umbrella wiring are
recorded. One result split into many lemmas or modules counts once. External
novelty is not claimed: user forbids external novelty research.

## Verified contributions

1. Actual-prime realization of arbitrary compact-clock controls with vanishing
   normalized quadratic diagonal cost. Card:
   `../3-formalized/mc-prime-clock-realization-2026-10-16.md`.
   Inputs: compact-clock separation (complete Abel source, Fourier–Borel
   detection, critical-line zero supply), prime-window capacity from the PNT
   corpus, and exact terminal divisor-fibre geometry. Paper proof complete;
   three Lean leaves compile cleanly; all eight public declarations have
   only standard axioms; all three imports are wired. Counted once.
   Global lint remains red on unrelated concurrent unwired modules and
   generated-file drift; the card records the exact failing modules.

## Working plan

1. Contribution 1 complete. Recheck significance and exact scope before
   counting every subsequent result; routine bridges do not qualify.
2. Revisit the entire Lean corpus between contributions, including HTGeometry
   and other theorem areas where mechanisms apply. Avoid a single-route loop.
3. Record failed conjectures, their exact obstruction, and positive survivors.
4. Repeat conjecture, attack, proof, formalization, and significance review
   until 100 qualifying results are verified. Do not mark the goal complete
   on partial progress, successful helper proofs, or an arbitrary milestone.

## Uncounted next lead

Investigate a source-domain strengthening involving CHMD, after finishing the
current candidate. Whole-corpus search identified
`CHMDCompactStationaryJump.integrable_stationaryJump` and the HTGeometry
Sobolev derivative/translation machinery. Source reads confirm the former
requires actual jump-domain admission; uniform convergence alone does not
supply it. A proposed positive clock-cone synthesis in a Sobolev or jump-graph
topology is therefore a new open conjecture, not a corollary of the current
candidate. Audit the literal Abel derivative and dual distribution transform
before asserting it. Do not assume classical smoothness across arithmetic
breakpoints or count routine Sobolev estimates as a contribution.

## Environment

`update_plan` is not exposed in this session; this file carries the persistent
plan and audit ledger. Serena symbol access rejects the ignored Lean tree;
use direct Lean source reads and precise patches for that tree. Operational
AGENTS files and relevant Serena memories were read. `docs/architecture.md`
and `docs/testing.md` do not exist. Research-service hits had stale snapshot
warnings, so direct Lean audits remain authoritative.
