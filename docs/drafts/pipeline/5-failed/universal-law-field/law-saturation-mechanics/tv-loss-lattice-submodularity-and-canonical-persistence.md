# TV-loss lattice submodularity and canonical persistence — failed

- **Stage:** 5-failed
- **Claim killed:** Total-variation loss under generated identifications is universally submodular
  or supermodular on the partition/relation lattice, hence supplies a canonical convex persistence
  geometry for law formation.
- **Verdict:** [FALSIFIED BOTH DIRECTIONS] [MONOTONE ONLY] [HISTORY SURVIVOR RETAINED]

## Setup

For a finite signed profile difference `d` and a partition `pi`, let

\[
  L_d(\pi)=\frac12\sum_x |d_x|
  -\frac12\sum_{B\in\pi}\left|\sum_{x\in B}d_x\right|.
\]

This is the exact total-variation distinguishability lost after aggregating atoms along the blocks
of `pi`.  It is nonnegative and monotone under partition coarsening.

## Counterexamples

On three atoms, use the two partitions

\[
 \pi=\{\{0,1\},\{2\}\},\qquad
 \sigma=\{\{0,2\},\{1\}\}.
\]

For `d=(-1,4,2)`, the submodular inequality fails: the two intermediate losses sum to `2`, while
the meet/join side sums to `1` under the corresponding convention.  For `d=(1,-4,1)`, the reverse
inequality fails: the same intermediate side is `1`, while the meet/join side is `2`.

The failure persists when identifications are supplied by edge sets and saturated by connected
components.  For `d=(-4,2,1)`, suitable edge families on three vertices give one pair with
`L(A)+L(B)<L(A cap B)+L(A cup B)` and another with the strict reverse inequality.  Hence changing
from partitions to generated relations does not restore either lattice convexity.

## Why the conjecture failed

Loss is produced by cancellation of signed block masses.  Joining identifications can expose or
hide cancellation depending on sign placement, so there is no universal diminishing-returns or
increasing-returns law.  Persistence weights built from `L_d` are valid monotone filtrations, but
their topology carries no additional universal convexity.

## Positive survivor

Along every nested formation history, loss remains monotone and admits the exact telescoping law

\[
 L(\pi_n)-L(\pi_0)
 =\sum_{k=0}^{n-1}\bigl(L(\pi_{k+1})-L(\pi_k)\bigr).
\]

The endpoint loss depends only on the final generated identification, while first-conflict time,
local cancellation profile, and critical-path provenance can depend on schedule.  Thus the live
geometry is directed formation history, not lattice convexity.

## Do not reattempt as

- a polymatroid rank without extra sign/laminar hypotheses;
- generic submodular clustering cost;
- persistence claimed universal merely because loss is monotone;
- a scalar replacement for reporter provenance.

## Log

- 2026-08-10 — exhaustive three-to-five-atom hostile checks found strict counterexamples to both
  submodularity and supermodularity; nested-history telescoping retained.
