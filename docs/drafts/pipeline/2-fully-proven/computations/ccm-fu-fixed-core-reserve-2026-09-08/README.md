# Fixed-core signed energy reserve diagnostic

Numerical evidence only; this directory does not establish a paper theorem or
supply a Lean premise. The [predeclared protocol](../../../1-in-progress/ccm-fu-fixed-core-reserve-sign.md)
specifies all cutoffs, states, thresholds, selection and audit rules.

## Execution and reconstruction

Ran `screen.py` on the supplied RunPod host on 2026-09-08, with eight cutoff
workers and one thread per numerical library, under one 60-second foreground
deadline. The screen took 0.409 seconds; the complete run including the
80-digit audit took 6.565 seconds. Exit status was zero.

For S={2,3,5,7,11,13}, computed all 64 processed subsets and 192 directed
mergers at every M=2^k, k=9,...,18. Every source index and surviving label is
included. Channels use the proved clipped dilation identity, retaining its
last partial square-root-clock block. `summary.json` contains all states and
edges. `stdout.log` records the diagnostic classification and selected audit.

The selected audit independently reconstructed divisor counts and Möbius signs
from prime exponents and recalculated the complete source at 80 digits. It
uses the same proved clipped identity. Only this preselected edge received
the high-precision audit; other edges remain floating-point diagnostics.

## Findings

91 edges have normalized release (Q_P-Q_(P+q))/M² below -1e-8 at all three
largest cutoffs. All 91 parents also have Q_P<=Q_empty at those cutoffs.
There are 14 parents for which every remaining prime **in S** has negative
release. One is P={2,3}; its four tested successors add energy despite the
parent using approximately 14.3% of the original energy budget.

The predeclared strongest edge is P={3,5,11,13}, q=7. At M=262144 its audited
normalized release is -0.0001210322426141682276026738976596830389987760567192330;
the nonempty-fibre contribution is -0.0001210317306016523855720375448136972961939812988480942.
The two normalized energy discrepancies between float and high precision
are below 6.3e-18. The parent uses approximately 34.8% of the original budget.

These observations direct the next proof toward the signed dilation correlation
of the actual fixed-core source. They do not establish any eventual sign,
exclude primes outside S, or refute an admissible completion. In particular,
Q_P<=Q_empty is weaker than full successor-envelope admission. No larger
screen or repeat is scheduled.

## Reproducibility and cleanup

`SHA256SUMS` records hashes matched between the remote and downloaded files.
The remote process completed; an explicit process check found no worker
remaining in the owned directory. The three remote files and directory were
then removed. No computed result is used in a formal proof.
