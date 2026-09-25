# Positive exact-gcd budget: discriminating computation

Numerical evidence only. No result in this directory is a Lean premise or
an interval certificate. The RH proof goal remains open.

## Frozen question

For the actual divisor Abel coefficients C_d(M), let D=sum C_d^2 and let
G_r be the complete ordered off-diagonal contribution with exact gcd r.
Test `sum_r max(G_r,0)<=D`. The already formal identity
`S^2=D+sum_r G_r` makes this a sufficient quadratic producer. Existing
failures of individual or binary-packet signs do not decide this budget.

[Protocol and broader corpus applicability audit](../../../1-in-progress/ccm-fu-positive-gcd-budget.md).
The protocol was written before execution. No constant or grouping was
changed after observing the result.

## Result

All 165 frozen cutoffs were processed: every integer from 101 through 256,
and powers of two from 512 through 131072. Every channel and gcd group is
retained. The constant-one candidate failed at 48 tested cutoffs. At all
165 cutoffs the complete signed cross sum remained negative.

The first tested failure, M=115, was independently reconstructed at 80
decimal digits from log-factorial, the literal divisor sum, Möbius signs,
the original square-root time weights, and every unordered channel pair.

| Quantity at M=115 | 80-digit audit, displayed approximately |
|---|---:|
| Diagonal D | 15.4570632546571346693 |
| Positive gcd mass P | 16.0841565793869973922 |
| Negative gcd mass N | 29.9652634592927361430 |
| Excess P-D | 0.6270933247298627229 |
| Complete head square | 1.5759563747513959185 |

The audit's complete reconstruction error is below `1.7e-80`; differences
from the long-double screen are below `3.4e-16` for the reported scalar
quantities. These precision checks support the numerical rejection, not
a formal inequality certificate.

The screen's largest P/D ratio is approximately 4.8119122 at M=65536.
There G_1 is negative, while large positive groups include gcd 3, 2, 5, 7,
30, and 42. Cancellation between different groups is quantitatively
important. The large-cutoff results were not independently audited at
80 digits. The experiment does not exclude a different universal constant
or establish one.

## Execution and checks

- Host: supplied RunPod SSH endpoint; no local mathematical computation.
- Screen: four worker processes, one BLAS thread, long-double arithmetic,
  90-second deadline; elapsed 1.68293 seconds.
- Audit: four worker processes, 80 digits, separate 90-second deadline;
  elapsed 0.02324 seconds.
- Screen computes complete divisibility cross sums and recovers exact-gcd
  groups by descending divisor subtraction.
- Every cutoff passes the full sum reconstruction. All channel pairs are
  independently checked at every M=101,...,112; all defining time-sum
  channels are independently checked at M=101,...,104.
- The independent M=115 audit uses direct gcd grouping of all pairs,
  not the screen's divisor inversion.
- No cutoff extension, fitted coefficient, or confirmation run followed.

`summary.json` records every scalar result and selected audit cutoff.
`cutoff_M.npz` retains C, G, and the divisibility cross sums B;
`cutoff_M.json` records the positive groups and verification errors.
`source.npz` retains the screen's Möbius and divisor-defect arrays.
`audit.json` retains every 80-digit channel and gcd group.
`SHA256SUMS` records all 335 remote source/result files before download.
All 335 files were downloaded and their hashes verified locally.
The owned RunPod directory was removed after verifying that no experiment
process remained. No Lean process or build was started for this diagnostic.

## Mathematical implication

The tested bound fails while the complete signed estimate survives at
the tested points. Keep the exact identity `S^2=D+P-N` and seek a joint
arithmetic bound on P-N. Neither a primitive-only upper bound nor this
positive-part diagonal budget replaces that full comparison. No new
Lean theorem or formal no-go is claimed by this experiment.
