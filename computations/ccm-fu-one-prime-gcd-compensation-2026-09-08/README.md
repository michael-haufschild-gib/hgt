# One-prime compensation of exact gcd groups

Numerical evidence only; no interval certificate or Lean premise.
The uniform inequality and RH remain unproved.

## Frozen test

For actual divisor Abel channels C_d, let D=sum C_d^2 and let G_r be
the complete ordered off-diagonal contribution with exact gcd r.
Transfer positive G mass to negative G mass only when their labels differ
by multiplication or division by one prime. Let U be unmatched positive
mass after optimal capacity-respecting transfer. Test U<=D. With the
existing identity S^2=D+sum G, a uniform proof would give S^2<=2D.

[Research card and proof attempt](../../../1-in-progress/ccm-fu-one-prime-gcd-compensation.md).
`frozen-protocol.md` is the unmodified protocol uploaded before execution.

## Result

All 161 prescribed cutoffs passed: every integer from 101 through 256,
and powers of two from 512 through 8192. No range extension followed.

| M | Positive mass / D | Unmatched positive mass / D |
|---:|---:|---:|
| 223 | 0.80865222 | 0.25122246 |
| 512 | 0.87635681 | 0.10505310 |
| 1024 | 2.74156432 | 0.01404707 |
| 2048 | 2.46026925 | 0.13649514 |
| 4096 | 2.77987248 | 0.21932424 |
| 8192 | 2.16108237 | 0.05852545 |

The maximum U/D occurs at M=223. An independent 80-digit reconstruction
from the defining source and all channel pairs, followed by a different
augmenting-path solver, gives D=59.99466979756561086838... and
U=15.07200882771911030021.... The maximizing positive set is {6,10};
its negative neighbor union is {5,30,42,70}. Neither positive vertex is
isolated. The cut therefore detects competition for shared capacity.

At M=4096 the maximizing cut has 17 positive labels and starts at 30.
Its isolated positive mass is only 0.00567569 D, well below the full
deficit 0.21932424 D. Source non-isolation does not control the cut.
Larger cutoffs were not independently reconstructed at 80 digits.

## Checks and execution

- Supplied RunPod only; no local mathematical computation.
- Four-worker screen, one BLAS thread; 0.05636 seconds. Four-worker
  source audit; 0.09786 seconds. Separate 90-second deadlines.
- Reused saved long-double source arrays; no new source screen.
- Deterministic Dinic flow with capacities normalized by D; every edge,
  row/column load, residual and maximizing cut retained.
- Flow/cut, mass and capacity checks at every cutoff; independent
  trial-division adjacency enumeration at every M=101,...,112.
- Audit uses literal log-factorial and divisor sums, original time-sum
  channels, every channel pair, and 80-digit Edmonds–Karp flow.
- Largest audited G discrepancy from saved input: below 1.9e-15;
  normalized flow/cut discrepancy: below 1.1e-81.
- All 327 source/result/input file hashes verified after download.
  Owned RunPod scratch and local transfer archives removed; no owned
  experiment process remained. No Lean process or build was started.

## Files

`summary.json` records all cutoffs, scalars and the predetermined audit
selection. `flow_M.json` records every edge flow, positive residual,
isolated label, cut, input hash and verification error. `inputs/` retains
the exact 161 reused source arrays. `audit.json` retains every 80-digit
channel, gcd group and audited flow. `SHA256SUMS` covers all 327 remote
files; this README was added locally after verification.

The new information is finite arithmetic compensation along a fixed
prime graph and the explicit shared-capacity obstruction. Neither an
abstract matching theorem nor this finite success establishes uniform
control of every actual weighted cut.
