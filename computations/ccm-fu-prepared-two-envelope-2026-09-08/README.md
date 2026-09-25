# Prepared-core prime-two envelope diagnostic

## Frozen question and decision

[BRIDGE diagnostic], not a primary universal conjecture. Does inserting
prime 2 preserve the complete successor envelope at every actual core
containing all odd primes below 15? The known cutoff-17 example excludes
separate matching-energy contraction; it does not decide this envelope
comparison. The new macroscopic-prime repair theorem does not handle 2.
Neither outcome is assumed or predicted by the existing bounds.

Enumerate EVERY cutoff M=16..96 and EVERY subset P of primes below M
which contains {3,5,7,11,13} and excludes 2. Compare Psi(M,P+2) with Psi(M,P),
retaining every available successor on each side. Record the number of
violations, their first state and worst margin at each cutoff. Also record
whether each flagged state meets the original diagonal budget and whether
its post-2 envelope exceeds that same budget. No random sampling or extension
of the range after seeing results.

A violation triggers an independent 80-decimal reconstruction of the FIRST
flagged state, its entire two envelopes, every signed fibre, and all immediate
repair choices. This identifies the actual remaining successor causing the
excess and whether a further prime restores the parent envelope. If no
violation occurs, report only finite evidence, not a universal theorem.
No floating-point result may become a Lean premise.

## Method and limits

Compute original signed divisor-Abel coefficients directly from the divisor
counting defect. Group them after the prepared core. The energy at each
processed mask is the subset sum of the XOR autocorrelation of this sparse
signed field; this follows from equality of the remaining labels exactly
when their symmetric difference was processed. Use NumPy subset transforms
and eight independent cutoff workers, one numerical-library thread each.
Compare with tolerance 1e-11*max(1,original diagonal energy).

Run only on the supplied RunPod. Enforce 50 seconds internally and a
60-second external timeout, then download script and results and remove
owned remote files/processes. No longer or larger follow-up scan is allowed
by this design. Algebraic follow-up is determined by the observed witness.

## Result

RunPod completed all 3,185,446 prepared-core states in 0.377 seconds with
eight workers. There were 526 pointwise envelope increases. The first is
M=84, P={3,5,7,11,13}, where the maximizing successor is 17 on both sides:

- Before inserting 2: Psi=3.95782109875967318627.
- After inserting 2: Psi=4.01950652270180606914.
- Increase: 0.06168542394213288287.
- Current energy decreases from 3.17224714582802528120 to
  3.06496666892338508691.

The independent 80-decimal reconstruction confirms the strict increase,
retaining both complete successor lists and all signed source fibres in
`summary.json`. No tested prepared-core state admitted by the original
diagonal budget violated that budget after inserting 2. This is only a
finite observation; pointwise envelope monotonicity is already numerically
false. No numerical counterexample has been promoted to a Lean theorem.

The positive replacement is to charge the new envelope cost to the OTHER
remaining primes. Their bounded quotients give an O(M^(3/2)) front cost
under a quadratic budget, even for the prescribed small prime 2. Actual
source-square reserve can then pay that cost. The observed current-energy
decrease does not remove the need to control the new successors.

Remote directory `/tmp/ccm-prepared-two-UvoLxo` and its completed processes
were removed. No expanded or repeated scan was run.

SHA256:

- `screen.py`: `1e86bbf78bbd71583706afcd31f99d54b47951f446cfc6fee05c87a42b189ec4`
- `summary.json`: `e92f3d2f95fe82f8c6fa029756adea504ef5812a6779d2fcee731013bdb3da3c`
