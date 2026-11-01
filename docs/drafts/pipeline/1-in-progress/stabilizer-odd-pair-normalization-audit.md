# Audit the odd-pair stabilizer normalization

- **Stage:** 1-in-progress
- **Type:** CANDIDATE / SOURCE NORMALIZATION
- **Parent:** [Argon routes](../1-in-progress/argon-quasi-rh-and-critical-proportion.md).

## Exact source

`ParitySensitiveRamanujanStabilizerTransfer.stabilizerModelOddCoalSum` sums over odd
integer pairs and assigns weight

`(1/4) parityStabilizerWeight(Q, |n−m|)/sqrt(nm)`.

`parityStabilizerWeight(Q,h)=2 Σ_{q≤Q, q odd} μ(q)² c_q(h)/φ(q)²`.
At Q=1 the raw arithmetic weight is therefore 1/2 on odd pairs. Such pairs have
density 1/4 in a full integer rectangle, so this model's full-period raw mean is 1/8.
The exact subtraction identity remains valid for every normalization; it does not
establish a centered Hardy–Littlewood comparison.

## Target

Audit the claimed density normalization against complete-period Ramanujan orthogonality
and the actual von Mangoldt weight. Prove the unique coefficient giving raw mean one
on complete odd-coordinate periods: the candidate coefficient is 2 rather than 1/4.
Extend from Q=1 to finite odd-modulus packets, where every nonconstant Ramanujan mode
has zero complete-period mean.

The positive survivor should be an exact normalization and corrected signed discrepancy
identity. A full-period mean audit alone does not settle the narrow signed coalescent sum,
whose kernel can cancel constant errors. Do not infer failure of the actual prime-pair
conjecture or change existing definitions until this distinction is formalized.

## Complete-period proof route

For each positive q dividing M, shifted Ramanujan orthogonality against conductor
one gives `Σ_{i<M} c_q(i+n)=M·1_{q=1}`. The existing exact period-square identity
for `ramanujanAutocorrelationWeight` then gives
`Σ_{i,j<M} c_q(|i−j|)=M²·1_{q=1}`. Odd-conductor invariance under doubling
transfers this identity to `|(2i+1)−(2j+1)|`.

Thus every finite odd-modulus packet with Q≥1 and common positive period M has
`Σ_{i,j<M} parityStabilizerWeight(Q, |(2i+1)−(2j+1)|)=2M²`.
After normalization by `(2M)²`, scalar β has mean β/2. Mean one therefore forces
β=2; the source's β=1/4 has mean 1/8. Choosing M=Q! discharges the common-period
condition. No narrow-aperture or oscillatory-kernel conclusion follows from this identity.

Corpus search found the shifted orthogonality and period-square building blocks,
but no matching stabilizer normalization theorem. An actual prime comparison can
use `RHTower.tendsto_sum_primesBelow_log_div`; its source and dependencies still
need checking before any discrepancy-limit claim.

## Stronger source comparison to check

Let W₀ be the packet value at lag zero. Removing coordinate one and the diagonal
from the full odd-coordinate rectangle should leave exactly
`2M²−4M−(M−2)W₀`. For fixed Q this retains raw mean β/2 as M tends to infinity
through complete periods. The actual distinct odd-prime logarithmic weight has
mean one by the prime number theorem, with diagonal cost `O(X log X)`.
Thus the source's raw full-rectangle discrepancy should have limiting mean 7/8;
the uniquely normalized scalar two should give zero. The aperture and signed
kernel are still absent from this comparison. These stronger claims are not
formalized and are not used as premises.
