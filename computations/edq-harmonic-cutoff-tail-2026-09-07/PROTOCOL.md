# Harmonic cutoff selection versus the complementary weighted tail

Status: frozen before execution. Numerical diagnostic only; no asymptotic or Lean certificate.

## Uncertain question and consequences

Existing identities determine the initial segment from one scalar H_N, but do
not determine whether small H_N correlates with a small complementary tail.
The primary readout tests that unproved coupling, not any identity already
predictable by reasoning. If suppression persists across scales, pursue a
cutoff-selection law coupling harmonic cancellation to the divisor tail. If
the tail persists despite tiny initial error, pursue the signed Mertens-increment
field exposed by the exact first-block identity. Mixed outcomes require retaining
both mechanisms. None of these outcomes settles an infinite-cutoff claim.

## Frozen design

For each integer k=10,...,16, inspect every N in [2^k,2^(k+1)). Select the N
minimizing abs(sqrt(N)*H_N), the N maximizing it, and the midpoint 3*2^(k-1).
Ties use the smallest N. No energy data are used to select cutoffs.

For these 21 slots compute exact integer divisor sums
C_N(n)=sum_(d<=N)mu(d)*floor(n/d), using a sieve of jumps and integer prefix
sums. Then F_N(n)=C_N(n)-n*H_N. Record actual carrier energy and target-error
energy on [1,N] and each dyadic block (2^j*N,2^(j+1)*N], j=0,...,6.
The last coordinate is 128*N. Use weights 1/(n*(n+1)). Record the initial
scalar predictor N*H_N^2 and all H_N sign crossings per bin.

Primary comparison: tail target-error energy on (N,128N] at the minimum-defect
cutoff divided by the same quantity at the midpoint. Ratios below 0.1 in all
seven bins count as consistent finite suppression; ratios above 0.5 in at least
four bins count as persistent complementary tail. Otherwise classify as mixed.
These diagnostic thresholds are chosen before data; they are not mathematical
constants or estimates. Also retain maximum-defect controls and every block,
so aggregate cancellation cannot conceal displaced tail mass.

## Limits and validation

The series after 128*N is NOT evaluated. The crude uniform source bound gives
an omitted raw-energy upper bound N^2/(128*N+1), and target-error upper bound
(N+1)^2/(128*N+1); retain these even when too large to discriminate. Finite
tail energy is a lower bound on the full nonnegative tail, not an estimate
silently promoted to the whole norm. Arithmetic integers are exact within the
chosen int64 ranges; H_N and energies use long-double arithmetic. Compare H_N
with compensated summation at selected cutoffs. Check discrete floor sums at
deterministic coordinates by direct summation, and check the exact first-block
Mertens identity throughout that block. These are implementation validation,
not formal numerical certificates.

## Execution budget and provenance

Run only on root@157.157.221.29:27094 using ~/.ssh/id_ed25519. Use up to eight
independent Python worker processes, each with NumPy internal threads capped at
one. Hard timeout: 240 seconds, with process-group cleanup on timeout; no
automatic scale increase or hours-long run. Download script, JSON results,
validation, environment metadata and logs to this directory. Record SHA-256
hashes and actual runtime. Do not use any numerical result in Lean.
