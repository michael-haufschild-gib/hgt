# One-step successor-envelope average

Frozen question: at every proper actual state admitted by
`Psi(P)=max(Q_P,all immediate successor energies)<=B=Q_empty`, is the
uniform mean of `Psi(P+p)` over available primes at most B?
See the [frozen card](../../../5-failed/ccm-fu-successor-average-reserve.md).
This differs from existence of a good successor and from independent
half-subset averaging. No larger repeat screen was run.

The [script](screen.py) reads all8860 stored states through cutoff32,
cross-checks every energy against the original CSV, and tests all8176
admitted proper states using the unchanged tolerance `1e-12*max(1,B)`.
It flags262 failures. Every flagged state and every required first/second
successor is independently reconstructed from the defining divisor defects
and Abel sums at80 digits; all262 failures remain. Shared field caches
and all failure alternatives are retained in [summary.json](summary.json).
None of the failures lies on the stored deterministic least-energy path.

The first failure is M=22, P={3,7,11,17,19}, with remaining primes2,5,13.
Here B is about0.55122126, current energy0.34836295, and current envelope
0.54355971. The successor envelopes are about0.22188513 for prime2 and
0.74662494 for each of primes5,13. Their mean is0.57171167, exceeding
B by0.02049041. Prime-specific selection remains possible.

The actual signed field at this state has only five nonzero labels:
empty about-0.47956509, {2} about0.18226872, {5} about-0.12646568,
{2,5} about0.20272187, and {13} about-0.16753706. Thus the first failure
exposes a prime separating two persistent sign classes. The card now
contains a separate analytic Lean certificate: the mean exceeds B+1/75,
while prime 2 contracts after every subset of the other mergers and
preserves admission. Its proof uses no experimental values as premises. The numerical failure does not refute exact extension,
least-energy selection, PE4, SD1, or RH. These data supply no Lean premise.

Execution used the supplied RunPod host, eight worker processes,
one-thread numerical libraries, and a60-second foreground deadline.
Successful elapsed runtime was0.10254687815904617seconds. The first attempt
stopped on Python3.8 lacking `int.bit_count`; replacing that operation by
`bin(support).count('1')` changed no mathematical test or tolerance.
The second run exited successfully. All owned remote files were removed
after checking that no worker remained in the temporary directory.

Local and remote SHA-256 hashes match:

| File | SHA-256 |
|---|---|
| screen.py | 33075b82bc6505aeb53dcfc88ec04b3a8f4fb0253f6814b41bb7f1d7008e56fe |
| summary.json | d94564a44bc7487ea48341a6915f575721a95f3a2daf21c995415ce41b40b38e |
| defect-reserve-reanalysis.json | c6542367707c793fcf00675252e0b67e7bf7786a7a87769971dd4c2bcc944ff5 |
| subset-states.csv | ba22442cb19cf20b5df1e9cc07d57c67d4105963a2a7cb75b5ab96c53e225fd9 |

The two input files remain in
`../ccm-fu-adaptive-prime-energy-2026-09-06/`; they were neither changed
nor regenerated for the main screen.
