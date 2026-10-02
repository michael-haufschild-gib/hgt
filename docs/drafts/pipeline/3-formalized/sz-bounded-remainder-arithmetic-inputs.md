# SZ bounded-remainder arithmetic inputs

- ID: sz-bounded-remainder-arithmetic-inputs
- Stage: 3-formalized
- Route: SZ
- Scope: prescribed shift lower bound and uniform full-Mangoldt cancellation inputs
- RH status: unresolved; no odd-response or signed-Wronskian theorem asserted

## New statements

For the actual physical bounded remainder B_a and prescribed interval
shift c_a, norm(B_a)>=sinh(a)+a and exp(a)<=2*c_a, for every positive
aperture. The proof uses the even pole vector and the audited bound on
B_a minus its polar operator, followed by the actual unitary transport.
It introduces no prime asymptotic premise.

For every epsilon>0, eventually in ambient X, the complete twisted
Mangoldt prefix has norm at most epsilon*N, uniformly throughout the
corpus growing cutoff and frequency window:

- exp((log X)^(19/20))<=N;
- log N<=twoRangeLx 2 X;
- twoRangeT0 2 100 X<=abs(tau)<=2*pi*X.

Every integer M<=N in that same cutoff window gives the actual weighted
tail estimate
  norm(sum_{M<n<=N} n^(-1/2)*Lambda(n)*n^(-i*tau))
    <=4*epsilon*sqrt(N+1).
The complete weighted prefix is at most
  21*sqrt(M)+4*epsilon*sqrt(N+1).
The head is retained through the unconditional positive prime-mass bound.
Every prime power remains included; no derivative of the oscillatory
phase and no frequency-dependent transfer loss is introduced.

## Paper proof of the weighted transfer

Apply discrete Abel summation with w(n)=1/sqrt(n). Bound every prefix by
epsilon*(n+1). Both endpoint norms and the nonnegative weight variation
are retained. Apply the same Abel identity to the constant sequence 1;
the majorant becomes epsilon*(sum_{M<n<=N}w(n)+2*sqrt(M+1)). The corpus
square-root harmonic-sum bound closes it. Splitting the original prefix
at M and bounding the head by its literal positive mass proves the full
prefix estimate.

## Lean evidence

- CCMRestrictedWeilPolarShiftLower: three public theorems; direct leaf audit passed.
- Sieve/VonMangoldtTwistPolynomialWindow: one public theorem; direct leaf audit passed.
- Sieve/VonMangoldtTwistHalfDensityWindow: two public theorems; direct leaf audit passed.

Each final leaf command was `lake --old env lean <leaf> -o <leaf.olean>`
from formal/, with one foreground build at a time. All three leaves are
wired into GaloisForLFunctions/RHTower.lean; no umbrella build was run.
All six public axiom queries passed with propext, Classical.choice,
and Quot.sound only; no new axiom or RH premise occurs.

Repository lint ran and failed on eleven unrelated unreachable modules:
CCMApertureChainProfile, CCMApertureTranslationChains,
CCMExponentialRampPrimeMoment, CCMExponentialRampSourceDissipation,
CCMExponentialRampTerminalEntropy, CCMRetainedChainKernelLower,
MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines,
SoninAnnularDilationNilpotent, ThetaMovingShellFirstOrderPhase,
ZetaZeroDensityPowerSaving. None of these three new leaves was reported.
The global lint gate is not green.

## Remaining mathematical obligations

The low-frequency PNT/Stieltjes transfer is now formalized separately in
`sz-prime-polar-polynomial-frequency.md`; its union with this growing
window remains open. So are the finite truncated-exponential iterate
closure, Fourier tails, many-moment residual, and actual odd-source weld.
Even the proposed uniform odd energy bound would leave signed aperture
Wronskian control, normalization and shift removal open. The candidate
and exact next source estimates remain in
`../1-in-progress/sz-bounded-remainder-source-iteration.md`.
