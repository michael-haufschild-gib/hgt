# Successor cells and the height-dependent phase boundary

- **ID:** EDQ-CELL-PHASE
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **RH chain:** literal arithmetic source -> independent phase constraint at every zero -> exclusion of off-line zeros. The final source constraint remains open.

## Frozen question R [BRIDGE]

For `sigma=Re(s)>0`, `t=Im(s)>0`, and an integer `n>=1`, let

`R_s(n)=sum_(j=1..n)j^(-s)-zeta(s)-n^(1-s)/(1-s)-n^(-s)/2`

and `g_s(n)=n^(-s)conjugate(R_s(n))/[conjugate(s)(conjugate(s)+1)]`.

**R:** If `t < 2*pi*n`, then `Im(g_s(n)) < 0`.

This conjecture concerns the literal source at all parameters, not only zeros. It would confine exceptional signs to a finite head proportional to height. It would not bound the unit value at high zeros, where the hypothesis fails, and is not an RH implication. The earlier fixed-parameter eventual sign theorem does not prove this uniform threshold.

## Corpus origin and proof attack

`EulerDeletionPowerSumRemainder.powerSumRemainder_eq_bernoulli` identifies `R_s(n)/[s(s+1)]` with the integral of `b(x)x^(-s-2)` from `n` to infinity, where `b(x)=(fract(x)^2-fract(x))/2` is nonpositive, periodic, and zero at integer endpoints. The exact successor difference is

`R_s(n+1)-R_s(n) = (n^(-s)+(n+1)^(-s))/2 - ((n+1)^(1-s)-n^(1-s))/(1-s)`.

The corpus's `EulerMaclaurinSawtooth` gives the local trapezoid identity. Searches also examined arithmetic additive carries, multiplicative power response, discrete summation by parts, and phase/sign variation. None supplies R or the missing RH sign as a theorem.

For `t=lambda*n`, writing `x=n+y` makes the normalized phase `exp(i*t*log(1+y/n))`. Its derivative starts at `lambda` and decreases. The first oscillation of the periodic cell has rate `2*pi`. This motivates R but is not a proof: absence of a stationary phase does not imply the sign of the integral. Merely propagating the recurrence with its decaying tail is also not an independent zero constraint.

Attack R on small and large cutoffs, near the proposed threshold, and over several real parts. Numerical evaluation must run on Runpod and remain separate from Lean. Freeze any replacement before testing it; do not adjust the threshold to rescue R silently.

## Separate proof-strategy conjecture S

**S:** The fixed-anchor imaginary integral can be proved nonpositive by showing all sufficiently late complete integer cells are nonpositive.

This is a claim about a proposed proof of R, not a reformulation of R. Attack it at the exact height `t=pi/log(2)`, with anchor one. On the cell `[2^k,2^k+1]`, the logarithmic phase lies between `k*pi` and `(k+1)*pi`. The periodic quadratic is strictly negative inside the cell. Thus the cell contribution should be strictly negative at even depths and strictly positive at odd depths, for every real part `sigma`. Infinitely many cells of both signs would refute S while leaving R unchanged.

**Frozen positive survivor S+:** establish that exact alternating dyadic-cell sign law for the literal Bernoulli integrand. This identifies the cancellation that a proof of R must retain. It does not prove the sign of the complete tail and is not a theorem about prime-sieve increments.

## Results and remaining problem

R survives the numerical attack: all 567 tested triples satisfying its strict bound have negative phase. The complete scan has 1,008 points; 118 of the points outside the strict bound have positive phase. An initial set of five apparent counterexamples was invalidated by insufficient precision for extremely small tails. A corrected scan and independent ordinary-prefix verification are documented in the [Runpod report](../2-fully-proven/computations/arithmetic-successor-phase-threshold/REPORT.md). No computed value is a Lean premise, and R remains unproved.

S is refuted symbolically. S+ and the exact source connection are proved in the scratch/source-checked module `ArithmeticSuccessorCellPhase`. If

`J(sigma,t;m)=integral_(m..m+1) b(x)x^(-sigma-2)sin(t log x) dx`,

then `(-1)^k J(sigma,pi/log(2);2^k)<0` for every real `sigma` and natural `k`. Consequently both signs occur arbitrarily far out. The proof keeps the positive power weight and uses the exact phase interval `(k*pi,(k+1)*pi)` inside each selected cell. It is an elementary logarithmic-phase law; no novelty claim is made.

The formal source connection proves that the complex cell is

`[conjugate(R_s(m))-conjugate(R_s(m+1))]/[conjugate(s)(conjugate(s)+1)]`.

Every finite cell sum retains the terminal remainder. Their ordinary infinite-cutoff limit recovers `conjugate(R_s(m))/[conjugate(s)(conjugate(s)+1)]`. Thus the alternating contributions are part of the literal source, not a perturbed model. The fixed height in this counterexample is not asserted to be a zero. It refutes an all-parameter cellwise proof strategy, not every zero-specific argument.

The next unresolved proof obligation for R is an estimate retaining cancellation across cells uniformly in `t/n`. Even that result would leave the RH producer open: the finite exceptional head must obey an independent constraint forcing the required unit-boundary sign at every zero. No new constraint of that strength was established in this investigation. The S/S+ source module passed its serialized leaf build, all twelve public axiom checks, and `lint --check-generated`; no full or umbrella build ran. See the [S closure](../5-failed/arithmetic-cellwise-phase-sign.md) and [formal certificate](../3-formalized/arithmetic-successor-cell-phase.md).

## Literature boundary

The ordinary recurrence and Bernoulli representation are classical, explicitly recorded in [DLMF 25.11.3–6](https://dlmf.nist.gov/25.11#iii). [Nemes's 2017 paper](https://arxiv.org/html/1702.05316v2) treats sharp complex-parameter remainder bounds; its stated sign theorem is for real parameters and does not prove R as stated. This bounded check establishes neither novelty of R nor a radical new RH architecture. No Gamma/terminant representation from that paper is used in the proof here.

## Limits of this investigation

The required RH producer remains a source-derived constraint at the unit term. A proven cutoff theorem would be a quantitative bridge controlling the exceptional head, not its cancellation. No claim of literature novelty or independence from every classical technique is made. No spectral, completed-function, or excluded route is used here.
