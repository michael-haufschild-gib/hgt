# EDQ logarithmic cutoff averaging: exact source and tail transfer

Stage: 1-in-progress. Experimental discriminator plus a derived [BRIDGE]; RH remains the primary objective.
Full chain: Euler deletion → exact complex zero balance → signed arithmetic separation → off-line exclusion → RH.
Objective: determine whether cutoff averaging offers a useful arithmetic upper-bound source after retaining the complete compensation.

## Corpus basis

EulerDeletionDilationPowerGrowth reduces the sufficient upper target to cofinal
subpower growth. CountertermRigidity fixes the global scalar compensation.
The inspected MenonMobiusLargeValues theorem controls ordinary short windows;
BarbanVehovSharpSummatory controls logarithmically weighted divisor sums with
an explicit floor-removal error. Neither supplies the actual weighted primitive
bound. The existing raw-Möbius critical-tail obstruction excludes convergence
of the unsmoothed raw error, but does not decide a cutoff average.

## Exact source [BRIDGE]

For integers 1<=X<M define a probability on cutoffs X<=j<M by
alpha_j=log((j+1)/j)/log(M/X). Average the actual raw vectors F_j with these
weights. Reversing finite sums gives generator coefficient
mu(d)*log(M/max(X,d))/log(M/X) for d<=M, zero beyond M.
Thus all coefficients d<=X remain exactly mu(d), with a logarithmic taper
above X; the coefficient at M is zero. Its harmonic compensator is the same
weighted average of the literal H_j. No scalar is chosen independently.
Its full target-error vector is the weighted average of the full original
target-error vectors. This exact construction can be formalized without any
numerical evidence. Existing initial-prefix dilation separation still applies
to its shared scalar on source coordinates through X.

## Frozen finite experiment question

Does a fixed-width logarithmic cutoff average suppress the post-support error
energy compared with the raw vector at its largest cutoff, consistently across
scales? Or does apparent initial improvement leave a comparable later tail?
This magnitude and distribution comparison is not implied by Jensen's
inequality: the control is a single endpoint, not average input energy.
No asymptotic law or RH conclusion will be inferred from finite data.

Design: X=2^k for k=10,...,16; M=2X and 4X; common coordinate ceiling T=256X.
Compute raw F_X,F_(2X),F_(4X) and the two exact logarithmic averages. Record
target-error energy and raw squared norm with weights 1/(n(n+1)), the head
through X, and all eight dyadic coordinate blocks (X,256X]. Primary ratios
compare averaged and endpoint-raw target-error energy on (M,T].
All fourteen ratios <=1/4 means strong post-support suppression. At least four
of the seven width-four ratios >=3/4 means persistent post-support error.
Otherwise classify mixed. Thresholds and parameters remain fixed after data.

Validate integer Möbius sieve against direct factorization on fixed checks,
logarithmic coefficients against suffix sums of alpha_j, raw head floor
identities, and direct coordinate sums. Use long-double weighted arithmetic,
integer raw floor sums, and repeat fixed coordinate checks independently.
Record omitted-tail upper bounds (1+sum(abs(coeff)))^2/(T+1), and raw-norm
tail bounds sum(abs(coeff))^2/(T+1). These may be too large to certify full
energy; report that limitation explicitly.

Numerics run only on the authorized RunPod, parallel across seven independent
scale jobs, with BLAS threads fixed at one and a 240-second hard deadline.
Download scripts, frozen design, results, logs, and hashes into the computations
directory. No result enters a Lean proof.

## Status

Protocol frozen; execution and exact finite-source formalization pending.
