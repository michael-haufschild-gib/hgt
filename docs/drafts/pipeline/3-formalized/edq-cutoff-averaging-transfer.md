# EDQ logarithmic cutoff averaging: exact source and tail transfer

Stage: 3-formalized. Exact source and derived [BRIDGE]; numerical discriminator recorded separately. RH remains the primary objective.
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

## Closed source bridge

`EulerDeletionCutoffAverage.lean`, namespace `RHTower.DeletionCutoffAverage`,
proves the positive weights, unit total mass, exact suffix/taper identity,
finite summation reversal in any real module, modular and harmonic formulas,
and the full coordinate error identity. Its ordinary complex prefix is exactly
`H_(X,M)*S_s(K)-1` for `1<=K<=X`.

The taper is also realized in the original deletion paths with coefficients
`taper(X,M,p+1)*mu(p+1)/(p+1)`. Its complete current is the original mixed
quadratic current of this finite vector; all cross terms remain. The exact
path and endpoint identities connect averaging to that current.

Dilation separation gives a prefix-square floor `X/(64D)` uniformly over
**every** `M>X`, eventually in `X`. At a right-half zero it yields
`Re Q_(X,M)(rho)>=C_rho*X^(2 Re(rho)-1)`, again uniformly in `M>X`.
The constant and inner threshold depend only on the zero. Increasing the
outer support cannot erase this retained inner-prefix floor.

Consequently Lean proves the exact adaptive-cutoff criterion
`RH iff forall rho, forall e>0, exists B, forall K, exists X>=K, exists M>X,
abs(Re Q_(X,M)(rho))<=B*X^e`.
The selected outer cutoff may depend on the inner cutoff, exponent, and zero,
without any growth restriction. The upper comparison must use **X**, the
preserved source scale; a subpower estimate in an uncontrolled larger **M**
does not meet this theorem. Reflection is used only to exclude a left-half
zero through its right-half partner. No arithmetic upper ceiling is proved.

## Finite experimental result

The frozen decision is **mixed**. Width-four post-support ratios range from
0.152376 to 0.392510; width-two ratios range from 0.300004 to 0.700958.
All fourteen measured ratios are below one. Suppression is present beyond
support at these scales, but no monotone scale law or full-tail bound follows.
The omitted-tail bounds remain too large. The 9.867-second RunPod run passed
all validation with seven workers and no design changes. Script, frozen
protocol, full block results, logs, hashes, and limits are in the
[computation record](../2-fully-proven/computations/edq-cutoff-averaging-transfer-2026-09-07/REPORT.md).
No numerical output is imported into Lean.

## Validation

The complete scratch passed `lake env lean` without diagnostics. The leaf
contains seventeen public theorems, seven definitions, and four private
helpers. Final `lake build --old GaloisForLFunctions.RHTower.EulerDeletionCutoffAverage`
built only this leaf in 9.0 seconds; dependencies were cached. All twenty-four
new public declarations were audited once through a temporary `lake env lean`
file. Each depends exactly on `propext`, `Classical.choice`, and `Quot.sound`.
No added axiom, admission, or numerical certificate is used. The leaf is wired
once into `RHTower.lean`; no full or umbrella build was run.

Formal lint passed and the search index was refreshed once. Scoped source,
axiom coverage, whitespace, documentation links, and stage checks passed.
All owned Lean and RunPod processes exited. The verified numerical records
were downloaded and the owned remote directory removed. Temporary Lean
sources were removed; local check/build/audit logs remain under
`/tmp/edq_average.*.log`.

## Remaining mathematical producer

The [exact divisor source and cumulative covariance](edq-averaged-divisor-covariance.md) now connect this family to the corpus’s Barban–Vehov coefficient-square estimates while retaining the full error tail.

Derive a cofinal subpower bound for the complete averaged current in the
inner scale, or a separately proved full arithmetic-energy transfer and bound
that implies it. The fixed-width experiment does not establish such a bound.
The current criterion is a derived [BRIDGE], not a replacement conjecture for
RH and not a proof of RH.
