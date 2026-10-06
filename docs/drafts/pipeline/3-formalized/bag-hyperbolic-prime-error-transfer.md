# BAG: actual hyperbolic prime-window error transfer

2026-10-06,18az. CLOSED in Lean as an analytic step of the signed phase-cell proof.
The full discrete phase-cell packet and the full cubic remain open in Lean.

For every natural M, set δ=N^(1/5-1) and
Pδ(x)=[ψ(x+δx)-ψ(x)]/(δx). Let K(N,M,x) be the ordered hyperbolic kernel
summed over the actual primes p,r in (N,2N], with p≠r,
|p-r|<|x-r| and |p-r||x-r|≤Mr. It retains the original V/W profiles,
physical factor 2π/r, recentered phase e((p-r)(x-r)/r), and density 1/log x.

The complex integrand (Pδ-1)K is eventually integrable on [N,2N], and

    (log² N/N) ‖∫_[N,2N] (Pδ(x)-1) K(N,M,x) dx‖ → 0.

No analytic premise or discarded exceptional set occurs in this theorem.
The kernel is independently proved integrable, and its value at every
prime q in the original band is exactly the corresponding ordered sum of
original cubic entries divided by log q. The ordering constraint retains
q≠r. This is one ordered sector; p=q belongs to the ties, treated separately
in the full packet proof.

## Proof

Group integer pairs by d=|p-r|, retaining both signs. For each d≥1 the
hyperbolic constraint confines r to an interval of length 2Y/d around the
real interpolation point. Each sign determines p. The interval-cardinality
bound and harmonic sum give, uniformly in real x≥0,

    #{p,r≤B: p≠r, |p-r||x-r|≤Y} ≤ 4Y(1+log B)+2B.

This bound holds even without the ordering restriction. For the actual
kernel take B=floor(2N), Y=2MN. The literal amplitude is at most
2π/(N log N), hence ‖K(N,M,x)‖≤64π(M+1) for N≥4, log N≥1 and x∈[N,2N].
Measurable sharp supports and continuous amplitudes prove integrability.

The exact norm of Pδ-1 is the previously proved prime-window relative
error. Its complete L1 integral beats every logarithmic power. Multiplying
that error by this actual uniformly bounded kernel proves both eventual
integrability and the displayed limit. This is Lebesgue averaging; it
makes no assertion about sampling the exceptional set at primes.

## Lean and validation

`formal/GaloisForLFunctions/RHTower/ChiCubicHyperbolicPrimeKernel.lean`,
391 lines, nine public declarations. Main theorem:
`RHTower.chiCubicHyperbolicPrimeDensityError_tendsto` at349.
Exact prime-point identity at206; kernel bound at230.

Final foreground leaf37885, `lake --old env lean` with explicit olean:
`/tmp/bag-hyperbolic-prime-kernel-final-18az.log`, exit0, empty output.
One umbrella import. Index55264 exited0 and all nine API rows were checked.
Imported axiom/API audit77831 exited0:
`/tmp/bag-hyperbolic-prime-kernel-axioms-final-18az.log`. All nine public
declarations use only propext, Classical.choice and Quot.sound. The same
scratch audit verified the new mathlib names in this toolchain.
No new axioms, admissions, heartbeat increases, full or umbrella builds.

Authoritative lint87587 exited1 with unrelated reachability errors for
RHTower.KuznetsovKloostermanSmallModulus, RHTower.KuznetsovQuadraticPhase,
RHTower.KuznetsovSqrtPhasePoisson, RHTower.WeilFiniteTypeContinuation,
RHTower.WeilFiniteTypeResidues and HTGeometry.HilbertSchmidtTraceIdeal.
No finding names this leaf; global lint is not clean.
Log: `/tmp/bag-hyperbolic-prime-kernel-lint-18az.log`.

## Remaining signed proof

Exact dual averaging must still connect this integral to the discrete
von Mangoldt sum, paying sharp boundary displacements and then proper
prime powers. The averaged prime-pair specialization and completed-period
cancellation must also be formalized. The detailed paper proof remains in
`../2-fully-proven/bag-hyperbolic-phase-cell-cancellation.md`.
The complement outside every fixed M, growing moments/cofactors,
common-height return and RH remain open.
