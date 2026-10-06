# BAG: exact dual averaging and actual prime-power removal

2026-10-06,19az. CLOSED in Lean as two steps of the fixed-radius signed
hyperbolic phase-cell proof. Sharp displacement and full packet cancellation
are still open in Lean.

Let K(N,M,x) be the actual ordered hyperbolic prime kernel from
`ChiCubicHyperbolicPrimeKernel.lean`, and δ=N^(1/5-1). Define its finite
von Mangoldt dual average by

    A(N,M) = Σ_{1≤n≤floor(3N)} Λ(n)
      ∫_[n/(1+δ),n)∩[N,2N] K(N,M,x)/(δx) dx.

For N>1 and δ≤1/2, this equals the integral of the actual density
[ψ(x+δx)-ψ(x)]/(δx) against K on [N,2N]. That integrand and every term
used in finite integral exchange are proved integrable. The half-open
dual window is derived from the actual ψ endpoint convention.

For every natural M, Lean proves unconditionally

    (log²N/N) ‖A(N,M) - ∫_[N,2N] K(N,M,x) dx‖ → 0.

It also proves, for every natural M,

    (log²N/N) ‖Σ_{N<n≤2N} Λ(n)K(N,M,n) - Q(N,M)‖ → 0,

where Q is defined directly as the original triple sum over true band
primes q,p,r with p≠r, |p-r|<|q-r| and |p-r||q-r|≤Mr. Each surviving
term is the original `primeGaussianCubicMainEntry`, including all V/W,
physical reciprocal and phase factors. The ordering also excludes q=r.
The transpose and ties remain separate parts of the full packet.

## Proof

Expand the ψ increment as its finite von Mangoldt sum. For x∈[N,2N],
δ≤1/2 ensures every included integer is at most3N. The exact floor
inequalities identify n/(1+δ)≤x<n. The literal kernel divided by δx is
integrable on the positive compact band, by kernel integrability and
continuity of the reciprocal factor. Indicators and constant weights
preserve admission. Finite summation commutes with integration, with no
endpoint approximation. Subtract the kernel integral and invoke the
already proved complete signed density-error estimate.

To remove proper prime powers, split the actual von Mangoldt sum into
prime and nonprime terms. The exact prime-point kernel identity and
Λ(q)=log q recover Q with its original entries. The entire remaining
norm is bounded by 64π(M+1)[ψ(2N)-θ(2N)], hence by
64π(M+1)*8sqrt(N)log N for large N. The normalized error is bounded by
a constant times log³N/sqrt(N), which tends to zero. No prime-power or
exceptional-set estimate is assumed.

## Lean and validation

`formal/GaloisForLFunctions/RHTower/ChiCubicHyperbolicPrimeAveraging.lean`,
258 lines, six public declarations:

- `chiCubicHyperbolicVonMangoldtAverage` at46.
- `chiCubicHyperbolicVonMangoldtAverage_eq` at67.
- `chiCubicHyperbolicVonMangoldtAverage_tendsto` at116.
- `chiCubicHyperbolicPrimePacket` at141.
- `chiCubicHyperbolicVonMangoldtSum` at148.
- `chiCubicHyperbolicPrimePowerError_tendsto` at232.

Final foreground leaf52251: `lake --old env lean` with explicit olean,
`/tmp/bag-hyperbolic-prime-averaging-03az.log`, exit0, empty output.
The new leaf is wired once into RHTower. Imported axiom/API audit1310
exited0: `/tmp/bag-hyperbolic-prime-averaging-axioms-19az.log`. All six
declarations use only propext, Classical.choice and Quot.sound. Index61969
exited0, and all six public API rows were checked. No new axioms,
admissions, raised heartbeats, full or umbrella builds.

Authoritative lint78230 exited1 with367 existing large-file warnings
and eleven unrelated unreachable modules: RHTower.CCMRestrictedWeilGroundParityCrossing,
KuznetsovGaussianTails, KuznetsovKloostermanSmallModulus, KuznetsovQuadraticPhase,
KuznetsovSqrtPhasePoisson, WeilFiniteTypeContinuation, WeilFiniteTypeResidues,
ZetaMollifiedShortWindowMeanSquare; HTGeometry.FiniteRankDeterminant,
HilbertSchmidtCalculus and HilbertSchmidtTraceIdeal. No finding names this
leaf. Global lint is not clean. Log:
`/tmp/bag-hyperbolic-prime-averaging-lint-19az.log`.

## Remaining problem

These results leave a specific difference: A(N,M) must approximate
κδ ΣΛ(n)K(N,M,n), where κδ=log(1+δ)/δ. The sharp-boundary displacement
estimate is not implied by the exact identity. The current proof uses
the actual kernel's total variation O_M(sqrt(N)/log N), including all
endpoint jumps, and a finite telescoping overlap estimate. Its detailed
paper argument is recorded in the active phase-cell card; Lean proof
remains. Completed-period cancellation and the averaged prime-pair
specialization also remain. Full cubic, growing moments/cofactors,
common-height return and RH are not closed.
