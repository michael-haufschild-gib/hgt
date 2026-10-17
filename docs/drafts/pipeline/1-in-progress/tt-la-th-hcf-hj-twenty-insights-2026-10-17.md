# Twenty cross-route insights: TT / LA / TH / HCF / HJ

## Contract

User task: attachment `277aa2d6-28d3-4b7c-aca7-800d9e29a1ca/pasted-text-1.txt`.
Find 20 significant insights combining frontier theorems from multiple routes,
each advancing TT, LA, TH, HCF, or HJ directly or indirectly. A new wrapper,
restatement of an RH equivalence, or routine lemma does not earn insight credit.

Use current local Lean sources and corpus search. No external search, numerical
experiments, or external novelty audit. Frontier map is read-only. Prove exact
claims on paper before Lean. No unproved premises, added axioms, heartbeat
increases, full builds, or umbrella builds. Check individual modules in the
foreground, reuse unchanged dependencies with `--old`, wire finished modules,
audit axioms from `/tmp`, run formal lint, and remove owned temporary artifacts.

## Plan

1. Inspect current route interfaces and search the entire indexed Lean corpus.
2. Form falsifiable cross-route conjectures; reject circular and routine claims.
3. Complete dependency-closed proofs, including positive survivors of no-go results.
4. Formalize and audit each significant result; update exact count and evidence.
5. Repeat until all 20 contributions meet the contract.

`update_plan` is unavailable in this tool session; this file tracks the plan.
Serena symbol access rejects the ignored Lean tree; use exact source reads and
patches after that observed failure. `docs/architecture.md` and `docs/testing.md`
were absent from the initial file inventory.

## Current investigation

Question: can the literal Hurwitz reflection residual quantify negative heat
moment directions, rather than merely share their RH-equivalent zero locus?

Inputs inspected:

- `PrimeTailSeedHurwitzReflection.lean`: literal co-Poisson residual and first-prime
  seam have the same open-strip zero locus.
- `XiGaussianHeatRouteCapstone.lean`: exact heat/Hankel receivers at one positive
  time; source orientation remains unproved.
- `XiGaussianHeatRegularKernelProjections.lean`: mutually orthogonal signed
  reproducing block kernels, including singular gaps.

## Conjecture 1: two prime-log heat grids survive arbitrary finite prefixes

For any integers K,L >= 0, put
`s_(h,K)(n) = nu((2K+1+n)h)`, where `nu` is the literal Xi heat trace.
Conjecture: RH iff both complete Hankel forms of `s_(log 2,K)` and
`s_(log 3,L)` are positive semidefinite.

Attack: the direct Hurwitz/heat seam equivalence is already present in
`HeatAperturePrimeSeamReflection.lean`; reject it as a contribution.
A single exponential sampling grid aliases spectral frequencies modulo
`2 pi i / h`; no claim that one grid determines reality. Two prime-log grids
eliminate this exact obstruction. Existing corpus searches did not return this
two-grid heat receiver. No external novelty claim is made.

### Dependency-closed paper proof

Write `w_q = z_q^2` for the actual squared Xi spectral points and
`lambda_q(h) = exp(-h w_q)`. For h>0 these are nonzero, absolutely summable,
and tend to zero off finite sets (`summable_xiGaussianHeatTerm`). Finite
polynomial expansion and absolute convergence identify the Hankel functional
on p^2 with
`Re sum_q lambda_q(h)^(2K+1) p(lambda_q(h))^2`.
This is exactly the trace-Hankel form on the principal ideal `X^K`, since
`lambda^(2K+1) p(lambda)^2 = lambda (lambda^K p(lambda))^2`.

The corpus theorem
`traceHankel_nonnegative_on_principalIdeal_implies_real` applies: `X^K` cannot
vanish at any exponential node. Thus positivity on the h-grid forces every
`exp(-h w_q)` to be real. Equality with its complex conjugate implies
`exp(-2 i h Im(w_q)) = 1`. Applying this at h=log 2 and h=log 3,
`primeLogPhaseClockPair_two_three_injective` forces `Im(w_q)=0`.
The established height gap (`xiSpectralSq_im_ne_zero_of_im_ne_zero`) then
forces every z_q real, hence RH. Conversely, under RH all lambda_q(h) are
strictly positive real, so every term in each polynomial-square form is
nonnegative. This proves the exact equivalence without any sign premise left
unproved in the theorem.

Sources combined: HCF actual heat trace and spectral shell laws; TH/LA
trace-Hankel principal-ideal separation; prime-log phase injectivity. HJ will
receive the exact sampled criterion through its literal reflection residual,
without counting that corollary as a separate insight.

Formalization pending. Principal-ideal separation imports a general theorem
with hypotheses; all its hypotheses above are proved for the actual Xi source.

### Arithmetic source strengthening (same contribution)

Let `A(t) = Re(gaussianArchCriticalC(t)-gaussianPrimeChirpC(t))/pi`.
The existing exact source formula gives `A(t)=nu(t)-2 exp(t/4)`.
At grid h with offset 2K+1, set alpha=exp(h/4). For every real polynomial p,
the sampled source functional is the heat functional minus
`2 alpha^(2K+1) p(alpha)`. Therefore their square forms agree on p(alpha)=0.
Applying principal-ideal separation to `X^K (X-alpha)` still excludes every
nonreal exponential node: this generator has only real roots. The two-grid
proof consequently works with source positivity restricted to the two pole
hyperplanes. This gives a derivative-free arithmetic-source criterion and
the exact literal HJ reflection-residual criterion. These are parts of the
same contribution, not extra count.

## Verified contribution count

0 / 20. No mathematical result claimed yet.

## Workspace preservation

Initial unrelated changes: `docs/prompts.md`,
`HTGeometry/SymbolicTransferOperator.lean`,
`RHTower/PrimeArchSignedCompactCompletionCollapse.lean`, and untracked
`RHTower/OddSectorGroundDivisionOperator.lean`. Preserve them.
