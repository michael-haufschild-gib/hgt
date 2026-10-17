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

All four modules passed their narrow `:olean` builds and final individual
`lake env lean` audits without warnings in these modules. All 37 public
declarations were audited with `#print axioms` in a temporary file: only
`propext`, `Classical.choice`, and `Quot.sound` occur. All four imports are
wired into `RHTower.lean`; index refresh and `git diff --check` passed.
Repository lint exited 1 on 31 unrelated modules missing umbrella imports
(OddSector, Bernstein, and HTGeometry work from concurrent agents). No lint
error concerns these four modules. This is a repository gate limitation,
not a claim that repository lint passed.
Principal-ideal separation imports a general theorem
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

### Exact one-grid obstruction (same contribution)

For any h>0 choose b=2pi/h, a=1+b^2, and w=a+ib. Then w is nonreal,
`(Im w)^2 < Re w`, and the conjugate-pair heat trace
`T(t)=exp(-tw)+exp(-t conjugate(w))` has
`T(nh)=2 exp(-nha)` for every natural n, including all discarded-prefix
Hankel moments. Thus every sampled Hankel form is nonnegative, exactly as
for a positive real one-atom source. Yet `T(h/2)=-2 exp(-ha/2)<0`.
This kills a universal one-grid replacement even inside the natural parabolic
spectral region. It is an abstract spectral countermodel, not a claim about
actual Xi zeros. The two-grid theorem is its positive survivor.

### Finite-offset conjecture and obstruction (same contribution)

Conjecture: finitely many independently chosen offsets of one grid might
replace two incommensurate grid steps. Verdict: FALSE for the abstract
parabolic spectral class.

For offsets tau_i and grid h, simultaneous integer approximation supplies
arbitrarily large integers n for which each `2 pi n tau_i/h` lies within 1
of an integral multiple of 2pi. Hence all cosines are at least 1/2. Take
the preceding countermodel with smaller step delta=h/n. On every entire
offset grid its trace is exactly
`2 exp(-a tau_i) cos(2 pi n tau_i/h) (exp(-a h))^m`.
Each coefficient is strictly positive, so each complete Hankel form is
positive semidefinite. The same trace remains strictly negative at delta/2.
This preserves arbitrarily high alias frequencies and all ranks at every
finite collection of offsets. The positive survivor remains the exact
two-incommensurate-grid source theorem, rather than more offsets.

Imported recurrence: `exists_fin_simultaneous_integer_approximation_of_lt`
and `one_sub_sq_phaseError_div_two_le_re_exp_I_mul_real` in
`CCMPrimePoleFiniteCoherence.lean`. Full-corpus recurrence search returned
complete retrieval; both candidates were verified in this toolchain and the
finite-offset theorem passed its final Lean audit.

## Verified contribution count

1 / 20. One contribution: the exact two-prime sampled heat/source criterion
with sharp single-grid and finite-offset obstruction. Its 37 declarations,
source and HJ corollaries, and boundary theorems are not counted separately.
The remaining all-rank arithmetic positivity is open; RH is not proved.

## Next live conjecture

Does equality of all heat-trace values on two prime-log grids reconstruct a
spectral packet? Individual phase pairs are injective, but the two trace
sequences supply unpaired marginals. A rectangle switch between imaginary
frequencies `{0,L1+L2}` and `{L1,L2}`, with `Li=2*pi/hi`, appears to preserve
both grid traces. Audit conjugate closure and the Xi parabola, then extract
the strongest positive recovery theorem from mixed samples. This is not yet
a proved or counted contribution.

### Paper proof: marginal ambiguity and finite mixed recovery

For arbitrary positive steps h,k put a=2*pi/h, b=2*pi/k and
A=1+(a+b)^2. Compare the conjugation-closed packets, including multiplicity,
`{A,A,A+i(a+b),A-i(a+b)}` and `{A+ia,A-ia,A+ib,A-ib}`.
Their heat traces are respectively
`F(t)=2 exp(-At)(1+cos((a+b)t))` and
`G(t)=2 exp(-At)(cos(at)+cos(bt))`.
Every frequency satisfies Im(w)^2<Re(w), since a,b>0. On t=nh,
at=2*pi*n, so cosine addition gives F(t)=G(t); on t=nk the same
argument uses bt=2*pi*n. At t*=2*pi/(a+b)>0, however,
F(t*)=4 exp(-At*) while G(t*)=4 exp(-At*)cos(a*t*).
Since 0<a*t*<2*pi, cosine is strictly below one. The packets therefore
have distinct full traces despite agreement on both entire marginal grids.
This works for h=log2,k=log3 and is not a counterexample about actual Xi.

The positive survivor is exact finite spectral recovery from mixed samples
at `t0+m log(p)+n log(q)`, for distinct primes p,q. The paired map
`z -> (exp(-log(p)z),exp(-log(q)z))` is injective: equality first fixes
Re(z) by taking norms; subtracting points gives exponentials equal to one,
and two-prime phase injectivity fixes the imaginary part. For a finite
set S of distinct complex frequencies and coefficient differences c_z,
vanishing mixed samples say
`sum_S c_z exp(-t0*z) x_z^m y_z^n=0` for all m,n>=0.
Linearity extends this to every bivariate complex polynomial. The existing
finite multivariate CRT, with point-ideal powers one, supplies a polynomial
taking value one at any selected paired point and zero at all others.
Testing it gives `c_z exp(-t0*z)=0`; exponential nonvanishing gives c_z=0.
Thus the mixed sampling map is injective for arbitrary complex weights on
every finite support and every real initial offset. Comparing two packets
uses their union support, so their spectra and multiplicities agree.

This proof uses no positivity assumption or unknown source premise.
It combines the prime phase theorem, finite Hermite CRT, and heat packet
encoding. Corpus retrieval was complete but compiler coverage partial;
each imported candidate will be checked by Lean. An infinite packet
extension requires a separate localization argument.

### Stronger survivor: countable mixed-moment determinacy

For sequences x_j,y_j tending to zero, assume the paired points are distinct
and no pair is (0,0). Exclude the countably many complex slopes
`-x_j/y_j` and `(x_l-x_j)/(y_j-y_l)`. Any remaining slope r makes
`z_j=x_j+r*y_j` nonzero and injective; cases with zero denominator are
settled directly by the paired assumptions. The z_j still tend to zero.
For absolutely summable complex weights c_j, all mixed moments converge
because x and y are bounded. If they vanish, binomial expansion and finite
sum interchange show every positive power moment of z vanishes. Apply
`coeff_eq_zero_of_atomicMoments_vanish` from `AtomicMomentDeterminacy.lean`:
all c_j vanish. This upgrades finite recovery to countable recovery without
requiring either marginal coordinate to be injective. The nonconstructive
slope is used only in the proof; the observed data remain the original
nonnegative mixed powers.

For distinct frequencies w_j with Re(w_j) tending to infinity, positive
prime-log heat coordinates tend to zero and are jointly injective. Thus
the theorem applies to every summable coefficient sequence, and to any
heat-regularized packet whose regularized coefficients are summable.
No RH, spectral reality, or sign assumption is needed. This is the positive
survivor to formalize, stronger than the finite CRT version above.

## Workspace preservation

Initial unrelated changes: `docs/prompts.md`,
`HTGeometry/SymbolicTransferOperator.lean`,
`RHTower/PrimeArchSignedCompactCompletionCollapse.lean`, and untracked
`RHTower/OddSectorGroundDivisionOperator.lean`. Preserve them.
