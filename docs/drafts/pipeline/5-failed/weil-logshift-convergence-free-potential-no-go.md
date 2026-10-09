# Convergence-free totalized potential criterion: diagonal divergence obstruction

Status: [FAILED AS STATED; COUNTEREXAMPLE AND POSITIVE SURVIVORS LEAN VERIFIED]
Date: 2026-10-09
Source policy: our Lean corpus only; no web or external papers.

## Target and plan

Test the proposed removal of every convergence condition from the current
potential criterion: summable excess plus `psi(0)<=psi(log m)` for every
integer m>=2 would imply asymptotic log-shift positivity.

1. Formalize a general diagonal weight construction for countably many
   strictly positive kernels and an arbitrary nonnegative target envelope.
2. Apply it to the paired Riemann kernel to build a zero-excess minorant whose
   sampled signed series all diverge, with partial sums tending to minus infinity.
3. Show the totalized potentials are all zero while asymptotic positivity fails.
4. Audit the strongest positive survivor, the already-proved sparse-convergence
   criterion and covering-probe regularization; wire/index, lint, clean scratch.

## Dependency-closed paper counterexample

For any strictly positive matrix P(m,n) and nonnegative envelope r(n), set

`v(n)=0` for n<2, and `v(n)=r(n) sum_{j=0}^n 1/P(j,n)` for n>=2.

Then v>=0 and, whenever n>=max(2,m), `v(n) P(m,n)>=r(n)`, by retaining
the j=m summand. This is the general positive construction to extract.

Take r(n)=1 and
`P(m,n)=K(log m+log n)+K(log m-log n)`.
Strict positivity of K is already in the corpus, so P>0 even at m=0 or n=0.
Set `lam(n)=vonMangoldt(n)-sqrt(n) v(n)`. The guard v(n)=0 below 2 gives
normalized deviation a(n)=-v(n) everywhere. Thus lam is a minorant and excess
is identically zero. Since v(2)P(0,2)>=1, v(2)>0 and lam(2)<vonMangoldt(2).

For each fixed m, the nonnegative sequence v(n)P(m,n) is eventually at least
one. It is not summable, and its partial sums tend to plus infinity. The signed
potential terms are its negatives, so their series is not summable and its
partial sums tend to minus infinity.

Lean's totalized real tsum is zero on a nonsummable family. Therefore every
`psi(log m)=0`, including psi(0) via log 1=0. All totalized potential inequalities
hold. If asymptotic positivity held, the existing one-sided excess-control
theorem would imply convergence at every real shift, contradicting the result
at log 2. This refutes the convergence-free receiver.

## Positive survivor and closure audit

This obstruction concerns totalized sums, not a convergent potential counterexample.
The exact surviving criterion is already paper-proved and Lean-formalized:
under summable excess, asymptotic positivity is equivalent to convergence at
`log(floor(exp j)+1)` for every j plus all integer-log potential inequalities.
See `weil-logshift-sparse-convergence.md` and the theorem
`weilLogShiftAsymptoticPositive_iff_sparse_potential`.

Its stronger regularization mechanism is also formalized: convergent probes
covering logarithmic blocks within any fixed radius, with a uniform real lower
bound on their potentials, imply absolute-deviation Cauchy control. This recovers
all-real convergence and uniform panel limits. These exact survivors will be
included in the final axiom audit; do not retire this route with only its negative
statement.

The diagonal envelope construction above is an additional positive theorem.
No claim about external novelty, RH, or mixed-sign rigidity follows. No numerical
experiments, new axioms, or heartbeat increases are permitted.

## Exact new insight and positive closure

Summable excess does not constrain a rapidly growing negative part. A finite
diagonal reciprocal sum can overwhelm every member of a countable positive
kernel family, despite each individual kernel's decay. The resulting divergent
signed series have partial sums tending to minus infinity; their zero totalized
values therefore carry no positivity information.

Positive construction: `exists_nonneg_diagonal_weight_for_positive_kernels`
proves the arbitrary-envelope statement above. Paper proof and Lean proof are
complete, not merely the constant-envelope specialization.

Exact replacement criterion: `weilLogShiftAsymptoticPositive_iff_sparse_potential`
retains convergence only at the explicit exponentially spaced probes, with
integer-log inequalities at every m>=2. Its paper proof is dependency closed in
`../3-formalized/weil-logshift-sparse-convergence.md`; its Lean proof and the two
covering-probe regularization results were re-audited alongside this counterexample.
Thus the no-go is closed with nontrivial positive survivors.

## Lean artifact and validation

Leaf: `formal/GaloisForLFunctions/RHTower/WeilLogShiftConvergenceNoGo.lean`.
Public declarations:

- `exists_nonneg_diagonal_weight_for_positive_kernels`
- `exists_zero_excess_divergent_potential`
- `not_logShift_potential_only_receiver`

Final `lake --old env lean ... -o ...` passed with default heartbeats and no
diagnostics. Scratch API checks, public signatures, and all six axiom audits
passed: the three new declarations and the three positive survivor declarations
each use exactly `[propext, Classical.choice, Quot.sound]`.

Module wired into `RHTower.lean`. Index refresh passed; all three API rows were
verified. Scoped whitespace checks passed. Authoritative lint exited 1 with
seven unrelated unreachable modules: RHTower's `PaperCircleAdaptiveHistory`
and `PaperCirclePosteriorSplitInformation`; HTGeometry's `ApertureConeCalculus`,
`ApertureConeWinding`, `ApertureLogTranslation`, `ApertureOpenHistoryIdeal`, and
`BoundaryCoronaCStarAlgebra`. No reported lint error concerns this leaf.

Local exact lexical search found no indexed combination for the proposed
counterexample. Broader local search returned 1284 declarations across 268
modules and located the potential, convergence, and summation dependencies.
No external novelty claim or exhaustive semantic-search claim is made.

## Remaining frontier

The convergence-free receiver is retired only on its unrestricted coefficient
domain. The nonnegative-domain refinement is now paper-proved and Lean-verified
in `../3-formalized/weil-logshift-nonnegative-potential-domain.md` and
`WeilLogShiftNonnegativePotential.lean`. Nonnegative lam and summable excess
give `|a(n)|<=max(log n,total excess)` independently of test positivity, hence
all-real potential convergence. The potential inequalities alone characterize
asymptotic positivity on this domain. Among nonnegative minorants they hold
exactly for von Mangoldt. All four public theorems passed axiom audits with
only `[propext, Classical.choice, Quot.sound]`.

Genuine mixed-sign rigidity remains open; the exact classification above also
requires the minorant hypothesis.

## Stronger positive survivor: an exact convergence guard

The paper proof and Lean proof in `WeilLogShiftCofinalPotential.lean` now give
an exact operational replacement for the missing convergence condition.
With finite excess, eventual lower bounds on the actual probes at
`m_j=floor(exp j)+1` are equivalent to potential convergence at EVERY real shift.
Each probe may have its own bound and cutoff. Combining this guard with the
potential inequalities at all integer-log samples is equivalent to asymptotic
log-shift positivity (`weilLogShiftAsymptoticPositive_iff_guarded_potential`).
No coefficient nonnegativity or explicit convergence premise remains.

The stronger domain theorem allows ANY cofinal sequence of integer-log probes;
no uniform spacing or monotonicity is required. Its analytic basis is stronger
still: for arbitrary signed weights, convergence of the paired kernel series
on any real shifts unbounded above is equivalent to whole-line convergence,
without a finite-excess assumption. A convergent outer sample dominates each
inner tail; the finite head is harmless.

These are dependency-closed paper proofs and Lean-verified results. All six
new public theorems passed axiom audits with only `propext`, `Classical.choice`,
and `Quot.sound`. See `../3-formalized/weil-logshift-cofinal-potential-domain.md`
for the exact chain and validation. The original convergence-free totalized-sum
receiver remains false; the new guard excludes its divergent counterexample.

## The convergence guard is exactly subexponential growth

`WeilLogShiftSubexponentialDomain.lean` further identifies the guard with an
elementary coefficient condition. For ANY signed real weights v, the following
are equivalent:

- paired-kernel potential summability at every real shift;
- summability of |v(n)|exp(-epsilon*n) for every epsilon>0;
- for every epsilon>0, some C>=0 bounds |v(n)| by C exp(epsilon*n) for all n.

This classification requires neither coefficient nonnegativity nor finite
excess. Its dependency-closed paper proof converts the existing literal-kernel
double-exponential upper/lower envelopes at log n into exponential damping in n.
The remaining damping/growth equivalence follows from single-term bounds and
geometric summability. The complete Lean leaf has compiled.

For Weil deviations with finite excess, subexponential growth is therefore
equivalent to the cofinal-probe lower-bound guard. Together with all integer-log
potential inequalities, it is equivalent to asymptotic positivity. The exact
positive replacement is `weilLogShiftAsymptoticPositive_iff_subexponential_potential`;
validation is recorded in `../3-formalized/weil-logshift-subexponential-domain.md`.
The unrestricted totalized-sum receiver remains retired; no RH or mixed-sign
rigidity conclusion is inferred.
