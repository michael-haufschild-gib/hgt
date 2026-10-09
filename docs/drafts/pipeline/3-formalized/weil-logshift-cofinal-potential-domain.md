# Cofinal probes characterize the whole potential domain

Status: [FORMALIZED; GLOBAL LINT HAS ONE UNRELATED UMBRELLA ERROR]
Date: 2026-10-09
Source policy: our Lean corpus only; no web or external papers.

## Target and plan

Characterize whole-real-line potential convergence using only eventual lower
bounds on any cofinal sequence of integer-log probes, under finite excess.
Use this to replace explicit convergence in the potential-inequality receiver
by lower bounds on the fixed sparse sequence floor(exp j)+1.

1. Transfer the proved cutoff-uniform inward-shift gain to the full kernel.
2. Prove a convergent outer potential with arbitrary signed weights at c controls
   each potential at y with c>=|y|+4; finite heads impose no restriction.
3. Derive whole-line convergence iff convergence on any cofinal sample sequence;
   then iff eventual lower bounds on cofinal actual probes, with no common
   bound, cutoff, spacing, or monotonicity requirement.
4. Instantiate the explicit sparse sequence and derive the guarded
   potential-inequality receiver. Retain inequalities at all integer-log samples.
5. Compile/export final leaf, audit all public theorems, wire/index/lint,
   promote card, save memory, clean owned scratch.

## Closed paper proof

The previous cutoff-uniform theorem gives A*K_L(x)<=K_L(x-d) eventually in x,
for every L whenever d>=4. Passing L to infinity gives the same full-kernel
bound. For c>=|y|+4 apply it at x+y with d=c+y and at x-y with d=c-y, A=1.
Both right sides are K(x-c). Evenness and nonnegativity therefore give, for
large x,

K(y+x)+K(y-x) <= 2[K(c+x)+K(c-x)].

For arbitrary signed weights v, multiply by |v(n)|. The nonnegative paired
kernel identifies these terms with norms of the weighted terms. The norm of
the convergent outer real series is summable, so it dominates the inner tail.
The finitely many remaining integer n form a summable head. Consequently,
convergence on any sequence unbounded above is equivalent to convergence at
every real shift, for arbitrary signed weights, WITHOUT finite excess.
This strengthening has the same closed domination proof; finite excess enters
only in the subsequent recovery from actual probe bounds.

Now let m_j be integer probes with log(m_j) unbounded above. If every actual
probe Q_{m_j}(k) has its own eventual lower bound, choose one log(m_j)>=4.
The previous theorem forces finite origin deficit moment. Each probe lower
bound then forces signed convergence at its sample. Cofinality gives whole-line
convergence. Conversely, whole-line convergence gives a finite limit for every
fixed probe, hence an eventual lower bound. No positivity of those limits is
needed for this domain classification.

The explicit m_j=floor(exp j)+1 is cofinal by integer_log_probe_bounds. Thus
its eventual lower bounds recover all convergence needed by the existing
sampled-potential positivity theorem. Combining them with the inequalities
psi(0)<=psi(log m) for ALL integers m>=2 is equivalent to uniform asymptotic
log-shift positivity. Sparse inequalities alone are not claimed sufficient.

## Corpus evidence and boundaries

Cached lexical search: 342 declarations, 124 modules, 174 eligible entries.
Relevant current sources inspected: TailComparison, FiniteExcessCriterion,
SignedDivergence, ExcessControl. Existing sparse-potential theorem requests
convergence on its prescribed sequence; this result characterizes that domain
from actual probe behavior, including arbitrarily sparse cofinal sequences.

No RH or general mixed-sign rigidity conclusion. Finite excess is retained for
the probe-bound domain characterization and the positivity receiver, but is
unnecessary for the general weighted-series convergence classification.
No external novelty claim, numerical experiments, analytic axioms, heartbeat
increase, full build, or umbrella build. The totalized-potential no-go remains
valid without the new convergence guard.

## Verification checkpoint

New `WeilLogShiftCofinalPotential.lean` compiled/exported without diagnostics
at default heartbeats. All six public theorems are proved, including the
arbitrary-signed-weight convergence classification and the guarded positivity
receiver. The norm-summability and eventual comparison APIs were verified in
a scratch file. The leaf is wired into `RHTower.lean`; scoped whitespace
checks passed. All six public theorem axiom audits passed with only `propext`,
`Classical.choice`, and `Quot.sound`. `scripts/formal_tools.py index` passed;
all six API rows were checked. Final leaf audit used
`lake --old env lean GaloisForLFunctions/RHTower/WeilLogShiftCofinalPotential.lean
-o .lake/build/lib/lean/GaloisForLFunctions/RHTower/WeilLogShiftCofinalPotential.olean`.

Global lint exited 1 solely because the unrelated
`GaloisForLFunctions.RHTower.ChronologicalBoundedRowMobiusRigidity` module is
unreachable from its theorem-area umbrella. No reported error concerns this
leaf. Unrelated sources/imports were not modified. No full or umbrella build
was run.

The failed convergence-free route card now records this exact positive survivor
and its paper/Lean status, preserving the counterexample and its scope.

## Exact advance

Whole-line kernel-potential convergence has an exact cofinal sampling criterion
for arbitrary signed weights. This requires neither coefficient growth nor
finite excess. For actual Weil deviations with finite excess, individual lower
bounds on cofinal probes are an exact equivalent condition. Their bounds and
cutoffs can vary freely with the probe. The explicit exponential probes give
a valid convergence guard for the potential-inequality receiver; every
integer-log potential inequality is still required.

## Next conjecture

Whole-line convergence for arbitrary signed weights may be equivalent to
`forall epsilon>0, Summable (fun n => |v(n)|*exp(-epsilon*n))`, hence to
subexponential coefficient growth. The corpus's full-kernel double-exponential
upper and lower envelopes suggest this after substituting log n. This potential
domain/growth correspondence is unproved here and needs a fresh corpus and
paper audit before formalization.
