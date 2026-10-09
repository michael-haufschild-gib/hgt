# Finite excess: pointwise probes recover their own convergence

Status: [FORMALIZED]
Date: 2026-10-09
Source policy: our Lean corpus only; no web or external papers.

## Target and plan

Remove coefficient nonnegativity and sampled-potential convergence from the
pointwise-to-uniform log-shift positivity criterion, retaining finite positive
excess. This discharges the extra analytic domain assumptions in
`WeilLogShiftPointwiseCriterion.lean` rather than changing the target positivity.

1. Extract the existing generic nonnegative head/tail bound from
   `WeilLogShiftDivergentMinorant.lean`; preserve its existing theorems.
2. Prove divergent deficit mass forces a fixed probe to minus infinity with
   summable excess. Treat origin divergence first, then shifted divergence
   when origin mass is finite.
3. Recover origin and sampled convergence from eventual lower bounds on probes.
   Deduce the pointwise/uniform equivalence using the existing convergent-domain
   theorem. Extract a persistent fixed negative witness when positivity fails.
4. Compile/export changed and new leaves, audit every changed/new public theorem,
   wire, index, lint, promote card, save memory, clean owned scratch.

## Closed paper argument

Write a=e-v, e=max(a,0), v=max(-a,0), E=sum e<infinity. Put
T_w(L,y)=sum_n w(n)[K_L(y+log n)+K_L(y-log n)] and
D_L=sum_n v(n)K_L(log n). All truncated sums have finite support.
For every L,y, 0<=T_e(L,y)<=2K(0)E. The exact corpus probe identity is
Q_m(L)=W_m(L)+2[T_e(L,log m)-T_e(L,0)+2D_L-T_v(L,log m)],
and W_m(L)->0.

If sum v(n)K(log n) diverges, then D_L->infinity. The previous tail theorem
gives, for each fixed c=log m>=4, some finite H with
4D_L<=T_v(L,c)+4H for every L. Hence
Q_m(L)<=W_m(L)+4K(0)E-4D_L+8H -> -infinity.
One fixed eventual lower bound at m0=floor(exp4)+1 therefore forces origin
deficit summability.

With finite origin mass D, 2D_L<=2D. If the nonnegative full deficit series at
a fixed log m diverges, finite partial sums and termwise kernel convergence
give T_v(L,log m)->infinity (cutoff monotonicity is unnecessary). Thus
Q_m(L)<=W_m(L)+4K(0)E+4D-2T_v(L,log m)->-infinity.
An eventual lower bound at that probe forces shifted deficit summability.
The excess potential series is summable at every real shift by its uniform
kernel bound; subtracting deficit recovers signed convergence.

Pointwise approximate positivity supplies all needed eventual lower bounds
(choose epsilon=1), hence origin and every integer-log sample converge. Apply
the already-proved convergent-domain pointwise/uniform equivalence. Conversely,
uniform positivity already supplies all potential convergence and pointwise
positivity through the existing theorem.

For a failed uniform-positive sequence, either origin deficit diverges (use
m0), some sampled deficit diverges (use that probe), or all relevant potentials
converge. In the last case the sampled-potential criterion gives a strictly
negative limiting probe, hence a fixed positive negative margin eventually.
All three cases yield a persistent fixed witness in sufficiently late panels.

## Corpus evidence and boundaries

Local lexical search returned 439 declarations across 189 modules, with 261
eligible entries. Inspected actual definitions/proofs in the divergent-minorant,
pointwise-criterion, sampled-potential, excess-control, and deviation-translation
modules. Existing results require either nonnegative coefficients or explicit
sample convergence; the new argument supplies that convergence from probe
behavior. No numerical experiments, analytic axioms, external novelty claim,
RH conclusion, heartbeat increase, or full/umbrella build.

General mixed-sign rigidity remains open. Finite excess is retained as the
domain condition; it is not claimed automatic for arbitrary coefficients.

## Verification checkpoint

The extracted generic `exists_truncated_origin_gain_bound` and preserved
minorant theorems compiled/exported at default heartbeats. The new
`WeilLogShiftSignedDivergence.lean` compiled/exported without diagnostics:
signed/deficit convergence equivalence, nonnegative potential divergence,
uniform excess budget, divergent-origin probe limit, and divergent-sample
probe limit are checked. The scratch API audit passed.

`WeilLogShiftFiniteExcessCriterion.lean` compiled/exported without diagnostics
at default heartbeats. Its four public theorems recover origin convergence
from one lower-bounded large probe, recover sampled signed convergence from
that probe's lower bound, remove nonnegativity and convergence from the
pointwise/uniform criterion, and extract a persistent fixed negative witness
for every failed finite-excess sequence. Both new modules are wired.
All 14 public theorems across the three touched leaves passed the axiom audit,
with only `propext`, `Classical.choice`, and `Quot.sound`. Ten public theorems
are new; four existing minorant-module theorems retain their statements. The
generic head/tail estimate is extracted once and reused by the minorant and
signed proofs.

Final checks:

- `lake --old env lean <leaf> -o <local olean>` passed for
  `WeilLogShiftDivergentMinorant.lean`, `WeilLogShiftSignedDivergence.lean`, and
  `WeilLogShiftFiniteExcessCriterion.lean`, at default heartbeats, without
  diagnostics. The scratch axiom audit imported the final exported leaf.
- `scripts/formal_tools.py index` passed; all 14 public API rows were checked.
- `scripts/formal_tools.py lint` passed globally. The unrelated missing-import
  error recorded in the preceding increment is no longer present.
- Scoped whitespace checks passed. No full or umbrella build was run.

## Exact advance

Finite positive excess suffices for pointwise approximate positivity to imply
a cutoff uniform over every expanding panel. Removed coefficient nonnegativity
and every explicit origin/sampled convergence premise from this criterion.
The actual probe lower bounds force their own analytic domain: divergent
deficit mass would make a fixed probe tend to minus infinity. Thus any failure
in the finite-excess domain is already persistent at one fixed probe.

The earlier no-go for convergence-free *totalized potential inequalities*
remains valid. This theorem uses actual truncated probe behavior to recover
convergence before passing to full potentials.

## Next conjecture

Under finite excess, eventual lower bounds on a cofinal sequence of integer-log
probes may characterize convergence of the potential at every real shift.
Origin convergence follows from one large probe; an outward convergent sample
may dominate each intermediate kernel tail via the uniform shift-gain theorem.
This domain classification is unproved here and needs its own corpus/paper audit.
