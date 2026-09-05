# Literal weighted chronological schedule boundary

Status: formalized source boundary conservation. No RH producer.

## Target and scope

Test the proposed source schedule transgression without assuming its vanishing.
For weighted deletion jumps `x` and a squarefree interaction `y`, keep the original
Mellin factor and vary the inner chronological cutoff `K_N(n)` before taking the
outer cutoff `N`. Does simultaneous zero closure eliminate the boundary between
strict and inclusive chronological order?

Corpus inputs: `EulerDeletionQuasiShuffleSecondConvergence` gives the exact
zero-endpoint Abel decay; `EulerDeletionFactorizationGraded` gives the positive
weighted singleton/interaction cross term. `EulerDeletionQuasiShuffleOrderedDilation`
retains finite strict floor boundaries, but supplies no moving-schedule theorem.
Full-index searches for chronological slope/jump, ordered wedge boundary,
deletion uniform schedule, and uniform modulus were checked before this target.

## Paper derivation

Suppose `sigma>1/2`, `|sum_(m<k) x_m| <= A(k+1)^(-sigma)`,
and `|y_n| <= B(n+1)^(-sigma)`. Fix `c>0`. Every schedule with
`K_N(n)+1 >= c(n+1)` has its outer summand bounded by
`AB c^(-sigma)(n+1)^(-2sigma)`, independently of `N`. This is summable.
If each fixed row eventually stabilizes at `k(n)`, dominated convergence gives
the ordinary series with that row cutoff. No upper bound on `K_N(n)` is needed.

Taking the two row limits `n` and `n+1`, the difference is exactly
`sum_n x_n conj(y_n)`, not zero. For the literal singleton `a_Q(n)n^(-s)`
and interaction `a_P(n)a_Q(n)n^(-s)`, this is the real source number
`Z(2sigma)(1-P P^(-2sigma))(1+Q(Q-2)Q^(-2sigma))`, strictly positive
for coprime `P,Q>1`. The hypothetical zeta zero supplies the Abel estimate;
it does not annihilate the boundary.

Proved consequence: moving cofinal cutoffs satisfying a common positive
relative lower bound cannot erase this particular strict/inclusive boundary.
This does not classify three-index regions, unbounded arity, or schedules whose
inner/outer ratio collapses to zero. It is not an RH proof or a blanket retirement.
Generic dominated convergence and diagonal splitting are classical; no novelty claim.

Explicit schedules are `Kminus_N(n)=n-floor(n/(N+2))` and
`Kplus_N(n)=n+1+floor(n/(N+2))`. Both satisfy the relative lower bound `c=1/2`;
each row eventually becomes respectively `n` and `n+1`. The construction is fixed
before any zero. The generic theorem permits arbitrary overshoot of the inner cutoff:
only its positive relative lower bound and eventual row stabilization are needed.

## Research consequence

The proposed cancellation does not follow from cofinal schedule independence:
the exact source boundary survives that independence. This closes the present
two-index, fixed-positive-ratio test. It does not disprove a global RH-equivalent
annihilation statement: such a statement still needs an independent arithmetic law.
No actual off-line zero is asserted or used as a counterexample.

Do not repackage this diagonal identity as the missing producer. A successor using
this pair must supply another arithmetic relation, not assume that simultaneous
closed endpoints identify the strict and inclusive orientations. Higher-index
regions and collapsing-ratio schedules remain outside this theorem.

Periodic-coefficient ordered Dirichlet sums belong to the classical family in
Kelliher–Masri, [equation (1.4) and section 9.2](https://math.ucr.edu/~kelliher/papers/LFunctionsFull.pdf).
The interchange here uses mathlib's proved Tannery theorem, not a new convergence principle.

## Verification

Leaf: `formal/GaloisForLFunctions/RHTower/EulerDeletionChronologicalScheduleBoundary.lean`.
Namespace: `RHTower.DeletionSchedule`.

- `tendsto_scheduledPrefix`: all moving schedules in one positive relative cone.
- `interaction_diagonal`, `tsum_interaction_diagonal`: exact weighted arithmetic collision.
- `source_schedule_boundary`: source-derived boundary at every hypothetical right-half zero.
- `canonical_source_boundary`: explicit source schedules with the positive boundary retained.

Scratch and published leaf passed without warnings. Seven imported capstone axiom audits
returned only `propext`, `Classical.choice`, `Quot.sound`. Global formal lint passed with
existing large-file warnings. Olean built; umbrella wired, never built. All owned processes
finished. No numerical computation, RunPod job, new axiom, or RH assumption was introduced.
