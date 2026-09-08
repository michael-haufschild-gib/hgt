# CCM-FU: fixed coercive weight for signed energy transfer

- Stage: 1-in-progress.
- Type: [BRIDGE], source-specific selection candidate, unproved.
- Target: uniform signed Abel bound and RH through complete prime selection.
- Prior facts: monotone Q paths fail at cutoff 7; universal local V descent
  fails at cutoff 25 while both full successor envelopes contract.

## Frozen mathematical question

Write Q(M,P) for the actual retained sum-of-squares energy, H(M,P) for
its empty-label head, and V=Q-H². For a fixed real 0<alpha<1 define

`L_alpha(M,P)=V(M,P)+alpha H(M,P)^2`.

Does there exist one alpha, independent of cutoff, such that at every
cutoff some complete prime ordering makes L_alpha nonincreasing at every
step? The stronger separate question asks whether one such alpha supplies
a nonincreasing next step at EVERY proper actual processed state.
Failure of the stronger statement does not refute the complete-path claim.

This potential keeps positive control of both head and nonempty field
while permitting the transfers forced by the cutoff-25 theorem. It is
a bridge candidate in the standard quadratic-potential framework, not
a new universal theory or an asserted solution. Its truth is uncertain.
Unlike V alone, its terminal value is alpha times the complete signed
sum squared. Initial L_alpha is at most Q(empty), already bounded by
722 M². Thus a uniform positive weight and complete monotone paths would
give the required uniform signed bound. No final bound is assumed.

## Frozen discriminating experiment

Reuse all 8,860 saved subset states at cutoffs 1..32. Recover heads from
the audited isolated late-prime energy identity and cross-check all late
anchors. Regenerate no channels in the primary screen and do not enlarge
the range. Each edge imposes the affine inequality

`Delta V + alpha Delta(H²) <= 0`.

Compute its full admissible interval inside [0,1], without a weight grid.
Represent interval endpoints by exact fractions of the recovered binary
floating-point values. Propagate finite unions of intervals through every
subset state: union over predecessor paths of their weight intervals
intersected with the edge interval. Intersect terminal feasible sets over
all cutoffs. Separately intersect, over all proper states, the union of
their outgoing-edge intervals. These answer complete paths and universal
local extension respectively on the saved data, without conflating them.

Run both relaxed and tightened inequalities with right sides respectively
+tau and -tau, tau=1e-12 max(1,Q(empty)). The relaxed set contains possible
small errors; an empty relaxed set is a robust candidate obstruction.
The tightened set identifies finite paths with margins. Save each cutoff's
sets, cumulative intersections, and the first empty cumulative set for
each assertion. Retain all earlier cutoffs that strictly reduced that
intersection as its finite obstruction certificate.

Independently reconstruct the defining arithmetic channels at 80 decimal
digits for the cutoffs in the first obstruction certificate for each
assertion. Repeat the interval graph test from these direct fields. If a
claim has no empty relaxed intersection, audit its narrowest nonempty
cumulative set and record the weight interval; do not extend the range.
Finite passes and numeric interval endpoints remain guidance only.

Run only on the supplied RunPod with at most eight workers, one-thread
numeric libraries, a 50-second internal deadline and 60-second external
timeout. Download script, results, input hashes and audit; remove owned
remote files and workers. No numerical value enters Lean.

## Interpretation and next proof obligation

If no fixed positive weight survives, extract the exact incompatibility
between required payments; do not rescue the frozen claim with a variable
weight. Audit the strongest positive classification before retirement.
If weights survive, attack the arithmetic signed inequality for that
whole range and its compatibility under exhaustive selection. Do not
promote a finite interval into an all-cutoff result.

## Current result

The frozen RunPod screen and independent source reconstruction preserve
complete monotone paths for every weight in (0,0.2009978627...) across
the saved cutoffs. The endpoint is constrained successively at 7, 11
and 19; it is numerical guidance, not an all-cutoff bound.

Universal local descent is incompatible with every fixed weight already
at cutoff 25. Two actual states expose the conflict: the core leaving
only prime 7 requires a small head weight to absorb a same-sign leaf;
the core leaving primes 3 and 5 requires a larger head weight to pay
its forced nonempty-energy growth. Analytic certification and exact
positive completion criteria are in progress. The main complete-path
claim remains unchanged and open.
