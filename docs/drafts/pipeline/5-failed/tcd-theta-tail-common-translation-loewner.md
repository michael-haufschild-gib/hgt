# TCD theta-tail common-translation Loewner propagation

- **ID:** TCD-CTL
- **Stage:** 5-failed
- **Type:** PROVEN ROUTE NO-GO; POSITIVE SURVIVOR RETAINED
- **Corpus source:** `scripts/formal_tools.py research` results for
  `theta tail common translation Loewner derivative generator determinant shift-tail`, together
  with `thetaTailFirstMomentKernel_eq_shiftTail` and the all-plane theta-tail Bezoutian endpoint.

## Conjecture TCD-CTL1

For every nonnegative common shift `a`, the finite kernel difference

`thetaTailFirstMomentKernel x_i x_j - thetaTailFirstMomentKernel (x_i+a) (x_j+a)`

is positive semidefinite for every finite real node packet.

## Exact RH proof chain this conjecture tries to close

1. Prove positive semidefiniteness of `thetaTailFirstMomentKernel` on nonnegative nodes using its
   corpus geometric--deficit decomposition.
2. Given an arbitrary finite real packet, choose one common shift carrying all nodes into the
   nonnegative cone.
3. TCD-CTL1 adds a positive-semidefinite translation defect to the shifted positive-cone matrix,
   giving all-plane kernel positive semidefiniteness.
4. The corpus double-Laplace identity transfers this to theta-tail first-moment Bezoutian
   positivity.
5. Apply `riemannHypothesis_iff_posSemidef_thetaTailFirstMomentBezoutian` to obtain RH.

Thus TCD-CTL1 would remove the complete mixed-sign extension burden, rather than improve a bound.

## Hostile first test

Differentiate the corpus shift-tail formula under common translation.  The negative derivative is
the rank-two kernel

`G_a(x,t) = (x+t+2a) f(x+a) f(t+a)`, where `f = thetaCuspFullSource`.

Loewner decrease forces every finite compression of `G_a` to be positive semidefinite.  Test its
smallest nontrivial compression before attempting any finite-shift theorem.  A strictly negative
two-node determinant kills the conjecture and proves that any surviving mixed-sign propagation
must use nonlocal finite-shift cancellation, not an infinitesimal Loewner flow.

## Log

- 2026-08-29 — conjecture admitted from exact corpus shift-tail identity and all-plane Bezoutian
  endpoint; frontier map remains read-only.
- 2026-08-29 — route killed unconditionally in Lean.  The common-shift derivative is exactly
  `-G_a`.  Every distinct two-node compression of `G_a` has determinant
  `-(x-t)^2 f(x+a)^2 f(t+a)^2 < 0`.  More strongly, a closed local-rise argument produces an
  actual finite shift `b>1` for which the kernel difference from cut `1` has a strictly negative
  quadratic direction.

## Positive survivor

Mixed-sign extension cannot follow from any Loewner-decreasing common-translation flow, even
locally and even on the positive node pair `{0,1}` after shifting to cut `1`.  A successful TCD
closure must therefore retain nonlocal cancellation across the full shift interval, use a
different non-common transport, or attack the all-plane kernel directly.  The exact moving-cut
identity, derivative law, universal negative determinant, and actual finite-shift witness are all
formalized in `ThetaTailCommonTranslationLoewnerNoGo`.
