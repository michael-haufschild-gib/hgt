# Q-II: source effectivity, Riemann–Roch, and linear degree

- **ID:** q-ii-source-effectivity-and-linear-degree
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** docs/reports/review-2410/opus.md, Q-II and Mechanism B
- **Statement:** Determine a source-defined cone on the original scaling surface satisfying Riemann–Roch at every aperture, and determine whether its Bézout axiom follows from an independent linear degree law.

## Goal

Answer Q-II in full; formalize the answer and its corollaries without extra analytic assumptions, and apply results across the existing programmes. A reformulation of RH, a compensated pairing, a restricted test space, or a degree-positive cone without Bézout does not complete this goal.

## Gates

- [x] Read the full review and inspect the current source frontier.
- [x] Search the Lean corpus before mathlib.
- [ ] Dependency-closed paper proof of the full answer.
- [ ] Lean proofs, individual foreground `lake --old env lean` audits, and transitive axiom checks.
- [ ] Umbrella imports and applications to relevant existing programmes.

## Current evidence

Existing `AllApertureSourceRiemannRochAndCoercivityLaws` proves all-aperture RR for graded cones with negative reserves, and RR on compensated surfaces. Neither provides the requested cone with an independent Bézout law on the original surface. The existing nonnegative source-cone theorem identifies RR with the lower bound `Φ ≤ defect`.

The actual theorem `sourceCone_bezout_of_defect_le` uses the opposite bound `defect ≤ Φ`, together with Hodge index. The overview of `SourceDeterminantalSectionsAndArithmeticRiemannRoch` incorrectly describes this direction in its first numbered item. Audit the consequences before correcting prose.

## Conjecture loop

1. **Boundary rigidity.** For a nonnegative fibre-invariant source functional, RR and Bézout together force `Φ(x) = defect(x,x)` pointwise. Test this by translating each primitive source to the exact determinantal boundary `2 deg_H deg_V = Φ`.
2. **Linear degree limitation.** Fibre degrees alone do not see primitive negative-square directions. Identify the exact positive survivor: all degree-linear tests determine only the fibre quadrant, while Bézout requires the source boundary.
3. **Further source construction.** Use the rigidity result to test candidate source section theories, principal divisors, and payment cohomology; do not stop at the negative result.

## Open obligations

- An original-surface, all-aperture source section theory with RR supply and an independently proved Bézout/degree mechanism remains unproved.
- The proposed payment cohomology must have genuine additive/dimensional content; a Boolean rank encoding of a quadratic inequality does not discharge that obligation.
- Preserve unrelated work already present in this worktree.

## Log

- 2026-10-25 — Read attachment and full review; discovered existing all-aperture RR results and the opposite inequalities governing RR versus Bézout. Began boundary-rigidity audit.
