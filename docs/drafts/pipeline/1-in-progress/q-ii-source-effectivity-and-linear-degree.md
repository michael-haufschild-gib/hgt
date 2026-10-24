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
4. **Full Bézout classification.** For nonnegative even fibre-invariant `Φ`, conjecture
   `Bezout(EΦ) ↔ ∀x y, δ(x,y)²≤Φ(x)Φ(y)`. Necessity uses balanced fibre lifts with
   degrees `sqrt(Φ(x)/2)` and the two source signs; sufficiency is hyperbolic AM–GM.
   This would identify the exact source contraction obligation without assuming Hodge index.
5. **No finite L² reserve at any aperture.** Strengthen the half-coercivity counterexample:
   the Weil Rayleigh quotient is unbounded above on `realTestsAt r` for every `r>0`.
   For arbitrarily large auxiliary aperture `A≥r`, impose the finite low grid of `A`
   and pole conditions on tests supported in `[-r,r]`. Finite-dimensional linear
   constraints leave a nonzero test by the translated-bump construction already used
   in `exists_ne_zero_mem_lowBlindTests`. The existing coercive estimate then gives
   `W(f,f)/∫f²≥lowBlindCoercivity(A)`, which grows without bound. This proves failure
   of Bézout for every finite constant `c`, not just for a strict known lower floor.

## Open obligations

- An original-surface, all-aperture source section theory with RR supply and an independently proved Bézout/degree mechanism remains unproved.
- The proposed payment cohomology must have genuine additive/dimensional content; a Boolean rank encoding of a quadratic inequality does not discharge that obligation.
- Preserve unrelated work already present in this worktree.

## Boundary-rigidity paper proof

[PROVED HERE, paper; Lean audit running.] Write `δ(x,y)=polar(x,y)-pair(x,y)`.
Let `Φ` be nonnegative, even, and unchanged by adding either fibre. The source cone is
`EΦ={x: deg_H(x)≥0, deg_V(x)≥0, Φ(x)≤2 deg_H(x)deg_V(x)}`.

For any source `x`, translate its fibres to degrees `(Φ(x),1/2)`. This keeps both `Φ` and `δ`
unchanged and produces a member `y` of `EΦ` with `y²=Φ(x)-δ(x,x)`. Hence Bézout forces
`δ≤Φ`. Existing RR classification gives `Φ≤δ`. Both axioms therefore force `Φ=δ`.
Conversely exact equality and nonnegativity give Hodge index, RR, and Bézout by the existing
polar-surface theorems. The resulting cone is exactly the positive cone.

The strict cone has the same rigidity: when `Φ(x)<δ(x,x)`, put its polar capacity strictly
between these two values. The resulting class lies strictly inside the source cone but has
negative square. Thus removing the boundary cannot repair Bézout.

All fibre-linear degrees are nonnegative on every `EΦ`, irrespective of the defect. With
`Φ=0`, Bézout holds exactly when `δ` vanishes identically: both `prim(x)` and `-prim(x)`
belong to this cone, so their self and mixed intersections force `δ(x,x)=0`. Conversely
zero defect leaves just the nonnegative hyperbolic pairing in the fibre quadrant.

For `Φ=c∫f²`, the simultaneous RR/Bézout criterion is the exact identity `W(f,f)=c∫f²`
on the entire source subspace, not a lower bound. A concrete counterexample family uses
the existing `lowBlindTests a` at every `a>0`: choose `c=lowBlindCoercivity(a)/2`.
RR and ampleness hold by the proved coercive floor, while a nonzero test has strictly
greater Weil energy and supplies the strict negative-square cycle above. This is an
unconditional example on the original, uncompensated subsurface.

## Related ongoing work

The independent `biarithmetic-geometry-foundations` card audits the proposed ordinary
dimension identity `h⁰-h¹=E(s)` and its weighted arithmetic replacement. It already records
the nonintegrality obstruction below the first prime. Avoid duplicating that work; use its
finished theorem when available. This obstruction does not itself construct the requested
payment sheaf or prove duality.

## Log

- 2026-10-25 — Read attachment and full review; discovered existing all-aperture RR results and the opposite inequalities governing RR versus Bézout. Began boundary-rigidity audit.
