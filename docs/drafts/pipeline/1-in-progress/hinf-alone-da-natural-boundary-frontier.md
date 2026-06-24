# H-infinity Alone for DA Natural Boundaries

- **ID:** hinf-alone-da-natural-boundary-frontier
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** split from `../2-fully-proven/not-new/ade-boundary-hinf-ht.md`
- **Statement:** There exists a holomorphic differentially algebraic function `f in H^infty(D)` whose unit
  circle is a natural boundary. Equivalently, function-level boundedness alone cannot replace bounded
  order-`n` jet control in the ADE bounded-jet continuation lemma.

## Goal

Separate the open frontier from the classical bridge lemma:

```text
bounded order-n jet + ADE  =>  no natural boundary
```

The proven bridge uses boundedness of the jet to keep the companion-system trajectory a positive distance
from the separant-singular locus near a good boundary approach. This card asks whether the derivative
boundedness is genuinely necessary.

If the conjecture is true, the witness should satisfy:

1. `f` is holomorphic and bounded on `D`;
2. `f` satisfies a nonzero algebraic differential equation over `C(z)`;
3. `partial D` is a natural boundary for `f`;
4. some derivative in the minimal ADE jet is unbounded near `partial D`.

## Gates

- [x] 0 -> 1 in-progress: well-posed frontier split from the ADE bounded-jet card.
- [ ] 1 -> 2 fully-proven: construct an explicit witness or prove an impossibility theorem.
- [ ] 2 -> 3 formalized: not planned until the analytic construction is complete.
- [ ] 3 -> 4 publication-ready: standalone note comparing the witness with Chazy/quasi-Painleve examples.

## Mechanism

The candidate mechanism is a boundary built from accumulating finite-value algebraic branch points.

At a local algebraic branch point,

```text
f(z) = a_0 + a_1 (z-z_0)^(1/q) + ...
```

the function value can remain finite while

```text
f'(z) ~ (a_1/q) (z-z_0)^(1/q - 1)
```

blows up. A dense accumulation of such branch points on `partial D` would give a natural boundary while
leaving open the possibility that `f` itself stays bounded.

This is the bounded analogue of the Chazy pole barrier: Chazy-type natural boundaries are compatible with
algebraic differential equations because derivatives blow up. The desired witness replaces accumulating
poles by accumulating finite-value algebraic branch points.

## Attack Plan

1. Search quasi-Painleve / movable algebraic singularity examples for an equation whose movable singularities
   are finite-value branch points and whose solutions can accumulate those branch points at a circle.
2. Prove a concrete solution remains globally bounded in the disk.
3. Prove the accumulation set is a genuine natural boundary, not just a large singular subset.
4. Verify the minimal ADE order and identify which derivative leaves `H^infty`.

## Failure Mode

If every bounded DA function on `D` has enough derivative/separant control to continue through at least one
boundary point, then this conjecture is false and the ADE bridge can be strengthened from bounded order-`n`
jet to `f in H^infty`.

## Log

- 2026-06-24 — Split from `ade-boundary-hinf-ht.md` after the bounded-jet theorem was classified as a
  not-new classical bridge lemma. This card now carries the unproven frontier conjecture.
