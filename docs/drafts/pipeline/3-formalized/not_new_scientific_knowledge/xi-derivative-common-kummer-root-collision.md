# Xi--derivative common Kummer-root collision

- **ID:** `xi-derivative-common-kummer-root-collision`
- **Stage:** 3-formalized
- **Type:** TOP-DOWN RH CHAIN / ADJACENT KUMMER CONSTRAINTS
- **Scientific status:** `[BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Lean parents:** `KummerObstruction`, `RHLadderTheory`
- **Lean module:** `formal/GaloisForLFunctions/RHTower/XiDerivativeKummerCollision.lean`

## Statement

Let `d>1`.  Suppose both `xi` and its derivative admit analytic `d`-th roots on the right
half-plane `Re s > 1/2`.  Then RH holds.

Indeed, a hypothetical right-half zero of `xi` has some positive order `m`.  The root of `xi`
forces `d | m`.  Its derivative has order exactly `m-1`, while the root of the derivative forces
`d | (m-1)`.  Hence `d | 1`, contradicting `d>1`.

```text
common analytic d-th Kummer root of xi and deriv xi on Re s > 1/2, d > 1
  -> d divides ord(xi) and ord(deriv xi) at every right-half xi zero
  -> d divides m and m-1
  -> no right-half xi zero
  -> RH.
```

For `d=2`, the first premise is exactly `RHLadder 1`.  Thus the square-root specialization is

```text
RHLadder 1
  + analytic square root of deriv xi on the right half-plane
  -> RH.
```

## Non-circularity and kill tests

Neither root condition alone excludes right-half zeros: it only restricts their local
multiplicities.  The proof uses the derivative's one-order shift, not a zero-free assumption or a
sign condition.  The derivative-root condition permits arbitrary derivative zeros whose orders
are multiples of `d`.

The separation is visible already in elementary models.  The function `(z-a)^d` has a global
`d`-th root while retaining a zero, so the Xi-root premise alone is not zero-freeness.  Conversely,
`z-a` has derivative `1`, whose `d`-th root is constant, while the original function still has a
zero.  It is precisely the simultaneous cover—not either cover separately—that is impossible at
one zero.

This mechanism is elementary Kummer/divisor theory and is not claimed as new scientific
knowledge.  Its value is as a genuinely different source interface: a construction of compatible
ramified covers for the theta source and its differentiated source would close RH without Weil
positivity, anti-Herglotzness, zero enumeration, or the rectangular subpower route.

The route dies if the proposed derivative cover is obtained by first reading the Xi divisor, or
if it only supplies roots on a domain with the Xi zeros removed.  The root must be analytic across
the entire right half-plane.

## Open core

`[OPEN CORE]` Construct, from the theta--prime--Gamma source and without using Xi zero locations,
one common degree `d>1` Kummer cover for `xi` and `deriv xi` on `Re s>1/2`.  The minimal target is
an analytic square root of `deriv xi` together with the already isolated first Xi ladder rung.

## Gates

- [x] exact derivative order loss available in complex analytic order theory
- [x] analytic roots force local order divisibility
- [x] formalize the common-root collision implication
- [ ] construct the Xi root without divisor-selected data
- [ ] construct the derivative root without divisor-selected data
- [ ] RH

## Formal verification

Lean proves the general common-degree theorem
`riemannHypothesis_of_xiDerivativeCommonKummerRootRightHalf` and the square specialization
`riemannHypothesis_of_rhLadder_one_of_xiDerivativeSquareRootRightHalf`.  The named module build
passes in the repository toolchain.  Both capstones use only `propext`, `Classical.choice`, and
`Quot.sound`.
