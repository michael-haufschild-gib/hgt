# Literal first-atom odd-four positivity

- **ID:** TT-C53-first-atom
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [C53 source card](../1-in-progress/tt-actual-odd-border-primitive.md)
- **Statement:** For every real center whose first-atom scale q is at least five,
  the signed odd reflection matrix of the literal first theta atom through
  order fourteen is positive definite.

## Scope

This proves a finite-rank source head, not the full theta source or RH.
The signed unequal-pair contribution remains an open obligation. In particular,
the theorem cannot be used as if it proved C53 at the compensation zero.

## Paper proof [PROVED HERE]

Write B=(2q-3)^2 and K=4q^2 exp(x-2q)>0. The existing exact source identity
expresses the first-atom reflected pair as K times

    A(q,B,t) = (B-12q(cosh(2t)-1))*exp(-2q(cosh(2t)-1)).

Its derivative is -4q sinh(2t) A(q,B+6,t). Leibniz gives the even-jet
recurrence, with R_0(q,B)=B,

    R_(n+1)(q,B) = -4q sum_(j=0)^n choose(2n+1,2j+1)
                    *2^(2j+1)*R_(n-j)(q,B+6).

Thus R_n is exactly the source's derivative of order 2n after removing K.
The finite recurrences through n=7 supply every odd-block entry.

For coefficient vector c, define

    z3 = c3,
    z2 = c2-(56-168q)z3,
    z1 = c1-(20-80q)z2-(784-3360q+6720q^2)z3,
    y0 = c0-(4-24q)z1-(64-320q+960q^2)z2
            -(2304-10752q+26880q^2-53760q^3)z3,
    y1 = -24q z1, y2 = 768q^2 z2, y3 = -43008q^3 z3.

This triangular transformation is invertible for q>0. Direct substitution
of the exact finite recurrence gives the source energy K*8qB*y^T M y.
The full displayed matrix M and its row certificates are on the C53 card.
Its parameters v=1/(2q), h=6/B satisfy
0<v<=1/10 and h(1-3v)^2=6v^2. Its first three row diagonal-dominance
reserves are positive. For the last reserve R, writing r=1-10v gives

    112000(1-3v)^2 R
      =6083+45941r-13814r^2+26166r^3+14931r^4+693r^5 > 0,

because 0<=r<=1. The signed cross-term square inequalities then prove
strict positivity for every nonzero y. Positive K*8qB and invertibility
of the coordinate transformation prove the literal source conclusion.
Every step above, including the source incidence, is in the checked leaf.

## Lean certificate

Module: `GaloisForLFunctions.RHTower.ThetaCuspFirstAtomOddFourPositivity`.
Public definition: `RHTower.ThetaCuspOddCentral.firstAtomOddFour`.
Public theorem: `RHTower.ThetaCuspOddCentral.firstAtomOddFour_posDef`.
All recurrence, coordinate, and matrix helpers are private.

- Targeted `lake build --old +GaloisForLFunctions.RHTower.ThetaCuspFirstAtomOddFourPositivity`: passed.
- Final `lake env lean GaloisForLFunctions/RHTower/ThetaCuspFirstAtomOddFourPositivity.lean`: passed.
- Compiled-module axiom audit of both public declarations: only
  `propext`, `Classical.choice`, `Quot.sound`.
- Wired once into `RHTower.lean`; declaration index refreshed.
- Global formal lint: ten unrelated unreachable modules; this leaf is not flagged.
- No full or umbrella build, heartbeat increase, numerical experiment,
  added axiom, subagent, commit, or push.

## Research consequence

The first-atom odd-four reserve is now a verified starting point for the
complete-source comparison on the neutral window. The actual two-atom
core still needs a sign certificate through order fourteen, and the
infinite omitted source must be included. Neither a positive first-atom
matrix nor a positive single test direction proves that full matrix.

## Log

- 2026-10-02 — Paper certificate closed by exact affine source recurrence;
  all source and positivity steps formalized and directly audited.
