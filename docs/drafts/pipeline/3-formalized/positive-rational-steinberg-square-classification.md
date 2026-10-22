# Positive-rational Steinberg square classification

- **Stage:** 3-formalized
- **Type:** exact source-ideal classification / positive survivor
- **Date:** 2026-10-06
- **Status:** paper and Lean proofs complete; novelty unverified; no RH closure

## Statement

Let `R=C[Q_{>0}^*]`, with basis `[q]`, augmentation ideal `I`, and ideal
`J=([x]-1)([1-x]-1) : x rational, 0<x<1`. Then `J=I^2`.
For the actual full rational group algebra, replace `I` by the positive augmentation ideal
`I_+`. The carrier audit and corrected full-source theorem are detailed below.

The positive survivor is an exact presentation `R/J = R/I^2`, canonically the
square-zero algebra `C direct-sum (Q_{>0}^* tensor_Z C)`. This retains every independent
prime tangent direction, not only the one-dimensional logarithmic Kummer regulator.
It neither locates Xi zeros nor constructs the missing source-marked geometric comparison.

## Plan

- [x] Inspect actual Steinberg ideal, augmentation-square inclusion, and nonzero escape.
- [x] Freeze exact conjecture before formalization.
- [x] Complete hostile internal/external collision audit.
- [x] Audit complete paper argument, including all infinite-generation issues.
- [x] Formalize the audited exact result; targeted build and final source/axiom checks pass.
- [ ] Global lint green; final global result recorded below.
- [x] Record consequence for arithmetic comparison and next nontrivial construction.

## Candidate paper argument

Work in `A=R/J`, write `U_q=[q]-1`. The relation for `x=1/n`, `1-x=(n-1)/n`, multiplied
by the unit `[n]^2`, gives `U_n^2=U_n U_(n-1)`. Induction implies `U_n^n=0` for every
positive integer `n`. For positive rational `a/b`,
`U_(a/b)=(U_a-U_b)[b]^(-1)` is nilpotent, since a finite sum of commuting nilpotents
is nilpotent. Thus every basis unit lies in `1+Nil(A)`.

In a commutative Q-algebra the finite nilpotent logarithm gives a group homomorphism
`L(q)=log([q])` into the additive nilradical. Every use involves a finitely generated
nilpotent ideal; no infinite convergence or global nilpotence is assumed. Since
`exp(L(q))-1=L(q)` times a unit with constant term one, the Steinberg relations imply
`L(x)L(1-x)=0` for `0<x<1`.

For `0<a<1`, apply this relation to `a^2`, use
`1-a^2=(1-a)(1+a)`, and subtract twice the relation for `a`. Division by two gives
`L(a)L(1+a)=0`. For `a>1`, apply this identity to `1/a`; it gives
`L(a)L(a+1)=L(a)^2`. The complementary pair `a/(a+1),1/(a+1)` gives
`L(a+1)^2=L(a)L(a+1)`. With `L(1)=0`, induction yields `L(n)^2=0` for all
positive integers. Expanding `L(nm)^2=0` then gives `2L(n)L(m)=0`. Rational
factorization and additivity give `L(q)L(r)=0` for all positive rationals `q,r`.
Therefore every `U_q=L(q)` and every `U_q U_r=0`. These products generate the image
of `I^2`, so `I^2 <= J`; the reverse inclusion is immediate. QED. The elementary proof
below is the proof formalized in Lean, with the corrected full-source carrier.

## Hostile tests / limitations

- The initial logarithm proof uses a commutative Q-algebra. The later finite ring proof
  needs only invertibility of two; no assertion is made when two is not invertible.
- Finite local nilpotence alone does not imply a globally nilpotent ideal, and
  `I^2=I^3` alone would not imply zero for this infinitely generated algebra. The argument
  deliberately uses individual finite logarithms and exact identities instead.
- This is stronger than the existing `J <= I^2` and nonmembership of the successor
  edge. It may still be classical or a routine consequence of known Steinberg-symbol
  theory; external novelty is not established.
- The logarithm here is a finite algebraic nilpotent polynomial, not a spectral, energy,
  positivity, or estimate-based argument.

## Stronger audit: an elementary proof avoids the logarithm

The same exact conclusion follows by finite ring identities. In `A=R/J`, put `T(q)=[q]`
and retain `U_q=T(q)-1`. Nilpotence of each `U_n` follows from the induction above, so
`T(n)+1=2+U_n` is a unit. Each positive rational is a quotient of positive integers;
therefore its `U_q` is nilpotent and `T(q)+1` is a unit as well.

For `0<a<1`, use the Steinberg relations at `a` and `a^2`. Factor
`T(a^2)-1=(T(a)-1)(T(a)+1)` and
`T(1-a^2)=T(1-a)T(1+a)`. After subtracting the relation at `a` multiplied by
`T(a)+1`, one obtains

`(T(a)+1) T(1-a) U_a U_(1+a)=0`.

Both initial factors are units; hence `U_a U_(1+a)=0`. For `a>1`, substitute `1/a`
in this identity and multiply by `T(a)^2`; this gives `U_a U_(a+1)=U_a^2`.
The complementary pair `a/(a+1),1/(a+1)` gives
`U_(a+1)^2=U_a U_(a+1)`. The latter identity also holds at `a=1` and implies
`U_2^2=0`. Induction now gives `U_n^2=0` for every positive integer.

For positive integers `n,m`, write `u=U_n`, `v=U_m`. Multiplicativity gives
`U_(nm)=u+v+uv`; its square, using `u^2=v^2=0`, is `2uv`. Thus `uv=0`.
Finally `U_(a/b)=(U_a-U_b)T(b)^(-1)` makes every rational product `U_q U_r` zero.
This proves `J=I^2` without analytic logarithms, completion, global nilpotence, or
an inference from `I^2=I^3`. Every identity involves finitely many elements.

## Actual source carrier correction

`CCMRationalAdelicScalingAction.lean` defines its label group as **all** nonzero rationals,
including negative ones. `RouteRMultiplierKOne.KummerGroupRing` is its complex group algebra.
Thus the literal source statement is **not** `deningerKummerSteinbergIdeal =
deningerKummerAugmentationIdeal^2`: the sign character annihilates all positive Steinberg
cells but detects `([-1]-1)^2`. That proposed unqualified transfer is false.

Write the full group as `{+1,-1} × Q_{>0}^*`, and let `I_+` be the ideal generated by
`[q]-1` for positive rational `q`. The corrected full-source statement is `J=I_+^2`.
Consequently the full quotient is two sign sectors, each a copy of the square-zero tangent
algebra. The actual positive successor escape belongs to either sector with its prime tangent
retained. This sign separation is required before connecting any geometric reflection.

## Primary-source audit so far

- Rogers--Schlichting, *On the presentation of the Grothendieck--Witt group of symmetric
  bilinear forms over local rings* (2024), Theorem 1.3, Remark 1.4, and Lemma 3.6:
  <https://link.springer.com/article/10.1007/s00209-024-03513-9>.
  Their presentation also imposes square-class/hyperbolic relations and uses all field units.
  It cannot be imported verbatim into the positive-only relation ideal. The Steinberg
  manipulations are classical parent machinery; no novelty claim is made for that machinery.
- Lurie's *Lecture 23: Formal Groups*, Examples 4--5:
  <https://people.math.harvard.edu/~lurie/205notes/Lecture23-Logarithm.pdf>.
  This supplies the classical finite nilpotent-logarithm parent of the first proof.
  The revised proof above avoids needing that formalization.
- Schlichting, *Euler class groups and the homology of elementary and special linear
  groups*, Definition 4.2 and Lemma 4.4:
  <https://warwick.ac.uk/fac/sci/maths/people/staff/marco_schlichting/research/eulerclassfinal.pdf>.
  This is adjacent graded Milnor--Witt machinery with relations on all field units. Its
  skew-commutativity identities do not by themselves identify our positive-only relation
  ideal. It reinforces the classical ancestry of the algebraic manipulations.

Final scope verdict: **corpus extension; scientific novelty unverified**. The exact
source-ideal classification is proved. Its elementary parent methods are classical.
The main RH comparison remains open.

### Admission and first Lean checkpoint

The exact-name/augmentation corpus search found only the inclusion and individual escape
nonmembership, not this ideal equality. The deep search returned unrelated proposed ingredients;
none was used. It reported `partial=false`, no unfinished stages, mixed compiler freshness,
and semantic coverage `not_measured`. Primary-source searches for the exact positive-rational
relation ideal found the adjacent Witt presentations above, not the claimed equality. This is
an audited corpus extension with **novelty unverified**, not a claim of literature priority.

The finite ring proof also works over any commutative coefficient ring in which `2` is a unit.
The original logarithm proof's Q-algebra restriction is unnecessary. This stronger coefficient
statement has the same dependency-closed ring proof; no characteristic-two assertion follows.

The natural-number core has passed scratch Lean audit in `/tmp/rh-steinberg-square-core.lean`:
for a multiplicative map on natural numbers with positive inputs mapping to units and the exact
scaled complementary relations, all products `(f(n)-1)(f(m)-1)` vanish. Its theorem uses only
`propext`, `Classical.choice`, and `Quot.sound`. The rational extension and corrected
actual-source equality were subsequently completed, with the negative sign retained.

The positive-rational extension and corrected actual-source equality subsequently passed
scratch Lean audit as well. The exact equality
`deningerKummerSteinbergIdeal_eq_positiveAugmentationIdeal_sq` has no unproved premise and
uses only `propext`, `Classical.choice`, and `Quot.sound`. Repository integration and the
strict sign-sector counterexample are also complete; final evidence follows.


## Final formalization and evidence

- `formal/GaloisForLFunctions/HTGeometry/PositiveRationalSteinbergSquare.lean` proves the
  general positive-rational character theorem over any commutative ring where two is a unit.
- `formal/GaloisForLFunctions/RHTower/Deninger/DeningerPositiveSteinbergSquare.lean` defines the actual
  positive augmentation ideal and proves
  `deningerKummerSteinbergIdeal_eq_positiveAugmentationIdeal_sq`. It also constructs the sign
  augmentation, proves the explicit negative-square counterexample, and concludes
  `deningerKummerSteinbergIdeal_lt_augmentationIdeal_sq`.
- Both leaves are wired into their respective umbrellas exactly once. No umbrella build ran.
- `lake --old build +GaloisForLFunctions.RHTower.Deninger.DeningerPositiveSteinbergSquare` exited zero
  and built both new leaves. Existing dependency warnings were replayed; neither new leaf
  produced a warning.
- Final sequential `lake env lean` checks of both repository source files exited zero with
  empty logs. The final axiom audit imports the built source leaf and checks all nine public
  declarations, transitively covering their private helpers. Every audit lists only
  `propext`, `Classical.choice`, and `Quot.sound`.
- Evidence: `/tmp/rh-steinberg-square-build-20261006.log`,
  `/tmp/rh-steinberg-square-generic-final-20261006.log`,
  `/tmp/rh-steinberg-square-source-final-20261006.log`, and
  `/tmp/rh-steinberg-square-axioms-final-20261006.log`.
- `scripts/formal_tools.py index` completed after the final source edits. Global lint outcome
  is recorded below; no claim of a clean full repository follows from the leaf audits.

The two-sign-sector square-zero-algebra interpretation is a paper corollary of the group
splitting and the ideal equality. No Lean algebra equivalence to that explicit product is
claimed. The exact ideal equality and strict inclusion are the formalized statements.

### Global lint result

`scripts/formal_tools.py lint --check-generated` exited one. Its complete error set is the
five pre-existing unwired HTGeometry modules `ApertureConeCalculus`, `ApertureConeWinding`,
`ApertureLogTranslation`, `ApertureOpenHistoryIdeal`, and `BoundaryCoronaCStarAlgebra`, plus
generated-file drift in `formal/LEAN_GAPS.md` and `formal/LEAN_OVERVIEW.md` in the shared tree.
No error names either new leaf. The final log is
`/tmp/rh-steinberg-square-lint-final-20261006.log`. Global lint is **not** green.

The superseded scratch implementations and API probes were removed after promotion. The
final axiom scratch, build/source/axiom/lint logs, and the separate successful suspension
scratch remain as evidence. No owned process remains pending.

## Research assessment and next construction

The suspension cycle clarified a missing hypothesis but rediscovered classical machinery.
This cycle strengthens the corpus's one-sided ideal inclusion to a complete relation-ideal
classification. No RH-bearing premise was discharged, and literature priority remains
unverified. No construction was declined on grounds of effort.

The next source-geometric comparison must retain the independent sign sector and positive
prime tangent directions, while identifying the actual terminal Xi class with a geometric
mark. The existing Tate boundary and static Steinberg quotient are now exactly distinguished;
one cannot silently substitute one for the other. Construct a source-defined extension or
moving-relation comparison carrying that tangent class, then prove its functional-equation
compatibility without assuming neutrality. The RH goal remains active.
