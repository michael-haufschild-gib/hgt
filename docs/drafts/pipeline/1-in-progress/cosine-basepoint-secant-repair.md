# Cosine basepoint repair and secant projection

- **ID:** cosine-basepoint-secant-repair
- **Stage:** 1-in-progress
- **Type:** CANDIDATE; no significant novelty claim
- **Parent:** labeled-lattice-section-periodicity.md; ../3-formalized/rational-cosine-diagonal-repair.md

## Exact candidate and open core

Keep T from `LabeledCosineDescent`, a=T(0), and define

    s(w)=(T(w)+T(-w)-2a)/2, t(w)=(T(w)-T(-w))/2,
    V(w)=(t(w)+i*s(w))/(t(w)-i*s(w)).

Interpret V as a meromorphic map, cancelling common zeros. This is projection from the diagonal basepoint (a,a), followed by a Cayley transformation. On the generic diagonal t=0 it takes -1; at w=0 the tangent is s=0 and the cancelled value is +1. Both required reflections hold: s is even, t odd, and both commute with conjugation.

**Conjecture E [OPEN CORE]:** This V has a genuine nonreal holomorphic 1-fiber. A stronger candidate asserts infinitely many such fibers. Equivalently, find nonreal w with T(w)+T(-w)=2a and T(w)!=T(-w), retaining noncancellation. Do not infer E from the regular-diagonal theorem, whose hypothesis fails here.

## Dependency-closed local survivor [PROVED HERE]

For any analytic source f with f'(0)!=0, let b(w) be its analytic divided difference `(f(w)-f(0))/w`, filled at zero by f'(0). Then

    t(w)=w*(b(w)+b(-w))/2,
    s(w)=w*(b(w)-b(-w))/2.

Cancelling w yields analytic numerator/denominator near zero; their common value is f'(0)!=0. Hence V extends holomorphically with V(0)=1. Its derivative is `i*f''(0)/f'(0)` when the second derivative is supplied. No assertion of simple local degree is made without proving f''(0)!=0. The generic diagonal sign therefore cannot determine the filled basepoint value. This local statement is classical blowup/tangent geometry, not a new field.

For the specific T, the divided difference b is entire: away from zero it is an ordinary quotient, and at zero its analytic series is the shifted series of T. Its reflected even/odd parts give entire coordinates `N=b(w)+b(-w)+i*(b(w)-b(-w))` and `D=b(w)+b(-w)-i*(b(w)-b(-w))`. Reflection swaps N,D; conjugation conjugates and swaps them. The already-proved source jet gives T'(0)!=0, so N(0)=D(0)=2T'(0)!=0. These identities also certify that the quotient is nonconstant: on every diagonal point w_n from Theorem D, the cosine deck identity proves T(w_n)!=T(0) (otherwise its nonzero imaginary lift would equal a real lift modulo cosine deck transformations). Thus b(w_n)!=0, b(-w_n)=-b(w_n), D(w_n)=-2i*b(w_n)!=0, and V(w_n)=-1. Since the w_n are distinct and nonreal, the holomorphic -1-fiber is infinite. This proves that removable normalization plus both reflections does not select the positive generic diagonal sign. It does not refute an extension of D's final conclusion: Conjecture E could still be true.

## Failed short attacks and retained geometry

- The earlier real-coefficient quotient has the wrong conjugation law. Adding i as above repairs that defect; this candidate must be tested further.
- The cosine coincidence sequence gives V=-1, an unmarked value, so it does not prove E.
- An intermediate-value argument along the imaginary axis would compare `cos(x)*cosh(y)` with a while `x²-y²=(pi/9)²`. Its proposed sign comparisons use positivity/bounds; do not use this as the requested mechanism or rename it topology.
- Set u²=(4*pi²/27)*(w+1/12), v²=(4*pi²/27)*(-w+1/12). Then u²+v²=2*(pi/9)². The 1-fiber equation is `cos(u)+cos(v)=2a`. With X=exp(i*u), Y=exp(i*v), it lies on `X+X^-1+Y+Y^-1=4a`. Its logarithmic covering retains the quadratic equation. An intersection argument on that covering could address E, but none is established.

## Corpus and literature audit

Deep query `cosine diagonal basepoint reciprocal` returned 20 candidates and 20 source arguments, all inspected; the proposed cosine-diagonal recurrence ingredient is unrelated. `partial=false`, no errors, compiler freshness incomplete, slightly older coverage snapshot. No exact hit; this is not a novelty certificate.

The Laurent elliptic family is classical: [Juyal–Moody, Integers 21 (2021), pp. 1–3](https://tsapps.nist.gov/publication/get_pdf.cfm?pub_id=931852) gives the family `X+X^-1+Y+Y^-1+q=0`, its Weierstrass form, and nonsingularity for q!=0,+4,-4. We use only this geometric parent, not its Mahler-measure or arithmetic-rank results. Current task is the specific logarithmic-cover intersection, not an unresolved conjecture from that paper.

**Hostile verdict:** local cancellation is REDISCOVERED; exact source specialization is BRIDGE; Conjecture E remains open. Even E would exclude only this repair, not prove C2-P or RH.

## Formal boundary certificate, 2026-10-07

`CosineBasepointRepair.lean` now checks directly without warnings and its targeted build passes (3402 jobs). `scaled_coordinates` identifies the entire divided-difference pair with the literal secant quotient after multiplying both coordinates by w. `basepoint_escape` proves V(0)=1, holomorphy at zero, both reflection identities, and infinitely many genuine nonreal holomorphic -1-points, with no assumptions. Three axiom checks report only `propext`, `Classical.choice`, `Quot.sound`. These are properties of this concrete model; the marked 1-fiber and C2-P are not certified.

Final global lint reports the same five unrelated unreachable HTGeometry modules (ApertureConeCalculus, ApertureConeWinding, ApertureLogTranslation, ApertureOpenHistoryIdeal, BoundaryCoronaCStarAlgebra). No owned repair leaf is flagged; global lint is not clean.

## Next geometric attack

An exact no-escape mechanism is now developed in [logarithmic toric boundary card](logarithmic-toric-no-asymptotic-values.md). It uses the four boundary corners of the Laurent curve and the nonreal points at infinity of the lifted quadratic curve. The full specialization to E, including infinite fibers and the finite real part of each fiber, is recorded there for hostile audit and formalization. The card remains in progress: a paper argument is not a Lean proof, and a general boundary hypothesis must not be silently assumed.
