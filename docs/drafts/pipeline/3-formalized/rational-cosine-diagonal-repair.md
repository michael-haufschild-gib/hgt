# Rational reciprocal repairs and the reflection diagonal

- **ID:** rational-cosine-diagonal-repair
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), BRIDGE; significant novelty unverified
- **Parent:** ../1-in-progress/labeled-lattice-section-periodicity.md; ../5-failed/cosine-reciprocal-symmetrization.md

## Exact candidate

Keep the entire T from `CosineReflectionCoincidence.lean`, and write a=T(0). Let P,Q in C[X,Y] satisfy the polynomial identity

    P(X,Y)*P(Y,X) = Q(X,Y)*Q(Y,X),

and require P(a,a)=Q(a,a)!=0. Define the meromorphic pullback

    V(w)=P(T(w),T(-w))/Q(T(w),T(-w)).

**Theorem D [LEAN-PROVED]:** V has infinitely many off-real points where it is holomorphic and equals 1. Thus no such rational repair can satisfy the labeled-fiber requirements of C2-P.

The regularity condition Q(a,a)!=0 is essential to the proposed scope. Do not replace it with the weaker statement that the pullback has a removable value at w=0. Also do not omit the positive diagonal sign selected by P(a,a)=Q(a,a). The negative sign is a live escape case, and C2-P permits V(0)=-1.

## Paper mechanism and first audit

Set p(X)=P(X,X), q(X)=Q(X,X). The norm identity gives `(p-q)*(p+q)=0`. Since C[X] is a domain, p=q or p=-q. Evaluation at a and q(a)!=0 excludes the second case, so p=q and q is a nonzero polynomial.

For each integer n>=1 put r_n=sqrt(81*n²-1), w_n=3*i*n*r_n/2, and u_n=pi*n+i*pi*r_n/9. Exact square identities give T(w_n)=cos(u_n)=T(-w_n). Every w_n is nonreal: r_n=0 would imply 81*n²=1, impossible already modulo three. If cos(u_n)=cos(u_m), the cosine identity gives equality up to sign of the imaginary parts. Squaring gives r_n²=r_m², hence n²=m² and n=m. Thus the diagonal values x_n=T(w_n) are pairwise distinct.

The zero set of a nonzero polynomial q is finite. Consequently q(x_n)!=0 for infinitely many n. At each such n, the numerator equals the same nonzero value and V(w_n)=1; the denominator is nonzero locally, so V is holomorphic. This completes the proposed proof using exact cover geometry, an integral-domain factorization, and finiteness of a polynomial zero set. No asymptotic estimate or numerical experiment is involved.

**[LEAN-PROVED]** `CosineInfiniteDiagonal.source_point_injective` and `infinite_coincidences_avoiding` certify the collision geometry; `RationalCosineDiagonalRepair.infinite_off_real_one_fiber` certifies the complete theorem, including holomorphy and nonzero denominators. Lean exposes the harmless strengthening that the regular normalizing diagonal point a can be arbitrary; the same paper factorization proves this stronger statement. No scientific novelty or RH result is claimed.

## Escape through a diagonal basepoint

The distinction is concrete. For a rational expression H=P/P_swap, a zero of order k in P(T(w),T(-w)) at w=0 gives the removable value `(-1)^k` for H there. An overall sign changes this to `epsilon*(-1)^k`. Thus the sign on the generic diagonal and the sign of the pulled-back value at 0 can differ after cancellation.

For example, `-(T(w)-a)/(T(-w)-a)` has negative generic diagonal sign but removable value +1 at 0, since T'(0)!=0. It is outside Theorem D, but its real coefficients give the wrong conjugation law. A more serious candidate is `-(T(w)-a+i*(T(-w)-a))/(T(-w)-a+i*(T(w)-a))`. Equivalently, set s=(T(w)+T(-w)-2a)/2 and t=(T(w)-T(-w))/2, and take `(t+i*s)/(t-i*s)`. This satisfies both reflections meromorphically, has negative generic diagonal sign and removable value +1 at 0. Its complete marked fibers remain unaudited. See [active basepoint card](../1-in-progress/cosine-basepoint-secant-repair.md).

## Current audit state

Deep query `rational symmetric diagonal reciprocal polynomial infinite coincidence` completed with `partial=false`, no errors; compiler freshness incomplete and coverage snapshot slightly older. All candidate/source statements and the proposed ingredient set were inspected. The useful parent hits concern symmetric rational fields and permutation actions; none supplies this exact pullback obstruction. External broad phrase searches mostly returned unrelated generating-function diagonal literature. A targeted Hilbert-90 search located the classical norm-one parent ([Elkies, Math 250 notes, Theorem 4.28](https://people.math.harvard.edu/~elkies/M250.01/index.html)); no external theorem is needed beyond the elementary diagonal factorization proved above.

**Hostile verdict BRIDGE.** The norm-one algebra and finite polynomial zero set are classical. The exact infinite collision family supplies the concrete application. Significant novelty remains unverified; this should not consume the research programme as a substitute for full C2-P. Finish its certificate, then attack the negative-sign/basepoint escape directly.

## Verification, 2026-10-07

- Direct checks of both leaves passed without warnings; targeted builds `lake build --old +GaloisForLFunctions.HTGeometry.CosineInfiniteDiagonal` and `+GaloisForLFunctions.HTGeometry.RationalCosineDiagonalRepair` passed (3401/3403 jobs).
- Four theorem axiom checks report only `propext`, `Classical.choice`, `Quot.sound`.
- Final direct `CosineInfiniteDiagonal.lean` audit also passes. Global lint retains five unrelated unreachable-module errors; no owned leaf is flagged.
- The source uses elementary sign facts to choose real square roots and identify positive integer indices. The obstruction itself is exact cover geometry and polynomial zero-set finiteness, with no positivity criterion, analytic bounds, numerical experiments or spectral mechanism.
- The implementation query returned unrelated semantic hits; no exact lexical hit, `partial=false`, compiler freshness incomplete, coverage snapshot older. Applicability was established by local mathlib source inspection and a successful scratch Lean name check.
