# Exact boundary energy of the infinite square-rate reader symbol

- **ID:** xi-theta-square-rate-boundary-energy
- **Stage:** 2-fully-proven
- **Type:** BRIDGE THEOREM / EXACT HARDY-BOUNDARY NORM, [PROVED]
- **Date:** 2026-07-10
- **Lean:** formal/GaloisForLFunctions/RHTower/XiThetaSquareRateBoundary.lean
- **Parent:** xi-theta-square-rate-reader-symbol.md

## Statement

Let

B(z)=sin(pi sqrt(z))/sinh(pi sqrt(z))

and let Q_n be the dimensionless exact reader symbol normalized at n squared. Let

R_n(s)=Q_n(s/pi)

be the physical-rate symbol interpolating the rates pi m squared. For every positive integer n,

integral_R |Q_n(it)|^2 dt = (4/pi) sinh(pi n)^2,             (1)

integral_R |R_n(it)|^2 dt = 4 sinh(pi n)^2.                  (2)

Consequently its boundary energy in the standard half-plane normalization is

(1/(2pi)) integral_R |R_n(it)|^2 dt
  = (2/pi) sinh(pi n)^2,                                    (3)

so the predicted normalized boundary norm is

sqrt(2/pi) sinh(pi n).                                      (4)

## Proof

### 1. The canonical quotient is inner on the punctured boundary

For real t not equal to zero, put w=pi sqrt(it). Since the square of sqrt(it) is it, its real and
imaginary parts have equal squares. Hence multiplication by i sends sqrt(it) either to its complex
conjugate or to the negative of its complex conjugate. The identities

sin(iw)=i sinh(w),

sin(conj(w))=conj(sin(w)),

and invariance of norm under conjugation and negation give

|sin(w)|=|sinh(w)|.

The denominator is nonzero: sqrt(it) has strictly positive real part when t is nonzero, whereas a
zero of sinh would force w times i to be an integral multiple of pi and hence to have zero imaginary
part. Therefore

|B(it)|=1                                                     (5)

away from the measure-zero origin.

### 2. Exact node slope

The node derivative computed in the parent theorem has norm

|B'(n^2)|=pi/(2n sinh(pi n)).                                 (6)

Using B(n squared)=0 and the difference-quotient definition of Q_n, (5) and (6) give the exact
Cauchy profile

|Q_n(it)|=
  2n sinh(pi n)/(pi sqrt(n^4+t^2)).                           (7)

### 3. Boundary integration

The elementary scaled Cauchy integral is

integral_R dt/(a^2+t^2)=pi/a,    a>0.                        (8)

Squaring (7) and applying (8) with a=n squared proves (1). The physical change of variables
t=pi u proves (2), and (3)-(4) follow immediately.

## Attack verdict

- [PROVED] The previously predicted `sinh(pi n)` condition number is the exact normalized boundary
  norm, not merely an asymptotic estimate.
- [DISCHARGED] No boundary-integrability or boundary-norm proposition remains for the explicit
  reader symbol.
- [NOT YET CLAIMED] Boundary energy alone supplies the full interior Hardy supremum or a source-side
  Paley-Wiener representative in the current formal library.

## Novelty and significance gate

The Cauchy integral and inner-function computation are classical, so the theorem is classified as a
bridge rather than new mathematics. Its significance is exact: it upgrades the project condition
number from a predicted imported value to a proved property of the concrete reader selected by the
completed theta source.

## Open core

[OPEN CORE] Prove analytic right-half-plane membership and uniform interior Hardy control for R_n,
then construct its L2 Paley-Wiener representative and compute the reflected balanced-Perron charge.

## Gates

- [x] 0 -> 1: explicit infinite physical-rate reader symbol constructed.
- [x] 1 -> 2: punctured-boundary inner identity and exact boundary energy proved.
- [x] 2 -> 3: boundary profile and both scaled and physical energies formalized.
- [ ] 3 -> 4: requires interior Hardy control, Paley-Wiener transport, and reflected charge.
