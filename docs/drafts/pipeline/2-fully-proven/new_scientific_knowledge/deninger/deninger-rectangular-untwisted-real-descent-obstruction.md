# Rectangular untwisted real-descent obstruction

- **ID:** `deninger-rectangular-untwisted-real-descent-obstruction`
- **Stage:** 2-fully-proven
- **Type:** NO-GO THEOREM WITH POSITIVE SURVIVOR
- **Parent:** `deninger-kahler-riemann-arithmetic-leaf-realization`
- **Source:** `deninger-rectangular-quaternionic-hodge`
- **Statement:** the untwisted rectangular power descent preserves both
  quaternionic Hodge parity and an ordinary real structure, so it cannot
  be Deninger's generic arithmetic coefficient.

## Theorem

For \(r,q>0\), on \(V_r=\mathbb C^2\) put
\[
 \kappa(z,w)=(\bar z,\bar w),\qquad
 J_r(z,w)=(-r\bar w,\bar z/r),
 \qquad
 U_q(z,w)=q^{-1/2}(qz,w).
\]
Then
\[
 \kappa^2=1,\qquad J_r^2=-1,\qquad
 U_q\kappa=\kappa U_q,\qquad
 U_qJ_r=J_{qr}U_q.
\]
Consequently the quotient of the moving rectangular family by the
untwisted \(\mathbb Q_{>0}\)-action carries both:

1. a quaternionic anti-linear structure \(J^2=-1\);
2. an anti-linear real structure \(\kappa^2=1\).

Thus the untwisted quotient is the complexification of a real local
system.  This is not excluded for the isolated \(\mathbb Q\) object,
which still has the required odd \(J^2=-1\) structure.  Deninger's
no-real-coefficients theorem excludes it only as a real-valued
\(H^1\) functorial over all number fields.

## Proof

Both assertions on squares follow by direct substitution.  Since
\(U_q\) has real diagonal coefficients, coordinatewise conjugation
commutes with it.  The rectangular identity
\[
 \operatorname{diag}(q,1)J_r
 =
 J_{qr}\operatorname{diag}(q,1)
\]
is unchanged by the real scalar \(q^{-1/2}\).  These identities are
equivariant, hence descend to the quotient.

## Strongest positive survivor

The local rectangular positive metric and quaternionic operator remain
valid.  What fails is only untwisted global descent.  A viable
coefficient must replace the real transition cocycle by genuinely
quaternionic transition data which:

1. preserves the positive Hermitian form and \(J\);
2. has no compatible anti-linear involution of square \(+1\);
3. is defined on the actual rational-Witt finite-correspondence
   groupoid, before derived sections;
4. preserves the Poisson differential and arithmetic cup product.

An honest constant representation of the abelian power semigroup is
not enough: its rectangular realization retains \(\kappa\).  The
minimal surviving candidates are a nonconstant groupoid cocycle or a
projective action arising from the selective Steinberg
bar--residue/central-extension data.  Full
\(\mathbb A^1\)-localization remains forbidden by
`deninger-a1-localized-rational-witt-coefficient`.

## Lean status

The four local identities are stated without axioms in
`DeningerArithmeticRectangularQuaternionicHodge.lean`.  Direct Lean
verification is deferred until concurrent external Lean saturation
clears.

## Verdict

`[PAPER-PROVED]`.  Untwisted real descent is insufficient for the
all-number-fields theory.  Positive local Hodge atom survives and is
admissible on the \(\mathbb Q\)-to-RH path; genuine quaternionic
groupoid twist is a separate functorial-extension gate.

## Log

- 2026-07-27 — Extracted the real involution preserved by every
  real-centered rectangular power map and isolated the exact global
  twist obligation.
