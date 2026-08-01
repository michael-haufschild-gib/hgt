# Rectangular untwisted real-descent obstruction

- **ID:** `deninger-rectangular-untwisted-real-descent-obstruction`
- **Stage:** 3-formalized
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

The four local identities are formalized in
`DeningerArithmeticRectangularQuaternionicHodge.lean` and verified:

- `κ² = 1` is `deningerRectangularConjugation_sq`;
- `J² = -1` is `deningerRectangularQuaternionicHodge_sq`, with the
  complex-linear form `deningerRectangularComplexJ_sq`;
- `U_q κ = κ U_q` is
  `deningerRectangularCenteredScale_intertwines_conjugation`;
- `U_q J_r = J_{qr} U_q` is
  `deningerRectangularCenteredScale_intertwines_hodge`.

The card's `U_q(z,w) = q^{-1/2}(qz,w)` appears as
`deningerRectangularCenteredScale a q`, the real rescaling by `a`
composed with the dilation by `q`; the unitary normalization is
`a² q = 1`.  The two intertwining identities are proved for every real
`a`, so they are slightly more general than the card.  The positive
local metric survives as `deningerRectangularComplexEnergy_pos` and its
weight-one law, which is the card's "strongest positive survivor".

### Verification

- Direct command: `lake env lean` on the module — passes with no
  errors and no warnings.
- Cached module build: completes.
- Scratch `#print axioms` on the four identities and the positivity
  theorem: only `propext`, `Classical.choice`, `Quot.sound`.
- Imported by the `GaloisForLFunctions.RHTower` umbrella.

## Gates

- [x] 0 → 1 in-progress: obstruction isolated
- [x] 1 → 2 fully-proven: the four identities and the descent verdict
- [x] 2 → 3 formalized: all four identities, with cached build and
      axiom audit
- [ ] 3 → 4 publication-ready: the genuinely quaternionic transition
      data that would replace the real cocycle is a separate
      functorial-extension gate, which this card identifies rather
      than constructs

## Verdict

`[PAPER-PROVED]`.  Untwisted real descent is insufficient for the
all-number-fields theory.  Positive local Hodge atom survives and is
admissible on the \(\mathbb Q\)-to-RH path; genuine quaternionic
groupoid twist is a separate functorial-extension gate.

## Log

- 2026-07-27 — Extracted the real involution preserved by every
  real-centered rectangular power map and isolated the exact global
  twist obligation.
- 2026-08-01 — Closed the stage-3 gate: verified the four Lean
  identities against the card, then ran the direct check, the cached
  build and the declaration-axiom audit.  The deferred verification
  note is superseded.  No new Lean was needed.
