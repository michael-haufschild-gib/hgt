# HB: actual projected Einstein current and QNM pairing

Chain: literal theta-cusp source → Xi occurrence → retained spin-two source →
physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.
RH remains unproved. The frontier map is read-only.

## Closed local action attachment

Three exact leaves are checked and audited:

- `ThetaCuspHawkingBMModeActionReconstruction`: actual two-jets of separated
  fields, original radius reconstruction, full mixed Einstein current.
- `ThetaCuspHawkingBMPhysicalModeAction`: actual causal projection, original
  coexact Eisenstein covector, homogeneous original left stream, complete
  forced right stream, finite-interval Einstein flux including both contacts.
- `ThetaCuspHawkingBMPhysicalTimeActionContinuation`: actual temporal current
  continuation, exact fundamental residue, analytic Laurent remainder and
  transfer of local field-residue nonvanishing.

At an interior original tortoise point x<0 set R=-coth(x),
lambda=u^2-1/4, u=physicalAngularParameter(r). Let f be the complete physical
projected response, g either original radial mode, and F the complete projected
source. All three cutoff corrections remain in F. Reconstruct the stream
coefficients as Rf and Rg with time frequencies w and -w, and retain the actual
coexact angular covector J. Write N=sum_j J_j^2, a complex bilinear square.
The original volume-weighted Einstein current at time zero is

```
A^0 = [-2w(lambda-2)fg/(R^2-1) - w R^2 g F/(R^2-1)^2] N,
A^1 = [-(lambda-2)(g'f-gf') - C] N,
A^2 = A^3 = 0,
C = [Rg + R^2 g'/(R^2-1)] F.
```

Every derivative slot is an actual field derivative. The angular equation is
derived from the literal Eisenstein covector. The right stream master is
`-R^3 F J/(R^2-1)` and the left stream master is zero. No radial ODE or angular
eigen-equation is supplied as an extra physical assumption. In the causal
Green band the reconstructed field is the radius lift of the actual causal
transform's physical projection, almost everywhere in the original measure.

For interior s≤t<0 the checked Einstein flux identity is

```
A^1(t)-A^1(s) = [-(lambda-2) integral_s^t gF - (C(t)-C(s))] N.
```

This identifies a projected mixed sector. Full angular reconstruction,
independent SS/VV sectors, retarded/advanced Peierls identification and
integrated QNM endpoint limits remain open.

## Closed local temporal QNM transfer

The temporal current has a proved meromorphic continuation from the actual
physical band. Its exact QNM residue is

```
-2 w0 (lambda-2) g(w0,x) Res(f)(x) N/(R^2-1).
```

Proof mechanism: the source-rate pole is distinct from either fundamental
frequency; all three principal cutoff responses are analytic there. Their
finite angular decomposition therefore makes the complete F analytic there.
The original radial mode is analytic there. Consequently the retained
source contact is regular and contributes zero residue. The existing exact
field-residue limit then transfers to the actual temporal Einstein current.
All three leaves pass scratch checks and exact leaf audits. The current has
an analytic Laurent remainder. At every interior point its radial
multiplier is nonzero, so a nonzero field residue and nonzero angular
bilinear square imply a nonzero local Einstein temporal residue.

The fundamental mode is
`Psi(x)=z^(w0/2) sqrt(1-z)`, where `z=sech(x)^2`, not `exp(2x)`.
Both original radial normalizations agree at resonance. The temporal
coefficient therefore carries Psi squared. Its radial integral, if admitted
with the original horizon finite part, is a beta integral
`(1/2) B(w0,3/2)`. That endpoint identification and integration have not been
proved here. They must follow from the actual current, with its original
contacts, rather than define a new pairing.

## Other unresolved source factors

The source-moment substitution produces an incomplete beta integral; it does
not supply a nonvanishing proof. Source transposition retains the onset
remainder and horizon finite part. The actual angular source, radial source
moment, fixed onset, angular integration, and Hawking-clock extinction remain
substantive open problems. No numerical experiments are used.

The proposed radial norm has an explicit subtraction requiring no guessed
regularization constant. For nonreal w with Re(w)>-2, its candidate is

```
I(w) = 1/w - 1/(2(w+1))
       - (1/2) integral_0^1 z^(w+1)/(1+sqrt(1-z))^2 dz.
```

The algebraic identity
`sqrt(1-z) = 1-z/2-z^2/(2(1+sqrt(1-z))^2)`
identifies these as the first two actual horizon terms. The remainder has
absolute convergence because Re(w+1)>-1. The proposed next proof is
`w(w+1) I(w) = Gamma(w+2) Gamma(3/2)/Gamma(w+3/2)`, first in the ordinary
convergence half-plane, then by analytic continuation of both cleared sides.
This would give nonvanishing of this radial norm at every nonreal fundamental
frequency. The original-current cutoff limit and global angular pairing
must still be identified; this candidate is not yet a formal theorem.
