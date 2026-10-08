# Candidate: does the polar cone already fix the full pole completion?

Status: OPEN diagnostic, DEFERRED after the cycle21 utility audit. The exact
claim survives preliminary attack, but generic extension machinery supplies
neither its arithmetic core nor a WP02 producer. No theorem, scientific-novelty
claim, cone nonemptiness or WP02 lower estimate supplied.

## Exact incompatible assertions

C-lift:

    forall lambda : Nat -> Real,
      RHTower.WeilPositive lambda -> RHTower.WeilPositiveFull lambda.

C-defect: there exist one real integer weight lambda and one actual complex
compact C2 test f such that lambda is polar-positive at EVERY aperture but

    Re(weilFullFunctional lambda (EF.weilTest f f)) < 0.

These concern the same coefficient sequence and the fixed pole coefficient
one in `weilFullFunctional`. Do not replace the conclusion by existence of
some positive extension, another sequence, or an adjustable pole term.

The proposed next attack is C-lift. It would justify transporting the
corpus's genuinely stronger full-cone bounds to any polar candidate arising
in WP02's dual problem. It would not establish that a candidate exists, or
that the exposing value is attained. Reject the route on utility grounds if
it produces only a generic conditional extension theorem.

## Exact frontier and hostile audit

- `WeilFullConeExposedPoint.weilPositive_of_weilPositiveFull` proves the
  reverse direction only.
- `WeilPrimitiveSetMeanSquare` already gives polar mean-square control;
  this must not be advertised as a benefit unique to C-lift.
- The full-cone Herglotz theorem takes `WeilPositiveFull` as input. The pole
  residue theorem additionally assumes a decomposition and residue limit.
  Neither may be used to prove its own missing input.
- Polar tests kill both imaginary half-poles. For general Hermitian
  functionals, positivity on this codimension-two ideal does not imply
  positivity everywhere. The exact integer-supported arithmetic and gamma
  term must do additional work. An abstract positive-extension theorem does
  not specify the actual pole coefficient.
- No Euler product, meromorphic source, discrete/integer spectral mass,
  temperedness of the full functional, RH or prime-number theorem for lambda
  is available as a free premise.

## A representation to attack, not an established source theorem

Let W_lambda denote the even real distribution defined on smooth compact
tests by the actual full functional, and P=D^2-1/4. Since P maps compact
smooth sources to polar ones, polar positivity makes P^2 W_lambda positive
definite. A Bochner--Schwartz representation would give a positive tempered
measure for this differentiated distribution. Dividing on real frequency
by the strictly positive multiplier (tau^2+1/4)^2 gives a canonical positive
tempered distribution W_0. The homogeneous ODE leaves

    W_lambda - W_0 = a*cosh(u/2) + b*u*sinh(u/2)

for real a,b, provided all distribution and parity steps are established.
This finite-dimensional ambiguity is invisible on the polar ideal.

[OPEN CORE] Prove from the actual gamma term and exact integer atom support
that both coefficients vanish, or construct a literal polar-positive weight
for which they do not. In particular, an exponential growth bound is NOT
temperedness. The preceding representation is classical infrastructure;
eliminating the actual arithmetic remainder is the candidate new content.

External parents inspected: Jorgensen--Tian,
[Positive definite functions vs distributions](https://arxiv.org/pdf/1712.07264),
and Chung--Kim,
[Conditionally Positive Definite Hyperfunctions](https://ems.press/journals/prims/articles/2290).
The former's representation theorem and the latter's abstract do not fix
these arithmetic coefficients. No claim of their theorem's applicability
to W_lambda without the required distribution construction is made.

## Cycle21 utility decision

The source audit did not eliminate either remainder coefficient. The modified
completion residue theorem in `WeilWorkPBAPCriticalResidue` assumes positivity
on all smooth compact sources. Its coefficient boundary `b <= a` in
`WeilWorkPBAPCriticalBoundary` therefore cannot supply polar-to-full admission.
Even obtaining that boundary would not identify the actual pole coefficient.
`WeilFractionalMassAtomicRigidity` requires a spectral representation with
integer masses outside a finite exceptional set; polar positivity does not
provide that hypothesis. These are unavailable parents, not failed theorems.

The abstract obstruction is concrete: the even distribution `cosh(u/2)`
vanishes on autocorrelations of polar sources, while its value on an odd real
compact source with nonzero half-pole moment is negative. Thus a generic
positive-extension argument cannot identify the actual completion. This is
classical codimension/ODE information, not new scientific knowledge.

No literal integer-weight counterexample to C-lift was constructed. Do not
mark C-lift FALSE, use it as a premise, or claim that it creates a cone point.
Return to the all-family signed estimate in
`VANISHING-MASS-DEFECT-CONJECTURE.md`. Reopen this diagnostic only when an
actual arithmetic estimate addresses the remainder, rather than when more
distribution infrastructure becomes available.
