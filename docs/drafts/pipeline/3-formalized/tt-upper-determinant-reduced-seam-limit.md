# Positive source limit of the reduced upper determinant

- **ID:** TT-C117-REDUCED-SEAM
- **Stage:** 3-formalized
- **Depends on:** C116 exact seam-power factor; C113 scaled seam signs and
  complete upper quadratic identity; actual source ODE.
- **Lean status:** complete. Four production leaves and all 25 public
  declarations passed direct `lake --old env lean` audits with only
  propext, Classical.choice and Quot.sound. RHTower umbrella wired.

Production: `ThetaCuspRatioComplexSourceSlopes`,
`ThetaCuspRatioUpperCenterComplexIdentity`, `ThetaCuspRatioReducedSeamIdentity`,
and `ThetaCuspRatioReducedSeamLimit`. Capstones:
`actual_reduced_determinant_seam_complex`,
`actual_reduced_upper_determinant_tendsto_seam`, and
`actual_upper_determinant_pos_near_seam`.

## Exact statement

Let c=10^13, Q be the complete upper determinant, and R its exact polynomial
quotient by U^26 from C116. Put k0=k(0),

`lambda = 6^30*(k0-1/6)^7/(9*k0)`

and `delta = scaledUpperA(0)*scaledD(0)-scaledB(0)^2`.
Then, along positive actual centers approaching zero,

`Re R(actualSquarePoint x) -> lambda^2 * delta > 0`.

This identifies a nonzero positive leading source coefficient after the
exact common power is removed. It does not establish the intervening
compact sign.

## Paper proof

The existing normalized cofactor value identities are complex equalities
to casts of real functions. Differentiate them and use uniqueness of the
complex derivative of a real-valued function. This upgrades the source
slope identities from their real parts to complex equalities: each
normalized slope equals the cast of the corresponding real derivative.
The same applies to the center drive. The existing complete weighted
incidence and upper-center difference therefore give, without taking real
parts first,

`eval Qupper(c,eta) = endpointNormalizer(x) * x *
  (scaledUpperA(x)+2*scaledB(x)*eta+scaledD(x)*eta^2)`

as a cast into C, for every real eta and x>0. Exact polarization at eta
0,1,-1 recovers the three complex coefficients. Consequently

`eval Q = (endpointNormalizer(x)*x)^2 *
  (scaledUpperA(x)*scaledD(x)-scaledB(x)^2)`.

Divide the C116 identity Q=U^26 R by u^52, valid since u>0. With the
existing endpointNormalizer this gives

`Re R(actualSquarePoint x) =
  (6^30*(k(x)-1/6)^7*(x/u(x)))^2 *
  (scaledUpperA(x)*scaledD(x)-scaledB(x)^2)`.

C113 supplies continuity of the three divided slopes at zero and delta>0.
The source ODE gives u(0)=0 and u'(0)=9*k0>0. Therefore x/u(x) tends to
1/(9*k0) along positive centers; k is continuous there. Taking limits in
the exact identity proves the stated limit and strict positivity.

No numerical sample or estimate of a Taylor remainder is used. The source
moments, load, center-drive correction, and border square all remain in the
identity. Polynomial evaluation at actualSquarePoint(0) is not substituted
for the right-hand source limit: J/u has a removable, generally nonzero
limit even though division at zero is totalized in Lean.

## Next hard target

Use this positive reduced seam value and the proved positive terminal
normalization as boundary data for the full compact sign problem. The
candidate differential sign `K*squareLie R-34*squareField(K)*R <= 0`
still requires a complete actual-source proof.
