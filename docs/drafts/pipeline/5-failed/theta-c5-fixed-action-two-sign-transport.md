# Fixed-action two-sign transport for completed-theta C5

- **ID:** theta-c5-fixed-action-two-sign-transport
- **Stage:** 5-failed
- **Type:** NO-GO + SHARP POSITIVE SURVIVOR
- **Source route:** CLG/TTF completed-theta C5 gate
- **Status:** unconditionally refuted and formalized in Lean

## Proposed RH chain

The corpus action-velocity normal form rewrites completed-theta C5 as a first-order barrier
`K(q,v,v_q)`.  On fixed-action levels, if `h=partial_u v|_q`, then

`partial_u K|_q = 5 partial_q(vh) - (14+10v+8v/r)h`.

The proposed sufficient chamber `h<=0` and `partial_q(vh)>=0` would imply seam minimization,
global C5 nonnegativity, the rank-four Laguerre--Pólya/total-frequency gate, and then the recorded
CLG/TTF RH endpoint.

## Exact obstruction

Let `ell=log(thetaCuspFullSource)` and

`A=-ell''(0)`, `B=-ell''''(0)`, `C=-ell''''''(0)`.

Parity expansion of the exact seam transport gives first nonzero coefficient
`(A*C-2*B^2)/(6*A)`.  New self-dual modular-ODE elimination identifies the numerator with a
degree-eight polynomial in `X=(pi*theta_3(i)^4)^2`.  After shifting by the corpus threshold
`X=191/10+y`, its constant and every `y^j` coefficient are strictly negative.  Bell transfer
therefore proves, without premises,

`A*C < 2*B^2`.

Hence the companion forward-orientation needed by the two-sign transport decomposition fails at
the modular seam.  This specific fixed-action proof chain is dead.

## Sharp survivor

The strict reverse logarithmic law `A*C<2*B^2` is source-specific, exact, and new.  Its raw-source
form is

`f0^2*f2*f6 - 3*f0*f2^2*f4 + 12*f2^4 - 2*f0^2*f4^2 < 0`.

This classifies the first transverse action-velocity seam orientation.  It does not refute C5;
it redirects the proof to the direct Gaussian-deviation three-zone reduction, where the hard
survivor is accumulated-action/jet coupling rather than fixed-action monotonicity.

## Lean certificate

- `GaloisForLFunctions.HTGeometry.PolynomialODEJetClosure`
- `GaloisForLFunctions.RHTower.PrimeArchThetaModularDifferentialClosure`
- `GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspActionVelocitySeamLogMinorNoGo`
- Capstones:
  `thetaCuspActionVelocitySeam_curvature_sixth_lt_two_fourth_sq`,
  `not_thetaCuspActionVelocitySeamLogMinor_nonneg`
- Direct Lean checks: PASS
- Targeted builds: PASS
- Axioms: `propext`, `Classical.choice`, `Quot.sound` only
- Formal lint: new module is reachable and contains no forbidden declarations; repository lint
  remains red only from unrelated concurrently-added unreachable modules.

`NO POSITIVE SALVAGE FOUND` for the proposed forward two-sign decomposition beyond the exact
reverse seam law above.
