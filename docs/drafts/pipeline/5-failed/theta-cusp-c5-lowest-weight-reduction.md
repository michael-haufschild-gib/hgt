# Theta-Cusp C5 Lowest-Weight Reduction

- **ID:** CLG-TTF-C5-lowest-weight-reduction
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Failure theorem:**
  `modularThetaSourcePositiveC5ExactCompletedSeamOrientation_not_lowestWeight`

## Failed proposal

Hidden source `sl₂` makes adapted coordinates `r=U+3B` and
`k=Q+3/8-(3/8)B²` lowering-invariant, while `sl₂F=-∂b`. Proposed identity

`sl₂F(Ω_clear)=0`

would remove `b`; seam vanishing would then force `Ω_clear=r*P(r,k)`. Positivity of two-variable
factor on physical `(r,k)` trajectory would close compact C5 incidence and RH chain through
direct-J seam orientation and CLG/TTF or Weil positivity.

## Exact obstruction

At zero-scale seam, physical source field equals `sl₂F`. C5 orientation is zero, yet covariant Lie
law reduces its derivative to nonzero fixed-action C5 constant charge. Lean proves lowering
derivative is strictly positive there. Thus orientation is not lowering-invariant.

## Positive survivor

Exact anomaly is

`eval(sl₂F(Ω_clear)) = (-3/8)^5 * modularThetaC5FixedActionSeamPolynomial(0) > 0`.

It identifies irreducible clock information: compact first-contact proof must evolve `b` or carry
equivalent C5 charge in a new dynamical invariant. Eliminating clock coordinate loses orientation
data even on seam.

**Lean status:** obstruction and positive survivor fully formalized; compact physical-orbit
first-contact theorem remains open.

