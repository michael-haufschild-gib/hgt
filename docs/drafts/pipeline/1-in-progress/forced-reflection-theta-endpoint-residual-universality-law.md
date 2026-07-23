# Forced-reflection theta-endpoint residual universality law

Status: exact `lake env lean` audit passed; final module/lint/axiom audit pending.

## Lean sources

- `completedRiemannZeta_reflection_center_eq_half`
- `xiThetaEndpointResidual_eq`
- `completedRiemannZeta₀_eq_neg_inv_mul_iff_xi_eq_zero`
- `xi_one_sub`

## Survivor

Every reflection symmetry of the meromorphic completed zeta is forced to the functional-equation
reflection `s ↦ 1-s`.  This same forced reflection preserves the exact theta-endpoint residual and
transports the reflected rational endpoint anchor precisely to the original Xi-zero condition.

The pole-rigidity theorem fixed only the reflection center.  The endpoint theorem identified only
the local residual zero condition.  Their connector makes pole geometry determine the global
reflection law of the entire endpoint obstruction.

## Proof skeleton

Use the two-pole rigidity theorem to replace the arbitrary reflection center by one.  Apply the
exact residual formula at `s` and `1-s`, use `xi_one_sub`, and normalize the identical quadratic
denominators.  Apply the rational-anchor equivalence at `1-s` and transport its Xi value through
the same functional equation.

## Novelty audit

Pending post-formalization literature search.
