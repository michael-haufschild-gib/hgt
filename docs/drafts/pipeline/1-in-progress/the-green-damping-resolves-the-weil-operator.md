# Green damping resolves the Weil operator

- **Stage:** 1-in-progress
- **Type:** CONJECTURE / construction
- **Obstacle:** B133: passage from the geometric Green form to its actual inverse.

## Target

On every physical aperture, construct the bounded operator of the strict
Green damping with the literal saturated polar and prime terms. After the
existing coercive scalar shift, prove that its inverse converges strongly
to the existing source-defined Weil Friedrichs resolvent. No positivity of
the unshifted Weil form is assumed.

## Mechanism under investigation

For shifted inverse states `x_r=A_r⁻¹g`, square completion gives
`‖x_r−x_s‖² ≤ Re⟨g,x_r⟩−Re⟨g,x_s⟩` whenever `r≤s`.
The scalar energies are decreasing and nonnegative, so the states are Cauchy.
For their strong limit `x`, Fatou and continuity of the bounded remainder
should give `Q(x)≤Re⟨g,x⟩`, hence admission to the exact complete form domain.

Let `x_*` be the existing shifted Weil inverse state. The damped variational
inequality tested only at `x_*` gives `Q(x_*)≤Re⟨g,x⟩` in the limit.
The exact limiting Riesz equation then yields
`Q(x−x_*)≤Q(x_*)−Re⟨g,x⟩≤0`; coercivity forces `x=x_*`.
This avoids a separate passage to mixed jump integrals.

The complete form domain and finite Green limit are already identified in
`TheGreenDampingDetectsTheCompleteWeilFormDomain.lean`. The missing work is
operator construction and passage to the variational equation for moving
solutions. Norm resolvent convergence is a further question, not asserted.

## Boundary

This concerns the saturated arithmetic Green form. It does not identify one
invariant adelic torus Robin kernel with Weil's diagonal; the accepted gluing
obstruction remains in force.
