# Hilbert–Schmidt product trace has an exact adjoint defect

- **ID:** hilbert-schmidt-product-trace-has-an-exact-adjoint-defect
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Q-II; faithful quadratic source reserves.
- **Statement:** For Hilbert–Schmidt operators A and B, their average squared norm minus or plus the real product trace equals half the squared norm of A minus or plus B's adjoint.

## Proof and scope

Hilbert–Schmidt polarization gives

    (||A||²_HS+||B||²_HS)/2 ∓ Re tr(AB) = ||A ∓ B*||²_HS/2.

Adjoint preserves squared norm, and trace cyclicity identifies the real
mixed inner product. Thus the average dominates both signs of the trace.
Equality with the positive trace is exactly A=B*, by definiteness of the
Hilbert–Schmidt norm. Admission of A and B is part of the operator theorem's
domain, not an unproved arithmetic input. Actual Meyer admission is separately
certified in `MeyerHilbertSchmidtSource`.

The algebraic identity is standard and is not claimed novel. Its whole-source
arithmetic application remains on the separate reserve card.

## Lean certificate

Module: `HTGeometry/HilbertSchmidtTraceDefect.lean`.

- `hsNormSq_sub_eq_real_inner`
- `half_hsNormSq_sum_sub_re_trace`
- `half_hsNormSq_sum_add_re_trace`
- `half_hsNormSq_sum_le_re_trace_iff`

Actual-file `lake --old env lean` check passed. All four endpoint transitive
axiom audits contain only `propext`, `Classical.choice`, and `Quot.sound`.
Temporary prints removed; HTGeometry umbrella wired.
