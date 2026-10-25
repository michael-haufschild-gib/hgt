# Sublinear uncentered Vaughan pole cross entries

- **ID:** sublinear-uncentred-vaughan-pole-cross-entries
- **Stage:** 5-failed
- **Type:** REFUTED ESTIMATE WITH FORMALIZED POSITIVE SURVIVOR
- **Source:** ../1-in-progress/q-i-selective-square-root-band.md
- **Retired claim:** All four uncentered cross entries meeting the pole row can be `o(T)` for some moving cutoff schedule.

For every `ε>0`, their sum divided by `T` tends to `-ρ²<0`, independently of both
cutoffs. Eventually some entry is at most `-ρ²T/8` for every cutoff pair. Thus the
retired estimate contradicts an exact feature of the actual arithmetic source.

The strongest audited positive survivor comprises the cutoff-independent pole row,
the uniform negative-entry witness, the exact relative cancellation error, and the
uniform leading Gram law for arbitrary cutoffs. At square-root cutoffs the diagonal
density is `4ρ²`; complete mixed/diagonal ratio tends to `-1`. At fixed cutoffs,
bounded interior energy is exactly an `O(1/T)` bound on that relative cancellation
error. Near-total leading cancellation alone therefore carries no admission rate.

Paper proofs and Lean declarations are recorded in
`../3-formalized/vaughan-pole-mass-and-fixed-cutoff-gram.md` and
`../3-formalized/uniform-vaughan-gram-leading-term.md`. All supporting leaves passed
their final direct checks; audited declarations use only standard axioms; umbrella
imports are present. The uniform theorem is the positive result exposed by retaining
the full pole row rather than discarding it.

Only this sublinearity claim is retired. No impossibility theorem for Class III
identities, residual cancellation, fixed strips, or full Q-I is asserted.
