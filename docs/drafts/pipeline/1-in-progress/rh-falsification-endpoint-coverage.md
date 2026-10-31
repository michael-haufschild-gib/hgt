# Distinct RH falsification endpoints

- **Stage:** 1-in-progress
- **Scope:** All distinct missing falsification endpoints implied by the Lean corpus; ongoing conjecture and novelty audit.

## Formalized additions

| Mechanism | Exact witness | Lean owner |
|---|---|---|
| Anchored holomorphic dynamics | A nonanchor upper periodic point of the normalized Xi Donoghue map; period-one Gaussian stationary equation | `Bottcher/HalfPlane/XiDonoghueDynamics.lean` |

## Exclusions

Hankel defects, shifted-moment negativity, logarithmic-derivative sign failure, Möbius energy
escape, and positive-time heat multiple zeros already have falsification endpoints. New notation,
contraposition, changed sampling, or an equivalent witness alone does not constitute a new endpoint.
Further Donoghue orbit consequences belong to the existing dynamical family unless they add a
strictly stronger obstruction.

## Coverage requiring investigation

- Arithmetic continuation, signed energy, prime correlations, and quantitative source bounds.
- Heat dynamics, collision geometry, and zero displacement.
- Moment and approximation geometry beyond existing positivity defects.
- Spectral index, variational bounds, and rigidity of actual arithmetic operators.
- Analytic geometry of Xi and source-formed transforms beyond existing zero/sign receivers.

Each candidate requires exact source statements, a search for existing equivalents, a complete
proof, kernel formalization, and transitive axiom audit. No exhaustive-completion claim is made.
